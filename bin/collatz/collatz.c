/*-
 * Copyright (c) 2017 Dag-Erling Smørgrav
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include <assert.h>
#include <err.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static uintmax_t stop = (uintmax_t)1 << 30;

static bool opt_d;
static bool opt_i;
static bool opt_v;

static bool tty;

#define debug(...) \
	do { if (opt_d) fprintf(stderr, __VA_ARGS__); } while (0)
#define verbose(...) \
	do { if (opt_d || opt_v) fprintf(stderr, __VA_ARGS__); } while (0)

#define MIN(a, b)	((a) < (b) ? (a) : (b))
#define MAX(a, b)	((a) > (b) ? (a) : (b))

/*
 * Tree of reachable numbers
 */
typedef struct node {
	uintmax_t	 first;
	uintmax_t	 last;
	uintmax_t	 covered;
	unsigned int	 depth;
	struct node	*left;
	struct node	*right;
} node;

#define LEAF_NODE(n)	((n)->left == NULL && (n)->right == NULL)

static node *root;
static node *proven;
static unsigned int nodes;

/*
 * Work queue
 */
#define WORKQUEUE_SIZE		(1<<20)
#define WORKQUEUE_DEPTH		((qw + WORKQUEUE_SIZE - qr) % WORKQUEUE_SIZE)
static uintmax_t queue[WORKQUEUE_SIZE];
static unsigned int qr, qw;

/*
 * Statistics
 */
static unsigned int maxnodes, maxdepth, maxrecurse;

#define PROGRESS_INTERVAL	(1<<10)

static void fprintnodes(FILE *, const node *);
static node *create(unsigned int, uintmax_t, uintmax_t);
static void destroy(node *);
static bool insert_into_leaf(node *, uintmax_t, uintmax_t);
static bool insert_into_internal(node *, uintmax_t, uintmax_t);
static bool insert(node *, uintmax_t, uintmax_t);
static bool lookup(const node *, uintmax_t) __attribute__((__unused__));
static bool work_append(uintmax_t);
static uintmax_t work_fetch(void);
static void progress(bool);
static void collatz(void);
static void collatz_r(uintmax_t);
static void collatz_i(void);

/*
 * Print out the tree.
 */
static void
fprintnodes(FILE *f, const node *n)
{

	if (n->left == NULL && n->right == NULL)
		fprintf(f, "[%ju, %ju]\n", n->first, n->last);
	if (n->left != NULL)
		fprintnodes(f, n->left);
	if (n->right != NULL)
		fprintnodes(f, n->right);
}

/*
 * Create a leaf node.
 */
static node *
create(unsigned int depth, uintmax_t first, uintmax_t last)
{
	node *n;

	debug("%6u creating [%ju, %ju]\n", depth, first, last);
	if ((n = calloc(1, sizeof *n)) == NULL)
		err(1, "calloc()");
	n->covered = (n->last = last) - (n->first = first) + 1;
	if ((n->depth = depth) > maxdepth)
		maxdepth = depth;
	nodes++;
	if (++nodes > maxnodes)
		maxnodes = nodes;
	if (first == 1)
		proven = n;
	return (n);
}

/*
 * Destroy a node.
 */
static void
destroy(node *n)
{

	if (n == NULL)
		return;
	destroy(n->left);
	destroy(n->right);
	debug("%6u destroying [%ju, %ju]\n", n->depth, n->first, n->last);
	nodes--;
	free(n);
}

/*
 * Insert a range into a leaf node.
 *
 * Possible cases: the new range...
 * ...is a sub-range of this node
 * ...covers this node entirely
 * ...is left-adjacent to this node
 * ...is right-adjacent to this node
 * ...sits to the left of this node
 * ...sits to the right of this node
 *
 * Returns true if the entire range was already in the tree.
 */
static bool
insert_into_leaf(node *n, uintmax_t first, uintmax_t last)
{

	assert(n->left == NULL && n->right == NULL);

	/* cases where we remain a leaf */
	if (first >= n->first && last <= n->last) {
		/* sub-range */
		return (true);
	} else if (first <= n->last + 1 && last >= n->first - 1) {
		/* overlaps with or adjacent to us */
		debug("%6u expanding [%ju, %ju] to [%ju, %ju]\n",
		    n->depth, n->first, n->last, first, last);
		if (first < n->first)
			n->first = first;
		if (last > n->last)
			n->last = last;
		n->covered = n->last - n->first + 1;
		if (n->first == 1)
			proven = n;
		return (false);
	}

	/* cases where we split into child nodes */
	if (last < n->first - 1) {
		/* sits to the left */
		debug("%6u splitting into [%ju, %ju] and [%ju, %ju]\n",
		    n->depth, first, last, n->first, n->last);
		n->left = create(n->depth + 1, first, last);
		n->right = create(n->depth + 1, n->first, n->last);
	} else if (first > n->last + 1) {
		/* sits to the right */
		debug("%6u splitting into [%ju, %ju] and [%ju, %ju]\n",
		    n->depth, n->first, n->last, first, last);
		n->left = create(n->depth + 1, n->first, n->last);
		n->right = create(n->depth + 1, first, last);
	} else {
		assert(0);
	}
	n->first = n->left->first;
	n->last = n->right->last;
	n->covered = n->left->covered + n->right->covered;
	return (false);
}

/*
 * Insert a range into an internal node.
 *
 * Possible cases: the new range...
 * ...overlaps with or is adjacent to one of this node's children
 * ...overlaps with or is adjacent to both of this node's children
 * ...sits to the left of this node
 * ...sits to the right of this node
 * ...sits between this node's children
 *
 * Returns false if the number was already in the tree.
 */
static bool
insert_into_internal(node *n, uintmax_t first, uintmax_t last)
{
	bool found;

	assert(n->left != NULL && n->right != NULL);

	/* cases where we become a leaf */
	if (first <= n->left->last + 1 && last >= n->right->first - 1) {
		/* overlaps with or adjacent to both children */
		if (first < n->first)
			n->first = first;
		if (last > n->last)
			n->last = last;
		debug("%6u coalescing [%ju, %ju] [%ju, %ju] into [%ju, %ju]\n",
		    n->depth, n->left->first, n->left->last,
		    n->right->first, n->right->last,
		    n->first, n->last);
		destroy(n->left);
		destroy(n->right);
		n->left = n->right = NULL;
		n->covered = n->last - n->first + 1;
		if (n->first == 1)
			proven = n;
		return (false);
	}

	/* cases where we descend into our children */
	if (first > n->left->last + 1 && last < n->right->first - 1) {
		/* sits between them, pass it to the shallowest one */
		if (n->left->depth < n->right->depth)
			found = insert(n->left, first, last);
		else
			found = insert(n->right, first, last);
	} else if (last < n->right->first - 1) {
		/* overlaps with, adjacent to or left of left child */
		found = insert(n->left, first, last);
	} else if (first > n->left->last + 1) {
		/* overlaps with, adjacent to or right of right child */
		found = insert(n->right, first, last);
	} else {
		assert(0);
	}
	if (!found) {
		n->first = n->left->first;
		n->last = n->right->last;
		n->covered = n->left->covered + n->right->covered;
	}
	return (found);
}

/*
 * Dispatch to correct insert function depending on leafiness.
 */
static bool
insert(node *n, uintmax_t first, uintmax_t last)
{
	bool found;

	assert(first <= last);
	assert((n->left == NULL) == (n->right == NULL));
	assert(n->left == NULL || n->first == n->left->first);
	assert(n->right == NULL || n->last == n->right->last);
	if ((first == last && (first == n->first || last == n->last)) ||
	    (LEAF_NODE(n) && first == n->first && last == n->last)) {
		/* trivial cases */
		found = true;
	} else {
		/* do it the hard way */
		debug("%6u inserting [%ju, %ju] into [%ju, %ju]\n",
		    n->depth, first, last, n->first, n->last);
		found = LEAF_NODE(n) ? insert_into_leaf(n, first, last) :
		    insert_into_internal(n, first, last);
	}
	if (found) {
		/* range was already covered */
		debug("%6u found [%ju, %ju] in [%ju, %ju]\n",
		    n->depth, first, last, n->first, n->last);
	} else {
		/* range was inserted, adjust coverage etc. */
		if (LEAF_NODE(n)) {
			n->covered = n->last - n->first + 1;
		} else {
			n->first = n->left->first;
			n->last = n->right->last;
			n->covered = n->left->covered + n->right->covered;
		}
	}
	return (found);
}

/*
 * Returns true if the specified number is contained in the tree.
 */
static bool
lookup(const node *n, uintmax_t num)
{

	if (LEAF_NODE(n))
		return (num >= n->first && num <= n->last);
	else if (num >= n->left->first && num <= n->left->last)
		return (lookup(n->left, num));
	else if (num >= n->right->first && num <= n->right->last)
		return (lookup(n->right, num));
	else
		return (false);
}

/*
 * Work queue for iterative version
 */
bool
work_append(uintmax_t num)
{

	if (qw == qr && queue[qw] != 0)
		return (false);
//	debug("append %12ju\n", num);
	queue[qw] = num;
	qw = (qw + 1) % WORKQUEUE_SIZE;
	return (true);
}

uintmax_t
work_fetch(void)
{
	uintmax_t num;

	if (qr == qw && queue[qr] == 0)
		return (0);
	num = queue[qr];
	queue[qr] = 0;
	qr = (qr + 1) % WORKQUEUE_SIZE;
//	debug("fetch %12ju\n", num);
	return (num);
}

/*
 * Show the lowest and highest numbers recorded and the percentage of
 * numbers within that range that have also been recorded.
 */
static inline void
progress(bool final)
{
	static unsigned int count;
	static char buf[72];

	if (tty && (final || count-- == 0)) {
		snprintf(buf, sizeof buf,
		    "%3ju%% [1, %ju] (n %9u d %9u %c %9u)%*s",
		    (root->covered * 100 / (root->last - root->first + 1)),
		    proven->last, nodes, maxdepth, opt_i ? 'q' : 'r',
		    opt_i ? WORKQUEUE_DEPTH : maxrecurse, 72, " ");
		buf[70] = final ? '\n' : '\r';
		write(STDERR_FILENO, buf, sizeof buf - 1);
		count = PROGRESS_INTERVAL;
	}
}

/*
 * Demonstrate the Collatz conjecture by constructing all possible
 * sequences in reverse.
 *
 * Iterative version (experimental):
 *
 *   Initialization:
 *
 *     - Record 1 and 2 as reachable
 *     - Place 4 on the work queue
 *
 *   Iterative step for N:
 *
 *     - Record N as reachable
 *     - Place N = N * 2 on the queue
 *     - If N - 1 ≡ 3 mod 6, place N = (N - 1) / 3 on the queue
 *
 * Recursive version:
 *
 *   Initialization:
 *
 *     - Record 1 and 2 as reachable
 *     - Recurse for N = 4
 *
 *   Recursive step for N:
 *
 *     - Record N as reachable
 *     - Recurse for N = N * 2
 *     - If N - 1 ≡ 3 mod 6, recurse for N = (N - 1) / 3.
 *
 * Note: if N - 1 ≡ 0 mod 6, then (N - 1) / 3 ≡ 0 mod 6, which means it's
 * even, which means we wouldn't have gotten from there to N.
 */
static void
collatz(void)
{
	struct timespec start, end;

	clock_gettime(CLOCK_REALTIME, &start);
	verbose("stop at %ju\n", stop);
	root = create(0, 1, 2);
	debug("           ---\n");
	if (opt_i) {
		(void)work_append(4);
		collatz_i();
	} else {
		collatz_r(4);
	}
	progress(true);
	clock_gettime(CLOCK_REALTIME, &end);
	end.tv_sec -= start.tv_sec;
	if ((end.tv_nsec -= start.tv_nsec) < 0)
		end.tv_nsec += 1000000000;
	verbose("done in %lu.%.03lu s\n",
	    (unsigned long)end.tv_sec,
	    (unsigned long)end.tv_nsec / 1000000);
	if (opt_v)
		fprintnodes(stdout, root);
}

static void
collatz_i(void)
{
	uintmax_t num;

	while ((num = work_fetch()) != 0) {
		progress(false);
		if (num >= stop)
			continue;
		if (insert(root, num, num))
			continue;
		work_append(num * 2);
		if (--num % 6 == 3) {
			work_append(num / 3);
			debug("           ---\n");
		}
		debug("           ---\n");
	}
}

static void
collatz_r(uintmax_t num)
{
	static uintmax_t depth;
	bool found;

	if (++depth > maxrecurse)
		maxrecurse = depth;
	progress(false);
	if (num >= stop)
		return;
	found = insert(root, num, num);
	debug("           ---\n");
	if (found)
		return;
	collatz_r(num * 2);
	if (--num % 6 == 3)
		collatz_r(num / 3);
	--depth;
}

static void
usage(void)
{

	fprintf(stderr, "usage: collatz [-drv] [log2max]\n");
	exit(1);
}

int
main(int argc, char *argv[])
{
	unsigned long log2max;
	char *e;
	int opt;

	while ((opt = getopt(argc, argv, "div")) != -1)
		switch (opt) {
		case 'd':
			opt_d = true;
			break;
		case 'i':
			opt_i = true;
			break;
		case 'v':
			opt_v = true;
			break;
		default:
			usage();
		}

	argc -= optind;
	argv += optind;

	if (argc == 1) {
		log2max = strtoul(argv[0], &e, 10);
		if (*argv[0] == '\0' || *e != '\0')
			usage();
		if (log2max < 3 || log2max > 63)
			errx(1, "log2max must be between 3 and 63");
		stop = (uintmax_t)1 << log2max;
		argc--;
	}

	if (argc > 0)
		usage();

	tty = isatty(STDERR_FILENO);
	collatz();

	exit(0);
}
