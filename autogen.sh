#!/bin/sh
aclocal -I m4
autoheader
automake --add-missing --copy --foreign
autoconf
