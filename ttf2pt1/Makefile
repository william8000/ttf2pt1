
# This file should be configured before running `make'.
# Uncomment or change the values that are relevant for your OS.

# The preferred C compiler (by default use the OS-specific default value).
# For BSD/OS, FreeBSD, Linux (all flavors), NetBSD, OpenBSD the default
# compiler is GNU C. 
# (Note please the politically correct ordering by alphabet ! :-)
#
# Use GNU C even if it's not the default compiler
#
#CC=gcc
#
# Use the standard ANSI C compiler on HP-UX even if it's not default
#
#CC=c89

#
# The system-dependent flags for the C compiler
#
# Default

CFLAGS= -O

# For GNU C
#
#CFLAGS= -O2
#
# For GNU C on HP-UX/PA-RISC 1.1
#
#CFLAGS= -O2 -Wa,-w
#
# For the standard ANSI C on HP-UX
#
#CFLAGS= +O2 -D_HPUX_SOURCE

#
# The system-dependent libraries
#
# Defalut (for the BSD-style OSes)

LIBS= -lm

# For SystemV (such as SCO, UnixWare, Solaris, but _NOT_ Linux or HP-UX)
#
#LIBS= -lm -lsocket

# After you have configured the Makefile, comment out the following
# definition:
warning: docs
	@echo >&2
	@echo "  You have to configure the Makefile before running make!" >&2
	@echo "(or if you are lazy and hope that it will work as is run \`make all')">&2
	@echo >&2

DOCS=CHANGES README INSTALL INSTALL.hpux encodings/README other/README \
	app/X11/README app/netscape/README

all:	t1asm ttf2pfa ttf2pt1 docs rpm

docs: $(DOCS)

clean:
	rm -f t1asm ttf2pfa ttf2pt1 *.o app/RPM/Makefile
	( cd other && make clean; )

veryclean: clean
	rm -f $(DOCS)

rpm: app/RPM/Makefile

app/RPM/Makefile: Makefile
	sed 's/^CFLAGS.*=.*$$/CFLAGS= -O2/;/warning:/,/^$$/s/^/#/' <Makefile >app/RPM/Makefile

t1asm: t1asm.c
	$(CC) $(CFLAGS) -o t1asm -DSTANDALONE t1asm.c $(LIBS)

ttf2pfa:	ttf2pfa.c ttf.h
	$(CC) $(CFLAGS) -o ttf2pfa ttf2pfa.c $(LIBS)

ttf2pt1.o: ttf2pt1.c ttf.h pt1.h global.h
	$(CC) $(CFLAGS) -c ttf2pt1.c

pt1.o: pt1.c ttf.h pt1.h global.h
	$(CC) $(CFLAGS) -c pt1.c

ttf2pt1:	ttf2pt1.o pt1.o t1asm.o
	$(CC) $(CFLAGS) -o ttf2pt1 ttf2pt1.o pt1.o t1asm.o $(LIBS)

CHANGES: CHANGES.html
	scripts/unhtml <CHANGES.html >CHANGES

README: README.html
	scripts/unhtml <README.html >README

encodings/README: encodings/README.html
	scripts/unhtml <encodings/README.html >encodings/README

other/README: other/README.html
	scripts/unhtml <other/README.html >other/README

app/X11/README: app/X11/README.html
	scripts/unhtml <app/X11/README.html >app/X11/README

app/netscape/README: app/netscape/README.html
	scripts/unhtml <app/netscape/README.html >app/netscape/README

INSTALL: INSTALL.html
	scripts/unhtml <INSTALL.html >INSTALL

INSTALL.hpux: INSTALL.hpux.html
	scripts/unhtml <INSTALL.hpux.html >INSTALL.hpux
