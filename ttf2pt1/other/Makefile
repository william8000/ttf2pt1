
PROGS= bz cmpf

BZOBJS= bz.o bzscreen.o

CFLAGS= -g

all: $(PROGS)

clean:
	rm -f $(PROGS) *.o *.core

bz: $(BZOBJS)
	$(CC) $(CFLAGS) -o bz $(BZOBJS)

cmpf: cmpf.c
	$(CC) $(CFLAGS) -o cmpf -I/usr/local/include -L/usr/local/lib cmpf.c -lt1 -lm
