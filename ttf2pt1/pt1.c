/*
 * see COPYRIGHT
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <time.h>
#include <netinet/in.h>
#include <ctype.h>
#include <math.h>
#include <unistd.h>

#include "ttf.h"
#include "pt1.h"
#include "global.h"

int      stdhw, stdvw;	/* dominant stems widths */
int      stemsnaph[12], stemsnapv[12];	/* most typical stem width */

int      bluevalues[14];
int      nblues;
int      otherblues[10];
int      notherb;
int      bbox[4];	/* the FontBBox array */
double   italic_angle;

GLYPH   *glyph_list;
short    encoding[256];	/* inverse of glyph[].char_no */

int
sign(
     int x
)
{
	if (x > 0)
		return 1;
	else if (x < 0)
		return -1;
	else
		return 0;
}

GENTRY         *
newgentry(void)
{
	GENTRY         *ge;

	ge = malloc(sizeof(GENTRY));

	if (ge == 0) {
		fprintf(stderr, "***** Memory allocation error *****\n");
		exit(1);
	}
	ge->next = ge->prev = ge->first = 0;
	ge->stemid = -1;
	return ge;
}

/*
 * * SB * Routines to print out Postscript functions with optimization
 */

void
rmoveto(
	int dx,
	int dy
)
{
	if (optimize && dx == 0 && dy == 0)	/* for special pathologic
						 * case */
		return;
	else if (optimize && dx == 0)
		fprintf(pfa_file, "%d vmoveto\n", dy);
	else if (optimize && dy == 0)
		fprintf(pfa_file, "%d hmoveto\n", dx);
	else
		fprintf(pfa_file, "%d %d rmoveto\n", dx, dy);
}

void
rlineto(
	int dx,
	int dy
)
{
	if (optimize && dx == 0 && dy == 0)	/* for special pathologic
						 * case */
		return;
	else if (optimize && dx == 0)
		fprintf(pfa_file, "%d vlineto\n", dy);
	else if (optimize && dy == 0)
		fprintf(pfa_file, "%d hlineto\n", dx);
	else
		fprintf(pfa_file, "%d %d rlineto\n", dx, dy);
}

void
rrcurveto(
	  int dx1,
	  int dy1,
	  int dx2,
	  int dy2,
	  int dx3,
	  int dy3
)
{
	/* first two ifs are for crazy cases that occur surprisingly often */
	if (optimize && dx1 == 0 && dx2 == 0 && dx3 == 0)
		rlineto(0, dy1 + dy2 + dy3);
	else if (optimize && dy1 == 0 && dy2 == 0 && dy3 == 0)
		rlineto(dx1 + dx2 + dx3, 0);
	else if (optimize && dy1 == 0 && dx3 == 0)
		fprintf(pfa_file, "%d %d %d %d hvcurveto\n",
			dx1, dx2, dy2, dy3);
	else if (optimize && dx1 == 0 && dy3 == 0)
		fprintf(pfa_file, "%d %d %d %d vhcurveto\n",
			dy1, dx2, dy2, dx3);
	else
		fprintf(pfa_file, "%d %d %d %d %d %d rrcurveto\n",
			dx1, dy1, dx2, dy2, dx3, dy3);
}

void
closepath(void)
{
	fprintf(pfa_file, "closepath\n");
}

/*
** Routine that checks integrity of the path, for debugging
*/

void
assertpath(
	   GENTRY * from,
	   int line,
	   char *name
)
{
	GENTRY         *first, *pe, *ge;

	if(from==0)
		return;
	pe = from->prev;
	for (ge = from; ge != 0; pe = ge, ge = ge->next) {
		if (pe != ge->prev) {
			fprintf(stderr, "**** assertpath: called from line %d (%s) ****\n", line, name);
			fprintf(stderr, "unidirectional chain 0x%x -next-> 0x%x -prev-> 0x%x \n",
				pe, ge, ge->prev);
			exit(1);
		}
		if (ge->type == GE_MOVE)
			first = ge->next;
		if (ge->first && ge->first != first) {
			fprintf(stderr, "**** assertpath: called from line %d (%s) ****\n", line, name);
			fprintf(stderr, "broken loop 0x%x -...-> 0x%x -first-> 0x%x \n",
				first, ge, ge->first);
			exit(1);
		}
		if (ge->type == GE_PATH) {
			if (ge->prev == 0) {
				fprintf(stderr, "**** assertpath: called from line %d (%s) ****\n", line, name);
				fprintf(stderr, "empty path at 0x%x \n", ge);
				exit(1);
			}
			if (ge->prev->first == 0) {
				fprintf(stderr, "**** assertpath: called from line %d (%s) ****\n", line, name);
				fprintf(stderr, "path without backlink at 0x%x \n", pe);
				exit(1);
			}
		}
	}
}

/*
 * * SB * Routines to save the generated data about glyph
 */

void
g_rmoveto(
	  GLYPH * g,
	  int x,
	  int y)
{
	GENTRY         *oge;

	if (0)
		fprintf(stderr, "%s: rmoveto(%d, %d)\n", g->name, x, y);
	if ((oge = g->lastentry) != 0) {
		if (oge->type == GE_MOVE) {	/* just eat up the first move */
			oge->x3 = x;
			oge->y3 = y;
		} else if (oge->type == GE_LINE || oge->type == GE_CURVE) {
			fprintf(stderr, "Glyph %s: MOVE in middle of path\n", g->name);
		} else {
			GENTRY         *nge;

			nge = newgentry();
			nge->type = GE_MOVE;
			nge->x3 = x;
			nge->y3 = y;

			oge->next = nge;
			nge->prev = oge;
			g->lastentry = nge;
		}
	} else {
		GENTRY         *nge;

		nge = newgentry();
		nge->type = GE_MOVE;
		nge->x3 = x;
		nge->y3 = y;
		g->entries = g->lastentry = nge;
	}

}

void
g_rlineto(
	  GLYPH * g,
	  int x,
	  int y)
{
	GENTRY         *oge, *nge;

	if (0)
		fprintf(stderr, "%s: rlineto(%d, %d)\n", g->name, x, y);
	nge = newgentry();
	nge->type = GE_LINE;
	nge->x3 = x;
	nge->y3 = y;

	if ((oge = g->lastentry) != 0) {
		if (x == oge->x3 && y == oge->y3) {	/* empty line */
			/* ignore it or we will get in troubles later */
			free(nge);
			return;
		}
		if (g->path == 0)
			g->path = nge;

		oge->next = nge;
		nge->prev = oge;
		g->lastentry = nge;
	} else {
		fprintf(stderr, "Glyph %s: LINE outside of path\n", g->name);
#if 0
		g->entries = g->lastentry = nge;
#else
		free(nge);
#endif
	}

}

void
g_rrcurveto(
	    GLYPH * g,
	    int x1,
	    int y1,
	    int x2,
	    int y2,
	    int x3,
	    int y3)
{
	GENTRY         *oge, *nge;

	oge = g->lastentry;

	if (0)
		fprintf(stderr, "%s: rrcurveto(%d, %d, %d, %d, %d, %d)\n"
			,g->name, x1, y1, x2, y2, x3, y3);
	if (oge && oge->x3 == x1 && x1 == x2 && x2 == x3)	/* check if it's
								 * actually a line */
		g_rlineto(g, x1, y3);
	else if (oge && oge->y3 == y1 && y1 == y2 && y2 == y3)
		g_rlineto(g, x3, y1);
	else {
		nge = newgentry();
		nge->type = GE_CURVE;
		nge->x1 = x1;
		nge->y1 = y1;
		nge->x2 = x2;
		nge->y2 = y2;
		nge->x3 = x3;
		nge->y3 = y3;

		if (oge != 0) {
			if (x3 == oge->x3 && y3 == oge->y3) {
				free(nge);	/* consider this curve empty */
				/* ignore it or we will get in troubles later */
				return;
			}
			if (g->path == 0)
				g->path = nge;

			oge->next = nge;
			nge->prev = oge;
			g->lastentry = nge;
		} else {
			fprintf(stderr, "Glyph %s: CURVE outside of path\n", g->name);
#if 0
			g->entries = g->lastentry = nge;
#else
			free(nge);
#endif
		}
	}
}

void
g_closepath(
	    GLYPH * g
)
{
	GENTRY         *oge, *nge;

	if (0)
		fprintf(stderr, "%s: closepath\n", g->name);

	oge = g->lastentry;

	if (g->path == 0) {
		fprintf(stderr, "Warning: **** closepath on empty path in glyph \"%s\" ****\n",
			g->name);
		if (oge == 0) {
			fprintf(stderr, "No previois entry\n");
		} else {
			fprintf(stderr, "Previous entry type: %c\n", oge->type);
			if (oge->type == GE_MOVE) {
				g->lastentry = oge->prev;
				if (oge->prev == 0)
					g->entries = 0;
			}
		}
		return;
	}
	if (oge != 0) {		/* only if we actually have a path */
		nge = newgentry();
		nge->type = GE_PATH;
		oge->first = g->path;
		g->path = 0;
		oge->next = nge;
		nge->prev = oge;
		g->lastentry = nge;
	}
}

/*
 * * SB * Routines to smooth and fix the glyphs
 */

/*
** we don't want to see the curves with coinciding middle and
** outer points
*/

void
fixcvends(
	  GENTRY * ge
)
{
	int             dx, dy;
	int             x0, y0, x1, y1, x2, y2, x3, y3;

	if (ge->type != GE_CURVE)
		return;

	x0 = ge->prev->x3;
	y0 = ge->prev->y3;
	x1 = ge->x1;
	y1 = ge->y1;
	x2 = ge->x2;
	y2 = ge->y2;
	x3 = ge->x3;
	y3 = ge->y3;


	/* look at the start of the curve */
	if (x1 == x0 && y1 == y0) {
		dx = x2 - x1;
		dy = y2 - y1;

		if (dx == 0 && dy == 0
		    || x2 == x3 && y2 == y3) {
			/* Oops, we actually have a straight line */
			/*
			 * if it's small, we hope that it will get optimized
			 * later
			 */
			if (abs(x3 - x0) <= 2 || abs(y3 - y0) <= 2) {
				ge->x1 = x3;
				ge->y1 = y3;
				ge->x2 = x0;
				ge->y2 = y0;
			} else {/* just make it a line */
				ge->type = GE_LINE;
			}
		} else {
			if (abs(dx) < 4 && abs(dy) < 4) {	/* consider it very
								 * small */
				ge->x1 = x2;
				ge->y1 = y2;
			} else if (abs(dx) < 8 && abs(dy) < 8) {	/* consider it small */
				ge->x1 += dx / 2;
				ge->y1 += dy / 2;
			} else {
				ge->x1 += dx / 4;
				ge->y1 += dy / 4;
			}
			/* make sure that it's still on the same side */
			if (abs(x3 - x0) * abs(dy) < abs(y3 - y0) * abs(dx)) {
				if (abs(x3 - x0) * abs(ge->y1 - y0) > abs(y3 - y0) * abs(ge->x1 - x0))
					ge->x1 += sign(dx);
			} else {
				if (abs(x3 - x0) * abs(ge->y1 - y0) < abs(y3 - y0) * abs(ge->x1 - x0))
					ge->y1 += sign(dy);
			}

			ge->x2 += (x3 - x2) / 8;
			ge->y2 += (y3 - y2) / 8;
			/* make sure that it's still on the same side */
			if (abs(x3 - x0) * abs(y3 - y2) < abs(y3 - y0) * abs(x3 - x2)) {
				if (abs(x3 - x0) * abs(y3 - ge->y2) > abs(y3 - y0) * abs(x3 - ge->x2))
					ge->y1 -= sign(y3 - y2);
			} else {
				if (abs(x3 - x0) * abs(y3 - ge->y2) < abs(y3 - y0) * abs(x3 - ge->x2))
					ge->x1 -= sign(x3 - x2);
			}

		}
	} else if (x2 == x3 && y2 == y3) {
		dx = x1 - x2;
		dy = y1 - y2;

		if (dx == 0 && dy == 0) {
			/* Oops, we actually have a straight line */
			/*
			 * if it's small, we hope that it will get optimized
			 * later
			 */
			if (abs(x3 - x0) <= 2 || abs(y3 - y0) <= 2) {
				ge->x1 = x3;
				ge->y1 = y3;
				ge->x2 = x0;
				ge->y2 = y0;
			} else {/* just make it a line */
				ge->type = GE_LINE;
			}
		} else {
			if (abs(dx) < 4 && abs(dy) < 4) {	/* consider it very
								 * small */
				ge->x2 = x1;
				ge->y2 = y1;
			} else if (abs(dx) < 8 && abs(dy) < 8) {	/* consider it small */
				ge->x2 += dx / 2;
				ge->y2 += dy / 2;
			} else {
				ge->x2 += dx / 4;
				ge->y2 += dy / 4;
			}
			/* make sure that it's still on the same side */
			if (abs(x3 - x0) * abs(dy) < abs(y3 - y0) * abs(dx)) {
				if (abs(x3 - x0) * abs(ge->y2 - y3) > abs(y3 - y0) * abs(ge->x2 - x3))
					ge->x2 += sign(dx);
			} else {
				if (abs(x3 - x0) * abs(ge->y2 - y3) < abs(y3 - y0) * abs(ge->x2 - x3))
					ge->y2 += sign(dy);
			}

			ge->x1 += (x0 - x1) / 8;
			ge->y1 += (y0 - y1) / 8;
			/* make sure that it's still on the same side */
			if (abs(x3 - x0) * abs(y0 - y1) < abs(y3 - y0) * abs(x0 - x1)) {
				if (abs(x3 - x0) * abs(y0 - ge->y1) > abs(y3 - y0) * abs(x0 - ge->x1))
					ge->y1 -= sign(y0 - y1);
			} else {
				if (abs(x3 - x0) * abs(y0 - ge->y1) < abs(y3 - y0) * abs(x0 - ge->x1))
					ge->x1 -= sign(x0 - x1);
			}

		}
	}
}

/* if we have any curves that are in fact flat but
** are not horizontal nor vertical, substitute
** them also with lines
*/

void
flattencurves(
	      GLYPH * g
)
{
	GENTRY         *ge;
	int             x0, y0, x1, y1, x2, y2, x3, y3;

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type != GE_CURVE)
			continue;

		x0 = ge->prev->x3;
		y0 = ge->prev->y3;
		x1 = ge->x1;
		y1 = ge->y1;
		x2 = ge->x2;
		y2 = ge->y2;
		x3 = ge->x3;
		y3 = ge->y3;

		if ((x1 - x0) * (y2 - y1) == (x2 - x1) * (y1 - y0)
		    && (x1 - x0) * (y3 - y2) == (x3 - x2) * (y1 - y0)) {
			ge->type = GE_LINE;
		}
	}
}

/*
** After transformations we want to make sure that the resulting
** curve is going in the same quadrant as the original one,
** because rounding errors introduced during transformations
** may make the result completeley wrong.
**
** `dir' argument describes the direction of the original curve,
** it is the superposition of two values for the front and
** rear ends of curve:
**
** 1 - goes over the line connecting the ends
** 0 - coincides with the line connecting the ends
** -1 - goes under the line connecting the ends
*/

/* front end */
#define CVDIR_FUP	0x02	/* goes over the line connecting the ends */
#define CVDIR_FEQUAL	0x01	/* coincides with the line connecting the
				 * ends */
#define CVDIR_FDOWN	0x00	/* goes under the line connecting the ends */

/* rear end */
#define CVDIR_RSAME	0x30	/* is the same as for the front end */
#define CVDIR_RUP	0x20	/* goes over the line connecting the ends */
#define CVDIR_REQUAL	0x10	/* coincides with the line connecting the
				 * ends */
#define CVDIR_RDOWN	0x00	/* goes under the line connecting the ends */

void
fixcvdir(
	 GENTRY * ge,
	 int dir
)
{
	int             a, b, c, d;
	double          kk, kk1, kk2;
	int             changed;
	int             fdir, rdir;

	fdir = (dir & 0x0F) - CVDIR_FEQUAL;
	if ((dir & 0xF0) == CVDIR_RSAME)
		rdir = fdir;
	else
		rdir = ((dir & 0xF0) - CVDIR_REQUAL) >> 4;

	fixcvends(ge);

	c = sign(ge->x3 - ge->prev->x3);	/* note the direction of
						 * curve */
	d = sign(ge->y3 - ge->prev->y3);

	a = ge->y2 - ge->y1;
	b = ge->x2 - ge->x1;
	kk = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
	a = ge->y1 - ge->prev->y3;
	b = ge->x1 - ge->prev->x3;
	kk1 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
	a = ge->y3 - ge->y2;
	b = ge->x3 - ge->x2;
	kk2 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));

	changed = 1;
	while (changed) {
		if (ISDBG(FIXCVDIR)) {
			/* for debugging */
			fprintf(stderr, "fixcvdir %d %d (%d %d %d %d %d %d) %f %f %f\n",
				fdir, rdir,
				ge->x1 - ge->prev->x3,
				ge->y1 - ge->prev->y3,
				ge->x2 - ge->x1,
				ge->y2 - ge->y1,
				ge->x3 - ge->x2,
				ge->y3 - ge->y2,
				kk1, kk, kk2);
		}
		changed = 0;

		if (fdir > 0) {
			if (kk1 > kk) {	/* the front end has problems */
				if (c * (ge->x1 - ge->prev->x3) > 0) {
					ge->x1 -= c;
					changed = 1;
				} if (d * (ge->y2 - ge->y1) > 0) {
					ge->y1 += d;
					changed = 1;
				}
				/* recalculate the coefficients */
				a = ge->y2 - ge->y1;
				b = ge->x2 - ge->x1;
				kk = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
				a = ge->y1 - ge->prev->y3;
				b = ge->x1 - ge->prev->x3;
				kk1 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
			}
		} else if (fdir < 0) {
			if (kk1 < kk) {	/* the front end has problems */
				if (c * (ge->x2 - ge->x1) > 0) {
					ge->x1 += c;
					changed = 1;
				} if (d * (ge->y1 - ge->prev->y3) > 0) {
					ge->y1 -= d;
					changed = 1;
				}
				/* recalculate the coefficients */
				a = ge->y1 - ge->prev->y3;
				b = ge->x1 - ge->prev->x3;
				kk1 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
				a = ge->y2 - ge->y1;
				b = ge->x2 - ge->x1;
				kk = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
			}
		}
		if (rdir > 0) {
			if (kk2 < kk) {	/* the rear end has problems */
				if (c * (ge->x2 - ge->x1) > 0) {
					ge->x2 -= c;
					changed = 1;
				} if (d * (ge->y3 - ge->y2) > 0) {
					ge->y2 += d;
					changed = 1;
				}
				/* recalculate the coefficients */
				a = ge->y2 - ge->y1;
				b = ge->x2 - ge->x1;
				kk = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
				a = ge->y3 - ge->y2;
				b = ge->x3 - ge->x2;
				kk2 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
			}
		} else if (rdir < 0) {
			if (kk2 > kk) {	/* the rear end has problems */
				if (c * (ge->x3 - ge->x2) > 0) {
					ge->x2 += c;
					changed = 1;
				} if (d * (ge->y2 - ge->y1) > 0) {
					ge->y2 -= d;
					changed = 1;
				}
				/* recalculate the coefficients */
				a = ge->y2 - ge->y1;
				b = ge->x2 - ge->x1;
				kk = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
				a = ge->y3 - ge->y2;
				b = ge->x3 - ge->x2;
				kk2 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
			}
		}
	}
	fixcvends(ge);
}

/* Get the directions of ends of curve for further usage */

int
getcvdir(
	 GENTRY * ge
)
{
	int             a, b;
	double          k, k1, k2;
	int             dir = 0;

	a = ge->y2 - ge->y1;
	b = ge->x2 - ge->x1;
	k = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
	a = ge->y1 - ge->prev->y3;
	b = ge->x1 - ge->prev->x3;
	k1 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));
	a = ge->y3 - ge->y2;
	b = ge->x3 - ge->x2;
	k2 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : ((double) b / (double) a));

	if (k1 < k)
		dir |= CVDIR_FUP;
	else if (k1 > k)
		dir |= CVDIR_FDOWN;
	else
		dir |= CVDIR_FEQUAL;

	if (k2 > k)
		dir |= CVDIR_RUP;
	else if (k2 < k)
		dir |= CVDIR_RDOWN;
	else
		dir |= CVDIR_REQUAL;

	return dir;
}

/* a function just to test the work of fixcvdir() */
static void
testfixcvdir(
	     GLYPH * g
)
{
	GENTRY         *ge;
	int             dir;

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type == GE_CURVE) {
			dir = getcvdir(ge);
			fixcvdir(ge, dir);
		}
	}
}


/* check whether we can fix up the curve to change its size by (dx,dy) */
/* 0 means NO, 1 means YES */

int
checkcv(
	GENTRY * ge,
	int dx,
	int dy
)
{
	int             xdep, ydep;

	if (ge->type != GE_CURVE)
		return 0;

	xdep = ge->x3 - ge->prev->x3;
	ydep = ge->y3 - ge->prev->y3;

	if (ge->type == GE_CURVE
	    && (xdep * (xdep + dx)) > 0
	    && (ydep * (ydep + dy)) > 0) {
		return 1;
	} else
		return 0;
}

/* connect the ends of open contours */

void
closepaths(
	   GLYPH * g
)
{
	GENTRY         *ge, *fge;
	int             x = 0, y = 0;
	int             dir;

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if ((fge = ge->first) != 0) {
			if (fge->prev == 0 || fge->prev->type != GE_MOVE) {
				fprintf(stderr, "Glyph %s got strange beginning of path\n",
					g->name);
			}
			fge = fge->prev;
			if (fge->x3 != ge->x3 || fge->y3 != ge->y3) {
				/* we have to fix this open path */

				fprintf(stderr, "Glyph %s got path open by dx=%d dy=%d\n",
				g->name, fge->x3 - ge->x3, fge->y3 - ge->y3);

				if (abs(ge->x3 - fge->x3) <= 2 && abs(ge->y3 - fge->y3) <= 2) {
					/*
					 * small change, try to correct what
					 * we have
					 */
					int             xopen, yopen, xdep,
					                ydep, fxdep, fydep;

					xopen = fge->x3 - ge->x3;
					yopen = fge->y3 - ge->y3;
					xdep = ge->x3 - ge->prev->x3;
					ydep = ge->y3 - ge->prev->y3;
					fxdep = fge->next->x3 - fge->x3;
					fydep = fge->next->y3 - fge->y3;

					/* first try to fix a curve */
					if (checkcv(ge, xopen, yopen)) {
						dir = getcvdir(ge);
						ge->x2 += xopen;
						ge->x3 += xopen;
						ge->y2 += yopen;
						ge->y3 += yopen;
						fixcvdir(ge, dir);
					} else if (checkcv(fge->next, xopen, yopen)) {
						dir = getcvdir(fge->next);
						fge->x3 -= xopen;
						fge->next->x1 -= xopen;
						fge->y3 -= yopen;
						fge->next->y1 -= yopen;
						fixcvdir(fge->next, dir);

						/* then try to fix a line */
					} else if (ge->type == GE_LINE) {
						ge->x3 += xopen;
						ge->y3 += yopen;
					} else if (fge->next->type == GE_LINE) {
						fge->x3 -= xopen;
						fge->y3 -= yopen;

						/*
						 * and as the last resort
						 * draw a new line
						 */
					} else {
						GENTRY         *nge;

						nge = newgentry();
						nge->x3 = fge->x3;
						nge->y3 = fge->y3;
						nge->type = GE_LINE;

						nge->prev = ge;
						nge->next = ge->next;
						nge->first = ge->first;

						ge->next->prev = nge;
						ge->next = nge;
						ge->first = 0;
						ge = nge;
					}
				} else {
					/* big change, add new line */
					GENTRY         *nge;

					nge = newgentry();
					nge->x3 = fge->x3;
					nge->y3 = fge->y3;
					nge->type = GE_LINE;

					nge->prev = ge;
					nge->next = ge->next;
					nge->first = ge->first;

					ge->next->prev = nge;
					ge->next = nge;
					ge->first = 0;
					ge = nge;
				}
			}
		}
	}
}

void
smoothjoints(
	     GLYPH * g
)
{
	GENTRY         *ge, *ne;
	int             dx1, dy1, dx2, dy2, k;
	int             dir;

	if (g->entries == 0)	/* nothing to do */
		return;

	for (ge = g->entries->next; ge != 0; ge = ge->next) {
		if (ge->first) {
			ne = ge->first;
		} else {
			ne = ge->next;	/* previous entry */
		}

		/*
		 * although there should be no one-line path * and any path
		 * must end with CLOSEPATH, * nobody can say for sure
		 */

		if (ge == ne || ne == 0)
			continue;

		/* now handle various joints */

		if (ge->type == GE_LINE && ne->type == GE_LINE) {
			dx1 = ge->x3 - ge->prev->x3;
			dy1 = ge->y3 - ge->prev->y3;
			dx2 = ne->x3 - ge->x3;
			dy2 = ne->y3 - ge->y3;

			/* check whether they have the same direction */
			/* and the same slope */
			/* then we can join them into one line */

			if (dx1 * dx2 >= 0 && dy1 * dy2 >= 0 && dx1 * dy2 == dy1 * dx2) {
				if (ge->first) {
					/*
					 * move the starting point of the
					 * path
					 */
					ne->prev->x3 = ge->x3 = ne->x3;
					ne->prev->y3 = ge->y3 = ne->y3;

					/* get rid of the last line of path */
					ne->prev->next = ne->next;
					ne->next->prev = ne->prev;
					ge->first = ne->next;
					free(ne);
				} else {
					/* extend the previous line */
					ge->x3 = ne->x3;
					ge->y3 = ne->y3;

					/* and get rid of the next line */
					ge->first = ne->first;
					ne->prev->next = ne->next;
					ne->next->prev = ne->prev;
					free(ne);
				}
			}
		} else if (ge->type == GE_LINE && ne->type == GE_CURVE) {
			fixcvends(ne);

			dx1 = ge->x3 - ge->prev->x3;
			dy1 = ge->y3 - ge->prev->y3;
			dx2 = ne->x1 - ge->x3;
			dy2 = ne->y1 - ge->y3;

			/* if the line is nearly horizontal and we can fix it */
			if (dx1 != 0 && 5 * abs(dy1) / abs(dx1) == 0
			    && checkcv(ne, 0, -dy1)
			    && abs(dy1) <= 4) {
				dir = getcvdir(ne);
				ge->y3 -= dy1;
				ne->y1 -= dy1;
				fixcvdir(ne, dir);
				if (ge->first)
					ne->prev->y3 -= dy1;
				dy1 = 0;
			} else if (dy1 != 0 && 5 * abs(dx1) / abs(dy1) == 0
				   && checkcv(ne, -dx1, 0)
				   && abs(dx1) <= 4) {
				/* the same but vertical */
				dir = getcvdir(ne);
				ge->x3 -= dx1;
				ne->x1 -= dx1;
				fixcvdir(ne, dir);
				if (ge->first)
					ne->prev->x3 -= dx1;
				dx1 = 0;
			}
			/*
			 * if line is horizontal and curve begins nearly
			 * horizontally
			 */
			if (dy1 == 0 && dx2 != 0 && 5 * abs(dy2) / abs(dx2) == 0) {
				dir = getcvdir(ne);
				ne->y1 -= dy2;
				fixcvdir(ne, dir);
				dy2 = 0;
			} else if (dx1 == 0 && dy2 != 0 && 5 * abs(dx2) / abs(dy2) == 0) {
				/* the same but vertical */
				dir = getcvdir(ne);
				ne->x1 -= dx2;
				fixcvdir(ne, dir);
				dx2 = 0;
			}
		} else if (ge->type == GE_CURVE && ne->type == GE_LINE) {
			fixcvends(ge);

			dx1 = ge->x3 - ge->x2;
			dy1 = ge->y3 - ge->y2;
			dx2 = ne->x3 - ge->x3;
			dy2 = ne->y3 - ge->y3;

			/* if the line is nearly horizontal and we can fix it */
			if (dx2 != 0 && 5 * abs(dy2) / abs(dx2) == 0
			    && checkcv(ge, 0, dy2)
			    && abs(dy2) <= 4) {
				dir = getcvdir(ge);
				ge->y3 += dy2;
				ge->y2 += dy2;
				fixcvdir(ge, dir);
				if (ge->first)
					ne->prev->y3 += dy2;
				dy2 = 0;
			} else if (dy2 != 0 && 5 * abs(dx2) / abs(dy2) == 0
				   && checkcv(ge, dx2, 0)
				   && abs(dx2) <= 4) {
				/* the same but vertical */
				dir = getcvdir(ge);
				ge->x3 += dx2;
				ge->x2 += dx2;
				fixcvdir(ge, dir);
				if (ge->first)
					ne->prev->x3 += dx2;
				dx2 = 0;
			}
			/*
			 * if line is horizontal and curve ends nearly
			 * horizontally
			 */
			if (dy2 == 0 && dx1 != 0 && 5 * abs(dy1) / abs(dx1) == 0) {
				dir = getcvdir(ge);
				ge->y2 += dy1;
				fixcvdir(ge, dir);
				dy1 = 0;
			} else if (dx2 == 0 && dy1 != 0 && 5 * abs(dx1) / abs(dy1) == 0) {
				/* the same but vertical */
				dir = getcvdir(ge);
				ge->x2 += dx1;
				fixcvdir(ge, dir);
				dx1 = 0;
			}
		} else if (ge->type == GE_CURVE && ne->type == GE_CURVE) {
			fixcvends(ge);
			fixcvends(ne);

			dx1 = ge->x3 - ge->x2;
			dy1 = ge->y3 - ge->y2;
			dx2 = ne->x1 - ge->x3;
			dy2 = ne->y1 - ge->y3;

			/*
			 * check if we have a rather smooth joint at extremal
			 * point
			 */
			/* left or right extremal point */
			if (abs(dx1) <= 4 && abs(dx2) <= 4
			    && dy1 != 0 && 5 * abs(dx1) / abs(dy1) == 0
			    && dy2 != 0 && 5 * abs(dx2) / abs(dy2) == 0
			    && (ge->y3 < ge->prev->y3 && ne->y3 < ge->y3
				|| ge->y3 > ge->prev->y3 && ne->y3 > ge->y3)
			  && (ge->x3 - ge->prev->x3) * (ne->x3 - ge->x3) < 0
				) {
				dir = getcvdir(ge);
				ge->x2 += dx1;
				dx1 = 0;
				fixcvdir(ge, dir);
				dir = getcvdir(ne);
				ne->x1 -= dx2;
				dx2 = 0;
				fixcvdir(ne, dir);
			}
			/* top or down extremal point */
			else if (abs(dy1) <= 4 && abs(dy2) <= 4
				 && dx1 != 0 && 5 * abs(dy1) / abs(dx1) == 0
				 && dx2 != 0 && 5 * abs(dy2) / abs(dx2) == 0
				 && (ge->x3 < ge->prev->x3 && ne->x3 < ge->x3
				|| ge->x3 > ge->prev->x3 && ne->x3 > ge->x3)
				 && (ge->y3 - ge->prev->y3) * (ne->y3 - ge->y3) < 0
				) {
				dir = getcvdir(ge);
				ge->y2 += dy1;
				dy1 = 0;
				fixcvdir(ge, dir);
				dir = getcvdir(ne);
				ne->y1 -= dy2;
				dy2 = 0;
				fixcvdir(ne, dir);
			}
			/* or may be we just have a smooth junction */
			else if (dx1 * dx2 >= 0 && dy1 * dy2 >= 0
				 && 10 * abs(k = abs(dx1 * dy2) - abs(dy1 * dx2)) < (abs(dx1 * dy2) + abs(dy1 * dx2))) {
				int             tries[6][4];
				int             results[6];
				int             i, b;

				/* build array of changes we are going to try */
				/* uninitalized entries are 0 */
				if (k > 0) {
					static int      t1[6][4] = {
						{0, 0, 0, 0},
						{-1, 0, 1, 0},
						{-1, 0, 0, 1},
						{0, -1, 1, 0},
						{0, -1, 0, 1},
					{-1, -1, 1, 1}};
					memcpy(tries, t1, sizeof tries);
				} else {
					static int      t1[6][4] = {
						{0, 0, 0, 0},
						{1, 0, -1, 0},
						{1, 0, 0, -1},
						{0, 1, -1, 0},
						{0, 1, 0, -1},
					{1, 1, -1, -1}};
					memcpy(tries, t1, sizeof tries);
				}

				/* now try the changes */
				results[0] = abs(k);
				for (i = 1; i < 6; i++) {
					results[i] = abs((abs(dx1) + tries[i][0]) * (abs(dy2) + tries[i][1]) -
							 (abs(dy1) + tries[i][2]) * (abs(dx2) + tries[i][3]));
				}

				/* and find the best try */
				k = abs(k);
				b = 0;
				for (i = 1; i < 6; i++)
					if (results[i] < k) {
						k = results[i];
						b = i;
					}
				/* and finally apply it */
				if (dx1 < 0)
					tries[b][0] = -tries[b][0];
				if (dy2 < 0)
					tries[b][1] = -tries[b][1];
				if (dy1 < 0)
					tries[b][2] = -tries[b][2];
				if (dx2 < 0)
					tries[b][3] = -tries[b][3];

				dir = getcvdir(ge);
				ge->x2 -= tries[b][0];
				ge->y2 -= tries[b][2];
				fixcvdir(ge, dir);
				dir = getcvdir(ne);
				ne->x1 += tries[b][3];
				ne->y1 += tries[b][1];
				fixcvdir(ne, dir);
			}
		}
	}
}

/* debugging: print out stems of a glyph */
void
debugstems(
	   char *name,
	   STEM * hstems,
	   int nhs,
	   STEM * vstems,
	   int nvs
)
{
	int             i;

	fprintf(pfa_file, "%% %s\n", name);
	fprintf(pfa_file, "%% %d horizontal stems:\n", nhs);
	for (i = 0; i < nhs; i++)
		fprintf(pfa_file, "%% %3d    %d (%d...%d) %c %c%c%c%c\n", i, hstems[i].value,
			hstems[i].from, hstems[i].to,
			((hstems[i].flags & ST_UP) ? 'U' : 'D'),
			((hstems[i].flags & ST_END) ? 'E' : '-'),
			((hstems[i].flags & ST_FLAT) ? 'F' : '-'),
			((hstems[i].flags & ST_ZONE) ? 'Z' : ' '),
			((hstems[i].flags & ST_TOPZONE) ? 'T' : ' '));
	fprintf(pfa_file, "%% %d vertical stems:\n", nvs);
	for (i = 0; i < nvs; i++)
		fprintf(pfa_file, "%% %3d    %d (%d...%d) %c %c%c\n", i, vstems[i].value,
			vstems[i].from, vstems[i].to,
			((vstems[i].flags & ST_UP) ? 'U' : 'D'),
			((vstems[i].flags & ST_END) ? 'E' : '-'),
			((vstems[i].flags & ST_FLAT) ? 'F' : '-'));
}

/* add pseudo-stems for the limits of the Blue zones to the stem array */
int
addbluestems(
	STEM *s,
	int n
)
{
	int i;

	for(i=0; i<nblues && i<2; i+=2) { /* baseline */
		s[n].value=bluevalues[i];
		s[n].flags=ST_UP|ST_ZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i;
		n++;
		s[n].value=bluevalues[i+1];
		s[n].flags=ST_ZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i+1;
		n++;
	}
	for(i=2; i<nblues; i+=2) { /* top zones */
		s[n].value=bluevalues[i];
		s[n].flags=ST_UP|ST_ZONE|ST_TOPZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i;
		n++;
		s[n].value=bluevalues[i+1];
		s[n].flags=ST_ZONE|ST_TOPZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i+1;
		n++;
	}
	for(i=0; i<notherb; i+=2) { /* bottom zones */
		s[n].value=otherblues[i];
		s[n].flags=ST_UP|ST_ZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i+nblues;
		n++;
		s[n].value=otherblues[i+1];
		s[n].flags=ST_ZONE;
		/* don't overlap with anything */
		s[n].origin=s[n].from=s[n].to= -10000+i+1+nblues;
		n++;
	}
	return n;
}

/* sort stems in array */
void
sortstems(
	  STEM * s,
	  int n
)
{
	int             i, j;
	STEM            x;


	/* a simple sorting */
	/* hm, the ordering criteria are not quite simple :-) 
	 * if the values are tied
	 * ST_UP always goes under not ST_UP
	 * ST_ZONE goes on the most outer side
	 * ST_END goes towards inner side after ST_ZONE
	 * ST_FLAT goes on the inner side
	 */

	for (i = 0; i < n; i++)
		for (j = i + 1; j < n; j++) {
			if(s[i].value < s[j].value)
				continue;
			if(s[i].value == s[j].value) {
				if( (s[i].flags & ST_UP) < (s[j].flags & ST_UP) )
					continue;
				if( (s[i].flags & ST_UP) == (s[j].flags & ST_UP) ) {
					if( s[i].flags & ST_UP ) {
						if(
						(s[i].flags & (ST_ZONE|ST_FLAT|ST_END) ^ ST_FLAT)
							>
						(s[j].flags & (ST_ZONE|ST_FLAT|ST_END) ^ ST_FLAT)
						)
							continue;
					} else {
						if(
						(s[i].flags & (ST_ZONE|ST_FLAT|ST_END) ^ ST_FLAT)
							<
						(s[j].flags & (ST_ZONE|ST_FLAT|ST_END) ^ ST_FLAT)
						)
							continue;
					}
				}
			}
			x = s[j];
			s[j] = s[i];
			s[i] = x;
		}
}

/* check whether two stem borders overlap */

int
stemoverlap(
	    STEM * s1,
	    STEM * s2
)
{
	int             result;

	if (s1->from <= s2->from && s1->to >= s2->from
	    || s2->from <= s1->from && s2->to >= s1->from)
		result = 1;
	else
		result = 0;

	if (ISDBG(STEMOVERLAP))
		fprintf(pfa_file, "%% overlap %d(%d..%d)x%d(%d..%d)=%d\n",
			s1->value, s1->from, s1->to, s2->value, s2->from, s2->to, result);
	return result;
}

/* 
 * check if the stem [border] is in an appropriate blue zone
 * (currently not used)
 */

int
steminblue(
	STEM *s
)
{
	int i, val;

	val=s->value;
	if(s->flags & ST_UP) {
		/* painted size up, look at lower zones */
		if(nblues>=2 && val>=bluevalues[0] && val<=bluevalues[1] )
			return 1;
		for(i=0; i<notherb; i++) {
			if( val>=otherblues[i] && val<=otherblues[i+1] )
				return 1;
		}
	} else {
		/* painted side down, look at upper zones */
		for(i=2; i<nblues; i++) {
			if( val>=bluevalues[i] && val<=bluevalues[i+1] )
				return 1;
		}
	}

	return 0;
}

/* mark the outermost stem [borders] in the blue zones */

void
markbluestems(
	STEM *s,
	int nold
)
{
	int i, j, a, b, c;
	/*
	 * traverse the list of Blue Values, mark the lowest upper
	 * stem in each bottom zone and the topmost lower stem in
	 * each top zone with ST_BLUE
	 */

	/* top zones */
	for(i=2; i<nblues; i+=2) {
		a=bluevalues[i]; b=bluevalues[i+1];
		if(ISDBG(BLUESTEMS))
			fprintf(pfa_file, "%% looking at blue zone %d...%d\n", a, b);
		for(j=nold-1; j>=0; j--) {
			if( s[j].flags & (ST_ZONE|ST_UP|ST_END) )
				continue;
			c=s[j].value;
			if(c<a) /* too low */
				break;
			if(c<=b) { /* found the topmost stem border */
				/* mark all the stems with the same value */
				if(ISDBG(BLUESTEMS))
					fprintf(pfa_file, "%% found D BLUE at %d\n", s[j].value);
				/* include ST_END values */
				while( s[j+1].value==c && (s[j+1].flags & ST_ZONE)==0 )
					j++;
				s[j].flags |= ST_BLUE;
				for(j--; j>=0 && s[j].value==c 
						&& (s[j].flags & (ST_UP|ST_ZONE))==0 ; j--)
					s[j].flags |= ST_BLUE;
				break;
			}
		}
	}
	/* baseline */
	if(nblues>=2) {
		a=bluevalues[0]; b=bluevalues[1];
		for(j=0; j<nold; j++) {
			if( (s[j].flags & (ST_ZONE|ST_UP|ST_END))!=ST_UP )
				continue;
			c=s[j].value;
			if(c>b) /* too high */
				break;
			if(c>=a) { /* found the lowest stem border */
				/* mark all the stems with the same value */
				if(ISDBG(BLUESTEMS))
					fprintf(pfa_file, "%% found U BLUE at %d\n", s[j].value);
				/* include ST_END values */
				while( s[j-1].value==c && (s[j-1].flags & ST_ZONE)==0 )
					j--;
				s[j].flags |= ST_BLUE;
				for(j++; j<nold && s[j].value==c
						&& (s[j].flags & (ST_UP|ST_ZONE))==ST_UP ; j++)
					s[j].flags |= ST_BLUE;
				break;
			}
		}
	}
	/* bottom zones: the logic is the same as for baseline */
	for(i=0; i<notherb; i+=2) {
		a=otherblues[i]; b=otherblues[i+1];
		for(j=0; j<nold; j++) {
			if( (s[j].flags & (ST_UP|ST_ZONE|ST_END))!=ST_UP )
				continue;
			c=s[j].value;
			if(c>b) /* too high */
				break;
			if(c>=a) { /* found the lowest stem border */
				/* mark all the stems with the same value */
				if(ISDBG(BLUESTEMS))
					fprintf(pfa_file, "%% found U BLUE at %d\n", s[j].value);
				/* include ST_END values */
				while( s[j-1].value==c && (s[j-1].flags & ST_ZONE)==0 )
					j--;
				s[j].flags |= ST_BLUE;
				for(j++; j<nold && s[j].value==c
						&& (s[j].flags & (ST_UP|ST_ZONE))==ST_UP ; j++)
					s[j].flags |= ST_BLUE;
				break;
			}
		}
	}
}

/* Eliminate invalid stems, join equivalent lines and remove nested stems
 * to build the main (non-substituted) set of stems.
 * XXX add consideration of the italic angle
 */
int
joinmainstems(
	  STEM * s,
	  int nold,
	  int useblues /* do we use the blue values ? */
)
{
#define MAX_STACK	1000
	STEM            stack[MAX_STACK];
	int             nstack = 0;
	int             sbottom = 0;
	int             nnew;
	int             i, j, k;
	int             a, b, c, w1, w2, w3;
	int             fw, fd;
	/*
	 * priority of the last found stem: 
	 * 0 - nothing found yet 
	 * 1 - has ST_END in it (one or more) 
	 * 2 - has no ST_END and no ST_FLAT, can override only one stem 
	 *     with priority 1 
	 * 3 - has no ST_END and at least one ST_FLAT, can override one 
	 *     stem with priority 2 or any number of stems with priority 1
	 * 4 (handled separately) - has ST_BLUE, can override anything
	 */
	int             readystem = 0;
	int             pri;
	int             nlps = 0;	/* number of non-committed
					 * lowest-priority stems */


	for (i = 0, nnew = 0; i < nold; i++) {
		if (s[i].flags & (ST_UP|ST_ZONE)) {
			if(s[i].flags & ST_BLUE) {
				/* we just HAVE to use this value */
				if (readystem)
					nnew += 2;
				readystem=0;

				/* remember the list of Blue zone stems with the same value */
				for(a=i, i++; i<nold && s[a].value==s[i].value
					&& (s[i].flags & ST_BLUE); i++)
					{}
				b=i; /* our range is a <= i < b */
				c= -1; /* index of our best guess up to now */
				pri=0;
				/* try to find a match, don't cross blue zones */
				for(; i<nold && (s[i].flags & ST_BLUE)==0; i++) {
					if(s[i].flags & ST_UP)
						if(s[i].flags & ST_TOPZONE)
							break;
						else
							continue;
					for(j=a; j<b; j++) {
						if(!stemoverlap(&s[j], &s[i]) )
							continue;
						/* consider priorities */
						if( ( (s[j].flags|s[i].flags) & (ST_FLAT|ST_END) )==ST_FLAT ) {
							c=i;
							goto bluematch;
						}
						if( ((s[j].flags|s[i].flags) & ST_END)==0 )  {
							if(pri < 2) {
								c=i; pri=2;
							}
						} else {
							if(pri == 0) {
								c=i; pri=1;
							}
						}
					}
				}
			bluematch:
				/* clean up the stack */
				nstack=sbottom=0;
				readystem=0;
				/* add this stem */
				s[nnew++]=s[a];
				if(c<0) { /* make one-dot-wide stem */
					if(nnew>=b) { /* have no free space */
						for(j=nold; j>=b; j--) /* make free space */
							s[j]=s[j-1];
						b++;
						nold++;
					}
					s[nnew]=s[a];
					s[nnew].flags &= ~(ST_UP|ST_BLUE);
					nnew++;
					i=b-1;
				} else {
					s[nnew++]=s[c];
					i=c; /* skip up to this point */
				}
				if (ISDBG(MAINSTEMS))
					fprintf(pfa_file, "%% +stem %d...%d U BLUE\n",
						s[nnew-2].value, s[nnew-1].value);
			} else {
				if (nstack >= MAX_STACK) {
					fprintf(stderr, "Warning: **** stem stack overflow ****\n");
					nstack = 0;
				}
				stack[nstack++] = s[i];
			}
		} else if(s[i].flags & ST_BLUE) {
			/* again, we just HAVE to use this value */
			if (readystem)
				nnew += 2;
			readystem=0;

			/* remember the list of Blue zone stems with the same value */
			for(a=i, i++; i<nold && s[a].value==s[i].value
				&& (s[i].flags & ST_BLUE); i++)
				{}
			b=i; /* our range is a <= i < b */
			c= -1; /* index of our best guess up to now */
			pri=0;
			/* try to find a match */
			for (i = nstack - 1; i >= 0; i--) {
				if( (stack[i].flags & ST_UP)==0 )
					if( (stack[i].flags & (ST_ZONE|ST_TOPZONE))==ST_ZONE )
						break;
					else
						continue;
				for(j=a; j<b; j++) {
					if(!stemoverlap(&s[j], &stack[i]) )
						continue;
					/* consider priorities */
					if( ( (s[j].flags|stack[i].flags) & (ST_FLAT|ST_END) )==ST_FLAT ) {
						c=i;
						goto bluedownmatch;
					}
					if( ((s[j].flags|stack[i].flags) & ST_END)==0 )  {
						if(pri < 2) {
							c=i; pri=2;
						}
					} else {
						if(pri == 0) {
							c=i; pri=1;
						}
					}
				}
			}
		bluedownmatch:
			/* if found no match make a one-dot-wide stem */
			if(c<0) {
				c=0;
				stack[0]=s[b-1];
				stack[0].flags |= ST_UP;
				stack[0].flags &= ~ST_BLUE;
			}
			/* remove all the stems conflicting with this one */
			readystem=0;
			for(j=nnew-2; j>=0; j-=2) {
				if (ISDBG(MAINSTEMS))
					fprintf(pfa_file, "%% ?stem %d...%d -- %d\n",
						s[j].value, s[j+1].value, stack[c].value);
				if(s[j+1].value < stack[c].value) /* no conflict */
					break;
				if(s[j].flags & ST_BLUE) {
					/* oops, we don't want to spoil other blue zones */
					stack[c].value=s[j+1].value+1;
					break;
				}
				if( (s[j].flags|s[j+1].flags) & ST_END ) {
					if (ISDBG(MAINSTEMS))
						fprintf(pfa_file, "%% -stem %d...%d p=1\n",
							s[j].value, s[j+1].value);
					continue; /* pri==1, silently discard it */
				}
				/* we want to discard no nore than 2 stems of pri>=2 */
				if( ++readystem > 2 ) {
					/* change our stem to not conflict */
					stack[c].value=s[j+1].value+1;
					break;
				} else {
					if (ISDBG(MAINSTEMS))
						fprintf(pfa_file, "%% -stem %d...%d p>=2\n",
							s[j].value, s[j+1].value);
					continue;
				}
			}
			nnew=j+2;
			/* add this stem */
			if(nnew>=b-1) { /* have no free space */
				for(j=nold; j>=b-1; j--) /* make free space */
					s[j]=s[j-1];
				b++;
				nold++;
			}
			s[nnew++]=stack[c];
			s[nnew++]=s[b-1];
			/* clean up the stack */
			nstack=sbottom=0;
			readystem=0;
			/* set the next position to search */
			i=b-1;
			if (ISDBG(MAINSTEMS))
				fprintf(pfa_file, "%% +stem %d...%d D BLUE\n",
					s[nnew-2].value, s[nnew-1].value);
		} else if (nstack > 0) {

			/*
			 * check whether our stem overlaps with anything in
			 * stack
			 */
			for (j = nstack - 1; j >= sbottom; j--) {
				if (s[i].value <= stack[j].value)
					break;
				if (stack[j].flags & ST_ZONE)
					continue;

				if ((s[i].flags & ST_END)
				    || (stack[j].flags & ST_END))
					pri = 1;
				else if ((s[i].flags & ST_FLAT)
					 || (stack[j].flags & ST_FLAT))
					pri = 3;
				else
					pri = 2;

				if (pri < readystem && s[nnew + 1].value >= stack[j].value
				    || !stemoverlap(&stack[j], &s[i]))
					continue;

				if (readystem > 1 && s[nnew + 1].value < stack[j].value) {
					nnew += 2;
					readystem = 0;
					nlps = 0;
				}
				/*
				 * width of the previous stem (if it's
				 * present)
				 */
				w1 = s[nnew + 1].value - s[nnew].value;

				/* width of this stem */
				w2 = s[i].value - stack[j].value;

				if (readystem == 0) {
					/* nothing yet, just add a new stem */
					s[nnew] = stack[j];
					s[nnew + 1] = s[i];
					readystem = pri;
					if (pri == 1)
						nlps = 1;
					else if (pri == 2)
						sbottom = j;
					else {
						sbottom = j + 1;
						while (sbottom < nstack
						       && stack[sbottom].value <= stack[j].value)
							sbottom++;
					}
					if (ISDBG(MAINSTEMS))
						fprintf(pfa_file, "%% +stem %d...%d p=%d n=%d\n",
							stack[j].value, s[i].value, pri, nlps);
				} else if (pri == 1) {
					if (stack[j].value > s[nnew + 1].value) {
						/*
						 * doesn't overlap with the
						 * previous one
						 */
						nnew += 2;
						nlps++;
						s[nnew] = stack[j];
						s[nnew + 1] = s[i];
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% +stem %d...%d p=%d n=%d\n",
								stack[j].value, s[i].value, pri, nlps);
					} else if (w2 < w1) {
						/* is narrower */
						s[nnew] = stack[j];
						s[nnew + 1] = s[i];
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% /stem %d...%d p=%d n=%d %d->%d\n",
								stack[j].value, s[i].value, pri, nlps, w1, w2);
					}
				} else if (pri == 2) {
					if (readystem == 2) {
						/* choose the narrower stem */
						if (w1 > w2) {
							s[nnew] = stack[j];
							s[nnew + 1] = s[i];
							sbottom = j;
							if (ISDBG(MAINSTEMS))
								fprintf(pfa_file, "%% /stem %d...%d p=%d n=%d\n",
									stack[j].value, s[i].value, pri, nlps);
						}
						/* else readystem==1 */
					} else if (stack[j].value > s[nnew + 1].value) {
						/*
						 * value doesn't overlap with
						 * the previous one
						 */
						nnew += 2;
						nlps = 0;
						s[nnew] = stack[j];
						s[nnew + 1] = s[i];
						sbottom = j;
						readystem = pri;
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% +stem %d...%d p=%d n=%d\n",
								stack[j].value, s[i].value, pri, nlps);
					} else if (nlps == 1
						   || stack[j].value > s[nnew - 1].value) {
						/*
						 * we can replace the top
						 * stem
						 */
						nlps = 0;
						s[nnew] = stack[j];
						s[nnew + 1] = s[i];
						readystem = pri;
						sbottom = j;
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% /stem %d...%d p=%d n=%d\n",
								stack[j].value, s[i].value, pri, nlps);
					}
				} else if (readystem == 3) {	/* that means also
								 * pri==3 */
					/* choose the narrower stem */
					if (w1 > w2) {
						s[nnew] = stack[j];
						s[nnew + 1] = s[i];
						sbottom = j + 1;
						while (sbottom < nstack
						       && stack[sbottom].value <= stack[j].value)
							sbottom++;
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% /stem %d...%d p=%d n=%d\n",
								stack[j].value, s[i].value, pri, nlps);
					}
				} else if (pri == 3) {
					/*
					 * we can replace as many stems as
					 * neccessary
					 */
					nnew += 2;
					while (nnew > 0 && s[nnew - 1].value >= stack[j].value) {
						nnew -= 2;
						if (ISDBG(MAINSTEMS))
							fprintf(pfa_file, "%% -stem %d..%d\n",
								s[nnew].value, s[nnew + 1].value);
					}
					nlps = 0;
					s[nnew] = stack[j];
					s[nnew + 1] = s[i];
					readystem = pri;
					sbottom = j + 1;
					while (sbottom < nstack
					       && stack[sbottom].value <= stack[j].value)
						sbottom++;
					if (ISDBG(MAINSTEMS))
						fprintf(pfa_file, "%% +stem %d...%d p=%d n=%d\n",
							stack[j].value, s[i].value, pri, nlps);
				}
			}
		}
	}
	if (readystem)
		nnew += 2;

	/* change the 1-pixel-wide stems to 20-pixel-wide stems if possible 
	 * the constant 20 is recommended in the Type1 manual 
	 */
	if(useblues) {
		for(i=0; i<nnew; i+=2) {
			if(s[i].value != s[i+1].value)
				continue;
			if( ((s[i].flags ^ s[i+1].flags) & ST_BLUE)==0 )
				continue;
			if( s[i].flags & ST_BLUE ) {
				if(nnew>i+2 && s[i+2].value<s[i].value+22)
					s[i+1].value=s[i+2].value-2; /* compensate for fuzziness */
				else
					s[i+1].value+=20;
			} else {
				if(i>0 && s[i-1].value>s[i].value-22)
					s[i].value=s[i-1].value+2; /* compensate for fuzziness */
				else
					s[i].value-=20;
			}
		}
	}
	/* make sure that no stem it stretched between
	 * a top zone and a bottom zone
	 */
	if(useblues) {
		for(i=0; i<nnew; i+=2) {
			a=10000; /* lowest border of top zone crosing the stem */
			b= -10000; /* highest border of bottom zone crossing the stem */

			for(j=2; j<nblues; j++) {
				c=bluevalues[j];
				if( c>=s[i].value && c<=s[i+1].value && c<a )
					a=c;
			}
			if(nblues>=2) {
				c=bluevalues[1];
				if( c>=s[i].value && c<=s[i+1].value && c>b )
					b=c;
			}
			for(j=1; j<notherb; j++) {
				c=otherblues[j];
				if( c>=s[i].value && c<=s[i+1].value && c>b )
					b=c;
			}
			if( a!=10000 && b!= -10000 ) { /* it is stretched */
				/* split the stem into 2 ghost stems */
				for(j=nnew+1; j>i+1; j--) /* make free space */
					s[j]=s[j-2];
				nnew+=2;

				if(s[i].value+22 >= a)
					s[i+1].value=a-2; /* leave space for fuzziness */
				else
					s[i+1].value=s[i].value+20;

				if(s[i+3].value-22 <= b)
					s[i+2].value=b+2; /* leave space for fuzziness */
				else
					s[i+2].value=s[i+3].value-20;

				i+=2;
			}
		}
	}
	/* look for triple stems */
	for (i = 0; i < nnew; i += 2) {
		if (nnew - i >= 6) {
			a = s[i].value + s[i + 1].value;
			b = s[i + 2].value + s[i + 3].value;
			c = s[i + 4].value + s[i + 5].value;

			w1 = s[i + 1].value - s[i].value;
			w2 = s[i + 3].value - s[i + 2].value;
			w3 = s[i + 5].value - s[i + 4].value;

			fw = w3 - w1;	/* fuzz in width */
			fd = ((c - b) - (b - a));	/* fuzz in distance
							 * (doubled) */

			/* we are able to handle some fuzz */
			/*
			 * it doesn't hurt if the declared stem is a bit
			 * narrower than actual unless it's an edge in
			 * a blue zone
			 */
			if (abs(abs(fd) - abs(fw)) * 5 < w2
			    && abs(fw) * 20 < (w1 + w3)) {	/* width dirrerence <10% */

				if(useblues) { /* check that we don't disturb any blue stems */
					j=c; k=a;
					if (fw > 0) {
						if (fd > 0) {
							if( s[i+5].flags & ST_BLUE )
								continue;
							j -= fw;
						} else {
							if( s[i+4].flags & ST_BLUE )
								continue;
							j += fw;
						}
					} else if(fw < 0) {
						if (fd > 0) {
							if( s[i+1].flags & ST_BLUE )
								continue;
							k -= fw;
						} else {
							if( s[i].flags & ST_BLUE )
								continue;
							k += fw;
						}
					}
					pri = ((j - b) - (b - k));

					if (pri > 0) {
						if( s[i+2].flags & ST_BLUE )
							continue;
					} else if(pri < 0) {
						if( s[i+3].flags & ST_BLUE )
							continue;
					}
				}

				/*
				 * first fix up the width of 1st and 3rd
				 * stems
				 */
				if (fw > 0) {
					if (fd > 0) {
						s[i + 5].value -= fw;
						c -= fw;
					} else {
						s[i + 4].value += fw;
						c += fw;
					}
				} else {
					if (fd > 0) {
						s[i + 1].value -= fw;
						a -= fw;
					} else {
						s[i].value += fw;
						a += fw;
					}
				}
				fd = ((c - b) - (b - a));

				if (fd > 0) {
					s[i + 2].value += abs(fd) / 2;
				} else {
					s[i + 3].value -= abs(fd) / 2;
				}

				s[i].flags |= ST_3;
				i += 4;
			}
		}
	}

	return (nnew & ~1);	/* number of lines must be always even */
}

/*
 * these macros and function allow to set the base stem,
 * check that it's not empty and subtract another stem
 * from the base stem (possibly dividing it into multiple parts)
 */

/* pairs for pieces of the base stem */
static short xbstem[MAX_STEMS*2]; 
/* index of the last point */
static int xblast= -1; 

#define setbasestem(from, to) \
	(xbstem[0]=from, xbstem[1]=to, xblast=1)
#define isbaseempty()	(xblast<=0)

/* returns 1 if was overlapping, 0 otherwise */
static int
subfrombase(
	int from,
	int to
) 
{
	int a, b;
	int i, j;

	if(isbaseempty())
		return 0;

	/* handle the simple case simply */
	if(from > xbstem[xblast] || to < xbstem[0])
		return 0;

	/* the binary search may be more efficient */
	/* but for now the linear search is OK */
	for(b=1; from > xbstem[b]; b+=2) {} /* result: from <= xbstem[b] */
	for(a=xblast-1; to < xbstem[a]; a-=2) {} /* result: to >= xbstem[a] */

	/* now the interesting examples are:
	 * (it was hard for me to understand, so I looked at the examples)
	 * 1
	 *     a|-----|          |-----|b   |-----|     |-----|
	 *              f|-----|t
	 * 2
	 *     a|-----|b         |-----|    |-----|     |-----|
	 *      f|--|t
	 * 3
	 *     a|-----|b         |-----|    |-----|     |-----|
	 *           f|-----|t
	 * 4
	 *      |-----|b        a|-----|    |-----|     |-----|
	 *          f|------------|t
	 * 5
	 *      |-----|          |-----|b   |-----|    a|-----|
	 *                   f|-----------------------------|t
	 * 6
	 *      |-----|b         |-----|    |-----|    a|-----|
	 *   f|--------------------------------------------------|t
	 * 7
	 *      |-----|b         |-----|   a|-----|     |-----|
	 *          f|--------------------------|t
	 */

	if(a < b-1) /* hits a gap  - example 1 */
		return 0;

	/* now the subtraction itself */

	if(a==b-1 && from > xbstem[a] && to < xbstem[b]) {
		/* overlaps with only one subrange and splits it - example 2 */
		j=xblast; i=(xblast+=2);
		while(j>=b)
			xbstem[i--]=xbstem[j--];
		xbstem[b]=from-1;
		xbstem[b+1]=to+1;
		return 1;
	/* becomes
	 * 2a
	 *     a|b   ||          |-----|    |-----|     |-----|
	 *      f|--|t
	 */
	}

	if(xbstem[b-1] < from) {
		/* cuts the back of this subrange - examples 3, 4, 7 */
		xbstem[b] = from-1;
		b+=2;
	/* becomes
	 * 3a
	 *     a|----|           |-----|b   |-----|     |-----|
	 *           f|-----|t
	 * 4a
	 *      |---|           a|-----|b   |-----|     |-----|
	 *          f|------------|t
	 * 7a
	 *      |---|            |-----|b  a|-----|     |-----|
	 *          f|--------------------------|t
	 */
	}

	if(xbstem[a+1] > to) {
		/* cuts the front of this subrange - examples 4a, 5, 7a */
		xbstem[a] = to+1;
		a-=2;
	/* becomes
	 * 4b
	 *     a|---|              |---|b   |-----|     |-----|
	 *          f|------------|t
	 * 5b
	 *      |-----|          |-----|b  a|-----|          ||
	 *                   f|-----------------------------|t
	 * 7b
	 *      |---|           a|-----|b        ||     |-----|
	 *          f|--------------------------|t
	 */
	}

	if(a < b-1) /* now after modification it hits a gap - examples 3a, 4b */
		return 1; /* because we have removed something */

	/* now remove the subranges completely covered by the new stem */
	/* examples 5b, 6, 7b */
	i=b-1; j=a+2;
	/* positioned as:
	 * 5b                    i                           j
	 *      |-----|          |-----|b  a|-----|          ||
	 *                   f|-----------------------------|t
	 * 6    i                                             xblast  j
	 *      |-----|b         |-----|    |-----|    a|-----|
	 *   f|--------------------------------------------------|t
	 * 7b                    i               j
	 *      |---|           a|-----|b        ||     |-----|
	 *          f|--------------------------|t
	 */
	while(j <= xblast)
		xbstem[i++]=xbstem[j++];
	xblast=i-1;
	return 1;
}

/* for debugging */
void
printbasestem(void)
{
	int i;

	printf("( ");
	for(i=0; i<xblast; i+=2)
		printf("%d-%d ", xbstem[i], xbstem[i+1]);
	printf(") %d\n", xblast);
}

/*
 * Join the stem borders to build the sets of substituted stems
 * XXX add consideration of the italic angle
 */
void
joinsubstems(
	  STEM * s,
	  short *pairs,
	  int nold,
	  int useblues /* do we use the blue values ? */
)
{
	int i, j, x;
	static unsigned char mx[MAX_STEMS][MAX_STEMS];

	/* we do the substituted groups of stems first
	 * and it looks like it's going to be REALLY SLOW 
	 * AND PAINFUL but let's bother about it later
	 */

	/* for the substituted stems we don't bother about [hv]stem3 -
	 * anyway the X11R6 rasterizer does not bother about hstem3
	 * at all and is able to handle only one global vstem3
	 * per glyph 
	 */

	/* clean the used part of matrix */
	for(i=0; i<nold; i++)
		for(j=0; j<nold; j++)
			mx[i][j]=0;

	/* build the matrix of stem pairs */
	for(i=0; i<nold; i++) {
		if( s[i].flags & ST_ZONE )
			continue;
		if(s[i].flags & ST_BLUE)
			mx[i][i]=1; /* allow to pair with itself if no better pair */
		if(s[i].flags & ST_UP) { /* the down-stems are already matched */
			setbasestem(s[i].from, s[i].to);
			for(j=i+1; j<nold; j++) {
				if(s[i].value==s[j].value
				|| s[j].flags & ST_ZONE ) {
					continue;
				}
				x=subfrombase(s[j].from, s[j].to);

				if(s[j].flags & ST_UP) /* match only up+down pairs */
					continue;

				mx[i][j]=mx[j][i]=x;

				if(isbaseempty()) /* nothing else to do */
					break;
			}
		}
	}

	if(ISDBG(SUBSTEMS)) {
		fprintf(pfa_file, "%%     ");
		for(j=0; j<nold; j++)
			putc( j%10==0 ? '0'+(j/10)%10 : ' ', pfa_file);
		fprintf(pfa_file, "\n%%     ");
		for(j=0; j<nold; j++)
			putc('0'+j%10, pfa_file);
		putc('\n', pfa_file);
		for(i=0; i<nold; i++) {
			fprintf(pfa_file, "%% %3d ",i);
			for(j=0; j<nold; j++)
				putc( mx[i][j] ? 'X' : '.', pfa_file);
			putc('\n', pfa_file);
		}
	}

	/* now use the matrix to find the best pair for each stem */
	for(i=0; i<nold; i++) {
		int pri, lastpri, v, f;

		x= -1; /* best pair: none */
		lastpri=0;

		v=s[i].value;
		f=s[i].flags;

		if(f & ST_ZONE) {
			pairs[i]= -1;
			continue;
		}

		if(f & ST_UP) {
			for(j=i+1; j<nold; j++) {
				if(mx[i][j]==0)
					continue;

				if( (f | s[j].flags) & ST_END )
					pri=1;
				else if( (f | s[j].flags) & ST_FLAT )
					pri=3;
				else
					pri=2;

				if(lastpri==0
				|| pri > lastpri  
				&& ( lastpri==1 || s[j].value-v<20 || (s[x].value-v)*2 >= s[j].value-v ) ) {
					lastpri=pri;
					x=j;
				}
			}
		} else {
			for(j=i-1; j>=0; j--) {
				if(mx[i][j]==0)
					continue;

				if( (f | s[j].flags) & ST_END )
					pri=1;
				else if( (f | s[j].flags) & ST_FLAT )
					pri=3;
				else
					pri=2;

				if(lastpri==0
				|| pri > lastpri  
				&& ( lastpri==1 || v-s[j].value<20 || (v-s[x].value)*2 >= v-s[j].value ) ) {
					lastpri=pri;
					x=j;
				}
			}
		}
		if(x== -1 && mx[i][i])
			pairs[i]=i; /* a special case */
		else
			pairs[i]=x;
	}

	if(ISDBG(SUBSTEMS)) {
		for(i=0; i<nold; i++) {
			j=pairs[i];
			if(j>0)
				fprintf(pfa_file, "%% %d...%d  (%d x %d)\n", s[i].value, s[j].value, i, j);
		}
	}
}

/* 
 * Find the best stem in the array at the specified (value, origin) .
 * Returns its index in the array sp, -1 means "none".
 * prevbest is the result for the other end of the line, we must 
 * find something better than it or leave it as it is.
 */
static int
findstemat(
	int value,
	int origin,
	STEM *sp,
	short *pairs,
	int ns,
	int prevbest /* -1 means "none" */
)
{
	int i, min, max;
	int v, si;
	int pri, prevpri; /* priority, 0 = has ST_END, 1 = no ST_END */
	int wd, prevwd; /* stem width */

	si= -1; /* nothing yet */

	/* stems are ordered by value, binary search */
	min=0; max=ns; /* min <= i < max */
	while( min < max ) {
		i=(min+max)/2;
		v=sp[i].value;
		if(v<value)
			min=i+1;
		else if(v>value)
			max=i;
		else {
			si=i; /* temporary value */
			break;
		}
	}

	if( si < 0 ) /* found nothing this time */
		return prevbest;

	/* find the priority of the prevbest */
	/* we expect that prevbest has a pair */
	if(prevbest>=0) {
		i=pairs[prevbest];
		prevpri=1;
		if( (sp[prevbest].flags | sp[i].flags) & ST_END )
			prevpri=0; 
		prevwd=abs(sp[i].value-value);
	}

	/* stems are not ordered by origin, so now do the linear search */

	while( si>0 && sp[si-1].value==value ) /* find the first one */
		si--;

	for(; si<ns && sp[si].value==value; si++) {
		if(sp[si].origin != origin)
			continue;
		i=pairs[si]; /* the other side of this stem */
		if(i<0)
			continue; /* oops, no other side */
		pri=1;
		if( (sp[si].flags | sp[i].flags) & ST_END )
			pri=0;
		wd=abs(sp[i].value-value);
		if( prevbest == -1 || pri >prevpri 
		|| pri==prevpri && prevwd==0 || wd!=0 && wd<prevwd ) {
			prevbest=si;
			prevpri=pri;
			prevwd=wd;
			continue;
		}
	}

	return prevbest;
}

/* add the substems for one glyph entry 
 * (called from groupsubstems())
 * returns 0 if all OK, 1 if too many groups
 */

static int
gssentry( /* crazy number of parameters */
	GENTRY *ge,
	STEM *hs, /* horizontal stems, sorted by value */
	short *hpairs,
	int nhs,
	STEM *vs, /* vertical stems, sorted by value */
	short *vpairs,
	int nvs,
	STEMBOUNDS *s,
	short *egp,
	int *nextvsi, 
	int *nexthsi /* -2 means "check by yourself" */
) {
	enum {
		SI_VP,	/* vertical primary */
		SI_HP,	/* horizontal primary */
		SI_SIZE /* size of the array */
	};
	int si[SI_SIZE]; /* indexes of relevant stems */

	/* the bounds of the existing relevant stems */
	STEMBOUNDS r[ sizeof(si) / sizeof(si[0]) * 2 ];
	char rexpand; /* by how much we need to expand the group */
	int nr; /* and the number of them */

	/* yet more temporary storage */
	short lb, hb, isvert;
	int conflict, grp;
	int i, j, x, y;


	/* for each line or curve we try to find a horizontal and
	 * a vertical stem corresponding to its first point
	 * (corresponding to the last point of the previous
	 * glyph entry), because the directions of the lines
	 * will be eventually reversed and it will then become the last
	 * point. And the T1 rasterizer applies the hints to 
	 * the last point.
	 *
	 */

	/* start with the common part, the first point */
	x=ge->prev->x3;
	y=ge->prev->y3;

	if(*nextvsi == -2)
		si[SI_VP]=findstemat(x, y, vs, vpairs, nvs, -1);
	else {
		si[SI_VP]= *nextvsi; *nextvsi= -2;
	}
	if(*nexthsi == -2)
		si[SI_HP]=findstemat(y, x, hs, hpairs, nhs, -1);
	else {
		si[SI_HP]= *nexthsi; *nexthsi= -2;
	}

	/*
	 * For the horizontal lines we make sure that both
	 * ends of the line have the same horizontal stem,
	 * and the same thing for vertical lines and stems.
	 * In both cases we enforce the stem for the next entry.
	 * Otherwise unpleasant effects may arise.
	 */

	if(ge->type==GE_LINE) {
		if(ge->x3==x) { /* vertical line */
			*nextvsi=si[SI_VP]=findstemat(x, ge->y3, vs, vpairs, nvs, si[SI_VP]);
		} else if(ge->y3==y) { /* horizontal line */
			*nexthsi=si[SI_HP]=findstemat(y, ge->x3, hs, hpairs, nhs, si[SI_HP]);
		}
	}

	if(si[SI_VP]+si[SI_HP] == -2) /* no stems, leave it alone */
		return 0;

	/* build the array of relevant bounds */
	nr=0;
	for(i=0; i< sizeof(si) / sizeof(si[0]); i++) {
		STEM *sp;
		short *pairs;
		int step;
		int f;
		int nzones, firstzone, binzone, einzone;
		int btype, etype;

		if(si[i] < 0)
			continue;

		if(i<SI_HP) {
			r[nr].isvert=1; sp=vs; pairs=vpairs;
		} else {
			r[nr].isvert=0; sp=hs; pairs=hpairs;
		}

		r[nr].low=sp[ si[i] ].value;
		r[nr].high=sp[ pairs[ si[i] ] ].value;

		if(r[nr].low > r[nr].high) {
			j=r[nr].low; r[nr].low=r[nr].high; r[nr].high=j;
			step= -1;
		} else {
			step=1;
		}

		/* handle the interaction with Blue Zones */

		if(i>=SI_HP) { /* only for horizontal stems */
			if(si[i]==pairs[si[i]]) {
				/* special case, the outermost stem in the
				 * Blue Zone without a pair, simulate it to 20-pixel
				 */
				if(sp[ si[i] ].flags & ST_UP) {
					r[nr].high+=20;
					for(j=si[i]+1; j<nhs; j++)
						if( (sp[j].flags & (ST_ZONE|ST_TOPZONE))
						== (ST_ZONE|ST_TOPZONE) ) {
							if(r[nr].high > sp[j].value-2)
								r[nr].high=sp[j].value-2;
							break;
						}
				} else {
					r[nr].low-=20;
					for(j=si[i]-1; j>=0; j--)
						if( (sp[j].flags & (ST_ZONE|ST_TOPZONE))
						== (ST_ZONE) ) {
							if(r[nr].low < sp[j].value+2)
								r[nr].low=sp[j].value+2;
							break;
						}
				}
			}

			/* check that the stem borders don't end up in
			 * different Blue Zones */
			f=sp[ si[i] ].flags;
			nzones=0; einzone=binzone=0;
			for(j=si[i]; j!=pairs[ si[i] ]; j+=step) {
				if( (sp[j].flags & ST_ZONE)==0 )
					continue;
				/* if see a zone border going in the same direction */
				if( ((f ^ sp[j].flags) & ST_UP)==0 ) {
					if( ++nzones == 1 ) {
						firstzone=sp[j].value; /* remember the first one */
						etype=sp[j].flags & ST_TOPZONE;
					}
					einzone=1;

				} else { /* the opposite direction */
					if(nzones==0) { /* beginning is in a blue zone */
						binzone=1;
						btype=sp[j].flags & ST_TOPZONE;
					}
					einzone=0;
				}
			}

			/* beginning and end are in Blue Zones of different types */
			if( binzone && einzone && (btype ^ etype)!=0 ) {
				if( sp[si[i]].flags & ST_UP ) {
					if(firstzone > r[nr].low+22)
						r[nr].high=r[nr].low+20;
					else
						r[nr].high=firstzone-2;
				} else {
					if(firstzone < r[nr].high-22)
						r[nr].low=r[nr].high-20;
					else
						r[nr].low=firstzone+2;
				}
			}
		}

		if(ISDBG(SUBSTEMS))
			fprintf(pfa_file, "%%  at(%d,%d)[%d,%d] %d..%d %c (%d x %d)\n", x, y, i, nr,
				r[nr].low, r[nr].high, r[nr].isvert ? 'v' : 'h',
				si[i], pairs[si[i]]);

		nr++;
	}

	/* now try to find a group */
	conflict=0; /* no conflicts found yet */
	for(j=0; j<nr; j++)
		r[j].already=0;
	for(i=0, grp=0; i<egp[NSTEMGRP-1]; i++) {
		if(i == egp[grp]) { /* checked all stems in a group */
			if(conflict) {
				grp++; conflict=0; /* check the next group */
				for(j=0; j<nr; j++)
					r[j].already=0;
			} else
				break; /* insert into this group */
		}

		lb=s[i].low; hb=s[i].high; isvert=s[i].isvert;
		for(j=0; j<nr; j++)
			if( r[j].isvert==isvert  /* intersects */
			&& r[j].low <= hb && r[j].high >= lb ) {
				if( r[j].low == lb && r[j].high == hb ) /* coincides */
					r[j].already=1;
				else
					conflict=1;
			}

		if(conflict) 
			i=egp[grp]-1; /* fast forward to the next group */
	}

	/* do we have any empty group ? */
	if(conflict && grp < NSTEMGRP-1) {
		grp++; conflict=0;
		for(j=0; j<nr; j++)
			r[j].already=0;
	}

	if(conflict) { /* oops, can't find any group to fit */
		return 1;
	}

	/* OK, add stems to this group */

	rexpand = nr;
	for(j=0; j<nr; j++)
		rexpand -= r[j].already;

	if(rexpand > 0) {
		for(i=egp[NSTEMGRP-1]-1; i>=egp[grp]; i--)
			s[i+rexpand]=s[i];
		for(i=0; i<nr; i++)
			if(!r[i].already)
				s[egp[grp]++]=r[i];
		for(i=grp+1; i<NSTEMGRP; i++)
			egp[i]+=rexpand;
	}

	ge->stemid=grp;
	return 0;
}

/*
 * Create the groups of substituted stems from the list.
 * Each group will be represented by a subroutine in the Subs
 * array.
 */

static void
groupsubstems(
	GLYPH *g,
	STEM *hs, /* horizontal stems, sorted by value */
	short *hpairs,
	int nhs,
	STEM *vs, /* vertical stems, sorted by value */
	short *vpairs,
	int nvs
)
{
	GENTRY *ge;
	int i, j, x, y;

	/* temporary storage */
	STEMBOUNDS s[MAX_STEMS*2];
	/* indexes in there, pointing past the end each stem group */
	short egp[NSTEMGRP]; 

	int nextvsi, nexthsi; /* -2 means "check by yourself" */

	for(i=0; i<NSTEMGRP; i++)
		egp[i]=0;

	nextvsi=nexthsi= -2; /* processed no horiz/vert line */

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if(ge->type!=GE_LINE && ge->type!=GE_CURVE) {
			nextvsi=nexthsi= -2; /* next path is independent */
			continue;
		}

		if( gssentry(ge, hs, hpairs, nhs, vs, vpairs, nvs, s, egp, &nextvsi, &nexthsi) ) {
			fprintf(stderr, "*** glyph %s requires over %d hint subroutines, ignored them\n",
				g->name, NSTEMGRP);
			/* it's better to have no substituted hints at all than have only part */
			for (ge = g->entries; ge != 0; ge = ge->next)
				ge->stemid= -1;
			g->nsg=0; /* just to be safe, already is 0 by initialization */
			return;
		}

		/*
		 * handle the last vert/horiz line of the path specially,
		 * correct the hint for the first entry of the path
		 */
		if(ge->first && (nextvsi != -2 || nexthsi != -2) ) {
			if( gssentry(ge->first, hs, hpairs, nhs, vs, vpairs, nvs, s, egp, &nextvsi, &nexthsi) ) {
				fprintf(stderr, "*** glyph %s requires over %d hint subroutines, ignored them\n",
					g->name, NSTEMGRP);
				/* it's better to have no substituted hints at all than have only part */
				for (ge = g->entries; ge != 0; ge = ge->next)
					ge->stemid= -1;
				g->nsg=0; /* just to be safe, already is 0 by initialization */
				return;
			}
		}

	}

	/* find the index of the first empty group - same as the number of groups */
	if(egp[0]>0) {
		for(i=1; i<NSTEMGRP && egp[i]!=egp[i-1]; i++)
			{}
		g->nsg=i;
	} else
		g->nsg=0;

	if(ISDBG(SUBSTEMS)) {
		fprintf(pfa_file, "%% %d substem groups (%d %d %d)\n", g->nsg,
			g->nsg>1 ? egp[g->nsg-2] : -1,
			g->nsg>0 ? egp[g->nsg-1] : -1,
			g->nsg<NSTEMGRP ? egp[g->nsg] : -1 );
		j=0;
		for(i=0; i<g->nsg; i++) {
			fprintf(pfa_file, "%% grp %3d:      ", i);
			for(; j<egp[i]; j++) {
				fprintf(pfa_file, " %4d...%-4d %c  ", s[j].low, s[j].high,
					s[j].isvert ? 'v' : 'h');
			}
			fprintf(pfa_file, "\n");
		}
	}

	if(g->nsg==1) { /* it would be the same as the main stems */
		/* so erase it */
		for (ge = g->entries; ge != 0; ge = ge->next)
			ge->stemid= -1;
		g->nsg=0;
	}

	if(g->nsg>0) {
		if( (g->nsbs=malloc(g->nsg * sizeof (egp[0]))) == 0 ) {
			fprintf(stderr, "**** not enough memory for substituted stems ****\n");
			exit(1);
		}
		memmove(g->nsbs, egp, g->nsg * sizeof(short));
		if( (g->sbstems=malloc(egp[g->nsg-1] * sizeof (s[0]))) == 0 ) {
			fprintf(stderr, "**** not enough memory for substituted stems ****\n");
			exit(1);
		}
		memmove(g->sbstems, s, egp[g->nsg-1] * sizeof(s[0]));
	}
}

void
buildstems(
	   GLYPH * g
)
{
	STEM            hs[MAX_STEMS], vs[MAX_STEMS];	/* temporary working
							 * storage */
	short	hs_pairs[MAX_STEMS], vs_pairs[MAX_STEMS]; /* best pairs for these stems */
	STEM           *sp;
	GENTRY         *ge, *nge, *pge;
	int             nx, ny;
	int ovalue;

	g->nhs = g->nvs = 0;

	/* first search the whole character for possible stem points */

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type == GE_CURVE) {

			/*
			 * SURPRISE! 
			 * We consider the stems bounded by the
			 * H/V ends of the curves as flat ones.
			 *
			 * But we don't include the point on the
			 * other end into the range.
			 */

			/* first check the beginning of curve */
			/* if it is horizontal, add a hstem */
			if (ge->y1 == ge->prev->y3) {
				hs[g->nhs].value = ge->y1;

				if (ge->x1 < ge->prev->x3)
					hs[g->nhs].flags = ST_FLAT | ST_UP;
				else
					hs[g->nhs].flags = ST_FLAT;

				hs[g->nhs].origin = ge->prev->x3;

				if (ge->x1 < ge->prev->x3) {
					hs[g->nhs].from = ge->x1+1;
					hs[g->nhs].to = ge->prev->x3;
					if(hs[g->nhs].from > hs[g->nhs].to)
						hs[g->nhs].from--;
				} else {
					hs[g->nhs].from = ge->prev->x3;
					hs[g->nhs].to = ge->x1-1;
					if(hs[g->nhs].from > hs[g->nhs].to)
						hs[g->nhs].to++;
				}
				if (ge->x1 != ge->prev->x3)
					g->nhs++;
			}
			/* if it is vertical, add a vstem */
			else if (ge->x1 == ge->prev->x3) {
				vs[g->nvs].value = ge->x1;

				if (ge->y1 > ge->prev->y3)
					vs[g->nvs].flags = ST_FLAT | ST_UP;
				else
					vs[g->nvs].flags = ST_FLAT;

				vs[g->nvs].origin = ge->prev->y3;

				if (ge->y1 < ge->prev->y3) {
					vs[g->nvs].from = ge->y1+1;
					vs[g->nvs].to = ge->prev->y3;
					if(vs[g->nvs].from > vs[g->nvs].to)
						vs[g->nvs].from--;
				} else {
					vs[g->nvs].from = ge->prev->y3;
					vs[g->nvs].to = ge->y1-1;
					if(vs[g->nvs].from > vs[g->nvs].to)
						vs[g->nvs].to++;
				}

				if (ge->y1 != ge->prev->y3)
					g->nvs++;
			}
			/* then check the end of curve */
			/* if it is horizontal, add a hstem */
			if (ge->y3 == ge->y2) {
				hs[g->nhs].value = ge->y3;

				if (ge->x3 < ge->x2)
					hs[g->nhs].flags = ST_FLAT | ST_UP;
				else
					hs[g->nhs].flags = ST_FLAT;

				hs[g->nhs].origin = ge->x3;

				if (ge->x3 < ge->x2) {
					hs[g->nhs].from = ge->x3;
					hs[g->nhs].to = ge->x2-1;
					if( hs[g->nhs].from > hs[g->nhs].to )
						hs[g->nhs].to++;
				} else {
					hs[g->nhs].from = ge->x2+1;
					hs[g->nhs].to = ge->x3;
					if( hs[g->nhs].from > hs[g->nhs].to )
						hs[g->nhs].from--;
				}

				if (ge->x3 != ge->x2)
					g->nhs++;
			}
			/* if it is vertical, add a vstem */
			else if (ge->x3 == ge->x2) {
				vs[g->nvs].value = ge->x3;

				if (ge->y3 > ge->y2)
					vs[g->nvs].flags = ST_FLAT | ST_UP;
				else
					vs[g->nvs].flags = ST_FLAT;

				vs[g->nvs].origin = ge->y3;

				if (ge->y3 < ge->y2) {
					vs[g->nvs].from = ge->y3;
					vs[g->nvs].to = ge->y2-1;
					if( vs[g->nvs].from > vs[g->nvs].to )
						vs[g->nvs].to++;
				} else {
					vs[g->nvs].from = ge->y2+1;
					vs[g->nvs].to = ge->y3;
					if( vs[g->nvs].from > vs[g->nvs].to )
						vs[g->nvs].from--;
				}

				if (ge->y3 != ge->y2)
					g->nvs++;
			} else {

				/*
				 * check the end of curve for a not smooth
				 * local extremum
				 */
				if (ge->first)
					nge = ge->first;
				else
					nge = ge->next;

				if (nge == 0)
					continue;
				else if (nge->type == GE_LINE) {
					nx = nge->x3;
					ny = nge->y3;
				} else if (nge->type == GE_CURVE) {
					nx = nge->x1;
					ny = nge->y1;
				} else
					continue;

				/* check for vertical extremums */
				if (ge->y3 > ge->y2 && ge->y3 > ny
				    || ge->y3 < ge->y2 && ge->y3 < ny) {
					hs[g->nhs].value = ge->y3;
					hs[g->nhs].from
						= hs[g->nhs].to
						= hs[g->nhs].origin = ge->x3;

					if (ge->x3 < ge->x2
					    || nx < ge->x3)
						hs[g->nhs].flags = ST_UP;
					else
						hs[g->nhs].flags = 0;

					if (ge->x3 != ge->x2 || nx != ge->x3)
						g->nhs++;
				}
				/*
				 * the same point may be both horizontal and
				 * vertical extremum
				 */
				/* check for horizontal extremums */
				if (ge->x3 > ge->x2 && ge->x3 > nx
				    || ge->x3 < ge->x2 && ge->x3 < nx) {
					vs[g->nvs].value = ge->x3;
					vs[g->nvs].from
						= vs[g->nvs].to
						= vs[g->nvs].origin = ge->y3;

					if (ge->y3 > ge->y2
					    || ny > ge->y3)
						vs[g->nvs].flags = ST_UP;
					else
						vs[g->nvs].flags = 0;

					if (ge->y3 != ge->y2 || ny != ge->y3)
						g->nvs++;
				}
			}

		} else if (ge->type == GE_LINE) {
			if (ge->first)
				nge = ge->first;
			else
				nge = ge->next;

			/* if it is horizontal, add a hstem */
			/* and the ends as vstems if they brace the line */
			if (ge->y3 == ge->prev->y3
			&& ge->x3 != ge->prev->x3) {
				hs[g->nhs].value = ge->y3;
				if (ge->x3 < ge->prev->x3) {
					hs[g->nhs].flags = ST_FLAT | ST_UP;
					hs[g->nhs].from = ge->x3;
					hs[g->nhs].to = ge->prev->x3;
				} else {
					hs[g->nhs].flags = ST_FLAT;
					hs[g->nhs].from = ge->prev->x3;
					hs[g->nhs].to = ge->x3;
				}
				hs[g->nhs].origin = ge->x3;

				pge = ge->prev;
				if (pge->type == GE_MOVE) {
					for (pge = ge; pge->first == 0; pge = pge->next) {
					}
				}
				/* add beginning as vstem */
				vs[g->nvs].value = pge->x3;
				vs[g->nvs].origin
					= vs[g->nvs].from
					= vs[g->nvs].to = pge->y3;

				if(pge->type==GE_CURVE)
					ovalue=pge->y2;
				else
					ovalue=pge->prev->y3;

				if (pge->y3 > ovalue)
					vs[g->nvs].flags = ST_UP | ST_END;
				else if (pge->y3 < ovalue)
					vs[g->nvs].flags = ST_END;
				else
					vs[g->nvs].flags = 0;

				if( vs[g->nvs].flags != 0 )
					g->nvs++;

				/* add end as vstem */
				vs[g->nvs].value = ge->x3;
				vs[g->nvs].origin
					= vs[g->nvs].from
					= vs[g->nvs].to = ge->y3;

				if(nge->type==GE_CURVE)
					ovalue=nge->y1;
				else
					ovalue=nge->y3;

				if (ovalue > ge->y3)
					vs[g->nvs].flags = ST_UP | ST_END;
				else if (ovalue < ge->y3)
					vs[g->nvs].flags = ST_END;
				else
					vs[g->nvs].flags = 0;

				if( vs[g->nvs].flags != 0 )
					g->nvs++;

				g->nhs++;
			}
			/* if it is vertical, add a vstem */
			/* and the ends as hstems if they brace the line  */
			else if (ge->x3 == ge->prev->x3 
			&& ge->y3 != ge->prev->y3) {
				vs[g->nvs].value = ge->x3;
				if (ge->y3 > ge->prev->y3) {
					vs[g->nvs].flags = ST_FLAT | ST_UP;
					vs[g->nvs].from = ge->prev->y3;
					vs[g->nvs].to = ge->y3;
				} else {
					vs[g->nvs].flags = ST_FLAT;
					vs[g->nvs].from = ge->y3;
					vs[g->nvs].to = ge->prev->y3;
				}
				vs[g->nvs].origin = ge->y3;

				pge = ge->prev;
				if (pge->type == GE_MOVE) {
					for (pge = ge; pge->first == 0; pge = pge->next) {
					}
				}
				/* add beginning as hstem */
				hs[g->nhs].value = pge->y3;
				hs[g->nhs].origin
					= hs[g->nhs].from
					= hs[g->nhs].to = pge->x3;

				if(pge->type==GE_CURVE)
					ovalue=pge->x2;
				else
					ovalue=pge->prev->x3;

				if (pge->x3 < ovalue)
					hs[g->nhs].flags = ST_UP | ST_END;
				else if (pge->x3 > ovalue)
					hs[g->nhs].flags = ST_END;
				else
					hs[g->nhs].flags = 0;

				if( hs[g->nhs].flags != 0 )
					g->nhs++;

				/* add end as hstem */
				hs[g->nhs].value = ge->y3;
				hs[g->nhs].origin
					= hs[g->nhs].from
					= hs[g->nhs].to = ge->x3;

				if(nge->type==GE_CURVE)
					ovalue=nge->x1;
				else
					ovalue=nge->x3;

				if (ovalue < ge->x3)
					hs[g->nhs].flags = ST_UP | ST_END;
				else if (ovalue > ge->x3)
					hs[g->nhs].flags = ST_END;
				else
					hs[g->nhs].flags = 0;

				if( hs[g->nhs].flags != 0 )
					g->nhs++;

				g->nvs++;
			}
			/*
			 * check the end of line for a not smooth local
			 * extremum
			 */
			if (ge->first)
				nge = ge->first;
			else
				nge = ge->next;

			if (nge == 0)
				continue;
			else if (nge->type == GE_LINE) {
				nx = nge->x3;
				ny = nge->y3;
			} else if (nge->type == GE_CURVE) {
				nx = nge->x1;
				ny = nge->y1;
			} else
				continue;

			/* check for vertical extremums */
			if (ge->y3 > ge->prev->y3 && ge->y3 > ny
			    || ge->y3 < ge->prev->y3 && ge->y3 < ny) {
				hs[g->nhs].value = ge->y3;
				hs[g->nhs].from
					= hs[g->nhs].to
					= hs[g->nhs].origin = ge->x3;

				if (ge->x3 < ge->prev->x3
				    || nx < ge->x3)
					hs[g->nhs].flags = ST_UP;
				else
					hs[g->nhs].flags = 0;

				if (ge->x3 != ge->prev->x3 || nx != ge->x3)
					g->nhs++;
			}
			/*
			 * the same point may be both horizontal and vertical
			 * extremum
			 */
			/* check for horizontal extremums */
			if (ge->x3 > ge->prev->x3 && ge->x3 > nx
			    || ge->x3 < ge->prev->x3 && ge->x3 < nx) {
				vs[g->nvs].value = ge->x3;
				vs[g->nvs].from
					= vs[g->nvs].to
					= vs[g->nvs].origin = ge->y3;

				if (ge->y3 > ge->prev->y3
				    || ny > ge->y3)
					vs[g->nvs].flags = ST_UP;
				else
					vs[g->nvs].flags = 0;

				if (ge->y3 != ge->prev->y3 || ny != ge->y3)
					g->nvs++;
			}
		}
	}

	g->nhs=addbluestems(hs, g->nhs);
	sortstems(hs, g->nhs);
	sortstems(vs, g->nvs);

	if (ISDBG(STEMS))
		debugstems(g->name, hs, g->nhs, vs, g->nvs);

	/* find the stems interacting with the Blue Zones */
	markbluestems(hs, g->nhs);

	if(subhints) {
		if (ISDBG(SUBSTEMS))
			fprintf(pfa_file, "%% %s: joining subst horizontal stems\n", g->name);
		joinsubstems(hs, hs_pairs, g->nhs, 1);
		if (ISDBG(SUBSTEMS))
			fprintf(pfa_file, "%% %s: joining subst vertical stems\n", g->name);
		joinsubstems(vs, vs_pairs, g->nvs, 0);

		groupsubstems(g, hs, hs_pairs, g->nhs, vs, vs_pairs, g->nvs);
	}

	if (ISDBG(MAINSTEMS))
		fprintf(pfa_file, "%% %s: joining main horizontal stems\n", g->name);
	g->nhs = joinmainstems(hs, g->nhs, 1);
	if (ISDBG(MAINSTEMS))
		fprintf(pfa_file, "%% %s: joining main vertical stems\n", g->name);
	g->nvs = joinmainstems(vs, g->nvs, 0);

	if (ISDBG(MAINSTEMS))
		debugstems(g->name, hs, g->nhs, vs, g->nvs);

	if(g->nhs > 0) {
		if ((sp = malloc(sizeof(STEM) * g->nhs)) == 0) {
			fprintf(stderr, "**** not enough memory for stems ****\n");
			exit(1);
		}
		g->hstems = sp;
		memcpy(sp, hs, sizeof(STEM) * g->nhs);
	} else
		g->hstems = 0;

	if(g->nvs > 0) {
		if ((sp = malloc(sizeof(STEM) * g->nvs)) == 0) {
			fprintf(stderr, "**** not enough memory for stems ****\n");
			exit(1);
		}
		g->vstems = sp;
		memcpy(sp, vs, sizeof(STEM) * g->nvs);
	} else
		g->vstems = 0;

}

/* convert weird curves that are close to lines into lines.
** the flag shows whether we should straighten only zigzags
** or otler lines too
*/

void
straighten(
	   GLYPH * g,
	   int zigonly
)
{
	GENTRY         *ge, *pge, *nge, *oge;
	int             dx, dy;
	int             dir;
	int             prevlen, nextlen;	/* length of prev/next line
						 * if it's flat */
	int             psx, psy, nsx, nsy;	/* stretchability limits */
	int             n;
	int             svdir;

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type != GE_CURVE)
			continue;

		pge = ge->prev;
		if (ge->first)
			nge = ge->first;
		else
			nge = ge->next;

		dx = dy = 0;
		prevlen = nextlen = 0;

		/*
		 * if current curve is almost a vertical line, and it *
		 * doesn't begin or end horizontally * (and the prev/next
		 * line doesn't join smoothly ?)
		 */
		if (ge->y3 != ge->y2 && ge->y1 != pge->y3
		    && abs(ge->x3 - pge->x3) <= 2
		    && (!zigonly && (abs(ge->x3 - pge->x3) <= 1 || abs(ge->y3 - pge->y3) >= 10)
		     || sign(ge->x1 - pge->x3) + sign(ge->x2 - ge->x3) == 0)
			) {

			dx = ge->x3 - pge->x3;
			dir = sign(ge->y3 - pge->y3);
			ge->type = GE_LINE;

			/*
			 * suck in all the sequence of such almost lines *
			 * going in the same direction * but not deviating
			 * too far from vertical
			 */

			while (abs(dx) <= 5 && nge->type == GE_CURVE
			       && nge->y3 != nge->y2 && nge->y1 != ge->y3
			       && abs(nge->x3 - ge->x3) <= 2
			       && (!zigonly && (abs(nge->x3 - ge->x3) <= 1 || abs(nge->y3 - ge->y3) >= 10)
				   || sign(nge->x1 - ge->x3) + sign(nge->x2 - nge->x3) == 0)
			       && dir == sign(nge->y3 - ge->y3)) {
				ge->y3 = nge->y3;
				ge->x3 = nge->x3;

				if (ge->first) {
					/*
					 * move the start point of the
					 * contour
					 */
					nge->prev->x3 = nge->x3;
					nge->prev->y3 = nge->y3;
					nge->prev->next = nge->next;
					nge->next->prev = nge->prev;
					ge->first = nge->next;
					free(nge);
					nge = ge->first;
				} else {
					ge->first = nge->first;
					ge->next = nge->next;
					nge->next->prev = ge;
					free(nge);
					if (ge->first)
						nge = ge->first;
					else
						nge = ge->next;
				}

				dx = ge->x3 - pge->x3;
			}

			/* now check what do we have as previous/next line */

			if (pge->type == GE_LINE && pge->x3 == pge->prev->x3)
				prevlen = abs(pge->y3 - pge->prev->y3);
			if (nge->type == GE_LINE && nge->x3 == ge->x3)
				nextlen = abs(nge->y3 - ge->y3);
		}
		/*
		 * if current curve is almost a horizontal line, and it *
		 * doesn't begin or end vertucally * (and the prev/next line
		 * doesn't join smoothly ?)
		 */
		else if (ge->x3 != ge->x2 && ge->x1 != pge->x3
			 && abs(ge->y3 - pge->y3) <= 2
			 && (!zigonly && (abs(ge->y3 - pge->y3) <= 1 || abs(ge->x3 - pge->x3) >= 10)
			     || sign(ge->y1 - pge->y3) + sign(ge->y2 - ge->y3) == 0)
			) {

			dy = ge->y3 - pge->y3;
			dir = sign(ge->x3 - pge->x3);
			ge->type = GE_LINE;

			/*
			 * suck in all the sequence of such almost lines *
			 * going in the same direction * but doesn't deviate
			 * too far from horizontal
			 */

			while (abs(dy) <= 5 && nge->type == GE_CURVE
			       && nge->x3 != nge->x2 && nge->x1 != ge->x3
			       && abs(nge->y3 - ge->y3) <= 2
			       && (!zigonly && (abs(nge->y3 - ge->y3) <= 1 || abs(nge->x3 - ge->x3) >= 10)
				   || sign(nge->y1 - ge->y3) + sign(nge->y2 - nge->y3) == 0)
			       && dir == sign(nge->x3 - ge->x3)) {
				ge->x3 = nge->x3;
				ge->y3 = nge->y3;

				if (ge->first) {
					/*
					 * move the start point of the
					 * contour
					 */
					nge->prev->y3 = nge->y3;
					nge->prev->x3 = nge->x3;
					nge->prev->next = nge->next;
					nge->next->prev = nge->prev;
					ge->first = nge->next;
					free(nge);
					nge = ge->first;
				} else {
					ge->first = nge->first;
					ge->next = nge->next;
					nge->next->prev = ge;
					free(nge);
					if (ge->first)
						nge = ge->first;
					else
						nge = ge->next;
				}

				dy = ge->y3 - pge->y3;
			}

			/* now check what do we have as previous/next line */

			if (pge->type == GE_LINE && pge->y3 == pge->prev->y3)
				prevlen = abs(pge->x3 - pge->prev->x3);
			if (nge->type == GE_LINE && nge->y3 == ge->y3)
				nextlen = abs(nge->x3 - ge->x3);
		}
		if (prevlen != 0) {
			/* join the previous line with current */
			ge->next->prev = pge;
			pge->next = ge->next;
			pge->first = ge->first;

			pge->x3 = ge->x3;
			pge->y3 = ge->y3;

			free(ge);
			ge = pge;
			pge = ge->prev;
		}
		if (nextlen != 0) {
			/* join the next line with current */
			ge->x3 = nge->x3;
			ge->y3 = nge->y3;

			if (ge->first) {
				ge->first = nge->next;
				nge->prev->x3 = nge->x3;
				nge->prev->y3 = nge->y3;
				nge->next->prev = nge->prev;
				nge->prev->next = nge->next;
				free(nge);
				nge = ge->first;
			} else {
				ge->first = nge->first;
				ge->next = nge->next;
				nge->next->prev = ge;
				free(nge);
				if (ge->first)
					nge = ge->first;
				else
					nge = ge->next;
			}

		}
		/* if we have to align the lines */
		if (dx != 0 || dy != 0) {

			/* find the stretchability limits of prev element */
			if (pge->type == GE_LINE) {
				psx = pge->x3 - pge->prev->x3;
				psy = pge->y3 - pge->prev->y3;
			} else if (pge->type == GE_CURVE) {
				psx = pge->x2 - pge->x1;
				psy = pge->y2 - pge->y1;
			} else {/* beginning of contour, can't stretch */
				psx = psy = 0;
			}
			if (sign(psx) == sign(dx))
				psx = 1000;	/* unlimited */
			else
				psx = abs(psx);
			if (sign(psy) == sign(dy))
				psy = 1000;	/* unlimited */
			else
				psy = abs(psy);

			/* find the stretchability limits of next element */
			if (nge->type == GE_LINE) {
				nsx = nge->x3 - ge->x3;
				nsy = nge->y3 - ge->y3;
			} else if (pge->type == GE_CURVE) {
				nsx = nge->x2 - nge->x1;
				nsy = nge->y2 - nge->y1;
			} else {/* beginning of contour, can't stretch */
				nsx = nsy = 0;
			}
			if (sign(nsx) == sign(-dx))
				nsx = 1000;	/* unlimited */
			else
				nsx = abs(nsx);
			if (sign(nsy) == sign(-dy))
				nsy = 1000;	/* unlimited */
			else
				nsy = abs(nsy);

			/* convert the stretchability limits to actual values */
			if (psx + nsx < abs(dx)) {	/* if we have troubles */
				n = abs(dx) - (psx + nsx);
				if (nsx != 0 && nge->type == GE_CURVE
				    && psx != 0 && pge->type == GE_CURVE) {	/* split the difference */
					psx += n / 2;
					nsx += n - n / 2;
				} else if (nsx != 0 && nge->type == GE_CURVE) {
					nsx += n;
				} else if (psx != 0 && pge->type == GE_CURVE) {
					psx += n;
				} else if (nsx != 0 && nge->type == GE_LINE
				      && psx != 0 && pge->type == GE_LINE) {	/* split the difference */
					psx += n / 2;
					nsx += n - n / 2;
				} else if (nsx != 0 && nge->type == GE_LINE) {
					nsx += n;
				} else if (psx != 0 && pge->type == GE_LINE) {
					psx += n;
				} else {
					/*
					 * we got no other choice than to
					 * insert a piece
					 */
					GENTRY         *zzge;

					zzge = newgentry();
					zzge->type = GE_LINE;
					zzge->x3 = ge->x3;
					zzge->y3 = ge->y3;
					zzge->next = ge->next;
					zzge->prev = ge;
					zzge->first = ge->first;

					ge->next->prev = zzge;
					ge->next = zzge;
					ge->first = 0;
					ge->x3 -= dx;
					if (abs(ge->y3 - pge->y3) >= 10)
						ge->y3 -= 5 * sign(ge->y3 - pge->y3);
					else
						ge->y3 -= (ge->y3 - pge->y3) / 2;

					pge = ge;
					ge = zzge;
					dx = psx = nsx = 0;

				}
			} else if (psx + nsx > abs(dx)) {	/* try to spilt fairly */
				if (prevlen >= 2 * nextlen) {
					if (nsx >= abs(dx))
						nsx = abs(dx);
					psx = abs(dx) - nsx;
				} else if (nextlen >= 2 * prevlen) {
					if (psx >= abs(dx))
						psx = abs(dx);
					nsx = abs(dx) - psx;
				} else {
					n = abs(dx) / 2;
					if (psx <= n)
						nsx = abs(dx) - psx;
					else if (nsx <= n)
						psx = abs(dx) - nsx;
					else {
						psx = n;
						nsx = abs(dx) - psx;
					}
				}
			}
			if (psy + nsy < abs(dy)) {	/* if we have troubles */
				n = abs(dy) - (psy + nsy);
				if (nsy != 0 && nge->type == GE_CURVE
				    && psy != 0 && pge->type == GE_CURVE) {	/* split the difference */
					psy += n / 2;
					nsy += n - n / 2;
				} else if (nsy != 0 && nge->type == GE_CURVE) {
					nsy += n;
				} else if (psy != 0 && pge->type == GE_CURVE) {
					psy += n;
				} else if (nsy != 0 && nge->type == GE_LINE
				      && psy != 0 && pge->type == GE_LINE) {	/* split the difference */
					psy += n / 2;
					nsy += n - n / 2;
				} else if (nsy != 0 && nge->type == GE_LINE) {
					nsy += n;
				} else if (psy != 0 && pge->type == GE_LINE) {
					psy += n;
				} else {
					/*
					 * we got no other choice than to
					 * insert a piece
					 */
					GENTRY         *zzge;

					zzge = newgentry();
					zzge->type = GE_LINE;
					zzge->x3 = ge->x3;
					zzge->y3 = ge->y3;
					zzge->next = ge->next;
					zzge->prev = ge;
					zzge->first = ge->first;

					ge->next->prev = zzge;
					ge->next = zzge;
					ge->first = 0;
					ge->y3 -= dy;
					if (abs(ge->x3 - pge->x3) >= 10)
						ge->x3 -= 5 * sign(ge->x3 - pge->x3);
					else
						ge->x3 -= (ge->x3 - pge->x3) / 2;

					pge = ge;
					ge = zzge;
					dy = psy = nsy = 0;

				}
			} else if (psy + nsy > abs(dy)) {	/* try to spilt fairly */
				if (prevlen >= 2 * nextlen) {
					if (nsy >= abs(dy))
						nsy = abs(dy);
					psy = abs(dy) - nsy;
				} else if (nextlen >= 2 * prevlen) {
					if (psy >= abs(dy))
						psy = abs(dy);
					nsy = abs(dy) - psy;
				} else {
					n = abs(dy) / 2;
					if (psy <= n)
						nsy = abs(dy) - psy;
					else if (nsy <= n)
						psy = abs(dy) - nsy;
					else {
						psy = n;
						nsy = abs(dy) - psy;
					}
				}
			}
			/* now stretch the neigboring elements */
			if (dx != 0) {
				dx = sign(dx);

				if (nsx != 0) {
					ge->x3 -= dx * nsx;
					if (ge->first)
						nge->prev->x3 -= dx * nsx;
					if (nge->type == GE_CURVE) {
						svdir = getcvdir(nge);
						nge->x1 -= dx * nsx;
						fixcvdir(nge, svdir);
					}
				}
				if (psx != 0) {
					pge->x3 += dx * psx;
					if (pge->type == GE_CURVE) {
						svdir = getcvdir(pge);
						pge->x2 += dx * psx;
						fixcvdir(pge, svdir);
					}
				}
			}
			if (dy != 0) {
				dy = sign(dy);

				if (nsy != 0) {
					ge->y3 -= dy * nsy;
					if (ge->first)
						nge->prev->y3 -= dy * nsy;
					if (nge->type == GE_CURVE) {
						svdir = getcvdir(nge);
						nge->y1 -= dy * nsy;
						fixcvdir(nge, svdir);
					}
				}
				if (psy != 0) {
					pge->y3 += dy * psy;
					if (pge->type == GE_CURVE) {
						svdir = getcvdir(pge);
						pge->y2 += dy * psy;
						fixcvdir(pge, svdir);
					}
				}
			}
		}
	}
}

/* find the approximate length of curve */

double
curvelen(
	 int x0, int y0, int x1, int y1,
	 int x2, int y2, int x3, int y3
)
{
	double          len = 0.;
	double          dx, dy;
	double          step, t, mt, n, x = (double) x0, y = (double) y0;
	int             i;

	x1 *= 3;
	y1 *= 3;
	x2 *= 3;
	y2 *= 3;

	step = 1. / 10.;
	t = 0;
	len = 0;
	for (i = 1; i <= 10; i++) {
		t += step;
		mt = 1 - t;

		n = x0 * mt * mt * mt + x1 * mt * mt * t + x2 * mt * t * t + x3 * t * t * t;
		dx = n - x;
		x = n;

		n = y0 * mt * mt * mt + y1 * mt * mt * t + y2 * mt * t * t + y3 * t * t * t;
		dy = n - y;
		y = n;

		len += sqrt(dx * dx + dy * dy);
	}

	return len;
}

/* split the zigzag-like curves into two parts */

void
splitzigzags(
	     GLYPH * g
)
{
	GENTRY         *ge, *nge;
	double          k, k1, k2;
	int             a, b, c, d;

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type != GE_CURVE)
			continue;

		a = ge->y2 - ge->y1;
		b = ge->x2 - ge->x1;
		k = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : (double) b / (double) a);
		a = ge->y1 - ge->prev->y3;
		b = ge->x1 - ge->prev->x3;
		k1 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : (double) b / (double) a);
		a = ge->y3 - ge->y2;
		b = ge->x3 - ge->x2;
		k2 = fabs(a == 0 ? (b == 0 ? 1. : 100000.) : (double) b / (double) a);

		/* if the curve is not a zigzag */
		if (k1 >= k && k2 <= k || k1 <= k && k2 >= k) {
			fixcvends(ge);
			continue;
		}
		/*
		 * we probably have also to check that the curve is in one *
		 * quadrant but we don't (yet)
		 */

		/* split the curve */
		nge = newgentry();
		nge->type = GE_CURVE;

		nge->next = ge->next;
		ge->next->prev = nge;

		ge->next = nge;
		nge->prev = ge;

		nge->first = ge->first;
		ge->first = 0;

		/*
		 * 2000 is for predictable truncating/rounding of negative
		 * values
		 */
		a = ge->prev->x3;
		b = ge->x1;
		c = ge->x2;
		d = ge->x3;
		nge->x3 = d;
		nge->x2 = (c + d + 4001) / 2 - 2000;
		nge->x1 = (b + 2 * c + d + 8002) / 4 - 2000;
		ge->x3 = (a + b * 3 + c * 3 + d + 16004) / 8 - 2000;
		ge->x2 = (a + 2 * b + c + 8002) / 4 - 2000;
		ge->x1 = (a + b + 4001) / 2 - 2000;

		a = ge->prev->y3;
		b = ge->y1;
		c = ge->y2;
		d = ge->y3;
		nge->y3 = d;
		nge->y2 = (c + d + 4001) / 2 - 2000;
		nge->y1 = (b + 2 * c + d + 8002) / 4 - 2000;
		ge->y3 = (a + b * 3 + c * 3 + d + 16004) / 8 - 2000;
		ge->y2 = (a + 2 * b + c + 8002) / 4 - 2000;
		ge->y1 = (a + b + 4001) / 2 - 2000;

		if (nge->x3 == ge->x3 && nge->y3 == ge->y3) {
			/* oops, the curve is too small to split */
			ge->first = nge->first;
			ge->next = nge->next;
			nge->next->prev = ge;
			free(nge);
		} else if (ge->x3 == ge->prev->x3 && ge->y3 == ge->prev->y3) {
			/* oops again, the curve is too small to split */
			nge->prev = ge->prev;
			*ge = *nge;
			ge->next->prev = ge;
			free(nge);
		} else {
			/* check whether we have created more zigzags */

			/* the first new curve */
			/* guess the direction by the front end */
			fixcvdir(ge,
				 (k1 < k ? CVDIR_FUP : (k1 > k ? CVDIR_FDOWN : CVDIR_FEQUAL)) | CVDIR_RSAME
				);

			ge = nge;
		}
		/* check whether we have created more zigzags */

		/* the second new curve or the whole unsplit curve */
		/* guess the direction by the rear end */
		fixcvdir(ge,
			 (k2 > k ? CVDIR_FUP : (k2 < k ? CVDIR_FDOWN : CVDIR_FEQUAL)) | CVDIR_RSAME
			);
	}
}

/* force conciseness: substitute 2 or more curves going in the
** same quadrant with one curve
*/

void
forceconcise(
	     GLYPH * g
)
{
	GENTRY         *ge, *nge;
	double          firstlen, lastlen, sumlen, scale;
	int             dxw1, dyw1, dxw2, dyw2;
	int             dxb1, dyb1, dxe1, dye1;
	int             dxb2, dyb2, dxe2, dye2;
	int             n;	/* number of curves we are going to sum */

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type != GE_CURVE)
			continue;

		n = 1;

		/* the whole direction of curve */
		dxw1 = ge->x3 - ge->prev->x3;
		dyw1 = ge->y3 - ge->prev->y3;

		while (1) {
			/* the whole direction of curve */
			dxw1 = ge->x3 - ge->prev->x3;
			dyw1 = ge->y3 - ge->prev->y3;

			/* directions of  ends of curve */
			dxb1 = ge->x1 - ge->prev->x3;
			dyb1 = ge->y1 - ge->prev->y3;
			dxe1 = ge->x3 - ge->x2;
			dye1 = ge->y3 - ge->y2;

			/* if this curve ends horizontally or vertically */
			/* or crosses quadrant boundaries */
			if (dxe1 == 0 || dye1 == 0 || dxb1 * dxe1 < 0 || dyb1 * dye1 < 0)
				break;

			if (ge->first)
				nge = ge->first;
			else
				nge = ge->next;

			if (nge->type != GE_CURVE)
				break;

			dxw2 = nge->x3 - ge->x3;
			dyw2 = nge->y3 - ge->y3;

			dxb2 = nge->x1 - ge->x3;
			dyb2 = nge->y1 - ge->y3;
			dxe2 = nge->x3 - nge->x2;
			dye2 = nge->y3 - nge->y2;

			/* if curve changes direction */
			if (sign(dxw1) != sign(dxw2) || sign(dyw1) != sign(dyw2))
				break;

			/* if the next curve crosses quadrant boundaries */
			/* or joints very abruptly */
			if (dxb2 * dxe2 < 0 || dyb2 * dye2 < 0
			    || sign(dxb2) != sign(dxe1) || sign(dyb2) != sign(dye1))
				break;

			/* if the arch is going in other direction */
			if (sign(abs(dxb1 * dyw1) - abs(dyb1 * dxw1))
			    * sign(abs(dxe2 * dyw2) - abs(dye2 * dxw2)) >= 0)
				break;

			/* if the next curve is not continuing the trend set */
			/* by the end of the first curve, i.e. could make a zigzag */
			/* note, the previous one has ">=", this one has ">" */

			if( sign(abs(dye1 * dxw2) - abs(dyw2 * dxe1))
				* sign(abs(dye1 * dxw1) - abs(dyw1 * dxe1)) > 0 )
				break;

			/* OK, it seeme like we can join these two curves */
			if (n == 1) {
				firstlen = sumlen = curvelen(ge->prev->x3, ge->prev->y3,
							     ge->x1, ge->y1, ge->x2, ge->y2, ge->x3, ge->y3);
			}
			lastlen = curvelen(ge->x3, ge->y3,
					   nge->x1, nge->y1, nge->x2, nge->y2, nge->x3, nge->y3);
			sumlen += lastlen;
			n++;

			ge->x2 = nge->x2;
			ge->y2 = nge->y2;
			ge->x3 = nge->x3;
			ge->y3 = nge->y3;

			if (ge->first) {
				nge->prev->x3 = ge->x3;
				nge->prev->y3 = ge->y3;
				nge->prev->next = nge->next;
				nge->next->prev = nge->prev;
				ge->first = nge->next;
			} else {
				ge->first = nge->first;
				ge->next = nge->next;
				nge->next->prev = ge;
			}
			free(nge);
		}

		if (n > 1) {	/* we got something to do */
			dxb1 = ge->x1 - ge->prev->x3;
			dyb1 = ge->y1 - ge->prev->y3;
			dxe1 = ge->x3 - ge->x2;
			dye1 = ge->y3 - ge->y2;

			/* scale the first segment */
			scale = sumlen / firstlen;
			ge->x1 = ge->prev->x3 + (int) (0.5 + scale * dxb1);
			ge->y1 = ge->prev->y3 + (int) (0.5 + scale * dyb1);

			/* scale the last segment */
			scale = sumlen / lastlen;
			ge->x2 = ge->x3 - (int) (0.5 + scale * dxe1);
			ge->y2 = ge->y3 - (int) (0.5 + scale * dye1);
		}
	}
}

void
print_glyf(
	   int glyphno
)
{
	GLYPH          *g;
	GENTRY         *ge;
	int             x = 0, y = 0;
	int             i;
	int             grp, lastgrp= -1;

	g = &glyph_list[glyphno];

	fprintf(pfa_file, "/%s { \n", g->name);

	/* consider widths >MAXLEGALWIDTH as bugs */
	if( g->scaledwidth <= MAXLEGALWIDTH ) {
		fprintf(pfa_file, "0 %d hsbw\n", g->scaledwidth);
	} else {
		fprintf(pfa_file, "0 1000 hsbw\n");
		fprintf(stderr, "glyph %s: width %d seems to be buggy, set to 1000\n",
			g->name, g->scaledwidth);
	}

#if 0
	fprintf(pfa_file, "%% contours: ");
	for (i = 0; i < g->ncontours; i++)
		fprintf(pfa_file, "%s(%d,%d) ", (g->contours[i].direction == DIR_OUTER ? "out" : "in"),
			g->contours[i].xofmin, g->contours[i].ymin);
	fprintf(pfa_file, "\n");

	if (g->rymin < 5000)
		fprintf(pfa_file, "%d lower%s\n", g->rymin, (g->flatymin ? "flat" : "curve"));
	if (g->rymax > -5000)
		fprintf(pfa_file, "%d upper%s\n", g->rymax, (g->flatymax ? "flat" : "curve"));
#endif

	if (g->hstems)
		for (i = 0; i < g->nhs; i += 2) {
			if (g->hstems[i].flags & ST_3) {
				fprintf(pfa_file, "%d %d %d %d %d %d hstem3\n",
					g->hstems[i].value,
				g->hstems[i + 1].value - g->hstems[i].value,
					g->hstems[i + 2].value,
					g->hstems[i + 3].value - g->hstems[i + 2].value,
					g->hstems[i + 4].value,
					g->hstems[i + 5].value - g->hstems[i + 4].value
					);
				i += 4;
			} else {
				fprintf(pfa_file, "%d %d hstem\n", g->hstems[i].value,
				g->hstems[i + 1].value - g->hstems[i].value);
			}
		}

	if (g->vstems)
		for (i = 0; i < g->nvs; i += 2) {
			if (g->vstems[i].flags & ST_3) {
				fprintf(pfa_file, "%d %d %d %d %d %d vstem3\n",
					g->vstems[i].value,
				g->vstems[i + 1].value - g->vstems[i].value,
					g->vstems[i + 2].value,
					g->vstems[i + 3].value - g->vstems[i + 2].value,
					g->vstems[i + 4].value,
					g->vstems[i + 5].value - g->vstems[i + 4].value
					);
				i += 4;
			} else {
				fprintf(pfa_file, "%d %d vstem\n", g->vstems[i].value,
				g->vstems[i + 1].value - g->vstems[i].value);
			}
		}

	for (ge = g->entries; ge != 0; ge = ge->next) {
		if(g->nsg>0) {
			grp=ge->stemid;
			if(grp >= 0 && grp != lastgrp)  {
				fprintf(pfa_file, "%d 4 callsubr\n", grp+g->firstsubr);
				lastgrp=grp;
			}
		}

		switch (ge->type) {
		case GE_MOVE:
			if (absolute)
				fprintf(pfa_file, "%d %d amoveto\n", ge->x3, ge->y3);
			else
				rmoveto(ge->x3 - x, ge->y3 - y);
			if (0)
				fprintf(stderr, "Glyph %s: print moveto(%d, %d)\n",
					g->name, ge->x3, ge->y3);
			x = ge->x3;
			y = ge->y3;
			break;
		case GE_LINE:
			if (absolute)
				fprintf(pfa_file, "%d %d alineto\n", ge->x3, ge->y3);
			else
				rlineto(ge->x3 - x, ge->y3 - y);
			x = ge->x3;
			y = ge->y3;
			break;
		case GE_CURVE:
			if (absolute)
				fprintf(pfa_file, "%d %d %d %d %d %d arcurveto\n",
					ge->x1, ge->y1, ge->x2, ge->y2, ge->x3, ge->y3);
			else
				rrcurveto(ge->x1 - x, ge->y1 - y,
					  ge->x2 - ge->x1, ge->y2 - ge->y1,
					  ge->x3 - ge->x2, ge->y3 - ge->y2);
			x = ge->x3;
			y = ge->y3;
			break;
		case GE_PATH:
			closepath();
			break;
		default:
			fprintf(stderr, "Glyph %s: unknown entry type '%c'\n",
				g->name, ge->type);
			break;
		}
	}

	fprintf(pfa_file, "endchar } ND\n");
}

/* print the subroutines for this glyph, returns the number of them */
int
print_glyf_subs(
	   int glyphno,
	   int startid /* start numbering subroutines from this id */
)
{
	GLYPH *g;
	int i, grp;

	g = &glyph_list[glyphno];

	if(!hints || !subhints || g->nsg<1)
		return 0;

	g->firstsubr=startid;

	fprintf(pfa_file, "%% %s %d\n", g->name, g->nsg);
	for(grp=0; grp<g->nsg; grp++) {
		fprintf(pfa_file, "dup %d {\n", startid++);
		for(i= (grp==0)? 0 : g->nsbs[grp-1]; i<g->nsbs[grp]; i++)
			fprintf(pfa_file, "\t%d %d %cstem\n", g->sbstems[i].low, 
				g->sbstems[i].high-g->sbstems[i].low,
				g->sbstems[i].isvert ? 'v' : 'h');
		fprintf(pfa_file, "\treturn\n\t} NP\n");
	}

	return g->nsg;
}

void
print_glyf_metrics(
	   int code,
	   int glyphno
)
{
	TTF_GLYF *glyf_table;

	get_glyf_table(glyphno, &glyf_table, NULL);

	if(transform)
	  fprintf(afm_file, "C %d ; WX %d ; N %s ; B %d %d %d %d ;\n",
		  code,
		  glyph_list[glyphno].scaledwidth,
		  glyph_list[glyphno].name,
		  scale((short)ntohs(glyf_table->xMin)),
		  scale((short)ntohs(glyf_table->yMin)),
		  scale((short)ntohs(glyf_table->xMax)),
		  scale((short)ntohs(glyf_table->yMax)));
	else
	  fprintf(afm_file, "C %d ; WX %d ; N %s ; B %d %d %d %d ;\n",
		  code,
		  glyph_list[glyphno].width,
		  glyph_list[glyphno].name,
		  (short)ntohs(glyf_table->xMin),
		  (short)ntohs(glyf_table->yMin),
		  (short)ntohs(glyf_table->xMax),
		  (short)ntohs(glyf_table->yMax));
}

/*
 SB:
 An important note about the BlueValues.

 The Adobe documentation says that the maximal width of a Blue zone
 is connected to the value of BlueScale, which is by default 0.039625.
 The BlueScale value defines, at which point size the overshoot
 suppression be disabled.

 The formula for it that is given in the manual is:

  BlueScale=point_size/240, for a 300dpi device

 that makes us wonder what is this 240 standing for. Incidentally
 240=72*1000/300, where 72 is the relation between inches and points,
 1000 is the size of the glyph matrix, and 300dpi is the resolution of
 the output device. Knowing that we can recalculate the formula for
 the font size in pixels rather than points:

  BlueScale=pixel_size/1000

 That looks a lot simpler than the original formula, does not it ?
 And the limitation about the maximal width of zone also looks
 a lot simpler after the transformation:

  max_width < 1000/pixel_size

 that ensures that even at the maximal pixel size when the overshoot
 suppression is disabled the zone width will be less than one pixel.
 This is important, failure to comply to this limit will result in
 really ugly fonts (been there, done that). But knowing the formula
 for the pixel width, we see that in fact we can use the maximal width
 of 24, not 23 as specified in the manual.

*/

#define MAXBLUEWIDTH (24)

/*
 * Find the indexes of the most frequent values
 * in the hystogram, sort them in ascending order, and save which one
 * was the best one (if asked).
 * Returns the number of values found (may be less than maximal because
 * we ignore the zero values)
 */

#define MAXHYST	(2000)		/* size of the hystogram */
#define HYSTBASE 500

static int
besthyst(
	 short *hyst,		/* the hystogram */
	 int base,		/* the base point of the hystogram */
	 int *best,		/* the array for indexes of best values */
	 int nbest,		/* its allocated size */
	 int width,		/* minimal difference between indexes */
	 int *bestindp		/* returned top point */
)
{
	unsigned char   hused[MAXHYST / 8 + 1];
	int             i, max, j, w;
	int             nf = 0;

	width--;

	for (i = 0; i <= MAXHYST / 8; i++)
		hused[i] = 0;

	max = 1;
	for (i = 0; i < nbest && max != 0; i++) {
		best[i] = 0;
		max = 0;
		for (j = 1; j < MAXHYST - 1; j++) {
			w = hyst[j];

			if (w > max && (hused[j >> 3] & (1 << (j & 0x07))) == 0) {
				best[i] = j;
				max = w;
			}
		}
		if (max != 0) {
			for (j = best[i] - width; j <= best[i] + width; j++) {
				if (j >= 0 && j < MAXHYST)
					hused[j >> 3] |= (1 << (j & 0x07));
			}
			best[i] -= base;
			nf = i + 1;
		}
	}

	if (bestindp)
		*bestindp = best[0];

	/* sort the indexes in ascending order */
	for (i = 0; i < nf; i++) {
		for (j = i + 1; j < nf; j++)
			if (best[j] < best[i]) {
				w = best[i];
				best[i] = best[j];
				best[j] = w;
			}
	}

	return nf;
}

/*
 * Find the next best Blue zone in the hystogram.
 * Return the weight of the found zone.
 */

static int
bestblue(
	 short *zhyst,		/* the zones hystogram */
	 short *physt,		/* the points hystogram */
	 short *ozhyst,		/* the other zones hystogram */
	 int *bluetab		/* where to put the found zone */
)
{
	int             i, j, w, max, ind, first, last;

	/* find the highest point in the zones hystogram */
	/* if we have a plateau, take its center */
	/* if we have multiple peaks, take the first one */

	max = -1;
	first = last = -10;
	for (i = 0; i <= MAXHYST - MAXBLUEWIDTH; i++) {
		w = zhyst[i];
		if (w > max) {
			first = last = i;
			max = w;
		} else if (w == max) {
			if (last == i - 1)
				last = i;
		}
	}
	ind = (first + last) / 2;

	if (max == 0)		/* no zones left */
		return 0;

	/* now we reuse `first' and `last' as inclusive borders of the zone */
	first = ind;
	last = ind + (MAXBLUEWIDTH - 1);

	/* our maximal width is far too big, so we try to make it narrower */
	w = max;
	j = (w & 1);		/* a pseudo-random bit */
	while (1) {
		while (physt[first] == 0)
			first++;
		while (physt[last] == 0)
			last--;
		if (last - first < (MAXBLUEWIDTH * 2 / 3) || (max - w) * 10 > max)
			break;

		if (physt[first] < physt[last]
		    || physt[first] == physt[last] && j) {
			if (physt[first] * 20 > w)	/* if weight is >5%,
							 * stop */
				break;
			w -= physt[first];
			first++;
			j = 0;
		} else {
			if (physt[last] * 20 > w)	/* if weight is >5%,
							 * stop */
				break;
			w -= physt[last];
			last--;
			j = 1;
		}
	}

	/* save our zone */
	bluetab[0] = first - HYSTBASE;
	bluetab[1] = last - HYSTBASE;

	/* invalidate all the zones overlapping with this one */
	/* the constant of 2 is determined by the default value of BlueFuzz */
	for (i = first - (MAXBLUEWIDTH - 1) - 2; i <= last + 2; i++)
		if (i >= 0 && i < MAXHYST) {
			zhyst[i] = 0;
			ozhyst[i] = 0;
		}
	return w;
}

/*
 * Try to find the Blue Values, bounding box and italic angle
 */

void
findblues(void)
{
	/* hystograms for upper and lower zones */
	short           hystl[MAXHYST];
	short           hystu[MAXHYST];
	short           zuhyst[MAXHYST];
	short           zlhyst[MAXHYST];
	int             nchars;
	int             ns;
	int             i, j, k, w, max;
	GENTRY         *ge;
	GLYPH          *g;
	double          ang;

	/* find the lowest and highest points of glyphs */
	/* and by the way build the values for FontBBox */
	/* and build the hystogram for the ItalicAngle */

	/* re-use hystl for the hystogram of italic angle */

	bbox[0] = bbox[1] = 5000;
	bbox[2] = bbox[3] = -5000;

	for (i = 0; i < MAXHYST; i++)
		hystl[i] = 0;

	nchars = 0;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		if (g->flags & GF_USED) {
			nchars++;

			g->rymin = 5000;
			g->rymax = -5000;
			for (ge = g->entries; ge != 0; ge = ge->next) {
				if (ge->type == GE_LINE) {

					j = ge->y3 - ge->prev->y3;
					k = ge->x3 - ge->prev->x3;
					if (j > 0)
						ang = atan2(-k, j) * 180.0 / M_PI;
					else
						ang = atan2(k, -j) * 180.0 / M_PI;

					k /= 100;
					j /= 100;
					if (ang > -45.0 && ang < 45.0) {
						/*
						 * be careful to not overflow
						 * the counter
						 */
						hystl[HYSTBASE + (int) (ang * 10.0)] += (k * k + j * j) / 4;
					}
					if (ge->y3 == ge->prev->y3) {
						if (ge->y3 <= g->rymin) {
							g->rymin = ge->y3;
							g->flatymin = 1;
						}
						if (ge->y3 >= g->rymax) {
							g->rymax = ge->y3;
							g->flatymax = 1;
						}
					} else {
						if (ge->y3 < g->rymin) {
							g->rymin = ge->y3;
							g->flatymin = 0;
						}
						if (ge->y3 > g->rymax) {
							g->rymax = ge->y3;
							g->flatymax = 0;
						}
					}
				} else if (ge->type == GE_CURVE) {
					if (ge->y3 < g->rymin) {
						g->rymin = ge->y3;
						g->flatymin = 0;
					}
					if (ge->y3 > g->rymax) {
						g->rymax = ge->y3;
						g->flatymax = 0;
					}
				}
				if (ge->type == GE_LINE || ge->type == GE_CURVE) {
					if (ge->x3 < bbox[0])
						bbox[0] = ge->x3;
					if (ge->x3 > bbox[2])
						bbox[2] = ge->x3;
					if (ge->y3 < bbox[1])
						bbox[1] = ge->y3;
					if (ge->y3 > bbox[3])
						bbox[3] = ge->y3;
				}
			}
		}
	}

	/* get the most popular angle */
	max = 0;
	w = 0;
	for (i = 0; i < MAXHYST; i++) {
		if (hystl[i] > w) {
			w = hystl[i];
			max = i;
		}
	}
	ang = (double) (max - HYSTBASE) / 10.0;
	fprintf(stderr, "Guessed italic angle: %f\n", ang);
	if (italic_angle == 0.0)
		italic_angle = ang;

	/* build the hystogram of the lower points */
	for (i = 0; i < MAXHYST; i++)
		hystl[i] = 0;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		if ((g->flags & GF_USED)
		    && g->rymin + HYSTBASE >= 0 && g->rymin < MAXHYST - HYSTBASE) {
			hystl[g->rymin + HYSTBASE]++;
		}
	}

	/* build the hystogram of the upper points */
	for (i = 0; i < MAXHYST; i++)
		hystu[i] = 0;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		if ((g->flags & GF_USED)
		    && g->rymax + HYSTBASE >= 0 && g->rymax < MAXHYST - HYSTBASE) {
			hystu[g->rymax + HYSTBASE]++;
		}
	}

	/* build the hystogram of all the possible lower zones with max width */
	for (i = 0; i < MAXHYST; i++)
		zlhyst[i] = 0;

	for (i = 0; i <= MAXHYST - MAXBLUEWIDTH; i++) {
		for (j = 0; j < MAXBLUEWIDTH; j++)
			zlhyst[i] += hystl[i + j];
	}

	/* build the hystogram of all the possible upper zones with max width */
	for (i = 0; i < MAXHYST; i++)
		zuhyst[i] = 0;

	for (i = 0; i <= MAXHYST - MAXBLUEWIDTH; i++) {
		for (j = 0; j < MAXBLUEWIDTH; j++)
			zuhyst[i] += hystu[i + j];
	}

	/* find the baseline */
	w = bestblue(zlhyst, hystl, zuhyst, &bluevalues[0]);
	if (0)
		fprintf(stderr, "BaselineBlue zone %d%% %d...%d\n", w * 100 / nchars,
				bluevalues[0], bluevalues[1]);

	if (w == 0)		/* no baseline, something weird */
		return;

	/* find the upper zones */
	for (nblues = 2; nblues < 14; nblues += 2) {
		w = bestblue(zuhyst, hystu, zlhyst, &bluevalues[nblues]);

		if (0)
			fprintf(stderr, "Blue zone %d%% %d...%d\n", w * 100 / nchars, 
				bluevalues[nblues], bluevalues[nblues+1]);

		if (w * 20 < nchars)
			break;	/* don't save this zone */
	}

	/* find the lower zones */
	for (notherb = 0; notherb < 10; notherb += 2) {
		w = bestblue(zlhyst, hystl, zuhyst, &otherblues[notherb]);

		if (0)
			fprintf(stderr, "OtherBlue zone %d%% %d...%d\n", w * 100 / nchars,
				otherblues[notherb], otherblues[notherb+1]);


		if (w * 20 < nchars)
			break;	/* don't save this zone */
	}

}

/*
 * Find the actual width of the glyph and modify the
 * description to reflect it. Not guaranteed to do
 * any good, may make character spacing too wide.
 */

void
docorrectwidth(void)
{
	int             i;
	GENTRY         *ge;
	GLYPH          *g;
	int             xmin, xmax;
	int             maxwidth, minsp;

	/* enforce this minimal spacing,
	 * we limit the amount of the enforced spacing to avoid
	 * spacing the bold wonts too widely
	 */
	minsp = (stdhw>60 || stdhw<10)? 60 : stdhw;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		g->oldwidth=g->scaledwidth; /* save the old width, will need for AFM */

		if (correctwidth && g->flags & GF_USED) {
			xmin = 5000;
			xmax = -5000;
			for (ge = g->entries; ge != 0; ge = ge->next) {
				if (ge->type != GE_LINE && ge->type != GE_CURVE) 
					continue;

				if (ge->x3 <= xmin) {
					xmin = ge->x3;
				}
				if (ge->x3 >= xmax) {
					xmax = ge->x3;
				}
			}

			maxwidth=xmax+minsp;
			if( g->scaledwidth < maxwidth ) {
				g->scaledwidth = maxwidth;
				fprintf(stderr, "glyph %s: extended from %d to %d\n",
					g->name, g->oldwidth, g->scaledwidth );
			}
		}
	}

}

/*
 * Try to find the typical stem widths
 */

void
stemstatistics(void)
{
	short           hyst[MAXHYST];
	int             best[12];
	int             i, j, w;
	int             nchars;
	int             ns;
	STEM           *s;
	GENTRY         *ge;
	GLYPH          *g;

	/* start with typical stem width */

	nchars=0;

	/* build the hystogram of horizontal stem widths */
	for (i = 0; i < MAXHYST; i++)
		hyst[i] = 0;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		if (g->flags & GF_USED) {
			nchars++;
			s = g->hstems;
			for (j = 0; j < g->nhs; j += 2) {
				if ((s[j].flags | s[j + 1].flags) & ST_END)
					continue;
				w = s[j + 1].value - s[j].value+1;
				if(w==20) /* split stems should not be counted */
					continue;
				if (w > 0 && w < MAXHYST - 1) {
					/*
					 * handle some fuzz present in
					 * converted fonts
					 */
					hyst[w] += 2;
					hyst[w - 1]++;
					hyst[w + 1]++;
				}
			}
		}
	}

	/* find 12 most frequent values */
	ns = besthyst(hyst, 0, best, 12, 3, &stdhw);

	/* store data in stemsnaph */
	for (i = 0; i < ns; i++)
		stemsnaph[i] = best[i];
	if (ns < 12)
		stemsnaph[ns] = 0;

	/* build the hystogram of vertical stem widths */
	for (i = 0; i < MAXHYST; i++)
		hyst[i] = 0;

	for (i = 0, g = glyph_list; i < numglyphs; i++, g++) {
		if (g->flags & GF_USED) {
			s = g->vstems;
			for (j = 0; j < g->nvs; j += 2) {
				if ((s[j].flags | s[j + 1].flags) & ST_END)
					continue;
				w = s[j + 1].value - s[j].value+1;
				if (w > 0 && w < MAXHYST - 1) {
					/*
					 * handle some fuzz present in
					 * converted fonts
					 */
					hyst[w] += 2;
					hyst[w - 1]++;
					hyst[w + 1]++;
				}
			}
		}
	}

	/* find 12 most frequent values */
	ns = besthyst(hyst, 0, best, 12, 3, &stdvw);

	/* store data in stemsnaph */
	for (i = 0; i < ns; i++)
		stemsnapv[i] = best[i];
	if (ns < 12)
		stemsnapv[ns] = 0;

}

/*
 * SB
 * A funny thing: TTF paths are going in reverse direction compared
 * to Type1. So after all (because the rest of logic uses TTF
 * path directions) we have to reverse the paths.
 *
 * It was a big headache to discover that.
 */

void
reversepathsfromto(
		   GENTRY * from,
		   GENTRY * to
)
{
	GENTRY         *ge, *fge, *nge, *pge;
	GENTRY         *co, *cn, *last;

	for (ge = from; ge != 0 && ge != to; ge = ge->next) {
		if (ISDBG(REVERSAL))
			fprintf(stderr, "%% 0x%x <- 0x%x, 0x%x\n", ge, ge->prev, ge->first);

		if (ge->first) {
			/* we got a path, reverse it */
			nge = ge->next;
			fge = ge->first;
			pge = fge->prev;

			if (pge == 0) {
				fprintf(stderr, "*** No MOVE before line !!! Fatal. ****\n");
				exit(1);
			}
			last = pge;

			/* go back on it and generate new entries */
			for (co = ge; co != pge; co = co->prev) {
				cn = newgentry();

				cn->type = co->type;
				if (co->type == GE_CURVE) {
					cn->x1 = co->x2;
					cn->y1 = co->y2;
					cn->x2 = co->x1;
					cn->y2 = co->y1;
				}
				cn->x3 = co->prev->x3;
				cn->y3 = co->prev->y3;
				cn->stemid = co->stemid;
				cn->flags = co->flags;

				cn->first = 0;
				last->next = cn;
				cn->prev = last;
				last = cn;
			}

			/* then connect the chain back */
			last->first = pge->next;
			last->next = nge;
			nge->prev = last;

			/* neccessary for open paths */
			pge->x3 = ge->x3;
			pge->y3 = ge->y3;

			/* cut the old path from list of entries */
			fge->prev = 0;
			ge->next = 0;

			/* and finally discard the old chain */
			for (co = fge; co != 0; co = cn) {
				cn = co->next;
				free(co);
			}

			/* reset to new path */
			ge = last;
		}
	}
}

void
reversepaths(
	     GLYPH * g
)
{
	reversepathsfromto(g->entries, NULL);
}

#if 0

/*
** This function is commented out because the information
** collected by it is not used anywhere else yet. Now
** it only collects the directions of contours. And the
** direction of contours gets fixed already in draw_glyf().
**
***********************************************
**
** Here we expect that the paths are already closed.
** We also expect that the contours do not intersect
** and that curves doesn't cross any border of quadrant.
**
** Find which contours go inside which and what is
** their proper direction. Then fix the direction
** to make it right.
**
*/

#define MAXCONT	1000

void
fixcontours(
	    GLYPH * g
)
{
	CONTOUR         cont[MAXCONT];
	short           ymax[MAXCONT];	/* the highest point */
	short           xofmax[MAXCONT];	/* X-coordinate of any point
						 * at ymax */
	short           ymin[MAXCONT];	/* the lowest point */
	short           xofmin[MAXCONT];	/* X-coordinate of any point
						 * at ymin */
	short           count[MAXCONT];	/* count of lines */
	char            dir[MAXCONT];	/* in which direction they must go */
	GENTRY         *start[MAXCONT], *minptr[MAXCONT], *maxptr[MAXCONT];
	int             ncont;
	int             i;
	int             dx1, dy1, dx2, dy2;
	GENTRY         *ge, *nge;

	/* find the contours and their most upper/lower points */
	ncont = 0;
	ymax[0] = -5000;
	ymin[0] = 5000;
	for (ge = g->entries; ge != 0; ge = ge->next) {
		if (ge->type == GE_LINE || ge->type == GE_CURVE) {
			if (ge->y3 > ymax[ncont]) {
				ymax[ncont] = ge->y3;
				xofmax[ncont] = ge->x3;
				maxptr[ncont] = ge;
			}
			if (ge->y3 < ymin[ncont]) {
				ymin[ncont] = ge->y3;
				xofmin[ncont] = ge->x3;
				minptr[ncont] = ge;
			}
		}
		if (ge->first) {
			start[ncont++] = ge->first;
			ymax[ncont] = -5000;
			ymin[ncont] = 5000;
		}
	}

	/* determine the directions of contours */
	for (i = 0; i < ncont; i++) {
		ge = minptr[i];
		if (ge->first)
			nge = ge->first;
		else
			nge = ge->next;

		if (ge->type == GE_CURVE) {
			dx1 = ge->x3 - ge->x2;
			dy1 = ge->y3 - ge->y2;

			if (dx1 == 0 && dy1 == 0) {	/* a pathological case */
				dx1 = ge->x3 - ge->x1;
				dy1 = ge->y3 - ge->y1;
			}
			if (dx1 == 0 && dy1 == 0) {	/* a more pathological
							 * case */
				dx1 = ge->x3 - ge->prev->x3;
				dy1 = ge->y3 - ge->prev->y3;
			}
		} else {
			dx1 = ge->x3 - ge->prev->x3;
			dy1 = ge->y3 - ge->prev->y3;
		}
		if (nge->type == GE_CURVE) {
			dx2 = ge->x3 - nge->x1;
			dy2 = ge->y3 - nge->y1;
			if (dx1 == 0 && dy1 == 0) {	/* a pathological case */
				dx2 = ge->x3 - nge->x2;
				dy2 = ge->y3 - nge->y2;
			}
			if (dx1 == 0 && dy1 == 0) {	/* a more pathological
							 * case */
				dx2 = ge->x3 - nge->x3;
				dy2 = ge->y3 - nge->y3;
			}
		} else {
			dx2 = ge->x3 - nge->x3;
			dy2 = ge->y3 - nge->y3;
		}

		/* compare angles */
		cont[i].direction = DIR_INNER;
		if (dy1 == 0) {
			if (dx1 < 0)
				cont[i].direction = DIR_OUTER;
		} else if (dy2 == 0) {
			if (dx2 > 0)
				cont[i].direction = DIR_OUTER;
		} else if (dx2 * dy1 < dx1 * dy2)
			cont[i].direction = DIR_OUTER;

		cont[i].ymin = ymin[i];
		cont[i].xofmin = xofmin[i];
	}

	/* save the information that may be needed further */
	g->ncontours = ncont;
	if (ncont > 0) {
		g->contours = malloc(sizeof(CONTOUR) * ncont);
		if (g->contours == 0) {
			fprintf(stderr, "***** Memory allocation error *****\n");
			exit(1);
		}
		memcpy(g->contours, cont, sizeof(CONTOUR) * ncont);
	}
}

#endif

/*
 *
 */

