/*
 * Handling of the bitmapped glyphs
 *
 * Copyright (c) 2001 by the TTF2PT1 project
 * Copyright (c) 2001 by Sergey Babkin
 *
 * see COPYRIGHT for the full copyright notice
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "pt1.h"
#include "global.h"

/* possible values of limits */
#define L_NONE	0 /* nothing here */
#define L_ON	1 /* black is on up/right */
#define L_OFF	2 /* black is on down/left */

static int warnedhints = 0;


#ifdef USE_AUTOTRACE
#include <autotrace/autotrace.h>

/*
 * Produce an autotraced outline from a bitmap.
 * scale - factor to scale the sizes
 * bmap - array of dots by lines, xsz * ysz
 * xoff, yoff - offset of the bitmap's lower left corner
 *              from the logical position (0,0)
 */

static void
autotraced_bmp_outline(
	GLYPH *g,
	int scale,
	char *bmap,
	int xsz,
	int ysz,
	int xoff,
	int yoff
)
{
	at_bitmap_type atb;
	at_splines_type *atsp;
	at_fitting_opts_type *atoptsp;
	at_spline_list_type *slp;
	at_spline_type *sp;
	int i, j, k;
	double lastx, lasty;
	double fscale;
	char *xbmap;

	fscale = (double)scale;

	/* provide a white margin around the bitmap */
	xbmap = malloc((ysz+2)*(xsz+2));
	if(xbmap == 0)  {
		fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
		exit(255);
	}
	memset(xbmap, 0, xsz+2);  /* top margin */
	for(i=0, j=xsz+2; i<ysz; i++, j+=xsz+2) {
		xbmap[j] = 0; /* left margin */
		memcpy(&xbmap[j+1], &bmap[xsz*(ysz-1-i)], xsz); /* a line of bitmap */
		xbmap[j+xsz+1] = 0; /* right margin */
	}
	memset(xbmap+j, 0, xsz+2);  /* bottom margin */
	xoff--; yoff-=2; /* compensate for the margins */

	atoptsp = at_fitting_opts_new();

	atb.width = xsz+2;
	atb.height = ysz+2;
	atb.np = 1;
	atb.bitmap = xbmap;

	atsp = at_splines_new(&atb, atoptsp);

	lastx = lasty = -1.;
	for(i=0; i<atsp->length; i++) {
		slp = &atsp->data[i];
#if 0
		fprintf(stderr, "%s: contour %d: %d entries clockwise=%d color=%02X%02X%02X\n",
			g->name, i, slp->length, slp->clockwise, slp->color.r, slp->color.g, slp->color.b);
#endif
		if(slp->length == 0)
			continue;
#if 0
		if(slp->color.r + slp->color.g + slp->color.b == 0)
			continue;
#endif
		fg_rmoveto(g, fscale*(slp->data[0].v[0].x+xoff), fscale*(slp->data[0].v[0].y+yoff));
		for(j=0; j<slp->length; j++) {
#if 0
			fprintf(stderr, "  ");
			for(k=0; k<4; k++)
				fprintf(stderr, "(%g %g) ", 
					fscale*(slp->data[j].v[k].x+xoff), 
					fscale*(ysz-slp->data[j].v[k].y+yoff)
					);
			fprintf(stderr, "\n");
#endif
			fg_rrcurveto(g,
				fscale*(slp->data[j].v[1].x+xoff), fscale*(slp->data[j].v[1].y+yoff),
				fscale*(slp->data[j].v[2].x+xoff), fscale*(slp->data[j].v[2].y+yoff),
				fscale*(slp->data[j].v[3].x+xoff), fscale*(slp->data[j].v[3].y+yoff) );
		}
		g_closepath(g);
	}

	at_splines_free(atsp);
	at_fitting_opts_free(atoptsp);
	free(xbmap);
}

#endif /*USE_AUTOTRACE*/

/* a fragment of a contour: a bunch of stairs-style gentries that
 * may be replaced by one straight line or curve
 */
struct cfrag {
	GENTRY *first; /* first gentry (inclusive) */
	GENTRY *last;  /* last gentry */
	double usefirst; /* use this length at the end of the first ge */
	double uselast; /* use this length at the beginning of the last ge */
	int flags;
#define FRF_DHPLUS	0x0001 /* horiz direction towards increased coordinates */
#define FRF_DHMINUS	0x0002 /* horiz direction towards decreased coordinates */
#define FRF_DHMASK	0x0003 /* horiz direction mask */
#define FRF_DVPLUS	0x0004 /* vert direction towards increased coordinates */
#define FRF_DVMINUS	0x0008 /* vert direction towards decreased coordinates */
#define FRF_DVMASK	0x000C /* vert direction mask */
#define FRF_DPLUS_MASK	0x0005 /* any direction towards increased coordinates */
#define FRF_DMINUS_MASK	0x000A /* any direction towards decreased coordinates */
#define FRF_LINE	0x0010 /* this is a line - else curve */
#define FRF_CORNER	0x0020 /* this curve is just a (potentially) rounded corner */
#define FRF_IGNORE	0x0040 /* this fragment should be ignored */
#define FRF_EXPAND_05	0x0080 /* this fragment should be expanded by 0.5 points */

};
typedef struct cfrag CFRAG;

/*
 * Produce an outline from a bitmap.
 * scale - factor to scale the sizes
 * bmap - array of dots by lines, xsz * ysz
 * xoff, yoff - offset of the bitmap's lower left corner
 *              from the logical position (0,0)
 */

void
bmp_outline(
	GLYPH *g,
	int scale,
	char *bmap,
	int xsz,
	int ysz,
	int xoff,
	int yoff
)
{
	char *hlm, *vlm; /* arrays of the limits of outlines */
	char *amp; /* map of ambiguous points */
	int x, y, nfrags, maxfrags;
	char *ip, *op;
	double fscale;

#ifdef USE_AUTOTRACE
	if(use_autotrace) {
		autotraced_bmp_outline(g, scale, bmap, xsz, ysz, xoff, yoff);
		return;
	}
#endif /*USE_AUTOTRACE*/

	fscale = (double)scale;
	g->flags &= ~GF_FLOAT; /* build it as int first */

	if(!warnedhints) {
		warnedhints = 1;
		if(subhints) {
			WARNING_2 fprintf(stderr, 
				"Use of hint substitution on bitmap fonts is not recommended\n");
		}
	}

#if 0
	printbmap(bmap, xsz, ysz, xoff, yoff);
#endif

	/* now find the outlines */
	maxfrags = 0;

	hlm=calloc( xsz, ysz+1 ); /* horizontal limits */
	vlm=calloc( xsz+1, ysz ); /* vertical limits */
	amp=calloc( xsz, ysz ); /* ambiguous points */

	if(hlm==0 || vlm==0 || amp==0)  {
		fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
		exit(255);
	}

	/*
	 * hlm and vlm represent a grid of horisontal and
	 * vertical lines. Each pixel is surrounded by the grid
	 * from all the sides. The values of [hv]lm mark the
	 * parts of grid where the pixel value switches from white
	 * to black and back.
	 */

	/* find the horizontal limits */
	ip=bmap; op=hlm;
	/* 1st row */
	for(x=0; x<xsz; x++) {
		if(ip[x])
			op[x]=L_ON;
	}
	ip+=xsz; op+=xsz;
	/* internal rows */
	for(y=1; y<ysz; y++) {
		for(x=0; x<xsz; x++) {
			if(ip[x]) {
				if(!ip[x-xsz])
					op[x]=L_ON;
			} else {
				if(ip[x-xsz])
					op[x]=L_OFF;
			}
		}
		ip+=xsz; op+=xsz;
	}

	/* last row */
	ip-=xsz;
	for(x=0; x<xsz; x++) {
		if(ip[x])
			op[x]=L_OFF;
	}

	/* find the vertical limits */
	ip=bmap; op=vlm;
	for(y=0; y<ysz; y++) {
		if(ip[0])
			op[0]=L_ON;
		for(x=1; x<xsz; x++) {
			if(ip[x]) {
				if(!ip[x-1])
					op[x]=L_ON;
			} else {
				if(ip[x-1])
					op[x]=L_OFF;
			}
		}
		if(ip[xsz-1])
			op[xsz]=L_OFF;
		ip+=xsz; op+=xsz+1; 
	}

	/*
	 * Ambiguous points are the nodes of the grids
	 * that are between two white and two black pixels
	 * located in a checkerboard style. Actually
	 * there are only two patterns that may be
	 * around an ambiguous point:
	 *
	 *    X|.    .|X
	 *    -*-    -*-
	 *    .|X    X|.
	 *
	 * where "|" and "-" represent the grid (respectively members
	 * of vlm and hlm), "*" represents an ambiguous point
	 * and "X" and "." represent black and white pixels.
	 *
	 * If these sample pattern occur in the lower left corner
	 * of the bitmap then this ambiguous point will be
	 * located at amp[1][1] or in other words amp[1*xsz+1].
	 *
	 * These points are named "ambiguous" because it's
	 * not easy to guess what did the font creator mean
	 * at these points. So we are going to treat them 
	 * specially, doing no aggressive smoothing.
	 */

	/* find the ambiguous points */
	for(y=ysz-1; y>0; y--)
		for(x=xsz-1; x>0; x--) {
			if(bmap[y*xsz+x]) {
				if( !bmap[y*xsz+x-1] && !bmap[y*xsz-xsz+x] && bmap[y*xsz-xsz+x-1] )
					amp[y*xsz+x]=1;
			} else {
				if( bmap[y*xsz+x-1] && bmap[y*xsz-xsz+x] && !bmap[y*xsz-xsz+x-1] )
					amp[y*xsz+x]=1;
			}
		}

#if 0
	printlimits(hlm, vlm, amp, xsz, ysz);
#endif

	/* generate the vectored (stepping) outline */

	while(1) {
		int found = 0;
		int outer; /* flag: this is an outer contour */
		int hor, newhor; /* flag: the current contour direction is horizontal */
		int dir; /* previous direction of the coordinate, 1 - L_ON, 0 - L_OFF */
		int startx, starty; /* start of a contour */
		int firstx, firsty; /* start of the current line */
		int newx, newy; /* new coordinates to try */
		char *lm, val;
		int maxx, maxy, xor;

		for(y=ysz; !found &&  y>0; y--) 
			for(x=0; x<xsz; x++) 
				if(hlm[y*xsz+x] > L_NONE) 
					goto foundcontour;
		break; /* have no contours left */

	foundcontour:
		ig_rmoveto(g, x+xoff, y+yoff); /* intermediate as int */

		startx = firstx = x;
		starty = firsty = y;

		if(hlm[y*xsz+x] == L_OFF) {
			outer = 1; dir = 0;
			hlm[y*xsz+x] = -hlm[y*xsz+x]; /* mark as seen */
			hor = 1; x++;
		} else {
			outer = 0; dir = 0;
			hor = 0; y--;
			vlm[y*(xsz+1)+x] = -vlm[y*(xsz+1)+x]; /* mark as seen */
		}

		while(x!=startx || y!=starty) {
#if 0
			printf("trace (%d, %d) outer=%d hor=%d dir=%d\n", x, y, outer, hor, dir);
#endif

			/* initialization common for try1 and try2 */
			if(hor) {
				lm = vlm; maxx = xsz+1; maxy = ysz; newhor = 0;
			} else {
				lm = hlm; maxx = xsz; maxy = ysz+1; newhor = 1;
			}
			xor = (outer ^ hor ^ dir);

		try1:
			/* first we try to change axis, to keep the
			 * contour as long as possible
			 */

			newx = x; newy = y;
			if(!hor && (!outer ^ dir))
				newx--;
			if(hor && (!outer ^ dir))
				newy--;

			if(newx < 0 || newx >= maxx || newy < 0 || newy >= maxy)
				goto try2;

			if(!xor)
				val = L_ON;
			else
				val = L_OFF;
#if 0
			printf("try 1, want %d have %d at %c(%d, %d)\n", val, lm[newy*maxx + newx],
				(newhor ? 'h':'v'), newx, newy);
#endif
			if( lm[newy*maxx + newx] == val )
				goto gotit;

		try2:
			/* try to change the axis anyway */

			newx = x; newy = y;
			if(!hor && (outer ^ dir))
				newx--;
			if(hor && (outer ^ dir))
				newy--;

			if(newx < 0 || newx >= maxx || newy < 0 || newy >= maxy)
				goto try3;

			if(xor)
				val = L_ON;
			else
				val = L_OFF;
#if 0
			printf("try 2, want %d have %d at %c(%d, %d)\n", val, lm[newy*maxx + newx],
				(newhor ? 'h':'v'), newx, newy);
#endif
			if( lm[newy*maxx + newx] == val )
				goto gotit;

		try3:
			/* try to continue in the old direction */

			if(hor) {
				lm = hlm; maxx = xsz; maxy = ysz+1;
			} else {
				lm = vlm; maxx = xsz+1; maxy = ysz;
			}
			newhor = hor;
			newx = x; newy = y;
			if(hor && dir)
				newx--;
			if(!hor && !dir)
				newy--;

			if(newx < 0 || newx >= maxx || newy < 0 || newy >= maxy)
				goto badtry;

			if(dir)
				val = L_ON;
			else
				val = L_OFF;
#if 0
			printf("try 3, want %d have %d at %c(%d, %d)\n", val, lm[newy*maxx + newx],
				(newhor ? 'h':'v'), newx, newy);
#endif
			if( lm[newy*maxx + newx] == val )
				goto gotit;

		badtry:
			fprintf(stderr, "**** Internal error in the contour detection code at (%d, %d)\n", x, y);
			fprintf(stderr, "glyph='%s' outer=%d hor=%d dir=%d\n", g->name, outer, hor, dir);
			fflush(stdout);
			exit(1);

		gotit:
			if(hor != newhor) { /* changed direction, end the previous line */
				maxfrags++;
				ig_rlineto(g, x+xoff, y+yoff); /* intermediate as int */
				firstx = x; firsty = y;
			}
			lm[newy*maxx + newx] = -lm[newy*maxx + newx];
			hor = newhor;
			dir = (val == L_ON);
			if(newhor)
				x -= (dir<<1)-1;
			else
				y += (dir<<1)-1;
		}
#if 0
		printf("trace (%d, %d) outer=%d hor=%d dir=%d\n", x, y, outer, hor, dir);
#endif
		maxfrags++;
		ig_rlineto(g, x+xoff, y+yoff); /* intermediate as int */
		g_closepath(g);
	}


	/* try to vectorize the curves and sloped lines in the bitmap */
	if(vectorize) { 
		GENTRY *ge, *pge, *cge, *loopge;
		CFRAG *frag;
		int fhint;

		/* there can't be more fragments than gentries */
		maxfrags += 2; /* empty fragments at the beginning and the end */
		frag = calloc(maxfrags, sizeof *frag);
		if(frag == 0)  {
			fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
			exit(255);
		}
		nfrags = 0;
		/* put an empty fragment into the array for convenience */
		frag[0].first = frag[0].last = NULL;
		frag[0].usefirst = frag[0].uselast = 0.; 
		frag[nfrags++].flags = FRF_IGNORE;

		dumppaths(g, NULL, NULL);
		for(cge=g->entries; cge!=0; cge=cge->next) {
			if(cge->type != GE_MOVE)
				continue;

			/* we've found the beginning of a contour */
			{
				int hdir, vdir, d, firsthor, hor, count;
				int firstlen, lastlen, nextlen;
				/* these are flags showing what this fragment may be yet */
				int hline, vline, convex, concave, hline2, vline2, hline3, vline3;
				int nexthline, nextvline, nextconvex, nextconcave;
				int lastdx, lastdy, maxlen, minlen;

				/* we know that all the contours start at the top-left corner,
				 * so at most it might be before/after the last element of
				 * the last/first fragment
				 */

				ge = cge->next;
				pge = ge->bkwd;
				if(ge->ix3 == pge->ix3) { /* a vertical line */
					/* we want to start always from a horizontal line because
					 * then we always start from top and that is quaranteed to be a 
					 * fragment boundary, so move the start point of the contour
					 */
					pge->prev->next = pge->next;
					pge->next->prev = pge->prev;
					cge->next = pge;
					pge->prev = cge;
					pge->next = ge;
					ge->prev = pge;
					ge = pge; pge = ge->bkwd;
					cge->ix3 = pge->ix3; cge->iy3 = pge->iy3;
				}

				do { /* for each fragment */
					hdir = isign(ge->ix3 - pge->ix3);
					vdir = isign(ge->iy3 - pge->iy3);
					firsthor = hor = (hdir != 0);
					lastlen = maxlen = minlen = lastdx = lastdy = 0;
					if(hor) {
						firstlen = lastlen = abs(ge->ix3 - pge->ix3);
						nexthline = hline = hline2 = hline3 = 1;
						nextvline = vline = vline2 = vline3 = 0;
					} else {
						firstlen = lastlen = abs(ge->iy3 - pge->iy3);
						nexthline = hline = hline2 = hline3 = 0;
						nextvline = vline = vline2 = vline3 = 1;
					}

					frag[nfrags].first = ge;
					count = 1;

					fprintf(stderr, " frag start at %p\n", ge);

					/* the (rather random) definitions are:
					 * convex: dx gets longer, dy gets shorter towards the end (vh-curve)
					 * concave: dx gets shorter, dy gets longer towards the end (hv-curve)
					 */
					nextconvex = convex = nextconcave = concave = 1;

					do {
						fprintf(stderr, " hline=%d vline=%d convex=%d concave=%d\n",
							hline, vline, convex, concave);
						pge = ge;
						ge = ge->frwd;
						fprintf(stderr, " frag + %p\n",  ge);
						hor = !hor; /* we know that the directions alternate nicely */
						count++; /* including the current ge */

						if(hor) {
							d = isign(ge->ix3 - pge->ix3);
							if(hdir==0)
								hdir = d;
							else if(hdir != d) {
								fprintf(stderr, " wrong hdir ");
								goto overstepped;
							}
							nextlen = abs(ge->ix3 - pge->ix3);

							if(lastdx != 0) {
								if(nextconvex && nextlen < lastdx)
									nextconvex = 0;
								if(nextconcave && nextlen > lastdx)
									nextconcave = 0;
							}
							lastdx = nextlen;
						} else {
							d = isign(ge->iy3 - pge->iy3);
							if(vdir==0)
								vdir = d;
							else if(vdir != d) {
								fprintf(stderr, " wrong vdir ");
								goto overstepped;
							}
							nextlen = abs(ge->iy3 - pge->iy3);

							if(lastdy != 0) {
								if(nextconvex && nextlen > lastdx)
									nextconvex = 0;
								if(nextconcave && nextlen < lastdx)
									nextconcave = 0;
							}
							lastdy = nextlen;
						}
						if(lastlen > 1 && nextlen > 1) { /* an abrupt step */
							fprintf(stderr, " abrupt step\n");
							if(count > 2) {
						overstepped: /* the last gentry does not belong to this fragment */
								fprintf(stderr, " frag - %p\n",  ge);
								hor = !hor;
								count--; ge = pge; pge = ge->bkwd;
							}
							break;
						}
						/* may it be a continuation of the line in its long direction ? */
						if( nexthline && hor || nextvline && !hor ) {
							if(maxlen==0)
								maxlen = minlen = nextlen;
							else if(maxlen==minlen) {
								if(nextlen < maxlen) {
									if(nextlen < minlen-1)
										nexthline = nextvline = 0; /* it can't */
									else
										minlen = nextlen;
								} else {
									if(nextlen > maxlen+1)
										nexthline = nextvline = 0; /* it can't */
									else
										maxlen = nextlen;
								}
							} else if(nextlen < minlen || nextlen > maxlen)
								nexthline = nextvline = 0; /* it can't */
						}
						/* may it be a continuation of the line in its short direction ? */
						if( nexthline && !hor || nextvline && hor ) {
							if(nextlen != 1)
								nexthline = nextvline = 0; /* it can't */
						}

						if(!nextconvex && !nextconcave && !nexthline && !nextvline)
							goto overstepped; /* this can not be a reasonable continuation */

						lastlen = nextlen;
						hline3 = hline2; hline2 = hline; hline = nexthline;
						vline3 = vline2; vline2 = vline; vline = nextvline;
						convex = nextconvex;
						concave = nextconcave;
					} while(ge != cge->next);

					/* see what kind of fragment we have got */
					if(count < 2) {
						fprintf(stderr, "**** weird fragment in '%s' count=%d around (%f, %f)\n",
							g->name, count, fscale*frag[nfrags].first->ix3, fscale*frag[nfrags].first->iy3);
						continue;
					} 

					/* calculate the direction flags */
					d = 0;
					if(hdir < 0)
						d |= FRF_DHMINUS;
					else
						d |= FRF_DHPLUS;
					if(vdir < 0)
						d |= FRF_DVMINUS;
					else
						d |= FRF_DVPLUS;
					frag[nfrags].flags = d;

					if(count == 2) {
				makecorner:
						frag[nfrags].flags |= FRF_CORNER;
						frag[nfrags].usefirst = frag[nfrags].uselast = 1. ;
						frag[nfrags].last = ge;
						fprintf(stderr, "%s: corner at (%d, %d)\n",
							g->name, frag[nfrags].first->ix3, frag[nfrags].first->iy3);
						nfrags++;
						continue;
					}

					/* convenient for future calculations */
					if(hor)
						lastlen = abs(ge->ix3 - pge->ix3);
					else
						lastlen = abs(ge->iy3 - pge->iy3);

					/* If the last gentry is going on the same axis as the first
					 * then we prefer to treat it as a line. The line flag from
					 * one step back is used since if the last gentry is short,
					 * it will clear the line flags for the last step.
					 */
					if(firsthor==hor && (hline2 | vline2)) {
				makeline:
						frag[nfrags].flags |= FRF_LINE;
						if(maxlen != 0) {
							if(maxlen == minlen) {
								if(firstlen == maxlen-1 || lastlen == maxlen-1)
									minlen--;
								else if(firstlen == maxlen+1 || lastlen == maxlen+1)
									maxlen++;
							}
							if(maxlen == minlen) { /* try another way now */
								if(firstlen+lastlen == maxlen-1)
									minlen--;
								else if(firstlen+lastlen == maxlen+1)
									maxlen++;
							}
						}

						if(count==3 /* only one step, also implies maxlen==0 */
						/* or both the first and last gentries fit */
						|| firstlen+lastlen >= minlen && firstlen+lastlen <= maxlen) {
							/* make the line as long as possible */
							frag[nfrags].usefirst = (double)firstlen;
							frag[nfrags].uselast = (double)lastlen;
						} else if( firstlen >= minlen && firstlen <=maxlen
						&& lastlen >= minlen && lastlen <=maxlen ) {
							/* expand the endpoints by 0.5 on the other axis
							 * by shortening the previous and next gentries 
							 */
							frag[nfrags].flags |= FRF_EXPAND_05;

							/* make the line as long as possible */
							frag[nfrags].usefirst = (double)firstlen;
							frag[nfrags].uselast = (double)lastlen;
						} else  {
							/* nextlen is the line length without 1st and last gentries */
							if(hor)
								nextlen = abs(ge->ix3 - frag[nfrags].first->ix3);
							else
								nextlen = abs(ge->iy3 - frag[nfrags].first->iy3);

							/* (count/2-1) is the length of the line in the other dimension */
							frag[nfrags].usefirst = frag[nfrags].uselast 
								= (double)nextlen / (double)(count/2-1) / 2. ;
							if(firstlen < frag[nfrags].usefirst) {
								frag[nfrags].uselast += frag[nfrags].usefirst - firstlen;
								frag[nfrags].usefirst = firstlen;
							}
							if(lastlen < frag[nfrags].uselast) {
								if(fabs(lastlen-frag[nfrags].uselast) < 0.5) {
									/* no big deal, squeeze it a little */
									frag[nfrags].uselast = lastlen;
								} else {
									/* no good, try to make a curve */
									frag[nfrags].flags &= ~FRF_LINE;
									goto makecurve;
								}
							}
						}

						frag[nfrags].last = ge;
						fprintf(stderr, "%s: line at (%d, %d) %f - (%d, %d) %f\n",
							g->name, frag[nfrags].first->ix3, frag[nfrags].first->iy3,
							frag[nfrags].usefirst,
							frag[nfrags].last->prev->ix3, frag[nfrags].last->prev->iy3,
							frag[nfrags].uselast );
						nfrags++;
						continue;
					}
					/*
					 * if the last gentry is going on a different axis than the first
					 * then we prefer to treat it as a curve
					 */
				makecurve:
					/* a curve must have firsthor!=hor */
					if(firsthor==hor) {
						fprintf(stderr, "inconvenient frag - %p\n",  ge);
						hor = !hor;
						count--; ge = pge; pge = ge->bkwd;
						hline = hline2; hline2 = hline3;
						vline = vline2; vline2 = vline3;
					}
					if(count == 2)
						goto makecorner;

					if( !(convex|concave) ) {
						/* Got here because the first attempt to make
						 * a line has failed. Make one more step back and retry.
						 */
						fprintf(stderr, "inconvenient frag - %p\n",  ge);
						hor = !hor;
						count--; ge = pge; pge = ge->bkwd;
						hline = hline2; hline2 = hline3;
						vline = vline2; vline2 = vline3;

						/* at this point count>=3 because now firsthor==hor */
						goto makeline;
					}

					/* at this point a curve is guaranteed to fit */
					frag[nfrags].usefirst = (double)firstlen;
					frag[nfrags].uselast = (double)lastlen;
					frag[nfrags].last = ge;
					fprintf(stderr, "%s: curve at (%d, %d) - (%d, %d)\n",
						g->name, frag[nfrags].first->prev->ix3, frag[nfrags].first->prev->iy3,
						frag[nfrags].last->ix3, frag[nfrags].last->iy3);
					nfrags++;
					continue;

				} while(ge != cge->next);
			}

		}

		/* all the fragments are found, do the vectorization */
		fhint = 0; /* hint for finding fragments */
		pge = g->entries;
		g->entries = g->lastentry = 0;
		g->flags |= GF_FLOAT;
		loopge = 0;

		for(ge = pge; ge != 0; ge = ge->next) {
			CFRAG *fthis, *fprev, *fprev2, *fnext, *fnext2;
			int i, shor, ehor, mask1, mask2;
			double len, olen;
			double start[2 /*X,Y*/], end[2 /*X,Y*/], mid[2 /*X,Y*/];
			double dstart[2 /*X,Y*/], dend[2 /*X,Y*/];

			switch(ge->type) {
			case GE_LINE:
				/* find fragments beginning this ge */
				i = ++fhint;
				do {
					if(fhint == nfrags)
						fhint = 1;
					if(fhint == i)
						break; /* oops, made a full circle */
				} while(frag[fhint].flags & FRF_IGNORE);

				fprintf(stderr, "fhint=%d first=%p nfrags=%d\n", fhint, frag[fhint].first, nfrags);

				if(frag[fhint].first == ge)
					fthis = &frag[fhint];
				else 
					fthis = &frag[0]; /* an empty frag */

				cge = fthis->last; /* last ge of this fragment */
				if(cge == 0)
					cge = ge; /* a gentry without a valid fragment */

				/* get the coordinates of the start and end points */
				start[0] = (double)ge->bkwd->ix3;
				start[1] = (double)ge->bkwd->iy3;
				end[0] = (double)cge->ix3;
				end[1] = (double)cge->iy3;

				dstart[0] = dstart[1] = dend[0] = dend[1] = 0.; /* offset from EXPAND_05 */

				/* find the fragment ending with this ge */
				i = (fhint==1? nfrags : fhint) - 1;
				if(frag[i].last == ge && !(frag[i].flags & FRF_IGNORE))
					fprev = &frag[i];
				else 
					fprev = &frag[0]; /* an empty frag */

				/* find the fragment ending at the previous ge */
				if(--i == 0)
					i = nfrags -1;
				if(frag[i].last == ge->bkwd && !(frag[i].flags & FRF_IGNORE))
					fprev2 = &frag[i];
				else 
					fprev2 = &frag[0]; /* an empty frag */

				/* find the fragment immediately following fthis */
				i = fhint+1;
				if(i == nfrags)
					i = 1;
				if(frag[i].first == cge && !(frag[i].flags & FRF_IGNORE))
					fnext = &frag[i];
				else 
					fnext = &frag[0]; /* an empty frag */

				/* find the fragment starting at the next gentry from fthis */
				if(++i == nfrags)
					i = 1;
				if(frag[i].first == cge->frwd && !(frag[i].flags & FRF_IGNORE))
					fnext2 = &frag[i];
				else 
					fnext2 = &frag[0]; /* an empty frag */

				fprintf(stderr, "Vect %p (%p-%p) (%p-%p) _(%p-%p)_ (%p-%p) (%p-%p)\n",
					ge, fprev2->first, fprev2->last, fprev->first, fprev->last,
					fthis->first, fthis->last,
					fnext->first, fnext->last, fnext2->first, fnext2->last);

				/* if this fragment is expanded, it affects the neighbors */
				if(fthis->flags & FRF_EXPAND_05) {
					if(fprev->flags & FRF_CORNER) {
						fprev->flags |= FRF_IGNORE;
						fprev = &frag[0];
					}
					if(fnext->flags & FRF_CORNER) {
						fnext->flags |= FRF_IGNORE;
						fnext = &frag[0];
					}
					fprintf(stderr, " expanded (%p-%p) (%p-%p) _(%p-%p)_ (%p-%p) (%p-%p)\n",
						fprev2->first, fprev2->last, fprev->first, fprev->last,
						fthis->first, fthis->last,
						fnext->first, fnext->last, fnext2->first, fnext2->last);
				}

				/* split the first gentry with another frag if neccessary */

				/* find the available length */
				shor = (isign(ge->ix3 - ge->prev->ix3) != 0);
				if(shor) {
					len = (double)abs(ge->ix3 - ge->prev->ix3);
					mask1 = FRF_DVMASK;
					mask2 = FRF_DHMASK;
				} else {
					len = (double)abs(ge->iy3 - ge->prev->iy3);
					mask1 = FRF_DHMASK;
					mask2 = FRF_DVMASK;
				}
				olen = len;

				/* correct the length for the expansion of neighbors */
				if(fprev->flags & FRF_EXPAND_05) {
					if(fthis->flags & FRF_CORNER)  {
						fthis->flags |= FRF_IGNORE;
						fthis->usefirst = 0.;
						fthis = &frag[0];
					}
					if(fthis->flags & FRF_IGNORE) {
						if( (fprev->flags ^ fthis->flags) & mask1 )
							dstart[shor] = (fthis->flags & mask1 & FRF_DMINUS_MASK) ? 0.5 : -0.5;
						else
							dstart[shor] = (fthis->flags & mask1 & FRF_DMINUS_MASK) ? -0.5 : 0.5;
					}
				}
				if(fprev2->flags & FRF_EXPAND_05) {
					if( (fprev2->flags ^ fthis->flags) & mask2 ) {
						len += 0.5;
						dstart[!shor] = (fthis->flags & mask2 & FRF_DMINUS_MASK) ? -0.5 : 0.5;
					} else {
						len -= 0.5;
						dstart[!shor] = (fthis->flags & mask2 & FRF_DMINUS_MASK) ? 0.5 : -0.5;
					}
				}

				if(fthis->usefirst + fprev->uselast > len) {
					/* redistribute the space */
					if(len < 0.01) {
						fthis->usefirst = fprev->uselast = 0.;
					} else {
						double sum;

						sum = len / (fthis->usefirst + fprev->uselast);
						fthis->usefirst *= sum;
						fprev->uselast = len - fthis->usefirst;
					}
				}
				fprintf(stderr, " start %c at(%f, %f) d(%f, %f) olen=%f len=%f prevuse=%f thisuse=%f\n",
					(shor? 'h':'v'), start[0], start[1], dstart[0], dstart[1], olen, len, 
					fprev->uselast, fthis->usefirst);

				/* do the expansion of the front of this fragment if neccessary */
				if(fthis->flags & FRF_EXPAND_05) {
					double dd;
					dd = 0.5 * fthis->usefirst / olen;
					dstart[shor] += (fthis->flags & mask1 & FRF_DMINUS_MASK) ? dd : -dd;
					fprintf(stderr, " expanded start d(%f, %f)\n", dstart[0], dstart[1]);
				}

				/* split the last gentry with another frag if neccessary */

				/* find the available length */
				ehor = (isign(cge->ix3 - cge->prev->ix3) != 0);
				if(ehor) {
					len = (double)abs(cge->ix3 - cge->prev->ix3);
					mask1 = FRF_DVMASK;
					mask2 = FRF_DHMASK;
				} else {
					len = (double)abs(cge->iy3 - cge->prev->iy3);
					mask1 = FRF_DHMASK;
					mask2 = FRF_DVMASK;
				}
				olen = len;

				/* correct the length for the expansion of neighbors */
				if(fnext->flags & FRF_EXPAND_05) {
					if(fthis->flags & FRF_CORNER)  {
						fthis->flags |= FRF_IGNORE;
						fthis->uselast = 0.;
						fthis = &frag[0];
					}
					if(fthis->flags & FRF_IGNORE) {
						if( (fnext->flags ^ fthis->flags) & mask1 )
							dend[ehor] = (fthis->flags & mask1 & FRF_DMINUS_MASK) ? -0.5 : 0.5;
						else
							dend[ehor] = (fthis->flags & mask1 & FRF_DMINUS_MASK) ? 0.5 : -0.5;
					}
				}
				if(fnext2->flags & FRF_EXPAND_05) {
					if( (fnext2->flags ^ fthis->flags) & mask2 ) {
						len += 0.5;
						dend[!ehor] = (fthis->flags & mask2 & FRF_DMINUS_MASK) ? -0.5 : 0.5;
					} else {
						len -= 0.5;
						dend[!ehor] = (fthis->flags & mask2 & FRF_DMINUS_MASK) ? 0.5 : -0.5;
					}
				}

				if(fthis->uselast + fnext->usefirst > len) {
					/* redistribute the space */
					if(len < 0.01) {
						fthis->uselast = fnext->usefirst = 0.;
					} else {
						double sum;

						sum = len / (fthis->uselast + fnext->usefirst);
						fthis->uselast *= sum;
						fnext->usefirst = len - fthis->uselast;
					}
				}
				fprintf(stderr, " end %c at(%f, %f) d(%f, %f) olen=%f len=%f thisuse=%f nextuse=%f\n",
					(ehor? 'h':'v'), end[0], end[1], dend[0], dend[1], olen, len, 
					fthis->uselast, fnext->usefirst);


				/* do the expansion of the end of this fragment if neccessary */
				if(fthis->flags & FRF_EXPAND_05) {
					double dd;
					dd = 0.5 * fthis->uselast / olen;
					dend[ehor] += (fthis->flags & mask1 & FRF_DMINUS_MASK) ? -dd : dd;
					fprintf(stderr, " expanded end d(%f, %f)\n", dend[0], dend[1]);
				}

				/* finally draw the lines */

				/* first draw the unused part */
				start[0] += dstart[0];
				start[1] += dstart[1];
				mid[0] = ge->ix3;
				mid[1] = ge->iy3;
				if(shor) {
					start[0] += fsign(mid[0]-start[0]) * fprev->uselast;
					mid[0] += fsign(start[0]-mid[0]) * fthis->usefirst;
					mid[1] += dstart[1];
					len = fabs(mid[0] - start[0]);
				} else {
					start[1] += fsign(mid[1]-start[1]) * fprev->uselast;
					mid[1] += fsign(start[1]-mid[1]) * fthis->usefirst;
					mid[0] += dstart[0];
					len = fabs(mid[1] - start[1]);
				}
				fprintf(stderr, " Start %p: (%f, %f) -> (%f, %f) len=%f\n",
					ge, start[0], start[1], mid[0], mid[1], len);
				if(len > 0.01)
					fg_rlineto(g, fscale * mid[0], fscale * mid[1]);

				start[0] = mid[0];
				start[1] = mid[1];

				/* then draw the main part */
				if(fthis->flags & FRF_IGNORE) {
					/* do nothing */
				} else if(fthis->flags & FRF_LINE) {
					mid[0] = cge->prev->ix3;
					mid[1] = cge->prev->iy3;
					if(ehor) {
						mid[0] += fsign(end[0]-mid[0]) * fthis->uselast;
						mid[1] += dend[1];
					} else {
						mid[1] += fsign(end[1]-mid[1]) * fthis->uselast;
						mid[0] += dend[0];
					}
					len = fabs(mid[1] - start[1]) + fabs(mid[1] - start[1]);
					fprintf(stderr, " Line %p: (%f, %f) -> (%f, %f) len=%f\n",
						ge, start[0], start[1], mid[0], mid[1], len);
					if(len > 0.01)
						fg_rlineto(g, fscale * mid[0], fscale * mid[1]);
				} else {
					/* a curve */
#if 0
					if(fthis->flags & FRF_CORNER) {
						/* keep it symmetric */
						if(fthis->usefirst < 0.99 || fthis->uselast < 0.99) {
							if(fthis->usefirst >= 0.499 && fthis->uselast >= 0.499)
								fthis->usefirst = fthis->uselast = 0.5;
							else
								fthis->usefirst = fthis->uselast = 0.;
						}
					}
#endif
					mid[0] = cge->prev->ix3;
					mid[1] = cge->prev->iy3;
					if(ehor) {
						mid[0] += fsign(end[0]-mid[0]) * fthis->uselast;
						mid[1] += dend[1];
					} else {
						mid[1] += fsign(end[1]-mid[1]) * fthis->uselast;
						mid[0] += dend[0];
					}
					len = fabs(mid[0] - start[0]) + fabs(mid[1] - start[1]);
					fprintf(stderr, " Curve %p: (%f, %f) -> (%f, %f) len=%f\n",
						ge, start[0], start[1], mid[0], mid[1], len);

					/* XXX try to do an elliptic curve */
					if(len > 0.01)
						if(shor)
							fg_rrcurveto(g, 
								fscale * mid[0], fscale * start[1],
								fscale * mid[0], fscale * start[1],
								fscale * mid[0], fscale * mid[1]);
						else
							fg_rrcurveto(g, 
								fscale * start[0], fscale * mid[1],
								fscale * start[0], fscale * mid[1],
								fscale * mid[0], fscale * mid[1]);
				}
#if 0
				if( !(fthis->flags & FRF_IGNORE) ) {
					end[0] += dend[0];
					end[1] += dend[1];
					if(ehor) {
						end[0] += fsign(cge->bkwd->ix3-end[0]) * fnext->usefirst;
					} else {
						end[1] += fsign(cge->bkwd->iy3-end[1]) * fnext->usefirst;
					}
				}
#endif
				/* skip the fragment but don't miss the end of contour */
				if(ge != cge) {
					while(ge != cge && ge->frwd == ge->next)
						ge = ge->next;
					if(ge == cge)
						ge = ge->prev;
				}
				break;
			case GE_MOVE:
				fg_rmoveto(g, fscale * ge->ix3, fscale * ge->iy3);
				/* remember the reference to update it later */
				loopge = g->lastentry;
				break;
			case GE_PATH:
				/* update the first MOVE of this contour */
				if(loopge) {
					if( loopge->fx3 != g->lastentry->fx3
					|| loopge->fy3 != g->lastentry->fy3)
						fprintf(stderr, "Corrected Moveto from (%f, %f) to (%f, %f)\n",
							loopge->fx3/fscale, loopge->fy3/fscale,
							g->lastentry->fx3/fscale, g->lastentry->fy3/fscale);

					loopge->fx3 = g->lastentry->fx3;
					loopge->fy3 = g->lastentry->fy3;
					loopge = 0;
				}
				g_closepath(g);
				break;
			}
		}
		for(ge = pge; ge != 0; ge = cge) {
			cge = ge->next;
			free(ge);
		}
		dumppaths(g, NULL, NULL);
		
		free(frag);
		/* end of vectorization logic */
	} else {
		/* convert the data to float */
		GENTRY *ge;
		double x, y;

		for(ge = g->entries; ge != 0; ge = ge->next) {
			ge->flags |= GEF_FLOAT;
			if(ge->type != GE_MOVE && ge->type != GE_LINE) 
				continue;

			x = fscale * ge->ix3;
			y = fscale * ge->iy3;

			ge->fx3 = x;
			ge->fy3 = y;
		}
		g->flags |= GF_FLOAT;
	}

	free(hlm); free(vlm); free(amp);
}

#if 0
/* print out the bitmap */
printbmap(bmap, xsz, ysz, xoff, yoff)
	char *bmap;
	int xsz, ysz, xoff, yoff;
{
	int x, y;

	for(y=ysz-1; y>=0; y--) {
		putchar( (y%10==0) ? y/10+'0' : ' ' );
		putchar( y%10+'0' );
		for(x=0; x<xsz; x++)
			putchar( bmap[y*xsz+x] ? 'X' : '.' );
		if(-yoff==y)
			putchar('_'); /* mark the baseline */
		putchar('\n');
	}
	putchar(' '); putchar(' ');
	for(x=0; x<xsz; x++)
		putchar( x%10+'0' );
	putchar('\n'); putchar(' '); putchar(' ');
	for(x=0; x<xsz; x++)
		putchar( (x%10==0) ? x/10+'0' : ' ' );
	putchar('\n');
}

/* print out the limits of outlines */
printlimits(hlm, vlm, amp, xsz, ysz)
	char *hlm, *vlm, *amp;
	int xsz, ysz;
{
	int x, y;
	static char h_char[]={ ' ', '~', '^' };
	static char v_char[]={ ' ', '(', ')' };

	for(y=ysz-1; y>=0; y--) {
		for(x=0; x<xsz; x++) {
			if(amp[y*xsz+x])
				putchar('!'); /* ambigouos point is always on a limit */
			else
				putchar(v_char[ vlm[y*(xsz+1)+x] & (L_ON|L_OFF) ]);
			putchar(h_char[ hlm[(y+1)*xsz+x] & (L_ON|L_OFF) ]);
		}
		putchar(v_char[ vlm[y*(xsz+1)+x] & (L_ON|L_OFF) ]);
		putchar('\n');
	}
	/* last line */
	for(x=0; x<xsz; x++) {
		putchar(' ');
		putchar(h_char[ hlm[x] & (L_ON|L_OFF) ]);
	}
	putchar(' ');
	putchar('\n');
}
#endif /* 0 */
