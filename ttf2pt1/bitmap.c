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
#define FRF_DVPLUS	0x0004 /* vert direction towards increased coordinates */
#define FRF_DVMINUS	0x0008 /* vert direction towards decreased coordinates */
#define FRF_LINE	0x0010 /* this is a line - else curve */
#define FRF_CORNER	0x0020 /* this curve is just a (potentially) rounded corner */
#define FRF_IGNORE	0x0040 /* this fragment should be ignored */
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

		/* there can't be more fragments than gentries */
		frag = calloc(maxfrags, sizeof *frag);
		if(frag == 0)  {
			fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
			exit(255);
		}
		nfrags = 0;

		dumppaths(g, NULL, NULL);
		for(cge=g->entries; cge!=0; cge=cge->next) {
			if(cge->type != GE_MOVE)
				continue;

			/* we've found the beginning of a contour */
			{
				int hdir, vdir, d, firsthor, hor, count;
				int lastlen, nextlen;
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
						lastlen = abs(ge->ix3 - pge->ix3);
						nexthline = hline = hline2 = hline3 = 1;
						nextvline = vline = vline2 = vline3 = 0;
					} else {
						lastlen = abs(ge->iy3 - pge->iy3);
						nexthline = hline = hline2 = hline3 = 0;
						nextvline = vline = vline2 = vline3 = 1;
					}

					frag[nfrags].first = ge;
					count = 1;

					fprintf(stderr, "%s: frag start at %p\n", g->name, ge);

					/* the (rather random) definitions are:
					 * convex: dx gets longer, dy gets shorter towards the end (vh-curve)
					 * concave: dx gets shorter, dy gets longer towards the end (hv-curve)
					 */
					nextconvex = convex = nextconcave = concave = 1;

					do {
						pge = ge;
						ge = ge->frwd;
						fprintf(stderr, "frag + %p\n",  ge);
						hor = !hor; /* we know that the directions alternate nicely */
						count++; /* including the current ge */

						if(hor) {
							d = isign(ge->ix3 - pge->ix3);
							if(hdir==0)
								hdir = d;
							else if(hdir != d) {
								fprintf(stderr, "wrong hdir ");
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
								fprintf(stderr, "wrong vdir ");
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
							fprintf(stderr, "abrupt step\n");
							if(count > 2) {
						overstepped: /* the last gentry does not belong to this fragment */
								fprintf(stderr, "frag - %p\n",  ge);
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

					/* see, what kind of fragment we have got */
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
						frag[nfrags].flags |= FRF_CORNER;
						frag[nfrags].usefirst = frag[nfrags].uselast = 0.5 ;
						frag[nfrags].last = ge;
						fprintf(stderr, "%s: corner at (%d, %d)\n",
							g->name, frag[nfrags].first->ix3, frag[nfrags].first->iy3);
						nfrags++;
						continue;
					}
					/* XXX get the other types */

				} while(ge != cge->next);
			}

		}
		
		free(frag);
	} /* end of vectorization logic */

	/* convert the data to float */
	{
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
