#!/usr/bin/perl
#
# script to create HTML file with character table
# in plain, italic, bold, bold-italic
#
# see COPYRIGHT
#

sub printall
{
	for $i (32..255) {
		$c=chr($i);
		if($c eq '<') {
			$c="&lt;";
		} elsif($c eq '>') {
			$c="&gt;";
		}
		printf("%03d&nbsp;%s&nbsp&nbsp;|&nbsp&nbsp\n", $i, $c);
	}
}

sub printstyles
{
	&printall();
	printf("<p><i>\n");
	&printall();
	printf("<p></i><b>\n");
	&printall();
	printf("<p><i>\n");
	&printall();
	printf("<p></i></b>\n");
}

printf("<HTML><BODY>\n");

&printstyles();
printf("<tt>\n");
&printstyles();
printf("</tt>\n");

printf("</BODY></HTML>\n");
