rem file to build ttf2pt1 with Cygnus GCC on Windows
rem don't forget to copy CYGWIN1.DLL into C:\WINDOWS

gcc -o ttf2pt1 -DWINDOWS ttf2pt1.c pt1.c t1asm.c ttf.c -lm
gcc -o t1asm -DWINDOWS -DSTANDALONE t1asm.c

