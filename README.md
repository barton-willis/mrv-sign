# mrv-sign

 This is new implementation of Maxima function mrv-sign that is used by Gruntz code. The hope is that this revised mrv-sign function will fix some bugs and will extend the set of cases the Gruntz code can handle. There are no user-level functions in mrv-sign.lisp.

 To test this code, place the file mrv-sign.lisp in a folder that Maxima can find and
 load the file from a Maxima command line. 
 
 This version of mrv-sign seems to fix the notorious Bug 3054 (https://sourceforge.net/p/maxima/bugs/3054/) for Maxima compiled with Clozure CL (1.12.2), but _not_ with Maxima compiled with SBCL (2.2.2).

