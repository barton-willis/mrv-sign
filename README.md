# mrv-sign

 This is a new implementation of the Maxima function mrv-sign that is used by Gruntz code. The hope is that this revised mrv-sign function will fix some bugs and extend the set of cases the Gruntz code can handle. There are no user-level functions in mrv-sign.lisp. Presumably, when this code is polished, it will be
 blended into the Maxima source.

 The file rtest_gruntz is translated to Maxima from the SymPy tests (Copyright (c) 2006-2023 SymPy Development Team). For the
 license for this code, see LICENSE. I thank the SymPy developers
 for making this resource available.

 To test this code, place the file mrv-sign.lisp in a folder that Maxima can find and
 load the file from a Maxima command line. 
 
This version of mrv-sign seems to fix the notorious Bug 3054 (https://sourceforge.net/p/maxima/bugs/3054/) for Maxima compiled with Clozure CL (1.12.2), but _not_ with Maxima compiled with SBCL (2.2.2).  For Maxima compiled with SBCL, Maxima will compute the limit correctly three times, but on the fourth time, the result is a Lisp error. For the fifth and subsequent tries, the limit is evaluated correctly. Using Maxima compiled with Clozure CL, repeated evaluations of this limit are OK.
 
 If you test this code with other versions of Common Lisp, please let me know what you discover.

