# mrv-sign

 This is a new implementation of the Maxima function mrv-sign that is used by Gruntz code. The hope is that this revised mrv-sign function will fix some bugs and extend the set of cases the Gruntz code can handle. There are no user-level functions in mrv-sign.lisp. Presumably, when I finish polishing this code, it will be
 blended into the Maxima source.

The file rtest_gruntz is translated to Maxima from the SymPy tests (Copyright (c) 2006-2023 SymPy Development Team). For the license for this code, see LICENSE. I thank the SymPy developers for making this resource available.

To test this code, place the file mrv-sign.lisp in a folder that Maxima can find and
load the file from a Maxima command line. 

Although I don't entirely understand why, this version of mrv-sign seems to fix the notorious Bug 3054 (https://sourceforge.net/p/maxima/bugs/3054/).
 
If you test this code with other versions of Common Lisp, please let me know what you discover.

