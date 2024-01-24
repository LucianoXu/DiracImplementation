#!/bin/sh

CIME=$1


./primitive_generator.opt 3 1 | $CIME 
./primitive_generator.opt 5 1 | $CIME 
./primitive_generator.opt 7 1 | $CIME 
./primitive_generator.opt 3 2 | $CIME
./primitive_generator.opt 11 1 | $CIME 
./primitive_generator.opt 13 1 | $CIME 
./primitive_generator.opt 17 1 | $CIME 
./primitive_generator.opt 19 1 | $CIME 
./primitive_generator.opt 23 1 | $CIME 
./primitive_generator.opt 5 2 | $CIME 
./primitive_generator.opt 3 3 | $CIME 
./primitive_generator.opt 29 1 | $CIME 
./primitive_generator.opt 31 1 | $CIME 
./primitive_generator.opt 37 1 | $CIME 
./primitive_generator.opt 41 1 | $CIME 
./primitive_generator.opt 43 1 | $CIME 
./primitive_generator.opt 47 1 | $CIME 
./primitive_generator.opt 7 2 | $CIME
./primitive_generator.opt 53 1 | $CIME
./primitive_generator.opt 59 1 | $CIME
./primitive_generator.opt 61 1 | $CIME
./primitive_generator.opt 67 1 | $CIME
./primitive_generator.opt 71 1 | $CIME
./primitive_generator.opt 73 1 | $CIME
./primitive_generator.opt 79 1 | $CIME
./primitive_generator.opt 3 4  | $CIME
./primitive_generator.opt 83 1 | $CIME
./primitive_generator.opt 89 1 | $CIME
./primitive_generator.opt 97 1 | $CIME