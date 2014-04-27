
SetVerbose("User2", true);

variant := {"mindeg", "profile"};


A<W,X,Y,Z> := FunctionField(Rationals(), 4);
f := 1/W*Y+1/W*X*Y*Z+1/W*Z+1/W*Y*Z+W/Y+W/Z+W*X+1/W+1/W/X*Y+1/W/X+1/W/X*Z+W/Y/Z+W/X/Y/Z; // (Batyrev & Kreuzer, 2010)
time deq1 := LaurentSequence(f : r := 2,  variant := variant);

f := 1/W+W/X/Y+1/W*Z+1/W*Y+1/W*Y*Z+W/X/Y/Z+W/Z+1/W*X*Y*Z+1/W*X*Y+1/W*X*Z+W/Y+1/W*X+W/X/Z; // (Batyrev & Kreuzer, 2010)
time deq2 := LaurentSequence(f : r := 2,  variant := variant);

deq1 eq deq2;


