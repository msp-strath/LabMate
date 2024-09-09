%%> times    :: [ 1 x 12 ] double

%%> voltages :: [ 1 x 12 ] double


%> z3 :: [ 3 x 1 ] double
z3 = [ 0; 0; 0 ]
%> i3 :: [ 3 x 1 ] double
i3 = [ 1; 1; 1 ]

% %> ddnc :: [ 12 x 4 ] double
ddnc = [ i3  z3  i3  z3
        -i3  z3  i3  z3
         z3  i3  z3  i3
         z3 -i3  z3  i3 ]
%> typeof ddnc

%M = [ ddnc times' ]
%%> typeof M

%x = M \ voltages
%%> typeof x
