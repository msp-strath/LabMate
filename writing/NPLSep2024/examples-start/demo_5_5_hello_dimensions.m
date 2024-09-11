%> dimensions D for Q over metre for `Length, kg for `Mass, sec for `Time, amp for `Current

newton = kg * metre / sec / sec
joule = newton * metre
watt = joule / sec
volt = watt / amp
%> typeof volt

%> times    :: [ 1 x 12 ] double
%> voltages :: [ 1 x 12 ] double

%> readfrom 'inputs.txt' times voltages

%> z3 :: [ 3 x 1 ] double
z3 = [ 0; 0; 0 ]
%> i3 :: [ 3 x 1 ] double
i3 = [ 1; 1; 1 ]

ddnc = [ i3  z3  i3  z3
        -i3  z3  i3  z3
         z3  i3  z3  i3
         z3 -i3  z3  i3 ]
%> typeof ddnc

M = [ ddnc times' ]
%> typeof M

x = M \ voltages'
%> typeof x
