%> dimensions V for Q over metre for `Length, kg for `Mass, sec for `Time

%> x :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
x = [ 2      3*metre
      4/sec  5*metre/sec ];

%> y :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
y = [ 5      4*metre
      3/sec  2*metre/sec ];

z = x + y
%> typeof z
