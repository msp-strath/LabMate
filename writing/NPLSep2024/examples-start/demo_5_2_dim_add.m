%> dimensions D for Q over metre for `Length, kg for `Mass, sec for `Time

%> x :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
x = [ 3      2*metre
      5/sec  4*metre/sec ]
%> typeof 2*metre

%> y :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
y = [ 7      8*metre
      5/sec  6*metre/sec ]

z = x + y
%> typeof z




















