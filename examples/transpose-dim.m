%> dimensions V for Q over metre for `Length, kg for `Mass, sec for `Time

%> x :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
x = [ 2      3*metre
      4/sec  5*metre/sec ];
%> typeof x

y = x';
%> typeof y
