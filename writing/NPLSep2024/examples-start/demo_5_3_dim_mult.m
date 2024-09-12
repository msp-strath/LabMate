%> dimensions V for Q over metre for `Length, kg for `Mass, sec for `Time

%> x :: [i <- [{} {`Time}] x j <- [{} {`Length}]] Q({`Mass * j / i})
x = [ 2*kg       5*kg*metre
      3*kg/sec   4*kg*metre/sec ]

%> typeof x

%  [ {`Mass}       {`Mass * `Length}
%    {`Mass/`Time} {`Mass * `Length / `Time } ]

%> y :: [j <- [{} {`Length} ] x k <- [{}, {1/`Mass}]] Q({k/j})
y = [ 7        3/kg
      5/metre  2/kg/metre ]

%> typeof y

z = x * y

%> typeof z
