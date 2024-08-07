%> dimensions V for Q over `Length, `Mass, `Time

%> unit metre :: Q({ `Length })
%> unit kg :: Q({ `Mass })
%> unit sec :: Q({ `Time })

%> x :: [i <- [{} {`Time}] x j <- [{} {`Length}]] Q({`Mass * j / i})
x = [ 2*kg       5*kg*metre
      3*kg/sec   4*kg*metre/sec ]

%> typeof x

%%> y :: [j <- [{} {`Length} ] x k <- [{}, {1/`Mass}]] Q({j/k})
%y = [ 7        3/kg
%      5/metre  2/kg/metre ]
