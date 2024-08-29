%> dimensions V for Q over `Length, `Mass, `Time

%> unit metre :: Q({ `Length })
%> unit kg :: Q({ `Mass })
%> unit hz :: Q({ 1/`Time })

%> x :: [i <- [{} {`Time}] x j <- [{} {`Length}]] Q({`Mass * j / i})
x = [ 2*kg       5*kg*metre
      3*kg*hz   4*kg*metre*hz ]
%> typeof x

%  [ {`Mass}       {`Mass * `Length}
%    {`Mass/`Time} {`Mass * `Length / `Time } ]
