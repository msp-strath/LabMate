%< LabMate 0.2.0.6
%> dimensions D for Q over metre for `Length, kg for `Mass, sec for `Time
%<{
% LabMate tells MATLAB that units are 1s
metre = 1;
kg = 1;
sec = 1;
%<}

%> x :: [ i <- [{} {`Time}] x j <- [{} {`Length}] ] Q({j/i})
x = [ 3      2*metre
      5/sec  4*metre/sec ]
%> typeof 2*metre
%< 2*metre :: Q({`Length})
%> typeof x
%< x :: [ i <- [{}, {`Time}] x j <- [{}, {`Length}] ] Q({j / i})
                                                                            
%> y :: [ i <- [{} {`Time}] x j <- [{} {`Length*`Mass}] ] Q({j/i/`Mass})
y = [ 7/kg      8*metre
      5/sec/kg  6*metre/sec ]
%>typeof y
%< y :: [ i <- [{}, {`Time}] x j <- [{}, {`Mass * `Length}] ] Q({j / i / `Mass})

z = x + y
%> typeof z
%< There is something wrong with z. Relevant: x + y



















