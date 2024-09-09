%> dimensions V for Q over `Length, `Mass, `Time

%> unit metre :: Q({ `Length })
%> unit kg    :: Q({ `Mass })
%> unit sec   :: Q({ `Time })

%> x :: Q({})
x = 6.6

y = x * metre
%> typeof y

z = x * kg
%> typeof z

% This should not typecheck:
%bad = y + z
%%> typeof bad
