%< LabMate 0.2.0.0
%> dimensions V for Q over `Length, `Mass, `Time

%> unit metre :: Q({ `Length })
%<{
metre = 1;
%<}

%> unit foo :: Q({ `Length * `Time})
%<{
foo = 1;
%<}

%> unit unitless :: Q({})
%<{
unitless = 1;
%<}

%> unit unitless2 :: Q({ `Length / `Length})
%<{
unitless2 = 1;
%<}

%> unit baz :: Q( {`Length / `Time^2})
%<{
baz = 1;
%<}

%> unit sq :: Q( { { `Length } })
%<{
sq = 1;
%<}

%> typeof unitless2
%< unitless2 :: Quantity (Enum [`Length, `Mass, `Time]) {}



