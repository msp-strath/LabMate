% missing quantities from core type theory
% users should be able to declare
% * the type of Free Abelian group of their unit system
% * indexed over the type of quantities
% * users should be able to declare *standard* units as well, and LabMate will emit:
%   `meter = 1;` in Matlab land
% do we want a general notion of LabMate definition?


%> dimensions V for Q over 'Length, 'Mass, 'Time
%{
	Type \ni X   Abel(X) \ni d
	--------------------------
	Type \ni Quantity(X, d)

	V = Abel(Enum['Length, 'Mass, 'Time])
	Q(v::V) = Quantity(Enum['Length, 'Mass, 'Time], v)  (<- to be implemented in CoreTT)
%}
%> unit meter :: Q({'Length})
meter = 1;
% if we have the matrix A
A = [1 2]
% we can decorate it with units (maybe?)
A = [1 * meter, 2 * meter] % (??)

%{
      --------- TODO ---------
      1. Quantity type in CoreTT
      2. `dimensions` directive
      3. `unit` directive
      4. dimensionless constants
      5. ...
      6. sugar for matrix types
%}
