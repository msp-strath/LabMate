myfunction = @(x,y)x^2 + y^2 + x*y;
foo = @()myfunction ;
x = 1;
y = 10;
z = foo()
