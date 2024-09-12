x = 5;
y = x + x;

%> rename x a
%> rename y b

function y = foo(x)
  y = x + 7;
  %>rename y c
end
