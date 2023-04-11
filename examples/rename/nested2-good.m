
f1()

function x = f1()

  % This should be allowed, because w in f2 is not capturable.

  %> rename z w
  z = 5;
  k = f2(43);
  x = z;

  function y = f2(w)
    w = 7;
    y = w;
  end
end
