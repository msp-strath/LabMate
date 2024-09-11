
f1()

function x = f1()
  % This is an example of a renaming the Matlab editor gets wrong.
  % It should be disallowed, because it captures w in f2.

  %> rename z w

  z = 5;
  k = f2();
  x = z;

  function y = f2()
    w = 7;
    y = w;
  end
end

