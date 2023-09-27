
f1()

function f1()
  % This is an example of a renaming the Matlab editor gets wrong.
  % It should be disallowed, because it captures w in f2.

  %> rename x z

  x = 5;
  f2();
  disp(x);

  function y = f2()
    z = 7;
    y = z;
  end
end
