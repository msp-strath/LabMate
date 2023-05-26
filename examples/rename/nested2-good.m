%< LabRat 0.1.2.2

f1()

function x = f1()

  % This should be allowed, because w in f2 is not capturable.

  %< renamed z w % this is a comment
  w = 5;
  k = f2(43);
  x = w;

  function y = f2(w)
    w = 7;
    y = w;
  end
end
