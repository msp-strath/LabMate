k = 7;
foo()
k % still 7

  function t = foo()

    k = 1;

%> rename k base % should rename k to base inside foo, but not the outer k

% if we instead were to do
% %> rename k m
% then this should be an error, because m is captured at a use site of k

%> rename m i % this should be an error -- no m in scope in this block

    t = fac(4);

    function n = fac(m)
%> rename m i % should succeed, but not touch fac2
      if m == 0
        n = k;
      else
        n = m * fac(m-1);
      end
    end

    function n = fac2(m)
      if m == 0
        n = k;
      else
        n = m * fac2(m-1);
      end
    end

  end

