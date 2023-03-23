function [] = nestedrename()

  function x = f1()
    %> rename x y
    x = 5;
  end

  function y = f2()
    y = 7;
  end

end
