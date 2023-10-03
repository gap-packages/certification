InstallGlobalFunction(CertifiedFunction,
function(func, args...)
    local opts, certifunc, rnam, cf, type;
    # Make default options record
    opts := rec( funcname := NameFunction(func),
                 certifunc := ReturnTrue );

    # Import user options
    for rnam in RecNames(args[1]) do
      opts.(rnam) := args[1].(rnam);
    od;

  # Make the record
  cf := rec( func := func, 
             funcname := opts.funcname,
             certifunc := opts.certifunc);

  # Objectify
  type := NewType(FunctionsFamily, IsCertifiedFunction);
  cf := Objectify(type, cf);

  return cf;
end);


InstallMethod(CallFuncList,
"for a certified function",
[IsCertifiedFunction, IsList],
function(cf, args)
  local key, val, cert;
  val := CallFuncList(cf!.func, args);
  cert := CallFuncList(cf!.certifunc, Concatenation([val], args));
  return [val, cert];
end);


InstallMethod(ViewObj,
"for a certified function",
[IsCertifiedFunction],
function(cf)
  Print("<certified ");
  ViewObj(cf!.func);
  Print(">");
end);
