module Int32 {
  newtype {:nativeType "int"} t = x | -2000000 <= x < 2000001
  const max : t := 2000000;
  const min : t := -2000000;
  
  ghost method test(x : t) {
    var m1 : t := -x;
  }
}
