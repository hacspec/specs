module Core.Ops

open Core.Types

class add_tc self rhs = {
  output: Type;
  in_bounds: self -> rhs -> Type0;
  (+.): x:self -> y:rhs {in_bounds x y} -> output;
}

open FStar.UInt32

instance _: add_tc u32 u32 = {
  output = u32;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 32);
  (+.) = (fun x y -> x +^ y)
}

