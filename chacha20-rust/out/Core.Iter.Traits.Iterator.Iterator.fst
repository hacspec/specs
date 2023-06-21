module Core.Iter.Traits.Iterator.Iterator

open Core.Types

class tc self = {
  item: Type;
  next: self -> self * option item;
  size_hint: self -> option usize;
  fold: b:Type -> self -> b -> (b -> item -> b) -> b
}

