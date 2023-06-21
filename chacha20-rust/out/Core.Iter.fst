module Core.Iter

open Core.Types

class iterator self = {
  item: Type;
  next: self -> self * option item;
  size_hint: self -> option usize;
  fold: #b:Type -> self -> b -> (b -> item -> b) -> b
}

open Core.Ops.Range.Range

instance iterator_array t len: iterator (array t len) = {
  item = t;
  next = (fun s -> admit ());
  size_hint = (fun s -> Some (admit ()));
  fold = (fun #b s init f -> admit ())
}

let rec fold_range'
  (min: SizeT.t) (max: SizeT.t {SizeT.v min <= SizeT.v max})
  (init: 'a) (f: 'a -> usize -> 'a)
  : Tot 'a (decreases (SizeT.v max - SizeT.v min))
  = let open FStar.SizeT in
    if min = max
    then init
    else fold_range' (min +^ 1sz) max (f init min) f
  
instance iterator_range: iterator range = 
  let open FStar.SizeT in
  {
  item = usize;
  next = (fun {f_start; f_end} -> 
    if f_start <^ f_end
    then ({f_start = f_start `SizeT.add` 1sz; f_end}, Some f_start)
    else ({f_start; f_end}, None)
  );
  size_hint = (fun {f_start; f_end} -> 
    Some (if f_start <^ f_end
          then f_end -^ f_start 
          else 0sz)
  );
  fold = (fun #b r init f -> 
    if r.f_start <^ r.f_end
    then fold_range' r.f_start r.f_end init f
    else init
  );
}

instance range_index t len : index (array t len) range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) {f_start; f_end} -> 
    SizeT.v f_start <= SizeT.v len &&
    SizeT.v f_end   <= SizeT.v len
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start `SizeT.lt` f_end
      then Seq.slice arr (SizeT.v f_start) (SizeT.v f_end)
      else Seq.empty
    );
}

instance range_index_slice t : index (slice t) Core.Ops.Range.Range.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: slice t) {f_start; f_end} -> 
    SizeT.v f_start <= Seq.length arr &&
    SizeT.v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start `SizeT.lt` f_end
      then Seq.slice arr (SizeT.v f_start) (SizeT.v f_end)
      else Seq.empty
    );
}

module RangeTo = Core.Ops.Range.RangeTo

instance rangeTo_index t len : index (array t len) RangeTo.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) { RangeTo.f_end } -> 
    SizeT.v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr { f_end } -> 
      Seq.slice arr 0 (SizeT.v f_end)
    );
}

module RangeFrom = Core.Ops.Range.RangeFrom

instance rangeFrom_index t len : index (array t len) RangeFrom.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) { RangeFrom.f_start } -> 
    SizeT.v f_start < SizeT.v len
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (SizeT.v f_start) (Seq.length arr)
    );
}

instance rangeFrom_index_slice t : index (slice t) RangeFrom.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: slice t) { RangeFrom.f_start } -> 
    SizeT.v f_start < Seq.length arr
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (SizeT.v f_start) (Seq.length arr)
    );
}

let into_iter = id
