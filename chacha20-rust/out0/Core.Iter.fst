module Core.Iter

open Core.Types

class iterator self = {
  item: Type;
  next: self -> self * option item;
  size_hint: self -> option usize;
  fold: #b:Type -> self -> b -> (b -> item -> b) -> b
}

// class into_iter_tc self = {
//   ii_item: Type;
//   into_iter_t: Type;
//   into_iter_super_iterator: iterator into_iter_t;

//   into_iter: self -> into_iter_t;
// }

open FStar.Seq
instance iterator_array t len: iterator (array t len) = {
  item = t;
  next = (fun s -> admit ());
  // next = (fun s -> s.[0], Some(slice s 1 (length s - 1));
  size_hint = (fun s -> Some (admit ()));
  fold = (fun #b s init f -> admit ())
}

open FStar.SizeT
let rec fold_range'
  (min: SizeT.t) (max: SizeT.t {v min <= v max})
  (init: 'a) (f: 'a -> usize -> 'a)
  : Tot 'a (decreases (v max - v min))
  = if min = max
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


let into_iter = id
// instance into_iter_tc_range: into_iter_tc range = {
//   ii_item = usize;
//   into_iter_t = range;
//   into_iter_super_iterator = iterator_range;
//   into_iter = id;
// }
