module Core.Types

type u8 = FStar.UInt8.t
type u32 = FStar.UInt32.t
type usize = FStar.SizeT.t
type slice = FStar.Seq.seq
type array t (l: usize) = s: FStar.Seq.seq t {FStar.Seq.length s == FStar.SizeT.v l}

// Move me to Range.Range.Rnage.etc
type range = {f_start: usize; f_end: usize}

class index self idx = {
  output: Type;
  in_range: self -> idx -> bool;
  (.[]): s:self -> i:idx {in_range s i} -> output;
}

class update_at self idx = {
  super_index: index self idx;
  (.[]<-): s: self -> i: idx {super_index.in_range s i} -> super_index.output -> self;
}

