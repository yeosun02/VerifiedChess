trait Piece 
  {

  var location: (int, int)
  var captured: bool

  function class_invariant(): bool
    reads this
  {
    0 <= location.0 < 8 && 0 <= location.1 < 8
  }
}

class Pawn extends Piece
  {
  
  function read_loc(): (int, int)
    reads this
  {
    (location.0, location.1)
  }
}