include "board.dfy"


method CanCaptureKing(possilbe_capture: Move, king_color: Color, king_rank: int, king_file: int, piece: Piece, board: Board) returns (kill_king: bool)
  requires possilbe_capture.PieceMove?
  requires board.piece_pre(possilbe_capture, piece)
  requires board.move_in_range(possilbe_capture)
  requires possilbe_capture.capture 
  requires board.capture_pre(possilbe_capture)
{
  match piece
  case Pawn => 
    return board.pawn_pre(possilbe_capture);
  case Rook =>
    return board.rook_pre(possilbe_capture);
  case Knight =>
    return board.knight_pre(possilbe_capture);
  case Bishop =>
    return board.bishop_pre(possilbe_capture);
  case Queen =>
    return board.queen_pre(possilbe_capture);
  case King =>
    return false;
}

method CheckChecker(king_rank: int, king_file: int, board: Board) returns (check: bool)
  requires 0 <= king_rank < 8 && 0 <= king_file < 8
  requires board.grid.Length0 == board.grid.Length1 == 8
  requires board.grid[king_rank, king_file].Piece?
  requires board.grid[king_rank, king_file].piece == King
  // ensures exists i, j :: 0 <= i < 8 && 0 <= j < 8 && board.grid[i, j]
{
  var king_color := board.grid[king_rank, king_file].color;
  var moves := new (int, int)[64](i => (-1, -1));
  var idx := 0;
  
  for i := 0 to board.grid.Length0
  {
    for j := 0 to board.grid.Length1
    {
      if board.grid[i, j] == Empty {
        continue;
      }
      if board.grid[i, j].color != king_color {
        var possilbe_capture := PieceMove((i, j), (king_rank, king_file), capture := true);
        check := CanCaptureKing(possilbe_capture, king_color, king_rank, king_file, board.grid[i, j].piece, board);
        if check {
          return;
        }
      }
    }
  }
  
  return false;
}

method Test() 
{
  var board := new Board();
  assert board.class_invariant();
  var is_check := CheckChecker(7, 4, board);
  // assert !is_check;
  // board.grid[0,0] := Piece()
}