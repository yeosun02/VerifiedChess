include "board.dfy"



method CanCaptureKing(possilbe_capture: Move, king_rank: int, king_file: int, piece: Piece, board: Board) returns (kill_king: bool)
  requires possilbe_capture.PieceMove?
  requires board.move_in_range(possilbe_capture)
  requires possilbe_capture.capture 
  requires board.CapturePre(possilbe_capture)
{
  match piece
  case Pawn => 
    return board.PawnPre(possilbe_capture);
  case Rook =>
  case Knight =>
  case Bishop =>
  case Queen =>
  case King =>
}

method CheckChecker(king_color: Color, king_rank: int, king_file: int, board: Board) returns (check: bool)
  requires 0 <= king_rank < 8 && 0 <= king_file < 8
  requires board.grid.Length0 == board.grid.Length1 == 8
{
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
        check := CanCaptureKing(possilbe_capture, king_rank, king_file, board.grid[i, j].piece, board);
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

}