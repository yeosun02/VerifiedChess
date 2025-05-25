datatype Color = White | Black
datatype Piece = Pawn | Bishop | Knight | Rook | Queen | King
datatype Cell = Empty | Piece(color: Color, piece: Piece, moved: bool)

datatype Move = PieceMove(from: (int, int), to: (int, int), capture: bool) 
                | KingsideCastle
                | QueensideCastle

class Board {
    // I treat the grid as a row-major 2D array. The rows of the array
    // represent ranks of the chess board and the columns represent files. The
    // index order corresponds to the chess rank and file numbering/lettering
    // order. E.g. column 0 is file A and row 0 is rank 1.
    var grid: array2<Cell>

    function class_invariant(): bool
        reads this, grid
    {
        grid.Length0 == 8 &&
        grid.Length1 == 8
        // TODO: Number of each color's kings is exactly one.
        // Optional: We can make sure each piece count is not above a certain
        // amount.
    }

    // Helper function for initial_board.
    static function piece_at(i: int, j: int): Piece
        requires 0 <= i < 8
        requires 0 <= j < 8
        requires i <= 1 || i >= 6
    {
        if i == 1 || i == 6 then Pawn
        else if j == 0 || j == 7 then Rook
        else if j == 1 || j == 6 then Knight
        else if j == 2 || j == 5 then Bishop
        else if j == 3 then Queen
        else King
    }

    // Describe the initial board as a function.
    static function initial_board(i: int, j: int): Cell
        requires 0 <= i < 8
        requires 0 <= j < 8
    {
        if 2 <= i <= 5 then Empty else
            if i <= 1 then
                Piece(White, piece_at(i, j), false)
            else
                Piece(Black, piece_at(i, j), false)
    }

    constructor()
        ensures class_invariant() && fresh(grid)
    {
        grid := new Cell[8, 8](initial_board);
    }

    // Is the given move in the right range of the board?
    function MoveInRange(move: Move): bool
        requires move.PieceMove?
    {
        0 <= move.from.0 < 8 &&
        0 <= move.from.1 < 8 &&
        0 <= move.to.0 < 8 &&
        0 <= move.to.1 < 8
    }

    function NoCapturePre(move: Move): bool
        requires move.PieceMove? && !move.capture
        reads this, grid
        requires class_invariant()
    {
        && MoveInRange(move)
        && grid[move.from.0, move.from.1] != Empty
        && grid[move.to.0, move.to.1] == Empty
    }

    // Does this move describe a valid capture on the board?
    // TODO: Exceptions for en passant.
    function CapturePre(move: Move): bool
        requires move.PieceMove? && move.capture
        reads this, grid
        requires class_invariant()
    {
        && MoveInRange(move)
        && grid[move.from.0, move.from.1] != Empty
        && grid[move.to.0, move.to.1] != Empty
        && grid[move.from.0, move.from.1].color 
            != grid[move.to.0, move.to.1].color
    }

    // Is the board in the expected state after making the move?
    function PieceMovePost(move: Move, cell: Cell): bool
        requires move.PieceMove?
        reads this, grid
        requires class_invariant()
    {
        && MoveInRange(move)
        && grid[move.from.0, move.from.1] == Empty
        && cell.Piece?
        && grid[move.to.0, move.to.1] == Piece(cell.color, cell.piece, true)
    }

    // TODO: Verify counts of pieces. Actually, we need to ensure that all
    // other pieces are unchanged.
    method MakeMove(move: Move)
        requires class_invariant()
        modifies grid

        requires move.PieceMove? && !move.capture ==> NoCapturePre(move)
        requires move.PieceMove? && move.capture ==> CapturePre(move)

        ensures class_invariant()
        ensures old(grid) == grid // Reference is unchanged.

        ensures move.PieceMove? ==>
            PieceMovePost(move, old(grid[move.from.0, move.from.1]))
    {
        if move.PieceMove? {
            var cell := grid[move.from.0, move.from.1];
            grid[move.to.0, move.to.1] := Piece(
                cell.color, cell.piece, true
            );
            grid[move.from.0, move.from.1] := Empty;
        }
    }

    method ParseMove(s: string) returns (move: Move)
    {
        // 0-0: Kingside castling
        // 0-0-0: Queenside castling
        move := KingsideCastle;
    }

}

method TestBoard() {
    var board := new Board();

    board.grid[0, 0] := Piece(White, Rook, false);
    board.grid[7, 7] := Piece(Black, Rook, false);
    board.grid[7, 7] := Empty;
    board.MakeMove(PieceMove((0, 0), (7, 7), false));
    assert board.grid[0, 0] == Empty;
    assert board.grid[7, 7] != Empty;
    assert board.grid[7, 7].color == White;
    assert board.grid[7, 7].piece == Rook;
    assert board.grid[7, 7].moved == true;

    assert board.grid[7, 7] == Piece(White, Rook, true);
}
