datatype Color = White | Black
datatype Piece = Pawn | Bishop | Knight | Rook | Queen | King
datatype Cell = Empty | Piece(color: Color, piece: Piece, moved: bool)

datatype Move = PieceMove(from: (int, int), to: (int, int), capture: bool) 
                | Castle(color: Color, kingside: bool) | EnPassant(from: (int, int), to: (int, int), color: Color) | PawnPromotion(from: (int, int), to: (int, int), color: Color, newPiece: Piece)

class Board {
    // I treat the grid as a row-major 2D array. The rows of the array
    // represent ranks of the chess board and the columns represent files. The
    // index order corresponds to the chess rank and file numbering/lettering
    // order. E.g. column 0 is file A and row 0 is rank 1.
    var grid: array2<Cell>

    // Keep track of moves for special cases like en passant
    var moves: seq<Move>

    function class_invariant(): bool
        reads this, grid
    {
        grid.Length0 == 8 &&
        grid.Length1 == 8 &&
        |moves| >= 0
        // TODO: Number of each color's kings is exactly one.
        // Optional: We can make sure each piece count is not above a certain
        // amount.
    }

    // Helper function for creating the initial_board.
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
        ensures forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> grid[i, j] == initial_board(i, j)
    {
        grid := new Cell[8, 8](initial_board);
        moves := [];
    }

    // Is the given move in the right range of the board?
    function MoveInRange(move: Move): bool
        requires move.PieceMove? || move.EnPassant?
    {
        0 <= move.from.0 < 8 &&
        0 <= move.from.1 < 8 &&
        0 <= move.to.0 < 8 &&
        0 <= move.to.1 < 8
    }

    // This is a precondition for a normal move, to and from must be in bounds,
    // the source cell must have a piece, and the destination cell must be empty
    function NoCapturePre(move: Move): bool
        requires move.PieceMove? && !move.capture
        reads this, grid
        requires class_invariant()
        requires MoveInRange(move)
    {
        && grid[move.from.0, move.from.1] != Empty
        && grid[move.to.0, move.to.1] == Empty
    }

    // Does this move describe a valid capture on the board?
    // TODO: Exceptions for en passant.
    function CapturePre(move: Move): bool
        requires move.PieceMove? || move.EnPassant?
        requires move.PieceMove? ==> move.capture
        reads this, grid
        requires MoveInRange(move)
        requires class_invariant()
    {
        && MoveInRange(move)
        && grid[move.from.0, move.from.1] != Empty
        && grid[move.to.0, move.to.1] != Empty
        && grid[move.from.0, move.from.1].color 
            != grid[move.to.0, move.to.1].color
    }

    // Is the board in the expected state after making the move?
    // Have NO OTHER cells been modified?
    // TODO: Conditions for En Passant, Castling
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

    function CastlePre(move: Move): bool
        requires move.Castle?
        reads this, grid
        requires class_invariant()
    {
        var rank := if move.color == White then 0 else 7;
        var rookfile := if move.kingside then 7 else 0;

        && grid[rank, 4] == Piece(move.color, King, false)
        && grid[rank, rookfile] == Piece(move.color, Rook, false)
        && (move.kingside ==>
            && grid[rank, 5] == Empty
            && grid[rank, 6] == Empty
        )
        && (!move.kingside ==>
            && grid[rank, 1] == Empty
            && grid[rank, 2] == Empty
            && grid[rank, 3] == Empty
        )
    }

    function CastlePost(move: Move): bool
        requires move.Castle?
        reads this, grid
        requires class_invariant()
    {
        var rank := if move.color == White then 0 else 7;
        var rookfile := if move.kingside then 7 else 0;

        && grid[rank, 4] == Empty
        && grid[rank, rookfile] == Empty
        && (move.kingside ==>
            && grid[rank, 5] == Piece(move.color, Rook, true)
            && grid[rank, 6] == Piece(move.color, King, true)
        )
        && (!move.kingside ==>
            && grid[rank, 1] == Empty
            && grid[rank, 2] == Piece(move.color, King, true)
            && grid[rank, 3] == Piece(move.color, Rook, true)
        )
    }

    predicate PiecePre(move: Move, piece: Piece)
    reads this, this.grid
    {
        move.PieceMove? &&
        class_invariant() &&
        MoveInRange(move) &&
        (move.capture == false ==> NoCapturePre(move)) &&
        (move.capture == true ==> CapturePre(move)) //&&
        
        // grid[move.from.0, move.from.1] != Empty &&
        // grid[move.from.0, move.from.1].piece == piece &&
        // grid[move.to.0, move.to.1] == Empty
    }

    predicate PawnPre(move: Move)
        reads this, this.grid
        requires PiecePre(move, Pawn)
    {
        var cell := grid[move.from.0, move.from.1];
        var color := cell.color;
        var from := move.from;
        var to := move.to;

        match color
        case White =>
            // Forward direction: increase rank (row number)
            if !move.capture then
                (to.1 == from.1) &&
                (
                    (to.0 == from.0 + 1) || // single step
                    (from.0 == 1 && to.0 == from.0 + 2 && grid[from.0 + 1, from.1] == Empty) // double step from start
                )
            else // Pawn capture case
                (to.0 == from.0 + 1) && // Moves up a row
                (to.1 == from.1 + 1 || to.1 == from.1 - 1) //&& // Moves Diagonal 1
                // (grid[to.0, to.1] != Empty) // There's a piece at the destination
        case Black =>
            if !move.capture then
                (to.1 == from.1) &&
                (
                (to.0 == from.0 - 1) ||
                (from.0 == 6 && to.0 == from.0 - 2 && grid[from.0 - 1, from.1] == Empty))
            else
                (to.0 == from.0 - 1) &&
                (to.1 == from.1 + 1 || to.1 == from.1 - 1) &&
                grid[to.0, to.1] != Empty
    }

    predicate RookPre(move: Move)
        reads this, this.grid
        requires PiecePre(move, Rook)
    {
        var from := move.from;
        var to := move.to;
        var fromCell := grid[from.0, from.1];
        // 1. Establish Direction
        // 2. Ensure that everything on the way to the destination is free (if not a capture), else last space must have a piece
        // for each direction
        if to.0 > from.0 && to.1 == from.1 // UP (from increasing)
        then 
            (move.capture &&
            (forall i :: from.0 < i < to.0 ==> grid[i, to.1] == Empty) &&
            grid[to.0, to.1] != Empty &&
            grid[to.0, to.1].color != fromCell.color
            ) ||
            (!move.capture &&
            (forall i :: from.0 < i <= to.0 ==> grid[i, to.1] == Empty))
        else if to.0 < from.0 && to.1 == from.1 // DOWN
        then
            (move.capture &&
            (forall i :: to.0 < i < from.0 ==> grid[i, to.1] == Empty) &&
            grid[to.0, to.1] != Empty &&
            grid[to.0, to.1].color != fromCell.color
            ) ||
            (!move.capture &&
            (forall i :: to.0 <= i < from.0 ==> grid[i, to.1] == Empty))
        else if to.1 > from.1 && to.0 == from.0 // RIGHT
        then
            (move.capture &&
            (forall i :: from.1 < i < to.1 ==> grid[to.0, i] == Empty) &&
            grid[to.0, to.1] != Empty &&
            grid[to.0, to.1].color != fromCell.color
            ) ||
            (!move.capture &&
            (forall i :: from.1 < i <= to.1 ==> grid[to.0, i] == Empty))
        else if to.1 < from.1 && to.0 == from.0 // LEFT
        then
            (move.capture &&
            (forall i :: to.1 < i < from.1 ==> grid[to.0, i] == Empty) &&
            grid[to.0, to.1] != Empty &&
            grid[to.0, to.1].color != fromCell.color
            ) ||
            (!move.capture &&
            (forall i :: to.1 <= i < from.1 ==> grid[to.0, i] == Empty))
        else false
    }

    predicate KnightPre(move: Move)
        reads this, this.grid
        requires PiecePre(move, Knight)
    {
        var from := move.from;
        var to := move.to;
        var fromCell := grid[from.0, from.1];

        // Valid knight L-shaped move
        var dx := if from.0 > to.0 then from.0 - to.0 else to.0 - from.0;
        var dy := if from.1 > to.1 then from.1 - to.1 else to.1 - from.1;

        ((dx == 2 && dy == 1) || (dx == 1 && dy == 2)) &&
        (
            (!move.capture && grid[to.0, to.1] == Empty) ||
            (move.capture &&
            grid[to.0, to.1] != Empty &&
            grid[to.0, to.1].color != fromCell.color)
        )
    }

    predicate LegalMoveChecker(move: Move)
    reads this, grid
    requires class_invariant()
    requires move.PieceMove? || move.EnPassant? ==> MoveInRange(move)
    {
        match move
        case PieceMove(from, to, capture) => (
            MoveInRange(move) &&
            match move.capture
            case true => (
                CapturePre(move) &&
                match grid[move.from.0, move.from.1].piece
                case Pawn => PawnPre(move)
                case Rook => RookPre(move)
                case Knight => KnightPre(move)
                case _ => false
            )
            case false =>
            (
                NoCapturePre(move) &&
                match grid[move.from.0, move.from.1].piece
                case Pawn => PawnPre(move)
                case Rook => RookPre(move)
                case Knight => KnightPre(move)
                case _ => false
            )
        )
        case Castle(color, kingside) =>
            CastlePre(move)
        case EnPassant(from, to, color) =>
            // true
            EnPassantPre(move) // Not yet implemented
        case PawnPromotion(_, _, _, _) =>
            false // Not yet implemented
    }

    predicate EnPassantPre(move: Move)
        reads this, this.grid
        requires class_invariant()
        requires move.EnPassant?
        requires MoveInRange(move)
    {

        var from := move.from;
        var to := move.to;
        var cell := grid[from.0, from.1];
        var color := move.color;

        cell != Empty &&
        cell.piece == Pawn &&
        grid[to.0, to.1] == Empty &&

        if color == White then
            from.0 == 4 && // White must be on rank 5
            to.0 == 5 &&
            (to.1 == from.1 + 1 || to.1 == from.1 - 1) &&
            // The captured pawn must be a Black pawn
            var capturedCol := to.1;
            grid[4, capturedCol] == Piece(Black, Pawn, true) &&
            |moves| > 0 &&
            moves[|moves| - 1] == PieceMove((6, capturedCol), (4, capturedCol), false)
        else
            from.0 == 3 && // Black must be on rank 4
            to.0 == 2 &&
            (to.1 == from.1 + 1 || to.1 == from.1 - 1) &&
            var capturedCol := to.1;
            // The captured pawn must be a White pawn
            grid[3, capturedCol] == Piece(White, Pawn, true) &&
            |moves| > 0 &&
            moves[|moves| - 1] == PieceMove((1, capturedCol), (3, capturedCol), false)
    }

    function EnPassantPost(move: Move, oldGrid: array2<Cell>): bool
        requires move.EnPassant?
        reads this, this.grid, oldGrid
        requires class_invariant()
        requires MoveInRange(move)
        requires this.grid.Length0 == oldGrid.Length0 && this.grid.Length1 == oldGrid.Length1
    {
        var from := move.from;
        var to := move.to;
        var fromCell := grid[from.0, from.1];
        var toCell := grid[to.0, to.1];
        var capturedCell := grid[from.0, to.1];
        // assume this.grid.Length0 == oldGrid.Length0 && this.grid.Length1 == oldGrid.Length1;

        // Check the pawn has moved to the destination
        toCell != Empty &&
        toCell.piece == Pawn &&
        ((move.color == White && toCell.color == White) || ((move.color == Black) && toCell.color == Black)) &&
        toCell.moved == true &&
        fromCell == Empty &&
        // The captured pawn has been removed
        grid[from.0, to.1] == Empty //&&
        // All other squares have been unchanged
        // forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 && (i, j) != (from.0, from.1) && (i, j) != (to.0, to.1) && (i, j) != (from.0, to.1) ==> this.grid[i, j] == oldGrid[i, j]
    }

    // TODO: Verify counts of pieces. Actually, we need to ensure that all
    // other pieces are unchanged.
    method MakeMove(move: Move)
        modifies this, grid
        requires class_invariant()
        requires move.PieceMove? || move.EnPassant? ==> MoveInRange(move)
        requires LegalMoveChecker(move)

        ensures class_invariant()
        ensures move.PieceMove? ==> PieceMovePost(move, old(grid[move.from.0, move.from.1]))
        ensures move.Castle? ==> CastlePost(move)
        ensures move.EnPassant? ==> EnPassantPost(move, old(this.grid))
        ensures move.EnPassant? ==> 
            forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 && (i, j) != (move.from.0, move.from.1) && (i, j) != (move.to.0, move.to.1) && (i, j) != (move.from.0, move.to.1) ==> grid[i, j] == old(grid[i, j])

        ensures this.moves == old(this.moves) + [move]
        ensures this.grid == old(this.grid) // Needed for some reason

        // Ensure NOTHING ELSE CHANGED IN THE BOARD
        ensures move.PieceMove? ==> forall i, j :: 0 <= i < this.grid.Length0 && 0 <= j < this.grid.Length1 && (i, j) != move.from && (i, j) != move.to ==> this.grid[i, j] == old(this.grid[i, j])

        // TODO: Ensure nothing else changed in the board for Castle, then En Passant

        // Ensure the move was added, and that the rest of the sequence is the same
        ensures this.moves == old(this.moves) + [move]
    {
        if move.PieceMove? {
            var cell := grid[move.from.0, move.from.1];

            match cell.piece
            case Pawn =>
                // Pretty much the lemmas / predicates go here
                var cell := grid[move.from.0, move.from.1];
                grid[move.to.0, move.to.1] := Piece(
                    cell.color, cell.piece, true
                );
                grid[move.from.0, move.from.1] := Empty;
            case _ =>
                var cell := grid[move.from.0, move.from.1];
                grid[move.to.0, move.to.1] := Piece(
                    cell.color, cell.piece, true
                );
                grid[move.from.0, move.from.1] := Empty;
        } else if move.Castle? {
            var rank := if move.color == White then 0 else 7;
            var rookfile := if move.kingside then 7 else 0;
            if move.kingside {
                grid[rank, 5] := Piece(move.color, Rook, true);
                grid[rank, 6] := Piece(move.color, King, true);
                grid[rank, 7] := Empty;
            } else {
                grid[rank, 0] := Empty;
                grid[rank, 2] := Piece(move.color, King, true);
                grid[rank, 3] := Piece(move.color, Rook, true);
            }
            grid[rank, 4] := Empty;
        } else if move.EnPassant? {
            var cell := grid[move.from.0, move.from.1];
            var from := move.from;
            var to := move.to;

            match cell.color
            case White =>
                // 1. Move White Pawn
                grid[to.0, to.1] := Piece(move.color, Pawn, true);
                grid[from.0, from.1] := Empty;

                // 2. Capture Black Pawn (Just set it to empty for now TODO)
                grid[from.0, to.1] := Empty;

            case Black =>
                // 1. Move Black Pawn
                grid[to.0, to.1] := Piece(move.color, Pawn, true);
                grid[from.0, from.1] := Empty;

                // 2. Capture White Pawn
                grid[from.0, to.1] := Empty;
        }

        // Add the move to the moves list
        this.moves := this.moves + [move];
    }

    method ParseMove(s: string) returns (move: Move)
    {
        // 0-0: Kingside castling
        // 0-0-0: Queenside castling
        move := Castle(White, true);
    }

}

method TestBoard() {
    var board := new Board();

    board.grid[0, 0] := Piece(White, Rook, false);
    board.grid[0, 7] := Piece(White, Rook, false);
    board.grid[7, 0] := Piece(Black, Rook, false);
    board.grid[7, 7] := Piece(Black, Rook, false);
    board.grid[0, 5] := Empty;
    board.grid[0, 6] := Empty;
    // board.grid[7, 7] := Empty;
    // board.MakeMove(PieceMove((0, 0), (7, 7), false));
    // assert board.grid[0, 0] == Empty;
    //assert board.grid[7, 7] != Empty;
    //assert board.grid[7, 7].color == White;
    //assert board.grid[7, 7].piece == Rook;
    //assert board.grid[7, 7].moved == true;

    // //assert board.grid[7, 7] == Piece(White, Rook, true);

    // board.grid[0, 4] := Piece(White, King, false);
    // board.grid[7, 4] := Piece(Black, King, false);

    // board.MakeMove(Castle(White, true));
    //board.MakeMove(Castle(White, false));

    // // Test Pawn Normal Moves
    // var pawns := new Board();
    // var move := PieceMove((1,0), (2,0), false);
    // // assert forall i, j :: 0 <= i < pawns.grid.Length0 && 0 <= j < pawns.grid.Length1 ==> pawns.grid[i, j] == pawns.initial_board(i, j);
    // // assert pawns.grid[1, 0].Piece?;
    // // assert pawns.grid[1, 0].piece == Pawn;
    // // assert pawns.grid[2, 0].Empty?;
    // pawns.MakeMove(move);
    // assert pawns.grid[2, 0].piece == Pawn;
    // assert pawns.grid[1, 0].Empty?;
    // move := PieceMove((2,0), (3,0), false);
    // pawns.MakeMove(move);
    // assert pawns.grid[3, 0].piece == Pawn;
    // // move := PieceMove((3,0), (5,0), false);
    // // pawns.MakeMove(move); // This fails (as it should since it's an invalid move)

    // move := PieceMove((1,1), (3,1), false);
    // pawns.MakeMove(move);
    // assert pawns.grid[1, 1].Empty?;
    // assert pawns.grid[3,1].piece == Pawn;
    // assert pawns.moves[|pawns.moves| - 1] == move; // we really only care about the last move

    // move := PieceMove((6,1), (4,1), false);
    // pawns.MakeMove(move);
    // assert pawns.grid[6,1].Empty?;
    // assert pawns.grid[4, 1].piece == Pawn;

    // //// Test Pawn Capture Moves

    // var pawnCapture := new Board();
    // pawnCapture.grid[2,1] := Piece(Black, Pawn, false);
    // move := PieceMove((1,0), (2,1), true);
    // pawnCapture.MakeMove(move);
    // assert pawnCapture.grid[2,1].color == White;
    // assert pawnCapture.grid[1, 0].Empty?;

    // pawnCapture.grid[6,3] := Piece(White, Queen, false);
    // move := PieceMove((7,2), (6,3), true);
    // pawnCapture.MakeMove(move);
    // assert pawnCapture.grid[6,3].color == Black;
    // assert pawnCapture.grid[7,2].Empty?;

    // // En Passant Tester
    // var pawnEnPassant := new Board();
    // move := PieceMove((1,0), (3,0), false);
    // // Move
    // pawnEnPassant.MakeMove(move);
    // move := PieceMove((3,0), (4,0), false);
    // pawnEnPassant.MakeMove(move);
    // // Black pawn moves forward 2, opening up En Passant for white pawn at 4,0
    // move := PieceMove((6,1), (4,1), false);
    // pawnEnPassant.MakeMove(move);
    // assert pawnEnPassant.grid[4,1].color == Black;
    // assert pawnEnPassant.grid[4,0].color == White;

    // move := EnPassant((4,0), (5,1), White);
    // pawnEnPassant.MakeMove(move);
    // assert pawnEnPassant.grid[4,1].Empty?;
    // assert pawnEnPassant.grid[5,1].color == White;
    // assert pawnEnPassant.grid[6, 6].color == Black; // Making sure some random piece is still in the right spot
    // assert pawnEnPassant.grid[7,0].piece == Rook;

    // // Move a random piece
    // pawnEnPassant.MakeMove(PieceMove((7,1), (6,1), false));
    // assert pawnEnPassant.grid[6,1].color == Black;

    // // Test Black En Passant
    // pawnEnPassant.MakeMove(PieceMove((6, 5), (4, 5), false)); // Black Pawn forward 2
    // pawnEnPassant.MakeMove(PieceMove((4, 5), (3, 5), false)); // Black Pawn forward 1
    // pawnEnPassant.MakeMove(PieceMove((1, 6), (3, 6), false)); // White Pawn forward 2 (Black is now setup for en passant)
    // pawnEnPassant.MakeMove(EnPassant((3, 5), (2, 6), Black)); // Black En Passant
    // assert pawnEnPassant.grid[2,6].color == Black;
    // assert pawnEnPassant.grid[2,6].piece == Pawn;
    // assert pawnEnPassant.grid[3,6].Empty?;

    // // Move a random piece (this captures)
    // pawnEnPassant.MakeMove(PieceMove((6,1), (5,1), true));
    // assert pawnEnPassant.grid[5,1].color == Black;

    // // Testing Rook
    // var rookTest := new Board();
    // // Move pawns out of the way
    // rookTest.MakeMove(PieceMove((6,0), (4,0), false)); // Move left black pawn down
    // rookTest.MakeMove(PieceMove((1,0), (3,0), false)); // Move left white pawn up

    // rookTest.MakeMove(PieceMove((0,0), (2,0), false)); // Move left white rook up
    // rookTest.MakeMove(PieceMove((7,0), (5,0), false)); // Move left black rook down
    // assert rookTest.grid[2,0].color == White && rookTest.grid[2,0].piece == Rook;
    // assert rookTest.grid[5,0].color == Black && rookTest.grid[5,0].piece == Rook;

    // // Testing Rook Capture
    // rookTest.MakeMove(PieceMove((5,0), (5,5), false)); // Move left black rook right
    // rookTest.MakeMove(PieceMove((5,5), (1,5), true)); // Move left black rook down and capture a pawn
    // assert rookTest.grid[1,5].color == Black && rookTest.grid[1,5].piece == Rook;

    // Testing Knight
    var knightBoard := new Board();
    knightBoard.MakeMove(PieceMove((0,1), (2,2), false));
    knightBoard.MakeMove(PieceMove((7,1), (5,2), false));
    assert knightBoard.grid[2,2].piece == Knight && knightBoard.grid[2,2].color == White;
    assert knightBoard.grid[5,2].piece == Knight && knightBoard.grid[5,2].color == Black;
    // Testing Knight Capture
    // knightBoard.MakeMove(PieceMove((5,2), (4,3), false)); // This should fail
    knightBoard.MakeMove(PieceMove((1,3), (3,3), false));
    assert knightBoard.grid[3,3].piece == Pawn && knightBoard.grid[3,3].color == White;
    knightBoard.MakeMove(PieceMove((5,2), (3,3), true)); // Knight Capture
    assert knightBoard.grid[3,3].piece == Knight && knightBoard.grid[3,3].color == Black;
}
