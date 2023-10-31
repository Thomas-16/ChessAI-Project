using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using static System.Math;

namespace ChessChallenge.Example
{
    // A simple bot that can spot mate in one, and always captures the most valuable piece it can.
    // Plays randomly otherwise.
    public class EvilBot : IChessBot
    {
        private static int[] pieceValues = { 0, 100, 320, 330, 500, 900, 20000 };
        private const int MAX_KILLER_MOVES = 3;

        private int MaxDepth = 0; // Adjust as necessary
                                  //private TranspositionTable transpositionTable = new TranspositionTable();
        private List<Move> killerMoves = new List<Move>(MAX_KILLER_MOVES);
        //public Dictionary<ulong, TranspositionTableEntry> transpositionTable = new Dictionary<ulong, TranspositionTableEntry>();
        TranspositionTable transpositionTable = new TranspositionTable();


        private static readonly string path = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "resources", "Book.txt");
        private OpeningBook openingBook = new OpeningBook(File.ReadAllText(path));
        private bool isWhite;
        private string lastSearchedPos;
        private int positionsSearched = 0;



        // Square values can be calculated by bit shifting
        private ulong centerSquares = ((ulong)1 << new Square("e4").Index)
                            | ((ulong)1 << new Square("d4").Index)
                            | ((ulong)1 << new Square("e5").Index)
                            | ((ulong)1 << new Square("d5").Index)
                            | ((ulong)1 << new Square("c3").Index)
                            | ((ulong)1 << new Square("f3").Index)
                            | ((ulong)1 << new Square("c6").Index)
                            | ((ulong)1 << new Square("f6").Index)
                            | ((ulong)1 << new Square("c4").Index)
                            | ((ulong)1 << new Square("f4").Index)
                            | ((ulong)1 << new Square("c5").Index)
                            | ((ulong)1 << new Square("f5").Index)
                            | ((ulong)1 << new Square("d3").Index)
                            | ((ulong)1 << new Square("e3").Index)
                            | ((ulong)1 << new Square("d6").Index)
                            | ((ulong)1 << new Square("e6").Index);


        #region Piece-Square Tables
        private static readonly int[] PawnTable = new int[64] {
        0,  0,  0,  0,  0,  0,  0,  0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
         5,  5, 10, 25, 25, 10,  5,  5,
         0,  0,  0, 40, 40,  0,  0,  0,
         5, -5, 15,  0,  0, 15, -5,  5,
         5, 10, 10,-20,-20, 10, 10,  5,
         0,  0,  0,  0,  0,  0,  0,  0
    };
        private static readonly int[] PawnEndGameTable = new int[64] {
        0,  0,  0,  0,  0,  0,  0,  0,
        90, 90, 90, 90, 90, 90, 90, 90,
         60, 60, 60, 60, 60, 60, 60, 60,
         40, 40, 40, 40, 40, 40, 40, 40,
         20, 20, 20, 20, 20, 20, 20, 20,
         10, 10, 10, 10, 10, 10, 10, 10,
         10, 10, 10, 10, 10, 10, 10, 10,
         0,  0,  0,  0,  0,  0,  0,  0
    };
        private static readonly int[] KnightTable = new int[64] {
        -50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20,  0,  0,  0,  0,-20,-40,
        -30,  0, 10, 15, 15, 10,  0,-30,
        -30,  5, 15, 20, 20, 15,  5,-30,
        -30,  0, 15, 20, 20, 15,  0,-30,
        -30,  5, 30, 15, 15, 30,  5,-30,
        -40,-20,  0,  5,  5,  0,-20,-40,
        -50,-40,-30,-30,-30,-30,-40,-50,
    };

        private static readonly int[] BishopTable = new int[64] {
        -20,-10,-10,-10,-10,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5, 10, 10,  5,  0,-10,
        -10,  5,  5, 10, 10,  5,  5,-10,
        -10,  0, 10, 10, 10, 10,  0,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10,  5,  0,  0,  0,  0,  5,-10,
        -20,-10,-10,-10,-10,-10,-10,-20,
    };

        private static readonly int[] RookTable = new int[64] {
        0,  0,  0,  0,  0,  0,  0,  0,
          5, 10, 10, 10, 10, 10, 10,  5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
          0,  0,  0,  5,  5,  0,  0,  0
    };

        private static readonly int[] QueenTable = new int[64] {
        -20,-10,-10, -5, -5,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5,  5,  5,  5,  0,-10,
         -5,  0,  5,  5,  5,  5,  0, -5,
          0,  0,  5,  5,  5,  5,  0, -5,
        -10,  5,  5,  5,  5,  5,  0,-10,
        -10,  0,  5,  0,  0,  0,  0,-10,
        -20,-10,-10,  0, -5,-10,-10,-20
    };

        private static readonly int[] KingMiddleGameTable = new int[64] {
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
         20, 20,  0,  0,  0,  0, 20, 20,
         20, 30, 20,-10,  0, 10, 30, 20
    };
        private static readonly int[] KingEndGameTable = new int[64] {
        -50,-40,-30,-20,-20,-30,-40,-50,
        -30,-20,-10,  0,  0,-10,-20,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-30,  0,  0,  0,  0,-30,-30,
        -50,-30,-30,-30,-30,-30,-30,-50
    };
        private static readonly int[] KingEndEndGameTable = new int[64] {
        -50,-50,-50,-50,-50,-50,-50,-50,
        -50,-30,-30,-30,-30,-30,-30,-50,
        -50,-30,  0,  0,  0,  0,-30,-50,
        -50,-30,  0, 10, 10,  0,-30,-50,
        -50,-30,  0, 10, 10,  0,-30,-50,
        -50,-30,  0,  0,  0,  0,-30,-50,
        -50,-30,-30,-30,-30,-30,-30,-50,
        -50,-50,-50,-50,-50,-50,-50,-50
    };
        #endregion

        public enum ScoreType { Exact, Alpha, Beta }
        public struct TranspositionTableEntry
        {
            public int Depth;
            public int Score;
            public Move BestMove;
            public int Flag; // 0 = exact, 1 = lower bound, 2 = upper bound
        }


        public class TranspositionTable
        {
            private const int TableSize = 1 << 24; // Adjust based on memory constraints
            private readonly CacheItem[] table;
            private int entries = 0;

            public TranspositionTable() {
                table = new CacheItem[TableSize];
            }

            private struct CacheItem
            {
                public ulong Key;
                public int Score;
                public Move BestMove;
                public int Depth;
                public ScoreType ScoreType;
            }

            public void Add(ulong boardHash, int score, Move bestMove, int depth, ScoreType scoreType) {
                int index = (int)(boardHash % TableSize);
                CacheItem cacheItem = new() {
                    Key = boardHash,
                    Score = score,
                    BestMove = bestMove,
                    Depth = depth,
                    ScoreType = scoreType
                };
                table[index] = cacheItem; // Overwrite the existing entry if any
                entries++;
            }

            public (int? score, Move bestMove, int? depth, ScoreType? scoreType) Get(ulong boardHash) {
                int index = (int)(boardHash % TableSize);
                CacheItem cacheItem = table[index];
                if (cacheItem.Key == boardHash) {
                    return (cacheItem.Score, cacheItem.BestMove, cacheItem.Depth, cacheItem.ScoreType);
                }
                return (null, Move.NullMove, null, null);
            }

            public void Clear() {
                Array.Clear(table, 0, table.Length);
                entries = 0;
            }

            public int Count() => entries;
        }

        public class OpeningBook
        {
            readonly Dictionary<string, BookMove[]> movesByPosition;
            readonly Random rng;

            public OpeningBook(string file) {
                rng = new Random();
                Span<string> entries = file.Trim(new char[] { ' ', '\n' }).Split("pos").AsSpan(1);
                movesByPosition = new Dictionary<string, BookMove[]>(entries.Length);

                for (int i = 0; i < entries.Length; i++) {
                    string[] entryData = entries[i].Trim('\n').Split('\n');
                    string positionFen = entryData[0].Trim();
                    Span<string> allMoveData = entryData.AsSpan(1);

                    BookMove[] bookMoves = new BookMove[allMoveData.Length];

                    for (int moveIndex = 0; moveIndex < bookMoves.Length; moveIndex++) {
                        string[] moveData = allMoveData[moveIndex].Split(' ');
                        bookMoves[moveIndex] = new BookMove(moveData[0], int.Parse(moveData[1]));
                    }

                    movesByPosition.Add(positionFen, bookMoves);
                }
            }

            public bool HasBookMove(string positionFen) {
                return movesByPosition.ContainsKey(RemoveMoveCountersFromFEN(positionFen));
            }

            // WeightPow is a value between 0 and 1.
            // 0 means all moves are picked with equal probablity, 1 means moves are weighted by num times played.
            public bool TryGetBookMove(Board board, out string moveString, double weightPow = 0.5) {
                string positionFen = board.GetFenString();
                weightPow = Math.Clamp(weightPow, 0, 1);
                if (movesByPosition.TryGetValue(RemoveMoveCountersFromFEN(positionFen), out var moves)) {
                    int totalPlayCount = 0;
                    foreach (BookMove move in moves) {
                        totalPlayCount += WeightedPlayCount(move.numTimesPlayed);
                    }

                    double[] weights = new double[moves.Length];
                    double weightSum = 0;
                    for (int i = 0; i < moves.Length; i++) {
                        double weight = WeightedPlayCount(moves[i].numTimesPlayed) / (double)totalPlayCount;
                        weightSum += weight;
                        weights[i] = weight;
                    }

                    double[] probCumul = new double[moves.Length];
                    for (int i = 0; i < weights.Length; i++) {
                        double prob = weights[i] / weightSum;
                        probCumul[i] = probCumul[Math.Max(0, i - 1)] + prob;
                        //string debugString = $"{moves[i].moveString}: {prob * 100:0.00}% (cumul = {probCumul[i]})";
                        //Console.WriteLine(debugString);
                    }


                    double random = rng.NextDouble();
                    for (int i = 0; i < moves.Length; i++) {

                        if (random <= probCumul[i]) {
                            moveString = moves[i].moveString;
                            return true;
                        }
                    }
                }

                moveString = "Null";
                return false;

                int WeightedPlayCount(int playCount) => (int)Math.Ceiling(Math.Pow(playCount, weightPow));
            }

            string RemoveMoveCountersFromFEN(string fen) {
                string fenA = fen[..fen.LastIndexOf(' ')];
                return fenA[..fenA.LastIndexOf(' ')];
            }


            public readonly struct BookMove
            {
                public readonly string moveString;
                public readonly int numTimesPlayed;

                public BookMove(string moveString, int numTimesPlayed) {
                    this.moveString = moveString;
                    this.numTimesPlayed = numTimesPlayed;
                }
            }
        }

        public Move Think(Board board, Timer timer) {
            this.isWhite = board.IsWhiteToMove;

            if (board.PlyCount == 0) {

                Move dMove = new Move("d2d4", board);
                Move eMove = new Move("e2e4", board);

                Random rand = new Random();

                Move selectedMove;

                if (rand.Next(2) == 0)  // Randomly generates 0 or 1
                {
                    selectedMove = dMove;
                }
                else {
                    selectedMove = eMove;
                }

                return selectedMove;
            }

            if (openingBook.TryGetBookMove(board, out string moveString, 0.4)) {
                //Console.WriteLine($"Book: {moveString}");
                return new Move(moveString, board);
            }

            if (board.PlyCount == 1) {
                // If the bot is playing black and the opponent played "d4" or "e4", mirror their move
                Move lastMove = board.GameMoveHistory[^1]; // Gets the last move
                Move nextMove;
                Random rand = new Random();

                if (lastMove.ToString() == "d2d4") {
                    return new Move("d7d5", board);
                }
                else if (lastMove.ToString() == "e2e4") {
                    if (rand.Next(3) == 0)  // Randomly generates 0 or 1
                    {
                        nextMove = new Move("e7e5", board);
                    }
                    else {
                        nextMove = new Move("c7c5", board);
                    }
                    return nextMove;
                }
            }


            Move bestMove = IterativeDeepening(board, timer);

            return bestMove;
        }
        private Move IterativeDeepening(Board board, Timer timer) {
            Move bestMove = Move.NullMove;
            Move bestMoveThisDepth = Move.NullMove;
            int totalPieces = CountPiecesOnBoard(board);

            bool isOpening = totalPieces > 29;
            bool isMidgame = totalPieces <= 29 && totalPieces > 15;
            bool isEndgame = totalPieces <= 15;
            bool isEndEndgame = totalPieces <= 5;

            int depthMaxTime = 100;

            if (isOpening) {
                MaxDepth = 10;
            }
            else if (isMidgame) {
                MaxDepth = 12;
            }
            else if (isEndgame) {
                MaxDepth = 30;
            }
            else if (isEndEndgame) {
                MaxDepth = 33;
            }
            //MaxDepth = 4;

            Stopwatch totalSW = new();
            totalSW.Start();

            Stopwatch depthSW = new();

            int depth = 1;
            int score = 0;
            bool foundMate = false;

            while (depth <= MaxDepth && !foundMate) {
                depthSW.Restart();

                try {
                    int alpha = int.MinValue;
                    int beta = int.MaxValue;
                    score = AlphaBetaSearch(board, depth, alpha, beta, board.IsWhiteToMove, ref bestMoveThisDepth, timer, ref depthSW, depthMaxTime);
                    // Only set the bestMove if a move was found at this depth
                    if (bestMoveThisDepth != Move.NullMove) {
                        bestMove = bestMoveThisDepth;
                    }
                }

                catch (Exception e) when (e.Message == "Time limit exceeded") {
                    if (bestMoveThisDepth != Move.NullMove) {
                        bestMove = bestMoveThisDepth;
                    }
                    break;
                }
                if (bestMoveThisDepth != Move.NullMove) {
                    bestMove = bestMoveThisDepth;
                }

                if (score == (this.isWhite ? int.MaxValue : int.MinValue)) {
                    if (bestMoveThisDepth != Move.NullMove) {
                        bestMove = bestMoveThisDepth;
                    }
                    foundMate = true;
                    break;
                }

                depth++;
            }

            if (bestMove == Move.NullMove) {
                Move[] moves = GetOrderedMoves(board);
                bestMove = moves[0];
                //Console.WriteLine("first move from list");
            }

            totalSW.Stop();

            depthSW.Reset();

            board.MakeMove(bestMove);
            //Console.WriteLine($"Ply: {board.PlyCount}, Depth: {depth - 1}, Best Move: {bestMove}, Score: {score}, Eval: {EvaluateBoard(board)}, " +
            //    $"Elapsed time: {Math.Round(totalSW.ElapsedMilliseconds / 1000f, 2)}, Piece count: {CountPiecesOnBoard(board)}, " +
            //    $"Trans count: {transpositionTable.Count()}");
            //Console.WriteLine(positionsSearched);
            //Console.WriteLine(lastSearchedPos);
            //Console.WriteLine(board.GetFenString());
            board.UndoMove(bestMove);

            //transpositionTable.Clear();

            positionsSearched = 0;

            return bestMove;
        }


        private int AlphaBetaSearch(Board board, int depth, int alpha, int beta, bool maximizingPlayer, ref Move bestMove, Timer timer, ref Stopwatch sw, int depthMaxTime = 6000, bool doNullMove = true) {
            positionsSearched++;
            // Time check
            if (sw.ElapsedMilliseconds > depthMaxTime && doNullMove) {
                throw new Exception("Time limit exceeded");
            }

            // Terminal node: checkmate or stalemate
            if (board.IsInCheckmate() || board.IsDraw()) {
                return EvaluateBoard(board);
            }
            if (depth == 0) {
                return EvaluateBoard(board);
            }

            // Null move pruning(makes blunders)
            //if (doNullMove && depth >= 4 && !board.IsInCheck()) {
            //    board.TrySkipTurn();
            //    int nullScore = -AlphaBetaSearch(board, depth - 2, -beta, -beta + 1, !maximizingPlayer, ref bestMove, timer, ref sw, depthMaxTime, false);
            //    board.UndoSkipTurn();
            //    if (nullScore >= beta) {
            //        return beta; // beta-cutoff
            //    }
            //}

            // Check if the position is in the transposition table
            var (transpositionTableScore, _, transpositionTableDepth, transpositionTableType) = transpositionTable.Get(board.ZobristKey);

            if (transpositionTableScore != null && transpositionTableDepth >= depth) {
                if (transpositionTableType == ScoreType.Exact)
                    return transpositionTableScore.Value;
                else if (transpositionTableType == ScoreType.Alpha)
                    alpha = Math.Max(alpha, transpositionTableScore.Value);
                else if (transpositionTableType == ScoreType.Beta)
                    beta = Math.Min(beta, transpositionTableScore.Value);

                if (alpha >= beta)
                    return transpositionTableScore.Value;  // Cutoff
            }

            Move[] moves = GetOrderedMoves(board);
            if (moves.Length == 0) {
                return EvaluateBoard(board);
            }

            //Move[] moves = board.GetLegalMoves();
            Move bestMoveForThisDepth = Move.NullMove;
            ScoreType scoreType = ScoreType.Alpha;

            // Order the killer moves first, then by moves from transposition table
            //moves = moves.OrderByDescending(move => killerMoves.Contains(move) ? 2 : (move == transpositionTableMove ? 1 : 0)).ToArray();


            for (int i = 0; i < moves.Length; i++) {
                Move move = moves[i];
                board.MakeMove(move);
                lastSearchedPos = board.GetFenString();

                int tempScore;

                try {
                    if (maximizingPlayer) {
                        tempScore = AlphaBetaSearch(board, depth - 1, alpha, beta, false, ref bestMoveForThisDepth, timer, ref sw, depthMaxTime);
                        if (tempScore > alpha) {
                            // Verify if this 'move' leads to a valid state before considering it as the best move
                            alpha = tempScore;  // Alpha acts like max in MiniMax
                            bestMove = move;
                            //scoreType = ScoreType.Exact;
                        }
                    }
                    else {
                        tempScore = AlphaBetaSearch(board, depth - 1, alpha, beta, true, ref bestMoveForThisDepth, timer, ref sw, depthMaxTime);
                        if (tempScore < beta) {
                            beta = tempScore;  // Beta acts like min in MiniMax
                            bestMove = move;
                            //scoreType = ScoreType.Exact;
                        }
                    }
                }
                finally {
                    board.UndoMove(move);
                }

                // If cutoff, then add the move to killerMoves and return the cutoff value
                if (maximizingPlayer && tempScore >= beta) {
                    if (killerMoves.Count >= MAX_KILLER_MOVES)
                        killerMoves.RemoveAt(0);
                    killerMoves.Add(move);
                    return beta;  // Beta cutoff
                }

                if (!maximizingPlayer && tempScore <= alpha) {
                    if (killerMoves.Count >= MAX_KILLER_MOVES)
                        killerMoves.RemoveAt(0);
                    killerMoves.Add(move);
                    return alpha;  // Alpha cutoff
                }
            }

            // No cutoff or exact value found, this is a "real" score
            if (scoreType != ScoreType.Exact) {
                scoreType = maximizingPlayer ? ScoreType.Alpha : ScoreType.Beta;
            }

            transpositionTable.Add(board.ZobristKey, maximizingPlayer ? alpha : beta, bestMove, depth, scoreType);

            return maximizingPlayer ? alpha : beta;
        }

        private int EvaluateBoard(Board board) {

            // Check for end of game conditions and return corresponding score.
            if (board.IsInCheckmate()) {
                return board.IsWhiteToMove ? -int.MaxValue : int.MaxValue;
            }
            if (board.IsDraw()) {
                return 0;
            }

            int score = 0;

            ulong whitePieces = board.WhitePiecesBitboard;
            ulong blackPieces = board.BlackPiecesBitboard;

            int totalPieces = CountPiecesOnBoard(board);

            bool isOpening = totalPieces > 25;
            bool isMidgame = totalPieces <= 25 && totalPieces > 15;
            bool isEndgame = totalPieces <= 15 && totalPieces > 8;
            bool isEndEndgame = totalPieces <= 8;


            //BitboardHelper.VisualizeBitboard(centerSquares);

            // Center control score can be calculated by counting the number of set bits in the intersection of pieces and center squares
            int whiteCenterControlScore = BitboardHelper.GetNumberOfSetBits(whitePieces & centerSquares);
            int blackCenterControlScore = BitboardHelper.GetNumberOfSetBits(blackPieces & centerSquares);


            // In the opening and midgame, add score for center control and subtract for king safety
            if (isOpening || isMidgame) {
                score += (whiteCenterControlScore - blackCenterControlScore) * 10;

                Square whiteKingSquare = board.GetKingSquare(true);
                Square blackKingSquare = board.GetKingSquare(false);
                if (whiteKingSquare.File >= 4 && whiteKingSquare.File <= 5) {
                    score -= 25;
                }
                if (blackKingSquare.File >= 4 && blackKingSquare.File <= 5) {
                    score += 25;
                }
            }

            score += CountMaterial(board, true) - CountMaterial(board, false);
            score += (int)Math.Round(EvaluatePieceSquareTables(board, true) - EvaluatePieceSquareTables(board, false) * 0.9);

            if (!board.IsWhiteToMove) {
                //Console.WriteLine("black eval");
                score = -score;
            }

            return score;
        }


        private int EvaluatePieceSquareTables(Board board, bool isWhite) {
            int value = 0;

            PieceType[] pieceTypes = { PieceType.Pawn, PieceType.Knight, PieceType.Bishop, PieceType.Rook, PieceType.Queen };

            for (int i = 0; i < pieceTypes.Length; i++) {
                int pieceTypeInt = (int)pieceTypes[i];
                int adjustment = (((pieceValues[pieceTypeInt] - 100) / (i == 1 || i == 2 ? 4 : 5)) + 100) / 100;
                value += EvaluatePieceSquareTable(board, pieceTypes[i], board.GetPieceList(pieceTypes[i], isWhite), isWhite) * adjustment;
            }

            return value;
        }

        private static int EvaluatePieceSquareTable(Board board, PieceType pieceType, PieceList pieceList, bool isWhite) {
            int value = 0;
            int pieceTypeInt = (int)pieceType;
            int pieceCount = CountPiecesOnBoard(board);
            bool isEndGame = IsEndgame(board);
            bool isEndEndGame = isEndGame && pieceCount <= 5;

            int[] kingTable = isEndGame ? KingMiddleGameTable : KingEndGameTable;
            if (isEndEndGame) {
                kingTable = KingEndEndGameTable.Select(x => (int)(x * 1.5)).ToArray();
            }

            for (int i = 0; i < pieceList.Count; i++) {
                Square square = pieceList[i].Square;
                int squareIndex = isWhite ? square.File + square.Rank * 8 : square.File + (7 - square.Rank) * 8;

                int[]? pieceSquareTable = pieceTypeInt switch {
                    (int)PieceType.Pawn => isEndGame ? PawnTable : PawnEndGameTable,
                    (int)PieceType.Knight => KnightTable,
                    (int)PieceType.Bishop => BishopTable,
                    (int)PieceType.Rook => RookTable,
                    (int)PieceType.Queen => QueenTable,
                    (int)PieceType.King => kingTable,
                    _ => null
                };

                if (pieceSquareTable != null) {
                    value += pieceSquareTable[squareIndex];
                }
            }

            return value;
        }
        private static int EvaluatePieceSquareTable(Board board, PieceType pieceType, Square square, bool isWhite) {
            int value = 0;
            int pieceTypeInt = (int)pieceType;
            int pieceCount = CountPiecesOnBoard(board);
            bool isEndGame = IsEndgame(board);
            bool isEndEndGame = isEndGame && pieceCount <= 5;

            int[] kingTable = isEndGame ? KingMiddleGameTable : KingEndGameTable;
            if (isEndEndGame) {
                kingTable = KingEndEndGameTable.Select(x => (int)(x * 1.5)).ToArray();
            }

            int squareIndex = isWhite ? square.File + square.Rank * 8 : square.File + (7 - square.Rank) * 8;

            int[]? pieceSquareTable = pieceTypeInt switch {
                (int)PieceType.Pawn => isEndGame ? PawnTable : PawnEndGameTable,
                (int)PieceType.Knight => KnightTable,
                (int)PieceType.Bishop => BishopTable,
                (int)PieceType.Rook => RookTable,
                (int)PieceType.Queen => QueenTable,
                (int)PieceType.King => kingTable,
                _ => null
            };

            if (pieceSquareTable != null) {
                value += pieceSquareTable[squareIndex];
            }

            return value;
        }



        private int CountMaterial(Board board, bool white) {
            int material = 0;

            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Pawn, white)) * pieceValues[1];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Knight, white)) * pieceValues[2];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Bishop, white)) * pieceValues[3];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Rook, white)) * pieceValues[4];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Queen, white)) * pieceValues[5];

            return material;
        }


        private Move[] GetOrderedMoves(Board board, bool onlyCaptures = false) {
            // Retrieve all legal moves
            Span<Move> moves = stackalloc Move[218];
            board.GetLegalMovesNonAlloc(ref moves, onlyCaptures);
            int moveCount = moves.Length;

            // Use a tuple to hold both move and score, enabling sort of both with Array.Sort()
            (Move, int)[] moveScores = new (Move, int)[moveCount];
            for (int i = 0; i < moveCount; i++) {
                moveScores[i] = (moves[i], EvaluateMoveHeuristic(moves[i], board));
            }

            // Sort moveScores array by score (in descending order) using built-in Array.Sort
            Array.Sort(moveScores, (x, y) => y.Item2.CompareTo(x.Item2));

            // Extract sorted moves into a new array
            Move[] sortedMoves = new Move[moveCount];
            for (int i = 0; i < moveCount; i++) {
                sortedMoves[i] = moveScores[i].Item1;
            }

            return sortedMoves;
        }

        private int EvaluateMoveHeuristic(Move move, Board board) {
            int score = 0;
            Piece movePiece = board.GetPiece(move.StartSquare);
            Piece capturePiece = board.GetPiece(move.TargetSquare);
            PieceType movePieceType = movePiece.PieceType;
            Square targetSquare = move.TargetSquare;
            Square startSquare = move.StartSquare;
            bool isWhite = movePiece.IsWhite;
            bool isEndGame = IsEndgame(board);

            // MakeMove() and UndoMove() only once.
            //board.MakeMove(move);
            //bool isCheckmate = board.IsInCheckmate();
            //bool isInCheck = board.IsInCheck();
            //board.UndoMove(move);

            if (move.IsPromotion) {
                score += 1400;
            }

            if (killerMoves.Contains(move)) {
                score += 2000;
            }

            if (move.IsCapture) {
                if (board.SquareIsAttackedByOpponent(targetSquare)) {
                    score -= pieceValues[(int)movePieceType];
                }
                else {
                    score += 1000 * ((int)capturePiece.PieceType - (int)movePieceType);
                }
            }

            if (!movePiece.IsKing && !movePiece.IsPawn) {
                score += EvaluatePieceSquareTable(board, movePieceType, targetSquare, isWhite)
                        - EvaluatePieceSquareTable(board, movePieceType, startSquare, isWhite);
            }

            // Encourage central control
            if (targetSquare.File >= 3 && targetSquare.File <= 4 && targetSquare.Rank >= 3 && targetSquare.Rank <= 4) {
                score += 100;
            }

            // Prioritize checks
            //if (isInCheck) {
            //    score += 300;
            //}

            // Prioritize centralization, particularly for knights and pawns
            if (movePiece.IsKnight || movePiece.IsPawn) {
                score += (int)((10 - Math.Max(Math.Abs(3.5 - targetSquare.File), Math.Abs(3.5 - targetSquare.Rank))) / 1.3);
            }

            // Prioritize pawn advances
            if (movePiece.IsPawn) {
                score += (isWhite ? targetSquare.Rank : 7 - targetSquare.Rank) * 2;
            }

            // Encourage moves that keep or place the king in safety.
            if (movePiece.IsKing && !isEndGame) {
                if (BitboardHelper.GetNumberOfSetBits(BitboardHelper.GetKingAttacks(targetSquare)) <
                    BitboardHelper.GetNumberOfSetBits(BitboardHelper.GetKingAttacks(startSquare))) {
                    score += 200;
                }
            }

            return score;
        }

        public static int CountPiecesOnBoard(Board board) => BitboardHelper.GetNumberOfSetBits(board.AllPiecesBitboard);

        private static bool IsEndgame(Board board) {
            ulong whiteQueens = board.GetPieceBitboard(PieceType.Queen, true);
            ulong blackQueens = board.GetPieceBitboard(PieceType.Queen, false);

            bool whiteHasQueen = whiteQueens != 0;
            bool blackHasQueen = blackQueens != 0;

            // Condition 1: Both sides have no queens
            if (!whiteHasQueen && !blackHasQueen) {
                return true;
            }

            // Condition 2: Every side which has a queen has additionally no other pieces or one minorpiece maximum.
            ulong whiteMinorPieces = board.GetPieceBitboard(PieceType.Knight, true) | board.GetPieceBitboard(PieceType.Bishop, true);
            ulong blackMinorPieces = board.GetPieceBitboard(PieceType.Knight, false) | board.GetPieceBitboard(PieceType.Bishop, false);

            bool whiteQueenCondition = whiteHasQueen && BitCount(whiteMinorPieces) <= 1 && BitCount(board.WhitePiecesBitboard & ~whiteQueens & ~whiteMinorPieces) == 0;
            bool blackQueenCondition = blackHasQueen && BitCount(blackMinorPieces) <= 1 && BitCount(board.BlackPiecesBitboard & ~blackQueens & ~blackMinorPieces) == 0;

            return whiteQueenCondition || blackQueenCondition;
        }

        private static int BitCount(ulong b) {
            int count = 0;
            while (b != 0) {
                b &= b - 1; // Remove the least significant bit set
                count++;
            }
            return count;
        }

    }
}