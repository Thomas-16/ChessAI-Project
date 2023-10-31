using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using static System.Math;

namespace ChessChallenge.Example
{
    // A simple bot that can spot mate in one, and always captures the most valuable piece it can.
    // Plays randomly otherwise.
    public class EvilBot : IChessBot
    {
        const bool useTimer = Application.Settings.GameDurationMilliseconds != int.MaxValue;
        const int maxTimePerMove = 100;
        const bool printDebug = false;
        const bool bookMoves = false;
        static int[] pieceValues = { 0, 100, 320, 330, 500, 900, 20000 };
        const ulong whiteTerritoryMask = 0x00000000FFFFFFFF; // The bottom 4 ranks (1-4)
        const ulong blackTerritoryMask = 0xFFFFFFFF00000000; // The top 4 ranks (5-8)
        const ulong notAFile = 0xFEFEFEFEFEFEFEFE;
        const ulong notHFile = 0x7F7F7F7F7F7F7F7F;

        Entry[] _transpositions = new Entry[16777216];
        static int transCount;
        float _budgetCounter = 121, budget;
        bool searchCancelled;
        Timer timer;
        Board board;
        HashSet<Move> _killerMoves = new();

        private static readonly string path = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "resources", "Book.txt");
        private OpeningBook openingBook = new(File.ReadAllText(path));

        // Square values can be calculated by bit shifting
        ulong centerSquares = ((ulong)1 << new Square("e4").Index)
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
        // Masks for each file on the chessboard
        static ulong[] files = {
        0x0101010101010101, // File A
        0x0202020202020202, // File B
        0x0404040404040404, // File C
        0x0808080808080808, // File D
        0x1010101010101010, // File E
        0x2020202020202020, // File F
        0x4040404040404040, // File G
        0x8080808080808080  // File H
    };
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
                        string debugString = $"{moves[i].moveString}: {prob * 100:0.00}% (cumul = {probCumul[i]})";
                        // Console.WriteLine(debugString);
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
        public static string GetTranspositionPercentage() {
            return $"{Math.Round(transCount / 16777216.0 * 100.0, 2)}%";
        }
        public void ResetTrans() {
            transCount = 0;
            //_transpositions = new Entry[16777216];
        }
        float OneMinusEndgameT(Board board, bool white) {
            int endgameWeightSum = 0;
            foreach (var pl in board.GetAllPieceLists())
                if (pl.IsWhitePieceList == white)
                    endgameWeightSum += (0x942200 >> 4 * (int)pl.TypeOfPieceInList & 0xf) * pl.Count;

            return Min(1, endgameWeightSum * 0.04f);
        }
        int EvaluateBoard() {
            float score = 0f;

            float ownOneMinusEndgameT = OneMinusEndgameT(board, false), otherOneMinusEndgameT = OneMinusEndgameT(board, true);
            foreach (var pl in board.GetAllPieceLists())
                score += 0b1000010 >> (int)pl.TypeOfPieceInList != 0
                    ? (pl.IsWhitePieceList ? ownOneMinusEndgameT : -otherOneMinusEndgameT) * EvaluatePieceSquareTable(Starts, pl)
                      + (pl.IsWhitePieceList ? 1.0f - ownOneMinusEndgameT : otherOneMinusEndgameT - 1.0f) * EvaluatePieceSquareTable(Ends, pl)
                    : EvaluatePieceSquareTable(Starts, pl);


            ulong whitePieces = board.WhitePiecesBitboard;
            ulong blackPieces = board.BlackPiecesBitboard;

            int totalPieces = CountPiecesOnBoard(board);

            bool isOpening = totalPieces > 25;
            bool isMidgame = totalPieces <= 25 && totalPieces > 15;
            bool isEndEndgame = totalPieces < 15;


            // Center control score can be calculated by counting the number of set bits in the intersection of pieces and center squares
            int whiteCenterControlScore = BitboardHelper.GetNumberOfSetBits(whitePieces & centerSquares);
            int blackCenterControlScore = BitboardHelper.GetNumberOfSetBits(blackPieces & centerSquares);


            // In the opening and midgame, add score for center control and subtract for king safety
            if (isOpening || isMidgame) {
                float openingScalingFactor = Clamp(totalPieces / 20f, 0f, 1f);

                score += (whiteCenterControlScore - blackCenterControlScore) * 25f * openingScalingFactor;

                Square whiteKingSquare = board.GetKingSquare(true);
                Square blackKingSquare = board.GetKingSquare(false);
                if (whiteKingSquare.File >= 4 && whiteKingSquare.File <= 5) {
                    score -= 25f * openingScalingFactor;
                }
                if (blackKingSquare.File >= 4 && blackKingSquare.File <= 5) {
                    score += 25f * openingScalingFactor;
                }
            }

            // Pawn Structure
            ulong whitePawns = board.GetPieceBitboard(PieceType.Pawn, true);
            ulong blackPawns = board.GetPieceBitboard(PieceType.Pawn, false);

            // Doubled Pawns
            int whiteDoubledPawns = CountDoubledPawns(whitePawns);
            int blackDoubledPawns = CountDoubledPawns(blackPawns);
            score -= (whiteDoubledPawns - blackDoubledPawns) * 40;

            // Isolated Pawns
            int whiteIsolatedPawns = CountIsolatedPawns(whitePawns);
            int blackIsolatedPawns = CountIsolatedPawns(blackPawns);
            score -= (whiteIsolatedPawns - blackIsolatedPawns) * 35;

            // Passed Pawns
            int whitePassedPawns = CountPassedPawns(whitePawns, blackPawns, true);
            int blackPassedPawns = CountPassedPawns(blackPawns, whitePawns, false);
            score += (whitePassedPawns - blackPassedPawns) * 35;

            // Rooks on Open Files
            ulong allPawns = whitePawns | blackPawns;
            int whiteRooksOnOpenFiles = CountRooksOnOpenFiles(board.GetPieceBitboard(PieceType.Rook, true), allPawns);
            int blackRooksOnOpenFiles = CountRooksOnOpenFiles(board.GetPieceBitboard(PieceType.Rook, false), allPawns);
            score += (whiteRooksOnOpenFiles - blackRooksOnOpenFiles) * 35;

            // Bishop Pair
            bool whiteHasBishopPair = BitCount(board.GetPieceBitboard(PieceType.Bishop, true)) >= 2;
            bool blackHasBishopPair = BitCount(board.GetPieceBitboard(PieceType.Bishop, false)) >= 2;
            score += (whiteHasBishopPair ? 20 : 0) - (blackHasBishopPair ? 20 : 0);

            // Space (How to win at Chess P.112) and King Safety
            //float spaceFactor = CalculateMultiplier(totalPieces, 13, 24);

            //ulong whitePiecesViewInEnemyTerritory = 0;
            //ulong blackPiecesViewInEnemyTerritory = 0;

            //ulong blackMask = BlendBitboards(blackTerritoryMask, GetKingSurroundingSquares(false), spaceFactor);
            //ulong whiteMask = BlendBitboards(whiteTerritoryMask, GetKingSurroundingSquares(true), spaceFactor);

            //foreach (PieceType pieceType in Enum.GetValues(typeof(PieceType))) {
            //    if (pieceType == PieceType.None) continue;

            //    while (whitePieces != 0) {
            //        Square square = new Square(BitboardHelper.ClearAndGetIndexOfLSB(ref whitePieces));
            //        ulong attacks = BitboardHelper.GetPieceAttacks(pieceType, square, board, true);
            //        whitePiecesViewInEnemyTerritory |= attacks & blackMask;
            //    }

            //    while (blackPieces != 0) {
            //        Square square = new Square(BitboardHelper.ClearAndGetIndexOfLSB(ref blackPieces));
            //        ulong attacks = BitboardHelper.GetPieceAttacks(pieceType, square, board, false);
            //        blackPiecesViewInEnemyTerritory |= attacks & whiteMask;
            //    }
            //}

            //score += (BitboardHelper.GetNumberOfSetBits(whitePiecesViewInEnemyTerritory) - BitboardHelper.GetNumberOfSetBits(blackPiecesViewInEnemyTerritory)) * 14f;


            // Mop-up Evaluation
            if (isEndEndgame) {
                Square opponentKingSquare = board.IsWhiteToMove ? board.GetKingSquare(false) : board.GetKingSquare(true);
                int distanceToEdge = Min(opponentKingSquare.File, 7 - opponentKingSquare.File);
                distanceToEdge = Min(distanceToEdge, opponentKingSquare.Rank);
                distanceToEdge = Min(distanceToEdge, 7 - opponentKingSquare.Rank);

                float mopUpBonus = (3 - distanceToEdge) * 33f;

                // Scale the bonus based on how close you are to the endgame
                float endgameScalingFactor = 1.0f - Clamp(totalPieces / 15f, 0f, 1f);
                mopUpBonus = MathF.Round(mopUpBonus * endgameScalingFactor);

                //score += board.IsWhiteToMove ? mopUpBonus : -mopUpBonus;
                score += mopUpBonus;
            }


            return (int)Round(board.IsWhiteToMove ? score : -score);
        }

        #region Evaluation Helpers
        ulong GetKingSurroundingSquares(bool isWhite) {
            // Masks for A and H files
            ulong notAFile = 0xFEFEFEFEFEFEFEFE;
            ulong notHFile = 0x7F7F7F7F7F7F7F7F;

            // Get the king's square
            Square kingSquare = board.GetKingSquare(isWhite);

            // Convert the king's square to a bitboard using the Index property
            ulong kingBitboard = 1UL << kingSquare.Index;

            // Calculate the surrounding squares
            ulong surroundingSquares = kingBitboard
                | (kingBitboard << 8) | (kingBitboard >> 8) // squares above and below the king
                | ((kingBitboard & notHFile) << 1) // squares to the right of the king
                | ((kingBitboard & notHFile) << 9) // square above and to the right of the king
                | ((kingBitboard & notHFile) >> 7) // square below and to the right of the king
                | ((kingBitboard & notAFile) >> 1) // squares to the left of the king
                | ((kingBitboard & notAFile) >> 9) // square above and to the left of the king
                | ((kingBitboard & notAFile) << 7); // square below and to the left of the king

            return surroundingSquares;
        }

        ulong BlendBitboards(ulong bb1, ulong bb2, float weight) {
            if (weight < 0f) return bb1;
            if (weight > 1f) return bb2;

            int bitsFromBB1 = (int)(weight * 64); // 64 bits in a ulong
            ulong result = 0;

            for (int i = 0; i < 32; i++) {
                // Check the higher bit (from the outside)
                if ((bb1 & (1UL << (63 - i))) != 0 && bitsFromBB1 > 0) {
                    result |= (1UL << (63 - i));
                    bitsFromBB1--;
                }
                else if ((bb2 & (1UL << (63 - i))) != 0) {
                    result |= (1UL << (63 - i));
                }

                // Check the lower bit (from the outside)
                if ((bb1 & (1UL << i)) != 0 && bitsFromBB1 > 0) {
                    result |= (1UL << i);
                    bitsFromBB1--;
                }
                else if ((bb2 & (1UL << i)) != 0) {
                    result |= 1UL << i;
                }
            }

            return result;
        }
        // Calculate the scaling factor based on the number of total pieces
        float CalculateMultiplier(int totalPieces, int min, int max) {
            // Clamp the total pieces to the defined range
            totalPieces = Math.Max(min, Math.Min(max, totalPieces));

            // Calculate the interpolation factor (t) based on the number of total pieces
            float t = (float)(totalPieces - min) / (max - min);

            // Use the lerp function to calculate the scaling factor
            return Lerp(0f, 1f, t);
        }

        ulong EvaluatePieceSquareTable(ulong[][] table, PieceList pl) {
            ulong value = 0;
            foreach (var p in pl) {
                var sq = p.Square;
                value += table[(int)p.PieceType][sq.File >= 4 ? 7 - sq.File : sq.File] << 8 * (pl.IsWhitePieceList ? 7 - sq.Rank : sq.Rank) >> 56;
            }
            return 25 * value;
        }
        int CountMaterial(Board board, bool white) {
            int material = 0;

            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Pawn, white)) * pieceValues[1];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Knight, white)) * pieceValues[2];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Bishop, white)) * pieceValues[3];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Rook, white)) * pieceValues[4];
            material += BitboardHelper.GetNumberOfSetBits(board.GetPieceBitboard(PieceType.Queen, white)) * pieceValues[5];

            return material;
        }

        static int CountDoubledPawns(ulong bitboard) {
            int doubledCount = 0;

            foreach (ulong file in files) {
                // Count the number of pawns on this file
                int pawnsOnFile = BitCount(bitboard & file);

                // If there's more than one pawn on this file, increment the doubled count
                if (pawnsOnFile > 1) {
                    doubledCount += pawnsOnFile - 1; // Add (pawnsOnFile - 1) to the count for each additional pawn on the same file
                }
            }

            return doubledCount;
        }
        static int CountIsolatedPawns(ulong bitboard) {
            int isolatedCount = 0;

            for (int i = 0; i < 8; i++) {
                ulong currentFile = files[i];
                ulong pawnsOnCurrentFile = bitboard & currentFile;

                if (pawnsOnCurrentFile == 0)
                    continue; // No pawns on this file, skip to the next file

                ulong adjacentPawns = 0;

                // Check left adjacent file if not on file A
                if (i > 0)
                    adjacentPawns |= bitboard & files[i - 1];

                // Check right adjacent file if not on file H
                if (i < 7)
                    adjacentPawns |= bitboard & files[i + 1];

                // If no pawns on adjacent files, then all pawns on the current file are isolated
                if (adjacentPawns == 0)
                    isolatedCount += BitCount(pawnsOnCurrentFile);
            }

            return isolatedCount;
        }
        public static int CountPassedPawns(ulong ownPawns, ulong opponentPawns, bool isWhite) {
            int passedCount = 0;

            while (ownPawns != 0) {
                // Get the least significant bit's position
                ulong lsb = ownPawns & (~ownPawns + 1);

                // If it's a white pawn, check the squares above it
                if (isWhite) {
                    ulong pathToPromotion = NorthFill(lsb);
                    ulong adjacentFiles = WestOne(lsb) | EastOne(lsb);
                    ulong blockingRegion = pathToPromotion | (NorthOne(pathToPromotion) & adjacentFiles);

                    if ((blockingRegion & opponentPawns) == 0)
                        passedCount++;
                }
                else // If it's a black pawn, check the squares below it
                {
                    ulong pathToPromotion = SouthFill(lsb);
                    ulong adjacentFiles = WestOne(lsb) | EastOne(lsb);
                    ulong blockingRegion = pathToPromotion | (SouthOne(pathToPromotion) & adjacentFiles);

                    if ((blockingRegion & opponentPawns) == 0)
                        passedCount++;
                }

                // Clear the least significant bit
                ownPawns &= ownPawns - 1;
            }

            return passedCount;
        }
        static int CountRooksOnOpenFiles(ulong rooks, ulong allPawns) {
            int openFileRooks = 0;

            while (rooks != 0) {
                // Get the least significant bit's position (the position of one of the rooks)
                ulong lsb = rooks & (~rooks + 1);

                // Create a mask for the file this rook is on
                ulong fileMask = NorthFill(lsb) | SouthFill(lsb);

                // Check if there are no pawns on this file
                if ((fileMask & allPawns) == 0)
                    openFileRooks++;

                // Clear the least significant bit (move to the next rook)
                rooks ^= lsb;
            }

            return openFileRooks;
        }

        #endregion

        #region Helper methods for bitboard manipulation
        private static ulong NorthOne(ulong bb) => bb << 8;
        private static ulong SouthOne(ulong bb) => bb >> 8;
        private static ulong EastOne(ulong bb) => (bb & 0xFEFEFEFEFEFEFEFE) << 1;
        private static ulong WestOne(ulong bb) => (bb & 0x7F7F7F7F7F7F7F7F) >> 1;

        private static ulong NorthFill(ulong bb) {
            bb |= bb << 8;
            bb |= bb << 16;
            bb |= bb << 32;
            return bb;
        }

        private static ulong SouthFill(ulong bb) {
            bb |= bb >> 8;
            bb |= bb >> 16;
            bb |= bb >> 32;
            return bb;
        }
        #endregion

        (int, Move, bool) Search(int depthLeft, int checkExtensionsLeft, bool isCaptureOnly, int alpha = -32200, int beta = 32200) {
            if (board.IsInCheckmate())
                return (-32100, default, true);

            if (board.IsDraw() || board.PlyCount == ChessChallenge.Application.ChallengeController.MAX_PLY_COUNT)
                return (0, default, board.IsInStalemate() || board.IsInsufficientMaterial() || board.PlyCount == ChessChallenge.Application.ChallengeController.MAX_PLY_COUNT);

            if (depthLeft == 0) {
                ++depthLeft;
                if (board.IsInCheck() && checkExtensionsLeft > 0)
                    --checkExtensionsLeft;
                else if (!isCaptureOnly && checkExtensionsLeft == 4)
                    return Search(8, checkExtensionsLeft, true, alpha, beta);
                else
                    return (EvaluateBoard(), default, true);
            }

            ulong key = board.ZobristKey;
            Entry trans = _transpositions[key % 16777216];
            int bestScore = -32150, score;
            Move best = default;
            if (trans.Key == key && Abs(trans.Depth) >= depthLeft) {
                board.MakeMove(trans.Move);
                bool toDraw = board.IsDraw();
                board.UndoMove(trans.Move);

                if (toDraw)
                    trans = default;
                else {
                    alpha = Max(alpha, bestScore = trans.Score);
                    best = trans.Move;
                    if (beta < alpha || trans.Depth >= 0)
                        return (trans.Score, trans.Move, true);
                }
            }

            if (isCaptureOnly && (score = EvaluateBoard()) > bestScore && beta < (alpha = Max(alpha, bestScore = score)))
                return (score, default, true);

            Span<Move> legals = stackalloc Move[218];
            board.GetLegalMovesNonAlloc(ref legals, isCaptureOnly);

            Span<(float, Move)> prioritizedMoves = stackalloc (float, Move)[legals.Length];

            // Move Ordering
            OrderMoves(board, ref legals, ref prioritizedMoves, trans);

            bool canUseTranspositions = true, approximate = false, canUse;
            int loopvar = 0;
            foreach (var (_, move) in prioritizedMoves) {
                if (!searchCancelled)
                    searchCancelled = timer.MillisecondsElapsedThisTurn >= budget;

                if (searchCancelled)
                    return (bestScore, best, canUseTranspositions);

                board.MakeMove(move);
                try {
                    if (depthLeft >= 3 && ++loopvar >= 4 && !move.IsCapture) {
                        score = -Search(depthLeft - 2, checkExtensionsLeft, isCaptureOnly, -beta, -alpha).Item1;

                        if (searchCancelled)
                            break;

                        if (score < bestScore)
                            continue;
                    }
                    (score, _, canUse) = Search(depthLeft - 1, checkExtensionsLeft, isCaptureOnly, -beta, -alpha);

                    if (searchCancelled)
                        break;

                    score = -score + (Abs(score) >= 30000 ? Sign(score) : 0);

                    if (score <= bestScore)
                        continue;

                    bestScore = score;
                    best = move;
                    alpha = Max(alpha, score);
                    canUseTranspositions = canUse;


                    if (approximate = beta < alpha) {
                        _killerMoves.Add(move);
                        break;
                    }
                }
                finally {
                    board.UndoMove(move);
                }
            }

            if (!searchCancelled && !isCaptureOnly && canUseTranspositions && bestScore != 0) {
                _transpositions[key % 16777216] = new Entry { Key = key, Depth = (short)(approximate ? -depthLeft : depthLeft), Score = (short)bestScore, Move = best };
                transCount++;
            }

            return (bestScore, best, canUseTranspositions);
        }
        void OrderMoves(Board board, ref Span<Move> legals, ref Span<(float, Move)> prioritizedMoves, Entry trans) {
            int loopvar = 0;

            int totalPieces = CountPiecesOnBoard(board);

            bool isOpening = totalPieces > 25;
            bool isMidgame = totalPieces <= 25 && totalPieces > 15;
            bool isEndEndgame = totalPieces < 15;
            bool isEndGame = IsEndgame(board);

            foreach (var lmove in legals) {
                Piece movePiece = board.GetPiece(lmove.StartSquare);
                Piece capturePiece = board.GetPiece(lmove.TargetSquare);
                PieceType movePieceType = movePiece.PieceType;
                Square targetSquare = lmove.TargetSquare;
                Square startSquare = lmove.StartSquare;
                bool isWhite = movePiece.IsWhite;

                float moveScore = 0f;

                // Transposition table move
                if (trans.Key == board.ZobristKey && lmove == trans.Move) {
                    moveScore += 5000;
                }
                // Killer moves
                else if (_killerMoves.Contains(lmove)) {
                    moveScore += 500;
                }

                // Encourage central control
                if (isOpening || isMidgame) {
                    if (targetSquare.File >= 3 && targetSquare.File <= 4 && targetSquare.Rank >= 3 && targetSquare.Rank <= 4) {
                        moveScore += .75f;
                    }
                }

                // Prioritize pawn advances
                // Define some constants for the opening and endgame
                const float OPENING_PIECES = 25f;

                // Calculate endgameT
                float endgameT = 0;
                if (totalPieces < OPENING_PIECES) {
                    endgameT = (float)(OPENING_PIECES - totalPieces) / (OPENING_PIECES - 2);
                }

                // Prioritize pawn advances with endgameT scaling
                if (movePiece.IsPawn && !isOpening) {
                    moveScore += (isWhite ? targetSquare.Rank : 7 - targetSquare.Rank) * .35f * endgameT;
                }

                // Encourage moves that keep or place the king in safety.
                if (movePiece.IsKing && !isEndGame) {
                    if (BitCount(BitboardHelper.GetKingAttacks(targetSquare)) <
                        BitCount(BitboardHelper.GetKingAttacks(startSquare))) {
                        moveScore += .5f;
                    }
                }

                //Castling
                if ((isOpening || isMidgame) && lmove.IsCastles) {
                    moveScore += 1f;
                }

                //Promotion
                if (lmove.IsPromotion) {
                    moveScore += 5;
                }

                // Add the score from the capture piece type
                moveScore += 0x0953310 >> 4 * (int)lmove.CapturePieceType & 0xf;

                prioritizedMoves[loopvar++] = (moveScore, lmove);
            }

            prioritizedMoves.Sort((a, b) => -a.Item1.CompareTo(b.Item1));
        }

        public Move Think(Board b, Timer t) {
            board = b;
            timer = t;

            // Book moves
            if (bookMoves) {
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

                if (board.PlyCount == 1) {
                    // If the bot is playing black and the opponent played "d4" or "e4", mirror their move
                    Move lastMove = board.GameMoveHistory[^1]; // Gets the last move
                    Move nextMove;
                    Random rand = new Random();

                    if (lastMove.ToString() == "d2d4") {
                        return new Move("d7d5", board);
                    }
                    else if (lastMove.ToString() == "e2e4") {
                        if (rand.Next(4) == 0)  // Randomly generates 0 or 1
                        {
                            nextMove = new Move("e7e5", board);
                        }
                        else {
                            nextMove = new Move("c7c5", board);
                        }
                        return nextMove;
                    }
                }
                if (openingBook.TryGetBookMove(board, out string moveString, 0.3)) {
                    if (printDebug)
                        Console.WriteLine($"Book: {moveString}");
                    return new Move(moveString, board);
                }
            }

            Stopwatch totalSW = new();
            totalSW.Start();

            budget = useTimer ? Min(0.0333333333333333333f, 2.0f / --_budgetCounter) * t.MillisecondsRemaining : maxTimePerMove;
            searchCancelled = false;

            _killerMoves.Clear();
            Move bestMove = default, move;
            int totalPieces = CountPiecesOnBoard(board);

            bool isOpening = totalPieces > 29;
            bool isMidgame = totalPieces <= 29 && totalPieces > 15;
            bool isEndgame = totalPieces <= 15;
            bool isEndEndgame = totalPieces <= 5;

            int maxDepth = 0;
            int depth = 0;

            if (isOpening) {
                maxDepth = 14;
            }
            else if (isMidgame) {
                maxDepth = 16;
            }
            else if (isEndgame) {
                maxDepth = 30;
            }
            else if (isEndEndgame) {
                maxDepth = 33;
            }
            while (++depth <= maxDepth && !searchCancelled)
                if ((move = Search(depth, 4, false).Item2) != default)
                    bestMove = move;

            if (bestMove == default) {
                Console.WriteLine("First in list");
                //Span<Move> legal = stackalloc Move[218];
                //GetOrderedMoves(ref legal, board);
                bestMove = board.GetLegalMoves()[0];
            }

            board.MakeMove(bestMove);
            if (printDebug) {
                Console.WriteLine($"Ply: {board.PlyCount}, Depth: {depth - 1}, Best Move: {bestMove}" +
                    $", Elapsed time: {Math.Round((double)totalSW.ElapsedMilliseconds, 2)}");
            }
            board.UndoMove(bestMove);

            totalSW.Stop();

            return bestMove;
        }
        #region Unused
        Move[] GetOrderedMoves(ref Span<Move> moves, Board board, Entry trans, bool onlyCaptures = false) {
            // Retrieve all legal moves
            board.GetLegalMovesNonAlloc(ref moves, onlyCaptures);
            int moveCount = moves.Length;

            // Use a tuple to hold both move and score, enabling sort of both with Array.Sort()
            (Move, int)[] moveScores = new (Move, int)[moveCount];
            for (int i = 0; i < moveCount; i++) {
                moveScores[i] = (moves[i], EvaluateMoveHeuristic(moves[i], board, trans));
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

        private int EvaluateMoveHeuristic(Move move, Board board, Entry trans) {
            int score = 0;
            Piece movePiece = board.GetPiece(move.StartSquare);
            Piece capturePiece = board.GetPiece(move.TargetSquare);
            PieceType movePieceType = movePiece.PieceType;
            Square targetSquare = move.TargetSquare;
            Square startSquare = move.StartSquare;
            bool isWhite = movePiece.IsWhite;
            bool isEndGame = IsEndgame(board);

            if (move.IsPromotion) {
                score += 1000;
            }

            if (trans.Key == board.ZobristKey) {
                score += 5000;
            }
            else if (_killerMoves.Contains(move)) {
                score += 1000;
            }

            if (move.PromotionPieceType == PieceType.Queen) {
                score += 500;
            }

            if (move.IsCapture) {
                int whiteMaterial = CountMaterial(board, true) / 100;
                int blackMaterial = CountMaterial(board, false) / 100;
                int materialDifference = whiteMaterial - blackMaterial;

                // Encourage equal captures when up in material
                if (materialDifference > 0 && movePieceType == capturePiece.PieceType) {
                    score += 300;
                }
                else if (materialDifference < 0 && movePieceType == capturePiece.PieceType) {
                    score -= 500;
                }

                if (board.SquareIsAttackedByOpponent(targetSquare) && (int)capturePiece.PieceType < (int)movePieceType) {
                    score -= pieceValues[(int)movePieceType];
                }
                else {
                    score += 2 * ((int)capturePiece.PieceType - (int)movePieceType);
                }
            }

            // Encourage central control
            if (targetSquare.File >= 3 && targetSquare.File <= 4 && targetSquare.Rank >= 3 && targetSquare.Rank <= 4) {
                score += 125;
            }

            // Prioritize pawn advances
            if (movePiece.IsPawn) {
                score += (isWhite ? targetSquare.Rank : 7 - targetSquare.Rank) * 20;
            }

            // Encourage moves that keep or place the king in safety.
            if (movePiece.IsKing && !isEndGame) {
                if (BitCount(BitboardHelper.GetKingAttacks(targetSquare)) <
                    BitCount(BitboardHelper.GetKingAttacks(startSquare))) {
                    score += 200;
                }
            }

            return score;
        }
        #endregion
        static bool IsEndgame(Board board) {
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
        static int BitCount(ulong b) {
            int count = 0;
            while (b != 0) {
                b &= b - 1; // Remove the least significant bit set
                count++;
            }
            return count;
        }
        static int CountPiecesOnBoard(Board board) => BitboardHelper.GetNumberOfSetBits(board.AllPiecesBitboard);

        static float Lerp(float a, float b, float t) {
            return a + t * (b - a);
        }


        static readonly ulong[] Knights = { 0x3234363636363432ul, 0x34383c3d3c3d3834ul, 0x363c3e3f3f3e3c36ul, 0x363c3f40403f3d36ul },
                                       Bishops = { 0x3c3e3e3e3e3e3e3cul, 0x3e4040414042413eul, 0x3e4041414242403eul, 0x3e4042424242403eul },
                                       Rooks = { 0x6465636363636364ul, 0x6466646464646464ul, 0x6466646464646464ul, 0x6466646464646465ul },
                                       Queens = { 0xb0b2b2b3b4b2b2b0ul, 0xb2b4b4b4b4b5b4b2ul, 0xb2b4b5b5b5b5b5b2ul, 0xb3b4b5b5b5b5b4b3ul };
        ulong[][] Starts = { null, new[] { 0x141e161514151514ul, 0x141e161514131614ul, 0x141e181614121614ul, 0x141e1a1918141014ul }, Knights, Bishops, Rooks,
                               Queens, new[] { 0x0004080a0c0e1414ul, 0x020406080a0c1416ul, 0x020406080a0c0f12ul, 0x02040406080c0f10ul } },
                         Ends = { null, new[] { 0x14241e1a18161614ul, 0x14241e1a18161614ul, 0x14241e1a18161614ul, 0x14241e1a18161614ul }, Knights, Bishops, Rooks,
                               Queens, new[] { 0x0c0f0e0d0c0b0a06ul, 0x0e100f0e0d0c0b0aul, 0x0e1114171614100aul, 0x0e1116191815100aul } };

        struct Entry
        {
            public ulong Key;
            public short Score, Depth;
            public Move Move;
        }

    }
}