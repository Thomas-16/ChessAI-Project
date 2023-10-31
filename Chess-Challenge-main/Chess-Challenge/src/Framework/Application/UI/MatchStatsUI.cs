﻿using Raylib_cs;
using System.Numerics;
using System;

namespace ChessChallenge.Application
{
    public static class MatchStatsUI
    {
        public static void DrawMatchStats(ChallengeController controller)
        {
            int nameFontSize = UIHelper.ScaleInt(40);
            int regularFontSize = UIHelper.ScaleInt(35);
            int headerFontSize = UIHelper.ScaleInt(45);
            Color col = new(180, 180, 180, 255);
            Vector2 startPos = UIHelper.Scale(new Vector2(1500, 250));
            float spacingY = UIHelper.Scale(35);

            if(controller.PlayerWhite.Bot is not MyBot || controller.PlayerBlack.Bot is not MyBot) {
                DrawNextText($"TT {MyBot.GetTranspositionPercentage()} full", headerFontSize, Color.WHITE);
                startPos.Y += spacingY * 2;
            }

            if (controller.PlayerWhite.IsBot && controller.PlayerBlack.IsBot)
            {
                DrawNextText($"Game {controller.CurrGameNumber} of {controller.TotalGameCount}", headerFontSize, Color.WHITE);
                startPos.Y += spacingY * 2;

                DrawStats(controller.BotStatsA);
                startPos.Y += spacingY * 2;
                DrawStats(controller.BotStatsB);

            }

            void DrawStats(ChallengeController.BotMatchStats stats) {
                DrawNextText(stats.BotName + ":", nameFontSize, Color.WHITE);
                DrawNextText($"Score: +{stats.NumWins} ={stats.NumDraws} -{stats.NumLosses}", regularFontSize, col);
                DrawNextText($"Num Timeouts: {stats.NumTimeouts}", regularFontSize, col);
                DrawNextText($"Num Illegal Moves: {stats.NumIllegalMoves}", regularFontSize, col);
            }

            void DrawNextText(string text, int fontSize, Color col) {
                UIHelper.DrawText(text, startPos, fontSize, 1, col);
                startPos.Y += spacingY;
            }
        }
    }
}