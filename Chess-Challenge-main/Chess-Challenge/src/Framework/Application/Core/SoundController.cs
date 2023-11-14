using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Raylib_cs;
using System.Media;
using NAudio;
using NAudio.Wave;
using System.IO;
using Chess_Challenge.Application;

namespace ChessChallenge.Application
{
    static class SoundController
    {
        private static CachedSound capture;
        private static CachedSound move;

        private static string capturePath = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, @"resources\Sound Effects\Capture.mp3");
        private static string movePath = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, @"resources\Sound Effects\Move.mp3");

        public static void Initialize() {
            // Initialize players
            capture = new CachedSound(capturePath);
            move = new CachedSound(movePath);
        }

        public static void PlayCaptureSFX() {
            //Console.WriteLine("capture sfx played");
            AudioPlaybackEngine.Instance.PlaySound(capture);
        }

        public static void PlayMoveSFX() {
            //Console.WriteLine("move sfx played");
            AudioPlaybackEngine.Instance.PlaySound(move);
        }

        public static void Dispose() {
            // Dispose of all resources
            AudioPlaybackEngine.Instance.Dispose();
        }
    }
}
