using System;
using System.Collections;
using System.Text;
using System.IO;

namespace @FileInput {
    public partial class @Reader
    {
        public static char[] getContent() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {

                return System.IO.File.ReadAllText(argList[1], Encoding.UTF8).ToCharArray();
              } else {
                return "".ToCharArray();
              }
            }

            return "".ToCharArray();
        }

        public static long getTimestamp() {
          return DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
        }
    }
}
