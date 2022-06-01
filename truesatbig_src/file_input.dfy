module {:extern "FileInput"} FileInput {
    class {:extern "Reader"} Reader {
        static function method {:extern "getContent"} getContent() : array<char>
        static function method {:extern "getTimestamp"} getTimestamp() : int 
    }
}
