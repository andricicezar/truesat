include "int32.dfy"
include "parser.dfy"
include "file_input.dfy"
include "my_datatypes.dfy"
include "input_predicate.dfy"

module Input {
    import Int32
    import opened Useless
    import FileInput
    import opened MyDatatypes
    import InputPredicate

    method getInput() returns (result : Maybe<(Int32.t, seq<seq<Int32.t>>)>)
      ensures result.Just? ==>
        InputPredicate.valid(result.value);
    {
      var input := FileInput.Reader.getContent();
      if (0 < input.Length < Int32.max as int) {
        var parser := new Parser(input);
        var x := parser.parse();
        return x;
      } else {
        return Error("the file contains more data than Int32.max");
      }
    }

    function method getTimestamp() : int
    {
      FileInput.Reader.getTimestamp()
    }
}
