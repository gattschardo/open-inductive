theory OI_Test
imports
  Main
begin

ML {*
fun assert_eq a b =
  if a = b then ()
  else raise Fail "assert fail"
*}

ML_file "fail.ML"

ML_file "../src/pretty.ML"
ML_file "pretty_test.ML"

ML_file "../src/result.ML"
ML_file "result_test.ML"

end