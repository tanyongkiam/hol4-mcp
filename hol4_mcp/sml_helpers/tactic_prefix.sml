(* tactic_prefix.sml - Use HOL's TacticParse for exact tactic replay

   This uses HOL's own sliceTacticBlock to extract syntactically valid
   tactic prefixes, guaranteeing 100% match with holmake semantics.

   Usage:
     prefix_commands_json "rpt strip_tac >> simp[] >> fs[]" 20;
     => {"ok":"e(rpt strip_tac\n  >> simp[]);\n"}

     step_positions_json "rpt strip_tac >> simp[] >> fs[]";
     => {"ok":[13,23,31]}
*)

(* Load TacticParse *)
load "TacticParse";

(* JSON helpers *)
fun json_escape_char c =
  case c of
    #"\"" => "\\\""
  | #"\\" => "\\\\"
  | #"\n" => "\\n"
  | #"\r" => "\\r"
  | #"\t" => "\\t"
  | _ => if Char.ord c < 32
         then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord c))
         else String.str c

fun json_escape_string s =
  String.concat (map json_escape_char (String.explode s))

fun json_string s = "\"" ^ json_escape_string s ^ "\""
fun json_int n = Int.toString n
fun json_ok payload = "{\"ok\":" ^ payload ^ "}"
fun json_err msg = "{\"err\":" ^ json_string msg ^ "}"

fun json_string_array strs =
  "[" ^ String.concatWith "," (map json_string strs) ^ "]"

(* goals_json for getting proof state *)
fun goal_to_json (asms, concl) =
  "{\"asms\":" ^ json_string_array (map term_to_string asms) ^
  ",\"goal\":" ^ json_string (term_to_string concl) ^ "}"

fun goals_to_json_array goals =
  "[" ^ String.concatWith "," (map goal_to_json goals) ^ "]"

fun goals_json () =
  let val goals = top_goals()
  in print (json_ok (goals_to_json_array goals) ^ "\n") end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Get e() commands to replay tactics up to a given offset in the proof body.
   Uses HOL's sliceTacticBlock for exact semantics. *)
fun prefix_commands proofBody endOffset =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* sliceTacticBlock start stop sliceClose defaultSpan tree *)
    val frags = TacticParse.sliceTacticBlock 0 endOffset false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun prefix_commands_json proofBody endOffset =
  print (json_ok (json_string (prefix_commands proofBody endOffset)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Get all tactic steps with their end positions.
   Each step is a natural "stopping point" in the proof.
   Returns: [{"cmd":"e(tac);","end":offset}, ...] *)
fun tactic_steps proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)

    (* Helper to check if a tac_expr is "atomic" for linearization purposes *)
    fun isAtom e = case TacticParse.topSpan e of
        NONE => false
      | SOME (l, r) => true  (* Has a span = treat as atom *)

    (* Linearize the entire proof to get all fragments *)
    val allFrags = TacticParse.linearize isAtom tree

    (* Extract spans from fragments to find step boundaries *)
    fun fragSpan (TacticParse.FAtom a) = TacticParse.topSpan a
      | fragSpan (TacticParse.FGroup (p, _)) = SOME p
      | fragSpan _ = NONE

    (* Collect end positions of each top-level step *)
    fun collectEnds [] acc = rev acc
      | collectEnds (f::fs) acc =
          case fragSpan f of
            SOME (_, endPos) => collectEnds fs (endPos :: acc)
          | NONE => collectEnds fs acc

    val endPositions = collectEnds allFrags []

    (* For each end position, generate the e() command to reach that state *)
    fun makeStep endPos =
      let
        val frags = TacticParse.sliceTacticBlock 0 endPos false defaultSpan tree
        val cmd = TacticParse.printFragsAsE proofBody frags
      in
        (cmd, endPos)
      end
  in
    map makeStep endPositions
  end

fun step_to_json (cmd, endPos) =
  "{\"cmd\":" ^ json_string cmd ^ ",\"end\":" ^ json_int endPos ^ "}"

fun tactic_steps_json proofBody =
  let
    val steps = tactic_steps proofBody
    val jsonSteps = "[" ^ String.concatWith "," (map step_to_json steps) ^ "]"
  in
    print (json_ok jsonSteps ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Simpler API: just get step count and end positions *)
fun step_positions proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val allFrags = TacticParse.linearize isAtom tree

    fun fragSpan (TacticParse.FAtom a) = TacticParse.topSpan a
      | fragSpan (TacticParse.FGroup (p, _)) = SOME p
      | fragSpan _ = NONE

    fun collectEnds [] acc = rev acc
      | collectEnds (f::fs) acc =
          case fragSpan f of
            SOME (_, endPos) => collectEnds fs (endPos :: acc)
          | NONE => collectEnds fs acc
  in
    collectEnds allFrags []
  end

fun step_positions_json proofBody =
  let
    val positions = step_positions proofBody
    val jsonArr = "[" ^ String.concatWith "," (map json_int positions) ^ "]"
  in
    print (json_ok jsonArr ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Generate e() commands for full proof using sliceTacticBlock.
   Each step becomes a separate e() call, enabling backup_n. *)
fun step_commands proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* Full slice from 0 to end, sliceClose=false *)
    val frags = TacticParse.sliceTacticBlock 0 (String.size proofBody) false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun step_commands_json proofBody =
  print (json_ok (json_string (step_commands proofBody)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* backup_n - undo N e() calls in the goaltree *)
fun backup_n 0 = ()
  | backup_n n = (proofManagerLib.b(); backup_n (n - 1));

(* Generate e() commands for a slice of the proof body.
   Used after backup_n to execute just the remaining portion.
   startOffset/endOffset are character positions in proofBody.
   When slicing inside >-, generates HEADGOAL automatically. *)
fun partial_step_commands proofBody startOffset endOffset =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* sliceClose=false to avoid FFClose tokens unlinearize can't handle *)
    val frags = TacticParse.sliceTacticBlock startOffset endOffset false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun partial_step_commands_json proofBody startOffset endOffset =
  print (json_ok (json_string (partial_step_commands proofBody startOffset endOffset)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* step_plan: Get step boundaries aligned with executable commands.
   Returns (end_offset, command) pairs where each command is one e() call.
   This is the single source of truth for O(1) tactic navigation. *)
fun step_plan proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    val frags = TacticParse.sliceTacticBlock 0 (String.size proofBody) false defaultSpan tree
    
    (* Extract the maximum end offset from a fragment *)
    fun fragEnd (TacticParse.FAtom a) = 
        (case TacticParse.topSpan a of SOME (_, r) => r | NONE => 0)
      | fragEnd (TacticParse.FGroup ((_, r), _)) = r
      | fragEnd (TacticParse.FBracket (_, _, _, a)) = 
        (case TacticParse.topSpan a of SOME (_, r) => r | NONE => 0)
      | fragEnd (TacticParse.FMBracket (_, _, _, _, a)) = 
        (case TacticParse.topSpan a of SOME (_, r) => r | NONE => 0)
      | fragEnd _ = 0
    
    (* Get max end offset from a list of fragments *)
    fun fragsEnd [] = 0
      | fragsEnd fs = List.foldl (fn (f, mx) => Int.max (fragEnd f, mx)) 0 fs
    
    (* Process each step (frag list) to get (end_offset, cmd) *)
    fun processStep fragList =
      let
        val endOff = fragsEnd fragList
        val cmd = TacticParse.printFragsAsE proofBody [fragList]
      in
        (endOff, cmd)
      end
    
    (* Filter out empty commands *)
    val steps = map processStep frags
    val nonEmpty = List.filter (fn (_, cmd) => String.size cmd > 0) steps
  in
    nonEmpty
  end

fun step_plan_json proofBody =
  let
    val steps = step_plan proofBody
    fun stepToJson (endOff, cmd) =
      "{\"end\":" ^ json_int endOff ^ ",\"cmd\":" ^ json_string cmd ^ "}"
    val stepsJson = "[" ^ String.concatWith "," (map stepToJson steps) ^ "]"
  in
    print (json_ok stepsJson ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");
