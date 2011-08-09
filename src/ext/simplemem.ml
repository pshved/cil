(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(*
 * Simplemem: Transform a program so that all memory expressions are
 * "simple". Introduce well-typed temporaries to hold intermediate values
 * for expressions that would normally involve more than one memory
 * reference. 
 *
 * If simplemem succeeds, each lvalue should contain only one Mem()
 * constructor. 
 *)
open Cil

(* current context: where should we put our temporaries? *)
let thefunc = ref None 

(* build up a list of assignments to temporary variables *)
let assignment_list = ref []

(* turn "int a[5][5]" into "int ** temp" *)
let rec array_to_pointer tau = 
  match unrollType tau with
    TArray(dest,_,al) -> TPtr(array_to_pointer dest,al)
  | _ -> tau

exception TmpOutsideAFun

(* create a temporary variable in the current function *)
let make_temp prefix tau = 
  let tau = array_to_pointer tau in 
  match !thefunc with
    Some(fundec) -> makeTempVar fundec ~name:prefix tau
  | None -> raise TmpOutsideAFun

(* separate loffsets into "scalar addition parts" and "memory parts" *)
let rec separate_loffsets lo = 
  match lo with
    NoOffset -> NoOffset, NoOffset
  | Field(fi,rest) -> 
      let s,m = separate_loffsets rest in
      Field(fi,s) , m
  | Index(_) -> NoOffset, lo

(* Recursively decompose the lvalue so that what is under a "Mem()"
 * constructor is put into a temporary variable. *)
let rec handle_lvalue ?(skip_outside = false) prefix (lb,lo) = 
  let s,m = separate_loffsets lo in 
  match lb with
    Var(vi) -> 
      handle_loffset prefix (lb,s) m 
  | Mem(Lval(Var(_),NoOffset)) ->
			(* special case to avoid generating "tmp = ptr;" *)
      handle_loffset prefix (lb,s) m 
  | Mem(e) -> 
      begin try
        let new_vi = make_temp prefix (typeOf e) in
        assignment_list := (Set((Var(new_vi),NoOffset),e,!currentLoc)) 
          :: !assignment_list ;
        handle_loffset prefix (Mem(Lval(Var(new_vi),NoOffset)),NoOffset) lo
      with TmpOutsideAFun ->
        if skip_outside then
          (lb,s)
        else
          failwith "simplemem: temporary needed outside a function"
      end
and handle_loffset prefix lv lo = 
  match lo with
    NoOffset -> lv
  | Field(f,o) -> handle_loffset prefix (addOffsetLval (Field(f,NoOffset)) lv) o
  | Index(exp,o) -> handle_loffset prefix (addOffsetLval (Index(exp,NoOffset)) lv) o

(* the transformation is implemented as a Visitor *)
class simpleVisitor ?(skip_outside = false) prefix = object 
  inherit nopCilVisitor

  method vfunc fundec = (* we must record the current context *)
    thefunc := Some(fundec) ;
    DoChildren

  method vglob _ = (* we must also record that there's no matching context *)
    thefunc := None ;
    DoChildren

  method vlval lv = ChangeDoChildrenPost(lv,
      (fun lv -> handle_lvalue ~skip_outside:skip_outside prefix lv))

  method unqueueInstr () = 
      let result = List.rev !assignment_list in
      assignment_list := [] ;
      match (skip_outside,!thefunc) with
        |(true,None) -> [] (* pretend that we don't have any assignments *)
        |(_,_) -> result (* this may throw an exception if the context is improper (global variable initializer needs simplemem *)
end

(* Main entry point: apply the transformation to a file.  Optionally, you may specify a prefix for the new temporary variables. *)
let simplemem ?(prefix = "mem_") (f : file) =
  try 
    visitCilFileSameGlobals (new simpleVisitor prefix) f;
    f
  with e -> Printf.printf "Exception in Simplemem.simplemem: %s\n"
    (Printexc.to_string e) ; raise e

(* Auxillary entry point: apply the transformation to a file, but do not apply them outside functions.  Optionally, you may specify a prefix for the new temporary variables. *)
let simplemem_inside_functions ?(prefix = "mem_") (f : file) =
  try
    visitCilFileSameGlobals (new simpleVisitor ~skip_outside:true prefix) f;
    f
  with e -> Printf.printf "Exception in Simplemem.simplemem: %s\n"
    (Printexc.to_string e) ; raise e

let feature : featureDescr = 
  { fd_name = "simpleMem";
    fd_enabled = Cilutil.doSimpleMem;
    fd_description = "simplify all memory expressions" ;
    fd_extraopt = [];
    fd_doit = (function (f: file) -> ignore (simplemem f)) ;
    fd_post_check = true;
  } 
