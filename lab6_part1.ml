(*
                              CS51 Lab 6
     Variants, algebraic types, and pattern matching (continued)
 *)

(*
                               SOLUTION
 *)

(* Objective: This lab is intended to reinforce core concepts in
   typing in OCaml, including:

     Algebraic data types
     Using algebraic data types to enforce invariants
     Implementing polymorphic algebraic data types
 *)

(*======================================================================
                          Part 1: Camlville
                  Variants and invariants revisited

In this lab you'll continue to use algebraic data types to create
several data structures.

First, you'll complete instructive examples on variant types and
enforcing invariants to mdel residences in Camlville. Then, you'll
revisit an example from the reading to implement a polymorphic list as
an algebraic data type. Building on the reading, we'll add some more
functionality to this type.

NOTE: As was the case last time, since we ask that you define types in
this lab, you must complete certain exercises (1 and 9) before this will
compile with the testing framework on the course grading server. We'll
provide hints so you'll be sure to get those types right.

........................................................................
Exercise 1: There are two kinds of residences in Camlville.  A *house*
in Camlville has a street name, zip code, and building number. An
*apartment* in Camlville has a street name, zip code, building number
(the same for all units in the building), and a unit number.

Define a variant type to capture the idea of a residence. What
representation and types make sense? Is there one right answer or
several possibilities?

We will start by assuming there are no restrictions on the zip code and
building and unit numbers other than those given by their types (zip
codes must be strings and building and unit numbers must be integers).
Though zipcodes on first glance are numbers, they are generally not
treated as numbers. (What would be the conceptual meaning of averaging
zipcodes?) They also can contain leading zeros (Cambridge, 02138).
Consequently, we choose to represent zipcodes as strings.

However, there are only four streets in Camlville (regardless of
zipcode) which are the following:

    High Street
    Hauptstrasse
    Rue Principale
    Main Street

How might you use algebraic data types to enforce this invariant on
street names?

************************************************************************
Try to do this exercise first. There may be more than one way to solve
this problem, so if your solution doesn't compile against our unit
tests, see <https://url.cs51.io/lab6-1> for our solution and use that.
Do not proceed until your code compiles cleanly against the unit tests.
************************************************************************
......................................................................*)

type street =
  | HighStreet
  | Hauptstrasse
  | RuePrincipale
  | MainStreet ;;

type address = { building : int; street : street; zip_code : string } ;;

type residence =
  | House of address
  | Apartment of int * address ;;

(* A first pass at defining a residence algebraic data type may have
   looked like this:

      type residence =
        | House of int * street * string
        | Apartment of int * int * street * string ;;

   This algebraic data type follows the pattern of the RGB colors from
   the last lab. Each data component is an element of the tuple.
   However, RGB's have a well-known definitive ordering of data elements
   inherent in the name RGB. It is less clear what the ordering of
   elements in the tuples above represent. For instance, someone seeing
   the apartment value may not be sure which `int` represented the
   street number and which the unit. Records allow for the creation of
   names to clearly label values. As records are types, they can be used
   in algebraic data types as well. An alternative residence algebraic
   data type using records may have been as below:

      type house = { building : int; 
                     street : street;
                     zipcode : string} ;;
      type apartment = { unit : int;
                         building : int;
                         street : street;
                         zipcode : string} ;;
      type residence =
        | House of house
        | Apartment of apartment ;;

   This format has the advantage of named fields. For the apartment
   especially, it is now quite clear what each `int` represents, and
   the order of fields is not important. However, the `house` and
   `apartment` records have a lot in common. Our first algebraic data
   type packages that commonality into a single `address` record,
   which is common to both houses and apartments. As apartments have
   only one additional field, it seems reasonable to create the `int *
   address` tuple to add the unit number. *)

(* After implementing the residence type, compare it with our type
definition at <https://url.cs51.io/lab6-1>. Consider the tradeoffs we
may have considered if you find our definition differs from your own.

To compile against our unit tests, please change your definition to
match ours. You may comment out your original type definition if you
would like to keep it.

Valid zip codes in Camlville are given as five digits. For example,
12345, 63130, and 02138 are valid zipcodes, but -0004, 2138, and F69A
are not. We'll represent zip codes with strings, but will want to be
able to validate them appropriately. In this lab, we'll use the
`valid_` validation convention from lab 5. *)

(*......................................................................
Exercise 2: Define a function `valid_zip` that takes a `string` and
returns a `bool` indicating whether or not the string represents a valid
zip code. You may find the function `Stdlib.int_of_string_opt` and the
`String` or `Str` modules to be useful.

(For the purpose of defining a "valid zip code", you don't have to worry
about what the function does on strings interpreted as non-base-10
numbers. For example, `0x100` (hexadecimal) may or may not pass your
test but `abcde` definitely should not.)
......................................................................*)

(* This solution uses `int_of_string_opt` to convert a five-character
   string. It inherits some not ideal behavior from that function,
   for instance,

      # valid_zip "0___0" ;;
      - : bool = true
      # valid_zip "0x100" ;;
      - : bool = true
 *)
let valid_zip (zip : string) : bool =
  String.length zip = 5
  && match int_of_string_opt zip with
     | None -> false
     | Some x -> x >= 0 ;;

(* An alternative uses the simple regular expression patterns from the
   Str module. It more directly manifests the requirement of five
   decimal digits:

      # valid_zip "0___0" ;;
      - : bool = false
      # valid_zip "0x100" ;;
      - : bool = false

    let valid_zip (zip : string) : bool =
      let pattern = Str.regexp "^[0-9][0-9][0-9][0-9][0-9]$" in
      Str.string_match pattern zip 0 ;;
 *)

(*......................................................................
Exercise 3: Define a function `valid_residence` that enforces proper
zipcodes, and verifies that building and unit numbers are greater than
0. It should return `true` if its argument is valid and `false`
otherwise.
......................................................................*)

(* Here's a self-contained definition. *)

let valid_residence (res : residence) : bool =
  let valid_address ({building; zip_code; _} : address) : bool =
    valid_zip zip_code && building > 0 in
  match res with
  | House addr -> valid_address addr
  | Apartment (apt_unit, addr) -> valid_address addr && apt_unit > 0 ;;

(* An important design question is when one should define an auxiliary
   function *locally* within the body of a larger function (as with
   `valid_address` inside `valid_residence` above) and when to
   *globally* define an auxiliary function. Generally, you should define
   a function in the *smallest scope possible that simultaneously limits
   redundancy*. In other words, auxiliary functions should be defined
   within the function they are used unless they are of more general
   applicability. In the above approach, the `valid_address` function is
   localized to the `valid_residence` function. But an
   address-validation function is arguably of general utility. Thus it
   may be appropriate to separate it out, as

    let valid_address ({building; zip_code; _} : address) : bool =
      valid_zip zip_code && building > 0 ;;

   Then the `valid_residence` function can be simplified to 

    let valid_residence (res : residence) : bool =
      match res with
      | House addr -> valid_address addr
      | Apartment(apt_unit, addr) -> valid_address addr && apt_unit > 0 ;;
 *)

(*......................................................................
Exercise 4: Time to get neighborly. Define a function `neighbors` that
takes two residences and returns a `bool` indicating whether or not
they are neighbors. In Camlville, a neighbor is someone living on the
same street in the same zipcode.

Note: By this definition, a residence is considered to be its own
neighbor.
......................................................................*)

(* Further to the design issue of local versus global function
   definitions, because we will use `address_of_residence` in
   solutions to subsequent problems, we define it globally here. *)

let address_of_residence (r : residence) : address =
  match r with
  | House addr
  | Apartment(_, addr) -> addr ;;

let neighbors (place1 : residence) (place2 : residence) : bool =
  let addr1 = address_of_residence place1 in
  let addr2 = address_of_residence place2 in
  addr1.street = addr2.street
                 && addr1.zip_code = addr2.zip_code ;;

(*......................................................................
Exercise 5: When buyers purchase a new residence in Camlville, they
must register the residence with the town hall, which creates a record
of the residence location and owner.

Implement a function `record_residence` to perform this bookkeeping. It
should accept a residence and a name (which should be a string) and
return the corresponding entry to be made as a value of the type
`town_record`, defined below. The town works hard to prevent fraudulent
residences from being entered into historical records and has asked you
to do the same by raising an `Invalid_argument` exception when
appropriate.
......................................................................*)

type town_record = { residence : residence; name : string } ;;

let record_residence (residence : residence)
                     (name : string)
                   : town_record =
  if valid_residence residence then
    { residence; name }
  else
    raise (Invalid_argument "record_residence: invalid residence") ;;

(* We've renamed one of the arguments to take advantage of field
   punning in the return value. *)

(*......................................................................
Exercise 6: Neighbor search.

As part of Bob's promotion, he has been moved to the next floor up at
work. He doesn't yet know any of his coworkers, and so he decides to
search through Camlville's records to determine which of them are his
neighbors. Camlville keeps extensive records, so he doesn't want to
have to look them up manually. Instead, he asks you to do it for him,
since he heard you were learning a lot of useful skills in CS51.

Write a function `named_neighbors` that, given two names (strings
again) and a `town_record list`, searches though the list to
determine if the two people are neighbors, as defined above, and
returns a `bool`. Return a `Failure` exception in the event that
either of the names does not appear in the list of records. You can
assume that no two town records have the same name.

Hint: You may find the `List.find` function to be useful.
......................................................................*)

(* This implementation makes good use of the `List.find` function,
   trapping its exception and reraising the desired one if the name is
   not found. Notice how `find_residence_with_name` doesn't need an
   argument for the town records, as it is defined within the scope of
   the `records` argument. *)

let named_neighbors (name1 : string)
                    (name2 : string)
                    (records : town_record list)
                  : bool =

  let find_residence_with_name name =
    try
      (List.find (fun record -> record.name = name) records).residence
    with Not_found -> failwith "named_neighbors: name not found" in

  neighbors (find_residence_with_name name1)
            (find_residence_with_name name2) ;;
