---- MODULE HDiskSynod ----

(******************************************************************************)
(* Modification History                                                       *)
(******************************************************************************)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                        *)
(******************************************************************************)
(******************************************************************************)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                              *)
(******************************************************************************)
(******************************************************************************)
(* The BalancedKitty module defines a set of predicates and operators that    *)
(* describe the behavior of a simple smart contract.                           *)
(******************************************************************************)
(******************************************************************************)
(* The contract allows an owner to create new kitties, as well as to         *)
(* transfer ownership of them. It also keeps track of how many kitties each   *)
(* user has, and allows for the creation of special "gift" kitties that can be  *)
(* transferred but not created.                                               *)
(******************************************************************************)
(******************************************************************************)
(* The contract also includes a simple mechanism for balancing the supply of *)
(* kitties, where every user has to have at least a certain minimum number of *)
(* kitties before they can transfer any.                                       *)
(******************************************************************************)
(******************************************************************************)
(* The following variables and predicates are used in the definition of the  *)
(* contract:                                                                  *)
(******************************************************************************)
(******************************************************************************)
(* bk.bal is a record that keeps track of how many kitties each user has.    *)
(* It maps each user to an integer representing the number of kitties they   *)
(* have.                                                                     *)
(******************************************************************************)
(******************************************************************************)
(* bk.inp is a record that keeps track of all the inputs that have been sent *)
(* to the contract. It maps each input (i.e., a sender and receiver) to an   *)
(* integer representing the number of kitties they have received.            *)
(******************************************************************************)
(******************************************************************************)
(* bk.gift is a set that keeps track of all the gift kitties that exist in   *)
(* the contract.                                                             *)
(******************************************************************************)
(******************************************************************************)
(* bk.minBal is an integer representing the minimum number of kitties each  *)
(* user must have before they can transfer any.                               *)
(****************************************************************)
(***************************************************************************
* The following predicates are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is true if the number of kitties that user u
*     has exceeds the minimum balance.
*
*   - bk.canTransfer(u, v, k) is true if user u can transfer k kitties to
*     user v, taking into account the minimum balance and any gift kitties
*     that may be present.
*
*   - bk.transfer(u, v, k) transfers k kitties from user u to user v,
*     adjusting the balances accordingly.
***************************************************************************/
(******************************************************************************)
(* The following operators are used in the definition of the contract:
*
*   - bk.newKitty(u, k) creates a new kitty for user u with initial balance k
*     and adds it to their balance.
*
*   - bk.transferGift(u, v, k) creates a gift kitty for user u that can be
*     transferred to user v by the owner of the contract.
*
*   - bk.giveBack(u, k) removes k kitties from user u's balance and adds
*     them back to the balance of the user who owns the contract. This is
*     used to adjust the minimum balance for all users in the case that a
*     transfer would otherwise be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*   - bk.lem2(u, v, k) states that if user u can transfer k kitties to user v,
*     and user v has at least as many kitties as user u does before the transfer,
*     then the transfer will not be refused due to insufficient balance.
***************************************************************************/
(******************************************************************************)
(* The following spec is used in the definition of the contract:
*
*   - bk.spec states that the contract always behaves correctly, with respect to the
*     predicates and operators defined above.
***************************************************************************/
(******************************************************************************)
(* The following invariants are used in the definition of the contract:
*
*   - bk.balSufficient(u, k) is an invariant that ensures that all users have at
*     least a minimum number of kitties before they can transfer any.
***************************************************************************/
(******************************************************************************)
(* The following lemmas are used in the definition of the contract:
*
*   - bk.lem1(u, k) states that if user u has at least k kitties before a transfer is made,
*     then they will still have at least k kitties after the transfer is made.
*
*
====