import Lean
open Lean Meta Elab Tactic

/-!
  ReaderT: Monad transformer for adding a `r` parameter to the monad stack.
    `r` is the type of the context,
    which is a read-only environment shared by all monadic computations in the stack.
  StateRefT: Monad transformer for adding a `σ` parameter to the monad stack.
    `σ` is the type of the state,
    which is a mutable state that can be read and modified by all monadic computations in the stack.
-/

#check TacticM -- ReaderT Tactic.Context $ StateRefT Tactic.State TermElabM
#check TermElabM -- ReaderT Term.Context $ StateRefT Term.State MetaM
#check MetaM -- ReaderT Meta.Context $ StateRefT Meta.State CoreM
#check CoreM -- ReaderT Core.Context $ StateRefT Core.State (EIO Exception)
