import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl
set_option autoImplicit false
open Whatwg.Streams
#check (@Whatwg.Ecma262.Promise.Reaction.mk :
  ∀ {body : Type}, Nat → Nat → Whatwg.Ecma262.Promise.ReactionType → Option body →
    Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.Reaction body)
example : True := by
  have _ : Whatwg.Ecma262.Promise.Reaction Nat := ⟨0, 1, .fulfill, some 2, .waiting⟩
  trivial
