import Whatwg.Streams.Readable.DefaultReader
namespace Whatwg.Streams.Readable
example {α ε : Type} (s : State α ε) :
    (read s).nextRead = s.nextRead + 1 := by
  unfold read
  split
  · rfl
  · rfl
  · split
    · sorry
    · split
      · trace_state
        sorry
      · trace_state
        sorry
end Whatwg.Streams.Readable
