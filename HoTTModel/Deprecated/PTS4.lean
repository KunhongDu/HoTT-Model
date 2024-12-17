universe u

namespace PureTypeSystem

structure Specification where
  sort : Type u
  ax : sort → sort → Prop
  rel : sort → sort → sort → Prop

mutual
inductive PTerm (S : Specification)
| var : PTerm S -- ℕ → PTerm S????
| sort : S.sort → PTerm S
| app : PTerm S → PTerm S → PTerm S
| pi : PTerm S → PTerm S → PTerm S
| abs : PTerm S → PTerm S → PTerm S
| sub : PTerm S → PSub S → PTerm S

inductive PSub (S : Specification)
| emp : PSub S
| weak : PSub S
| id : PSub S
| comp : PSub S → PSub S → PSub S
| ext : PSub S → PTerm S → PSub S

end
