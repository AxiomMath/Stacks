module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The projection formula for a dualizable object

Let `F ⊣ G` be an adjunction between monoidal categories with `F` monoidal, and let `N` be an
object of the source of `F` with a left dual `N'` (an exact pairing `N' ⊣ N`). Then

`G(M ⊗ F N) ≅ G M ⊗ N`, naturally in `M`:

both sides are right adjoints, of `A ↦ F A ⊗ F N'` and of `A ↦ F(A ⊗ N')`, and these are
isomorphic through the tensor structure of `F`. Dually, for `L ⊣ R` with `R` monoidal and `N`
with a right dual, `L(M ⊗ R N) ≅ L M ⊗ N`. This is the formal half of the projection formula:
for sheaves of modules, `N` being locally free of finite rank is what makes it dualizable.

## Main definitions

* `CategoryTheory.Adjunction.tensorRightProjectionIso`: `(- ⊗ F N) ⋙ G ≅ G ⋙ (- ⊗ N)`.
* `CategoryTheory.Adjunction.tensorRightProjectionIsoOfMonoidalRight`:
  `(- ⊗ R N) ⋙ L ≅ L ⋙ (- ⊗ N)`.

## Main results

* `CategoryTheory.preservesInjectiveObjects_tensorRight_of_exactPairing`: tensoring with an
  object having duals on both sides preserves injective objects.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

namespace Adjunction

/-- The tensor structure of a monoidal functor, as an isomorphism
`(- ⊗ N) ⋙ F ≅ F ⋙ (- ⊗ F N)`. -/
def tensorRightCompIso (F : C ⥤ D) [F.Monoidal] (N : C) :
    tensorRight N ⋙ F ≅ F ⋙ tensorRight (F.obj N) :=
  NatIso.ofComponents (fun M => (Functor.Monoidal.μIso F M N).symm)
    (fun φ => by simp)

/-- **The projection formula for a right adjoint**: for an adjunction `F ⊣ G` with `F` monoidal
and an exact pairing `N' ⊣ N`, `G(M ⊗ F N) ≅ G M ⊗ N` naturally in `M`. Both functors are right
adjoints, of `F ⋙ (- ⊗ F N')` and of `(- ⊗ N') ⋙ F`, which are isomorphic through the tensor
structure of `F`. -/
def tensorRightProjectionIso {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] (N N' : C)
    [ExactPairing N' N] :
    tensorRight (F.obj N) ⋙ G ≅ G ⋙ tensorRight N :=
  letI := ExactPairing.map F N' N
  (adj.comp (tensorRightAdjunction (F.obj N') (F.obj N))).rightAdjointUniq
    (((tensorRightAdjunction N' N).comp adj).ofNatIsoLeft (tensorRightCompIso F N'))

/-- **The projection formula for a left adjoint**: for an adjunction `L ⊣ R` with `R` monoidal
and an exact pairing `N ⊣ N'`, `L(M ⊗ R N) ≅ L M ⊗ N` naturally in `M`. Both functors are left
adjoints, of `R ⋙ (- ⊗ R N')` and of `(- ⊗ N') ⋙ R`, which are isomorphic through the tensor
structure of `R`. -/
def tensorRightProjectionIsoOfMonoidalRight {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Monoidal]
    (N N' : D) [ExactPairing N N'] :
    tensorRight (R.obj N) ⋙ L ≅ L ⋙ tensorRight N :=
  letI := ExactPairing.map R N N'
  ((tensorRightAdjunction (R.obj N) (R.obj N')).comp adj).leftAdjointUniq
    ((adj.comp (tensorRightAdjunction N N')).ofNatIsoRight (tensorRightCompIso R N'))

end Adjunction

/-- **Tensoring with an object having duals on both sides preserves injective objects**: with
exact pairings `X ⊣ Y` and `Y ⊣ X`, `- ⊗ X` is right adjoint to `- ⊗ Y`, which is itself a right
adjoint and so preserves monomorphisms. -/
theorem preservesInjectiveObjects_tensorRight_of_exactPairing (X Y : C)
    (h₁ : ExactPairing X Y) (h₂ : ExactPairing Y X) :
    (tensorRight X).PreservesInjectiveObjects :=
  have : (tensorRight Y).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction (tensorRightAdjunction X Y)
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (tensorRightAdjunction Y X)

end CategoryTheory
