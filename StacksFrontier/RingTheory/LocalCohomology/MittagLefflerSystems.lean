module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing

/-!
# Local cohomology of an inverse system of finite modules is Mittag-Leffler

Over a Noetherian local ring `A`, applying local cohomology supported at the maximal ideal to
an inverse system of finite `A`-modules produces, in every degree, an inverse system satisfying
the Mittag-Leffler condition. Each term of the resulting system is Artinian, and in an Artinian
module the images of the transition maps into a fixed term form a descending chain, which
stabilizes.

## Main results

* `Stacks.LocalCohomology.isMittagLeffler_localCohomology` — the local cohomology modules of an
  inverse system of finite modules satisfy the Mittag-Leffler condition.

## Implementation notes

An inverse system is a functor out of `ℕᵒᵖ`. Local cohomology of its terms is formed by placing
each module in degree zero, applying the local cohomology functor supported at the maximal
ideal, and taking cohomology in the given degree, so the transition maps of the resulting
system are exactly those induced functorially by the transition maps of the given system.

## References

* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- An inverse system of Artinian modules is Mittag-Leffler: the images of the transition maps
into a fixed term form a descending chain of subobjects, which stabilizes. -/
@[ega "0 13.1.2" "special case"]
private theorem isMittagLeffler_of_isArtinian
    {A : Type u} [Ring A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    (hF : ∀ n : ℕᵒᵖ, IsArtinian A (F.obj n)) : IsMittagLefflerCategorical F := by
  intro i
  let fi : ℕ →o (Subobject (F.obj (Opposite.op i)))ᵒᵈ :=
    { toFun := fun n => transitionImage F i (i + n) (by omega)
      monotone' := by
        intro a b hab
        show Limits.imageSubobject (F.map (homOfLE (show i ≤ i + b by omega)).op) ≤
          Limits.imageSubobject (F.map (homOfLE (show i ≤ i + a by omega)).op)
        rw [show F.map (homOfLE (show i ≤ i + b by omega)).op =
            F.map (homOfLE (show i + a ≤ i + b by omega)).op ≫
              F.map (homOfLE (show i ≤ i + a by omega)).op by
            rw [← Functor.map_comp]
            congr 1]
        exact Limits.imageSubobject_comp_le _ _ }
  let e := (ModuleCat.subobjectModule (F.obj (Opposite.op i))).dual
  let g := e.toOrderEmbedding.toOrderHom.comp fi
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes g
  refine ⟨i + c, by omega, ?_⟩
  intro k hck
  have hEq := e.injective (hc (k - i) (by omega))
  change transitionImage F i (i + c) (by omega) =
    transitionImage F i (i + (k - i)) (by omega) at hEq
  simpa only [Nat.add_sub_of_le (by omega : i ≤ k)] using hEq.symm

/-- **Stacks Project, Tag 0DX1.** Over a Noetherian local ring, the local cohomology modules of
an inverse system of finite modules satisfy the Mittag-Leffler condition in every degree. -/
@[stacks 0DX1 "local_cohomology_system"]
public theorem isMittagLeffler_localCohomology
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{v} A) (hM : ∀ n, Module.Finite A (M.obj n)) (i : ℤ) :
    IsMittagLefflerCategorical
      (M ⋙ DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
        Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing ⋙
        (Dualizing.derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).ι ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} A) i) := by
  apply isMittagLeffler_of_isArtinian
  intro n
  let : Module.Finite A (M.obj n) := hM n
  simpa using isArtinian_localCohomology_maximalIdeal A (M.obj n) i

end Stacks.LocalCohomology

end
