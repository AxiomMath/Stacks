module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.SkyscraperUnit
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.DualOverField

/-!
# The dual is faithful on perfect complexes

Let `X` be a scheme and `D = R𝓗om(-, 𝒪_X)` the dual of [Stacks, Tag 08DQ] on `D(𝒪_X)`. On perfect
objects the biduality map `K ⟶ (K^∨)^∨` is an isomorphism, so `D` is faithful there: a morphism
`f : A ⟶ B` into a perfect complex is recovered from `f^∨∨` and the biduality maps, the one at
`B` being an isomorphism. In particular `Hom(A, B)` vanishes as soon as `Hom(B^∨, A^∨)` does.
Applied to the duals of perfect complexes, this is the step of the proof of [Stacks, Tag 0G03]
part (2) that passes from `Hom(𝒪_x, K[i]) = 0` to `Hom(K^∨, (𝒪_x)^∨[i]) = 0`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.dual_map_injective_of_isPerfect`: the dual is
  injective on morphisms into a perfect complex.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.subsingleton_hom_of_subsingleton_hom_dual`.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- **The dual is injective on morphisms into a perfect complex**: `f` is `f^∨∨` conjugated by the
biduality maps, the one at the target being an isomorphism ([Stacks, Tag 08DQ]). -/
theorem dual_map_injective_of_isPerfect {A B : DerivedCategory X.Modules}
    (hB : IsPerfect (X := X.toRingedSpace) B) {f g : A ⟶ B}
    (h : (DualOverField.dual X).map f.op = (DualOverField.dual X).map g.op) : f = g := by
  have hiso : IsIso ((Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app B) :=
    Stacks.SheafOfModules.isIso_derivedBidualMap_of_isPerfectSpace (X := X.toRingedSpace) B hB
  have hf := (Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).naturality f
  have hg := (Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).naturality g
  have key : f ≫ (Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app B =
      g ≫ (Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app B :=
    hf.trans (Eq.trans (congrArg (fun φ => _ ≫ (DualOverField.dual X).map φ.op) h) hg.symm)
  exact (@cancel_mono _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hiso) _ _).1 key

/-- **`Hom(A, B) = 0` as soon as `Hom(B^∨, A^∨) = 0`**, for `B` perfect. -/
theorem subsingleton_hom_of_subsingleton_hom_dual {A B : DerivedCategory X.Modules}
    (hB : IsPerfect (X := X.toRingedSpace) B)
    (h : Subsingleton ((DualOverField.dual X).obj (op B) ⟶ (DualOverField.dual X).obj (op A))) :
    Subsingleton (A ⟶ B) :=
  ⟨fun _ _ => dual_map_injective_of_isPerfect X hB (Subsingleton.elim _ _)⟩

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
