module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization

/-!
# A presheaf of rings mapping locally bijectively into a sheaf of rings

Let `(C, J)` be a site on which `RingCat`-valued presheaves can be sheafified. A morphism
`c : P ⟶ S.obj` from a presheaf of rings into a sheaf of rings which is locally injective and
locally surjective exhibits `S` as the sheafification of `P`.

This is the `RingCat` counterpart of `Stacks.sheafifyIsoOfLocallyBijective`, which says the same
for presheaves of modules; the proof is the same three steps, read in `RingCat` rather than in
`AddCommGrpCat`. A locally bijective morphism lies in `CategoryTheory.GrothendieckTopology.W` by
`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective`, membership of `W` is exactly
invertibility under `presheafToSheaf` by `CategoryTheory.GrothendieckTopology.W_iff`, and the
sheafification counit is an isomorphism.

## Main definitions

* `Stacks.sheafifyRingHom`: the morphism of sheaves of rings out of the sheafification of `P`
  determined by a morphism `P ⟶ S.obj`.
* `Stacks.sheafifyRingIsoOfLocallyBijective`: **a presheaf of rings which maps locally
  bijectively into a sheaf of rings exhibits that sheaf as its sheafification.**

## Main results

* `Stacks.toSheafify_sheafifyRingHom`: the induced morphism restricts along the sheafification
  unit to the given one, which is its defining property.
* `Stacks.isIso_sheafifyRingHom`: local bijectivity makes it an isomorphism.

## Implementation notes

The induced morphism is defined as the transpose of `c` under the sheafification adjunction rather
than as `CategoryTheory.sheafifyLift`, so that `CategoryTheory.Adjunction.homEquiv_counit`
identifies it with `presheafToSheaf J RingCat` applied to `c` followed by the counit with no
further rewriting; the two agree by definition, which is `Stacks.sheafifyRingHom_hom`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks

section SheafifyRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J RingCat.{w}] {P : Cᵒᵖ ⥤ RingCat.{w}} {S : Sheaf J RingCat.{w}}
  (c : P ⟶ S.obj)

/-- The morphism of sheaves of rings from the sheafification of a presheaf of rings `P` to a
sheaf of rings `S` determined by a morphism `P ⟶ S.obj`. -/
noncomputable def sheafifyRingHom : (presheafToSheaf J RingCat.{w}).obj P ⟶ S :=
  ((sheafificationAdjunction J RingCat.{w}).homEquiv P S).symm c

/-- The underlying morphism of presheaves of `sheafifyRingHom c` is `sheafifyLift J c`. -/
theorem sheafifyRingHom_hom : (sheafifyRingHom c).hom = sheafifyLift J c S.property := rfl

/-- The induced morphism restricts along the sheafification unit to the given one. -/
theorem toSheafify_sheafifyRingHom : toSheafify J P ≫ (sheafifyRingHom c).hom = c :=
  toSheafify_sheafifyLift J c S.property

/-- The induced morphism is the sheafification of `c` followed by the sheafification counit. -/
theorem sheafifyRingHom_eq :
    sheafifyRingHom c =
      (presheafToSheaf J RingCat.{w}).map c ≫
        (sheafificationAdjunction J RingCat.{w}).counit.app S :=
  (sheafificationAdjunction J RingCat.{w}).homEquiv_counit P S c

variable [J.WEqualsLocallyBijective RingCat.{w}]

/-- A locally bijective morphism into a sheaf of rings induces an isomorphism out of the
sheafification. -/
theorem isIso_sheafifyRingHom (hinj : Presheaf.IsLocallyInjective J c)
    (hsurj : Presheaf.IsLocallySurjective J c) : IsIso (sheafifyRingHom c) := by
  have := hinj
  have := hsurj
  have h : IsIso ((presheafToSheaf J RingCat.{w}).map c) :=
    (J.W_iff c).mp (GrothendieckTopology.W_of_isLocallyBijective J c)
  have h2 : IsIso ((presheafToSheaf J RingCat.{w}).map c ≫
      (sheafificationAdjunction J RingCat.{w}).counit.app S) :=
    IsIso.comp_isIso' h inferInstance
  rw [← sheafifyRingHom_eq] at h2
  exact h2

/-- **A presheaf of rings which maps locally bijectively into a sheaf of rings exhibits that
sheaf as its sheafification.** -/
noncomputable def sheafifyRingIsoOfLocallyBijective (hinj : Presheaf.IsLocallyInjective J c)
    (hsurj : Presheaf.IsLocallySurjective J c) :
    (presheafToSheaf J RingCat.{w}).obj P ≅ S :=
  haveI := isIso_sheafifyRingHom c hinj hsurj
  asIso (sheafifyRingHom c)

/-- The forward morphism of `sheafifyRingIsoOfLocallyBijective` is `sheafifyRingHom c`. -/
theorem sheafifyRingIsoOfLocallyBijective_hom (hinj : Presheaf.IsLocallyInjective J c)
    (hsurj : Presheaf.IsLocallySurjective J c) :
    (sheafifyRingIsoOfLocallyBijective c hinj hsurj).hom = sheafifyRingHom c :=
  rfl

end SheafifyRing

end Stacks

end
