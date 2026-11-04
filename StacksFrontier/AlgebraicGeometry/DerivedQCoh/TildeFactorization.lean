module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Grothendieck
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# Derived sheafification factors through the derived category of quasi-coherent modules

For a commutative ring `R` the triangle of [Stacks, Tag 06Z0] has three vertices, `D(R)`,
`D(QCoh(𝒪_{Spec R}))` and `D_QCoh(𝒪_{Spec R})`, and this repository already holds two of its
edges:

* `Stacks.DerivedQCoh.derivedTildeEquiv`, the `~` edge `D(R) ≌ D(QCoh(𝒪_{Spec R}))`, which *is*
  an equivalence because `AlgebraicGeometry.tildeEquiv` is an equivalence of abelian categories;
* `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison`, the comparison
  functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT], for any scheme `X`.

This file composes them and identifies the composite with derived sheafification
`AlgebraicGeometry.derivedTilde`. The identification is immediate once it is made after the
inclusion `D_QCoh(𝒪_{Spec R}) ⥤ D(𝒪_{Spec R})`: there both functors become the derived functor of
the exact functor `M ↦ M̃`, because `tildeEquiv.functor` followed by the inclusion of the
quasi-coherent modules *is* `AlgebraicGeometry.tilde.functor`, and that inclusion is fully
faithful, so the isomorphism descends.

The consequence is the one the duality material needs. Whether derived sheafification
`D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence — the remaining content of [Stacks, Tag 06Z0], and
a hypothesis of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjoint.lean` — is
*equivalent* to the single question of whether the comparison functor of 06VT is an equivalence on
an affine scheme. Both are now proved, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`:
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` and
`AlgebraicGeometry.derivedTilde_isEquivalence`.

## Main definitions

* `Stacks.DerivedQCoh.tildeSheafOfModules` — `AlgebraicGeometry.tilde.functor` with its codomain
  spelled `SheafOfModules (Spec R).ringCatSheaf`.

## Main results

* `Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso` — the `~` edge of 06Z0 followed by the
  comparison functor of 06VT is derived sheafification.
* `Stacks.DerivedQCoh.derivedTilde_isEquivalence_iff_comparison` — derived sheafification is an
  equivalence exactly when the comparison functor of 06VT is one, on an affine scheme.
* `Stacks.DerivedQCoh.derivedTilde_isEquivalence` — the direction the consumers use.

## Implementation notes

**What this file contributes, and where the remainder is proved.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/Inclusion.lean` and of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjoint.lean` record that the
remainder of Stacks 06Z0 "rests on unbounded affine vanishing, [Stacks, Tag 08D4]", which is
correct for the route the source takes. What this file adds is the reduction: the whole remainder
— the `RΓ(X, -)` edge of the triangle included, since two edges of a triangle of functors
determine the third — is the single statement
`(derivedQuasicoherentComparison (Spec R)).IsEquivalence`, with no `derivedTilde` in it. That
statement is proved in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`, along the route the
source takes for 06Z0: unbounded affine vanishing ([Stacks, Tag 08D4]) together with Serre
vanishing on an affine scheme ([Stacks, Tag 01XB]). The other route in the source is
[Stacks, Tag 08DB], the criterion for a quasi-compact scheme with affine diagonal, which rests on
the coherator ([Stacks, Tag 08D8]) and on [Stacks, Tag 08D7]; it is not formalized, and it is not
independent, since the source proves 08DB from 09T6 and 09T6 from [Stacks, Tag 08D9], which in
turn it proves from 06Z0.

**The `HasDerivedCategory` instance on `QCoh(𝒪_X)`.** `derivedQuasicoherentComparison` leaves its
two derived categories as instance arguments, and `AlgebraicGeometry.derivedTilde` is stated at the
locally small models `ModuleCat.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. To mention both in one statement a locally
small model for `D(QCoh(𝒪_X))` is needed, and the instance below supplies it: the quasi-coherent
modules on a scheme are Grothendieck abelian ([Stacks, Tag 077P]), so Tag 079Q applies. It is a
global instance for exactly the reason given in the implementation notes of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` — a Grothendieck abelian category has a
preferred derived category, and a comparison between `D(QCoh(𝒪_X))` and `D(𝒪_X)` is only usable
when both sides are taken at the locally small model.

**Two spellings of the module category.** `AlgebraicGeometry.tilde.functor` lands in
`(Spec R).Modules` while `CategoryTheory.ObjectProperty.ι` of
`AlgebraicGeometry.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf` lands in
`SheafOfModules (Spec R).ringCatSheaf`. The two are definitionally equal but carry separately
declared `Category`, `Abelian` and hence `Preadditive` instances, so `(tilde.functor R).Additive`
and the exactness instances are *different propositions* in the two views and instance search finds
only the first. `tildeSheafOfModules` is the type-ascribed laundering of the functor into the
second view, with its three exactness instances transported by `inferInstanceAs`; this is the same
device as `Stacks.DerivedQCoh.hasDerivedCategorySheafOfModules` in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/StructureSheafSpelling.lean`.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Stacks.DerivedQCoh

/-- The locally small derived category of the quasi-coherent `𝒪_X`-modules: the morphisms of
`D(QCoh(𝒪_X))` are in `Type u` and not merely in `Type (u + 1)`.

This is the companion of `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and of
`ModuleCat.hasDerivedCategory`, and is an instance for the same reason: the quasi-coherent modules
on a scheme are Grothendieck abelian, so they have a preferred derived category, and the
comparisons of [Stacks, Tag 06Z0] between `D(R)`, `D(QCoh(𝒪_X))` and `D(𝒪_X)` are only usable when
all three sides are taken at the locally small model. -/
instance hasDerivedCategoryQuasicoherent (X : Scheme.{u}) :
    HasDerivedCategory.{u} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

variable (R : CommRingCat.{u})

/-- The associated-sheaf functor `M ↦ M̃`, with its codomain spelled
`SheafOfModules (Spec R).ringCatSheaf` rather than `(Spec R).Modules`.

The two types are definitionally equal, but they carry separately declared `Preadditive`
instances, so additivity and exactness of `AlgebraicGeometry.tilde.functor` are statements about
the first view only. This ascription moves them to the second, which is the one in which the
inclusion of the quasi-coherent modules is stated. -/
def tildeSheafOfModules : ModuleCat.{u} R ⥤ SheafOfModules.{u} (Spec R).ringCatSheaf :=
  tilde.functor R

/-- `Stacks.DerivedQCoh.tildeSheafOfModules` is additive, being
`AlgebraicGeometry.tilde.functor`. -/
instance tildeSheafOfModules_additive : (tildeSheafOfModules R).Additive :=
  inferInstanceAs ((tilde.functor R).Additive)

/-- `Stacks.DerivedQCoh.tildeSheafOfModules` is left exact, the stalk of `M̃` at a prime being a
localization of `M` ([Stacks, Tag 01HV]). -/
instance tildeSheafOfModules_preservesFiniteLimits :
    PreservesFiniteLimits (tildeSheafOfModules R) :=
  inferInstanceAs (PreservesFiniteLimits (tilde.functor R))

/-- `Stacks.DerivedQCoh.tildeSheafOfModules` is right exact, being a left adjoint. -/
instance tildeSheafOfModules_preservesFiniteColimits :
    PreservesFiniteColimits (tildeSheafOfModules R) :=
  inferInstanceAs (PreservesFiniteColimits (tilde.functor R))

/-- **The `~` edge of Stacks 06Z0 followed by the comparison functor of Stacks 06VT is derived
sheafification.** The equivalence `D(R) ≌ D(QCoh(𝒪_{Spec R}))` of
`Stacks.DerivedQCoh.derivedTildeEquiv` composed with the comparison functor
`D(QCoh(𝒪_{Spec R})) ⥤ D_QCoh(𝒪_{Spec R})` of
`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison` is
`AlgebraicGeometry.derivedTilde`.

After the fully faithful inclusion `D_QCoh(𝒪_{Spec R}) ⥤ D(𝒪_{Spec R})` both sides are the derived
functor of `M ↦ M̃`: on the left because `tildeEquiv.functor` followed by the inclusion of the
quasi-coherent modules is `AlgebraicGeometry.tilde.functor` and the derived functor of a composite
of exact functors is the composite of the derived functors, on the right by
`AlgebraicGeometry.derivedTildeCompι`. -/
def derivedTildeEquivCompComparisonIso :
    (derivedTildeEquiv.{u, u} R).functor ⋙ derivedQuasicoherentComparison.{u} (Spec R) ≅
      derivedTilde R :=
  ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι.whiskeringRight
        (DerivedCategory (ModuleCat.{u} R))).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedQuasicoherentComparisonCompι.{u} (Spec R)) ≪≫
      Functor.mapDerivedCategoryCompIso
        (F := (tildeEquiv (R := R)).functor)
        (G := (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι)
        (H := tildeSheafOfModules R) (Iso.refl _) ≪≫
      (derivedTildeCompι R).symm)

/-- **The remaining content of Stacks 06Z0 for an affine scheme, in one statement.** Derived
sheafification `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence exactly when the comparison functor
`D(QCoh(𝒪_{Spec R})) ⥤ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06VT] is one.

Both implications are the transport of `Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso`
along the equivalence `Stacks.DerivedQCoh.derivedTildeEquiv`; neither direction uses any
cohomology. Neither side is proved here — that the comparison functor is an equivalence on an
affine scheme is the first assertion of [Stacks, Tag 08D9] part (3) — but both are proved in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`. -/
theorem derivedTilde_isEquivalence_iff_comparison :
    (derivedTilde R).IsEquivalence ↔
      (derivedQuasicoherentComparison.{u} (Spec R)).IsEquivalence := by
  have hEquiv : (derivedTildeEquiv.{u, u} R).functor.IsEquivalence :=
    (derivedTildeEquiv.{u, u} R).isEquivalence_functor
  have key := Functor.isEquivalence_iff_of_iso (derivedTildeEquivCompComparisonIso R)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key.mpr h
    exact Functor.isEquivalence_of_comp_left (derivedTildeEquiv.{u, u} R).functor _
  · have := h
    exact key.mp (Functor.isEquivalence_trans _ _)

/-- **Derived sheafification is an equivalence once the comparison functor of Stacks 06VT is.**
This is the direction of `Stacks.DerivedQCoh.derivedTilde_isEquivalence_iff_comparison` that the
affine duality statements consume: they take `(derivedTilde R).IsEquivalence` as a hypothesis, and
after this lemma that hypothesis is the first assertion of [Stacks, Tag 08D9] part (3) and nothing
else. That assertion is
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`, so the hypothesis is
unconditionally available; the unconditional form of the conclusion is
`AlgebraicGeometry.derivedTilde_isEquivalence`. -/
theorem derivedTilde_isEquivalence
    (h : (derivedQuasicoherentComparison.{u} (Spec R)).IsEquivalence) :
    (derivedTilde R).IsEquivalence :=
  (derivedTilde_isEquivalence_iff_comparison R).mpr h

end Stacks.DerivedQCoh

end
