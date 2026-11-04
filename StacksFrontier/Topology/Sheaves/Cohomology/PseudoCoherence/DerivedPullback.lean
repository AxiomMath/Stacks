module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatumUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.PullbackOfApproximations
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.RestrictionIsPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullbackReduction
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 09U7: derived pullback preserves pseudo-coherence

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be an object of
`D(𝒪_Y)` which is `m`-pseudo-coherent.  Stacks 09U7 asserts that `Lf^* E` is
`m`-pseudo-coherent.

`StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullbackReduction` reduces
this to the complex level: granted that
degreewise pullback preserves `m`-pseudo-coherence of K-flat complexes, the derived statement
follows by replacing `E` by a K-flat representative.  This file supplies that complex-level
statement and so closes the tag.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex`: restriction to an
  open subspace preserves K-flatness.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentComplexFrom_modulePullback`:
  degreewise pullback preserves
  `m`-pseudo-coherence of a K-flat complex.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback`:
  **Stacks 09U7**, with no hypotheses.

## Implementation notes

`m`-pseudo-coherence is local on the base, so the proof is purely a matter of matching up the
two localisations.  A point `x` of `X` is tested by a neighbourhood `V` of `f(x)` on which `P`
admits a strictly perfect approximation `α : Q ⟶ P|_V` in degrees `> m`; the neighbourhood of
`x` is `f⁻¹(V)`, and the approximation there is the pullback of `α` along the restricted
morphism `f|_{f⁻¹(V)}`, followed by the identification of `(f^*P)|_{f⁻¹(V)}` with
`(f|_{f⁻¹(V)})^*(P|_V)`.  The three inputs are:
`Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback`
(the pullback of a strictly perfect complex is strictly perfect, Stacks 09U6),
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.homologyBounds_modulePullback` (degreewise
  pullback preserves an approximation
between K-flat complexes), and
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` (restriction
    commutes
with pullback).

`homologyBounds_modulePullback` needs both ends of the approximation K-flat.  For `Q` that is
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect`; for `P|_V` it is
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex`,
which is Stacks 06YC at the open immersion `j_V`, since restriction to an open subspace *is*
pullback along `j_V`
  (`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback`).

The spellings `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z`,
  `StrictlyPerfect.OXMod Z` and
`SheafOfModules (structureSheafRing Z)` are `rfl`-equal, as are
`StacksDraft.KFlat.modulePullback f` and `RingedSpaceModuleAdjunction.modulePullback f`, but
instance search does not cross them; every statement below is therefore written at one spelling
and the crossings happen in term-mode applications only.  The two `PreservesZeroMorphisms`
instances that `NatIso.mapHomologicalComplex` wants are passed positionally for the same reason,
as `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` already does.

## References

* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 09U6](https://stacks.math.columbia.edu/tag/09U6)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction Stacks.Cohomology.HigherDirectImage

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Composing an approximation with an isomorphism

The two statements below are the functoriality of `homologyMap` under composition with an
isomorphism, hoisted out of the proof of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentComplexFrom_modulePullback` and
  stated over an abstract abelian
category.  `rw [HomologicalComplex.homologyMap_comp]` does not fire on the goal in situ: there
the complexes are complexes of sheaves of modules, where the `HasHomology` instance arguments of
`homologyMap` are reached through two spellings of the structure sheaf and the rewrite's motive
check runs at `instances` transparency.  Over an abstract `A` the rewrite is immediate, and the
resulting statement is applied as a term. -/

section Abstract

variable {A : Type*} [Category A] [Abelian A]

/-- Composing with an isomorphism keeps invertibility of a homology map. -/
theorem isIso_homologyMap_comp_isIso {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (ψ : L ⟶ M)
    (i : ℤ) (hφ : IsIso (HomologicalComplex.homologyMap φ i)) (hψ : IsIso ψ) :
    IsIso (HomologicalComplex.homologyMap (φ ≫ ψ) i) := by
  have := hφ
  have := hψ
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Composing with an isomorphism keeps surjectivity of a homology map. -/
theorem epi_homologyMap_comp_isIso {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (ψ : L ⟶ M)
    (i : ℤ) (hφ : Epi (HomologicalComplex.homologyMap φ i)) (hψ : IsIso ψ) :
    Epi (HomologicalComplex.homologyMap (φ ≫ ψ) i) := by
  have := hφ
  have := hψ
  rw [HomologicalComplex.homologyMap_comp]
  exact epi_comp _ _

end Abstract

/-- **K-flatness transports along an isomorphism of complexes.**  This is
`CochainComplex.KFlatBifunctor.KFlat.of_iso` at the tensor product of a ringed space.  It is
recorded as its own theorem because the four instance arguments of that lemma are found for a
ringed space *variable* `Z` and not for a term such as
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictToOpen Y V`; stating
it here discharges them once, at `Z`. -/
theorem kFlat_of_iso {Z : RingedSpace.{u, u}} {K K' : CochainComplex (Modules Z) ℤ}
    (hK : KFlat Z K) (e : K ≅ K') : KFlat Z K' :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) hK e

/-- **Restriction to an open subspace preserves K-flatness.**  Restriction to `V` is pullback
along the open immersion `j_V : (V, 𝒪_Y|_V) ⟶ (Y, 𝒪_Y)`, by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback`, and the pullback
  of a K-flat complex is K-flat by
Stacks 06YC. -/
theorem kFlat_restrictComplex {Y : RingedSpace.{u, u}} (V : Opens Y.carrier)
    (P : CochainComplex (Modules Y) ℤ) (hP : KFlat Y P) :
    KFlat (restrictToOpen Y V) (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V)
      := by
  have hpull := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
    (openSubspaceInclusion Y V) P hP
  have e := (@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (moduleRestriction_additive Y V))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (modulePullback_additive (openSubspaceInclusion Y V)))
    (restrictModulesIsoPullback Y V) (ComplexShape.up ℤ)).symm.app P
  exact kFlat_of_iso (Z := restrictToOpen Y V) hpull e

/-- **Degreewise pullback preserves `m`-pseudo-coherence of a K-flat complex.**  This is the
complex level of Stacks 09U7, the statement
`isPseudoCoherentFrom_derivedPullback_of_complexLevel` takes as its hypothesis.

A point `x` of `X` is tested at `f(x)`: there is an open `V ∋ f(x)` of `Y`, a strictly perfect
complex `Q` on `V` and a map `α : Q ⟶ P|_V` which is invertible on cohomology in degrees `> m`
and surjective in degree `m`.  Then `f⁻¹(V)` is an open neighbourhood of `x`, and
`(f|_{f⁻¹(V)})^*Q` is strictly perfect by Stacks 09U6.  Both `Q` and `P|_V` are K-flat, so
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.homologyBounds_modulePullback` says
  `(f|_{f⁻¹(V)})^*α` has the same two cohomology
properties, and composing it with the canonical identification of `(f|_{f⁻¹(V)})^*(P|_V)` with
`(f^*P)|_{f⁻¹(V)}` — an isomorphism, so harmless on cohomology — gives the required
approximation of `(f^*P)|_{f⁻¹(V)}`. -/
theorem isPseudoCoherentComplexFrom_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Y) ℤ) (m : ℤ) (hP : KFlat Y P)
    (hpc : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := Y) P m) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := X)
      (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) m := by
  intro x
  obtain ⟨V, hxV, Q, hQ, α, hiso, hepi⟩ := hpc (f.hom.base x)
  obtain ⟨h₁, h₂⟩ := homologyBounds_modulePullback pullbackKFlatInput (restrictedMorphism f V)
    α m (kFlat_of_isStrictlyPerfect Q hQ) (kFlat_restrictComplex V P hP) hiso hepi
  let F := (modulePullback (restrictedMorphism f V)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hinv := Iso.isIso_inv (restrictComplexPullbackIso f V P)
  exact ⟨preimageOpen f V, hxV, F.obj Q,
    Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback (restrictedMorphism f V) Q hQ,
    F.map α ≫ (restrictComplexPullbackIso f V P).inv,
    fun j hj => isIso_homologyMap_comp_isIso _ _ j (h₁ j hj) hinv,
    epi_homologyMap_comp_isIso _ _ m h₂ hinv⟩

/-- **Stacks 09U7.**  The derived pullback of an `m`-pseudo-coherent object of `D(𝒪_Y)` along a
morphism of ringed spaces is `m`-pseudo-coherent.

`isPseudoCoherentFrom_derivedPullback_of_complexLevel` reduces this to the complex level, which is
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentComplexFrom_modulePullback`. -/
@[stacks 09U7]
theorem isPseudoCoherentFrom_derivedPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (E : DerivedCategory (OXMod.{u} Y)) (m : ℤ)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := Y) E m) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := X)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E) m :=
  isPseudoCoherentFrom_derivedPullback_of_complexLevel f E m hE
    fun P hP hpc => isPseudoCoherentComplexFrom_modulePullback f P m hP hpc

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
