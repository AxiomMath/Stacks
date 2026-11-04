module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange

/-!
# The derived fibre of a sheafified complex is an algebraic derived base change

Let `R → A` be a ring map, let `f : Spec A ⟶ Spec R` be the associated morphism of affine
schemes, let `M^•` be a complex of `A`-modules, and let `p` be a prime of `R`. The *geometric*
derived fibre of the sheafification `M̃^•` at `p` is the derived pullback of `M̃^•` along the
projection `X_p = Spec A ×_{Spec R} Spec κ(p) ⟶ Spec A`. This file identifies it with the
sheafification, on `Spec (A ⊗_R κ(p))`, of the *algebraic* derived base change
`M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))`.

## Main results

* `AlgebraicGeometry.AffinePerfectDescent.isPullback_specFibre`: `Spec (A ⊗_R κ(p))` is the fibre
  product `Spec A ×_{Spec R} Spec κ(p)`, in the spelling in which the second factor is
  `AlgebraicGeometry.Scheme.fromSpecResidueField` rather than the spectrum of a ring map.
* `AlgebraicGeometry.AffinePerfectDescent.derivedFibreTildeIso`: the geometric derived fibre of
  `M̃^•` is the sheafification of `M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))`, read across the fibre
  identification. No hypothesis on `R → A`.
* `AlgebraicGeometry.AffinePerfectDescent.derivedFibreRestrictIso`: for `R → A` flat, the
  complex `K ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))` read over `κ(p)` is `K ⊗_R^{\mathbf{L}} κ(p)`, the
  derived fibre that Stacks 0GHJ is stated at.

## Implementation notes

**Why the comparison is two declarations and not one.** The geometric derived fibre lives on
`X_p = Spec A ×_{Spec R} Spec κ(p)`, so the complex it is compared with has to be a complex of
`A ⊗_R κ(p)`-modules; that is `derivedFibreTildeIso`, and it needs nothing of `R → A`. The
derived fibre appearing in Stacks 0GHJ,
`PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow`, is instead
`K ⊗_R^{\mathbf{L}} κ(p)`, a complex of `κ(p)`-modules. The two are related by restriction of
scalars along `κ(p) → A ⊗_R κ(p)`, and *that* step is where flatness of `A` over `R` is spent:
for a general `R → A` the underived `A ⊗_R κ(p)` is not `A ⊗_R^{\mathbf{L}} κ(p)` and the
identification is false. So the passage is isolated in `derivedFibreRestrictIso`, which carries
the flatness hypothesis and nothing else does. Composing the two in one statement is not
possible: a complex of `κ(p)`-modules cannot be sheafified on `X_p`.

**The fibre identification.** `isPullback_specFibre` is Mathlib's
`AlgebraicGeometry.pullbackSpecIso` with the second leg converted from `Spec` of
`algebraMap R κ(p)` to `AlgebraicGeometry.Scheme.fromSpecResidueField`, which is the spelling
condition (2) of Stacks 0GEH is stated at. Mathlib's
`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso` is the same conversion, but packaged as an
isomorphism of *arrows down to the residue field*, so it determines the second projection and
says nothing about the first; the derived pullback of condition (2) is taken along the first
projection, so the cartesian square is recorded here instead and both legs come from
`CategoryTheory.IsPullback.isoPullback_inv_fst`.

**The algebraic half.** `derivedFibreRestrictIso` is Stacks 065Z,
`RingTheory.TorIndependence.derivedBaseChangeComparison`, inverted by Stacks 0661; it is the
same move `PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect` (Stacks 0DHW) makes, at
`R' = κ(p)`. Its statement mentions `algebraMap κ(p) (A ⊗_R κ(p))`, which needs
`Algebra.TensorProduct.rightAlgebra`; that is not a global instance, so a consumer has to enable
it locally, exactly as Stacks 0DHW does.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 15.85.9 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
* [Stacks Project, Lemma 36.22.5 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Lemma 20.38.3 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Lemma 15.61.2 (Tag 065Z)](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Lemma 15.61.4 (Tag 0661)](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open StrictlyPerfect RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **`Spec (A ⊗_R κ(p))` is the fibre of `Spec A ⟶ Spec R` over `p`.** The square whose two
other legs are the structure morphism `Spec A ⟶ Spec R` and the canonical
`Spec κ(p) ⟶ Spec R` of `AlgebraicGeometry.Scheme.fromSpecResidueField` is cartesian.

Mathlib's `AlgebraicGeometry.pullbackSpecIso` is the same statement with the second leg spelled
as the spectrum of `algebraMap R κ(p)`; the two legs differ by the isomorphism
`AlgebraicGeometry.Scheme.Spec.residueFieldIso` between the residue field of the local ring of
`Spec R` at `p` and `Ideal.ResidueField p`, which is how
`AlgebraicGeometry.Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` relates them. -/
theorem isPullback_specFibre (p : PrimeSpectrum R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))))
      (Spec.map ((Scheme.Spec.residueFieldIso (CommRingCat.of R) p).hom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A)
          (B := p.asIdeal.ResidueField)).toRingHom))
      (specMap R A) ((Spec (CommRingCat.of R)).fromSpecResidueField p) := by
  have hw : Spec.map (CommRingCat.ofHom
        (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))) ≫ specMap R A =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A)
          (B := p.asIdeal.ResidueField)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) := by
    simp only [AlgHom.toRingHom_eq_coe]
    rw [← pullbackSpecIso_inv_fst' R A p.asIdeal.ResidueField,
      ← pullbackSpecIso_inv_snd R A p.asIdeal.ResidueField]
    simp only [Category.assoc, pullback.condition]
  refine (IsPullback.of_iso_pullback ⟨hw⟩ (pullbackSpecIso R A p.asIdeal.ResidueField).symm
    (pullbackSpecIso_inv_fst' R A p.asIdeal.ResidueField)
    (pullbackSpecIso_inv_snd R A p.asIdeal.ResidueField)).of_iso' (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv)) (Iso.refl _)
    (by simp) ?_ (by simp) ?_
  · simp [← Spec.map_comp]
  · simpa using Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
      (CommRingCat.of R) p

/-- **The fibre identification**: `Spec (A ⊗_R κ(p)) ≅ Spec A ×_{Spec R} Spec κ(p)`. -/
def fibreSpecIso (p : PrimeSpectrum R) :
    Spec (CommRingCat.of (A ⊗[R] p.asIdeal.ResidueField)) ≅
      Limits.pullback (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p) :=
  (isPullback_specFibre R A p).isoPullback

/-- Across the fibre identification the projection to `Spec A` is the spectrum of
`A → A ⊗_R κ(p)`. -/
theorem fibreSpecIso_inv_fst (p : PrimeSpectrum R) :
    (fibreSpecIso R A p).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)))
      = Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p) :=
  (isPullback_specFibre R A p).isoPullback_inv_fst

/-- `fibreSpecIso_inv_fst` read as an equation of morphisms of ringed spaces, which is the form
the composition formula for derived pullback consumes. -/
theorem fibreSpecIso_inv_fst_toShHom (p : PrimeSpectrum R) :
    (fibreSpecIso R A p).inv.toLRSHom.toShHom ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)))).toLRSHom.toShHom
      = (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : Limits.pullback (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p) ⟶ Spec (CommRingCat.of A) =>
      k.toLRSHom.toShHom) (fibreSpecIso_inv_fst R A p)

/-- **The geometric derived fibre of a sheafified complex is an algebraic derived base change.**
The derived pullback of `M̃^•` along the projection `Spec A ×_{Spec R} Spec κ(p) ⟶ Spec A` is,
across the fibre identification `fibreSpecIso`, the derived sheafification on
`Spec (A ⊗_R κ(p))` of the derived base change
`M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))`.

Nothing is assumed of `R → A`: the projection factors as the fibre identification followed by
the spectrum of `A → A ⊗_R κ(p)` (`fibreSpecIso_inv_fst`), the unconditional composition formula
for derived pullback, Stacks 0D5S, splits the derived pullback accordingly, and the affine
comparison square of Stacks 08DW, `derivedPullbackTildeObjIso`, evaluates the inner factor. -/
def derivedFibreTildeIso (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum R) :
    (derivedPullback (Limits.pullback.fst (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom).obj
        (tildeObj A M) ≅
      (derivedPullback (fibreSpecIso R A p).inv.toLRSHom.toShHom).obj
        ((tilde.functor (CommRingCat.of (A ⊗[R] p.asIdeal.ResidueField))).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))).functor.obj
              (DerivedCategory.Q.obj M))) :=
  eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj (tildeObj A M))
      (fibreSpecIso_inv_fst_toShHom R A p).symm) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (fibreSpecIso R A p).inv.toLRSHom.toShHom
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)))).toLRSHom.toShHom).app
      (tildeObj A M)).symm ≪≫
    (derivedPullback (fibreSpecIso R A p).inv.toLRSHom.toShHom).mapIso
      (derivedPullbackTildeObjIso (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) M
        (DerivedCategory.Q.obj M) (Iso.refl _))

section Algebraic

attribute [local instance] Algebra.TensorProduct.rightAlgebra

attribute [local implicit_reducible]
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex

/-- **The derived base change of `M^•` to `A ⊗_R κ(p)`, read over `κ(p)`, is its derived base
change over `R` to `κ(p)`.** For `R → A` flat and `K` an object of `D(A)`, restricting
`K ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))` to `κ(p)` gives `K ⊗_R^{\mathbf{L}} κ(p)`, where `K` is read
over `R` by restriction of scalars.

This is Stacks 065Z, `RingTheory.TorIndependence.derivedBaseChangeComparison`, at the base change
square of `R → A` along `R → κ(p)`, inverted by Stacks 0661,
`RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent`. Flatness of `A`
over `R` enters only through the Tor independence of `A` and `κ(p)` over `R`, which is
`PseudoCoherence.torIndependent_of_flat`; it is what makes `A ⊗_R κ(p)` the *derived* base change
of `A` and so is not removable. -/
def derivedFibreRestrictIso [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))
    (p : PrimeSpectrum R) :
    (totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.asIdeal.ResidueField)).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ≅
      (ModuleCat.restrictScalars (algebraMap p.asIdeal.ResidueField
          (A ⊗[R] p.asIdeal.ResidueField))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))).functor.obj K) :=
  letI Tg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.asIdeal.ResidueField)
  letI Th := totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))
  letI cmp := (RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u,
      u + 1, u + 1, u + 1, u + 1} (algebraMap R A) (algebraMap R p.asIdeal.ResidueField)
      (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))
      (algebraMap p.asIdeal.ResidueField (A ⊗[R] p.asIdeal.ResidueField))
      ((IsScalarTower.algebraMap_eq R A (A ⊗[R] p.asIdeal.ResidueField)).symm.trans
        (IsScalarTower.algebraMap_eq R p.asIdeal.ResidueField
          (A ⊗[R] p.asIdeal.ResidueField)))
      Tg.functor Th.functor Tg.comparison Th.comparison).2.1
  haveI : IsIso cmp :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u,
        u + 1, u + 1, u + 1, u + 1} (R := R) (A := A) (R' := p.asIdeal.ResidueField)
      (A' := A ⊗[R] p.asIdeal.ResidueField) PseudoCoherence.torIndependent_of_flat
      Tg.functor Th.functor Tg.comparison Th.comparison
  asIso (cmp.app K)

end Algebraic

end AlgebraicGeometry.AffinePerfectDescent

end
