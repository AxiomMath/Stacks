module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreTildeComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibresAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.Homology.RelativelyPerfect.Criterion
import all StacksFrontier.Homology.RelativelyPerfect.Criterion

/-!
# The fibrewise criterion on an affine scheme: the converse

Let `R → A` be a flat ring map of finite presentation, let `f : Spec A ⟶ Spec R` be the
associated morphism of affine schemes, and let `E = M̃^•` be the derived sheafification of a
complex `M^•` of `A`-modules which is pseudo-coherent as an object of `D(𝒪_{Spec A})`. If `E`
is locally bounded below and for every point `s` of `Spec R` the derived fibre
`L(X_s ⟶ X)^*E` is locally bounded below, then `E` is `Spec R`-perfect.

This is the implication (2) ⇒ (1) of Stacks 0GEH for a morphism of affine schemes.

## Main results

* `AlgebraicGeometry.isGE_mapDerivedCategory_iff`: an exact, additive, **faithful** functor both
  preserves and reflects boundedness below on derived categories.
* `AlgebraicGeometry.isGE_mapDerivedCategory_of_isGE`: exactness alone gives preservation.
* `AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_iff_exists_isGE`: on a quasi-compact
  ringed space, local boundedness below is boundedness below.
* `AlgebraicGeometry.isGE_derivedPullback`: derived pullback along a morphism of ringed spaces
  with exact pullback preserves boundedness below.
* `AlgebraicGeometry.AffinePerfectDescent.isGE_tildeObj_iff`: **the tilde dictionary for
  boundedness below.** `M̃^•` is bounded below in `D(𝒪_{Spec A})` exactly when `M^•` is bounded
  below in `D(A)`.
* `AlgebraicGeometry.AffinePerfectDescent.isGE_derivedPullback_fibre_iff`: **the fibre
  dictionary.** The geometric derived fibre `L(X_p ⟶ X)^*M̃^•` is bounded below exactly when the
  algebraic derived base change `M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))` is.
* `AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres`:
  **the implication (2) ⇒ (1) of Stacks 0GEH for a morphism of affine schemes and a sheafified
  complex.**
* `AlgebraicGeometry.AffinePerfectDescent.isPerfect_Q_single_self`: the free module of rank one
  in degree zero is a perfect complex.

## Implementation notes

**What the converse needs, and where it comes from.** The affine dictionary
`AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff` (Stacks 08E7 and
0DHY) turns condition (1) into relative perfection of `M^•` over `R`, and Stacks 0GHJ,
`PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow`, is already
available as a biconditional. The two remaining passages are dictionaries for *boundedness below*:

* from local boundedness below of `M̃^•` on `Spec A` to boundedness below of `M^•` in `D(A)`.
  `Spec A` is quasi-compact, so `RingedSpace.exists_isGE_of_isLocallyBoundedBelow` makes the
  local bound global, and then `isGE_tildeObj_iff` crosses the tilde functor: the associated
  sheaf functor is exact and **faithful** (`AlgebraicGeometry.tilde.fullyFaithfulFunctor`), and
  a faithful additive functor reflects zero objects, so it reflects the vanishing of cohomology
  sheaves in low degrees.
* from local boundedness below of the geometric derived fibre on
  `X_p = Spec A ×_{Spec R} Spec κ(p)` to boundedness below of `M^• ⊗_R^{\mathbf{L}} κ(p)`.
  `X_p` is affine, hence quasi-compact; the fibre identification
  `AlgebraicGeometry.AffinePerfectDescent.fibreSpecIso` is an isomorphism of schemes, and
  derived pullback along it is nothing but the degreewise pullback
  (`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory`, an
  isomorphism being an open immersion), hence exact, hence preserves boundedness below. The
  factorisation `fibreSpecIso.hom ≫ pullback.fst = Spec (A → A ⊗_R κ(p))` then lets Tag 0D5S
  (`Stacks.DerivedPullback.factorIso`) replace the geometric fibre by the affine one, which
  `derivedPullbackTildeObjIso` (Stacks 08DW) evaluates, and the tilde reflection finishes. The
  last step from `M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))` to `M^• ⊗_R^{\mathbf{L}} κ(p)` is
  `derivedFibreRestrictIso`, where flatness of `A` over `R` is spent, together with the
  reflection of boundedness below by restriction of scalars.

**Only exactness is needed in one direction.** `isGE_mapDerivedCategory_of_isGE` asks nothing of
faithfulness, which is why `isGE_derivedPullback` applies to both legs of `fibreSpecIso` and
`isGE_derivedPullback_fibre_iff` is a biconditional. It does **not** apply to
`Limits.pullback.fst (specMap R A) (fromSpecResidueField p)` itself: that projection is a base
change of `Spec κ(p) ⟶ Spec R`, its module pullback is not exact, and no instance for it is
synthesized. That is the precise sense in which the fibre identification, and not the
projection, carries the argument.

**The general case.** Stacks 0GEH for an arbitrary flat morphism `f : X ⟶ S` locally of finite
presentation and an arbitrary pseudo-coherent `E` is
`AlgebraicGeometry.isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres` in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres`. As in the source, it is
reduced to the affine case: both conditions are local on `X` and on `S`, and on an affine
scheme a pseudo-coherent object is a sheafified complex.

**A restated private lemma.** `isPerfect_Q_single_self` restates
`StacksDraft.Perfect.isPerfect_singleFunctor_obj`
(`StacksFrontier/Homology/DerivedCategory/Monoidal/Invertible.lean:165`), which is `private` and so
cannot be cited; its own file is a monoidal-structure file far outside this import closure.
De-privatizing it and deleting the restatement is a dedup target.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 15.85.9 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Lemma 36.22.5 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Lemma 20.38.3 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe d u

namespace AlgebraicGeometry

/-! ### Boundedness below across a functor -/

/-- Boundedness below depends only on the isomorphism class of an object. -/
theorem isGE_congr {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {E E' : DerivedCategory C} (e : E ≅ E') (N : ℤ) : E.IsGE N ↔ E'.IsGE N :=
  ⟨fun _ => DerivedCategory.TStructure.t.isGE_of_iso e N,
    fun _ => DerivedCategory.TStructure.t.isGE_of_iso e.symm N⟩

/-- **An exact additive functor preserves boundedness below.** Its cohomology commutes with the
functor, which carries zero objects to zero objects. Faithfulness is not needed. -/
theorem isGE_mapDerivedCategory_of_isGE {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (E : DerivedCategory A) (N : ℤ) (h : E.IsGE N) :
    (G.mapDerivedCategory.obj E).IsGE N := by
  rw [DerivedCategory.isGE_iff] at h ⊢
  intro i hi
  exact (isZero_homology_mapDerivedCategory_iff G E i).2 (Functor.map_isZero G (h i hi))

/-- **An exact additive faithful functor preserves and reflects boundedness below.** Boundedness
below is the vanishing of the cohomology objects in low degrees, cohomology commutes with the
functor, and a faithful additive functor reflects zero objects. -/
theorem isGE_mapDerivedCategory_iff {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Faithful]
    (E : DerivedCategory A) (N : ℤ) :
    (G.mapDerivedCategory.obj E).IsGE N ↔ E.IsGE N := by
  rw [DerivedCategory.isGE_iff, DerivedCategory.isGE_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  refine (isZero_homology_mapDerivedCategory_iff G E i).trans ?_
  exact ⟨fun h => isZero_of_faithful G h, fun h => Functor.map_isZero G h⟩

namespace RingedSpace

/-- **On a quasi-compact ringed space local boundedness below is boundedness below.** The
non-trivial direction is `AlgebraicGeometry.RingedSpace.exists_isGE_of_isLocallyBoundedBelow`;
conversely a global bound is witnessed on the open `⊤` at every point. -/
theorem isLocallyBoundedBelow_iff_exists_isGE (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X)) :
    IsLocallyBoundedBelow X E ↔ ∃ N : ℤ, E.IsGE N := by
  refine ⟨exists_isGE_of_isLocallyBoundedBelow X E, fun ⟨N, hN⟩ x => ⟨⊤, trivial, N, ?_⟩⟩
  intro i hi
  exact Functor.map_isZero _ ((DerivedCategory.isGE_iff E N).1 hN i hi)

end RingedSpace

/-- **Derived pullback along a morphism of ringed spaces with exact pullback preserves
boundedness below.** Nothing is derived: `Lf^*` is the degreewise `f^*` by Stacks 079W, and an
exact additive functor preserves boundedness below. -/
theorem isGE_derivedPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (N : ℤ) (h : K.IsGE N) :
    ((derivedPullback f).obj K).IsGE N :=
  (isGE_congr ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
      f).app K) N).2 (isGE_mapDerivedCategory_of_isGE (modulePullback f) K N h)

namespace AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

/-! ### The tilde dictionary for boundedness below -/

/-- The tilde functor `D(B) ⥤ D(𝒪_{Spec B})` preserves and reflects boundedness below. -/
private theorem isGE_mapDerivedCategory_tilde_iff (B : Type u) [CommRing B]
    (K : DerivedCategory (ModuleCat.{u} B)) (N : ℤ) :
    ((tilde.functor (CommRingCat.of B)).mapDerivedCategory.obj K).IsGE N ↔ K.IsGE N := by
  have : (tilde.functor (CommRingCat.of B) :
      ModuleCat.{u} B ⥤ OXMod.{u, u} (Spec (CommRingCat.of B)).toRingedSpace).Faithful :=
    tilde.fullyFaithfulFunctor.faithful
  exact isGE_mapDerivedCategory_iff _ K N

/-- **The tilde dictionary for boundedness below.** The derived sheafification `M̃^•` of a
complex of `A`-modules is bounded below in `D(𝒪_{Spec A})` exactly when `M^•` is bounded below in
`D(A)`.

The associated-sheaf functor is exact and faithful, so `isGE_mapDerivedCategory_iff` applies. -/
theorem isGE_tildeObj_iff (A : Type u) [CommRing A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : ℤ) :
    (tildeObj A M).IsGE N ↔ (DerivedCategory.Q.obj M).IsGE N :=
  (isGE_congr ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M) N).symm.trans
    (isGE_mapDerivedCategory_tilde_iff A _ N)

/-- **The first clause of condition (2) of Stacks 0GEH is boundedness below of the complex.**
`Spec A` is quasi-compact, so the local bounds of
`AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow` become one global bound, and the tilde
dictionary crosses to `D(A)`. -/
theorem isLocallyBoundedBelow_tildeObj_iff_exists_isGE (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace (tildeObj A M) ↔
      ∃ N : ℤ, (DerivedCategory.Q.obj M).IsGE N :=
  (RingedSpace.isLocallyBoundedBelow_iff_exists_isGE
    (Spec (CommRingCat.of A)).toRingedSpace _).trans
    (exists_congr fun N => isGE_tildeObj_iff A M N)

/-! ### The fibre dictionary for boundedness below -/

section Fibre

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Across the fibre identification the projection to `Spec A` is the spectrum of
`A → A ⊗_R κ(p)`; this is `fibreSpecIso_inv_fst` read on the other leg. -/
theorem fibreSpecIso_hom_fst (p : PrimeSpectrum R) :
    (fibreSpecIso R A p).hom ≫ Limits.pullback.fst (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p)
      = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))) := by
  rw [← fibreSpecIso_inv_fst R A p, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- `fibreSpecIso_hom_fst` read as an equation of morphisms of ringed spaces, which is the form
the composition formula for derived pullback consumes. -/
theorem fibreSpecIso_hom_fst_toShHom (p : PrimeSpectrum R) :
    (fibreSpecIso R A p).hom.toLRSHom.toShHom ≫
        (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom
      = (Spec.map (CommRingCat.ofHom
          (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)))).toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : Spec (CommRingCat.of (A ⊗[R] p.asIdeal.ResidueField)) ⟶
        Spec (CommRingCat.of A) => k.toLRSHom.toShHom) (fibreSpecIso_hom_fst R A p)

/-- **The fibre dictionary for boundedness below.** The geometric derived fibre
`L(X_p ⟶ X)^*M̃^•` on `X_p = Spec A ×_{Spec R} Spec κ(p)` is bounded below by `N` exactly when
the algebraic derived base change `M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))` is.

The fibre identification `fibreSpecIso` is an isomorphism of schemes, so derived pullback along
either of its legs is exact, hence preserves boundedness below; Tag 0D5S replaces the geometric
projection by `Spec (A → A ⊗_R κ(p))`, Stacks 08DW evaluates the derived pullback along that,
and the tilde dictionary crosses the last step. Nothing is assumed of `R → A`. -/
theorem isGE_derivedPullback_fibre_iff (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (p : PrimeSpectrum R) (N : ℤ) :
    ((derivedPullback (Limits.pullback.fst (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom).obj
          (tildeObj A M)).IsGE N ↔
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A (A ⊗[R] p.asIdeal.ResidueField))).functor.obj
          (DerivedCategory.Q.obj M)).IsGE N := by
  constructor
  · intro h
    refine (isGE_mapDerivedCategory_tilde_iff _ _ N).1 ?_
    refine (isGE_congr (derivedPullbackTildeObjIso
      (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) M (DerivedCategory.Q.obj M)
      (Iso.refl _)) N).1 ?_
    refine (isGE_congr ((Stacks.DerivedPullback.factorIso
      (fibreSpecIso R A p).hom.toLRSHom.toShHom
      (Limits.pullback.fst (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom
      _ (fibreSpecIso_hom_fst_toShHom R A p)).app (tildeObj A M)) N).1 ?_
    exact isGE_derivedPullback (fibreSpecIso R A p).hom.toLRSHom.toShHom _ N h
  · intro h
    refine (isGE_congr ((Stacks.DerivedPullback.factorIso
      (fibreSpecIso R A p).inv.toLRSHom.toShHom
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)))).toLRSHom.toShHom
      _ (fibreSpecIso_inv_fst_toShHom R A p)).app (tildeObj A M)) N).1 ?_
    refine isGE_derivedPullback (fibreSpecIso R A p).inv.toLRSHom.toShHom _ N ?_
    refine (isGE_congr (derivedPullbackTildeObjIso
      (algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) M (DerivedCategory.Q.obj M)
      (Iso.refl _)) N).2 ?_
    exact (isGE_mapDerivedCategory_tilde_iff _ _ N).2 h

section Algebraic

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The second clause of condition (2) of Stacks 0GEH is the fibre clause of Stacks 0GHJ.**
For `R → A` flat, the geometric derived fibre of `M̃^•` over a point `p` of `Spec R` is locally
bounded below exactly when `M^• ⊗_R^{\mathbf{L}} κ(p)` is bounded below.

`X_p` is affine, hence quasi-compact; `isGE_derivedPullback_fibre_iff` crosses to
`M^• ⊗_A^{\mathbf{L}} (A ⊗_R κ(p))`, and `derivedFibreRestrictIso` — where flatness is spent —
together with the reflection of boundedness below by restriction of scalars crosses to
`M^• ⊗_R^{\mathbf{L}} κ(p)`. -/
theorem isLocallyBoundedBelow_fibre_iff_exists_isGE [Module.Flat R A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum R) :
    RingedSpace.IsLocallyBoundedBelow
        (Limits.pullback (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toRingedSpace
        ((derivedPullback (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom).obj
            (tildeObj A M)) ↔
      ∃ N : ℤ, ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R p.asIdeal.ResidueField)).functor.obj
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj M))).IsGE N := by
  have key : ∀ N : ℤ,
      ((derivedPullback (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toLRSHom.toShHom).obj
            (tildeObj A M)).IsGE N ↔
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.asIdeal.ResidueField)).functor.obj
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
              (DerivedCategory.Q.obj M))).IsGE N := by
    intro N
    refine Iff.trans (isGE_derivedPullback_fibre_iff R A M p N) (Iff.trans ?_
      (isGE_congr (derivedFibreRestrictIso R A (DerivedCategory.Q.obj M) p) N).symm)
    exact (PseudoCoherence.isGE_restrictScalars_iff
      (algebraMap p.asIdeal.ResidueField (A ⊗[R] p.asIdeal.ResidueField)) _ N).symm
  exact (RingedSpace.isLocallyBoundedBelow_iff_exists_isGE (Limits.pullback (specMap R A)
    ((Spec (CommRingCat.of R)).fromSpecResidueField p)).toRingedSpace _).trans (exists_congr key)

/-! ### Stacks 0GEH for a morphism of affine schemes -/

/-- **Stacks 0GEH, the implication (2) ⇒ (1), for a morphism of affine schemes and a sheafified
complex.** Let `R → A` be flat of finite presentation, let `f : Spec A ⟶ Spec R` be the
associated morphism and let `M^•` be a complex of `A`-modules whose derived sheafification
`M̃^•` is a pseudo-coherent object of `D(𝒪_{Spec A})`. If `M̃^•` is locally bounded below and the
derived fibre `L(X_s ⟶ X)^*M̃^•` is locally bounded below for every point `s` of `Spec R`, then
`M̃^•` is `Spec R`-perfect.

Both hypotheses are converted to boundedness below in `D(A)` and `D(κ(p))` by
`isLocallyBoundedBelow_tildeObj_iff_exists_isGE` and
`isLocallyBoundedBelow_fibre_iff_exists_isGE`; the algebra result Stacks 0GHJ then gives
relative perfection of `M^•` over `R`, which the affine dictionary
`isPerfectRelativeTo_tildeObj_iff` turns into `Spec R`-perfectness of `M̃^•`. -/
theorem isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres [Module.Flat R A]
    [Algebra.FinitePresentation R A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hpc : RingedSpace.IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (tildeObj A M))
    (h1 : RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace
      (tildeObj A M))
    (h2 : ∀ s : Spec (CommRingCat.of R), RingedSpace.IsLocallyBoundedBelow
      (Limits.pullback (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toRingedSpace
      ((derivedPullback (Limits.pullback.fst (specMap R A)
        ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).obj
          (tildeObj A M))) :
    (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A M) := by
  refine (isPerfectRelativeTo_tildeObj_iff R A M).2 ?_
  refine (PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow
    (PseudoCoherence.canonicalDerivedTensoringDatum R).tensor
    (PseudoCoherence.canonicalDerivedTensoringDatum R).comparison
    (PseudoCoherence.canonicalDerivedTensoringDatum R).isLeftDerived
    (DerivedCategory.Q.obj M)
    ((RingedSpace.isPseudoCoherent_tilde_iff M).1 hpc)).2 ?_
  exact ⟨(isLocallyBoundedBelow_tildeObj_iff_exists_isGE A M).1 h1,
    fun p => (isLocallyBoundedBelow_fibre_iff_exists_isGE R A M p).1 (h2 p)⟩

/-! ### The free module of rank one -/

/-- **The free module of rank one, in degree zero, is a perfect complex of `A`-modules.** It is
its own bounded finite-projective representative.

This restates `StacksDraft.Perfect.isPerfect_singleFunctor_obj`
(`StacksFrontier/Homology/DerivedCategory/Monoidal/Invertible.lean:165`), which is `private`;
see the implementation notes. -/
theorem isPerfect_Q_single_self (B : Type u) [CommRing B] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) := by
  have h : ∀ i : ℤ,
      Module.Finite B
          (((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)).X i) ∧
        Module.Projective B
          (((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)).X i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B B)).toLinearEquiv
      exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
    · have : Subsingleton
          (((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of B B) i hi)
      exact ⟨inferInstance, Module.Projective.of_free⟩
  exact ⟨_, 0, 0, inferInstance, inferInstance, fun i => (h i).1, fun i => (h i).2,
    ⟨Iso.refl _⟩⟩

end Algebraic

end Fibre

end AffinePerfectDescent

end AlgebraicGeometry

end
