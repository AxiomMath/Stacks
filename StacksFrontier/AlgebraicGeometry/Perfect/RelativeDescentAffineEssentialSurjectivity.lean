module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulated
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom

/-!
# The affine case of the essential-surjectivity half of Stacks 0DI8

In the relative descent situation of Stacks 0DI6 — a directed inverse limit `S = lim Sᵢ` of
quasi-compact, quasi-separated schemes with affine transition maps, and a flat morphism of finite
presentation `X₀ ⟶ S₀` with base changes `Xᵢ ⟶ Sᵢ` and `X ⟶ S` — Stacks 0DI8 asserts that the
category of `S`-perfect objects of `D(𝒪_X)` is the colimit of the categories of `Sᵢ`-perfect
objects of `D(𝒪_{Xᵢ})`. Full faithfulness of the comparison is Stacks 0DI7, which the source
cites as known; what remains is essential surjectivity, that every `S`-perfect object of `D(𝒪_X)`
is the derived pullback `Lfᵢ^*Eᵢ` of an `Sᵢ`-perfect object at some stage `i`.

This file proves that in the affine case. The situation is taken in the form the ring-theoretic
Stacks 0DHX consumes: a filtered diagram `i ↦ Rᵢ` of `R₀`-algebras with colimit `R`, and a flat
`R₀`-algebra `A₀` of finite presentation, so that `Sᵢ = Spec Rᵢ`, `S = Spec R`, `X₀ = Spec A₀`,
`Xᵢ = Spec(Rᵢ ⊗_{R₀} A₀)` and `X = Spec(R ⊗_{R₀} A₀)`, and the structure morphisms are the
spectra of the ring maps. Over such a system the whole statement becomes algebra: an `S`-perfect
object of `D(𝒪_X)` has quasi-coherent cohomology by Stacks 08E5, hence is the derived
sheafification of an object of `D(R ⊗_{R₀} A₀)` by Stacks 06Z0; that object is perfect relative
to `R` in the sense of Stacks 0DHS by the affine dictionary below; Stacks 0DHX descends it to a
stage; and the affine comparison square of Stacks 08DW turns its derived extension of scalars
back into the derived pullback of its sheafification.

The affine dictionary — relative perfectness of a sheaf on `Spec A` over `Spec R` versus relative
perfectness of the corresponding complex of `A`-modules over `R` — rests on the
certificate-versus-canonical comparison of
`StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate`.

## Main definitions

* `AlgebraicGeometry.AffinePerfectDescent.tildeObj`: derived sheafification of a complex of
  `A`-modules, read in the `StrictlyPerfect.OXMod` spelling of `D(𝒪_{Spec A})` that relative
  perfectness of Stacks 0DI0 is stated at.
* `AlgebraicGeometry.AffinePerfectDescent.derivedScalarRestrictionTildeIso`: that object, read
  over `f^{-1}𝒪_{Spec R}`, is the complex of Stacks 0DHY.
* `AlgebraicGeometry.AffinePerfectDescent.derivedPullbackTildeObjIso`: the affine comparison
  square of Stacks 08DW read at an object of `D(B)` presented by a complex.

## Main results

* `AlgebraicGeometry.AffinePerfectDescent.relativeComplex_eq`: the complex of
  `f^{-1}𝒪_{Spec R}`-modules of Stacks 0DHY is termwise restriction of scalars of the
  sheafification, which is what makes `derivedScalarRestrictionTildeIso` typecheck.
* `AlgebraicGeometry.AffinePerfectDescent.locallyHasFiniteTorDimension_tildeObj_iff`: the
  Tor-dimension clause of Stacks 0DI0 for a sheafification on `Spec A`, at the canonical
  certificate family, is finite Tor dimension of the complex over `R`. This is Stacks 0DHY
  crossed with the certificate spelling.
* `AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff`: **the affine
  dictionary.** For a flat ring map `R → A` of finite presentation, the sheafification of `M^•`
  is `Spec R`-perfect exactly when `M^•` is perfect relative to `R`.
* `AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage`: **the affine case of
  the essential-surjectivity half of Stacks 0DI8**, for a filtered system of spectra of rings.

## Implementation notes

**The presentation of the situation.** The situation is the system of rings itself, every
scheme in it being a literal `AlgebraicGeometry.Spec` and every structure morphism a literal
`AlgebraicGeometry.Spec.map`, which is the form in which Stacks 0DHY,
`AlgebraicGeometry.AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_relativeComplex_iff`,
is stated. The affine case of a general Situation 0DI6 is deduced from it in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentPerfectAffineCase.lean`, through the
isomorphisms of the stages with the spectra of the algebras of Stacks 0DHX and the transport of
relative perfectness across isomorphisms of arrows of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectArrowIso.lean`.

**The hypotheses.** Only the data of the ring-level situation: the filtered diagram, the cocone
and its colimit property in the form Stacks 0DHX consumes, and flatness and finite presentation
of `R₀ → A₀`. Relative perfectness is read at
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` on both sides;
quasi-coherence of the cohomology sheaves of the given object, which Stacks 06Z0 needs, is
derived from its pseudo-coherence by Stacks 08E5.

**The Tor-dimension clause.** `locallyHasFiniteTorDimension_tildeObj_iff` passes from the
certificate-carrying `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` of Stacks 0DI0
to the pinned `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` at which Stacks
0DHY is stated, by
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`.

**Universes and the derived-category model.** Everything is at
`CategoryTheory.HasDerivedCategory.standard`, installed with priority `10000` as the
implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` require: the
import closure carries *global* locally small instances, which beat a default-priority local
attribute. The index category, its morphisms and the rings are all in one universe `u`, because
`PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor`, the only route to the colimit
hypothesis of Stacks 0DHX, has all three equal, and because the canonical derived tensor product
of Stacks 0BYI is a bifunctor on `D(ModuleCat.{u} R)` for `R : Type u`.

**A dedup target.** `locallyOfFinitePresentation_specMap` duplicates
`AlgebraicGeometry.locallyOfFinitePresentation_specMap` of
`StacksFrontier/AlgebraicGeometry/Smooth/SmoothLocusAffine.lean`, which is not in this file's import
closure.

**No `@[stacks]` attribute on the dictionary.** `isPerfectRelativeTo_tildeObj_iff` is Stacks 08E7
and Stacks 0DHY read together through the certificate comparison; neither tag states it, and both
are registered elsewhere.

## References

* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DHS](https://stacks.math.columbia.edu/tag/0DHS)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Lemma 36.10.5 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry StrictlyPerfect RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- `Spec` of a flat algebra is a flat morphism. -/
instance flat_specMap [Module.Flat R A] : Flat (specMap R A) :=
  (Flat.SpecMap_iff).2 (RingHom.flat_algebraMap_iff.2 inferInstance)

/-- `Spec` of an algebra of finite presentation is locally of finite presentation. -/
instance locallyOfFinitePresentation_specMap [Algebra.FinitePresentation R A] :
    LocallyOfFinitePresentation (specMap R A) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).2
    (RingHom.finitePresentation_algebraMap.2 inferInstance)

/-- Derived sheafification of a complex of `A`-modules, as an object of `D(𝒪_{Spec A})` in the
`OXMod` spelling that relative perfectness is stated at. -/
abbrev tildeObj (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace) :=
  DerivedCategory.Q.obj
    (((tilde.functor (CommRingCat.of A) :
        ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)

/-- **The complex of `f^{-1}𝒪_{Spec R}`-modules of Stacks 0DHY is termwise restriction of
scalars of the sheafification.** Both sides are the composite of `tilde.functor` with
`SheafOfModules.restrictScalars` along the adjoint `f^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` of the
structure-sheaf datum, applied degreewise, so they are equal. -/
theorem relativeComplex_eq (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    relativeComplex R A M =
      ((Scheme.Hom.scalarRestriction (specMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((tilde.functor (CommRingCat.of A) :
            ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := rfl

/-- Derived restriction of scalars along `f⁻¹𝒪_{Spec R} ⟶ 𝒪_{Spec A}` carries the derived
sheafification of `M^•` to the complex of `f⁻¹𝒪_{Spec R}`-modules of Stacks 0DHY. -/
def derivedScalarRestrictionTildeIso (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (Scheme.Hom.derivedScalarRestriction (specMap R A)).obj (tildeObj A M) ≅
      DerivedCategory.Q.obj (relativeComplex R A M) :=
  (Scheme.Hom.derivedScalarRestrictionFactors (specMap R A)).app _

section Pinned

open Stacks.Cohomology.TorAmplitude

variable {Y : RingedSpace.{u, u}}

/-- Tor amplitude at the derived tensor product of Stacks 06YU depends only on the isomorphism
class of the object: the predicate is the vanishing of the cohomology of a functor of it. -/
private theorem hasTorAmplitude_pinned_of_iso
    {E E' : DerivedCategory (OXMod.{u, u} Y)} (e : E ≅ E') {a b : ℤ}
    (h : HasTorAmplitude Y E a b) : HasTorAmplitude Y E' a b := fun F i hi =>
  (h F i hi).of_iso ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).mapIso
    (((derTensor Y).tensor.mapIso e).symm.app _))

/-- Locally finite Tor dimension at the derived tensor product of Stacks 06YU depends only on
the isomorphism class of the object: the same open covering serves, and restriction to an open is
a functor. -/
private theorem locallyHasFiniteTorDimension_pinned_of_iso
    {E E' : DerivedCategory (OXMod.{u, u} Y)} (e : E ≅ E')
    (h : LocallyHasFiniteTorDimension Y E) : LocallyHasFiniteTorDimension Y E' := by
  obtain ⟨J, U, hU, hfin⟩ := h
  refine ⟨J, U, hU, fun i => ?_⟩
  obtain ⟨a, b, hab⟩ := hfin i
  exact ⟨a, b, hasTorAmplitude_pinned_of_iso
    ((RingedSpace.PseudoCoherence.restrictModules Y (U i)).mapDerivedCategory.mapIso e) hab⟩

/-- Finite Tor dimension over a ring, at the canonical derived tensor product of Stacks 0BYI,
is invariant under isomorphism of objects of `D(S)`. -/
theorem hasFiniteTorDimensionCanonical_iff_of_iso {S : Type u} [CommRing S]
    {K K' : DerivedCategory (ModuleCat.{u} S)} (e : K ≅ K') :
    HasFiniteTorDimensionCanonical S K ↔ HasFiniteTorDimensionCanonical S K' := by
  rw [hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical,
    hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical]
  exact ⟨fun ⟨a, b, hab⟩ =>
      ⟨a, b, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b hab⟩,
    fun ⟨a, b, hab⟩ =>
      ⟨a, b, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b hab⟩⟩

end Pinned

/-- **The Tor-dimension clause of relative perfectness, read on an affine scheme.** The derived
sheafification of a complex `M^•` of `A`-modules locally has finite Tor dimension over
`f⁻¹𝒪_{Spec R}`, at the canonical certificate family, exactly when `M^•` read over `R` has finite
Tor dimension. -/
theorem locallyHasFiniteTorDimension_tildeObj_iff (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    RingedSpace.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((Scheme.Hom.derivedScalarRestriction (specMap R A)).obj (tildeObj A M)) ↔
      HasFiniteTorDimensionCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) := by
  refine Iff.trans (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff _ _) ?_
  refine Iff.trans ⟨fun h => locallyHasFiniteTorDimension_pinned_of_iso
      (derivedScalarRestrictionTildeIso R A M) h,
    fun h => locallyHasFiniteTorDimension_pinned_of_iso
      (derivedScalarRestrictionTildeIso R A M).symm h⟩ ?_
  exact locallyHasFiniteTorDimension_relativeComplex_iff R A M

/-- **The affine dictionary for relative perfectness.** For a flat ring map `R → A` of finite
presentation, the derived sheafification of a complex `M^•` of `A`-modules is an `Spec R`-perfect
object of `D(𝒪_{Spec A})`, at the canonical certificate family, exactly when `M^•` is perfect
relative to `R` in the sense of Stacks 0DHS.

The pseudo-coherence clauses agree by Stacks 08E7 and the Tor-dimension clauses by
`locallyHasFiniteTorDimension_tildeObj_iff`, which is Stacks 0DHY read at the canonical
certificate. -/
theorem isPerfectRelativeTo_tildeObj_iff [Module.Flat R A] [Algebra.FinitePresentation R A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (specMap R A).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A M) ↔
      PseudoCoherence.IsRelativelyPerfect.{u, u, u}
        (PseudoCoherence.canonicalDerivedTensoringDatum R).tensor
        (PseudoCoherence.canonicalDerivedTensoringDatum R).comparison
        (PseudoCoherence.canonicalDerivedTensoringDatum R).isLeftDerived
        (DerivedCategory.Q.obj M) := by
  have hpc := RingedSpace.isPseudoCoherent_tilde_iff M
  have htor := locallyHasFiniteTorDimension_tildeObj_iff R A M
  have hres : ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj M)) ≅ DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) :=
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app M
  have hdatum := PseudoCoherence.hasFiniteTorDimension_canonicalDerivedTensoringDatum_iff R
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj M))
  refine and_congr hpc (htor.trans (Iff.trans ?_ hdatum.symm))
  exact (hasFiniteTorDimensionCanonical_iff_of_iso hres).symm

/-- Relative perfectness of a complex of modules depends only on its isomorphism class in
`D(A)`. -/
private theorem isRelativelyPerfect_of_iso [Module.Flat R A] [Algebra.FinitePresentation R A]
    {dT : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R)}
    {cmp : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ dT.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q}
    {ild : ∀ N : ModuleCat.{u} R,
      (dT.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)
        ).IsLeftDerivedFunctor (cmp N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))}
    {K K' : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ K')
    (h : PseudoCoherence.IsRelativelyPerfect.{u, u, u} dT cmp ild K) :
    PseudoCoherence.IsRelativelyPerfect.{u, u, u} dT cmp ild K' :=
  ⟨h.1.ofIso e, (hasFiniteTorDimension_iff_hasFiniteTorDimensionCanonical cmp ild _).2
    ((hasFiniteTorDimensionCanonical_iff_of_iso
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.mapIso e)).1
      ((hasFiniteTorDimension_iff_hasFiniteTorDimensionCanonical cmp ild _).1 h.2))⟩

section AffineComparison

variable {B C : Type u} [CommRing B] [CommRing C] (φ : B →+* C)

/-- **The affine comparison square of Stacks 08DW at the level of objects.** The derived pullback
along `Spec φ` of the derived sheafification of a complex `M^•` of `B`-modules is the derived
sheafification of the derived extension of scalars along `φ` of any object of `D(B)` isomorphic
to `M^•`. -/
def derivedPullbackTildeObjIso (Mi : CochainComplex (ModuleCat.{u} B) ℤ)
    (Ki : DerivedCategory (ModuleCat.{u} B)) (eMi : DerivedCategory.Q.obj Mi ≅ Ki) :
    (derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj (tildeObj B Mi) ≅
      (tilde.functor (CommRingCat.of C)).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj Ki) :=
  (StandardModel.specDerivedPullback (CommRingCat.ofHom φ)).mapIso
      (((tilde.functor (CommRingCat.of B)).mapDerivedCategoryFactors.app Mi).symm ≪≫
        (tilde.functor (CommRingCat.of B)).mapDerivedCategory.mapIso eMi) ≪≫
    (StandardModel.affinePullbackComparison (CommRingCat.of B) (CommRingCat.of C)
      (CommRingCat.ofHom φ)).app Ki

end AffineComparison

section Descent

variable {R₀ : Type u} [CommRing R₀] {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommAlgCat.{u} R₀) (c : Cocone F)
  (hc : IsColimit ((CommAlgCat.uliftFunctor.{u, u, u} R₀).mapCocone c))
  (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀]

include hc in
/-- **The affine case of the essential-surjectivity half of Stacks 0DI8.** Let `R₀` be a ring,
let `i ↦ Rᵢ` be a filtered diagram of `R₀`-algebras with colimit `R`, and let `A₀` be a flat
`R₀`-algebra of finite presentation. Put `A = R ⊗_{R₀} A₀` and `Aᵢ = Rᵢ ⊗_{R₀} A₀`. Then every
object of `D(𝒪_{Spec A})` perfect relative to `Spec R` is, for some stage `i`, the derived
pullback along `Spec(Aᵢ → A)` of an object of `D(𝒪_{Spec Aᵢ})` perfect relative to `Spec Rᵢ`.

Relative perfectness is Stacks 0DI0 at the canonical certificate family on both sides. The
object has quasi-coherent cohomology by Stacks 08E5, so Stacks 06Z0 presents it as the derived
sheafification of a complex of `A`-modules; `isPerfectRelativeTo_tildeObj_iff` makes that complex
perfect relative to `R`; Stacks 0DHX descends it to a stage; and `derivedPullbackTildeObjIso`,
the affine comparison square of Stacks 08DW, identifies the derived pullback of the
sheafification at that stage with the sheafification of the derived extension of scalars.

Stacks 0DI8 itself is
`AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_colimit`. -/
@[stacks 0DI8 "essential surjectivity only, and only in the affine case of the filtered system \
of rings of Stacks 0DHX. Full faithfulness (Stacks 0DI7) is not reproved, and nothing is proved \
for a general Situation 0DI6; see the implementation notes."]
theorem exists_isPerfectRelativeTo_stage
    (E : DerivedCategory (OXMod.{u, u}
      (Spec (CommRingCat.of (c.pt ⊗[R₀] A₀))).toRingedSpace))
    (hE : (specMap c.pt (c.pt ⊗[R₀] A₀)).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    ∃ (i : I) (Ei : DerivedCategory (OXMod.{u, u}
        (Spec (CommRingCat.of (PseudoCoherence.stageAlgebra F A₀ i))).toRingedSpace)),
      (specMap (F.obj i) (PseudoCoherence.stageAlgebra F A₀ i)).IsPerfectRelativeTo
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) Ei ∧
        Nonempty ((derivedPullback (Spec.map (CommRingCat.ofHom
          (PseudoCoherence.stageToLimitMap c A₀ i))).toLRSHom.toShHom).obj Ei ≅ E) := by
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of (c.pt ⊗[R₀] A₀))).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent
      (Spec (CommRingCat.of (c.pt ⊗[R₀] A₀))) E hE.1
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory
    (CommRingCat.of (c.pt ⊗[R₀] A₀)) E hqc
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q
      (C := ModuleCat.{u} (c.pt ⊗[R₀] A₀))).essImage K :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  have eE : tildeObj (c.pt ⊗[R₀] A₀) M ≅ E :=
    ((tilde.functor (CommRingCat.of (c.pt ⊗[R₀] A₀))).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor (CommRingCat.of (c.pt ⊗[R₀] A₀))).mapDerivedCategory.mapIso eM ≪≫ eK
  have := Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo
    (specMap c.pt (c.pt ⊗[R₀] A₀))
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
  have hEtilde := (Scheme.Hom.isPerfectRelativeTo (specMap c.pt (c.pt ⊗[R₀] A₀))
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)).prop_of_iso eE.symm hE
  obtain ⟨i, Ki, hKi, ⟨eKi⟩⟩ := PseudoCoherence.exists_relativelyPerfect_stage F c hc A₀
    (DerivedCategory.Q.obj M)
    ((isPerfectRelativeTo_tildeObj_iff c.pt (c.pt ⊗[R₀] A₀) M).1 hEtilde)
  obtain ⟨Mi, ⟨eMi⟩⟩ : (DerivedCategory.Q
      (C := ModuleCat.{u} (PseudoCoherence.stageAlgebra F A₀ i))).essImage Ki :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) Ki
  refine ⟨i, tildeObj (PseudoCoherence.stageAlgebra F A₀ i) Mi, ?_, ⟨?_⟩⟩
  · exact (isPerfectRelativeTo_tildeObj_iff (F.obj i)
      (PseudoCoherence.stageAlgebra F A₀ i) Mi).2
      (isRelativelyPerfect_of_iso (F.obj i) (PseudoCoherence.stageAlgebra F A₀ i) eMi.symm hKi)
  · exact derivedPullbackTildeObjIso (PseudoCoherence.stageToLimitMap c A₀ i) Mi Ki eMi ≪≫
      (tilde.functor (CommRingCat.of (c.pt ⊗[R₀] A₀))).mapDerivedCategory.mapIso eKi ≪≫
      (tilde.functor (CommRingCat.of (c.pt ⊗[R₀] A₀))).mapDerivedCategoryFactors.app M ≪≫ eE

end Descent

end AlgebraicGeometry.AffinePerfectDescent

end
