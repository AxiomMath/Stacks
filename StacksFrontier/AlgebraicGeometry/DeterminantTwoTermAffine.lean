module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import Mathlib.RingTheory.PicardGroup

/-!
# The determinant of a two-term perfect complex on an affine scheme

Let `R` be a commutative ring and `X = Spec R`. Derived sheafification is an equivalence from the
groupoid of perfect objects of `D(R)` of Tor amplitude in `[-1, 0]` and their isomorphisms onto
the groupoid of perfect objects of `D(𝒪_X)` of Tor amplitude in `[-1, 0]` and their
isomorphisms, and the sheaf associated with an invertible `R`-module is an invertible
`𝒪_X`-module. Transporting the determinant of More on Algebra, Section 0FJI along these two
identifications gives the determinant functor of Stacks 0FJX on `X`, together with the canonical
global section of the determinant of a rank-zero object and its compatibility with isomorphisms.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.tildeSource`: derived sheafification, from the groupoid
  of perfect objects of `D(R)` of Tor amplitude in `[-1, 0]` to the source category of the
  determinant on `Spec R`.
* `AlgebraicGeometry.DeterminantTwoTerm.tildeSourceEquivalence` and
  `AlgebraicGeometry.DeterminantTwoTerm.sourceComplex`: that functor as an equivalence, and the
  complex of `R`-modules it attaches to an object of the source category on `Spec R`.
* `AlgebraicGeometry.DeterminantTwoTerm.specDet` and
  `AlgebraicGeometry.DeterminantTwoTerm.specDelta`: the determinant functor on `Spec R` and the
  canonical global section of the determinant of a rank-zero object.
* `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroSpec`: rank zero for an object of the source
  category on `Spec R`, namely rank zero for a corresponding complex of `R`-modules.
* `AlgebraicGeometry.DeterminantTwoTerm.affineDet` and
  `AlgebraicGeometry.DeterminantTwoTerm.affineDelta`: the determinant and its canonical section
  read on the groupoid of perfect objects of `D(R)`, from which the two above are transported.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_tilde`: the sheaf on `Spec R`
  associated with an invertible `R`-module is an invertible `𝒪_{Spec R}`-module.
* `AlgebraicGeometry.DeterminantTwoTerm.isPerfectTwoTermAmplitude_tilde_iff`: the sheaf
  associated with an object of `D(R)` is perfect of Tor amplitude in `[-1, 0]` exactly when the
  object is.
* `AlgebraicGeometry.DeterminantTwoTerm.specDet_map_specDelta`: the determinant of an isomorphism
  carries the canonical global section of a rank-zero object to that of the isomorphic object.
* `AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso` and
  `AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso_specDelta`: on `Spec R` the
  determinant is the sheaf associated with the determinant line of a two-term finite-projective
  presentation, and the canonical global section is the canonical element of that presentation.
* `AlgebraicGeometry.DeterminantTwoTerm.specDelta_ne_zero`: the canonical global section is
  nonzero as soon as the canonical element of More on Algebra, Section 0FJI is.

## Implementation notes

Rank zero is transported along the equivalence of source categories rather than read off
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`, the scheme-level notion, which asks for
the same condition on the affine opens of a cover.

Downstream files must write `attribute [local instance 10000] HasDerivedCategory.standard`; see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.10.4 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 36.10.7 (Tag 08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Lemma 36.10.1 (Tag 08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Lemma 17.23.2 (Tag 0B8K)](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Lemma 26.7.3 (Tag 01I8)](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TwoTermDeterminant
open Stacks.SheafOfModules (isInvertible_iff_exists_tensor_iso_unit)

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The sheaf associated with an invertible module -/

/-- The pairing `M ⊗_R Mᵛ ≅ R` of an invertible `R`-module with its dual. -/
def invertibleDualIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R) [Module.Invertible R M] :
    (M ⊗ ModuleCat.of R (Module.Dual R M) : ModuleCat.{u} R) ≅ ModuleCat.of R R :=
  ((TensorProduct.comm R M (Module.Dual R M)).trans
    (Module.Invertible.linearEquiv R M)).toModuleIso

/-- **The sheaf on `Spec R` associated with an invertible `R`-module is invertible.** -/
theorem isInvertibleModule_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.Invertible R M] : Stacks.Ample.IsInvertibleModule (Spec R) (tilde M) := by
  refine Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ ?_
  refine (isInvertible_iff_exists_tensor_iso_unit
    (hO := isSheaf_specStructureRingPresheaf R) (tilde M)).mpr
    ⟨tilde (ModuleCat.of R (Module.Dual R M)), ⟨?_⟩⟩
  exact (tildeTensorIso R M (ModuleCat.of R (Module.Dual R M))).symm ≪≫
    (tilde.functor R).mapIso (invertibleDualIso R M) ≪≫ tildeSelf

/-- A map of `R`-modules acts on the canonical global sections of the associated sheaves through
the map itself. -/
theorem app_tilde_toOpen (R : CommRingCat.{u}) {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    Scheme.Modules.Hom.app ((tilde.functor R).map f) ⊤ ((tilde.toOpen M ⊤).hom x) =
      (tilde.toOpen N ⊤).hom (f.hom x) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x

/-- The associated-sheaf functor, from invertible `R`-modules to the target category of the
determinant on `Spec R`. -/
def tildeInvertible (R : CommRingCat.{u}) :
    InvertibleModule R ⥤ InvertibleModuleCat (Spec R) :=
  ObjectProperty.lift _ ((invertibleModuleProperty R).ι ⋙ tilde.functor R) fun M => by
    have : Module.Invertible R M.obj := M.property
    exact isInvertibleModule_tilde R M.obj

/-! ### The source category on an affine scheme -/

/-- Perfectness together with Tor amplitude in `[-1, 0]` transports along an isomorphism of
`D(𝒪_X)`. -/
theorem IsPerfectTwoTermAmplitude.of_iso {X : Scheme.{u}}
    {K K' : DerivedCategory X.Modules} (h : IsPerfectTwoTermAmplitude X K) (e : K ≅ K') :
    IsPerfectTwoTermAmplitude X K' :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := X.toRingedSpace) e h.1,
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso
      (X := X.toRingedSpace) h.2 e.symm⟩

/-- **The source category of the determinant on `Spec R` is the ring-level one.** The sheaf
associated with an object `M` of `D(R)` is a perfect object of `D(𝒪_{Spec R})` of Tor amplitude
in `[-1, 0]` if and only if `M` is a perfect object of `D(R)` of Tor amplitude in `[-1, 0]`. -/
theorem isPerfectTwoTermAmplitude_tilde_iff (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) :
    IsPerfectTwoTermAmplitude (Spec R) ((tilde.functor R).mapDerivedCategory.obj M) ↔
      perfectTwoTermComplexProperty R M :=
  and_congr (isPerfect_tilde_iff M)
    ((hasTorAmplitude_tilde_iff M (-1) 0).trans
      (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R M (-1) 0))

/-- Derived sheafification, from the category of perfect objects of `D(R)` of Tor amplitude in
`[-1, 0]` to the source category of the determinant on `Spec R`. -/
def tildeSource (R : CommRingCat.{u}) :
    PerfectTwoTermComplex R ⥤ PerfectTwoTermAmplitude (Spec R) :=
  ObjectProperty.lift _
    ((perfectTwoTermComplexProperty R).ι ⋙ (tilde.functor R).mapDerivedCategory)
    fun K => (isPerfectTwoTermAmplitude_tilde_iff R K.obj).mpr K.property

/-- Derived sheafification is fully faithful on perfect objects of Tor amplitude in `[-1, 0]`. -/
def tildeSourceFullyFaithful (R : CommRingCat.{u}) : (tildeSource R).FullyFaithful where
  preimage {_ _} f :=
    ObjectProperty.homMk ((StandardModel.mapDerivedCategoryFullyFaithful R).preimage f.hom)
  map_preimage {_ _} f :=
    ObjectProperty.hom_ext _
      ((StandardModel.mapDerivedCategoryFullyFaithful R).map_preimage f.hom)
  preimage_map {_ _} f :=
    ObjectProperty.hom_ext _
      ((StandardModel.mapDerivedCategoryFullyFaithful R).preimage_map f.hom)

/-- Derived sheafification `tildeSource R` is full. -/
instance tildeSource_full (R : CommRingCat.{u}) : (tildeSource R).Full :=
  (tildeSourceFullyFaithful R).full

/-- Derived sheafification `tildeSource R` is faithful. -/
instance tildeSource_faithful (R : CommRingCat.{u}) : (tildeSource R).Faithful :=
  (tildeSourceFullyFaithful R).faithful

/-- Every perfect object of `D(𝒪_{Spec R})` of Tor amplitude in `[-1, 0]` is the sheaf associated
with one of `D(R)`. -/
instance tildeSource_essSurj (R : CommRingCat.{u}) : (tildeSource R).EssSurj where
  mem_essImage L := by
    obtain ⟨M, ⟨i⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R L.obj
      (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) L.obj
        (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
          (E := L.obj) L.property.1))
    exact ⟨⟨M, (isPerfectTwoTermAmplitude_tilde_iff R M).mp (L.property.of_iso i.symm)⟩,
      ⟨ObjectProperty.isoMk _ i⟩⟩

/-- Derived sheafification `tildeSource R` is an equivalence of categories. -/
instance tildeSource_isEquivalence (R : CommRingCat.{u}) : (tildeSource R).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **Derived sheafification is an equivalence onto the source category of the determinant on
`Spec R`.** -/
def tildeSourceEquivalence (R : CommRingCat.{u}) :
    PerfectTwoTermComplex R ≌ PerfectTwoTermAmplitude (Spec R) :=
  (tildeSource R).asEquivalence

/-- The perfect object of `D(R)` of Tor amplitude in `[-1, 0]` corresponding to an object of the
source category of the determinant on `Spec R`. -/
def sourceComplex (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R)) :
    PerfectTwoTermComplex R :=
  (tildeSourceEquivalence R).inverse.obj L

/-- The sheaf associated with `sourceComplex R L` is `L`. -/
def tildeSourceComplexIso (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R)) :
    (tildeSource R).obj (sourceComplex R L) ≅ L :=
  (tildeSourceEquivalence R).counitIso.app L

/-! ### The determinant on the ring-level groupoid -/

/-- The determinant of More on Algebra, Section 0FJI, read as a functor to invertible
`𝒪_{Spec R}`-modules and their isomorphisms. -/
def affineDet (R : CommRingCat.{u}) :
    Core (PerfectTwoTermComplex R) ⥤ Core (InvertibleModuleCat (Spec R)) :=
  det R ⋙ (tildeInvertible R).core

/-- The value of `affineDet` is the sheaf associated with the determinant of More on Algebra,
Section 0FJI. -/
theorem affineDet_obj (R : CommRingCat.{u}) (K : PerfectTwoTermComplex R) :
    ((affineDet R).obj ⟨K⟩).of.obj = tilde ((det R).obj ⟨K⟩).of.obj := rfl

/-- The canonical element of the determinant of a rank-zero object, read as a global section on
`Spec R`. -/
def affineDelta (R : CommRingCat.{u}) (K : PerfectTwoTermComplex R) (hK : IsRankZero K.obj) :
    Γ(((affineDet R).obj ⟨K⟩).of.obj, ⊤) :=
  (tilde.toOpen ((det R).obj ⟨K⟩).of.obj ⊤).hom (delta K hK)

/-- `affineDet` carries the canonical global section of a rank-zero object to that of any
isomorphic object. -/
theorem affineDet_map_affineDelta (R : CommRingCat.{u}) {K L : PerfectTwoTermComplex R}
    (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
    (hK : IsRankZero K.obj) (hL : IsRankZero L.obj) :
    Scheme.Modules.Hom.app
        ((IsInvertibleProperty (Spec R)).ι.map ((affineDet R).map a).iso.hom) ⊤
        (affineDelta R K hK) = affineDelta R L hL :=
  (app_tilde_toOpen R ((invertibleModuleProperty R).ι.map ((det R).map a).iso.hom)
      (delta K hK)).trans
    (congrArg (tilde.toOpen ((det R).obj ⟨L⟩).of.obj ⊤).hom (det_map_delta a hK hL))

/-- The value of `affineDet` is the sheaf associated with the determinant line of any two-term
presentation by finite projective modules. -/
def affineDetPresentationIso (R : CommRingCat.{u}) (K : PerfectTwoTermComplex R)
    (P : TwoTermPresentation K.obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    ((affineDet R).obj ⟨K⟩).of.obj ≅
      tilde (ModuleCat.of R
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  (tilde.functor R).mapIso (detPresentationIso K P).toModuleIso

/-- The identification of `affineDet` with the determinant line of a rank-zero two-term
presentation carries `affineDelta` to the canonical element of that presentation. -/
theorem affineDetPresentationIso_affineDelta (R : CommRingCat.{u})
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj) (hP : P.IsRankZero) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.Hom.app (affineDetPresentationIso R K P).hom ⊤
        (affineDelta R K ⟨P, hP⟩) =
      (tilde.toOpen (ModuleCat.of R
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP) :=
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  (app_tilde_toOpen R (detPresentationIso K P).toModuleIso.hom (delta K ⟨P, hP⟩)).trans
    (congrArg (tilde.toOpen (ModuleCat.of R
      (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
      (detPresentationIso_delta K P hP))

/-! ### Stacks 0FJX on an affine scheme -/

/-- The determinant functor on `Spec R`, from the groupoid of perfect objects of `D(𝒪_{Spec R})` of
Tor amplitude in `[-1, 0]` and their isomorphisms to the groupoid of invertible
`𝒪_{Spec R}`-modules and their isomorphisms.

It is the determinant of More on Algebra, Section 0FJI, transported along the identification of
the source groupoid with the ring-level one and along the associated-sheaf functor. -/
@[stacks 0FJX "the determinant functor, for an affine scheme"]
def specDet (R : CommRingCat.{u}) :
    Core (PerfectTwoTermAmplitude (Spec R)) ⥤ Core (InvertibleModuleCat (Spec R)) :=
  (tildeSourceEquivalence R).inverse.core ⋙ affineDet R

/-- Rank zero for an object of the source groupoid of the determinant on `Spec R`: a
corresponding perfect object of `D(R)` of Tor amplitude in `[-1, 0]` admits a two-term
presentation by finite projective modules of equal rank at every prime. -/
def IsRankZeroSpec (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R)) : Prop :=
  ∃ M : DerivedCategory (ModuleCat.{u} R),
    Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ L.obj) ∧ IsRankZero M

/-- Rank zero for a perfect object of `D(R)` of Tor amplitude in `[-1, 0]` depends only on its
isomorphism class. -/
theorem isRankZero_of_iso {R : Type u} [CommRing R]
    {K K' : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ K') (h : IsRankZero K) :
    IsRankZero K' :=
  ⟨{ h.choose with iso := e.symm ≪≫ h.choose.iso }, h.choose_spec⟩

/-- A rank-zero object of the source groupoid on `Spec R` has a rank-zero `sourceComplex`. -/
theorem isRankZero_sourceComplex (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R))
    (hL : IsRankZeroSpec R L) : IsRankZero (sourceComplex R L).obj := by
  obtain ⟨M, ⟨i⟩, hM⟩ := hL
  exact isRankZero_of_iso ((StandardModel.mapDerivedCategoryFullyFaithful R).preimageIso
    (i ≪≫ ((IsPerfectTwoTermAmplitude (Spec R)).ι.mapIso (tildeSourceComplexIso R L)).symm)) hM

/-- The canonical global section `δ(L)` of the determinant of a rank-zero object of the source
groupoid on `Spec R`: the canonical element of More on Algebra, Section 0FJI, read as a global
section. -/
@[stacks 0FJX "the canonical global section δ(L) of the determinant of a rank-zero object, for an
affine scheme"]
def specDelta (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R))
    (hL : IsRankZeroSpec R L) : Γ(((specDet R).obj ⟨L⟩).of.obj, ⊤) :=
  affineDelta R (sourceComplex R L) (isRankZero_sourceComplex R L hL)

/-- For every isomorphism `a : L ⟶ K` of rank-zero objects of the source groupoid on `Spec R`,
`det(a)(δ(L)) = δ(K)`. -/
@[stacks 0FJX "the compatibility det(a)(δ(L)) = δ(K) of the canonical global section with
isomorphisms, for an affine scheme"]
theorem specDet_map_specDelta (R : CommRingCat.{u}) {L K : PerfectTwoTermAmplitude (Spec R)}
    (a : (⟨L⟩ : Core (PerfectTwoTermAmplitude (Spec R))) ⟶ ⟨K⟩)
    (hL : IsRankZeroSpec R L) (hK : IsRankZeroSpec R K) :
    Scheme.Modules.Hom.app
        ((IsInvertibleProperty (Spec R)).ι.map ((specDet R).map a).iso.hom) ⊤
        (specDelta R L hL) = specDelta R K hK :=
  affineDet_map_affineDelta R ((tildeSourceEquivalence R).inverse.core.map a) _ _

/-- The determinant on `Spec R` of an object of the source groupoid is the sheaf associated with
the determinant line of More on Algebra, Section 0FJI of any two-term finite-projective
presentation of the corresponding complex of `R`-modules. Such a presentation always exists,
`TwoTermDeterminant.presentation` being one. -/
@[stacks 0FJX "the construction is locally the one of More on Algebra, Section 0FJI: on an affine
scheme the determinant is the determinant line of a two-term finite-projective presentation"]
def specDetPresentationIso (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R))
    (P : TwoTermPresentation (sourceComplex R L).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    ((specDet R).obj ⟨L⟩).of.obj ≅
      tilde (ModuleCat.of R
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) :=
  affineDetPresentationIso R (sourceComplex R L) P

/-- Under the identification of the determinant with the determinant line of a rank-zero two-term
finite-projective presentation, the canonical global section is the canonical element of More on
Algebra, Section 0FJI of that presentation. -/
@[stacks 0FJX "the canonical global section is locally the canonical element of More on Algebra,
Section 0FJI: on an affine scheme it is the determinant of the differential of a two-term
finite-projective presentation"]
theorem specDetPresentationIso_specDelta (R : CommRingCat.{u})
    (L : PerfectTwoTermAmplitude (Spec R)) (P : TwoTermPresentation (sourceComplex R L).obj)
    (hP : P.IsRankZero) (hL : IsRankZeroSpec R L) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.Hom.app (specDetPresentationIso R L P).hom ⊤ (specDelta R L hL) =
      (tilde.toOpen (ModuleCat.of R
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP) :=
  affineDetPresentationIso_affineDelta R (sourceComplex R L) P hP

/-- **The canonical global section is not the zero section.** If the canonical element of More on
Algebra, Section 0FJI of a rank-zero two-term finite-projective presentation is nonzero, then so
is the canonical global section of the determinant on `Spec R`. -/
theorem specDelta_ne_zero (R : CommRingCat.{u}) (L : PerfectTwoTermAmplitude (Spec R))
    (P : TwoTermPresentation (sourceComplex R L).obj) (hP : P.IsRankZero)
    (hL : IsRankZeroSpec R L)
    (h : letI := P.finite (-1)
         letI := P.projective (-1)
         letI := P.finite 0
         letI := P.projective 0
         TwoTermComplex.delta (P.complex.d (-1) 0).hom hP ≠ 0) :
    specDelta R L hL ≠ 0 := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  intro hz
  refine h (((ConcreteCategory.bijective_of_isIso (tilde.toOpen (ModuleCat.of R
    (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤)).1 ?_).symm)
  have key := specDetPresentationIso_specDelta R L P hP hL
  rw [hz, map_zero] at key
  exact (map_zero _).trans key

end AlgebraicGeometry.DeterminantTwoTerm

end
