module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Flat.GenericFlatness
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.RingTheory.Support.Fiber
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Generic flatness over a reduced base

For a finite type morphism to a reduced scheme and a finite type quasi-coherent
module on its source, there is a dense open part of the base over which both
the morphism and the module are flat and finitely presented.

## Main results

* `AlgebraicGeometry.exists_dense_open_flat_finitePresentation` gives the common dense
  open for the morphism and the module.

## Implementation notes

The base change to an open `U` is expressed as the restricted morphism from
`f ⁻¹ᵁ U` to `U`; the module on it is the restriction along the canonical open
immersion. The four properties share the same open and are therefore stated
together under its existential quantifier.

The open set is built affine-locally. Over an affine open of the base, affine generic
flatness supplies a dense open on which every pair of source charts is simultaneously good,
and the union of the resulting basic open sets over all affine opens of the base is the
required dense open. Flatness and finite presentation of the morphism are then checked on
the basic affine charts the good-away condition provides, and the sheaf-level conclusions
are assembled from an open cover of the preimage.

## References

* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set PrimeSpectrum
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/-- A finitely presented cyclic algebra module has quasi-compact support complement. -/
private theorem cyclic_support_compl_isCompact
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A]
    (hcyclic : Function.Surjective (Algebra.linearMap R A)) :
    IsCompact (Module.support R A)ᶜ := by
  have hker : LinearMap.ker (Algebra.linearMap R A) = Module.annihilator R A := by
    ext r
    simp only [LinearMap.mem_ker, Module.mem_annihilator]
    change (algebraMap R A r = 0) ↔ ∀ a : A, r • a = 0
    constructor
    · intro hr a
      rw [Algebra.smul_def, hr, zero_mul]
    · intro hr
      simpa [Algebra.smul_def] using hr 1
  have hAnn : (Module.annihilator R A).FG := by
    have h := (Module.FinitePresentation.fg_ker_iff
      (Algebra.linearMap R A) hcyclic).mpr inferInstance
    rwa [hker] at h
  have hsupp : Module.support R A =
      PrimeSpectrum.zeroLocus (Module.annihilator R A : Set R) := by
    rw [Module.support_eq_zeroLocus]
  exact (support_isClosed_and_compl_isCompact_of_eq_zeroLocus_FG
    (R := R) (M := A) hAnn hsupp).2

/-- Base changing a cyclic quotient still gives a cyclic module over the new algebra. -/
private theorem tensor_quotient_algebraMap_surjective
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (I : Ideal B) :
    Function.Surjective (Algebra.linearMap C (C ⊗[B] (B ⧸ I))) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c q =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨algebraMap B C b * c, ?_⟩
    have htmul : c ⊗ₜ[B] Ideal.Quotient.mk I b =
        (algebraMap B C b * c) ⊗ₜ[B] (1 : B ⧸ I) := by
      rw [show Ideal.Quotient.mk I b = b • (1 : B ⧸ I) by
        change algebraMap B (B ⧸ I) b = _
        exact Algebra.algebraMap_eq_smul_one b]
      rw [TensorProduct.tmul_smul]
      change (b • c) ⊗ₜ[B] (1 : B ⧸ I) = _
      rw [Algebra.smul_def]
    rw [htmul]
    change algebraMap C (C ⊗[B] (B ⧸ I)) _ = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  | add z z' hz hz' =>
    obtain ⟨c, rfl⟩ := hz
    obtain ⟨d, rfl⟩ := hz'
    exact ⟨c + d, map_add (Algebra.linearMap C (C ⊗[B] (B ⧸ I))) c d⟩

/-- The complement of the support of a finitely presented base change of a cyclic quotient is
quasi-compact. -/
private theorem tensor_quotient_support_compl_isCompact
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (I : Ideal B) [Module.FinitePresentation C (C ⊗[B] (B ⧸ I))] :
    IsCompact (Module.support C (C ⊗[B] (B ⧸ I)))ᶜ :=
  cyclic_support_compl_isCompact (R := C) (A := C ⊗[B] (B ⧸ I))
    (tensor_quotient_algebraMap_surjective I)

/-- A good-away witness for an affine overlap quotient makes its localized overlap
quasi-compact. -/
private theorem affineOverlap_localized_support_compl_isCompact
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal B) (a : R)
    (h : Algebra.IsFinitePresentationFreeAway R B (B ⧸ I) a) :
    IsCompact (Module.support
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) ⊗[B]
        (B ⧸ I)))ᶜ := by
  let C := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  have : Module.FinitePresentation C (C ⊗[B] (B ⧸ I)) := h.2.1
  exact tensor_quotient_support_compl_isCompact I

/-- A good-away witness also gives the condition for the algebra as a module over itself. -/
private theorem isFinitePresentationFreeAway_self
    {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] {a : R}
    (h : Algebra.IsFinitePresentationFreeAway R B M a) :
    Algebra.IsFinitePresentationFreeAway R B B a := by
  let Bf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let e := (Algebra.TensorProduct.rid B Bf Bf).toLinearEquiv.symm
  have : Module.Free (Localization.Away a) Bf := h.2.2.1
  exact ⟨h.1, Module.FinitePresentation.of_equiv e, h.2.2.1,
    Module.Free.of_equiv (e.restrictScalars (Localization.Away a))⟩

/-- The localization of `B` at the image of the powers of `a` is the localization away from the
image of `a`. -/
private theorem isLocalization_away_algebraMapSubmonoid
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B] (a : R) :
    IsLocalization.Away (algebraMap R B a)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))) := by
  rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers (R := R) (S := B)]
  infer_instance

/-- The spectrum of the localization of `B` at the image of the powers of `a` is an open
subscheme of `Spec B`. -/
private theorem isOpenImmersion_spec_map_localization
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B] (a : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)))))) := by
  rw [Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- A good-away witness gives finite presentation and flatness for the map on the corresponding
basic affine charts. This transports both properties across the canonical localization models. -/
private theorem affineGood_basicOpen_ringHom_properties
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.affineOpens) (W : X.affineOpens)
    (hWV : W.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(S, V.1))
    (h : letI : Algebra Γ(S, V.1) Γ(X, W.1) :=
        (f.appLE V.1 W.1 hWV).hom.toAlgebra
      Algebra.IsFinitePresentationFreeAway Γ(S, V.1) Γ(X, W.1) (Γ(X, W.1)) a) :
    RingHom.FinitePresentation
        (f.appLE (S.basicOpen a)
          (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a))
          (by simp [Scheme.Hom.appLE])).hom ∧
      RingHom.Flat
        (f.appLE (S.basicOpen a)
          (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a))
          (by simp [Scheme.Hom.appLE])).hom := by
  let g := (f.appLE V.1 W.1 hWV).hom
  let R := Γ(S, V.1)
  let A := Localization.Away a
  let A' := Γ(S, S.basicOpen a)
  let B := Γ(X, W.1)
  let : Algebra R B := g.toAlgebra
  let Bf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let C := Γ(X, X.basicOpen (g a))
  have : IsLocalization.Away a A := Localization.isLocalization
  have : IsLocalization.Away a A' := V.2.isLocalization_basicOpen a
  have : IsLocalization.Away (g a) Bf := isLocalization_away_algebraMapSubmonoid B a
  have : IsLocalization.Away (g a) C := W.2.isLocalization_basicOpen (g a)
  let : Algebra R Bf := ((algebraMap B Bf).comp g).toAlgebra
  let : Algebra A Bf := (IsLocalization.Away.map A Bf g a).toAlgebra
  let : Algebra R C := ((algebraMap B C).comp g).toAlgebra
  let : Algebra A' C := (IsLocalization.Away.map A' C g a).toAlgebra
  let eA : A ≃ₐ[R] A' := IsLocalization.algEquiv (Submonoid.powers a) A A'
  let eB : Bf ≃ₐ[B] C := IsLocalization.algEquiv (Submonoid.powers (g a)) Bf C
  have hcomm : (IsLocalization.Away.map A' C g a).comp eA.toRingEquiv.toRingHom =
      eB.toRingEquiv.toRingHom.comp (IsLocalization.Away.map A Bf g a) := by
    refine IsLocalization.ringHom_ext (M := Submonoid.powers a) (S := A) ?_
    ext r
    change IsLocalization.Away.map A' C g a (eA (algebraMap R A r)) =
      eB (IsLocalization.Away.map A Bf g a (algebraMap R A r))
    rw [eA.commutes, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.map,
      IsLocalization.map_eq, eB.commutes]
  let f₁ : CommRingCat.of A ⟶ CommRingCat.of Bf :=
    CommRingCat.ofHom (IsLocalization.Away.map A Bf g a)
  let f₂ : CommRingCat.of A' ⟶ CommRingCat.of C :=
    CommRingCat.ofHom (IsLocalization.Away.map A' C g a)
  have harrow : Arrow.mk f₁ ≅ Arrow.mk f₂ := by
    refine Arrow.isoMk eA.toRingEquiv.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso ?_
    ext x
    exact congrArg (fun k : A →+* C => k x) hcomm
  have : Algebra.FinitePresentation A Bf := h.1
  have hfp₁ : RingHom.FinitePresentation (IsLocalization.Away.map A Bf g a) :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hfp₂ : RingHom.FinitePresentation (IsLocalization.Away.map A' C g a) :=
    (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff harrow).mp hfp₁
  have hflat₁ : RingHom.Flat (IsLocalization.Away.map A Bf g a) := by
    have : Module.Free A Bf := h.2.2.1
    rw [← RingHom.algebraMap_toAlgebra (IsLocalization.Away.map A Bf g a)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflat₂ : RingHom.Flat (IsLocalization.Away.map A' C g a) :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff harrow).mp hflat₁
  have hEq := IsAffineOpen.appLE_eq_away_map f V.2 W.2 hWV a
  rw [hEq]
  exact ⟨by simpa [f₂] using hfp₂, by simpa [f₂] using hflat₂⟩

/-- The complement of the preimage of an affine open in an affine chart is closed. -/
private theorem isClosed_affineOverlap_compl
    {X : Scheme.{u}} (U V : X.affineOpens) :
    IsClosed (Set.univ \ U.2.fromSpec ⁻¹' (V.1 : Set X)) := by
  rw [Set.sdiff_eq, Set.univ_inter]
  exact (V.1.2.preimage U.2.fromSpec.continuous).isClosed_compl

/-- The ideal defining the complement of an affine chart overlap. -/
private noncomputable def affineOverlapIdeal
    {X : Scheme.{u}} (U V : X.affineOpens) : Ideal Γ(X, U.1) := by
  exact (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp (isClosed_affineOverlap_compl U V)
    |>.choose

/-- In an affine chart, the overlap with another affine chart is the complement of the support
of the cyclic quotient cut out by `affineOverlapIdeal`. -/
private theorem affineOverlap_preimage_eq_support_compl
    {X : Scheme.{u}} (U V : X.affineOpens) :
    U.2.fromSpec ⁻¹' (V.1 : Set X) =
      (Module.support Γ(X, U.1)
        (Γ(X, U.1) ⧸ affineOverlapIdeal U V))ᶜ := by
  let f := U.2.fromSpec
  let Z : Set (PrimeSpectrum Γ(X, U.1)) := Set.univ \ f ⁻¹' (V.1 : Set X)
  have hZ : IsClosed Z := isClosed_affineOverlap_compl U V
  have hzero : Z = PrimeSpectrum.zeroLocus (affineOverlapIdeal U V : Set Γ(X, U.1)) := by
    dsimp [affineOverlapIdeal]
    exact (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ |>.choose_spec
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, ← hzero]
  ext x
  change x ∈ f ⁻¹' (V.1 : Set X) ↔ x ∉ Z
  constructor
  · intro hx hdiff
    exact hdiff.2 (Set.mem_preimage.mpr hx)
  · intro hx
    by_contra hnot
    exact hx ⟨Set.mem_univ _, hnot⟩

section

/-- The image of the spectrum of a localization of an affine chart at a section is the basic
open set that section cuts out. -/
private theorem range_localized_affineChart
    {X : Scheme.{u}} (W : X.affineOpens) (a : Γ(X, W.1))
    (C : Type u) [CommRing C] [Algebra Γ(X, W.1) C] [IsLocalization.Away a C] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W.1) C)) ≫ W.2.fromSpec) =
      (X.basicOpen a : Set X) := by
  have hcomp : Set.range (W.2.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, W.1) C)) =
      W.2.fromSpec '' Set.range (PrimeSpectrum.comap (algebraMap Γ(X, W.1) C)) :=
    Set.range_comp _ _
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap Γ(X, W.1) C)) =
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, W.1))) :=
    PrimeSpectrum.localization_away_comap_range C a
  have himage : W.2.fromSpec '' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, W.1))) =
      (X.basicOpen a : Set X) :=
    congrArg (fun O : X.Opens => (O : Set X)) (W.2.fromSpec_image_basicOpen a)
  change Set.range (W.2.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, W.1) C)) = _
  exact (hcomp.trans (congrArg (fun t => W.2.fromSpec '' t) hrange)).trans himage

/-- A good-away witness for an affine overlap makes the intersection of the corresponding
basic open set with the other chart quasi-compact. -/
private theorem affineOverlap_basicOpen_inter_isCompact
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.affineOpens) (W W' : X.affineOpens)
    (hWV : W.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(S, V.1))
    (h : letI := (f.appLE V.1 W.1 hWV).hom.toAlgebra
      Algebra.IsFinitePresentationFreeAway Γ(S, V.1) Γ(X, W.1)
        (Γ(X, W.1) ⧸ affineOverlapIdeal W W') a) :
    IsCompact ((X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) : Set X) ∩ W'.1) := by
  let R := Γ(S, V.1)
  let B := Γ(X, W.1)
  let : Algebra R B := (f.appLE V.1 W.1 hWV).hom.toAlgebra
  let C := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let I := affineOverlapIdeal W W'
  have : IsLocalization.Away ((f.appLE V.1 W.1 hWV).hom a) C :=
    isLocalization_away_algebraMapSubmonoid B a
  let j : Spec (CommRingCat.of C) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ W.2.fromSpec
  have hcomp : IsCompact (Module.support C (C ⊗[B] (B ⧸ I)))ᶜ :=
    affineOverlap_localized_support_compl_isCompact I a h
  have hsupp : Module.support C (C ⊗[B] (B ⧸ I)) =
      PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B (B ⧸ I) :=
    Module.support_tensorProduct_eq_preimage_comap
  have hoverlap : (Module.support B (B ⧸ I))ᶜ = W.2.fromSpec ⁻¹' (W'.1 : Set X) :=
    (affineOverlap_preimage_eq_support_compl W W').symm
  have hpre : (Module.support C (C ⊗[B] (B ⧸ I)))ᶜ = j ⁻¹' (W'.1 : Set X) := by
    rw [hsupp, ← Set.preimage_compl, hoverlap]
    rfl
  have hrange : Set.range j = (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) : Set X) :=
    range_localized_affineChart W ((f.appLE V.1 W.1 hWV).hom a) C
  have heq : j '' (Module.support C (C ⊗[B] (B ⧸ I)))ᶜ =
      (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) : Set X) ∩ W'.1 :=
    calc j '' (Module.support C (C ⊗[B] (B ⧸ I)))ᶜ
        = j '' (j ⁻¹' (W'.1 : Set X)) := congrArg (fun t => j '' t) hpre
      _ = (W'.1 : Set X) ∩ Set.range j := Set.image_preimage_eq_inter_range
      _ = (W'.1 : Set X) ∩ (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) : Set X) :=
          congrArg (fun t => (W'.1 : Set X) ∩ t) hrange
      _ = (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) : Set X) ∩ W'.1 := Set.inter_comm _ _
  rw [← heq]
  exact hcomp.image j.continuous

/-- An open subset covered by affine opens whose pairwise intersections are quasi-compact is
quasi-separated. -/
private theorem isQuasiSeparated_of_affine_cover
    {X : Scheme.{u}} {T : X.Opens} {ι : Type*} (W : ι → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hcover : ⨆ i, W i = T)
    (hinter : ∀ i j, IsCompact ((W i : Set X) ∩ W j)) :
    IsQuasiSeparated (T : Set X) := by
  let W' : ι → T.toScheme.Opens := fun i => T.ι ⁻¹ᵁ W i
  have hle (i : ι) : W i ≤ T := hcover ▸ le_iSup W i
  have himage (i : ι) : T.ι ''ᵁ W' i = W i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hle i)]
  have haff (i : ι) : IsAffineOpen (W' i) :=
    T.ι.isAffineOpen_iff_of_isOpenImmersion.mp (by rw [himage]; exact hW i)
  have hcov : IsOpenCover W' := by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    have hx : T.ι x ∈ ⨆ i, W i := hcover.symm ▸ x.2
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have hcomp (i j : ι) : IsCompact ((W' i : Set T) ∩ W' j) := by
    rw [T.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
    have heq : T.ι '' ((W' i : Set T) ∩ W' j) = (W i : Set X) ∩ W j := by
      rw [Set.image_inter T.ι.isOpenEmbedding.injective]
      change (T.ι ''ᵁ W' i : Set X) ∩ (T.ι ''ᵁ W' j : Set X) = _
      rw [himage, himage]
    rw [heq]
    exact hinter i j
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ T.2).mpr
    (Scheme.quasiSeparatedSpace_of_isOpenCover W' hcov haff hcomp)

/-- Over a basic affine chart of the base where the good-away condition holds on every pair of
source charts, the inverse image of the chart is quasi-separated. -/
private theorem affineGood_preimage_isQuasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.affineOpens)
    (s : Set X.affineOpens) (hcover : f ⁻¹ᵁ V.1 = ⨆ W ∈ s, W.1)
    (a : Γ(S, V.1))
    (hgood : ∀ (W W' : X.affineOpens) (hW : W ∈ s) (_ : W' ∈ s),
      let hWV : W.1 ≤ f ⁻¹ᵁ V.1 := by
        rw [hcover]; exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)
      letI := (f.appLE V.1 W.1 hWV).hom.toAlgebra
      Algebra.IsFinitePresentationFreeAway Γ(S, V.1) Γ(X, W.1)
        (Γ(X, W.1) ⧸ affineOverlapIdeal W W') a) :
    IsQuasiSeparated (f ⁻¹ᵁ S.basicOpen a : Set X) := by
  let e (W : s) : W.1.1 ≤ f ⁻¹ᵁ V.1 := by
    rw [hcover]; exact le_iSup_of_le W.1 (le_iSup_of_le W.2 le_rfl)
  let W (i : s) : X.Opens := X.basicOpen ((f.appLE V.1 i.1.1 (e i)).hom a)
  have hW (i : s) : W i = i.1.1 ⊓ f ⁻¹ᵁ S.basicOpen a := by
    dsimp [W, Scheme.Hom.appLE]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  apply isQuasiSeparated_of_affine_cover W (fun i => i.1.2.basicOpen _)
  · simp only [hW, ← iSup_inf_eq]
    rw [iSup_subtype, ← hcover, inf_eq_right.mpr]
    exact Scheme.Hom.preimage_mono f (S.basicOpen_le a)
  · intro i j
    have heq : (W i : Set X) ∩ W j = (W i : Set X) ∩ j.1.1 := by
      rw [hW i, hW j]
      ext x
      simp only [Opens.coe_inf, Set.mem_inter_iff]
      tauto
    rw [heq]
    exact affineOverlap_basicOpen_inter_isCompact f V i.1 j.1 (e i) a
      (hgood i.1 j.1 i.2 j.2)

end

/-- The intersection of a finite family of dense open sets is dense. -/
@[ega "I 7.1.1" "density clause"]
private theorem dense_sInter_of_finite
    {X : Type*} [TopologicalSpace X] {s : Set (Set X)} (hs : s.Finite)
    (ho : ∀ U ∈ s, IsOpen U) (hd : ∀ U ∈ s, Dense U) : Dense (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert U s hUs hs ih =>
    simp only [sInter_insert, forall_mem_insert] at ho hd ⊢
    exact (hd.1).inter_of_isOpen_left (ih ho.2 hd.2) ho.1

/-- A finite family of finite type algebras and finite modules has a common dense open on which
all affine generic-flatness conclusions hold. -/
private theorem exists_dense_open_common_good
    {R : Type u} [CommRing R] [_root_.IsReduced R] {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Algebra.FiniteType R (B i)]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (B i) (M i)]
    [∀ i, Module.Finite (B i) (M i)] :
    ∃ W : Set (PrimeSpectrum R), IsOpen W ∧ Dense W ∧
      ∀ i x, x ∈ W → ∃ a : R, x ∈ basicOpen a ∧
        Algebra.IsFinitePresentationFreeAway R (B i) (M i) a := by
  classical
  let P (i : ι) :=
    Algebra.exists_isOpen_dense_isFinitePresentationFreeAway
      (R := R) (S := B i) (M := M i)
  let U (i : ι) : Set (PrimeSpectrum R) := (P i).choose
  have hU (i : ι) : IsOpen (U i) ∧ Dense (U i) ∧
      ∀ x ∈ U i, ∃ a : R, x ∈ basicOpen a ∧
        (basicOpen a : Set (PrimeSpectrum R)) ⊆ U i ∧
        Algebra.IsFinitePresentationFreeAway R (B i) (M i) a := (P i).choose_spec
  let W : Set (PrimeSpectrum R) := ⋂₀ Set.range U
  have hrange : (Set.range U).Finite := Set.finite_range U
  have hWopen : IsOpen W := hrange.isOpen_sInter fun V hV => by
    obtain ⟨i, rfl⟩ := hV
    exact (hU i).1
  have hWdense : Dense W := dense_sInter_of_finite hrange
    (fun V hV => by obtain ⟨i, rfl⟩ := hV; exact (hU i).1)
    (fun V hV => by obtain ⟨i, rfl⟩ := hV; exact (hU i).2.1)
  refine ⟨W, hWopen, hWdense, ?_⟩
  intro i x hx
  have hxUi : x ∈ U i := Set.mem_sInter.mp hx (U i) ⟨i, rfl⟩
  obtain ⟨a, hxa, -, hgood⟩ := (hU i).2.2 x hxUi
  exact ⟨a, hxa, hgood⟩

/-- Over a finite family, the pointwise generic-flatness witnesses can be shrunk to one basic
open.  The product lies in every witness open, and the good-away condition is preserved when its
element is replaced by a multiple. -/
private theorem exists_common_basicOpen_good
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (B i) (M i)]
    {x : PrimeSpectrum R}
    (h : ∀ i, ∃ a : R, x ∈ basicOpen a ∧
      Algebra.IsFinitePresentationFreeAway R (B i) (M i) a) :
    ∃ a : R, x ∈ basicOpen a ∧
      ∀ i, Algebra.IsFinitePresentationFreeAway R (B i) (M i) a := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose a ha using h
  refine ⟨∏ i, a i, ?_, ?_⟩
  · have hxmem : ∀ i, a i ∈ x.asIdeal.primeCompl := fun i => (ha i).1
    change (∏ i, a i) ∈ x.asIdeal.primeCompl
    have hprod : ∀ s : Finset ι, (∀ i ∈ s, a i ∈ x.asIdeal.primeCompl) →
        (∏ i ∈ s, a i) ∈ x.asIdeal.primeCompl := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        intro h
        rw [Finset.prod_insert hi]
        exact x.asIdeal.primeCompl.mul_mem
          (h i (Finset.mem_insert_self i s))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa using hprod Finset.univ (fun i _ => hxmem i)
  · intro i
    exact (ha i).2.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- Finite type and quasicoherence imply finite generation of sections on an affine open. -/
private lemma moduleFinite_sections_on_affine
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (U : S.affineOpens) : Module.Finite Γ(S, U.1) Γ(F, U.1) := by
  let R := Γ(S, U.1)
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let F' := F.restrict f
  have hPull : ((Scheme.Modules.pullback f).obj F).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom F
  have : ((Scheme.Modules.pullback f).obj F).IsFiniteType := hPull
  have : F'.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm
  have : F'.IsQuasicoherent := by infer_instance
  let M : ModuleCat R := AlgebraicGeometry.moduleSpecΓFunctor.obj F'
  have htilde : (tilde M).IsFiniteType := by
    have hiso : IsIso (F'.fromTildeΓ) :=
      (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ F').mp inferInstance
    have : IsIso (F'.fromTildeΓ) := hiso
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso F'.fromTildeΓ).symm
  have : Module.Finite R M := (AlgebraicGeometry.tilde_isFiniteType_iff M).mp htilde
  let e := affineSectionsLinearEquiv F U.2
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
  let q' : (Fin n → R) →ₗ[R] Γ(F, U.1) := e.toLinearMap.comp q
  have hq' : Function.Surjective q' := e.surjective.comp hq
  exact Module.Finite.of_surjective q' hq'

/-- The underlying module of extension of scalars is the usual tensor product.

The `Bf`-module structure on the extension of scalars is the one carried by the `ModuleCat`
object, so it is supplied explicitly on the tensor product before the linearity of the
comparison map is checked. -/
private noncomputable def moduleExtendScalarsTensorEquiv
    {B Bf : Type u} [CommRing B] [CommRing Bf] [Algebra B Bf]
    (N : ModuleCat.{u} (CommRingCat.of B))
    [IsScalarTower B Bf Bf] :
    let Nf := (ModuleCat.extendScalars (algebraMap B Bf)).obj N
    (Nf : Type u) ≃ₗ[Bf] Bf ⊗[B] (N : Type u) := by
  let A : Type u := (ModuleCat.restrictScalars (algebraMap B Bf)).obj (ModuleCat.of Bf Bf)
  let : Module Bf (A ⊗[B] (N : Type u)) :=
    inferInstanceAs (Module Bf ((ModuleCat.extendScalars (algebraMap B Bf)).obj N : Type u))
  let eB : A ≃ₗ[B] Bf :=
    { AddEquiv.refl Bf with
      map_smul' := fun r x => (Algebra.smul_def (R := B) (A := Bf) r x).symm }
  let e := TensorProduct.congr eB (LinearEquiv.refl B N)
  have key : ∀ (c : Bf) (w : A ⊗[B] (N : Type u)), e (c • w) = c • e w := by
    intro c w
    induction w using TensorProduct.inductionOn with
    | tmul r n => rfl
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { e.toAddEquiv with map_smul' := key }

/-- Over a basic affine chart where the good-away condition holds, the pullback of the module
to the localized chart is finitely presented. -/
private theorem affineGood_pullback_finitePresentation
    {R B M : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] (a : R)
    (h : Algebra.IsFinitePresentationFreeAway R B M a)
    (G : (Spec (CommRingCat.of B)).Modules) [G.IsQuasicoherent]
    (eN : (AlgebraicGeometry.moduleSpecΓFunctor.obj G : Type u) ≃ₗ[B] M) :
    let Bf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
    ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B Bf)))).obj G).IsFinitePresentation := by
  let Bf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let φ : CommRingCat.of B ⟶ CommRingCat.of Bf :=
    CommRingCat.ofHom (algebraMap B Bf)
  have : IsScalarTower B Bf Bf := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp)
  let N : ModuleCat (CommRingCat.of B) := AlgebraicGeometry.moduleSpecΓFunctor.obj G
  let eExt := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Bf Bf) eN
  have hfpExt : Module.FinitePresentation Bf (Bf ⊗[B] N) :=
    eExt.finitePresentation_iff.mpr h.2.1
  let Nf : ModuleCat (CommRingCat.of Bf) :=
    (ModuleCat.extendScalars (algebraMap B Bf)).obj N
  let eNf : (Nf : Type u) ≃ₗ[Bf] Bf ⊗[B] (N : Type u) :=
    moduleExtendScalarsTensorEquiv (B := B) (Bf := Bf) N
  have hfpNf : Module.FinitePresentation (CommRingCat.of Bf) Nf := by
    have : Module.FinitePresentation Bf (Bf ⊗[B] N) := hfpExt
    exact Module.FinitePresentation.of_equiv eNf.symm
  have htilde : (tilde Nf).IsFinitePresentation :=
    (AlgebraicGeometry.tilde_isFinitePresentation_iff Nf).2 hfpNf
  let eT := (AlgebraicGeometry.pullbackTildeIso
    (CommRingCat.of B) (CommRingCat.of Bf) φ).app N
  have hpullTilde :
      ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde N)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec (CommRingCat.of Bf)).ringCatSheaf).prop_of_iso
      eT.symm htilde
  have hGiso : IsIso G.fromTildeΓ :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ G).mp inferInstance
  have eG : tilde N ≅ G := @asIso _ _ _ _ G.fromTildeΓ hGiso
  exact (SheafOfModules.isFinitePresentation (Spec (CommRingCat.of Bf)).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullback (Spec.map φ)).mapIso eG) hpullTilde

/-- The ring map and module on any compatible pair of affine opens have the finite type
hypotheses needed by affine generic flatness. -/
private theorem affineFiniteData
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    (f.appLE V.1 U.1 hUV).hom.FiniteType ∧
      Module.Finite Γ(X, U.1) Γ(F, U.1) :=
  ⟨f.finiteType_appLE V.2 U.2 hUV, moduleFinite_sections_on_affine F U⟩

/-- The inverse image of an affine open under a quasi-compact morphism is covered by finitely
many affine opens of the source. -/
private theorem exists_finite_affine_cover_preimage
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (V : S.affineOpens) :
    ∃ s : Set X.affineOpens, s.Finite ∧
      f ⁻¹ᵁ V.1 = ⨆ U ∈ s, (U : X.Opens) := by
  have hcompact : IsCompact (f ⁻¹' (V.1 : Set S)) := f.isCompact_preimage V.2.isCompact
  have hopen : IsOpen (f ⁻¹' (V.1 : Set S)) := V.1.2.preimage f.continuous
  obtain ⟨s, hs, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hcompact, hopen⟩
  refine ⟨s, hs, ?_⟩
  apply SetLike.coe_injective
  simpa only [Scheme.Hom.coe_preimage, Opens.coe_iSup] using hcover

/-- The finite affine cover over a base chart together with its common dense good locus. -/
private structure AffineCommonGoodData
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (V : S.affineOpens) where
  charts : Set X.affineOpens
  charts_finite : charts.Finite
  charts_cover : f ⁻¹ᵁ V.1 = ⨆ U ∈ charts, (U : X.Opens)
  goodLocus : Set (PrimeSpectrum Γ(S, V.1))
  goodLocus_open : IsOpen goodLocus
  goodLocus_dense : Dense goodLocus
  goodAt : ∀ x, x ∈ goodLocus → ∃ a : Γ(S, V.1), x ∈ basicOpen a ∧
    (basicOpen a : Set (PrimeSpectrum Γ(S, V.1))) ⊆ goodLocus ∧
    (∀ (U : X.affineOpens) (hU : U ∈ charts),
      let hUV : U.1 ≤ f ⁻¹ᵁ V.1 := by
        rw [charts_cover]
        exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
      letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
        (f.appLE V.1 U.1 hUV).hom.toAlgebra
      Algebra.IsFinitePresentationFreeAway Γ(S, V.1)
        Γ(X, U.1) Γ(F, U.1) a) ∧
    (∀ (U U' : X.affineOpens) (hU : U ∈ charts) (_hU' : U' ∈ charts),
      let hUV : U.1 ≤ f ⁻¹ᵁ V.1 := by
        rw [charts_cover]
        exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
      letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
        (f.appLE V.1 U.1 hUV).hom.toAlgebra
      Algebra.IsFinitePresentationFreeAway Γ(S, V.1)
        Γ(X, U.1) (Γ(X, U.1) ⧸ affineOverlapIdeal U U') a)

/-- On an affine part of the base, the finitely many affine charts in a quasi-compact
preimage have a common dense open where their coordinate algebras, section modules, and pairwise
overlap quotients satisfy the affine generic-flatness conclusion. -/
private theorem exists_dense_open_affine_common_good
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (V : S.affineOpens) :
    Nonempty (AffineCommonGoodData f F V) := by
  classical
  obtain ⟨s, hs, hcover⟩ := exists_finite_affine_cover_preimage f V
  let ι := {U : X.affineOpens // U ∈ s}
  let : Fintype ι := hs.fintype
  let R := Γ(S, V.1)
  let B (i : ι) : Type u := Γ(X, i.1.1)
  let M (i : ι) : Type u := Γ(F, i.1.1)
  have hUV (i : ι) : i.1.1 ≤ f ⁻¹ᵁ V.1 := by
    rw [hcover]
    exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  let hAlg : ∀ i, Algebra R (B i) := fun i =>
    (f.appLE V.1 i.1.1 (hUV i)).hom.toAlgebra
  have hdata (i : ι) :
      (f.appLE V.1 i.1.1 (hUV i)).hom.FiniteType ∧
        Module.Finite Γ(X, i.1.1) Γ(F, i.1.1) :=
    affineFiniteData f F V i.1 (hUV i)
  have : ∀ i, Algebra.FiniteType R (B i) := fun i =>
      (RingHom.finiteType_algebraMap (A := R) (B := B i)).mp (by
      have hmap : algebraMap R (B i) = (f.appLE V.1 i.1.1 (hUV i)).hom := by
        simpa [hAlg, R, B, hUV] using
          (RingHom.algebraMap_toAlgebra (f.appLE V.1 i.1.1 (hUV i)).hom)
      rw [hmap]
      exact (hdata i).1)
  have : ∀ i, Module.Finite (B i) (M i) := fun i => hdata i |>.2
  let ι' := ι ⊕ (ι × ι)
  let B' (j : ι') : Type u := match j with
    | Sum.inl i => B i
    | Sum.inr ij => B ij.1
  let M' (j : ι') : Type u := match j with
    | Sum.inl i => M i
    | Sum.inr ij => B ij.1 ⧸ affineOverlapIdeal ij.1.1 ij.2.1
  let : ∀ j, CommRing (B' j) := fun j => by
    cases j with
    | inl i => exact inferInstance
    | inr ij => exact inferInstance
  let : ∀ j, Algebra R (B' j) := fun j => by
    cases j with
    | inl i => exact hAlg i
    | inr ij => exact hAlg ij.1
  let : ∀ j, AddCommGroup (M' j) := fun j => by
    cases j with
    | inl i => exact inferInstance
    | inr ij => exact inferInstance
  let : ∀ j, Module (B' j) (M' j) := fun j => by
    cases j with
    | inl i => exact inferInstance
    | inr ij => exact inferInstance
  have : ∀ j, Algebra.FiniteType R (B' j) := fun j => by
    cases j with
    | inl i => exact inferInstance
    | inr ij => exact inferInstance
  have : ∀ j, Module.Finite (B' j) (M' j) := fun j => by
    cases j with
    | inl i => exact hdata i |>.2
    | inr ij =>
      exact Module.Finite.of_surjective
        (Algebra.linearMap (B ij.1) (B ij.1 ⧸ affineOverlapIdeal ij.1.1 ij.2.1))
        (by
          intro x
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact ⟨b, rfl⟩)
  obtain ⟨W, hWopen, hWdense, hgood⟩ :=
    exists_dense_open_common_good (R := R) (ι := ι') (B := B') (M := M')
  let GoodElement := {a : R // ∀ k : ι',
    Algebra.IsFinitePresentationFreeAway R (B' k) (M' k) a}
  let goodLocus : Set (PrimeSpectrum R) :=
    ⋃ a : GoodElement, (basicOpen a.1 : Set (PrimeSpectrum R))
  have hgoodOpen : IsOpen goodLocus := isOpen_iUnion fun a => PrimeSpectrum.isOpen_basicOpen
  have hWgood : W ⊆ goodLocus := by
    intro x hx
    have hpoint : ∀ k : ι', ∃ a : R, x ∈ basicOpen a ∧
        Algebra.IsFinitePresentationFreeAway R (B' k) (M' k) a :=
      fun k => hgood k x hx
    obtain ⟨a, hxa, hall⟩ := exists_common_basicOpen_good B' M' hpoint
    exact Set.mem_iUnion.mpr ⟨⟨a, hall⟩, hxa⟩
  have hgoodDense : Dense goodLocus := hWdense.mono hWgood
  refine ⟨{
    charts := s
    charts_finite := hs
    charts_cover := hcover
    goodLocus := goodLocus
    goodLocus_open := hgoodOpen
    goodLocus_dense := hgoodDense
    goodAt := ?_ }⟩
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨⟨a, hall⟩, hxa⟩
  refine ⟨a, hxa, ?_, ?_, ?_⟩
  · intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨a, hall⟩, hz⟩
  · intro U hU
    let i : ι := ⟨U, hU⟩
    let : Algebra Γ(S, V.1) Γ(X, U.1) :=
      (f.appLE V.1 U.1 (by
        rw [hcover]
        exact le_iSup_of_le U (le_iSup_of_le hU le_rfl))).hom.toAlgebra
    let : Module Γ(X, U.1) Γ(F, U.1) := inferInstance
    have hAlgEq : hAlg i = (f.appLE V.1 U.1
        (by
          rw [hcover]
          exact le_iSup_of_le U (le_iSup_of_le hU le_rfl))).hom.toAlgebra := rfl
    simpa [i, B, M, R, hUV, hAlgEq] using hall (Sum.inl i)
  · intro U U' hU hU'
    let i : ι := ⟨U, hU⟩
    let j : ι := ⟨U', hU'⟩
    let : Algebra Γ(S, V.1) Γ(X, U.1) :=
      (f.appLE V.1 U.1 (by
        rw [hcover]
        exact le_iSup_of_le U (le_iSup_of_le hU le_rfl))).hom.toAlgebra
    have hAlgEq : hAlg i = (f.appLE V.1 U.1
        (by
          rw [hcover]
          exact le_iSup_of_le U (le_iSup_of_le hU le_rfl))).hom.toAlgebra := rfl
    simpa [i, j, B', M', B, M, R, hUV, hAlgEq] using hall (Sum.inr (i, j))

/-- A choice of common good data over an affine open of the base. -/
private noncomputable def affineCommonGoodDataChoice
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (V : S.affineOpens) :
    AffineCommonGoodData f F V :=
  Classical.choice (exists_dense_open_affine_common_good f F V)

/-- The open subset of an affine open of the base over which the chosen common good data holds,
viewed as an open of the base. -/
private noncomputable def affineCommonGoodChartOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (V : S.affineOpens) : S.Opens := by
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  exact V.2.fromSpec ''ᵁ
    ⟨(affineCommonGoodDataChoice f F V).goodLocus,
      (affineCommonGoodDataChoice f F V).goodLocus_open⟩

/-- The common good loci on all affine base charts assemble to a dense open of the base. -/
private noncomputable def affineCommonGoodOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : S.Opens :=
  ⨆ V : S.affineOpens, affineCommonGoodChartOpen f F V

/-- The open subset of the base over which all affine generic-flatness conclusions hold is
dense. -/
private theorem affineCommonGoodOpen_dense
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Dense (affineCommonGoodOpen f F : Set S) := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨y, hy⟩ := hOne
  obtain ⟨Vset, hVaff, hyV, hVO⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hy hO
  obtain ⟨V₀, hVeq⟩ := hVaff
  let V : S.affineOpens := ⟨V₀, hVeq.1⟩
  have hVaff' : IsAffineOpen V.1 := V.2
  have hyV' : y ∈ (V.1 : Set S) := hVeq.2 ▸ hyV
  have hVO' : (V.1 : Set S) ⊆ O := hVeq.2.symm ▸ hVO
  let D := affineCommonGoodDataChoice f F V
  have hrange : Set.range hVaff'.fromSpec = (V.1 : Set S) := by
    rw [← Scheme.Hom.coe_opensRange, hVaff'.opensRange_fromSpec]
  obtain ⟨p, hp⟩ := Set.mem_range.mp (hrange.symm ▸ hyV')
  obtain ⟨q, hq⟩ := D.goodLocus_dense.inter_open_nonempty Set.univ isOpen_univ
    ⟨p, Set.mem_univ p⟩
  have hqV : hVaff'.fromSpec q ∈ (V.1 : Set S) := hrange ▸ Set.mem_range_self q
  have hqO : hVaff'.fromSpec q ∈ O := hVO' hqV
  have hqGoodOpen : hVaff'.fromSpec q ∈ affineCommonGoodOpen f F := by
    change hVaff'.fromSpec q ∈ (⨆ W : S.affineOpens,
      affineCommonGoodChartOpen f F W : S.Opens)
    exact Opens.mem_iSup.mpr ⟨V, by
      change hVaff'.fromSpec q ∈ affineCommonGoodChartOpen f F V
      exact ⟨q, hq.2, rfl⟩⟩
  exact ⟨hVaff'.fromSpec q, ⟨hqO, hqGoodOpen⟩⟩

/-- A point in the assembled good open belongs to one of the affine good loci. -/
private theorem mem_affineCommonGoodOpen_iff
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (y : S) :
    y ∈ affineCommonGoodOpen f F ↔
      ∃ V : S.affineOpens, ∃ p : PrimeSpectrum Γ(S, V.1),
        V.2.fromSpec p = y ∧ p ∈ (affineCommonGoodDataChoice f F V).goodLocus := by
  change y ∈ (⨆ V : S.affineOpens, affineCommonGoodChartOpen f F V : S.Opens) ↔ _
  rw [Opens.mem_iSup]
  constructor
  · rintro ⟨V, ⟨p, hp, rfl⟩⟩
    exact ⟨V, p, rfl, hp⟩
  · rintro ⟨V, p, rfl, hp⟩
    exact ⟨V, p, hp, rfl⟩

/-- Every point of the good open subset of the base lies in a basic open set of some affine open
on which the chosen common good data holds. -/
private theorem exists_affine_common_good_at_mem
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {y : S}
    (hy : y ∈ affineCommonGoodOpen f F) :
    ∃ (V : S.affineOpens) (p : PrimeSpectrum Γ(S, V.1)),
      V.2.fromSpec p = y ∧
      ∃ a : Γ(S, V.1), p ∈ basicOpen a ∧
        (basicOpen a : Set (PrimeSpectrum Γ(S, V.1))) ⊆
          (affineCommonGoodDataChoice f F V).goodLocus ∧
        (∀ (U : X.affineOpens) (hU : U ∈ (affineCommonGoodDataChoice f F V).charts),
          let hUV : U.1 ≤ f ⁻¹ᵁ V.1 := by
            rw [(affineCommonGoodDataChoice f F V).charts_cover]
            exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
          letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
            (f.appLE V.1 U.1 hUV).hom.toAlgebra
          Algebra.IsFinitePresentationFreeAway Γ(S, V.1)
            Γ(X, U.1) Γ(F, U.1) a) ∧
        (∀ (U U' : X.affineOpens)
          (hU : U ∈ (affineCommonGoodDataChoice f F V).charts)
          (_hU' : U' ∈ (affineCommonGoodDataChoice f F V).charts),
          let hUV : U.1 ≤ f ⁻¹ᵁ V.1 := by
            rw [(affineCommonGoodDataChoice f F V).charts_cover]
            exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
          letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
            (f.appLE V.1 U.1 hUV).hom.toAlgebra
          Algebra.IsFinitePresentationFreeAway Γ(S, V.1)
            Γ(X, U.1) (Γ(X, U.1) ⧸ affineOverlapIdeal U U') a) := by
  obtain ⟨V, p, hpy, hp⟩ := (mem_affineCommonGoodOpen_iff f F y).mp hy
  exact ⟨V, p, hpy, (affineCommonGoodDataChoice f F V).goodAt p hp⟩

section

/-- The preimage of a quasi-separated set under an open embedding is quasi-separated. -/
private theorem isQuasiSeparated_preimage_of_isOpenEmbedding
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {j : A → B} (hj : Topology.IsOpenEmbedding j) {T : Set B}
    (hT : IsQuasiSeparated T) : IsQuasiSeparated (j ⁻¹' T) := by
  intro V W hVT hVo hVc hWT hWo hWc
  rw [hj.isEmbedding.isCompact_iff, Set.image_inter hj.injective]
  exact hT _ _ (Set.image_subset_iff.mpr hVT) (hj.isOpenMap _ hVo)
    (hVc.image hj.continuous) (Set.image_subset_iff.mpr hWT)
    (hj.isOpenMap _ hWo) (hWc.image hj.continuous)

/-- Quasi-separatedness of morphisms is Zariski-local at the target.  Mathlib derives this from
its affine characterisation; the affine target property is named here rather than being left
to instance search. -/
@[sga "4 IV 8.5.5" "Zariski target coverings"]
private theorem isZariskiLocalAtTarget_quasiSeparated :
    IsZariskiLocalAtTarget @QuasiSeparated :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat

/-- The dense open of the base produced for generic flatness has quasi-separated restricted
morphism. -/
private theorem affineCommonGoodOpen_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    QuasiSeparated (f.resLE (affineCommonGoodOpen f F)
      (f ⁻¹ᵁ affineCommonGoodOpen f F) le_rfl) := by
  let U := affineCommonGoodOpen f F
  let g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  have := isZariskiLocalAtTarget_quasiSeparated
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @QuasiSeparated)
  intro y
  obtain ⟨V, p, hpy, a, hpa, _, _, hgood⟩ :=
    exists_affine_common_good_at_mem f F (y := U.ι y) y.2
  let O : U.toScheme.Opens := U.ι ⁻¹ᵁ S.basicOpen a
  have hy : y ∈ O := by
    change U.ι y ∈ S.basicOpen a
    rw [← hpy, ← V.2.fromSpec_image_basicOpen]
    exact ⟨p, hpa, rfl⟩
  refine ⟨O, hy, ?_⟩
  have hqs := affineGood_preimage_isQuasiSeparated f V
    (affineCommonGoodDataChoice f F V).charts
    (affineCommonGoodDataChoice f F V).charts_cover a hgood
  have hqs' : IsQuasiSeparated (g ⁻¹ᵁ O : Set (f ⁻¹ᵁ U).toScheme) := by
    have ht := isQuasiSeparated_preimage_of_isOpenEmbedding
      (f ⁻¹ᵁ U).ι.isOpenEmbedding hqs
    convert ht using 1
    ext x
    have hx : (g x).1 = f x.1 := Scheme.Hom.coe_resLE_apply f le_rfl x
    change (g x).1 ∈ S.basicOpen a ↔ f x.1 ∈ S.basicOpen a
    exact iff_of_eq (congrArg (fun z : S => z ∈ S.basicOpen a) hx)
  have : QuasiSeparatedSpace (g ⁻¹ᵁ O).toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (g ⁻¹ᵁ O).2).mp hqs'
  infer_instance

end

/-- A quasi-coherent module on an affine scheme is flat over an affine base as soon as its module
of global sections is flat over the ring of the base. -/
private theorem flatOver_spec_of_flat_sections
    {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (G : (Spec B).Modules) [G.IsQuasicoherent]
    (h : letI : Module A (moduleSpecΓFunctor.obj G) := Module.compHom _ φ.hom
      Module.Flat A (moduleSpecΓFunctor.obj G)) :
    AlgebraicGeometry.IsFlatOver (Spec.map φ).toLRSHom.toShHom G := by
  let g := Spec.map φ
  let N := moduleSpecΓFunctor.obj G
  let R := Γ(Spec A, ⊤)
  let : Algebra R A := (Scheme.ΓSpecIso A).hom.hom.toAlgebra
  let : Module A N := Module.compHom _ φ.hom
  let : Module R N := Module.compHom _ (Scheme.ΓSpecIso A).hom.hom
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom))
  have : Module.Flat A N := h
  have : Module.Flat R N := Module.Flat.trans R A N
  apply ((AlgebraicGeometry.isFlatOver_tfae g G).out 4 1).mp
  refine ⟨PUnit.{u+1}, fun _ => ⊤, ?_, fun _ => isAffineOpen_top _, fun _ =>
    ⟨PUnit.{u+1}, fun _ => ⊤, ?_, fun _ => isAffineOpen_top _, fun _ => ?_⟩⟩
  · simp [IsOpenCover]
  · simp
  · let : Module R Γ(G, ⊤) := Module.compHom _ (g.appLE ⊤ ⊤ (by simp)).hom
    let e : N ≃ₗ[R] Γ(G, ⊤) :=
      { AddEquiv.refl _ with
        map_smul' := by
          intro r m
          change (φ.hom ((Scheme.ΓSpecIso A).hom r)) • m =
            @SMul.smul Γ(Spec B, ⊤) Γ(G, ⊤) inferInstance
              ((g.appLE ⊤ ⊤ (by simp)).hom r) m
          have heq : (Scheme.ΓSpecIso B).inv (φ.hom ((Scheme.ΓSpecIso A).hom r)) =
              g.appTop r := by
            change (((Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv) r) = _
            rw [Scheme.ΓSpecIso_inv_naturality φ, Iso.hom_inv_id_assoc]
          change @SMul.smul Γ(Spec B, ⊤) Γ(G, ⊤) inferInstance
            ((Scheme.ΓSpecIso B).inv (φ.hom ((Scheme.ΓSpecIso A).hom r))) m = _
          rw [heq]
          rfl }
    exact (Module.Flat.equiv_iff e).mp inferInstance

/-- Over a basic affine chart where the good-away condition holds, the pullback of the module to
the localized chart is flat over the localized base. -/
private theorem affineGood_pullback_flat
    {R B M : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] (a : R)
    (h : Algebra.IsFinitePresentationFreeAway R B M a)
    (G : (Spec (CommRingCat.of B)).Modules) [G.IsQuasicoherent]
    (eN : (moduleSpecΓFunctor.obj G : Type u) ≃ₗ[B] M) :
    let C := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
    AlgebraicGeometry.IsFlatOver
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away a) C))).toLRSHom.toShHom
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))).obj G) := by
  let A := Localization.Away a
  let C := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let φ : CommRingCat.of B ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap B C)
  let ψ : CommRingCat.of A ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap A C)
  have : IsOpenImmersion (Spec.map φ) := isOpenImmersion_spec_map_localization B a
  let N := moduleSpecΓFunctor.obj G
  let N' := (ModuleCat.extendScalars (algebraMap B C)).obj N
  let H := (Scheme.Modules.pullback (Spec.map φ)).obj G
  have : H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of C)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).app G) inferInstance
  let e : H ≅ tilde N' :=
    ((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso G.fromTildeΓ)).symm ≪≫
      (AlgebraicGeometry.pullbackTildeIso
        (CommRingCat.of B) (CommRingCat.of C) φ).app N
  let eΓ : (moduleSpecΓFunctor (R := CommRingCat.of C)).obj H ≅
      (moduleSpecΓFunctor (R := CommRingCat.of C)).obj (tilde N') :=
    (moduleSpecΓFunctor (R := CommRingCat.of C)).mapIso e
  let eT : (moduleSpecΓFunctor (R := CommRingCat.of C)).obj (tilde N') ≅ N' :=
    ((tilde.toTildeΓNatIso (R := CommRingCat.of C)).app N').symm
  let e' : ((moduleSpecΓFunctor (R := CommRingCat.of C)).obj H : Type u) ≃ₗ[C] N' :=
    (eΓ ≪≫ eT).toLinearEquiv
  let e'' : N' ≃ₗ[C] C ⊗[B] M := (moduleExtendScalarsTensorEquiv N).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eN)
  let : Module A N' := Module.compHom _ ψ.hom
  let : Module A (moduleSpecΓFunctor.obj H) := Module.compHom _ ψ.hom
  let : Module A (C ⊗[B] M) := Module.compHom _ ψ.hom
  have : IsScalarTower A C N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A C (moduleSpecΓFunctor.obj H) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A C (C ⊗[B] M) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Free A (C ⊗[B] M) := h.2.2.2
  let eA : ((moduleSpecΓFunctor.obj H : Type u)) ≃ₗ[A] (C ⊗[B] M) :=
    { (e'.trans e'').toAddEquiv with
      map_smul' := fun r x => (e'.trans e'').map_smul (ψ.hom r) x }
  have hf : Module.Flat A (moduleSpecΓFunctor.obj H) :=
    (Module.Flat.equiv_iff eA).mpr inferInstance
  exact flatOver_spec_of_flat_sections ψ H hf

/-- Every point over the good open subset of the base has a compatible pair of affine charts and
a section of the base on whose basic open set the good-away condition holds. -/
private theorem exists_affine_good_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : (f ⁻¹ᵁ affineCommonGoodOpen f F).toScheme) :
    ∃ (V : S.affineOpens) (W : X.affineOpens) (hWV : W.1 ≤ f ⁻¹ᵁ V.1)
      (a : Γ(S, V.1)),
      S.basicOpen a ≤ affineCommonGoodOpen f F ∧
      x.1 ∈ X.basicOpen ((f.appLE V.1 W.1 hWV).hom a) ∧
      (letI := (f.appLE V.1 W.1 hWV).hom.toAlgebra
       Algebra.IsFinitePresentationFreeAway Γ(S, V.1) Γ(X, W.1) Γ(F, W.1) a) := by
  obtain ⟨V, p, hpy, a, hpa, hsub, hgood, _⟩ :=
    exists_affine_common_good_at_mem f F (y := f x.1) x.2
  have hybasic : f x.1 ∈ S.basicOpen a := by
    rw [← hpy, ← V.2.fromSpec_image_basicOpen]
    exact ⟨p, hpa, rfl⟩
  have hyV : f x.1 ∈ V.1 := S.basicOpen_le a hybasic
  let D := affineCommonGoodDataChoice f F V
  have hxV : x.1 ∈ f ⁻¹ᵁ V.1 := hyV
  rw [D.charts_cover] at hxV
  obtain ⟨W, hx⟩ := Opens.mem_iSup.mp hxV
  obtain ⟨hW, hxW⟩ := Opens.mem_iSup.mp hx
  have hWV : W.1 ≤ f ⁻¹ᵁ V.1 := by
    rw [D.charts_cover]
    exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)
  refine ⟨V, W, hWV, a, ?_, ?_, hgood W hW⟩
  · rw [← V.2.fromSpec_image_basicOpen]
    rintro _ ⟨q, hq, rfl⟩
    exact le_iSup (fun V => affineCommonGoodChartOpen f F V) V ⟨q, hsub hq, rfl⟩
  · simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨hxW, hybasic⟩

/-- Every point over the good open subset of the base lies in the range of an open immersion
along which the module becomes flat and finitely presented over the base. -/
private theorem exists_openImmersion_sheaf_good
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : (f ⁻¹ᵁ affineCommonGoodOpen f F).toScheme) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ (f ⁻¹ᵁ affineCommonGoodOpen f F).toScheme),
      IsOpenImmersion j ∧ x ∈ Set.range j ∧
      AlgebraicGeometry.IsFlatOver
        (j ≫ f.resLE (affineCommonGoodOpen f F)
          (f ⁻¹ᵁ affineCommonGoodOpen f F) le_rfl).toLRSHom.toShHom
        ((Scheme.Modules.pullback j).obj (F.restrict (f ⁻¹ᵁ affineCommonGoodOpen f F).ι)) ∧
      ((Scheme.Modules.pullback j).obj
        (F.restrict (f ⁻¹ᵁ affineCommonGoodOpen f F).ι)).IsFinitePresentation := by
  let U := affineCommonGoodOpen f F
  let g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  let F' := F.restrict (f ⁻¹ᵁ U).ι
  obtain ⟨V, W, hWV, a, haU, hx, hgood⟩ := exists_affine_good_neighborhood f F x
  let R := Γ(S, V.1)
  let B := Γ(X, W.1)
  let k : R ⟶ B := f.appLE V.1 W.1 hWV
  let : Algebra R B := k.hom.toAlgebra
  let A := Localization.Away a
  let C := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let φ : B ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap B C)
  let ρ : R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  let ψ : CommRingCat.of A ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap A C)
  have : IsLocalization.Away (k.hom a) C := isLocalization_away_algebraMapSubmonoid B a
  have : IsOpenImmersion (Spec.map φ) := isOpenImmersion_spec_map_localization B a
  have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let j₀ := Spec.map φ ≫ W.2.fromSpec
  let i₀ := Spec.map ρ ≫ V.2.fromSpec
  let q := Spec.map ψ
  have hjrange : Set.range j₀ = (X.basicOpen (k.hom a) : Set X) :=
    range_localized_affineChart W (k.hom a) C
  have hirange : Set.range i₀ = (S.basicOpen a : Set S) :=
    range_localized_affineChart V a A
  have hcomm : j₀ ≫ f = q ≫ i₀ := by
    calc
      j₀ ≫ f = Spec.map φ ≫ (Spec.map k ≫ V.2.fromSpec) := by
        dsimp [j₀, k]
        rw [Category.assoc]
        exact congrArg (fun z : Spec B ⟶ S => Spec.map φ ≫ z)
          (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 hWV).symm
      _ = Spec.map (k ≫ φ) ≫ V.2.fromSpec := by rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (ρ ≫ ψ) ≫ V.2.fromSpec := by
        congr 2
        ext r
        change algebraMap B C (algebraMap R B r) = algebraMap A C (algebraMap R A r)
        simp only [← IsScalarTower.algebraMap_apply]
      _ = q ≫ i₀ := by simp [q, i₀, Spec.map_comp, Category.assoc]
  have hiU : Set.range i₀ ⊆ Set.range U.ι := by
    rw [hirange, Scheme.Opens.range_ι]
    exact haU
  have hjU : Set.range j₀ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have heq := congrArg (fun t : Spec (CommRingCat.of C) ⟶ S => t z) hcomm
    change f (j₀ z) = i₀ (q z) at heq
    change f (j₀ z) ∈ U
    rw [heq]
    apply haU
    change i₀ (q z) ∈ (S.basicOpen a : Set S)
    exact hirange ▸ Set.mem_range_self (q z)
  let j := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι j₀ hjU
  let i := IsOpenImmersion.lift U.ι i₀ hiU
  have : IsOpenImmersion j := inferInstance
  have : IsOpenImmersion i := inferInstance
  have hj : j ≫ (f ⁻¹ᵁ U).ι = j₀ := IsOpenImmersion.lift_fac _ _ _
  have hi : i ≫ U.ι = i₀ := IsOpenImmersion.lift_fac _ _ _
  have heq : j ≫ g = q ≫ i := by
    apply (cancel_mono U.ι).mp
    calc
      (j ≫ g) ≫ U.ι = j ≫ (g ≫ U.ι) := Category.assoc _ _ _
      _ = j ≫ ((f ⁻¹ᵁ U).ι ≫ f) := by rw [Scheme.Hom.resLE_comp_ι]
      _ = (j ≫ (f ⁻¹ᵁ U).ι) ≫ f := (Category.assoc _ _ _).symm
      _ = j₀ ≫ f := by rw [hj]
      _ = q ≫ i₀ := hcomm
      _ = (q ≫ i) ≫ U.ι := by rw [Category.assoc, hi]
  let G := F.restrict W.2.fromSpec
  let H := (Scheme.Modules.pullback (Spec.map φ)).obj G
  let e₁ : (Scheme.Modules.pullback j).obj F' ≅
      (Scheme.Modules.pullback j₀).obj F :=
    (Scheme.Modules.pullback j).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app F) ≪≫
      (Scheme.Modules.pullbackComp j (f ⁻¹ᵁ U).ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hj).app F
  let e₂ : H ≅ (Scheme.Modules.pullback j₀).obj F :=
    (Scheme.Modules.pullback (Spec.map φ)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback W.2.fromSpec).app F) ≪≫
      (Scheme.Modules.pullbackComp (Spec.map φ) W.2.fromSpec).app F
  let e := e₁ ≪≫ e₂.symm
  have hflat : AlgebraicGeometry.IsFlatOver q.toLRSHom.toShHom H :=
    affineGood_pullback_flat a hgood G (affineSectionsLinearEquiv F W.2)
  have hfp : H.IsFinitePresentation :=
    affineGood_pullback_finitePresentation a hgood G (affineSectionsLinearEquiv F W.2)
  refine ⟨Spec (CommRingCat.of C), j, inferInstance, ?_, ?_, ?_⟩
  · have hx' : x.1 ∈ (X.basicOpen (k.hom a) : Set X) := hx
    rw [← hjrange] at hx'
    obtain ⟨z, hz⟩ := hx'
    exact ⟨z, (f ⁻¹ᵁ U).ι.isOpenEmbedding.injective
      ((congrArg (fun t : Spec (CommRingCat.of C) ⟶ X => t z) hj).trans hz)⟩
  · have hc := (AlgebraicGeometry.isFlatOver_comp_iff_of_etale q i H).mpr hflat
    rw [← heq] at hc
    intro z
    exact (isFlatOverAt_iff_of_moduleIso (j ≫ g).toLRSHom.toShHom e z).mpr (hc z)
  · exact (SheafOfModules.isFinitePresentation
      (Spec (CommRingCat.of C)).ringCatSheaf).prop_of_iso e.symm hfp

/-- Over the good open subset of the base the module is flat and finitely presented. -/
private theorem affineCommonGoodOpen_sheaf_properties
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    AlgebraicGeometry.IsFlatOver
      (f.resLE (affineCommonGoodOpen f F) (f ⁻¹ᵁ affineCommonGoodOpen f F) le_rfl).toLRSHom.toShHom
      (F.restrict (f ⁻¹ᵁ affineCommonGoodOpen f F).ι) ∧
    (F.restrict (f ⁻¹ᵁ affineCommonGoodOpen f F).ι).IsFinitePresentation := by
  classical
  let U := affineCommonGoodOpen f F
  let g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  let G := F.restrict (f ⁻¹ᵁ U).ι
  let Y (x : (f ⁻¹ᵁ U).toScheme) := (exists_openImmersion_sheaf_good f F x).choose
  let j (x : (f ⁻¹ᵁ U).toScheme) : Y x ⟶ (f ⁻¹ᵁ U).toScheme :=
    (exists_openImmersion_sheaf_good f F x).choose_spec.choose
  have hs (x : (f ⁻¹ᵁ U).toScheme) :=
    (exists_openImmersion_sheaf_good f F x).choose_spec.choose_spec
  have : ∀ x, IsOpenImmersion (j x) := fun x => (hs x).1
  constructor
  · intro x
    obtain ⟨z, hz⟩ := (hs x).2.1
    have ht := (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
      (j x) g G z (Flat.stalkMap (j x) z)).mpr ((hs x).2.2.1 z)
    change AlgebraicGeometry.IsFlatOverAt g.toLRSHom.toShHom G ((j x) z) at ht
    have hz' : (j x) z = x := hz
    rwa [hz'] at ht
  · let 𝒰 : (f ⁻¹ᵁ U).toScheme.OpenCover := Scheme.Cover.mkOfCovers
      (f ⁻¹ᵁ U).toScheme Y j (fun x => ⟨x, (hs x).2.1⟩) (fun x => (hs x).1)
    let 𝒱 : (f ⁻¹ᵁ U).toScheme.Cover Scheme.fpqcPrecoverage :=
      { 𝒰.toPreZeroHypercover with
        mem₀ := Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ 𝒰.mem₀ }
    exact AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover G 𝒱 (fun x => (hs x).2.2.2)

/-- A ring-map property stable under composition with localizations away from an element, and
preserved by such localizations, transfers from one compatible pair of affine charts to a pair
of affine charts of the restricted morphism around a given point. -/
private theorem exists_resLE_appLE_of_appLE
    {X S : Scheme.{u}} {Q : ∀ {R T : Type u} [CommRing R] [CommRing T],
      (R →+* T) → Prop}
    (hPa : RingHom.StableUnderCompositionWithLocalizationAwayTarget Q)
    (hPl : RingHom.LocalizationAwayPreserves Q)
    (f : X ⟶ S) (U : S.Opens) (x : f ⁻¹ᵁ U)
    (U₂ : S.affineOpens) (V₂ : X.affineOpens)
    (hx₂ : (x : X) ∈ V₂.1) (e₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1)
    (h₂ : Q (f.appLE U₂ V₂ e₂).hom) :
    ∃ (U' : U.toScheme.affineOpens) (V' : (f ⁻¹ᵁ U).toScheme.affineOpens)
      (_ : x ∈ V'.1) (e' : V'.1 ≤ (f.resLE U (f ⁻¹ᵁ U) le_rfl) ⁻¹ᵁ U'.1),
      Q ((f.resLE U (f ⁻¹ᵁ U) le_rfl).appLE U' V' e').hom := by
  let iS : U.toScheme ⟶ S := U.ι
  let iX : (f ⁻¹ᵁ U).toScheme ⟶ X := (f ⁻¹ᵁ U).ι
  let V₁ : X.Opens := f ⁻¹ᵁ U
  obtain ⟨A, B, hA, hB, hxB, e, hAB⟩ :=
    exists_affineOpens_le_appLE_of_appLE (X := X) (Y := S) hPa hPl (x := (x : X))
      (U₁ := U) (U₂ := U₂) (V₁ := V₁) (V₂ := V₂) x.2 hx₂ e₂ h₂ x.2
  have hA' : A.1 ≤ iS.opensRange := by
    simpa [iS, Scheme.Opens.opensRange_ι] using hA
  have hB' : B.1 ≤ iX.opensRange := by
    simpa [iX, Scheme.Opens.opensRange_ι] using hB
  let A' : U.toScheme.affineOpens :=
    (IsOpenImmersion.affineOpensEquiv iS).symm ⟨A, hA'⟩
  let B' : (f ⁻¹ᵁ U).toScheme.affineOpens :=
    (IsOpenImmersion.affineOpensEquiv iX).symm ⟨B, hB'⟩
  have himageA : iS ''ᵁ A'.1 = A.1 := by
    have h := (IsOpenImmersion.affineOpensEquiv iS).apply_symm_apply ⟨A, hA'⟩
    have h' := congrArg (fun Z : S.affineOpens => Z.1) (congrArg Subtype.val h)
    simpa [A', IsOpenImmersion.affineOpensEquiv] using h'
  have himageB : iX ''ᵁ B'.1 = B.1 := by
    have h := (IsOpenImmersion.affineOpensEquiv iX).apply_symm_apply ⟨B, hB'⟩
    have h' := congrArg (fun Z : X.affineOpens => Z.1) (congrArg Subtype.val h)
    simpa [B', IsOpenImmersion.affineOpensEquiv] using h'
  have e' : B'.1 ≤ (f.resLE U (f ⁻¹ᵁ U) le_rfl) ⁻¹ᵁ A'.1 :=
    (Scheme.Hom.le_resLE_preimage_iff f le_rfl A'.1 B'.1).2
      (by rw [himageB, himageA]; exact e)
  have hxB' : x ∈ B'.1 := hxB
  refine ⟨A', B', hxB', e', ?_⟩
  rw [Scheme.Hom.resLE_appLE]
  exact (f.appLE_congr e himageA.symm himageB.symm (fun k => Q k.hom)).mp hAB

/-- A ring-map property satisfied by the localized charts around a good neighborhood of a point
is satisfied by a pair of affine charts of the restricted morphism around that point. -/
private theorem exists_resLE_appLE_of_good_neighborhood
    {X S : Scheme.{u}} {Q : ∀ {R T : Type u} [CommRing R] [CommRing T],
      (R →+* T) → Prop}
    (hPa : RingHom.StableUnderCompositionWithLocalizationAwayTarget Q)
    (hPl : RingHom.LocalizationAwayPreserves Q)
    (f : X ⟶ S) [IsReduced S] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : (f ⁻¹ᵁ affineCommonGoodOpen f F).toScheme)
    (hQ : ∀ (V : S.affineOpens) (W : X.affineOpens) (hWV : W.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(S, V.1)),
      RingHom.FinitePresentation (f.appLE (S.basicOpen a)
        (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a)) (by simp [Scheme.Hom.appLE])).hom ∧
      RingHom.Flat (f.appLE (S.basicOpen a)
        (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a)) (by simp [Scheme.Hom.appLE])).hom →
      Q (f.appLE (S.basicOpen a)
        (X.basicOpen ((f.appLE V.1 W.1 hWV).hom a)) (by simp [Scheme.Hom.appLE])).hom) :
    ∃ (U' : (affineCommonGoodOpen f F).toScheme.affineOpens)
      (V' : (f ⁻¹ᵁ affineCommonGoodOpen f F).toScheme.affineOpens)
      (_ : x ∈ V'.1) (e' : V'.1 ≤ (f.resLE (affineCommonGoodOpen f F)
        (f ⁻¹ᵁ affineCommonGoodOpen f F) le_rfl) ⁻¹ᵁ U'.1),
      Q ((f.resLE (affineCommonGoodOpen f F)
        (f ⁻¹ᵁ affineCommonGoodOpen f F) le_rfl).appLE U' V' e').hom := by
  obtain ⟨V, W, hWV, a, _, hx, hgood⟩ := exists_affine_good_neighborhood f F x
  let := (f.appLE V.1 W.1 hWV).hom.toAlgebra
  exact exists_resLE_appLE_of_appLE hPa hPl f _ x ⟨S.basicOpen a, V.2.basicOpen _⟩
    ⟨X.basicOpen ((f.appLE V.1 W.1 hWV).hom a), W.2.basicOpen _⟩ hx (by simp [Scheme.Hom.appLE])
    (hQ V W hWV a (affineGood_basicOpen_ringHom_properties f V W hWV a
      (isFinitePresentationFreeAway_self hgood)))

/-- **Stacks Project, Tag 052B.** A finite type morphism and a finite type
quasi-coherent module become flat and finitely presented over a common dense
open of a reduced base. -/
@[stacks 052B, ega "IV 8.9.4" "more general"]
public theorem exists_dense_open_flat_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ U : S.Opens,
      Dense (U : Set S) ∧
        Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
        AlgebraicGeometry.FinitePresentation (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
        AlgebraicGeometry.IsFlatOver
          (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom
          (F.restrict (f ⁻¹ᵁ U).ι) ∧
        (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation := by
  let hfl := RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
    (RingHom.Flat.propertyIsLocal.HoldsForLocalizationAway RingHom.Flat.containsIdentities)
  refine ⟨_, affineCommonGoodOpen_dense f F, ?_, ?_,
    (affineCommonGoodOpen_sheaf_properties f F).1,
    (affineCommonGoodOpen_sheaf_properties f F).2⟩
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Flat) hfl.1]
    intro x
    exact exists_resLE_appLE_of_good_neighborhood hfl.2
      RingHom.Flat.propertyIsLocal.localizationAwayPreserves f F x fun _ _ _ _ h => h.2
  · refine ⟨?_, ?_, affineCommonGoodOpen_quasiSeparated f F⟩
    · have hfp := RingHom.finitePresentation_stableUnderComposition
        |>.stableUnderCompositionWithLocalizationAway
          RingHom.finitePresentation_holdsForLocalizationAway
      rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
        (Q := RingHom.FinitePresentation) hfp.left]
      intro x
      exact exists_resLE_appLE_of_good_neighborhood hfp.2
        RingHom.finitePresentation_isLocal.localizationAwayPreserves f F x fun _ _ _ _ h => h.1
    · rw [Scheme.Hom.resLE_eq_morphismRestrict]
      infer_instance

end AlgebraicGeometry
