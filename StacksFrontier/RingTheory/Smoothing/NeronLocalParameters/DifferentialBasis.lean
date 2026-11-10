module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.Kaehler.Separable
public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.NeronDesingularization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.RegularParameters
import all StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.RegularParameters

/-!
# Separability and differential bases at the point of a Néron chart

In a Néron situation, with `𝔭 ⊆ A` the preimage of the maximal ideal of `Λ`, this file shows that
separability of the residue-field extension `κ(R) → κ(Λ)` passes to the residue field at `𝔭` and
to the closed fibre of the local ring at `𝔭`, and deduces that regular parameters of that closed
fibre have linearly independent differentials and extend to a basis of the module of relative
differentials of the local ring at `𝔭`.

## Main definitions

* `Stacks.Smoothing.NeronSituation.residueFieldExtension`: the algebra structure making the
  residue field of `Λ` an extension of the residue field of `R`.

## Implementation notes

Separability is a hypothesis about the residue-field extension `κ(R) → κ(Λ)`, whose algebra
structure is not canonical and therefore has to be supplied explicitly; this is what
`NeronSituation.residueFieldExtension` is for.
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.FlatFibreCriterion
open Stacks.Flatness.RegularSequenceQuotient

/-- The residue field of `Λ` as an extension of the residue field of `R`, induced by the local
homomorphism `R → Λ`. -/
@[instance_reducible]
noncomputable def NeronSituation.residueFieldExtension (S : NeronSituation) :
    Algebra (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField := by
  letI : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  exact (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
    (IsLocalRing.maximalIdeal S.Λ) (algebraMap S.R S.Λ)
    (IsLocalRing.maximalIdeal_comap (algebraMap S.R S.Λ)).symm).toAlgebra

/-- Separability descends along an injective algebra map of fields. -/
private lemma isSeparableExtension_of_injective
    {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra.IsSeparableExtension k L] (f : K →ₐ[k] L) (hf : Function.Injective f) :
    Algebra.IsSeparableExtension k K := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : Algebra.IsGeometricallyReduced k L :=
    ((Algebra.isSeparableExtension_tfae k L p).out 1 4).mp ‹_›
  have : Algebra.IsGeometricallyReduced k K := .of_injective f hf
  exact ((Algebra.isSeparableExtension_tfae k K p).out 1 4).mpr this

/-- The residue field at `𝔭` is a separable subextension of the residue field of `Λ`. -/
private lemma maximalIdealPreimage_residueField_isSeparableExtension
    (S : NeronSituation)
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension) :
    letI : Algebra (IsLocalRing.maximalIdeal S.R).ResidueField
        S.maximalIdealPreimage.ResidueField :=
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
        S.maximalIdealPreimage (algebraMap S.R S.A)
        (maximalIdealPreimage_comap S).symm).toAlgebra
    Algebra.IsSeparableExtension (IsLocalRing.maximalIdeal S.R).ResidueField
      S.maximalIdealPreimage.ResidueField := by
  let k := (IsLocalRing.maximalIdeal S.R).ResidueField
  let K := S.maximalIdealPreimage.ResidueField
  let L := (IsLocalRing.maximalIdeal S.Λ).ResidueField
  have : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  let : Algebra k L := S.residueFieldExtension
  let : Algebra k K :=
    (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
      S.maximalIdealPreimage (algebraMap S.R S.A)
      (maximalIdealPreimage_comap S).symm).toAlgebra
  let : Algebra K L :=
    (Ideal.ResidueField.map S.maximalIdealPreimage
      (IsLocalRing.maximalIdeal S.Λ) (algebraMap S.A S.Λ) rfl).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨r, rfl⟩ :=
      (IsLocalRing.maximalIdeal S.R).algebraMap_residueField_surjective x
    change (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
        (IsLocalRing.maximalIdeal S.Λ) (algebraMap S.R S.Λ)
        (IsLocalRing.maximalIdeal_comap (algebraMap S.R S.Λ)).symm)
        (algebraMap S.R k r) =
      (Ideal.ResidueField.map S.maximalIdealPreimage
        (IsLocalRing.maximalIdeal S.Λ) (algebraMap S.A S.Λ) rfl)
      ((Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
        S.maximalIdealPreimage (algebraMap S.R S.A)
        (maximalIdealPreimage_comap S).symm)
        (algebraMap S.R k r))
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply S.R S.A S.Λ r]
    exact (Ideal.ResidueField.map_algebraMap S.maximalIdealPreimage
      (IsLocalRing.maximalIdeal S.Λ) (algebraMap S.A S.Λ) rfl
      (algebraMap S.R S.A r)).symm
  exact isSeparableExtension_of_injective (IsScalarTower.toAlgHom k K L)
    (algebraMap K L).injective

private lemma cotangent_transport_injective
    {U N : Type*} [CommRing U] [AddCommGroup N] [Module U N]
    {I J : Ideal U} (h : I = J) (f : I.Cotangent →ₗ[U] N)
    (hf : Function.Injective f) :
    Function.Injective (h ▸ f : J.Cotangent →ₗ[U] N) := by
  cases h
  exact hf

private lemma cotangent_transport_apply
    {U N : Type*} [CommRing U] [AddCommGroup N] [Module U N]
    {I J : Ideal U} (h : I = J) (f : I.Cotangent →ₗ[U] N)
    {x : U} (hxI : x ∈ I) (hxJ : x ∈ J) :
    (h ▸ f : J.Cotangent →ₗ[U] N)
      (J.toCotangent ⟨x, hxJ⟩) =
    f (I.toCotangent ⟨x, hxI⟩) := by
  cases h
  rfl

/-- Minimal generators of the maximal ideal of a regular local algebra over a field have
independent differentials in the residue fibre, when the residue extension is separable. -/
@[ega "IV 17.15.9" "a ⇒ b", sga "1 II 5.9" "(i)"]
private lemma linearIndependent_differentials_of_regular_parameters
    (k U : Type*) [Field k] [CommRing U] [IsRegularLocalRing U]
    [Algebra k U] [Algebra.EssFiniteType k (IsLocalRing.ResidueField U)]
    [Algebra.IsSeparableExtension k (IsLocalRing.ResidueField U)]
    {c : ℕ} (g : Fin c → U)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal U)
    (hdim : ringKrullDim U = c) :
    LinearIndependent (IsLocalRing.ResidueField U)
      (fun i => (1 : IsLocalRing.ResidueField U) ⊗ₜ[U]
        KaehlerDifferential.D k U (g i)) := by
  let m := IsLocalRing.maximalIdeal U
  let κ := IsLocalRing.ResidueField U
  have hgm : ∀ i, g i ∈ m := fun i => by
    change g i ∈ IsLocalRing.maximalIdeal U
    rw [← hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  let y : Fin c → m := fun i => ⟨g i, hgm i⟩
  have hspanSub : Submodule.span U (Set.range y) = ⊤ := by
    apply Submodule.map_injective_of_injective
      (Submodule.injective_subtype m)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    change Ideal.span ((m.subtype) '' Set.range y) = m
    rw [← Set.range_comp]
    exact hgen
  have hspanCot : Submodule.span κ
      (Set.range fun i => m.toCotangent (y i)) = ⊤ := by
    rw [show Set.range (fun i => m.toCotangent (y i)) =
        m.toCotangent '' Set.range y from by rw [← Set.range_comp]; rfl]
    exact IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr hspanSub
  have hdimCot : Module.finrank κ (IsLocalRing.CotangentSpace U) = c := by
    calc
      Module.finrank κ (IsLocalRing.CotangentSpace U) = m.spanFinrank :=
        (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace U).symm
      _ = c := by
        have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := U)
        rw [hdim] at h
        exact_mod_cast h
  have hli : LinearIndependent κ (fun i => m.toCotangent (y i)) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hspanCot.ge
    simpa only [Fintype.card_fin] using hdimCot.symm
  have hker : RingHom.ker (algebraMap U κ) = m := by
    simpa [κ, m] using (IsLocalRing.ker_residue (R := U))
  have hinj := KaehlerDifferential.kerCotangentToTensor_injective_of_isSeparableExtension
    k U κ (by simpa [κ] using IsLocalRing.residue_surjective)
  let ψ : m.Cotangent →ₗ[U] TensorProduct U κ (KaehlerDifferential k U) :=
    hker ▸ (KaehlerDifferential.kerCotangentToTensor k U κ)
  have hψ : Function.Injective ψ :=
    cotangent_transport_injective hker
      (KaehlerDifferential.kerCotangentToTensor k U κ) hinj
  have hsurj : Function.Surjective (algebraMap U κ) := by
    simpa only [κ, IsLocalRing.ResidueField.algebraMap_eq] using
      (IsLocalRing.residue_surjective (R := U))
  let φ : m.Cotangent →ₗ[κ]
      TensorProduct U κ (KaehlerDifferential k U) :=
    ψ.extendScalarsOfSurjective hsurj
  have hφ : Function.Injective φ := hψ
  have hli' := hli.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hψg (i : Fin c) : ψ (m.toCotangent (y i)) =
      (1 : κ) ⊗ₜ[U] KaehlerDifferential.D k U (g i) := by
    change (hker ▸ KaehlerDifferential.kerCotangentToTensor k U κ)
      (m.toCotangent ⟨g i, hgm i⟩) = _
    rw [cotangent_transport_apply hker
      (KaehlerDifferential.kerCotangentToTensor k U κ)
      (hker.symm ▸ hgm i) (hgm i)]
    rfl
  simpa only [Function.comp_def, φ, LinearMap.extendScalarsOfSurjective_apply,
    hψg] using hli'

private lemma maximalIdeal_le_comap_span_uniformizer (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    IsLocalRing.maximalIdeal S.R ≤
      (Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} :
        Set (Localization.AtPrime S.maximalIdealPreimage))).comap
        (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage)) := by
  rw [hπ, Ideal.span_singleton_le_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The closed fibre of the local ring at `𝔭` carries the residue field of `R` as its
coefficient field. -/
@[instance_reducible]
private noncomputable def closedFibreAlgebra
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    Algebra (IsLocalRing.maximalIdeal S.R).ResidueField
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span
          ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _)) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let I : Ideal T := Ideal.span ({algebraMap S.R T π} : Set T)
  let m := IsLocalRing.maximalIdeal S.R
  let k := m.ResidueField
  have hle : m ≤ I.comap (algebraMap S.R T) := maximalIdeal_le_comap_span_uniformizer S π hπ
  letI : Algebra (S.R ⧸ m) (T ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  have hm : m.IsMaximal := (IsLocalRing.maximalIdeal.isMaximal S.R)
  letI : m.IsMaximal := hm
  let e : (S.R ⧸ m) ≃+* k :=
    RingEquiv.ofBijective (algebraMap (S.R ⧸ m) k)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  exact ((algebraMap (S.R ⧸ m) (T ⧸ I)).comp e.symm.toRingHom).toAlgebra

/-- Flatten a principal localization of a principal neighbourhood. -/
private lemma exists_away_algEquiv_of_away
    {A C : Type*} [CommRing A] [CommRing C] (p : Ideal A) [p.IsPrime]
    (f : A) (hf : f ∉ p) (z : Localization.Away f)
    [Algebra (Localization.Away f) C] [Algebra A C]
    [IsScalarTower A (Localization.Away f) C] [IsLocalization.Away z C]
    (hz : z ∉ p.map (algebraMap A (Localization.Away f))) :
    ∃ F : A, F ∉ p ∧
      Nonempty (Localization.Away F ≃ₐ[A]
        C) := by
  let a := (IsLocalization.Away.sec f z).1
  let F := f * a
  have hloc : IsLocalization.Away F C :=
    .mul_of_associated f a z
      (IsLocalization.Away.associated_sec_fst f z)
  let e : Localization.Away F ≃ₐ[A] C :=
    Localization.algEquiv _ _
  refine ⟨F, ?_, ⟨e⟩⟩
  refine Ideal.IsPrime.mul_notMem ‹_› hf fun hmem ↦ hz ?_
  rw [Ideal.mem_iff_of_associated
    (IsLocalization.Away.associated_sec_fst f z).symm]
  exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away f)) hmem

/-- Smoothness persists after shrinking a principal open by another element. -/
private lemma smooth_away_mul
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f g : A) [Algebra.Smooth R (Localization.Away f)] :
    Algebra.Smooth R (Localization.Away (f * g)) := by
  let B := Localization.Away f
  let C := Localization.Away (algebraMap A B g)
  have : Algebra.Smooth R C :=
    Algebra.Smooth.localization_away (algebraMap A B g)
  have : IsLocalization.Away (f * g) C :=
    IsLocalization.Away.mul' B C f g
  let e : Localization.Away (f * g) ≃ₐ[A] C :=
    Localization.algEquiv _ _
  exact Algebra.Smooth.of_equiv (e.restrictScalars R).symm

/-- A regular sequence contained in a prime stays regular after a further principal
localization avoiding that prime. -/
private lemma isRegular_away_mul
    {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime]
    (f g : A) (hf : f ∉ q) (hg : g ∉ q) (xs : List A)
    (hmem : ∀ x ∈ xs, x ∈ q)
    (hreg : RingTheory.Sequence.IsRegular (Localization.Away f)
      (xs.map (algebraMap A (Localization.Away f)))) :
    RingTheory.Sequence.IsRegular (Localization.Away (f * g))
      (xs.map (algebraMap A (Localization.Away (f * g)))) := by
  let B := Localization.Away f
  let C := Localization.Away (algebraMap A B g)
  let qB : Ideal B := q.map (algebraMap A B)
  have : qB.IsPrime := isPrime_map_algebraMap_of_notMem q hf
  have hqBg : algebraMap A B g ∉ qB := by
    intro h
    have h' : g ∈ qB.comap (algebraMap A B) := h
    have heq := IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers f) B (I := q) inferInstance
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf)
    exact hg (heq ▸ h')
  have hregC : RingTheory.Sequence.IsRegular C
      ((xs.map (algebraMap A B)).map (algebraMap B C)) :=
    isRegular_of_isLocalization_of_mem_prime
      (Submonoid.powers (algebraMap A B g)) qB
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hqBg)
      (xs.map (algebraMap A B)) hreg (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact Ideal.mem_map_of_mem _ (hmem y hy))
  have : IsLocalization.Away (f * g) C :=
    IsLocalization.Away.mul' B C f g
  let e : Localization.Away (f * g) ≃ₐ[A] C :=
    Localization.algEquiv _ _
  apply (isRegular_ringEquiv_congr e.toRingEquiv _).mpr
  have hlist : (xs.map (algebraMap A (Localization.Away (f * g)))).map e.toRingEquiv =
      (xs.map (algebraMap A B)).map (algebraMap B C) := by
    simp only [List.map_map, Function.comp_def]
    congr 1
    funext x
    change e (algebraMap A (Localization.Away (f * g)) x) = _
    rw [e.commutes]
    exact (IsScalarTower.algebraMap_apply A B C x).symm
  rwa [hlist]

/-- Equality of extended ideals persists on a smaller principal open. -/
private lemma ideal_map_away_mul
    {A : Type*} [CommRing A] (I J : Ideal A) (f g : A)
    (h : I.map (algebraMap A (Localization.Away f)) =
      J.map (algebraMap A (Localization.Away f))) :
    I.map (algebraMap A (Localization.Away (f * g))) =
      J.map (algebraMap A (Localization.Away (f * g))) := by
  let B := Localization.Away f
  let C := Localization.Away (algebraMap A B g)
  have : IsLocalization.Away (f * g) C :=
    IsLocalization.Away.mul' B C f g
  let e : Localization.Away (f * g) ≃ₐ[A] C :=
    Localization.algEquiv _ _
  apply ideal_map_injective_ringEquiv e.toRingEquiv
  have hc : e.toRingEquiv.toRingHom.comp
      (algebraMap A (Localization.Away (f * g))) =
      (algebraMap B C).comp (algebraMap A B) := by
    ext x
    change e (algebraMap A (Localization.Away (f * g)) x) = _
    rw [e.commutes]
    exact (IsScalarTower.algebraMap_apply A B C x).symm
  change Ideal.map e.toRingEquiv.toRingHom
      (Ideal.map (algebraMap A (Localization.Away (f * g))) I) =
    Ideal.map e.toRingEquiv.toRingHom
      (Ideal.map (algebraMap A (Localization.Away (f * g))) J)
  rw [Ideal.map_map, Ideal.map_map, hc]
  simpa only [Ideal.map_map] using congrArg (Ideal.map (algebraMap B C)) h

/-- The residue field of a local ring agrees with that of a local quotient. -/
private noncomputable def residueFieldEquivQuotient {T : Type*} [CommRing T] [IsLocalRing T]
    (I : Ideal T) [IsLocalRing (T ⧸ I)] :
    IsLocalRing.ResidueField T ≃+* IsLocalRing.ResidueField (T ⧸ I) :=
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (Ideal.Quotient.mk I))
    ⟨(IsLocalRing.ResidueField.map (Ideal.Quotient.mk I)).injective, fun y => by
      obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u
      exact ⟨IsLocalRing.residue T t,
        IsLocalRing.ResidueField.map_residue (Ideal.Quotient.mk I) t⟩⟩

private lemma residueFieldEquivQuotient_residue {T : Type*} [CommRing T] [IsLocalRing T]
    (I : Ideal T) [IsLocalRing (T ⧸ I)] (t : T) :
    residueFieldEquivQuotient I (IsLocalRing.residue T t) =
      IsLocalRing.residue (T ⧸ I) (Ideal.Quotient.mk I t) :=
  rfl

private lemma closedFibreAlgebra_isScalarTower (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    letI := closedFibreAlgebra S π hπ
    IsScalarTower S.R (IsLocalRing.maximalIdeal S.R).ResidueField
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span
          ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _)) := by
  let := closedFibreAlgebra S π hπ
  let T := Localization.AtPrime S.maximalIdealPreimage
  let I : Ideal T := Ideal.span ({algebraMap S.R T π} : Set T)
  let U := T ⧸ I
  let m := IsLocalRing.maximalIdeal S.R
  let k := m.ResidueField
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  let e : (S.R ⧸ m) ≃+* k :=
    RingEquiv.ofBijective (algebraMap (S.R ⧸ m) k)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  have he : e.symm (algebraMap S.R k r) = Ideal.Quotient.mk m r := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  let : Algebra (S.R ⧸ m) U :=
    Ideal.Quotient.algebraQuotientOfLEComap (maximalIdeal_le_comap_span_uniformizer S π hπ)
  change algebraMap S.R U r =
    (algebraMap (S.R ⧸ m) U) (e.symm (algebraMap S.R k r))
  rw [he]
  rfl

/-- The residue field of the closed fibre at `𝔭` is separable over the residue field of `R`. -/
private lemma isSeparableExtension_residueField_closedFibre (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    [IsLocalRing ((Localization.AtPrime S.maximalIdealPreimage) ⧸
      Ideal.span
        ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _))] :
    letI := closedFibreAlgebra S π hπ
    Algebra.IsSeparableExtension (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.ResidueField ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span
          ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _))) := by
  let := closedFibreAlgebra S π hπ
  let T := Localization.AtPrime S.maximalIdealPreimage
  let I : Ideal T := Ideal.span ({algebraMap S.R T π} : Set T)
  let U := T ⧸ I
  have : IsLocalRing U := ‹_›
  let k := (IsLocalRing.maximalIdeal S.R).ResidueField
  let K := S.maximalIdealPreimage.ResidueField
  have : IsScalarTower S.R k U := closedFibreAlgebra_isScalarTower S π hπ
  let : Algebra k K :=
    (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
      S.maximalIdealPreimage (algebraMap S.R S.A)
      (maximalIdealPreimage_comap S).symm).toAlgebra
  have hsepK : Algebra.IsSeparableExtension k K :=
    maximalIdealPreimage_residueField_isSeparableExtension S hsep
  let eK : K ≃+* IsLocalRing.ResidueField U := residueFieldEquivQuotient I
  have heK (x : k) : eK (algebraMap k K x) =
      algebraMap k (IsLocalRing.ResidueField U) x := by
    obtain ⟨r, rfl⟩ :=
      (IsLocalRing.maximalIdeal S.R).algebraMap_residueField_surjective x
    change eK ((Ideal.ResidueField.map (IsLocalRing.maximalIdeal S.R)
      S.maximalIdealPreimage (algebraMap S.R S.A)
      (maximalIdealPreimage_comap S).symm) (algebraMap S.R k r)) = _
    rw [Ideal.ResidueField.map_algebraMap]
    change residueFieldEquivQuotient I (IsLocalRing.residue T (algebraMap S.R T r)) = _
    rw [residueFieldEquivQuotient_residue,
      IsScalarTower.algebraMap_apply k U (IsLocalRing.ResidueField U)]
    congr 1
    change algebraMap S.R U r = algebraMap k U (algebraMap S.R k r)
    exact IsScalarTower.algebraMap_apply S.R k U r
  let eKa : K ≃ₐ[k] IsLocalRing.ResidueField U :=
    { __ := eK, commutes' := heK }
  exact isSeparableExtension_of_injective eKa.symm.toAlgHom eKa.symm.injective

/-- Minimal generators of the maximal ideal of a regular closed fibre `T ⧸ I` over a field `k`
with separable residue field have independent differentials in the fibre of `Ω[T⁄R]`. -/
private lemma linearIndependent_one_tmul_D_of_quotient
    {R T k : Type*} [CommRing R] [CommRing T] [Field k] [Algebra R T] [Algebra R k]
    (I : Ideal T) [IsRegularLocalRing (T ⧸ I)] [Algebra k (T ⧸ I)]
    [IsScalarTower R k (T ⧸ I)]
    [Algebra.EssFiniteType k (IsLocalRing.ResidueField (T ⧸ I))]
    [Algebra.IsSeparableExtension k (IsLocalRing.ResidueField (T ⧸ I))]
    {c : ℕ} (g₀ : Fin c → T)
    (hgen : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (g₀ i)) =
      IsLocalRing.maximalIdeal (T ⧸ I))
    (hdim : ringKrullDim (T ⧸ I) = c) :
    LinearIndependent (IsLocalRing.ResidueField (T ⧸ I)) fun i =>
      (1 : IsLocalRing.ResidueField (T ⧸ I)) ⊗ₜ[T] KaehlerDifferential.D R T (g₀ i) := by
  let U := T ⧸ I
  let κ := IsLocalRing.ResidueField U
  let gU : Fin c → U := fun i => Ideal.Quotient.mk I (g₀ i)
  have : IsScalarTower T U κ := ⟨fun t u x => by
    change (algebraMap U κ (Ideal.Quotient.mk I t * u)) * x =
      (algebraMap U κ (Ideal.Quotient.mk I t)) *
        ((algebraMap U κ u) * x)
    rw [map_mul, mul_assoc]⟩
  let θ : KaehlerDifferential R T →ₗ[T]
      TensorProduct U κ (KaehlerDifferential k U) :=
    ((TensorProduct.mk U κ (KaehlerDifferential k U) 1).restrictScalars T).comp
      (KaehlerDifferential.map R k T U)
  let θκ : TensorProduct T κ (KaehlerDifferential R T) →ₗ[κ]
      TensorProduct U κ (KaehlerDifferential k U) :=
    θ.liftBaseChange κ
  have hθ (i : Fin c) : θκ ((1 : κ) ⊗ₜ[T] KaehlerDifferential.D R T (g₀ i)) =
      (1 : κ) ⊗ₜ[U] KaehlerDifferential.D k U (gU i) := by
    simp only [θκ, LinearMap.liftBaseChange_tmul, one_smul, θ,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rfl
  apply LinearIndependent.of_comp θκ
  simpa only [Function.comp_def, hθ] using
    linearIndependent_differentials_of_regular_parameters k U gU hgen hdim

/-- Linear independence of the vectors `1 ⊗ vᵢ` passes along an isomorphism of fields over `T`. -/
private lemma linearIndependent_one_tmul_of_ringEquiv
    {T K κ M ι : Type*} [CommRing T] [Field K] [Field κ] [Algebra T K] [Algebra T κ]
    [AddCommGroup M] [Module T M] (eK : K ≃+* κ)
    (he : ∀ t, eK (algebraMap T K t) = algebraMap T κ t) (v : ι → M)
    (hli : LinearIndependent κ fun i => (1 : κ) ⊗ₜ[T] v i) :
    LinearIndependent K fun i => (1 : K) ⊗ₜ[T] v i := by
  let eKT : K ≃ₗ[T] κ :=
    { __ := eK.toAddEquiv
      map_smul' := fun t x => by
        change eK (t • x) = t • eK x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, he] }
  let τ : TensorProduct T K M ≃ₗ[T] TensorProduct T κ M :=
    TensorProduct.congr eKT (LinearEquiv.refl T M)
  have hτ (r : K) (m : TensorProduct T K M) : τ (r • m) = eK r • τ m := by
    induction m using TensorProduct.inductionOn with
    | tmul x y =>
        change (eK (r * x)) ⊗ₜ[T] y = (eK r * eK x) ⊗ₜ[T] y
        rw [map_mul]
    | add x y hx hy => simp [hx, hy, smul_add]
  have hli' := hli.map_of_injective_injectiveₛ
    eK τ.symm.toAddMonoidHom eK.injective τ.symm.injective (by
      intro r m
      apply τ.injective
      change τ (τ.symm (eK r • m)) = τ (r • τ.symm m)
      rw [τ.apply_symm_apply, hτ, τ.apply_symm_apply])
  have hs (i : ι) : τ.symm ((1 : κ) ⊗ₜ[T] v i) = (1 : K) ⊗ₜ[T] v i := by
    rw [τ.symm_apply_eq]
    change _ = (eK 1) ⊗ₜ[T] v i
    rw [map_one]
  change LinearIndependent K (fun i => τ.symm ((1 : κ) ⊗ₜ[T] v i)) at hli'
  simpa only [hs] using hli'

/-- Regular parameters of the closed fibre at `𝔭` have independent differentials in the fibre of
`Ω[A_𝔭⁄R]` at `𝔭`. -/
private lemma linearIndependent_one_tmul_D_atPrime
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) {c : ℕ}
    (g₀ : Fin c → Localization.AtPrime S.maximalIdealPreimage)
    (hdim : ringKrullDim
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span
          ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _)) = c)
    (hgen : IsLocalRing.maximalIdeal (Localization.AtPrime S.maximalIdealPreimage) =
      Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _) ⊔
        Ideal.span (Set.range g₀)) :
    LinearIndependent S.maximalIdealPreimage.ResidueField fun i =>
      (1 : S.maximalIdealPreimage.ResidueField) ⊗ₜ[Localization.AtPrime S.maximalIdealPreimage]
        KaehlerDifferential.D S.R (Localization.AtPrime S.maximalIdealPreimage) (g₀ i) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let I : Ideal T := Ideal.span ({algebraMap S.R T π} : Set T)
  let U := T ⧸ I
  have : IsRegularLocalRing U :=
    uniformizer_quotient_atPrime_isRegularLocalRing S π hπ hsm
  have hgenU : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (g₀ i)) =
      IsLocalRing.maximalIdeal U := by
    have hm := IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [← hm, hgen, Ideal.map_sup]
    change Ideal.span (Set.range fun i => Ideal.Quotient.mk I (g₀ i)) =
      Ideal.map (Ideal.Quotient.mk I) I ⊔
        Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g₀))
    rw [Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, ← Set.range_comp]
    rfl
  let k := (IsLocalRing.maximalIdeal S.R).ResidueField
  let : Algebra k U := closedFibreAlgebra S π hπ
  have : IsScalarTower S.R k U := closedFibreAlgebra_isScalarTower S π hπ
  have : Algebra.EssFiniteType S.R T := Algebra.EssFiniteType.comp S.R S.A T
  have : Algebra.EssFiniteType S.R U := Algebra.EssFiniteType.comp S.R T U
  have : Algebra.EssFiniteType k U := Algebra.EssFiniteType.of_comp S.R k U
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField U) :=
    Algebra.EssFiniteType.comp k U _
  have : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField U) :=
    isSeparableExtension_residueField_closedFibre S π hπ hsep
  exact linearIndependent_one_tmul_of_ringEquiv (residueFieldEquivQuotient I)
    (fun t => residueFieldEquivQuotient_residue I t) _
    (linearIndependent_one_tmul_D_of_quotient (R := S.R) (k := k) I g₀ hgenU hdim)

private lemma formallySmooth_atPrime_of_smoothAt (S : NeronSituation)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    Algebra.FormallySmooth S.R (Localization.AtPrime S.maximalIdealPreimage) := by
  obtain ⟨a, ha, hsma⟩ := hsm
  let T := Localization.AtPrime S.maximalIdealPreimage
  let B := Localization.Away a
  let q : Ideal B := S.maximalIdealPreimage.map (algebraMap S.A B)
  have : q.IsPrime := isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage ha
  let : Algebra B T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers a)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr ha)
  have : IsScalarTower S.A B T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower S.R B T := .to₁₃₄ _ S.A _ _
  have : IsLocalization.AtPrime T q :=
    isLocalization_atPrime_map_of_notMem (B := B) (C := T) ha
  have : Algebra.Smooth S.R B := hsma
  have : Algebra.FormallySmooth B T :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  exact Algebra.FormallySmooth.comp S.R B T

/-- The vectors `1 ⊗ dt` span the fibre of the module of differentials of a local ring. -/
private lemma span_range_one_tmul_D_eq_top {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing T] [Algebra R T] :
    Submodule.span (IsLocalRing.ResidueField T) (Set.range fun t : T =>
      (1 : IsLocalRing.ResidueField T) ⊗ₜ[T] KaehlerDifferential.D R T t) = ⊤ := by
  let K := IsLocalRing.ResidueField T
  let M := KaehlerDifferential R T
  let N : Submodule K (TensorProduct T K M) :=
    Submodule.span K (Set.range fun t : T => (1 : K) ⊗ₜ[T] KaehlerDifferential.D R T t)
  have hle : Submodule.span T (Set.range (KaehlerDifferential.D R T)) ≤
      (N.restrictScalars T).comap (TensorProduct.mk T K M 1) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨t, rfl⟩
    exact Submodule.subset_span ⟨t, rfl⟩
  rw [KaehlerDifferential.span_range_derivation] at hle
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  obtain ⟨x, rfl⟩ :=
    (TensorProduct.mk_surjective T M K (IsLocalRing.residue_surjective (R := T))) y
  exact hle trivial

/-- A linearly independent family of values of `vT`, whose values span, extends to a basis made
of values of `vT`. -/
private lemma exists_basis_extend_of_span_range {K V T : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (vT : T → V)
    (hspan : Submodule.span K (Set.range vT) = ⊤) {c : ℕ} (g₀ : Fin c → T)
    (hli : LinearIndependent K fun i => vT (g₀ i)) :
    ∃ (n : ℕ) (a : Fin n → T) (e : Fin c → Fin n), Function.Injective e ∧
      (∀ i, a (e i) = g₀ i) ∧ ∃ β : Module.Basis (Fin n) K V, ∀ i, β i = vT (a i) := by
  let v₀ : Fin c → V := fun i => vT (g₀ i)
  have hli₀ : LinearIndependent K v₀ := hli
  have hsub₀ : Set.range v₀ ⊆ Set.range vT := Set.range_comp_subset_range g₀ vT
  let ι := hli₀.linearIndepOn_id.extend hsub₀
  let β : Module.Basis ι K V :=
    Module.Basis.extendLe hli₀.linearIndepOn_id hsub₀ hspan.ge
  let j : Fin c → ι := fun i =>
    ⟨v₀ i, hli₀.linearIndepOn_id.subset_extend hsub₀ ⟨i, rfl⟩⟩
  have hj : Function.Injective j := fun _ _ h => hli₀.injective (congrArg Subtype.val h)
  have hβj (i : Fin c) : β (j i) = v₀ i :=
    Module.Basis.extendLe_apply_self hli₀.linearIndepOn_id hsub₀ hspan.ge _
  have hβrange (z : ι) : ∃ t : T, β z = vT t := by
    obtain ⟨t, ht⟩ := hli₀.linearIndepOn_id.extend_subset hsub₀ z.2
    exact ⟨t, by rw [Module.Basis.extendLe_apply_self]; exact ht.symm⟩
  let a₀ : ι → T := fun z => Classical.choose (hβrange z)
  let aT : ι → T := Function.extend j g₀ a₀
  have haTj (i : Fin c) : aT (j i) = g₀ i := hj.extend_apply g₀ a₀ i
  have hβa (z : ι) : β z = vT (aT z) := by
    by_cases hz : ∃ i, j i = z
    · obtain ⟨i, rfl⟩ := hz
      rw [haTj, hβj]
    · change β z = vT (Function.extend j g₀ a₀ z)
      rw [Function.extend_apply' g₀ a₀ z hz]
      exact Classical.choose_spec (hβrange z)
  have : Finite ι := Module.Finite.finite_basis β
  let : Fintype ι := Fintype.ofFinite ι
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => aT (eι.symm i), fun i => eι (j i), eι.injective.comp hj,
    fun i => by simp only [Equiv.symm_apply_apply, haTj], β.reindex eι, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hβa]

/-- Elements of `A_𝔭` with independent differentials in the fibre extend to a basis of
`Ω[A_𝔭⁄R]` made of differentials. -/
private lemma exists_basis_D_extend_atPrime (S : NeronSituation)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) {c : ℕ}
    (g₀ : Fin c → Localization.AtPrime S.maximalIdealPreimage)
    (hli : LinearIndependent S.maximalIdealPreimage.ResidueField fun i =>
      (1 : S.maximalIdealPreimage.ResidueField) ⊗ₜ[Localization.AtPrime S.maximalIdealPreimage]
        KaehlerDifferential.D S.R (Localization.AtPrime S.maximalIdealPreimage) (g₀ i)) :
    ∃ (n : ℕ) (a : Fin n → Localization.AtPrime S.maximalIdealPreimage) (e : Fin c → Fin n),
      Function.Injective e ∧ (∀ i, a (e i) = g₀ i) ∧
      ∃ bT : Module.Basis (Fin n) (Localization.AtPrime S.maximalIdealPreimage)
          (KaehlerDifferential S.R (Localization.AtPrime S.maximalIdealPreimage)),
        ∀ i, bT i = KaehlerDifferential.D S.R _ (a i) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let K := S.maximalIdealPreimage.ResidueField
  let M := KaehlerDifferential S.R T
  have : Algebra.FormallySmooth S.R T := formallySmooth_atPrime_of_smoothAt S hsm
  have : Algebra.EssFiniteType S.R T := Algebra.EssFiniteType.comp S.R S.A T
  have : Module.FinitePresentation T M := inferInstance
  have : Module.Flat T M := inferInstance
  have : Module.Finite K (TensorProduct T K M) := Module.Finite.base_change T K M
  obtain ⟨n, a, e, he, hae, β, hβ⟩ := exists_basis_extend_of_span_range _
    (span_range_one_tmul_D_eq_top (R := S.R) (T := T)) g₀ hli
  have hfamily :
      TensorProduct.mk T K M 1 ∘ (fun i => KaehlerDifferential.D S.R T (a i)) = β :=
    funext fun i => (hβ i).symm
  obtain ⟨bT, hbT⟩ := Module.exists_basis_of_basis_baseChange
    (fun i => KaehlerDifferential.D S.R T (a i))
    (by rw [hfamily]; exact β.linearIndependent) (by rw [hfamily]; exact β.span_eq)
    (Module.Flat.rTensor_preserves_injective_linearMap
      (IsLocalRing.maximalIdeal T).subtype Subtype.val_injective)
  exact ⟨n, a, e, he, hae, bT, hbT⟩

end Stacks.Smoothing

end
