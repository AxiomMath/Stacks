module

public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
import StacksFrontier.RingTheory.HenselizationUniverse.Basic

/-!
# The henselization after a ring map

Let `R → S` be a ring map and let `q ⊆ S` be a prime lying over `p ⊆ R`. Let `R_p → R^h` and
`S_q → S^h` be the henselizations. The local ring map `R^h → S^h` of Lemma 04GS identifies `S^h`
with the henselization of `R^h ⊗_R S` at the unique prime lying over the maximal ideal of `R^h`
and over `q`.

## Main results

* `IsLocalRing.IsHenselization.exists_isHenselization_localization_tensorProduct`: for any local
  map `f : R^h → S^h` over `R`, the prime `Q = g⁻¹(𝔪_{S^h})` of `R^h ⊗_R S`, where
  `g : R^h ⊗_R S → S^h` is induced by `f`, lies over `𝔪_{R^h}` and `q`, and `S^h` is a
  henselization of `(R^h ⊗_R S)_Q` with the same residue field.
* `IsLocalRing.IsHenselization.exists_unique_prime_isHenselization_tensorProduct`: Stacks 08HU.

## Implementation notes

The localizations `R_p`, `S_q` and the henselizations are abstract, all in one universe, as
`IsLocalRing.IsHenselization` requires. The prime of `R^h ⊗_R S` is characterized by its two
contractions and, equivalently, as the inverse image of the maximal ideal of `S^h`; the algebra
structure of `S^h` over its localization extends the canonical map from the tensor product.

## References

* [StacksProject 08HU](https://stacks.math.columbia.edu/tag/08HU)
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v

section Primes

/-- A ring map out of a localization `A` of `R` at `p` between local rings is local as soon as
`p` maps into the maximal ideal. -/
private theorem isLocalHom_of_atPrime_le {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra R A] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime A p] (φ : A →+* B)
    (h : p ≤ (maximalIdeal B).comap (φ.comp (algebraMap R A))) : IsLocalHom φ := by
  apply ((local_hom_TFAE φ).out 1 4).mpr
  rwa [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap]

/-- A local ring map from a localization at a prime extends to a local map out of it. -/
@[ega "IV 18.6.7" "partial"]
private theorem exists_algebra_atPrime {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    (g : A →+* B) (Q : Ideal A) [Q.IsPrime] (hQ : Q = (maximalIdeal B).comap g)
    (Aq : Type*) [CommRing Aq] [IsLocalRing Aq] [Algebra A Aq] [IsLocalization.AtPrime Aq Q] :
    ∃ _ : Algebra Aq B,
      IsLocalHom (algebraMap Aq B) ∧ (algebraMap Aq B).comp (algebraMap A Aq) = g := by
  have hu : ∀ y : Q.primeCompl, IsUnit (g y) := fun y =>
    notMem_maximalIdeal.mp fun hy => y.2 (hQ ▸ hy)
  refine ⟨(IsLocalization.lift hu).toAlgebra, ?_, IsLocalization.lift_comp hu⟩
  exact isLocalHom_of_atPrime_le Q (IsLocalization.lift hu)
    (by rw [IsLocalization.lift_comp hu]; exact hQ.le)

namespace StacksDraft

/-- If `π : A → K` is a surjection onto a field such that `R → K` is surjective on stalks, then a
prime of `S ⊗[R] A` containing `ker π` is determined by its contraction to `S`. -/
theorem tensorProduct_prime_eq_of_surjectiveOnStalks {R S A K : Type*} [CommRing R]
    [CommRing S] [CommRing A] [Field K] [Algebra R S] [Algebra R A] [Algebra R K]
    (π : A →ₐ[R] K) (hπ : Function.Surjective π) (hK : (algebraMap R K).SurjectiveOnStalks)
    (P Q : Ideal (S ⊗[R] A)) [P.IsPrime] [Q.IsPrime]
    (hP : RingHom.ker π ≤ P.comap Algebra.TensorProduct.includeRight)
    (hQ : RingHom.ker π ≤ Q.comap Algebra.TensorProduct.includeRight)
    (hS : P.comap (algebraMap S (S ⊗[R] A)) = Q.comap (algebraMap S (S ⊗[R] A))) : P = Q := by
  let t : S ⊗[R] A →ₐ[R] S ⊗[R] K := Algebra.TensorProduct.map (AlgHom.id R S) π
  have ht : Function.Surjective t :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hπ
  have hker : RingHom.ker t = (RingHom.ker π).map Algebra.TensorProduct.includeRight :=
    Algebra.TensorProduct.lTensor_ker π hπ
  have hc (I : Ideal (S ⊗[R] A)) (hI : RingHom.ker π ≤ I.comap Algebra.TensorProduct.includeRight) :
      (I.map t).comap t = I := by
    rw [Ideal.comap_map_of_surjective' t ht, sup_eq_left, hker]
    exact Ideal.map_le_iff_le_comap.mpr hI
  have hPk : RingHom.ker t ≤ P := hker ▸ Ideal.map_le_iff_le_comap.mpr hP
  have hQk : RingHom.ker t ≤ Q := hker ▸ Ideal.map_le_iff_le_comap.mpr hQ
  have := Ideal.map_isPrime_of_surjective ht hPk
  have := Ideal.map_isPrime_of_surjective ht hQk
  have htS : (t : S ⊗[R] A →+* S ⊗[R] K).comp (algebraMap S (S ⊗[R] A)) =
      algebraMap S (S ⊗[R] K) := by
    ext s
    simp [t]
  have he : P.map t = Q.map t := congrArg PrimeSpectrum.asIdeal
    ((PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R S K hK).injective
      (a₁ := ⟨P.map t, inferInstance⟩) (a₂ := ⟨Q.map t, inferInstance⟩) (Prod.ext
        (PrimeSpectrum.ext (by
          simp [PrimeSpectrum.tensorProductTo, ← htS, Ideal.comap_coe, hc P hP, hc Q hQ,
            hS]))
        (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm))))
  rw [← hc P hP, ← hc Q hQ, he]

/-- If `R → κ(A)` is surjective on stalks for a local `R`-algebra `A`, then a prime of `A ⊗[R] S`
lying over `𝔪_A` is determined by its contraction to `S`. -/
theorem tensorProduct_prime_eq_of_residue {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [IsLocalRing A] [Algebra R S] [Algebra R A]
    (hA : (algebraMap R (ResidueField A)).SurjectiveOnStalks) (P Q : Ideal (A ⊗[R] S))
    [P.IsPrime] [Q.IsPrime] (hP : P.comap (algebraMap A (A ⊗[R] S)) = maximalIdeal A)
    (hQ : Q.comap (algebraMap A (A ⊗[R] S)) = maximalIdeal A)
    (hS : P.comap Algebra.TensorProduct.includeRight = Q.comap Algebra.TensorProduct.includeRight) :
    P = Q := by
  let e := Algebra.TensorProduct.comm R S A
  have he (I : Ideal (A ⊗[R] S)) : (I.comap e).comap Algebra.TensorProduct.includeRight =
      I.comap (algebraMap A (A ⊗[R] S)) := by
    ext a
    simp [e]
  have he' (I : Ideal (A ⊗[R] S)) : (I.comap e).comap (algebraMap S (S ⊗[R] A)) =
      I.comap Algebra.TensorProduct.includeRight := by
    ext a
    simp [e]
  have hker : RingHom.ker (IsScalarTower.toAlgHom R A (ResidueField A)) = maximalIdeal A := by
    ext a
    exact residue_eq_zero_iff a
  exact Ideal.comap_injective_of_surjective e e.surjective
    (tensorProduct_prime_eq_of_surjectiveOnStalks (IsScalarTower.toAlgHom R A (ResidueField A))
      residue_surjective hA _ _ (by rw [he, hP, hker]) (by rw [he, hQ, hker])
      (by rw [he', he', hS]))

/-- If `A` is a localization of `R` and `A → B` is local and surjective on residue fields, then
`R → κ(B)` is surjective on stalks. -/
theorem surjectiveOnStalks_residue_of_localization {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsLocalHom (algebraMap A B)] (M : Submonoid R)
    [IsLocalization M A] (hs : Function.Surjective (ResidueField.map (algebraMap A B))) :
    (algebraMap R (ResidueField B)).SurjectiveOnStalks := by
  refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
  obtain ⟨y, rfl⟩ := hs x
  obtain ⟨a, rfl⟩ := residue_surjective y
  obtain ⟨⟨r, m⟩, he⟩ := IsLocalization.surj M a
  refine ⟨r, m, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply R A (ResidueField B)]
    exact (IsLocalization.map_units A m).map _
  · have he' : a * algebraMap R A m = algebraMap R A r := he
    rw [IsScalarTower.algebraMap_apply R A (ResidueField B),
      IsScalarTower.algebraMap_apply R A (ResidueField B), ResidueField.map_residue,
      IsScalarTower.algebraMap_apply A B (ResidueField B),
      IsScalarTower.algebraMap_apply A B (ResidueField B), ResidueField.algebraMap_eq,
      ← map_mul, ← map_mul, mul_comm, he']

/-- The map between localizations at primes `q` over `p` is local. -/
theorem isLocalHom_of_localizations {R S A B : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R S B] [IsScalarTower R A B] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] [IsLocalRing A] [IsLocalRing B]
    [IsLocalization.AtPrime A p] [IsLocalization.AtPrime B q] : IsLocalHom (algebraMap A B) := by
  have hq : (maximalIdeal B).comap (algebraMap S B) = q :=
    IsLocalization.AtPrime.under_maximalIdeal B q
  refine isLocalHom_of_atPrime_le p _ ?_
  rw [← IsScalarTower.algebraMap_eq R A B, IsScalarTower.algebraMap_eq R S B,
    ← Ideal.comap_comap, hq]
  exact Ideal.LiesOver.over.le

end StacksDraft

end Primes

namespace IsLocalRing.IsHenselization

variable {A Ah : Type u} [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]

/-- A henselian local ind-étale `A`-algebra with surjective residue field map is a henselization
of `A`. -/
private theorem of_ind_etale_of_surjective {B : Type u} [CommRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (h : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B))
    (hs : Function.Surjective (ResidueField.map (algebraMap A B))) :
    IsHenselization A (ResidueField A) B :=
  of_ind_etale inferInstance h
    ⟨RingEquiv.ofBijective _ ⟨RingHom.injective _, hs⟩, fun a => ResidueField.map_residue _ a⟩

/-- A henselization `C` of `A` which is ind-étale over an intermediate local ring `B`, with
`A → B → C` local, is a henselization of `B` with the same residue field; and a separable algebraic
closure of `κ(A)` is one of `κ(B)`. -/
private theorem exists_isHenselization_of_ind_etale {B C : Type u} {L : Type v} [CommRing B]
    [IsLocalRing B] [CommRing C] [IsLocalRing C] [Field L] [Algebra (ResidueField A) L]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [IsLocalHom (algebraMap A B)]
    [IsLocalHom (algebraMap B C)] [IsHenselization A L C]
    (hi : (CommAlgCat.etale.{u} B).ind.{u} (CommAlgCat.of B C)) :
    ∃ _ : Algebra (ResidueField B) L, IsHenselization B L C ∧
      (IsSepClosure (ResidueField A) L → IsSepClosure (ResidueField B) L) := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := A) (L := L) (Rh := C)
  let : Algebra (ResidueField B) L :=
    (e.symm.toRingHom.comp (ResidueField.map (algebraMap B C))).toAlgebra
  refine ⟨this, of_ind_etale (henselian (R := A) (L := L)) hi ⟨e, fun b => ?_⟩, fun hs => ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, ResidueField.map_residue]
  · have : IsScalarTower (ResidueField A) (ResidueField B) L := .of_algebraMap_eq' <| by
      ext a
      obtain ⟨a, rfl⟩ := residue_surjective a
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        ResidueField.algebraMap_residue, ResidueField.map_residue, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.eq_symm_apply, he, ← IsScalarTower.algebraMap_apply]
    exact ⟨IsSepClosure.sep_closed (ResidueField A),
      Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField B) L⟩

end IsLocalRing.IsHenselization

namespace IsLocalRing.IsHenselization

section Prime

variable {R A S B C : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [Algebra R A] [Algebra R S] [Algebra R C]
  [Algebra S C] [IsScalarTower R S C] [Algebra S B] [Algebra B C] [IsScalarTower S B C]
  [IsLocalHom (algebraMap B C)] (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime B q]

/-- The map `A ⊗[R] S → C` induced by `f : A → C` and `S → C`. -/
private noncomputable abbrev tensorLift (f : A →ₐ[R] C) : A ⊗[R] S →ₐ[R] C :=
  Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S C) fun _ _ => .all _ _

include q B in
/-- For a local `f : A → C`, the prime `Q = g⁻¹(𝔪_C)` of `A ⊗[R] S` lies over `𝔪_A` and over `q`,
where `g` is induced by `f` and `S → S_q → C`; and `C` is a local algebra over `(A ⊗[R] S)_Q`
compatibly with `g`. -/
private theorem exists_prime_tensorProduct (f : A →ₐ[R] C) (hf : IsLocalHom f) :
    let Q := (maximalIdeal C).comap (tensorLift (S := S) f).toRingHom
    Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := S)) =
        maximalIdeal A ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom = q ∧
      ∃ _ : Algebra (Localization.AtPrime Q) C, IsLocalHom (algebraMap (Localization.AtPrime Q) C) ∧
        (algebraMap (Localization.AtPrime Q) C).comp
          (algebraMap (A ⊗[R] S) (Localization.AtPrime Q)) = (tensorLift f).toRingHom := by
  intro Q
  have hleft : (tensorLift (S := S) f).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      f.toRingHom := by
    ext a
    simp
  have hright : (tensorLift f).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom =
      algebraMap S C := by
    ext a
    simp
  refine ⟨?_, ?_, exists_algebra_atPrime _ Q rfl _⟩
  · rw [Ideal.comap_comap, hleft]
    exact @maximalIdeal_comap _ _ _ _ _ _ f.toRingHom ⟨hf.map_nonunit⟩
  · rw [Ideal.comap_comap, hright, IsScalarTower.algebraMap_eq S B C, ← Ideal.comap_comap,
      maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal B q

end Prime

end IsLocalRing.IsHenselization

namespace IsLocalRing.IsHenselization

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)
  [p.IsPrime] [q.IsPrime] [q.LiesOver p]
  {Rp : Type u} [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
  {Sq : Type u} [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
  {Rh : Type u} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [Algebra Rp Rh]
  [IsScalarTower R Rp Rh]
  {Sh : Type u} [CommRing Sh] [IsLocalRing Sh] [Algebra R Sh] [Algebra S Sh] [Algebra Sq Sh]
  [IsScalarTower R S Sh] [IsScalarTower S Sq Sh]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
include p in
omit [q.LiesOver p] in
/-- The data behind `exists_isHenselization_localization_tensorProduct`: `Sh` is a local
ind-étale algebra over `U = (Rh ⊗[R] S)_Q`, which is a local `S_q`-algebra in a tower
`S_q → U → Sh`. -/
private theorem exists_localization_tensorProduct {Lr : Type v} [Field Lr]
    [Algebra (ResidueField Rp) Lr] [IsHenselization Rp Lr Rh] {Ls : Type v} [Field Ls]
    [Algebra (ResidueField Sq) Ls] [IsHenselization Sq Ls Sh] (f : Rh →ₐ[R] Sh)
    (hf : IsLocalHom f) :
    let g : Rh ⊗[R] S →ₐ[R] Sh :=
      Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Sh) fun _ _ => .all _ _
    let Q := (maximalIdeal Sh).comap g.toRingHom
    Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
        maximalIdeal Rh ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom = q ∧
      ∃ _ : Algebra (Localization.AtPrime Q) Sh,
        IsLocalHom (algebraMap (Localization.AtPrime Q) Sh) ∧
        (algebraMap (Localization.AtPrime Q) Sh).comp
          (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom ∧
        (CommAlgCat.etale.{u} (Localization.AtPrime Q)).ind.{u}
          (CommAlgCat.of (Localization.AtPrime Q) Sh) ∧
        ∃ _ : Algebra Sq (Localization.AtPrime Q),
          IsLocalHom (algebraMap Sq (Localization.AtPrime Q)) ∧
          IsScalarTower Sq (Localization.AtPrime Q) Sh := by
  intro g Q
  have := isLocalHom (R := Sq) (L := Ls) (Rh := Sh)
  obtain ⟨hl, hr, alg, hloc, hcomp⟩ := exists_prime_tensorProduct (B := Sq) q f hf
  refine ⟨hl, hr, alg, hloc, hcomp, ?_⟩
  have hS (s : S) : algebraMap S Sh s =
      algebraMap (Localization.AtPrime Q) Sh (algebraMap S (Localization.AtPrime Q) s) := by
    rw [IsScalarTower.algebraMap_apply S (Rh ⊗[R] S) (Localization.AtPrime Q) s,
      ← RingHom.comp_apply _ (algebraMap _ _), hcomp]
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  have : IsScalarTower S (Localization.AtPrime Q) Sh := .of_algebraMap_eq hS
  have hq : q = (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap S (Localization.AtPrime Q)) := by
    have hQU : (maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = Q :=
      IsLocalization.AtPrime.under_maximalIdeal _ Q
    rw [IsScalarTower.algebraMap_eq S (Rh ⊗[R] S), ← Ideal.comap_comap, hQU]
    exact hr.symm
  obtain ⟨algB, hBU, hBcomp⟩ := exists_algebra_atPrime _ q hq Sq
  have : IsScalarTower S Sq (Localization.AtPrime Q) := .of_algebraMap_eq' hBcomp.symm
  have hSqU : IsScalarTower Sq (Localization.AtPrime Q) Sh := .of_algebraMap_eq' <|
    IsLocalization.ringHom_ext q.primeCompl <| RingHom.ext fun s => by
      simp [← IsScalarTower.algebraMap_apply]
  have hRh := CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_atPrime R Rp p)
    (ind_etale_of_universe_le (R := Rp) (L := Lr) (Rh := Rh))
  have hSh := CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_atPrime S Sq q)
    (ind_etale_of_universe_le (R := Sq) (L := Ls) (Rh := Sh))
  have hU := CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_of_isPushout R S Rh _ hRh)
    (CommAlgCat.ind_etale_atPrime (Rh ⊗[R] S) (Localization.AtPrime Q) Q)
  exact ⟨CommAlgCat.ind_etale_of_comp hU hSh, algB, hBU, hSqU⟩

include p in
omit [q.LiesOver p] in
/-- **The henselization at the prime induced by a local map.** Let `Rh` and `Sh` be henselizations
of `R_p` and `S_q` with residue fields `Lr` and `Ls`, and let `f : Rh → Sh` be a local
`R`-algebra map. Let `g : Rh ⊗[R] S → Sh` be induced by `f` and `S → Sh`, and let `Q = g⁻¹(𝔪_Sh)`.
Then `Q` lies over `𝔪_Rh` and over `q`, and `Sh` is a henselization of `(Rh ⊗[R] S)_Q` with
residue field `Ls`, compatibly with `g`; a separable algebraic closure of `κ(q)` stays one. -/
theorem exists_isHenselization_localization_tensorProduct {Lr : Type v} [Field Lr]
    [Algebra (ResidueField Rp) Lr] [IsHenselization Rp Lr Rh] {Ls : Type v} [Field Ls]
    [Algebra (ResidueField Sq) Ls] [IsHenselization Sq Ls Sh] (f : Rh →ₐ[R] Sh)
    (hf : IsLocalHom f) :
    let g : Rh ⊗[R] S →ₐ[R] Sh :=
      Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Sh) fun _ _ => .all _ _
    let Q := (maximalIdeal Sh).comap g.toRingHom
    Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
        maximalIdeal Rh ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom = q ∧
      ∃ _ : Algebra (Localization.AtPrime Q) Sh,
        IsLocalHom (algebraMap (Localization.AtPrime Q) Sh) ∧
        (algebraMap (Localization.AtPrime Q) Sh).comp
          (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom ∧
        ∃ _ : Algebra (ResidueField (Localization.AtPrime Q)) Ls,
          IsHenselization (Localization.AtPrime Q) Ls Sh ∧
          (IsSepClosure (ResidueField Sq) Ls →
            IsSepClosure (ResidueField (Localization.AtPrime Q)) Ls) := by
  obtain ⟨hl, hr, alg, hloc, hcomp, hind, _, _, _⟩ :=
    exists_localization_tensorProduct p q (Rp := Rp) (Sq := Sq) (Lr := Lr) (Ls := Ls) f hf
  exact ⟨hl, hr, alg, hloc, hcomp, exists_isHenselization_of_ind_etale (A := Sq) hind⟩

include p in
/-- **The henselization after a ring map** (Stacks 08HU). Let `R → S` be a ring map and let
`q ⊆ S` lie over `p ⊆ R`. Let `Rh` and `Sh` be henselizations of `R_p` and `S_q`. The local
ring map `f : Rh → Sh` of Lemma 04GS (the unique local map over `R_p → S_q`) identifies `Sh` with
the henselization of `Rh ⊗[R] S` at the unique prime `Q` lying over `𝔪_Rh` and `q`: here `Q` is the
inverse image of `𝔪_Sh` under the map `g : Rh ⊗[R] S → Sh` induced by `f`, and `Sh` is a
henselization of `(Rh ⊗[R] S)_Q` through an algebra structure extending `g`. -/
@[stacks 08HU "The map `R^h → S^h` of 04GS is pinned as the unique local `R`-algebra map `f`
compatible with `R_p → S_q`. The prime is characterized by its two contractions, with uniqueness,
and equals `g⁻¹(𝔪_{S^h})` for the map `g` induced by `f`; that `S^h` is the henselization of
`(R^h ⊗_R S)_Q` is `IsHenselization` with residue field `κ(Q)`, through an algebra structure
extending `g`. All rings share one universe, as `IsHenselization` requires."]
theorem exists_unique_prime_isHenselization_tensorProduct [Algebra R Sq] [Algebra Rp Sq]
    [IsScalarTower R S Sq] [IsScalarTower R Rp Sq] [IsHenselization Rp (ResidueField Rp) Rh]
    [Algebra Rp Sh] [IsScalarTower Rp Sq Sh] [IsHenselization Sq (ResidueField Sq) Sh] :
    ∃ f : Rh →ₐ[R] Sh, IsLocalHom f ∧
      f.toRingHom.comp (algebraMap Rp Rh) = algebraMap Rp Sh ∧
      (∀ f' : Rh →ₐ[R] Sh, IsLocalHom f' →
        f'.toRingHom.comp (algebraMap Rp Rh) = algebraMap Rp Sh → f' = f) ∧
      let g : Rh ⊗[R] S →ₐ[R] Sh :=
        Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Sh) fun _ _ => .all _ _
      ∃ (Q : Ideal (Rh ⊗[R] S)) (_ : Q.IsPrime),
        Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
          maximalIdeal Rh ∧
        Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom = q ∧
        Q = (maximalIdeal Sh).comap g.toRingHom ∧
        (∀ Q' : Ideal (Rh ⊗[R] S), Q'.IsPrime →
          Q'.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
            maximalIdeal Rh →
          Q'.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom =
            q → Q' = Q) ∧
        ∃ _ : Algebra (Localization.AtPrime Q) Sh,
          IsLocalHom (algebraMap (Localization.AtPrime Q) Sh) ∧
          IsHenselization (Localization.AtPrime Q) (ResidueField (Localization.AtPrime Q)) Sh ∧
          (algebraMap (Localization.AtPrime Q) Sh).comp
            (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  have := StacksDraft.isLocalHom_of_localizations (A := Rp) (B := Sq) p q
  have := henselian (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  have := isLocalHom (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  have := isLocalHom (R := Rp) (L := ResidueField Rp) (Rh := Rh)
  have : IsLocalHom (algebraMap Rp Sh) := by
    rw [IsScalarTower.algebraMap_eq Rp Sq Sh]
    infer_instance
  have : IsScalarTower R Rp Sh := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply Rp Sq Sh, ← IsScalarTower.algebraMap_apply R Rp Sq,
      IsScalarTower.algebraMap_apply R S Sq, ← IsScalarTower.algebraMap_apply S Sq Sh,
      ← IsScalarTower.algebraMap_apply R S Sh]
  have hi := ind_etale (R := Rp) (L := ResidueField Rp) (Rh := Rh)
  have hb := (residueField_map_bijective (R := Rp) (Rh := Rh)).2
  let f : Rh →ₐ[Rp] Sh := HenselianLocalRing.indEtaleAlgHom (Sh := Sh) hi hb
  have hf : IsLocalHom f := HenselianLocalRing.isLocalHom_indEtaleAlgHom (Sh := Sh) hi hb
  have hu : ∀ g : Rh →ₐ[Rp] Sh, IsLocalHom g → g = f :=
    HenselianLocalRing.indEtaleAlgHom_unique (Sh := Sh) hi hb
  obtain ⟨hl, hr, alg, hloc, hcomp, hind, _, _, _⟩ := exists_localization_tensorProduct p q
    (Rp := Rp) (Sq := Sq) (Lr := ResidueField Rp) (Ls := ResidueField Sq) (f.restrictScalars R)
    ⟨hf.map_nonunit⟩
  refine ⟨f.restrictScalars R, ⟨hf.map_nonunit⟩, RingHom.ext f.commutes, fun f' hf' hcomp' =>
    AlgHom.ext fun x => AlgHom.congr_fun (hu { f'.toRingHom with
      commutes' := RingHom.congr_fun hcomp' } ⟨hf'.map_nonunit⟩) x, _, inferInstance, hl, hr, rfl,
    fun Q' _ hleft hright => ?_, alg, hloc, of_ind_etale_of_surjective hind
      (StacksDraft.residueFieldMap_surjective_of_tower (A := Sq)
        residueField_map_bijective.2), hcomp⟩
  exact StacksDraft.tensorProduct_prime_eq_of_residue
    (StacksDraft.surjectiveOnStalks_residue_of_localization p.primeCompl hb) Q' _
    hleft hl (hright.trans hr.symm)

end IsLocalRing.IsHenselization
