module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.StandardExample

/-!
# The standard cover is tamely ramified over the base in codimension one

Let `A` be a Noetherian ring, let `f : A` be a nonzerodivisor such that `A / fA` is reduced, and
let `e ≥ 1` be invertible in `A`.  The standard tamely ramified morphism attached to this data is
`Spec(C) ⟶ Spec(A)` for `C = A[x] / (x ^ e - f)`, and the associated cover is its restriction
`Spec(C_f) ⟶ Spec(A_f)`; see
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.Basic`.  This file proves that
the cover is tamely ramified over `Spec(A)` in codimension one, in the sense of
`Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne`.

## Main definitions

* `AlgebraicGeometry.standardTamelyRamifiedOpen` is the morphism `Spec(A_f) ⟶ Spec(A)` over which
  the standard cover is given.

## Main results

* `AlgebraicGeometry.standardTamelyRamifiedCover_isTamelyRamifiedInCodimensionOne` is the
  tameness assertion of [Stacks, Tag 0EYF].

## Implementation notes

The condition is a condition at the generic point `x` of a prime divisor of `Spec(A)` outside
`Spec(A_f)`, where the local ring `S = A_x` is given to be a discrete valuation ring.  Since `f`
lies in that prime and is a nonzerodivisor, the prime is minimal over `f`, so
`AlgebraicGeometry.isDiscreteValuationRing_of_mem_minimalPrimes` identifies `f` as a uniformizer
of `S`.  A field factor of the generic fibre consists of morphisms from spectra of fields; as
every scheme in sight is affine these are ring maps `A_f → K` and `C_f → L`, and the image `t`
of the root `x` of `X ^ e - f` is an `e`-th root of `f` in `L`.  The `K`-subalgebra `K[t]` of `L`
is then a field containing the image of `C_f`, and comparing the induced morphism from its
spectrum with the canonical morphism from the residue field at the point carrying the factor
shows that `K[t]` is all of `L`.  Tameness is therefore the statement about the generic fibre of
the standard morphism over `S` proved in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.StandardExample`.

## References

* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
* [Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The open subscheme `Spec(A_f)` of `Spec(A)` over which the standard cover lives. -/
public abbrev standardTamelyRamifiedOpen (A : Type u) [CommRing A] (f : A) :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))

/-- A prime containing `f` whose localization is a discrete valuation ring is minimal over
`f`. -/
private theorem mem_minimalPrimes_of_isDiscreteValuationRing
    {A : Type u} [CommRing A] {f : A} (hf : f ∈ nonZeroDivisors A)
    {p : Ideal A} [hp : p.IsPrime] (hfp : f ∈ p)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p]
    [IsDomain S] [IsDiscreteValuationRing S] :
    p ∈ (Ideal.span ({f} : Set A)).minimalPrimes := by
  have hspan : Ideal.span ({f} : Set A) ≤ p := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hfp
  refine ⟨⟨hp, hspan⟩, ?_⟩
  rintro q ⟨hq, hqf⟩ hqle
  have := hq
  have hd : Disjoint (p.primeCompl : Set A) (q : Set A) :=
    Set.disjoint_left.mpr fun a ha haq => ha (hqle haq)
  have : (q.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq hd
  have hfS : algebraMap A S f ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap (S := S) p.primeCompl hf
  have hPne : q.map (algebraMap A S) ≠ ⊥ := by
    intro h
    have hmem : algebraMap A S f ∈ q.map (algebraMap A S) :=
      Ideal.mem_map_of_mem _ (hqf (Ideal.mem_span_singleton_self f))
    rw [h, Ideal.mem_bot] at hmem
    exact nonZeroDivisors.ne_zero hfS hmem
  have hqm : q.map (algebraMap A S) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (_root_.IsPrime.to_maximal_ideal hPne)
  have hpm : p.map (algebraMap A S) = IsLocalRing.maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p S
  have hcq := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq hd
  have hcp := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hp disjoint_compl_left
  have heq : q = p := by rw [← hcq, ← hcp, hqm, hpm]
  exact le_of_eq heq.symm

/-- Algebraic core of tameness in codimension one for the standard cover: a field `L` over the
fraction field `K` of the local ring `S` at a prime containing `f`, generated over `K` by an
`e`-th root of `f`, is tamely ramified with respect to `S`. -/
private theorem isTamelyRamified_of_adjoin_root
    {A : Type u} [CommRing A] [IsNoetherianRing A] {f : A} {e : ℕ} [NeZero e]
    (hf : f ∈ nonZeroDivisors A)
    (hred : _root_.IsReduced (A ⧸ Ideal.span ({f} : Set A)))
    (hinv : IsUnit (e : A))
    {p : Ideal A} [p.IsPrime] (hfp : f ∈ p)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p]
    [IsDomain S] [IsDiscreteValuationRing S]
    (K L : Type u) [Field K] [Field L] [Algebra S K] [IsFractionRing S K]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra S L] [IsScalarTower S K L]
    (t : L) (ht : t ^ e = algebraMap S L (algebraMap A S f))
    (htop : Algebra.adjoin K ({t} : Set L) = ⊤) :
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo S K L := by
  obtain ⟨-, -, hirr⟩ := isDiscreteValuationRing_of_mem_minimalPrimes hf hred
    (mem_minimalPrimes_of_isDiscreteValuationRing hf hfp S) S
  let theta : standardTamelyRamifiedAlgebra S (algebraMap A S f) e →ₐ[S] L :=
    AdjoinRoot.liftAlgHom (Polynomial.X ^ e - Polynomial.C (algebraMap A S f))
      (Algebra.ofId S L) t (by simp [ht])
  let r : standardTamelyRamifiedAlgebra S (algebraMap A S f) e :=
    AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C (algebraMap A S f))
  have hthetar : theta r = t := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hle : (⊤ : Subalgebra K L) ≤
      (Algebra.TensorProduct.lift (Algebra.ofId K L) theta
        (fun _ _ => Commute.all _ _)).range := by
    rw [← htop]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨1 ⊗ₜ[S] r, ?_⟩)
    simp [Algebra.TensorProduct.lift_tmul, hthetar]
  obtain ⟨hfin, hsep, hres⟩ := standardTamelyRamifiedGenericFibreFactor_isTamelyRamified K
    (algebraMap A S f) e hirr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne e))
    (by simpa using hinv.map (algebraMap A S)) L
    (Algebra.TensorProduct.lift (Algebra.ofId K L) theta fun _ _ => Commute.all _ _)
    (fun z => hle (Algebra.mem_top (R := K) (x := z)))
  exact hres

/-- A `K`-subalgebra of a finite extension `L` of `K` is a field. -/
private theorem isField_subalgebra {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (T : Subalgebra K L) : IsField ↥T := by
  have : Algebra.IsIntegral K ↥T := ⟨fun z =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp
      (Algebra.IsIntegral.isIntegral (R := K) (z : L))⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/-- A field factor of a cover of affine schemes, read as ring data.  The two morphisms from
spectra of fields are `Spec` of ring maps `R → K` and `B → L` compatible with the local ring at
the point, and no proper `K`-subalgebra of `L` contains the image of `B`. -/
private theorem exists_ringHom_of_isFieldFactorAt
    {R₀ R B : Type u} [CommRing R₀] [CommRing R] [CommRing B]
    (iota : R₀ →+* R) (beta : R →+* B) (x : Spec (CommRingCat.of R₀))
    {K L : Type u} [Field K] [Field L]
    [Algebra R₀ ((Spec (CommRingCat.of R₀)).presheaf.stalk x)]
    [Algebra ((Spec (CommRingCat.of R₀)).presheaf.stalk x) K] [Algebra K L]
    [FiniteDimensional K L]
    (hst : (Spec (CommRingCat.of R₀)).fromSpecStalk x = Spec.map (CommRingCat.ofHom
      (algebraMap R₀ ((Spec (CommRingCat.of R₀)).presheaf.stalk x))))
    (hFF : Stacks.FundamentalGroup.IsFieldFactorAt (Spec.map (CommRingCat.ofHom iota))
      (Spec.map (CommRingCat.ofHom beta)) x K L) :
    ∃ chi : R →+* K, ∃ psi : B →+* L,
      chi.comp iota = (algebraMap ((Spec (CommRingCat.of R₀)).presheaf.stalk x) K).comp
          (algebraMap R₀ ((Spec (CommRingCat.of R₀)).presheaf.stalk x)) ∧
        psi.comp beta = (algebraMap K L).comp chi ∧
        ∀ T : Subalgebra K L, (∀ b : B, psi b ∈ T) → T = ⊤ := by
  obtain ⟨w, v, hw, hv, eiso, heiso⟩ := hFF
  obtain ⟨wh, rfl⟩ := Spec.map_surjective w
  obtain ⟨vh, rfl⟩ := Spec.map_surjective v
  rw [hst, ← Spec.map_comp, ← Spec.map_comp] at hw
  rw [← Spec.map_comp, ← Spec.map_comp] at hv
  have hw' := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  have hv' := congrArg CommRingCat.Hom.hom (Spec.map_injective hv)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hw' hv'
  refine ⟨wh.hom, vh.hom, hw', hv', ?_⟩
  revert eiso heiso
  generalize Spec.map vh (IsLocalRing.closedPoint L) = y
  intro eiso heiso T hT
  let : Field ↥T := (isField_subalgebra T).toField
  have hval : Spec.map (CommRingCat.ofHom (Subalgebra.val T).toRingHom)
      ≫ Spec.map (CommRingCat.ofHom (vh.hom.codRestrict T hT)) = Spec.map vh := by
    rw [← Spec.map_comp]
    rfl
  have hIso : IsIso (CommRingCat.ofHom
      (eiso.symm.toRingHom.comp (Subalgebra.val T).toRingHom)) := by
    refine Stacks.FundamentalGroup.isIso_of_specMap_comp_eq_fromSpecResidueField _ _
      (Spec.map (CommRingCat.ofHom (vh.hom.codRestrict T hT))) ?_
    have h2 : CommRingCat.ofHom eiso.toRingHom ≫ CommRingCat.ofHom eiso.symm.toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext (RingHom.ext fun z => eiso.symm_apply_apply z)
    have h3 : Spec.map (CommRingCat.ofHom eiso.symm.toRingHom)
        ≫ Spec.map (CommRingCat.ofHom eiso.toRingHom) = 𝟙 _ := by
      rw [← Spec.map_comp, h2, Spec.map_id]
    calc Spec.map (CommRingCat.ofHom
            (eiso.symm.toRingHom.comp (Subalgebra.val T).toRingHom))
          ≫ Spec.map (CommRingCat.ofHom (vh.hom.codRestrict T hT))
        = Spec.map (CommRingCat.ofHom eiso.symm.toRingHom)
            ≫ Spec.map (CommRingCat.ofHom (Subalgebra.val T).toRingHom)
              ≫ Spec.map (CommRingCat.ofHom (vh.hom.codRestrict T hT)) := by
          rw [← Category.assoc]
          exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (vh.hom.codRestrict T hT)))
            (Spec.map_comp (CommRingCat.ofHom (Subalgebra.val T).toRingHom)
              (CommRingCat.ofHom eiso.symm.toRingHom))
      _ = Spec.map (CommRingCat.ofHom eiso.symm.toRingHom) ≫ Spec.map vh := by rw [hval]
      _ = Spec.map (CommRingCat.ofHom eiso.symm.toRingHom)
            ≫ Spec.map (CommRingCat.ofHom eiso.toRingHom)
            ≫ (Spec (CommRingCat.of B)).fromSpecResidueField y := by rw [heiso]
      _ = (Spec (CommRingCat.of B)).fromSpecResidueField y := by
          rw [← Category.assoc, h3, Category.id_comp]
  have hsurj : Function.Surjective (Subalgebra.val T) := by
    have hbij := (ConcreteCategory.isIso_iff_bijective _).mp hIso
    intro z
    obtain ⟨c, hc⟩ := hbij.2 (eiso.symm z)
    exact ⟨c, eiso.symm.injective hc⟩
  refine Algebra.eq_top_iff.mpr fun z => ?_
  obtain ⟨c, hc⟩ := hsurj z
  exact hc ▸ c.2

/-- A ring map out of a localization away from `g` lands in a subalgebra `T` that is a field as
soon as the image of the ring does and the image of `g` is nonzero. -/
private theorem mem_of_isLocalizationAway {C : Type u} [CommRing C] {g : C}
    {Cf : Type u} [CommRing Cf] [Algebra C Cf] [IsLocalization.Away g Cf]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (psi : Cf →+* L) (T : Subalgebra K L) (hT : IsField ↥T)
    (hmem : ∀ c : C, psi (algebraMap C Cf c) ∈ T)
    (hg : psi (algebraMap C Cf g) ≠ 0) (b : Cf) : psi b ∈ T := by
  obtain ⟨binv, hbinv⟩ := hT.mul_inv_cancel (a := (⟨psi (algebraMap C Cf g), hmem g⟩ : ↥T))
    fun hcon => hg (by simpa using congrArg Subtype.val hcon)
  have hone : psi (algebraMap C Cf g) * (binv : L) = 1 := by
    simpa using congrArg Subtype.val hbinv
  obtain ⟨⟨c, m⟩, hm⟩ := IsLocalization.surj (M := Submonoid.powers g) b
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : C) g).mp m.2
  rw [← hn] at hm
  have h1 : psi b * psi (algebraMap C Cf g) ^ n = psi (algebraMap C Cf c) := by
    have h := congrArg psi hm
    simpa only [map_mul, map_pow] using h
  have h2 : psi b = psi (algebraMap C Cf c) * (binv : L) ^ n := by
    calc psi b = psi b * (psi (algebraMap C Cf g) * (binv : L)) ^ n := by
          rw [hone, one_pow, mul_one]
      _ = psi b * psi (algebraMap C Cf g) ^ n * (binv : L) ^ n := by ring
      _ = psi (algebraMap C Cf c) * (binv : L) ^ n := by rw [h1]
  rw [h2]
  exact mul_mem (hmem c) (pow_mem binv.2 n)

/-- A ring map out of `AdjoinRoot p` lands in a subalgebra containing the image of the root and
the image of the coefficient ring. -/
private theorem adjoinRoot_image_mem {A : Type u} [CommRing A] {p : Polynomial A}
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (rho : AdjoinRoot p →+* L) (T : Subalgebra K L)
    (hr : rho (AdjoinRoot.root p) ∈ T)
    (hA : ∀ a : A, rho (algebraMap A (AdjoinRoot p) a) ∈ T) (c : AdjoinRoot p) : rho c ∈ T := by
  have hc : c ∈ Algebra.adjoin A ({AdjoinRoot.root p} : Set (AdjoinRoot p)) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem z hz => obtain rfl := hz; exact hr
  | algebraMap a => exact hA a
  | add z₁ z₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | mul z₁ z₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂

/-- Tameness of the standard cover at a single boundary point of `Spec(A)`. -/
private theorem standardTamelyRamifiedCover_isTamelyRamifiedAt
    (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A) (e : ℕ) [NeZero e]
    (hf : f ∈ nonZeroDivisors A)
    (hred : _root_.IsReduced (A ⧸ Ideal.span ({f} : Set A)))
    (hinv : IsUnit (e : A)) (x : Spec (CommRingCat.of A))
    (hx : x ∉ Set.range (standardTamelyRamifiedOpen A f).base)
    [IsDomain ((Spec (CommRingCat.of A)).presheaf.stalk x)]
    [IsDiscreteValuationRing ((Spec (CommRingCat.of A)).presheaf.stalk x)]
    (K L : Type u) [Field K] [Field L]
    [Algebra ((Spec (CommRingCat.of A)).presheaf.stalk x) K]
    [IsFractionRing ((Spec (CommRingCat.of A)).presheaf.stalk x) K]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra ((Spec (CommRingCat.of A)).presheaf.stalk x) L]
    [IsScalarTower ((Spec (CommRingCat.of A)).presheaf.stalk x) K L]
    (hFF : Stacks.FundamentalGroup.IsFieldFactorAt (standardTamelyRamifiedOpen A f)
      (standardTamelyRamifiedCover A f e) x K L) :
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo
      ((Spec (CommRingCat.of A)).presheaf.stalk x) K L := by
  let : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk (CommRingCat.of A) x).hom.toAlgebra
  have : x.asIdeal.IsPrime := x.isPrime
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of A) x
  have hst : (Spec (CommRingCat.of A)).fromSpecStalk x
      = Spec.map (CommRingCat.ofHom
        (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk x))) :=
    Spec.fromSpecStalk_eq' _ _
  have hfp : f ∈ x.asIdeal := by
    by_contra hmem
    refine hx ?_
    have hr : Set.range (standardTamelyRamifiedOpen A f).base
        = Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := rfl
    rw [hr, PrimeSpectrum.localization_away_comap_range _ f]
    exact hmem
  obtain ⟨chi, psi, hchi, hpsi, hgen⟩ := exists_ringHom_of_isFieldFactorAt
    (algebraMap A (Localization.Away f))
    (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A f e)) f) x hst hFF
  have hmapcomp : (algebraMap (standardTamelyRamifiedAlgebra A f e)
        (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f))).comp
      (algebraMap A (standardTamelyRamifiedAlgebra A f e))
      = (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A f e)) f).comp
        (algebraMap A (Localization.Away f)) := (IsLocalization.map_comp _).symm
  have hAmem : ∀ a : A,
      psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
          (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
        (algebraMap A (standardTamelyRamifiedAlgebra A f e) a))
        = algebraMap ((Spec (CommRingCat.of A)).presheaf.stalk x) L
          (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk x) a) := by
    intro a
    have h0 := DFunLike.congr_fun hmapcomp a
    have h1 := DFunLike.congr_fun hpsi (algebraMap A (Localization.Away f) a)
    have h2 := DFunLike.congr_fun hchi a
    simp only [RingHom.comp_apply] at h0 h1 h2
    rw [h0, h1, h2,
      IsScalarTower.algebraMap_apply ((Spec (CommRingCat.of A)).presheaf.stalk x) K L]
  have hrootpow : (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f) :
      standardTamelyRamifiedAlgebra A f e) ^ e
      = algebraMap A (standardTamelyRamifiedAlgebra A f e) f := by
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C f)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      sub_eq_zero] at h
    exact h
  have hSne : algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk x) f ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.nonZeroDivisors_le_comap
      (S := ↥((Spec (CommRingCat.of A)).presheaf.stalk x)) x.asIdeal.primeCompl hf)
  have hinj : Function.Injective
      (algebraMap ((Spec (CommRingCat.of A)).presheaf.stalk x) L) := by
    rw [IsScalarTower.algebraMap_eq ((Spec (CommRingCat.of A)).presheaf.stalk x) K L,
      RingHom.coe_comp]
    exact (algebraMap K L).injective.comp
      (IsFractionRing.injective ((Spec (CommRingCat.of A)).presheaf.stalk x) K)
  obtain ⟨t, hts⟩ : ∃ t : L, psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
      (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
      (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f))) = t := ⟨_, rfl⟩
  have hCmem : ∀ c : standardTamelyRamifiedAlgebra A f e,
      psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
        (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f))) c)
        ∈ Algebra.adjoin K ({t} : Set L) := by
    intro c
    refine adjoinRoot_image_mem (p := Polynomial.X ^ e - Polynomial.C f)
      (psi.comp (algebraMap (standardTamelyRamifiedAlgebra A f e)
        (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f))))
      (Algebra.adjoin K ({t} : Set L)) ?_ (fun a => ?_) c
    · exact Algebra.subset_adjoin hts
    · change psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
          (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
          (algebraMap A (standardTamelyRamifiedAlgebra A f e) a))
          ∈ Algebra.adjoin K ({t} : Set L)
      rw [hAmem a,
        IsScalarTower.algebraMap_apply ((Spec (CommRingCat.of A)).presheaf.stalk x) K L]
      exact Subalgebra.algebraMap_mem _ _
  have hgne : psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
      (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
      (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)) ≠ 0 := by
    rw [hAmem f]
    intro hcon
    exact hSne (hinj (by rw [hcon, map_zero]))
  refine isTamelyRamified_of_adjoin_root hf hred hinv hfp
    ((Spec (CommRingCat.of A)).presheaf.stalk x) K L t ?_ ?_
  · have hpow : psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
          (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
        (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f))) ^ e
        = psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
          (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
          (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)) := by
      have h1 : psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
            (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
          (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f))) ^ e
          = psi ((algebraMap (standardTamelyRamifiedAlgebra A f e)
            (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))
            ((AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f) :
              standardTamelyRamifiedAlgebra A f e) ^ e)) :=
        (map_pow (psi.comp (algebraMap (standardTamelyRamifiedAlgebra A f e)
          (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f))))
          (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C f)) e).symm
      rw [h1, hrootpow]
    rw [← hts, hpow]
    exact hAmem f
  · exact hgen _ (mem_of_isLocalizationAway
      (g := algebraMap A (standardTamelyRamifiedAlgebra A f e) f) psi
      (Algebra.adjoin K ({t} : Set L)) (isField_subalgebra _) hCmem hgne)

/-- **Stacks 0EYF, tameness in codimension one.** Let `A` be a Noetherian ring, let `f : A` be a
nonzerodivisor such that `A / fA` is reduced, and let `e ≥ 1` be invertible in `A`.  The finite
étale cover `Spec(C_f) ⟶ Spec(A_f)` attached to `C = A[x] / (x ^ e - f)` is tamely ramified over
`Spec(A)` in codimension one. -/
@[stacks 0EYF "standard_cover_tame_codimension_one", sga "1 XIII 5.1" "r = 1, codim 1 tame"]
public theorem standardTamelyRamifiedCover_isTamelyRamifiedInCodimensionOne
    (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A) (e : ℕ) [NeZero e]
    (hf : f ∈ nonZeroDivisors A)
    (hred : _root_.IsReduced (A ⧸ Ideal.span ({f} : Set A)))
    (hinv : IsUnit (e : A)) :
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (standardTamelyRamifiedOpen A f) (standardTamelyRamifiedCover A f e) := by
  intro Z hZ hD hV K L _ _ _ _ _ _ _ _ _ hFF
  have := hD
  have := hV
  exact standardTamelyRamifiedCover_isTamelyRamifiedAt A f e hf hred hinv Z.genericPoint hZ K L
    hFF

end AlgebraicGeometry
