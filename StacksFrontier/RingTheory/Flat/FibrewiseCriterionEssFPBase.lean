module

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFP
public import StacksFrontier.RingTheory.Flat.LocalCriterionNonNoetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Critere de platitude par fibres: essential finite presentation of the intermediate ring

Let `R → S → S'` be local homomorphisms of local rings, let `𝔪` be the maximal ideal of `R` and
let `M` be a nonzero `S'`-module of finite presentation which is flat over `R` and whose fibre
`M/𝔪M` is flat over `S/𝔪S`. Assume `R → S'` is essentially of finite presentation and `R → S` is
essentially of finite type. Then `R → S` is essentially of finite *presentation*, `S` is flat over
`R` and `M` is flat over `S`. Here `𝔪S` is `(maximalIdeal R).map (algebraMap R S)` and `𝔪M` is
`𝔪S • ⊤` over `S`, so that `M/𝔪M` is a module over the fibre ring `S/𝔪S`.

## Main results

* `Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal`: the
  statement above.
* `Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq`: submodules over different rings
  with the same elements have isomorphic quotient groups.
* `Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top`: the `A`-submodule `𝔪A • ⊤` has the
  same elements as the `R`-submodule `𝔪 • ⊤`.

## References

* [Stacks Project, Tag 05UV](https://stacks.math.columbia.edu/tag/05UV)
-/

@[expose] public section


namespace Stacks.Flatness.FibrewiseCriterionEssFP

universe u v w

open IsLocalRing

/-- Two submodules `P`
and `Q` of the same additive group `M`, one over `A` and one over `A'`, with the same underlying
set have canonically isomorphic quotient groups, the isomorphism sending the class of `x` to the
class of `x`. -/
def quotAddEquivOfCoeEq {A A' M : Type*} [Ring A] [Ring A'] [AddCommGroup M]
    [Module A M] [Module A' M] (P : Submodule A M) (Q : Submodule A' M)
    (h : (P : Set M) = (Q : Set M)) : (M ⧸ P) ≃+ (M ⧸ Q) where
  toFun := Quotient.map id fun a b hab =>
    (Submodule.quotientRel_def Q).mpr (by
      rw [← SetLike.mem_coe, ← h]; exact (Submodule.quotientRel_def P).mp hab)
  invFun := Quotient.map id fun a b hab =>
    (Submodule.quotientRel_def P).mpr (by
      rw [← SetLike.mem_coe, h]; exact (Submodule.quotientRel_def Q).mp hab)
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by rintro ⟨x⟩; rfl
  map_add' := by rintro ⟨x⟩ ⟨y⟩; rfl

/-- For an `R`-algebra `A`
acting compatibly on `M`, the `A`-submodule `𝔪A • ⊤` of `M` has the same elements as the
`R`-submodule `𝔪 • ⊤`. -/
lemma coe_map_smul_top {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (𝔪 : Ideal R) :
    ((𝔪.map (algebraMap R A) • (⊤ : Submodule A M) : Submodule A M) : Set M)
      = ((𝔪 • (⊤ : Submodule R M) : Submodule R M) : Set M) := by
  have h := Ideal.smul_restrictScalars (R := R) (S := A) (M := M) 𝔪 (⊤ : Submodule A M)
  rw [Submodule.restrictScalars_top] at h
  exact congrArg (fun N : Submodule R M => (N : Set M)) h

/-- A surjection `f : T → S` and an ideal `I` of `T` with `ker f ≤ I` induce an isomorphism
`T ⧸ I ≅ S ⧸ IS`. -/
private noncomputable def quotientEquivQuotientMap {T S : Type*} [CommRing T] [CommRing S]
    {f : T →+* S} (hf : Function.Surjective f) {I : Ideal T} (hker : RingHom.ker f ≤ I) :
    (T ⧸ I) ≃+* (S ⧸ I.map f) :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f) fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((sup_le le_rfl hker) hx), by
      intro y
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨t, rfl⟩ := hf s
      exact ⟨Ideal.Quotient.mk I t, rfl⟩⟩

private lemma quotientEquivQuotientMap_mk {T S : Type*} [CommRing T] [CommRing S] {f : T →+* S}
    (hf : Function.Surjective f) {I : Ideal T} (hker : RingHom.ker f ≤ I) (t : T) :
    quotientEquivQuotientMap hf hker (Ideal.Quotient.mk I t)
      = Ideal.Quotient.mk (I.map f) (f t) := rfl

/-! ### The two ideals -/

/-- Let `B` be an `R`-algebra, `𝔪` an ideal of `R`, and `J₀ ≤ J'` two ideals of `B` with
`J' ≤ J₀ + 𝔪B`. If `B ⧸ J'` is flat over `R`, then `J' ≤ J₀ + (𝔪B)·J'`. -/
private theorem le_sup_smul_of_flat_quotient {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] {𝔪 : Ideal R} {J₀ J' : Ideal B} (hle : J₀ ≤ J')
    (hsup : J' ≤ J₀ ⊔ 𝔪.map (algebraMap R B)) [Module.Flat R (B ⧸ J')] :
    J' ≤ J₀ ⊔ 𝔪.map (algebraMap R B) • J' := by
  classical
  intro x hx
  obtain ⟨y, hy, z, hz, hxyz⟩ := Submodule.mem_sup.mp (hsup hx)
  obtain ⟨n, b, g, hbg⟩ :=
    Submodule.mem_span_set'.mp (hz : z ∈ Submodule.span B ((algebraMap R B) '' (𝔪 : Set R)))
  choose m hm hmg using fun i : Fin n => (g i).2
  have hzsum : ∑ i : Fin n, m i • b i = z := by
    rw [← hbg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← hmg i, smul_eq_mul, mul_comm]
  have hzmem : z ∈ J' := by simpa [← hxyz] using J'.sub_mem hx (hle hy)
  set π : B →ₐ[R] B ⧸ J' := Ideal.Quotient.mkₐ R J' with hπ
  have hπzero : ∀ w : B, π w = 0 ↔ w ∈ J' := fun w => by
    rw [hπ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨k, a, q, hq1, hq2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := R) (M := B ⧸ J') (f := m) (x := fun i => π (b i)) (by
        have h := (hπzero z).mpr hzmem
        rw [← hzsum, map_sum] at h
        simpa only [map_smul] using h)
  choose d hd using fun j : Fin k => Ideal.Quotient.mk_surjective (I := J') (q j)
  have hπd : ∀ j, π (d j) = q j := fun j => by rw [hπ, Ideal.Quotient.mkₐ_eq_mk]; exact hd j
  have hq1' : ∀ i, π (b i) = ∑ j, a i j • q j := hq1
  have hw : ∀ i, b i - ∑ j, a i j • d j ∈ J' := fun i => (hπzero _).mp <| by
    simp only [map_sub, map_sum, map_smul, hq1' i, hπd, sub_self]
  have hc0 : ∑ i : Fin n, m i • (∑ j, a i j • d j) = 0 := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.sum_smul, hq2 j, zero_smul]
  have hxeq : x = y + ∑ i : Fin n, m i • (b i - ∑ j, a i j • d j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hc0, sub_zero, hzsum, hxyz]
  rw [hxeq, Ideal.smul_eq_mul]
  refine Submodule.add_mem_sup hy (Ideal.sum_mem _ fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hm i)) (hw i)

/-- If `B ⧸ I` is Noetherian then every ideal `J` of `B` contains a finitely generated ideal `J₀`
with `J ≤ J₀ + I`. -/
private theorem exists_fg_le_sup_of_isNoetherianRing_quotient {B : Type*} [CommRing B]
    (I J : Ideal B) [IsNoetherianRing (B ⧸ I)] : ∃ J₀ ≤ J, J₀.FG ∧ J ≤ J₀ ⊔ I := by
  classical
  obtain ⟨s, hs⟩ :=
    (isNoetherianRing_iff.mp ‹IsNoetherianRing (B ⧸ I)›).noetherian (J.map (Ideal.Quotient.mk I))
  have hlift : ∀ g ∈ (s : Set (B ⧸ I)), ∃ c ∈ J, Ideal.Quotient.mk I c = g := by
    intro g hg
    refine (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ?_
    rw [← hs]; exact Ideal.subset_span hg
  choose! c hcJ hcmk using hlift
  refine ⟨Ideal.span (c '' (s : Set (B ⧸ I))), Ideal.span_le.mpr ?_,
    Submodule.fg_span (s.finite_toSet.image c), fun x hx => ?_⟩
  · rintro _ ⟨g, hg, rfl⟩; exact hcJ g hg
  · have hmap : J.map (Ideal.Quotient.mk I)
        ≤ (Ideal.span (c '' (s : Set (B ⧸ I)))).map (Ideal.Quotient.mk I) := by
      rw [← hs, Ideal.span_le]
      intro g hg
      rw [← hcmk g hg]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨g, hg, rfl⟩)
    have hmem := hmap (Ideal.mem_map_of_mem _ hx)
    rwa [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hmem

/-- Let `B` be an `R`-algebra with `𝔪B` inside the Jacobson radical and `B ⧸ 𝔪B`
Noetherian, and let `J` be an ideal of `B`. If `B ⧸ J'` is flat over `R` for every finitely
generated `J' ≤ J` with `J ≤ J' + 𝔪B`, then `J` is finitely generated. -/
private theorem fg_of_forall_flat_quotient {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {𝔪 : Ideal R} (hjac : 𝔪.map (algebraMap R B) ≤ (⊥ : Ideal B).jacobson)
    [IsNoetherianRing (B ⧸ 𝔪.map (algebraMap R B))] (J : Ideal B)
    (hflat : ∀ J' ≤ J, J'.FG → J ≤ J' ⊔ 𝔪.map (algebraMap R B) → Module.Flat R (B ⧸ J')) :
    J.FG := by
  obtain ⟨J₀, hJ₀le, hJ₀fg, hJle⟩ :=
    exists_fg_le_sup_of_isNoetherianRing_quotient (𝔪.map (algebraMap R B)) J
  suffices hJ : J = J₀ from hJ ▸ hJ₀fg
  refine le_antisymm (fun x hx => ?_) hJ₀le
  have hxle : Ideal.span {x} ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hfg : (J₀ ⊔ Ideal.span {x}).FG :=
    Submodule.FG.sup hJ₀fg (Submodule.fg_span_singleton x)
  have := hflat _ (sup_le hJ₀le hxle) hfg (hJle.trans (sup_le_sup_right le_sup_left _))
  have hEq : J₀ ⊔ Ideal.span {x} = J₀ :=
    Ideal.eq_of_le_sup_map_of_flat_quotient hfg le_sup_left 𝔪 hjac
      (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hJle hx))))
  exact hEq ▸ Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton x))

/-! ### Essential finite presentation -/

/-- A surjective ring map `g : B → S` whose kernel is finitely generated is essentially of finite
presentation. -/
private theorem essFP_of_surjective_of_fg_ker {B : Type v} {S : Type w} [CommRing B] [CommRing S]
    (g : B →+* S) (hsurj : Function.Surjective g) (hfg : (RingHom.ker g).FG) :
    g.EssentiallyOfFinitePresentation := by
  rw [RingHom.EssentiallyOfFinitePresentation]
  let instBS : Algebra B S := g.toAlgebra
  have : Algebra.FinitePresentation B (B ⧸ RingHom.ker g) :=
    Algebra.FinitePresentation.quotient hfg
  let e : (B ⧸ RingHom.ker g) ≃ₐ[B] S :=
    { RingHom.quotientKerEquivOfSurjective hsurj with commutes' := fun _ => rfl }
  have : Algebra.FinitePresentation B S := Algebra.FinitePresentation.equiv e
  have : IsLocalization (⊥ : Submonoid S) S := IsLocalization.of_le_isUnit bot_le
  exact essFP_reuniverse (R := B) (T := S) S (⊥ : Submonoid S)

/-- If `B` is essentially of finite presentation over `R` and `B → S` is surjective with finitely
generated kernel, then `S` is essentially of finite presentation over `R`. -/
private theorem essentiallyOfFinitePresentation_of_surjective_of_fg_ker {R B S : Type*}
    [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S] [Algebra R S]
    [IsScalarTower R B S] (hB : (algebraMap R B).EssentiallyOfFinitePresentation)
    (hsurj : Function.Surjective (algebraMap B S))
    (hfg : (RingHom.ker (algebraMap B S)).FG) :
    (algebraMap R S).EssentiallyOfFinitePresentation := by
  rw [IsScalarTower.algebraMap_eq R B S]
  exact essFinitePresentation_comp hB (essFP_of_surjective_of_fg_ker _ hsurj hfg)

/-- A localization of a finitely presented `R`-algebra `P` is essentially of finite presentation
over `R`. -/
private theorem essFP_of_isLocalization {R : Type u} {Pₘ : Type w} [CommRing R] [CommRing Pₘ]
    [Algebra R Pₘ] (P : Type (max u w)) [CommRing P] [Algebra R P] [Algebra P Pₘ]
    [IsScalarTower R P Pₘ] [Algebra.FinitePresentation R P] (M : Submonoid P)
    [IsLocalization M Pₘ] : (algebraMap R Pₘ).EssentiallyOfFinitePresentation := by
  rw [RingHom.EssentiallyOfFinitePresentation]
  exact ⟨P, inferInstance, inferInstance, inferInstance,
    @IsScalarTower.of_algebraMap_eq R P Pₘ _ _ _ _ _ (algebraMap R Pₘ).toAlgebra
      (IsScalarTower.algebraMap_apply R P Pₘ), inferInstance, M, inferInstance⟩

/-- If `R ⧸ I` is Noetherian and `σ` is finite then `R[σ] ⧸ I·R[σ]` is Noetherian. -/
@[ega "IV 1.4.1" "more general"]
private theorem isNoetherianRing_quotient_map_mvPolynomial {R : Type*} [CommRing R] {σ : Type*}
    [Finite σ] (I : Ideal R) [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing (MvPolynomial σ R ⧸ I.map (algebraMap R (MvPolynomial σ R))) := by
  classical
  have : IsNoetherianRing (MvPolynomial σ (R ⧸ I)) := MvPolynomial.isNoetherianRing
  rw [MvPolynomial.algebraMap_eq]
  exact isNoetherianRing_of_ringEquiv (MvPolynomial σ (R ⧸ I))
    (MvPolynomial.quotientEquivQuotientMvPolynomial I).toRingEquiv

/-- If `P ⧸ I` is Noetherian and `Pₘ` is a localization of `P`, then `Pₘ ⧸ I·Pₘ` is
Noetherian. -/
private theorem isNoetherianRing_quotient_map_of_isLocalization {P Pₘ : Type*} [CommRing P]
    [CommRing Pₘ] [Algebra P Pₘ] (M : Submonoid P) [IsLocalization M Pₘ] (I : Ideal P)
    [IsNoetherianRing (P ⧸ I)] : IsNoetherianRing (Pₘ ⧸ I.map (algebraMap P Pₘ)) :=
  IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid (P ⧸ I) M) _
    ‹IsNoetherianRing (P ⧸ I)›

/-- A local homomorphism `R → S` of local rings which is essentially of finite type factors as
`R → B → S` with `B` a local ring essentially of finite presentation over `R`, `B → S`
surjective, the maximal ideal of `R` mapping into the maximal ideal of `B`, and the fibre
`B ⧸ 𝔪B` Noetherian. -/
private theorem exists_essFP_surjective_of_essFiniteType (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra R B) (_ : Algebra B S)
      (_ : IsScalarTower R B S),
      (algebraMap R B).EssentiallyOfFinitePresentation ∧
      Function.Surjective (algebraMap B S) ∧
      (maximalIdeal R).map (algebraMap R B) ≤ maximalIdeal B ∧
      IsNoetherianRing (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by
  classical
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R (Algebra.EssFiniteType.subalgebra R S))
  let ψ : MvPolynomial (Fin n) R →ₐ[R] S := (Algebra.EssFiniteType.subalgebra R S).val.comp f
  let q : Ideal (MvPolynomial (Fin n) R) := Ideal.comap (ψ : MvPolynomial (Fin n) R →+* S)
    (maximalIdeal S)
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ y : q.primeCompl, IsUnit ((ψ : MvPolynomial (Fin n) R →+* S) y) :=
    fun y => not_not.mp y.2
  let algBS : Algebra (Localization.AtPrime q) S :=
    (IsLocalization.lift (M := q.primeCompl) hunit).toAlgebra
  have towerRBS : IsScalarTower R (Localization.AtPrime q) S :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) (Localization.AtPrime q) r,
        show algebraMap (Localization.AtPrime q) S
            (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime q) _) = ψ _ from
          IsLocalization.lift_eq (M := q.primeCompl) hunit _, ψ.commutes]
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime q) S) := by
    intro s
    obtain ⟨⟨a, t⟩, hs⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid R S) s
    obtain ⟨p, hp⟩ := hf a
    obtain ⟨w, hw⟩ := hf (t : Algebra.EssFiniteType.subalgebra R S)
    have htu : IsUnit (algebraMap (Algebra.EssFiniteType.subalgebra R S) S t) := by
      simpa [Algebra.EssFiniteType.submonoid, IsUnit.submonoid] using t.2
    have hψw : (ψ : MvPolynomial (Fin n) R →+* S) w
        = algebraMap (Algebra.EssFiniteType.subalgebra R S) S t := by
      show (Algebra.EssFiniteType.subalgebra R S).val (f w) = _
      rw [hw]; rfl
    have hwq : w ∈ q.primeCompl := fun hmem => by
      have hmem' : (ψ : MvPolynomial (Fin n) R →+* S) w ∈ maximalIdeal S := hmem
      rw [hψw, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem'
      exact hmem' htu
    refine ⟨IsLocalization.mk' (Localization.AtPrime q) p ⟨w, hwq⟩, ?_⟩
    rw [show (algebraMap (Localization.AtPrime q) S) = IsLocalization.lift
      (M := q.primeCompl) hunit from rfl, IsLocalization.lift_mk'_spec]
    have hψp : (ψ : MvPolynomial (Fin n) R →+* S) p
        = algebraMap (Algebra.EssFiniteType.subalgebra R S) S a := by
      show (Algebra.EssFiniteType.subalgebra R S).val (f p) = _
      rw [hp]; rfl
    rw [hψp, hψw, ← hs, mul_comm]
  have hRB : IsLocalHom (algebraMap R (Localization.AtPrime q)) :=
    ⟨fun r hr => isUnit_of_map_unit (algebraMap R S) r
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime q) S r ▸ hr.map _)⟩
  have : IsNoetherianRing (R ⧸ maximalIdeal R) :=
    isNoetherianRing_of_ringEquiv (IsLocalRing.ResidueField R) (RingEquiv.refl _)
  have := isNoetherianRing_quotient_map_mvPolynomial (R := R) (σ := Fin n) (maximalIdeal R)
  have hNB : IsNoetherianRing (Localization.AtPrime q ⧸
      (maximalIdeal R).map (algebraMap R (Localization.AtPrime q))) := by
    rw [show (maximalIdeal R).map (algebraMap R (Localization.AtPrime q))
        = ((maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n) R))).map
          (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime q)) by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]]
    exact isNoetherianRing_quotient_map_of_isLocalization q.primeCompl _
  exact ⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, algBS, towerRBS,
    essFP_of_isLocalization (MvPolynomial (Fin n) R) q.primeCompl, hsurj,
    ((IsLocalRing.local_hom_TFAE (algebraMap R (Localization.AtPrime q))).out 1 3).mp hRB, hNB⟩

/-! ### The fibre over the closed point -/

/-- Let `R → T → S` be algebras with `T → S` surjective and with `ker (T → S)` contained in `𝔪T`,
where `𝔪` is the maximal ideal of `R`, and let `M` carry compatible `R`-, `T`- and `S`-module
structures. If the fibre `M/𝔪M` is flat over `S/𝔪S`, then it is flat over `T/𝔪T`. -/
private theorem flat_fibre_of_ker_le_map_maximalIdeal {R T S M : Type*} [CommRing R] [CommRing T]
    [CommRing S] [IsLocalRing R] [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    [AddCommGroup M] [Module R M] [Module T M] [Module S M]
    [IsScalarTower R T M] [IsScalarTower T S M]
    (hsurj : Function.Surjective (algebraMap T S))
    (hker : RingHom.ker (algebraMap T S) ≤ (maximalIdeal R).map (algebraMap R T))
    [Module.Flat (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))] :
    Module.Flat (T ⧸ (maximalIdeal R).map (algebraMap R T))
      (M ⧸ ((maximalIdeal R).map (algebraMap R T) • (⊤ : Submodule T M))) := by
  have htower : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [IsScalarTower.algebraMap_apply R T S, algebraMap_smul, algebraMap_smul]
  set 𝔪T : Ideal T := (maximalIdeal R).map (algebraMap R T) with h𝔪T
  set 𝔪S : Ideal S := (maximalIdeal R).map (algebraMap R S) with h𝔪S
  have hmapeq : 𝔪T.map (algebraMap T S) = 𝔪S := by
    rw [h𝔪T, h𝔪S, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e : (T ⧸ 𝔪T) ≃+* (S ⧸ 𝔪S) :=
    (quotientEquivQuotientMap hsurj hker).trans (Ideal.quotEquivOfEq hmapeq)
  have hemk : ∀ t : T, e (Ideal.Quotient.mk 𝔪T t) = Ideal.Quotient.mk 𝔪S (algebraMap T S t) :=
    fun t => by
      rw [show e (Ideal.Quotient.mk 𝔪T t)
        = Ideal.quotEquivOfEq hmapeq (quotientEquivQuotientMap hsurj hker
          (Ideal.Quotient.mk 𝔪T t)) from rfl, quotientEquivQuotientMap_mk,
        Ideal.quotEquivOfEq_mk]
  let φ := quotAddEquivOfCoeEq (𝔪T • (⊤ : Submodule T M)) (𝔪S • (⊤ : Submodule S M))
    ((coe_map_smul_top (A := T) (M := M) (maximalIdeal R)).trans
      (coe_map_smul_top (A := S) (M := M) (maximalIdeal R)).symm)
  have hφmk : ∀ x : M, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun _ => rfl
  refine Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv e φ fun a n => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (𝔪T • (⊤ : Submodule T M)) n
  have hTt := Module.IsTorsionBySet.mk_smul
    (Module.isTorsionBySet_quotient_ideal_smul M 𝔪T) t (Submodule.Quotient.mk m)
  have hSs := Module.IsTorsionBySet.mk_smul
    (Module.isTorsionBySet_quotient_ideal_smul M 𝔪S) (algebraMap T S t)
    (Submodule.Quotient.mk m : M ⧸ (𝔪S • (⊤ : Submodule S M)))
  rw [hTt, hemk, hφmk, hSs, algebraMap_smul]
  exact hφmk _

/-- Let `R → S → S'` be ring maps of local rings with `S → S'` local and `R → S'` essentially of
finite presentation, and let `M` be a nonzero finitely presented `S'`-module, flat over `R`, whose
fibre `M/𝔪M` is flat over `S/𝔪S`. Let `B` be a local `R`-algebra, essentially of finite
presentation, with `𝔪B` inside the maximal ideal of `B` and `B → S` surjective, and let `J` be a
finitely generated ideal contained in `ker (B → S)` with `ker (B → S) ≤ J + 𝔪B`. Then `B ⧸ J` is
flat over `R`. -/
private theorem flat_quotient_of_flat_fibre {R B S S' M : Type*} [CommRing R] [CommRing B]
    [CommRing S] [CommRing S'] [IsLocalRing R] [IsLocalRing B] [IsLocalRing S] [IsLocalRing S']
    [Algebra R B] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M]
    [Module.FinitePresentation S' M] [Nontrivial M] [Module.Flat R M]
    [Module.Flat (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))]
    (hB : (algebraMap R B).EssentiallyOfFinitePresentation)
    (hS' : (algebraMap R S').EssentiallyOfFinitePresentation)
    (hsurj : Function.Surjective (algebraMap B S))
    (hmle : (maximalIdeal R).map (algebraMap R B) ≤ maximalIdeal B)
    (J : Ideal B) (hJfg : J.FG) (hJle : J ≤ RingHom.ker (algebraMap B S))
    (hJsup : RingHom.ker (algebraMap B S) ≤ J ⊔ (maximalIdeal R).map (algebraMap R B)) :
    Module.Flat R (B ⧸ J) := by
  have hntT : Nontrivial (B ⧸ J) := Submodule.Quotient.nontrivial_iff.mpr fun h =>
    RingHom.ker_ne_top (algebraMap B S) (top_le_iff.mp (h ▸ hJle))
  have hlocT : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmkalg : ∀ r : R, Ideal.Quotient.mk J (algebraMap R B r) = algebraMap R (B ⧸ J) r :=
    Ideal.Quotient.mk_algebraMap R J
  have hcompeq : algebraMap R (B ⧸ J) = (Ideal.Quotient.mk J).comp (algebraMap R B) :=
    RingHom.ext fun r => (hmkalg r).symm
  let f : (B ⧸ J) →+* S :=
    Ideal.Quotient.lift J (algebraMap B S) fun a ha => RingHom.mem_ker.mp (hJle ha)
  have hf : ∀ b : B, f (Ideal.Quotient.mk J b) = algebraMap B S b := fun b =>
    Ideal.Quotient.lift_mk _ _ _
  have hfR : ∀ r : R, f (algebraMap R (B ⧸ J) r) = algebraMap R S r := fun r => by
    rw [← hmkalg, hf, ← IsScalarTower.algebraMap_apply]
  let algTS : Algebra (B ⧸ J) S := f.toAlgebra
  have halgTS : algebraMap (B ⧸ J) S = f := rfl
  let algTS' : Algebra (B ⧸ J) S' := ((algebraMap S S').comp f).toAlgebra
  have halgTS' : ∀ x : B ⧸ J, algebraMap (B ⧸ J) S' x = algebraMap S S' (f x) := fun _ => rfl
  have towerRTS : IsScalarTower R (B ⧸ J) S :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [halgTS, hfR]
  have towerRTS' : IsScalarTower R (B ⧸ J) S' :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [halgTS', hfR, ← IsScalarTower.algebraMap_apply]
  let modTM : Module (B ⧸ J) M := Module.compHom M f
  have hsmulTM : ∀ (x : B ⧸ J) (m : M), x • m = f x • m := fun _ _ => rfl
  have towerTSM : IsScalarTower (B ⧸ J) S M :=
    IsScalarTower.of_algebraMap_smul fun x m => by rw [halgTS, hsmulTM]
  have towerTS'M : IsScalarTower (B ⧸ J) S' M :=
    IsScalarTower.of_algebraMap_smul fun x m => by rw [halgTS', algebraMap_smul, hsmulTM]
  have towerRTM : IsScalarTower R (B ⧸ J) M :=
    IsScalarTower.of_algebraMap_smul fun r m => by rw [hsmulTM, hfR, algebraMap_smul]
  have hfsurj : Function.Surjective (algebraMap (B ⧸ J) S) := fun s =>
    let ⟨b, hb⟩ := hsurj s; ⟨Ideal.Quotient.mk J b, by rw [halgTS, hf, hb]⟩
  have hkerf : RingHom.ker (algebraMap (B ⧸ J) S)
      ≤ (maximalIdeal R).map (algebraMap R (B ⧸ J)) := by
    rw [halgTS]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hf] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hJsup (RingHom.mem_ker.mpr hx))
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add, hcompeq, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hz
  have hfibre := flat_fibre_of_ker_le_map_maximalIdeal (R := R) (T := B ⧸ J) (S := S) (M := M)
    hfsurj hkerf
  have hRB : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 3 1).mp hmle
  have hmkJ : IsLocalHom (Ideal.Quotient.mk J) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hRT : IsLocalHom (algebraMap R (B ⧸ J)) := hcompeq ▸ RingHom.isLocalHom_comp _ _
  have hfloc : IsLocalHom (algebraMap (B ⧸ J) S) := Function.Surjective.isLocalHom _ hfsurj
  have hTS' : IsLocalHom (algebraMap (B ⧸ J) S') :=
    RingHom.isLocalHom_comp (algebraMap S S') (algebraMap (B ⧸ J) S)
  have hefpT : (algebraMap R (B ⧸ J)).EssentiallyOfFinitePresentation :=
    essentiallyOfFinitePresentation_of_surjective_of_fg_ker hB Ideal.Quotient.mk_surjective
      (by rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
  exact (Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal (R := R) (S := B ⧸ J)
    (S' := S') (M := M) hefpT hS').1

end Stacks.Flatness.FibrewiseCriterionEssFP

open IsLocalRing Stacks.Flatness.FibrewiseCriterionEssFP in
/-- Let `R → S → S'` be local homomorphisms of local rings, let `𝔪` be the maximal
ideal of `R`, and let `M` be a nonzero `S'`-module of finite presentation. Assume `R → S'` is
essentially of finite presentation, `R → S` is essentially of finite type, `M` is flat over `R`,
and the fibre `M/𝔪M` is flat over `S/𝔪S`. Then `R → S` is essentially of finite presentation, `S`
is flat over `R`, and `M` is flat over `S`.

Here `𝔪S` is `(maximalIdeal R).map (algebraMap R S)` and `𝔪M` is `𝔪S • ⊤`, so that `M/𝔪M` is a
module over the fibre ring `S/𝔪S`. -/
@[stacks 05UV "\"Essentially of finite type\" is Mathlib's `Algebra.EssFiniteType` (Definition
00QM (1)); \"essentially of finite presentation\" is `RingHom.EssentiallyOfFinitePresentation`
(Definition 00QM (2)), Mathlib having no such predicate. The chain `R → S → S'` is
`IsScalarTower R S S'`, `𝔪S` is `(maximalIdeal R).map (algebraMap R S)` and `𝔪M` is `𝔪S • ⊤` over
`S`, so that the fibre `M/𝔪M` is a module over the ring `S/𝔪S`. \"`M` is not zero\" is
`Nontrivial M`. The three conclusions are conjoined; see the module docstring.",
  ega "IV 11.3.10" "special case",
  sga "1 I 5.9" "partial",
  sga "1 IV 5.9" "(ii) ⇒ (i)",
  sga "3 VIB 1.3.0" "special case",
  sga "3 VIB 12.7" "special case",
  sga "3 VIB 2.5" "flatness clause",
  sga "3 X 3.5" "Flat case"]
public theorem
    Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal
    {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M]
    [Algebra.EssFiniteType R S] [Module.FinitePresentation S' M] [Nontrivial M] [Module.Flat R M]
    [Module.Flat (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))]
    (hS' : (algebraMap R S').EssentiallyOfFinitePresentation) :
    (algebraMap R S).EssentiallyOfFinitePresentation ∧ Module.Flat R S ∧ Module.Flat S M := by
  have hS : (algebraMap R S).EssentiallyOfFinitePresentation := by
    obtain ⟨B, instB, instLocB, instRB, instBS, instTower, hB, hsurj, hmle, hNoeth⟩ :=
      exists_essFP_surjective_of_essFiniteType R S
    let := instB; let := instLocB; let := instRB; let := instBS; let := instTower
    have := hNoeth
    exact essentiallyOfFinitePresentation_of_surjective_of_fg_ker hB hsurj
      (fg_of_forall_flat_quotient (𝔪 := maximalIdeal R)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hmle) _
        fun J hJle hJfg hJsup => flat_quotient_of_flat_fibre (M := M) hB hS' hsurj hmle J hJfg hJle
          hJsup)
  exact ⟨hS, Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal (S' := S') (M := M) hS hS'⟩
