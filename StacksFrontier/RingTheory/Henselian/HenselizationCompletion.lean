module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Completions and uniqueness of henselizations

A local ring and its henselization have the same adic completion: the structure map is flat and
induces an isomorphism on residue fields, hence on all quotients by powers of the maximal ideal.
The resulting isomorphism of completions is natural in the base, and the henselization itself is
unique up to a unique isomorphism over the base, even when base and henselization live in
unrelated universes.

## Main results

* `StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization`: the completion of a local
  ring is isomorphic to the completion of its henselization, compatibly with the completion maps.
* `StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization_square`: a local homomorphism
  of henselizations lying over a homomorphism of the bases whose completions agree induces an
  isomorphism of the completions of the henselizations.
* `StacksDraft.exists_ringEquiv_of_isHenselization`: two henselizations of a local ring, in
  arbitrary universes, are isomorphic over the base.
* `StacksDraft.isRegularLocalRing_iff_of_isHenselization`: a Noetherian local ring is regular if
  and only if its henselization is.

## References

* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace StacksDraft

/-- A compatible family of isomorphisms between the quotients by the powers of two ideals
assembles into an isomorphism of the adic completions. -/
private theorem exists_adicCompletion_equiv_of_quotient_equiv
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S)
    (he : ∀ n : ℕ, ∃ e : (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n),
      ∀ x : R, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x)) :
    ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ x : R, e (algebraMap R (AdicCompletion I R) x) =
        algebraMap S (AdicCompletion J S) (f x) := by
  classical
  choose e he using he
  have hnaturality {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
      e m (Ideal.Quotient.factorPow I hmn x) =
        Ideal.Quotient.factorPow J hmn (e n x) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, he]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J
      (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
      (fun {m n} hmn => by
        apply RingHom.ext
        intro x
        change Ideal.Quotient.factorPow J hmn (e n (AdicCompletion.evalₐ I n x)) =
          e m (AdicCompletion.evalₐ I m x)
        rw [← hnaturality, AdicCompletion.factorPow_evalₐ])
  have hmap (n : ℕ) (x : AdicCompletion I R) :
      AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    AdicCompletion.evalₐ_liftRingHom J _ _ n x
  let g : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I
      (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
      (fun {m n} hmn => by
        apply RingHom.ext
        intro x
        apply (e m).injective
        change e m (Ideal.Quotient.factorPow I hmn
            ((e n).symm (AdicCompletion.evalₐ J n x))) =
          e m ((e m).symm (AdicCompletion.evalₐ J m x))
        rw [hnaturality, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
          AdicCompletion.factorPow_evalₐ])
  have hg (n : ℕ) (x : AdicCompletion J S) :
      AdicCompletion.evalₐ I n (g x) = (e n).symm (AdicCompletion.evalₐ J n x) :=
    AdicCompletion.evalₐ_liftRingHom I _ _ n x
  have hleft : Function.LeftInverse g F := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hg, hmap, RingEquiv.symm_apply_apply]
  have hright : Function.RightInverse g F := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hmap, hg, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofBijective F
    ⟨hleft.injective, hright.surjective⟩, fun x => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n (F
    (algebraMap R (AdicCompletion I R) x)) = _
  rw [hmap]
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of] using he n x

/-- **The completion of a henselization.** A local ring and its henselization have canonically
isomorphic adic completions, compatibly with the two completion maps. -/
theorem exists_adicCompletion_ringEquiv_of_isHenselization
    {R : Type u} {H : Type v} [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal H) H,
      ∀ r : R, e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap H (AdicCompletion (IsLocalRing.maximalIdeal H) H) (algebraMap R H r) := by
  let := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := H)
  let := IsHenselization.flat (R := R) (L := ResidueField R) (Rh := H)
  have hm := IsHenselization.map_maximalIdeal (R := R) (L := ResidueField R) (Rh := H)
  have hr := IsHenselization.residueField_map_bijective (R := R) (Rh := H)
  have hq : Function.Bijective (Ideal.quotientMap
      ((maximalIdeal R).map (algebraMap R H)) (algebraMap R H) Ideal.le_comap_map) := by
    let e := Ideal.quotEquivOfEq hm
    have he : e.toRingHom.comp (Ideal.quotientMap
        ((maximalIdeal R).map (algebraMap R H)) (algebraMap R H) Ideal.le_comap_map) =
        ResidueField.map (algebraMap R H) := by
      ext r
      rfl
    have hh : Function.Bijective (e.toRingHom.comp (Ideal.quotientMap
        ((maximalIdeal R).map (algebraMap R H)) (algebraMap R H) Ideal.le_comap_map)) :=
      he.symm ▸ hr
    rw [RingHom.coe_comp] at hh
    exact (e.bijective.of_comp_iff' _).mp hh
  apply exists_adicCompletion_equiv_of_quotient_equiv (algebraMap R H)
    (maximalIdeal R) (maximalIdeal H)
  intro n
  have hn : (maximalIdeal R ^ n).map (algebraMap R H) = maximalIdeal H ^ n := by
    rw [Ideal.map_pow, hm]
  exact ⟨(RingEquiv.ofBijective _
    (quotientMap_pow_bijective_of_flat (maximalIdeal R) hq n)).trans
      (Ideal.quotEquivOfEq hn), fun r => rfl⟩

/-- An element of an adic completion all of whose truncations are units is a unit. -/
private theorem adicCompletion_isUnit_of_forall
    {R : Type*} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    (hx : ∀ n, IsUnit (x.val n)) : IsUnit x := by
  classical
  let y : AdicCompletion I R := ⟨fun n => ↑((hx n).unit⁻¹), by
    intro m n hmn
    change (AdicCompletion.transitionMapₐ I hmn) ↑((hx n).unit⁻¹) = _
    have hmap : Units.map (AdicCompletion.transitionMapₐ I hmn).toMonoidHom (hx n).unit =
        (hx m).unit := by
      apply Units.ext
      simp only [Units.coe_map, IsUnit.unit_spec]
      exact x.property hmn
    have hh := congrArg (fun z : (R ⧸ (I ^ m • (⊤ : Ideal R)))ˣ =>
      (↑(z⁻¹) : R ⧸ (I ^ m • (⊤ : Ideal R)))) hmap
    simp only [← map_inv, Units.coe_map] at hh
    exact hh⟩
  refine isUnit_iff_exists_inv.mpr ⟨y, ?_⟩
  apply AdicCompletion.ext
  intro n
  change x.val n * ↑((hx n).unit⁻¹) = 1
  simpa only [IsUnit.unit_spec] using (hx n).unit.mul_inv

/-- Evaluation of the maximal-adic completion of a local ring at level one is a local
homomorphism. -/
private theorem adicCompletion_evalOne_isLocalHom
    {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom := by
  refine ⟨fun x hx => adicCompletion_isUnit_of_forall _ x fun n => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val n)
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ (maximalIdeal R ^ 0 • (⊤ : Ideal R))) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    rw [Subsingleton.elim (x.val 0) 1]
    exact isUnit_one
  have hna : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hres : residue R a = AdicCompletion.evalOneₐ (maximalIdeal R) x := by
    have hh := x.property hna
    rw [← ha] at hh
    change Ideal.Quotient.mk _ a = x.val 1 at hh
    change Ideal.Quotient.mk _ a = _
    let F : (R ⧸ (maximalIdeal R ^ 1 • (⊤ : Ideal R))) →+* ResidueField R :=
      Ideal.Quotient.factor (by simp)
    have hh' := congrArg F hh
    change Ideal.Quotient.mk _ a = F (x.val 1) at hh'
    simp only [smul_eq_mul, AdicCompletion.evalOneₐ, AdicCompletion.evalₐ,
      Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ, AdicCompletion.eval, AlgHom.coe_comp,
      Function.comp_apply, AlgHom.ofLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_comp_apply, F] at hh' ⊢
    exact hh'
  have hau : IsUnit a := IsUnit.of_map (residue R) a (hres ▸ hx)
  rw [← ha]
  exact hau.map _

/-- The completion map of a local ring into its maximal-adic completion is a local
homomorphism. -/
private theorem adicCompletion_algebraMap_isLocalHom
    {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  ⟨fun r hr => IsUnit.of_map (residue R) r
    (hr.map (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom)⟩

/-- Evaluation of the maximal-adic completion of a local ring at a nonzero level is a local
homomorphism. -/
private theorem adicCompletion_eval_isLocalHom
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) (hn : n ≠ 0) :
    IsLocalHom (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom := by
  let := adicCompletion_evalOne_isLocalHom (R := R)
  refine ⟨fun x hx => ?_⟩
  apply IsUnit.of_map (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom x
  have h := hx.map (Ideal.Quotient.factorPow (maximalIdeal R)
    (Nat.one_le_iff_ne_zero.mpr hn))
  change IsUnit (Ideal.Quotient.factorPow (maximalIdeal R) _
    (AdicCompletion.evalₐ (maximalIdeal R) n x)) at h
  rw [AdicCompletion.factorPow_evalₐ] at h
  exact h.map (Ideal.quotientEquivAlgOfEq R (pow_one (maximalIdeal R)))

/-- Two local homomorphisms from a henselization into the completion of a henselian local ring
which agree on the base are equal. -/
private theorem henselization_hom_ext_to_adicCompletion
    {R : Type*} {H : Type*} {K : Type*}
    [CommRing R] [IsLocalRing R] [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsHenselization R (ResidueField R) H] [CommRing K] [HenselianLocalRing K]
    (f g : H →+* AdicCompletion (maximalIdeal K) K) [IsLocalHom f] [IsLocalHom g]
    (h : f.comp (algebraMap R H) = g.comp (algebraMap R H)) : f = g := by
  let := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := H)
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (K ⧸ maximalIdeal K ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  let Q := K ⧸ maximalIdeal K ^ n
  have hne : maximalIdeal K ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal K).ne_top (Ideal.pow_le_self hn)
  let : HenselianLocalRing Q := Stacks.Henselian.henselianLocalRing_quotient hne
  let := adicCompletion_eval_isLocalHom (R := K) n hn
  let fn : H →+* Q := (AdicCompletion.evalₐ (maximalIdeal K) n).toRingHom.comp f
  let gn : H →+* Q := (AdicCompletion.evalₐ (maximalIdeal K) n).toRingHom.comp g
  let : IsLocalHom fn := RingHom.isLocalHom_comp _ _
  let : IsLocalHom gn := RingHom.isLocalHom_comp _ _
  let : Algebra R Q := (fn.comp (algebraMap R H)).toAlgebra
  let : IsLocalHom (algebraMap R Q) := RingHom.isLocalHom_comp _ _
  let fa : H →ₐ[R] Q := { __ := fn, commutes' _ := rfl }
  let ga : H →ₐ[R] Q :=
    { __ := gn
      commutes' := fun r => by
        change gn (algebraMap R H r) = fn (algebraMap R H r)
        exact congrArg (AdicCompletion.evalₐ (maximalIdeal K) n) (RingHom.congr_fun h r).symm }
  have hfa : IsLocalHom fa := ⟨fun x hx =>
    (RingHom.isLocalHom_comp _ _ : IsLocalHom fn).map_nonunit x hx⟩
  have hga : IsLocalHom ga := ⟨fun x hx =>
    (RingHom.isLocalHom_comp _ _ : IsLocalHom gn).map_nonunit x hx⟩
  have hh := existsUnique_isLocalHom_of_indEtale (A := R) (B := H) (C := Q)
    (indEtale_of_isHenselization (ResidueField R))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := H)).2
  exact congrArg (fun t : H →ₐ[R] Q => t x) (hh.unique hfa hga)

/-- **Completions of henselizations in a commutative square.** A local homomorphism of
henselizations lying over a homomorphism of the base rings whose completions agree induces an
isomorphism of the completions of the henselizations, compatible with the completion maps. -/
theorem exists_adicCompletion_ringEquiv_of_isHenselization_square
    {R S H K : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H]
    [CommRing K] [IsLocalRing K] [Algebra S K]
    [IsLocalRing.IsHenselization S (IsLocalRing.ResidueField S) K]
    (r : R →+* S) (f : H →+* K) [IsLocalHom f]
    (h : f.comp (algebraMap R H) = (algebraMap S K).comp r)
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (he : ∀ x : R, e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) x) =
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (r x)) :
    ∃ E : AdicCompletion (IsLocalRing.maximalIdeal H) H ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal K) K,
      E.toRingHom.comp (algebraMap H (AdicCompletion (IsLocalRing.maximalIdeal H) H)) =
        (algebraMap K (AdicCompletion (IsLocalRing.maximalIdeal K) K)).comp f := by
  obtain ⟨eH, heH⟩ := exists_adicCompletion_ringEquiv_of_isHenselization (R := R) (H := H)
  obtain ⟨eK, heK⟩ := exists_adicCompletion_ringEquiv_of_isHenselization (R := S) (H := K)
  let E := eH.symm.trans (e.trans eK)
  refine ⟨E, ?_⟩
  let := IsHenselization.henselian S (ResidueField S) (Rh := K)
  let := adicCompletion_algebraMap_isLocalHom (R := H)
  let := adicCompletion_algebraMap_isLocalHom (R := K)
  let : IsLocalHom E.toRingHom := isLocalHom_toRingHom E
  let : IsLocalHom (E.toRingHom.comp (algebraMap H (AdicCompletion (maximalIdeal H) H))) :=
    RingHom.isLocalHom_comp _ _
  let : IsLocalHom ((algebraMap K (AdicCompletion (maximalIdeal K) K)).comp f) :=
    RingHom.isLocalHom_comp _ _
  apply henselization_hom_ext_to_adicCompletion (R := R)
  refine RingHom.ext fun x => ?_
  change eK (e (eH.symm (algebraMap H _ (algebraMap R H x)))) =
    algebraMap K _ (f (algebraMap R H x))
  rw [← heH, eH.symm_apply_apply, he, heK]
  exact congrArg (algebraMap K _) (RingHom.congr_fun h x).symm

/-- A composite of local algebra maps `B → C → B` out of an ind-étale `A`-algebra `B` with
surjective residue field map, over a henselian `B`, is the identity. -/
private theorem comp_eq_id_of_indEtale
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [IsLocalRing A]
    [CommRing B] [HenselianLocalRing B] [CommRing C] [IsLocalRing C] [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] (hi : IndEtale A B)
    (hs : Function.Surjective (ResidueField.map (algebraMap A B)))
    (f : B →ₐ[A] C) (g : C →ₐ[A] B) [hf : IsLocalHom f] [hg : IsLocalHom g] :
    g.comp f = AlgHom.id A B :=
  (existsUnique_isLocalHom_of_indEtale (C := B) hi hs).unique
    ⟨fun x hx => hf.map_nonunit x (hg.map_nonunit (f x) hx)⟩ ⟨fun _ hx => hx⟩

/-- **Cross-universe uniqueness of the henselization.** Two henselizations of a local ring, in
arbitrary universes, are isomorphic by an isomorphism commuting with the structure maps. -/
theorem exists_ringEquiv_of_isHenselization
    {R : Type u} {H : Type v} {H' : Type w} [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H]
    [CommRing H'] [IsLocalRing H'] [Algebra R H']
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H'] :
    ∃ e : H ≃+* H', ∀ r : R, e (algebraMap R H r) = algebraMap R H' r := by
  let : IsLocalHom (algebraMap R H) :=
    IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := H)
  let : IsLocalHom (algebraMap R H') :=
    IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := H')
  let : HenselianLocalRing H := IsHenselization.henselian R (ResidueField R) (Rh := H)
  let : HenselianLocalRing H' := IsHenselization.henselian R (ResidueField R) (Rh := H')
  have hiH : IndEtale R H := indEtale_of_isHenselization (ResidueField R)
  have hiH' : IndEtale R H' := indEtale_of_isHenselization (ResidueField R)
  have hsH : Function.Surjective (ResidueField.map (algebraMap R H)) :=
    (IsHenselization.residueField_map_bijective (R := R) (Rh := H)).2
  have hsH' : Function.Surjective (ResidueField.map (algebraMap R H')) :=
    (IsHenselization.residueField_map_bijective (R := R) (Rh := H')).2
  obtain ⟨f, hf, -⟩ := existsUnique_isLocalHom_of_indEtale (C := H') hiH hsH
  obtain ⟨g, hg, -⟩ := existsUnique_isLocalHom_of_indEtale (C := H) hiH' hsH'
  exact ⟨(AlgEquiv.ofAlgHom f g (comp_eq_id_of_indEtale hiH' hsH' g f)
    (comp_eq_id_of_indEtale hiH hsH f g)).toRingEquiv, f.commutes⟩

/-- **Regularity is invariant under henselization.** A Noetherian local ring is a regular local
ring if and only if its henselization is, in any universe. -/
@[ega "IV 18.6.10"]
theorem isRegularLocalRing_iff_of_isHenselization
    {R : Type u} {H : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H] :
    IsRegularLocalRing R ↔ IsRegularLocalRing H := by
  let κ := SeparableClosure (ResidueField R)
  let T := henselizationTower R κ
  obtain ⟨e, -⟩ := exists_ringEquiv_of_isHenselization (R := R) (H := H) (H' := T.henselization)
  exact (isRegularLocalRing_iff_henselizations R T.henselization T.strictHenselization κ).1.trans
    ⟨fun _ => IsRegularLocalRing.of_ringEquiv e.symm, fun _ => IsRegularLocalRing.of_ringEquiv e⟩

end StacksDraft

end
