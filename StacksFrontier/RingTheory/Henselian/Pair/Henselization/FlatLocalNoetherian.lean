module

public import StacksFrontier.RingTheory.Henselian.Pair.Henselization.UniversalProperty

/-!
# Henselization of a pair: flatness, local rings and Noetherian pairs

The henselization `A → A^h` of a pair `(A, I)` is flat and does not change the quotient:
`A / Iⁿ → A^h / (I^h)ⁿ` is an isomorphism for every `n`. For a local ring and its maximal ideal it
recovers the usual henselization, and for a Noetherian pair it is again Noetherian with the same
adic completion.

## Main results

* `flat_henselization_and_bijective_quotientMap`: `A → A^h` is flat and `A / Iⁿ ≃ A^h / (I^h)ⁿ`.
* `isHenselization_of_henselizationPair`: for a local ring this is the henselization.
* `henselization_isNoetherian_and_completion_equiv`: Noetherianness and the adic completion are
  preserved.

## References

* [Stacks: Tag 0EM7](https://stacks.math.columbia.edu/tag/0EM7)
-/

public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial
open scoped TensorProduct
open Stacks.Henselization.EtaleColimit

universe u v w

section


/-- An ind-étale `A`-algebra `B` is flat, and if `A ⧸ I → B ⧸ I B` is bijective then so is
`A ⧸ Iⁿ → B ⧸ Iⁿ B` for every `n`. -/
public theorem flat_and_bijective_quotientMap_pow_of_ind_etale
    (A : Type u) [CommRing A] (I : Ideal A)
    (B : Type v) [CommRing B] [Algebra A B]
    (h_ind : (CommAlgCat.etale.{v} A).ind.{v} (CommAlgCat.of A B))
    (h_mod_I : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map)) :
    Module.Flat A B ∧ ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap ((I ^ n).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map) := by
  have : Module.Flat A B := CommAlgCat.flat_of_ind_etale h_ind
  exact ⟨this, quotientMap_pow_bijective_of_flat I h_mod_I⟩

/-- The structural map to the henselization of a pair is flat, and it induces an isomorphism modulo
every power of the distinguished ideal. -/
@[stacks 0AGU]
public theorem flat_henselization_and_bijective_quotientMap
    (A : Type u) [CommRing A] (I : Ideal A)
    (Ah : Type v) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) :
    Module.Flat A Ah ∧
      ∀ n : ℕ,
        Function.Bijective
          (Ideal.quotientMap (Ideal.map (algebraMap A Ah) (I ^ n))
            (algebraMap A Ah) Ideal.le_comap_map) := by
  obtain ⟨e⟩ := nonempty_algEquiv_henselization A I Ah hh hι
  obtain ⟨hflat, hpow⟩ := flat_and_bijective_quotientMap_pow_of_ind_etale A I
    (henselization A I : Type u) (ind_henselization A I)
    (bijective_quotientMap_henselization A I)
  let H := (henselization A I : Type u)
  have : Module.Flat A H := hflat
  refine ⟨Module.Flat.of_linearEquiv e.symm.toLinearEquiv, fun n => ?_⟩
  let q := Ideal.quotientEquivAlg ((I ^ n).map (algebraMap A H))
    ((I ^ n).map (algebraMap A Ah)) e (by
      rw [Ideal.map_map]
      exact congrArg (fun f : A →+* Ah => (I ^ n).map f) e.toAlgHom.comp_algebraMap.symm)
  have hq : Ideal.quotientMap ((I ^ n).map (algebraMap A Ah))
      (algebraMap A Ah) Ideal.le_comap_map =
        q.toRingEquiv.toRingHom.comp (Ideal.quotientMap ((I ^ n).map (algebraMap A H))
          (algebraMap A H) Ideal.le_comap_map) := by
    ext a
    exact congrArg (Ideal.Quotient.mk _) (e.commutes a).symm
  rw [hq, RingHom.coe_comp]
  exact q.bijective.comp (hpow n)

end

section

private theorem henselianLocalRing_of_henselianPair_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R]
    (h : HenselianPair R (maximalIdeal R)) : HenselianLocalRing R := by
  refine ⟨fun f hf a₀ ha₀ hu ↦ ?_⟩
  let q : R →+* ResidueField R := Ideal.Quotient.mk (maximalIdeal R)
  let fb : (ResidueField R)[X] := f.map q
  let ab : ResidueField R := q a₀
  let g₀ : (ResidueField R)[X] := X - C ab
  let h₀ : (ResidueField R)[X] := fb /ₘ g₀
  have hroot : fb.IsRoot ab := by
    rw [IsRoot]
    change Polynomial.eval (q a₀) (f.map q) = 0
    rw [Polynomial.eval_map, eval₂_at_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 ha₀
  have hfac : fb = g₀ * h₀ := by
    symm
    exact (mul_divByMonic_eq_iff_isRoot (p := fb) (a := ab)).2 hroot
  have hfb : fb.Monic := hf.map q
  have hg₀ : g₀.Monic := monic_X_sub_C ab
  have hh₀ : h₀.Monic := hg₀.of_mul_monic_left (hfac ▸ hfb)
  have hderiv : fb.derivative.eval ab ≠ 0 := by
    have hu' : IsUnit (q (f.derivative.eval a₀)) := hu.map q
    simpa [fb, ab, Polynomial.eval_map] using hu'.ne_zero
  have hcop : IsCoprime g₀ h₀ :=
    isCoprime_of_is_root_of_eval_derivative_ne_zero fb ab hderiv
  obtain ⟨g, k, hg, hk, hfk, hgq, -⟩ := h.2 f hf g₀ h₀ hg₀ hh₀ hfac hcop
  change g.map q = g₀ at hgq
  have hdeg : g.natDegree = 1 := by
    rw [← hg.natDegree_map q, hgq]
    simp [g₀]
  let a : R := -g.coeff 0
  have hgeq : g = X - C a := by
    rw [hg.eq_X_add_C hdeg]
    simp [a]
  refine ⟨a, ?_, ?_⟩
  · rw [hfk, hgeq, IsRoot, eval_mul]
    simp
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    have hc := congrArg (fun p : (ResidueField R)[X] ↦ p.coeff 0) hgq
    have hc' : q (g.coeff 0) = -ab := by
      simpa [Polynomial.coeff_map, g₀] using hc
    change -(q (g.coeff 0)) - q a₀ = 0
    rw [hc']
    simp [ab]

/-- A henselization of the pair consisting of a local ring and its maximal ideal is a henselization
of the local ring. In particular, the target is local and the structural map is a local ring
homomorphism. -/
@[stacks 0A03]
public theorem isHenselization_of_henselizationPair
    (A : Type u) [CommRing A] [IsLocalRing A]
    (Ah : Type u) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah
      ((maximalIdeal A).map (algebraMap A Ah)))
    (hι : ∀ (B : Type u) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, maximalIdeal A ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧
              (maximalIdeal A).map (algebraMap A Ah) ≤ J.comap g) :
    ∃ (_ : IsLocalRing Ah) (_ : IsLocalHom (algebraMap A Ah)),
      IsHenselization A (ResidueField A) Ah := by
  let J : Ideal Ah := (maximalIdeal A).map (algebraMap A Ah)
  obtain ⟨-, hquot⟩ := flat_henselization_and_bijective_quotientMap
    A (maximalIdeal A) Ah hh hι
  have hq : Function.Bijective
      (Ideal.quotientMap J (algebraMap A Ah) Ideal.le_comap_map) := by
    change Function.Bijective
      (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A Ah))
        (algebraMap A Ah) Ideal.le_comap_map)
    have hq' := hquot 1
    rwa [pow_one] at hq'
  let eQ : ResidueField A ≃+* Ah ⧸ J :=
    RingEquiv.ofBijective (Ideal.quotientMap J (algebraMap A Ah) Ideal.le_comap_map) hq
  let hfield : IsField (Ah ⧸ J) :=
    @MulEquiv.isField (Ah ⧸ J) (ResidueField A) _ _
      (Field.toIsField (ResidueField A)) eQ.symm.toMulEquiv
  let : IsField (Ah ⧸ J) := hfield
  have hJmax : J.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).2 hfield
  have hlocal : IsLocalRing Ah := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨J, hJmax, fun M hM ↦ ?_⟩
    symm
    apply hJmax.eq_of_le hM.ne_top
    have : M.IsMaximal := hM
    exact hh.1.trans (by
      rw [Ideal.jacobson_bot]
      exact Ring.jacobson_le_of_isMaximal M)
  let : IsLocalRing Ah := hlocal
  have hJ : J = maximalIdeal Ah := IsLocalRing.eq_maximalIdeal hJmax
  have hlocalHom : IsLocalHom (algebraMap A Ah) := by
    apply ((local_hom_TFAE (algebraMap A Ah)).out 5 1).mp
    rw [← hJ]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hq.1 (by simpa using hx)
    · exact Ideal.le_comap_map
  let : IsLocalHom (algebraMap A Ah) := hlocalHom
  have hhens : HenselianLocalRing Ah := by
    apply henselianLocalRing_of_henselianPair_maximalIdeal Ah
    change HenselianPair Ah J at hh
    rwa [hJ] at hh
  let : HenselianLocalRing Ah := hhens
  obtain ⟨e⟩ := nonempty_algEquiv_henselization
    A (maximalIdeal A) Ah hh hι
  have hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A Ah) :=
    ((CommAlgCat.etale.{u} A).ind.{u}).prop_iff_of_iso
      (CommAlgCat.isoMk e) |>.mp (ind_henselization A (maximalIdeal A))
  let eResidue : ResidueField A ≃+* ResidueField Ah :=
    eQ.trans (Ideal.quotEquivOfEq hJ)
  refine ⟨hlocal, hlocalHom,
    IsLocalRing.IsHenselization.of_ind_etale.{u, _, 0} hhens hind ⟨eResidue, fun x ↦ ?_⟩⟩
  rfl

end

section

namespace Rig

/-- An `A`-algebra whose adic completion agrees with that of `A` maps canonically to the
adic completion of `A`. -/
@[expose]
public noncomputable def toAdicCompletionOfBijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    (hb : Function.Bijective
      (adicCompletionMap (algebraMap A B) I
        (I.map (algebraMap A B)) le_rfl)) : B →ₐ[A] AdicCompletion I A := by
  let F := adicCompletionMap (algebraMap A B) I
    (I.map (algebraMap A B)) le_rfl
  let E := RingEquiv.ofBijective F hb
  have hF (a : A) : F (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) (algebraMap A B a) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    unfold F adicCompletionMap
    rw [AdicCompletion.evalₐ_liftRingHom]
    simp
  refine
    { toRingHom := E.symm.toRingHom.comp
        (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B))
      commutes' := fun a ↦ ?_ }
  apply E.injective
  change E (E.symm
      (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) (algebraMap A B a))) =
    E (algebraMap A (AdicCompletion I A) a)
  rw [E.apply_symm_apply]
  exact (hF a).symm

end Rig

/-- The henselization of a Noetherian pair is Noetherian and has the same adic completion. The
structural map to the henselization is flat, and the canonical map from the henselization to the
original completion is faithfully flat (and hence, in particular, flat). -/
@[stacks 0AGV]
public theorem henselization_isNoetherian_and_completion_equiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (Ah : Type v) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) :
    Function.Bijective
        (adicCompletionMap (algebraMap A Ah) I
          (I.map (algebraMap A Ah)) le_rfl) ∧
      IsNoetherianRing Ah ∧
        (algebraMap A Ah).Flat ∧
        ∃ g : Ah →ₐ[A] AdicCompletion I A,
          g.toRingHom.Flat ∧
            g.toRingHom.FaithfullyFlat := by
  obtain ⟨hflat, hpow⟩ :=
    flat_henselization_and_bijective_quotientMap A I Ah hh hι
  have hcompletion := Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective
    (algebraMap A Ah) I hpow
  let H := (henselization A I : Type u)
  obtain ⟨e⟩ := nonempty_algEquiv_henselization A I Ah hh hι
  obtain ⟨_, hHpow⟩ :=
    flat_and_bijective_quotientMap_pow_of_ind_etale A I H
      (ind_henselization A I)
      (bijective_quotientMap_henselization A I)
  have hHcompletion := Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective
    (algebraMap A H) I hHpow
  let k : H →ₐ[A] AdicCompletion I A := Rig.toAdicCompletionOfBijective I hHcompletion
  let : Algebra H (AdicCompletion I A) := k.toRingHom.toAlgebra
  let : IsScalarTower A H (AdicCompletion I A) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (k.commutes a).symm
  have hkflat : Module.Flat H (AdicCompletion I A) :=
    CommAlgCat.flat_of_ind_etale_restrictScalars (ind_henselization A I)
  have hkflat' : k.toRingHom.Flat := RingHom.flat_algebraMap_iff.mpr hkflat
  let F := adicCompletionMap (algebraMap A H) I
    (I.map (algebraMap A H)) le_rfl
  let E := RingEquiv.ofBijective F hHcompletion
  let lE : AdicCompletion I A ≃ₗ[H]
      AdicCompletion (I.map (algebraMap A H)) H :=
    { E with
      map_smul' := fun r x ↦ by
        change E (k r * x) = algebraMap H _ r * E x
        rw [map_mul]
        congr 1
        change E (E.symm (algebraMap H _ r)) = _
        exact E.apply_symm_apply _ }
  have hkfaithful : Module.FaithfullyFlat H (AdicCompletion I A) := by
    rw [Module.faithfullyFlat_iff]
    refine ⟨hkflat, fun {m} hm ↦ ?_⟩
    have htarget : m • (⊤ : Submodule H
        (AdicCompletion (I.map (algebraMap A H)) H)) ≠ ⊤ := by
      have hIj : I.map (algebraMap A H) ≤ Ring.jacobson H := by
        simpa only [Ideal.jacobson_bot] using
          (henselianPair_henselization A I).1
      refine smul_top_ne_top_of_surjective m
        (f := (AdicCompletion.evalOneₐ (I.map (algebraMap A H))).toLinearMap)
        (AdicCompletion.evalOneₐ_surjective _) ?_
      rw [ne_eq, smul_top_quotient_eq_top_iff,
        sup_eq_left.mpr (hIj.trans (Ring.jacobson_le_of_isMaximal m))]
      exact hm.ne_top
    intro htop
    apply htarget
    have hmap : Submodule.map lE.toLinearMap
        (m • (⊤ : Submodule H (AdicCompletion I A))) =
          m • (⊤ : Submodule H
            (AdicCompletion (I.map (algebraMap A H)) H)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    rw [← hmap, htop, Submodule.map_top, LinearEquiv.range]
  let g : Ah →ₐ[A] AdicCompletion I A := k.comp e.symm
  have hgflat : g.toRingHom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.toRingEquiv.bijective) hkflat'
  let : Algebra Ah (AdicCompletion I A) := g.toRingHom.toAlgebra
  have : Module.FaithfullyFlat Ah (AdicCompletion I A) := by
    let : Algebra Ah H := e.symm.toRingHom.toAlgebra
    let : IsScalarTower Ah H (AdicCompletion I A) := IsScalarTower.of_algebraMap_eq' rfl
    let : Module.FaithfullyFlat Ah H := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact RingHom.FaithfullyFlat.of_bijective e.symm.toRingEquiv.bijective
    let : Module.FaithfullyFlat H (AdicCompletion I A) := hkfaithful
    exact Module.FaithfullyFlat.trans Ah H (AdicCompletion I A)
  have hgfaithful : g.toRingHom.FaithfullyFlat := this
  let hnoeth : IsNoetherianRing Ah :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (A := AdicCompletion I A)
      (isNoetherian_of_linearEquiv
        (Algebra.TensorProduct.rid Ah (AdicCompletion I A) (AdicCompletion I A)).symm.toLinearEquiv)
  exact ⟨hcompletion, hnoeth, RingHom.flat_algebraMap_iff.mpr hflat,
    g, hgflat, hgfaithful⟩

end

end
