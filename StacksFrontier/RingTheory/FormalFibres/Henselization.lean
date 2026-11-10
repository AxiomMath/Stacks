module

public import Mathlib
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.FormalFibres.HenselizationShared
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Ideal.SmulTop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal fibre properties and henselization

Let `P` be a property of formal fibres which is local on the target, ascends along regular maps,
descends along faithfully flat maps, and is preserved by separable algebraic extensions of the
ground field. The henselization of a pair whose underlying ring is a `P`-ring is again a `P`-ring,
and the henselization and the strict henselization of a local `P`-ring are again `P`-rings.

## Main results

* `isPRing_henselization`: the henselization of a pair over a `P`-ring is a `P`-ring.
* `isPRing_henselization_and_strictHenselization`: the henselization and the strict
  henselization of a local `P`-ring are `P`-rings.

## References

* [The Stacks Project, Tag 0BKA](https://stacks.math.columbia.edu/tag/0BKA)
* [The Stacks Project, Tag 0C36](https://stacks.math.columbia.edu/tag/0C36)
-/

@[expose] public section

open Stacks.FormalFibres (holds_of_equiv formalFibersHaveAt_iff formalFibersHaveAt_of_ringEquiv)

/-! ### Noetherianity of the henselization of a pair -/

section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w


/-- The henselization of a pair over a Noetherian ring is Noetherian. -/
private theorem isNoetherianRing_of_henselianPair
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (Ah : Type v) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) :
    IsNoetherianRing Ah := by
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
  have : IsScalarTower A H (AdicCompletion I A) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (k.commutes a).symm
  have hkflat : Module.Flat H (AdicCompletion I A) :=
    CommAlgCat.flat_of_ind_etale_restrictScalars (ind_henselization A I)
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
  have hgfaithful : g.toRingHom.FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat]
    let : Algebra Ah (AdicCompletion I A) := g.toRingHom.toAlgebra
    let : Algebra Ah H := e.symm.toRingHom.toAlgebra
    have : IsScalarTower Ah H (AdicCompletion I A) := IsScalarTower.of_algebraMap_eq' rfl
    have : Module.FaithfullyFlat Ah H := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact RingHom.FaithfullyFlat.of_bijective e.symm.toRingEquiv.bijective
    have : Module.FaithfullyFlat H (AdicCompletion I A) := hkfaithful
    exact Module.FaithfullyFlat.trans Ah H (AdicCompletion I A)
  let : Algebra Ah (AdicCompletion I A) := g.toRingHom.toAlgebra
  have : Module.FaithfullyFlat Ah (AdicCompletion I A) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact hgfaithful
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := AdicCompletion I A)
    (isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid Ah (AdicCompletion I A) (AdicCompletion I A)).symm.toLinearEquiv)

end

/-! ### The henselization of a pair -/

section

section

universe u v w x

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

private theorem exists_sub_mem_map_of_quotientMap_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    (h : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (b : B) : ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B) := by
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨a, Ideal.Quotient.eq.mp ha.symm⟩

private theorem maximal_comap_and_map_eq_of_quotientMap_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    (h : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (m : Ideal B) [m.IsMaximal] (hI : I.map (algebraMap A B) ≤ m) :
    (m.comap (algebraMap A B)).IsMaximal ∧
      (m.comap (algebraMap A B)).map (algebraMap A B) = m := by
  let f := (Ideal.Quotient.mk m).comp (algebraMap A B)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := exists_sub_mem_map_of_quotientMap_surjective I h b
    exact ⟨a, (Ideal.Quotient.eq.mpr (hI ha)).symm⟩
  have hp : (m.comap (algebraMap A B)).IsMaximal := by
    let : Field (B ⧸ m) := Ideal.Quotient.field m
    have heq : m.comap (algebraMap A B) = RingHom.ker f := by
      ext a
      change algebraMap A B a ∈ m ↔ Ideal.Quotient.mk m (algebraMap A B a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.symm
    rw [heq]
    exact RingHom.ker_isMaximal_of_surjective f hf
  refine ⟨hp, le_antisymm (Ideal.map_comap_le) ?_⟩
  intro b hb
  obtain ⟨a, ha⟩ := exists_sub_mem_map_of_quotientMap_surjective I h b
  have ha' : a ∈ m.comap (algebraMap A B) := by
    change algebraMap A B a ∈ m
    simpa only [sub_sub_cancel] using m.sub_mem hb (hI ha)
  have hba := Ideal.map_mono (Ideal.map_le_iff_le_comap.mp hI) ha
  simpa only [sub_add_cancel] using
    (m.comap (algebraMap A B)).map (algebraMap A B) |>.add_mem hba (Ideal.mem_map_of_mem _ ha')

private theorem localized_residueFieldMap_surjective_of_quotientMap_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    (h : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (m : Ideal B) [m.IsMaximal] (hI : I.map (algebraMap A B) ≤ m) :
    Function.Surjective
      (Ideal.ResidueField.map (m.comap (algebraMap A B)) m (algebraMap A B) rfl) := by
  intro y
  obtain ⟨b, rfl⟩ := m.algebraMap_residueField_surjective y
  obtain ⟨a, ha⟩ := exists_sub_mem_map_of_quotientMap_surjective I h b
  refine ⟨algebraMap A _ a, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hz := (Ideal.algebraMap_residueField_eq_zero).mpr (hI ha)
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

private theorem isLocalization_atPrime_of_surjective_of_isArtinianRing
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsArtinianRing R] [IsReduced R]
    (h : Function.Surjective (algebraMap R K))
    (p : Ideal R) [p.IsPrime] (hp : p = RingHom.ker (algebraMap R K)) :
    IsLocalization.AtPrime K p := by
  let L := Localization.AtPrime p
  let f : L →ₐ[R] K := IsLocalization.liftAlgHom
    (M := p.primeCompl) (f := Algebra.ofId R K)
    (fun s => isUnit_iff_ne_zero.mpr fun hz => s.property (hp.ge hz))
  have : IsArtinianRing L := IsArtinianRing.localization_artinian p.primeCompl L
  let : Field L := (IsArtinianRing.isField_of_isReduced_of_isLocalRing L).toField
  have hf : Function.Bijective f := ⟨(f.toRingHom).injective, fun y => by
    obtain ⟨r, rfl⟩ := h y
    exact ⟨algebraMap R L r, f.commutes r⟩⟩
  exact IsLocalization.isLocalization_of_algEquiv p.primeCompl (AlgEquiv.ofBijective f hf)

private theorem holds_of_algEquiv
    (P : RingMapProperty.{max u v, max u v})
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S)
    (h : P.Holds.{u, u, v, 0} (algebraMap k R)) :
    P.Holds.{u, u, v, 0} (algebraMap k S) :=
  holds_of_equiv.{u, u, v, 0} P _ _ (RingEquiv.refl _) e.toRingEquiv
    (by ext a; exact e.commutes a) h

attribute [local instance] ULift.algebra'

private theorem holds_of_isLocalization
    (P : RingMapProperty.{max u v, max u v})
    (hB : ∀ (k R : Type (max u v)) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (k R S : Type u) [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (M : Submonoid R) [IsLocalization M S]
    (h : P.Holds.{u, u, v, 0} (algebraMap k R)) :
    P.Holds.{u, u, v, 0} (algebraMap k S) := by
  let k' := ULift.{max u v} k
  let R' := ULift.{max u v} R
  let S' := ULift.{max u v} S
  let M' : Submonoid R' := M.map ULift.ringEquiv.symm.toMonoidHom
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  have : IsNoetherianRing S' := isNoetherianRing_of_ringEquiv S ULift.ringEquiv.symm
  have : IsLocalization M S' :=
    IsLocalization.isLocalization_of_algEquiv M (ULift.algEquiv.symm : S ≃ₐ[R] S')
  have : IsLocalization M' S' :=
    IsLocalization.of_ringEquiv_left (M₁ := M) (ULift.ringEquiv : R' ≃+* R)
      (by ext a; exact ⟨fun ⟨x, ⟨b, hb, hbx⟩, hxa⟩ => by
          subst x; simpa using hxa ▸ hb, fun ha => ⟨ULift.up a, ⟨a, ha, rfl⟩, rfl⟩⟩)
      (fun _ => rfl)
  exact Stacks.FormalFibres.property_of_isLocalization P hB k' R' S' M' h

private theorem holds_of_isSeparable
    (P : RingMapProperty.{max u v, max u v})
    (hE : ∀ (k K R : Type (max u v))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (k K R : Type u) [Field k] [Field K] [CommRing R]
    [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
    [IsNoetherianRing R] [Algebra.IsSeparable k K]
    (h : P.Holds.{u, u, v, 0} (algebraMap k R)) :
    P.Holds.{u, u, v, 0} (algebraMap K R) := by
  let k' := ULift.{max u v} k
  let K' := ULift.{max u v} K
  let R' := ULift.{max u v} R
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  have hsep : Algebra.IsSeparable k' K' :=
    Algebra.IsSeparable.of_equiv_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm rfl
  exact hE k' K' R' hsep.isAlgebraic hsep h

private theorem tensorProductToResidueField_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [IsArtinianRing (p.Fiber B)] :
    Function.Surjective (Algebra.TensorProduct.lift
      (Ideal.ResidueField.mapₐ p q (Algebra.ofId A B) (Ideal.LiesOver.over (P := q)))
      (IsScalarTower.toAlgHom A B q.ResidueField) (fun _ _ => mul_comm _ _)) := by
  let f := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId A B) (Ideal.LiesOver.over (P := q)))
    (IsScalarTower.toAlgHom A B q.ResidueField) (fun _ _ => mul_comm _ _)
  let R : Subring q.ResidueField := f.toRingHom.range
  have hfield : IsField R := IsArtinianRing.isField_of_isDomain R
  have hinv : ∀ x : q.ResidueField, x ∈ R → x ≠ 0 → x⁻¹ ∈ R := by
    intro x hx hx0
    obtain ⟨z, hz⟩ := hfield.mul_inv_cancel (a := ⟨x, hx⟩)
      (fun hz => hx0 (congrArg Subtype.val hz))
    have hxz : x * (z : q.ResidueField) = 1 := congrArg (Subring.subtype R) hz
    have hzinv : (z : q.ResidueField) = x⁻¹ :=
      mul_right_injective₀ hx0 (hxz.trans (mul_inv_cancel₀ hx0).symm)
    exact hzinv ▸ z.property
  have hBmem : ∀ b : B, algebraMap B q.ResidueField b ∈ R := by
    intro b
    refine ⟨1 ⊗ₜ[A] b, ?_⟩
    change f (1 ⊗ₜ[A] b) = _
    exact (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans
      (by rw [map_one, one_mul]; rfl)
  have hQmem : ∀ c : B ⧸ q, algebraMap (B ⧸ q) q.ResidueField c ∈ R := by
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    simpa only [Ideal.algebraMap_quotient_residueField_mk] using hBmem b
  intro y
  change y ∈ R
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  have hbn : algebraMap (B ⧸ q) q.ResidueField b ≠ 0 := fun hz => nonZeroDivisors.ne_zero hb
    ((IsFractionRing.injective (B ⧸ q) q.ResidueField) (hz.trans (map_zero _).symm))
  rw [← hab, div_eq_mul_inv]
  exact R.mul_mem (hQmem a) (hinv _ (hQmem b) hbn)

private theorem fiber_ringEquiv_of_isLocalization
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S] (q : Ideal S) [q.IsPrime] :
    let p := q.comap (algebraMap R S)
    ∃ e : p.ResidueField ≃+* q.ResidueField,
      ∃ E : p.Fiber T ≃+* q.Fiber T,
        E.toRingHom.comp (algebraMap p.ResidueField (p.Fiber T)) =
          (algebraMap q.ResidueField (q.Fiber T)).comp e.toRingHom := by
  dsimp only
  let p := q.comap (algebraMap R S)
  let f : p.ResidueField →ₐ[R] q.ResidueField :=
    { Ideal.ResidueField.map p q (algebraMap R S) rfl with
      commutes' := fun r => by
        change Ideal.ResidueField.map p q (algebraMap R S) rfl
          (algebraMap R p.ResidueField r) = algebraMap R q.ResidueField r
        rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply] }
  let e := AlgEquiv.ofBijective f
    ((RingHom.surjectiveOnStalks_of_isLocalization M S).residueFieldMap_bijective p q rfl)
  let E := (Algebra.TensorProduct.congr e (AlgEquiv.refl : T ≃ₐ[R] T)).toRingEquiv.trans
    (IsLocalization.algebraTensorEquiv M S q.ResidueField T).symm.toRingEquiv
  exact ⟨e.toRingEquiv, E, by ext a; rfl⟩

private theorem exists_tensorProduct_baseChangeRight_algEquiv
    (A B k T : Type u) [CommRing A] [CommRing B] [CommRing k] [CommRing T]
    [Algebra A B] [Algebra A k] [Algebra A T] [Algebra B T] [IsScalarTower A B T] :
    let : Algebra B (k ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Nonempty (((k ⊗[A] B) ⊗[B] T) ≃ₐ[k] (k ⊗[A] T)) := by
  let : Algebra B (k ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let e := (Algebra.TensorProduct.comm B (k ⊗[A] B) T).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[B] T)
      (Algebra.TensorProduct.commRight A B k).symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A B B T k).toRingEquiv.trans
        (Algebra.TensorProduct.comm A T k).toRingEquiv))
  refine ⟨{ e with commutes' := fun z => ?_ }⟩
  change e ((z ⊗ₜ[A] 1) ⊗ₜ[B] 1) = z ⊗ₜ[A] 1
  change (Algebra.TensorProduct.comm A T k)
    ((Algebra.TensorProduct.cancelBaseChange A B B T k) (1 ⊗ₜ[B] (1 ⊗ₜ[A] z))) = _
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul, Algebra.TensorProduct.comm_tmul]

private theorem isNoetherianRing_fiber
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    (p : Ideal A) [p.IsPrime] : IsNoetherianRing (p.Fiber B) := by
  let : Algebra B (Localization.AtPrime p ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing (Localization.AtPrime p ⊗[A] B) :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization.AtPrime p ⊗[A] B) inferInstance
  have hsurj : Function.Surjective
      (IsScalarTower.toAlgHom A (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  let f := Algebra.TensorProduct.map (S := A)
    (IsScalarTower.toAlgHom A (Localization.AtPrime p) p.ResidueField) (AlgHom.id A B)
  exact isNoetherianRing_of_surjective _ _ f.toRingHom
    (Algebra.TensorProduct.map_surjective _ _ hsurj Function.surjective_id)

private theorem holds_fiber_of_ind_etale
    (P : RingMapProperty.{max u v, max u v})
    (hB : ∀ (k R : Type (max u v)) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hE : ∀ (k K R : Type (max u v))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (A B T : Type u) [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
    [IsNoetherianRing B] [IsNoetherianRing T]
    (hind : IsFilteredColimitEtale.{u, u, u, u} A B)
    (q : Ideal B) [q.IsPrime]
    (h : P.Holds.{u, u, v, 0}
      (algebraMap (q.under A).ResidueField ((q.under A).Fiber T))) :
    P.Holds.{u, u, v, 0} (algebraMap q.ResidueField (q.Fiber T)) := by
  let p := q.under A
  let k := p.ResidueField
  let K := q.ResidueField
  let C := p.Fiber B
  obtain ⟨r, qs, hqs, hlo, hprod, -, hall⟩ :=
    hind.exists_fiber_algEquiv_pi_residueField p
  have : ∀ i, (qs i).IsPrime := hqs
  let : ∀ i, Algebra k (qs i).ResidueField := fun i =>
    (Ideal.ResidueField.map p (qs i) (algebraMap A B) (hlo i).over).toAlgebra
  obtain ⟨⟨e⟩, hsep, halg⟩ := hprod
  have : IsArtinianRing C := e.symm.toRingEquiv.isArtinianRing
  have : IsReduced C := isReduced_of_injective e e.injective
  let : Algebra k K := (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
  have hsepK : Algebra.IsSeparable k K := by
    obtain ⟨i, hi⟩ := (hall q inferInstance).mp inferInstance
    subst q
    exact hsep i
  have : Algebra.IsAlgebraic k K := hsepK.isAlgebraic
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsScalarTower.algebraMap_apply A B K a).trans
      (Ideal.ResidueField.map_algebraMap p q (algebraMap A B) rfl a).symm
  let f : C →ₐ[A] K := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId A B) (Ideal.LiesOver.over (P := q)))
    (IsScalarTower.toAlgHom A B K) (fun _ _ => mul_comm _ _)
  let : Algebra C K := f.toRingHom.toAlgebra
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B K b = f (1 ⊗ₜ[A] b)
    symm
    exact (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans
      (by rw [map_one, one_mul]; rfl)
  have : IsScalarTower k C K := IsScalarTower.of_algebraMap_eq fun z => by
    change algebraMap k K z = f (z ⊗ₜ[A] 1)
    symm
    exact (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans
      (by rw [map_one, mul_one]; rfl)
  let n := RingHom.ker f.toRingHom
  have : n.IsPrime := RingHom.ker_isPrime f.toRingHom
  have : IsLocalization.AtPrime K n :=
    isLocalization_atPrime_of_surjective_of_isArtinianRing
      (tensorProductToResidueField_surjective p q) n rfl
  have : IsNoetherianRing (p.Fiber T) := isNoetherianRing_fiber p
  let D := C ⊗[B] T
  let : CommRing D := inferInstanceAs (CommRing (C ⊗[B] T))
  obtain ⟨eD⟩ := exists_tensorProduct_baseChangeRight_algEquiv A B k T
  have : IsNoetherianRing D := isNoetherianRing_of_ringEquiv (p.Fiber T) eD.symm.toRingEquiv
  have hD := holds_of_algEquiv.{u, v} P eD.symm h
  let F := K ⊗[C] D
  let : CommRing F := inferInstanceAs (CommRing (K ⊗[C] D))
  let : Algebra D F := Algebra.TensorProduct.rightAlgebra (R := C) (A := K) (B := D)
  have : IsLocalization (Algebra.algebraMapSubmonoid D n.primeCompl) F := by
    apply (Algebra.isLocalization_iff_isPushout n.primeCompl K).mpr
    infer_instance
  have : IsNoetherianRing F := IsLocalization.isNoetherianRing
    (Algebra.algebraMapSubmonoid D n.primeCompl) F inferInstance
  have : IsScalarTower k C F := IsScalarTower.to₁₂₄ k C K F
  have : IsScalarTower k D F :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := D) (A := F) fun z => by
      rw [IsScalarTower.algebraMap_apply k C F, IsScalarTower.algebraMap_apply C D F,
        ← IsScalarTower.algebraMap_apply k C D]
  have hF := holds_of_isLocalization.{u, v} P hB k D F
    (Algebra.algebraMapSubmonoid D n.primeCompl) hD
  let eF : F ≃ₐ[K] q.Fiber T := Algebra.TensorProduct.cancelBaseChange B C K K T
  have hK : P.Holds.{u, u, v, 0} (algebraMap K F) :=
    holds_of_isSeparable.{u, v} P hE k K F hF
  exact holds_of_algEquiv.{u, v} P eF hK

private theorem holds_fiber_iff_of_isLocalization
    (P : RingMapProperty.{max u v, max u v})
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S] (q : Ideal S) [q.IsPrime] :
    P.Holds.{u, u, v, 0} (algebraMap (q.under R).ResidueField ((q.under R).Fiber T)) ↔
      P.Holds.{u, u, v, 0} (algebraMap q.ResidueField (q.Fiber T)) := by
  obtain ⟨e, E, he⟩ := fiber_ringEquiv_of_isLocalization (T := T) M q
  constructor
  · exact holds_of_equiv.{u, u, v, 0} P _ _ e E he
  · apply holds_of_equiv.{u, u, v, 0} P _ _ e.symm E.symm
    apply RingHom.ext
    intro a
    apply E.injective
    change E (E.symm (algebraMap q.ResidueField (q.Fiber T) a)) =
      E (algebraMap (q.under R).ResidueField ((q.under R).Fiber T) (e.symm a))
    rw [E.apply_symm_apply]
    have hh := DFunLike.congr_fun he (e.symm a)
    change E (algebraMap (q.under R).ResidueField ((q.under R).Fiber T) (e.symm a)) =
      algebraMap q.ResidueField (q.Fiber T) (e (e.symm a)) at hh
    rw [e.apply_symm_apply] at hh
    exact hh.symm

private theorem holds_fiber_of_eq
    (P : RingMapProperty.{max u v, max u v})
    {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (hpq : p = q)
    (h : P.Holds.{u, u, v, 0} (algebraMap p.ResidueField (p.Fiber T))) :
    P.Holds.{u, u, v, 0} (algebraMap q.ResidueField (q.Fiber T)) := by
  subst q
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem formalFibersHaveAt_localization_maximal_of_ind_etale
    (P : RingMapProperty.{max u v, max u v})
    (hB : ∀ (k R : Type (max u v)) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hE : ∀ (k K R : Type (max u v))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (I : Ideal A)
    (hquot : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (hind : IsFilteredColimitEtale.{u, u, u, u} A B)
    (hA : IsPRingAt.{u, v, 0} P A)
    (m : Ideal B) [m.IsMaximal] (hI : I.map (algebraMap A B) ≤ m) :
    FormalFibersHaveAt.{u, v, 0} P (Localization.AtPrime m) := by
  let p := m.under A
  obtain ⟨hp, hmap⟩ := maximal_comap_and_map_eq_of_quotientMap_surjective I hquot m hI
  let R := Localization.AtPrime p
  let S := Localization.AtPrime m
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p m
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
    calc
      (maximalIdeal R).map (algebraMap R S) = p.map (algebraMap A S) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq]
      _ = m.map (algebraMap B S) := by
        rw [IsScalarTower.algebraMap_eq A B S, ← Ideal.map_map, hmap]
      _ = maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal
  have hres : Function.Bijective (ResidueField.map (algebraMap R S)) :=
    ⟨RingHom.injective _,
      localized_residueFieldMap_surjective_of_quotientMap_surjective I hquot m hI⟩
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (A := R) (B := S) (maximalIdeal R).fg_of_isNoetherianRing hmax hres
  let T := AdicCompletion (maximalIdeal S) S
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A R T := IsScalarTower.to₁₂₄ A R S T
  let eT : AdicCompletion (maximalIdeal R) R ≃ₐ[R] T := { e with commutes' := he }
  apply (formalFibersHaveAt_iff.{u, v, 0} P S).mpr
  intro q
  let r := q.asIdeal.under B
  have hrm : r ≤ m := by
    have hle := Ideal.comap_mono (f := algebraMap B S) (le_maximalIdeal q.isPrime.ne_top)
    change r ≤ (maximalIdeal S).under B at hle
    rwa [IsLocalization.AtPrime.under_maximalIdeal S m] at hle
  let l := r.under A
  have hlp : l ≤ p := Ideal.comap_mono hrm
  let qA := l.map (algebraMap A R)
  have : qA.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime p (S := R) hlp
  have hqA : qA.under A = l := Ideal.under_map_of_isLocalizationAtPrime p (S := R) hlp
  have hqAT : P.Holds.{u, u, v, 0} (algebraMap qA.ResidueField (qA.Fiber T)) :=
    holds_of_algEquiv.{u, v} P
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : qA.ResidueField ≃ₐ[qA.ResidueField] qA.ResidueField) eT)
      ((formalFibersHaveAt_iff.{u, v, 0} P R).mp (hA.2 ⟨p, inferInstance⟩) ⟨qA, inferInstance⟩)
  have hlT : P.Holds.{u, u, v, 0} (algebraMap l.ResidueField (l.Fiber T)) :=
    holds_fiber_of_eq.{u, v} P hqA
      ((holds_fiber_iff_of_isLocalization.{u, v} P (T := T) p.primeCompl qA).mpr hqAT)
  exact (holds_fiber_iff_of_isLocalization.{u, v} P (T := T) m.primeCompl q.asIdeal).mp
    (holds_fiber_of_ind_etale.{u, v} P hB hE A B T hind r hlT)

/-- A henselization of a pair over a `P`-ring is again a `P`-ring when `P` is local on the
target, ascends along regular maps, descends along faithfully flat maps, and is preserved by
separable algebraic extensions of the ground field. -/
@[stacks 0BKA, ega "IV 18.7.2" "Forward implication"]
public theorem isPRing_henselization :
    ∀ (P : RingMapProperty.{max u v, max u v}),
    (∀ (k R : Type (max u v)) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R)) →
    (∀ (R S T : Type (max u v))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) →
    (∀ (R S T : Type (max u v))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.FaithfullyFlat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
    (∀ (k K R : Type (max u v))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R)) →
    ∀ {A : Type u} {Ah : Type v} [CommRing A] [CommRing Ah] [Algebra A Ah]
      (I : Ideal A),
      HenselianPair Ah (I.map (algebraMap A Ah)) →
      (∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
        HenselianPair B J →
          ∀ f : A →+* B, I ≤ J.comap f →
            ∃! g : Ah →+* B,
              g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) →
      IsPRingAt.{u, v, v} P A →
      IsPRingAt.{v, u, u} P Ah := by
  intro P hB hC hD hE A Ah _ _ _ I hh hι hA
  have : IsNoetherianRing A := hA.1
  have hAh : IsNoetherianRing Ah := isNoetherianRing_of_henselianPair A I Ah hh hι
  let H := (henselization A I : Type u)
  obtain ⟨eH⟩ := nonempty_algEquiv_henselization A I Ah hh hι
  have : IsNoetherianRing H := isNoetherianRing_of_ringEquiv Ah eH.symm.toRingEquiv
  have : Module.Flat A H := CommAlgCat.flat_of_ind_etale (ind_henselization A I)
  have hH : IsPRingAt.{u, v, 0} P H :=
    (isPRing_iff_formalFibersHave_localization_maximal.{u, v, 0} P hC hD).mpr fun m _ =>
      formalFibersHaveAt_localization_maximal_of_ind_etale.{u, v} P hB hE I
        (bijective_quotientMap_henselization A I).surjective
        (Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind A H (ind_henselization A I))
        hA m ((henselianPair_henselization A I).1.trans (by
          simpa only [Ideal.jacobson_bot] using Ring.jacobson_le_of_isMaximal m))
  refine ⟨hAh, fun q => ?_⟩
  let p : PrimeSpectrum H := PrimeSpectrum.comap eH.toRingHom q
  exact formalFibersHaveAt_of_ringEquiv.{u, v, 0, 0} P
    (Localization.localRingEquiv p.asIdeal q.asIdeal eH.toRingEquiv rfl) (hH.2 p)

end

end

/-! ### The henselization and the strict henselization of a local ring -/

section

section

open IsLocalRing

universe u v w x

open scoped TensorProduct

@[sga "4 VIII 4.4"]
private lemma isNoetherianRing_strictHenselization
    (R : Type u) (L : Type v) (H : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field L] [Algebra (ResidueField R) L] [IsSepClosure (ResidueField R) L]
    [CommRing H] [IsLocalRing H] [Algebra R H] [IsHenselization R L H] :
    IsNoetherianRing H := by
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H' ≃+* H := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsLocalRing H' := eH.symm.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R eR.symm
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') L :=
    ((algebraMap (ResidueField R) L).comp (ResidueField.mapEquiv eR).toRingHom).toAlgebra
  let : IsHenselization R' L H' := Stacks.Henselization.Shared.isHenselization_ulift R L H
  have : IsSepClosure (ResidueField R') L :=
    { sep_closed := IsSepClosure.sep_closed (ResidueField R)
      separable := Algebra.IsSeparable.of_equiv_equiv
        (ResidueField.mapEquiv eR).symm (RingEquiv.refl L) (by
          ext a
          change algebraMap (ResidueField R) L
            ((ResidueField.mapEquiv eR) ((ResidueField.mapEquiv eR).symm a)) = _
          rw [RingEquiv.apply_symm_apply]
          rfl) }
  obtain ⟨Rh, _, _, _, hh⟩ := IsLocalRing.exists_isHenselization_residueField R'
  have : IsNoetherianRing H' :=
    (isNoetherianRing_iff_henselizations R' Rh H' L).2.mp inferInstance
  exact isNoetherianRing_of_ringEquiv H' eH

private lemma formalFibersHaveAt_localization_maximal_iff
    (P : RingMapProperty.{max u v, max u v w})
    (R : Type u) [CommRing R] [IsLocalRing R] :
    FormalFibersHaveAt.{u, v, w} P
      (Localization.AtPrime (maximalIdeal R)) ↔
        FormalFibersHaveAt.{u, v, w} P R := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl (fun x => by simpa using! fun a => a)
  exact ⟨formalFibersHaveAt_of_ringEquiv.{u, u, v, w} P e.symm.toRingEquiv,
    formalFibersHaveAt_of_ringEquiv.{u, u, v, w} P e.toRingEquiv⟩

private lemma isRegularRingHom_of_isFormallySmooth
    {R : Type v} {S : Type w}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S]
    (f : R →+* S) [IsLocalHom f]
    (h : letI : TopologicalSpace R := (maximalIdeal R).adicTopology
         letI : IsTopologicalRing R := (maximalIdeal R).nonarchimedean.toIsTopologicalRing
         letI : IsLinearTopology R R := (maximalIdeal R).isLinearTopology
         letI : TopologicalSpace S := (maximalIdeal S).adicTopology
         letI : IsTopologicalRing S := (maximalIdeal S).nonarchimedean.toIsTopologicalRing
         letI : IsLinearTopology S S := (maximalIdeal S).isLinearTopology
         IsFormallySmooth.{max v w} f) : IsRegularRingHom f :=
  ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae f).out 4 1).mp
    (Stacks.Henselization.Shared.formallySmoothNAdic_of_isFormallySmooth f (maximalIdeal R)
      (maximalIdeal S) h)

private lemma isLocalHom_completionMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (g : A →+* B) [IsLocalHom g]
    (f : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    (hf : f.comp (algebraMap A _) = (algebraMap B _).comp g) : IsLocalHom f := by
  apply ((IsLocalRing.local_hom_TFAE f).out 3 1).mp
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hf, ← Ideal.map_map]
  exact (Ideal.map_mono (map_maximalIdeal_le g)).trans
    (AdicCompletion.maximalIdeal_eq_map (R := B)).ge

/-- A henselization of `R` at the residue field maps locally to any henselian local `R`-algebra
with local structure map. -/
private lemma exists_algebra_isLocalHom_henselization
    (R Rh H : Type u) [CommRing R] [IsLocalRing R] [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing H] [HenselianLocalRing H] [Algebra R H] [IsLocalHom (algebraMap R H)]
    [IsHenselization R (ResidueField R) Rh] :
    ∃ (_ : Algebra Rh H) (_ : IsScalarTower R Rh H), IsLocalHom (algebraMap Rh H) := by
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  let g : Rh →ₐ[R] H := HenselianLocalRing.indEtaleAlgHom
    (R := R) (Rh := Rh) (Sh := H)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := Rh)).2
  have hg : IsLocalHom g := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (R := R) (Rh := Rh) (Sh := H)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := Rh)).2
  let : Algebra Rh H := g.toRingHom.toAlgebra
  exact ⟨this, IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm,
    ⟨fun a ha => IsLocalHom.map_nonunit (f := g) a ha⟩⟩

private lemma exists_regular_completionMap_strictHenselization
    (R H : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [IsSepClosure (ResidueField R) L] [IsHenselization R L H] :
    ∃ f : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal H) H,
      f.comp (algebraMap R _) = (algebraMap H _).comp (algebraMap R H) ∧
      IsRegularRingHom f := by
  have : IsNoetherianRing H := isNoetherianRing_strictHenselization R L H
  have : IsLocalHom (algebraMap R H) := IsHenselization.isLocalHom (L := L)
  have : HenselianLocalRing H := IsHenselization.henselian R L
  obtain ⟨Rh, _, _, _, hh⟩ := IsLocalRing.exists_isHenselization_residueField R
  obtain ⟨_, _, _⟩ := exists_algebra_isLocalHom_henselization R Rh H
  obtain ⟨hRlocal, hRhlocal, hHlocal, hRhNoeth, hHNoeth, hRhComplete, hHComplete,
      e, he, hflatRh, hflatH, ⟨f, hf, hSmooth⟩, hrest⟩ :=
    (isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, u}
      R Rh H L).2 inferInstance
  have hf' : f.comp (algebraMap R _) = (algebraMap H _).comp (algebraMap R H) := RingHom.ext hf
  have : IsLocalHom f := isLocalHom_completionMap (algebraMap R H) f hf'
  exact ⟨f, hf', isRegularRingHom_of_isFormallySmooth f hSmooth⟩

private lemma isLocalization_of_surjectiveOnStalks
    {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]
    [IsArtinianRing A] [IsReduced A]
    (h : (algebraMap A K).SurjectiveOnStalks) :
    IsLocalization ((⊥ : Ideal K).comap (algebraMap A K)).primeCompl K := by
  let p := (⊥ : Ideal K).comap (algebraMap A K)
  let Ap := Localization.AtPrime p
  let Kp := Localization.AtPrime (⊥ : Ideal K)
  let : Field Ap := (IsArtinianRing.isField_of_isReduced_of_isLocalRing (R := Ap)).toField
  let f : Ap →+* Kp := Localization.localRingHom p (⊥ : Ideal K) (algebraMap A K) rfl
  have hf : Function.Bijective f := ⟨f.injective, h.localRingHom_surjective p ⊥ rfl⟩
  let eK : K ≃ₐ[K] Kp := IsLocalization.atUnits K (⊥ : Ideal K).primeCompl
    (fun x hx => (isUnit_iff_ne_zero.mpr hx : IsUnit x))
  let E : Ap ≃ₐ[A] K :=
    { (RingEquiv.ofBijective f hf).trans eK.symm.toRingEquiv with
      commutes' := fun a => by
        apply eK.injective
        change eK (eK.symm (f (algebraMap A Ap a))) = eK (algebraMap A K a)
        rw [eK.apply_symm_apply]
        change f (algebraMap A Ap a) = algebraMap K Kp (algebraMap A K a)
        exact Localization.localRingHom_to_map p ⊥ (algebraMap A K) rfl a }
  exact IsLocalization.isLocalization_of_algEquiv p.primeCompl E

private lemma exists_fiber_localization
    (R H T : Type u) [CommRing R] [CommRing H] [CommRing T]
    [Algebra R H] [Algebra H T] [Algebra R T] [IsScalarTower R H T]
    (q : Ideal H) [q.IsPrime]
    (p : Ideal R) [p.IsPrime] (hp : p = q.comap (algebraMap R H))
    [IsArtinianRing (p.Fiber H)] [IsReduced (p.Fiber H)] :
    letI : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (algebraMap R H) hp).toAlgebra
    letI : Algebra p.ResidueField (q.Fiber T) := Algebra.TensorProduct.leftAlgebra
    ∃ (_ : Algebra (p.Fiber T) (q.Fiber T))
      (_ : IsScalarTower p.ResidueField (p.Fiber T) (q.Fiber T))
      (M : Submonoid (p.Fiber T)), IsLocalization M (q.Fiber T) := by
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R H) hp).toAlgebra
  let : Algebra p.ResidueField (q.Fiber T) := Algebra.TensorProduct.leftAlgebra
  let F := p.Fiber H
  let : Algebra H F := Algebra.TensorProduct.rightAlgebra
  let K := q.ResidueField
  let φ₀ : F →ₐ[R] K := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId R H) hp)
    (IsScalarTower.toAlgHom R H K) (fun _ _ => Commute.all _ _)
  let φ : F →ₐ[H] K :=
    { φ₀.toRingHom with
      commutes' := by
        intro h
        change φ₀ ((1 : p.ResidueField) ⊗ₜ[R] h) = algebraMap H K h
        change (Ideal.ResidueField.mapₐ p q (Algebra.ofId R H) hp) 1 * algebraMap H K h = _
        rw [map_one, one_mul] }
  let : Algebra F K := φ.toRingHom.toAlgebra
  have : IsScalarTower H F K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hφ : φ.toRingHom.SurjectiveOnStalks := by
    apply RingHom.SurjectiveOnStalks.of_comp (f := algebraMap H F)
    change (φ.toRingHom.comp (algebraMap H F)).SurjectiveOnStalks
    rw [show φ.toRingHom.comp (algebraMap H F) = algebraMap H K from RingHom.ext φ.commutes]
    exact q.surjectiveOnStalks_residueField
  let M := ((⊥ : Ideal K).comap (algebraMap F K)).primeCompl
  have : IsLocalization M K := isLocalization_of_surjectiveOnStalks hφ
  let D := F ⊗[H] T
  let : Algebra F D := Algebra.TensorProduct.leftAlgebra
  let G := q.Fiber T
  let δ : D →ₐ[H] G := Algebra.TensorProduct.map φ (AlgHom.id H T)
  let : Algebra D G := δ.toRingHom.toAlgebra
  let : Algebra F G := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower F D G := IsScalarTower.of_algebraMap_eq' (R := F) (S := D) (A := G) (by
    apply RingHom.ext
    intro a
    change (φ a) ⊗ₜ[H] (1 : T) = δ (a ⊗ₜ[H] (1 : T))
    rfl)
  have hloc :=
    IsLocalization.tensorProduct_tensorProduct H T M K (by
      apply RingHom.ext
      intro t
      change (φ 1) ⊗ₜ[H] t = 1 ⊗ₜ[H] t
      rw [map_one])
  let e : D ≃+* p.Fiber T :=
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.commRight R H p.ResidueField).symm
      (AlgEquiv.refl : T ≃ₐ[H] T)).toRingEquiv.trans
    ((Algebra.TensorProduct.comm H (H ⊗[R] p.ResidueField) T).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange R H H T p.ResidueField).toRingEquiv.trans
      (Algebra.TensorProduct.comm R T p.ResidueField).toRingEquiv))
  let : Algebra (p.Fiber T) G := (δ.toRingHom.comp e.symm.toRingHom).toAlgebra
  refine ⟨inferInstance, ?_, (Algebra.algebraMapSubmonoid D M).map e.toMonoidHom, ?_⟩
  · apply IsScalarTower.of_algebraMap_eq' (R := p.ResidueField) (S := p.Fiber T) (A := G)
    apply RingHom.ext
    intro a
    change algebraMap q.ResidueField G (algebraMap p.ResidueField q.ResidueField a) =
      δ (e.symm (a ⊗ₜ[R] (1 : T)))
    change (algebraMap p.ResidueField q.ResidueField a) ⊗ₜ[H] (1 : T) =
      (φ ((a ⊗ₜ[R] (1 : H)))) ⊗ₜ[H] (1 : T)
    congr 1
    change _ = (Ideal.ResidueField.map p q (algebraMap R H) hp a) * algebraMap H K 1
    rw [map_one, mul_one]
    rfl
  · exact IsLocalization.of_surjective (R := D) (R' := p.Fiber T) (S' := G)
      (Algebra.algebraMapSubmonoid D M) G e.toRingHom e.surjective (RingHom.id G)
      Function.surjective_id
      (by
        apply RingHom.ext
        intro d
        change δ d = δ (e.symm (e d))
        rw [e.symm_apply_apply])
      (by
        rw [(RingHom.injective_iff_ker_eq_bot (RingHom.id G)).mp Function.injective_id]
        exact bot_le)

section

attribute [local instance] ULift.algebra'

private lemma flat_ulift
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    Module.Flat (ULift.{v} R) (ULift.{v} S) :=
  RingHom.flat_algebraMap_iff.mp <|
    (RingHom.Flat.of_bijective (f := (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom)
      ULift.ringEquiv.bijective).comp
    ((RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).comp
      (RingHom.Flat.of_bijective (f := (ULift.ringEquiv : ULift.{v} S ≃+* S).symm.toRingHom)
        ULift.ringEquiv.symm.bijective))

end

/-- A ring-map property of the fibre over `q.comap e` transports along compatible isomorphisms. -/
private lemma holds_fiber_of_ringEquiv
    (P : RingMapProperty.{max u v w, max u v w x})
    {R S : Type u} {R' S' : Type v} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] (e : R ≃+* R') (f : S ≃+* S')
    (hf : ∀ r, f (algebraMap R S r) = algebraMap R' S' (e r)) (q : Ideal R') [q.IsPrime]
    (h : P.Holds.{u, u, max v w, x}
      (algebraMap (q.comap e.toRingHom).ResidueField ((q.comap e.toRingHom).Fiber S))) :
    P.Holds.{v, v, max u w, x} (algebraMap q.ResidueField (q.Fiber S')) := by
  obtain ⟨E, hE⟩ := Stacks.FormalFibres.exists_fiber_ringEquiv e f hf q
  exact holds_of_equiv.{u, v, w, x} P _ _ (Ideal.residueFieldRingEquiv _ q e rfl) E
    (RingHom.ext hE) h

private lemma fibersHave_of_regularAscent
    (P : RingMapProperty.{max u v, max u v})
    (hC : ∀ (R S T : Type (max u v))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)))
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
    [Module.Flat R S] [Module.Flat S T]
    (hRS : ∀ p : PrimeSpectrum R,
      P.Holds.{u, u, v, 0} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))
    (hST : ∀ q : PrimeSpectrum S,
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) :
    ∀ p : PrimeSpectrum R,
      P.Holds.{u, u, v, 0} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)) := by
  let R' := ULift.{max u v} R
  let S' := ULift.{max u v} S
  let T' := ULift.{max u v} T
  let : Algebra R' S' := ULift.algebra' R S'
  let : Algebra S' T' := ULift.algebra' S T'
  let : Algebra R' T' := ULift.algebra' R T'
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  have : IsNoetherianRing S' := isNoetherianRing_of_ringEquiv S ULift.ringEquiv.symm
  have : IsNoetherianRing T' := isNoetherianRing_of_ringEquiv T ULift.ringEquiv.symm
  have : Module.Flat R' S' := flat_ulift R S
  have : Module.Flat S' T' := flat_ulift S T
  have : IsScalarTower R' S' T' := IsScalarTower.of_algebraMap_eq' (R := R') (S := S') (A := T') (by
    apply RingHom.ext
    intro a
    change ULift.up (algebraMap R T a.down) =
      ULift.up (algebraMap S T (algebraMap R S a.down))
    rw [← IsScalarTower.algebraMap_apply R S T])
  have hRS' : ∀ p : PrimeSpectrum R',
      P.Holds.{max u v, max u v, 0, 0}
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S')) := by
    intro p
    refine holds_fiber_of_ringEquiv.{u, max u v, v, 0} P (R := R) (S := S) (R' := R') (S' := S')
      ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ => rfl) p.asIdeal ?_
    let p₀ : PrimeSpectrum R := ⟨p.asIdeal.comap ULift.ringEquiv.symm.toRingHom, inferInstance⟩
    exact hRS p₀
  have hST' : ∀ q : PrimeSpectrum S',
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T') := by
    intro q
    let q₀ : PrimeSpectrum S := ⟨q.asIdeal.comap ULift.ringEquiv.symm.toRingHom, inferInstance⟩
    have hg₀ : RingMapProperty.geometricallyRegular.Holds.{u, u, v, 0}
        (algebraMap q₀.asIdeal.ResidueField (q₀.asIdeal.Fiber T)) :=
      (RingMapProperty.geometricallyRegular_holds_iff _).mpr
        (by
          rw [toAlgebra_algebraMap]
          exact hST q₀)
    have hg := holds_fiber_of_ringEquiv.{u, max u v, v, 0} RingMapProperty.geometricallyRegular
      (R := S) (S := T) (R' := S') (S' := T') ULift.ringEquiv.symm ULift.ringEquiv.symm
      (fun _ => rfl) q.asIdeal hg₀
    have hg' := (RingMapProperty.geometricallyRegular_holds_iff _).mp hg
    rwa [toAlgebra_algebraMap] at hg'
  have hRT' := hC R' S' T' hRS' hST'
  intro p
  let p' : PrimeSpectrum R' := ⟨p.asIdeal.comap ULift.ringEquiv.toRingHom, inferInstance⟩
  exact holds_fiber_of_ringEquiv.{max u v, u, v, 0} P (R := R') (S := T') (R' := R) (S' := T)
    ULift.ringEquiv ULift.ringEquiv (fun _ => rfl) p.asIdeal (hRT' p')

private lemma isSeparable_residueField_of_eq
    (R H : Type*) [CommRing R] [CommRing H] [Algebra R H]
    (p : Ideal R) [p.IsPrime] (q q' : Ideal H) [q.IsPrime] [q'.IsPrime]
    (hp : p = q.comap (algebraMap R H)) (hp' : p = q'.comap (algebraMap R H))
    (h : q = q') :
    @Algebra.IsSeparable p.ResidueField q.ResidueField _ _
        (Ideal.ResidueField.map p q (algebraMap R H) hp).toAlgebra →
      @Algebra.IsSeparable p.ResidueField q'.ResidueField _ _
        (Ideal.ResidueField.map p q' (algebraMap R H) hp').toAlgebra := by
  subst q'
  exact id

private lemma fibersHave_of_fiber_decomposition
    (P : RingMapProperty.{max u v, max u v})
    (hB : ∀ (k A : Type (max u v)) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k A))
    (hE : ∀ (k K A : Type (max u v)) [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
      [IsNoetherianRing A], Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k A) → P (algebraMap K A))
    (R H T : Type u) [CommRing R] [CommRing H] [CommRing T]
    [Algebra R H] [Algebra H T] [Algebra R T] [IsScalarTower R H T]
    [IsNoetherianRing T]
    (hdec : ∀ (p : Ideal R) [p.IsPrime],
      ∃ (n : ℕ) (q : Fin n → Ideal H) (hq : ∀ i, (q i).IsPrime)
        (hlo : ∀ i, (q i).LiesOver p),
        (letI : ∀ i, (q i).IsPrime := hq
         letI : ∀ i, Algebra p.ResidueField (q i).ResidueField := fun i =>
           (Ideal.ResidueField.map p (q i) (algebraMap R H) (hlo i).over).toAlgebra
         Nonempty (p.Fiber H ≃ₐ[p.ResidueField] (∀ i, (q i).ResidueField)) ∧
           (∀ i, Algebra.IsSeparable p.ResidueField (q i).ResidueField) ∧
           (∀ i, Algebra.IsAlgebraic p.ResidueField (q i).ResidueField)) ∧
        Function.Injective q ∧
        (∀ q' : Ideal H, ∀ _ : q'.IsPrime, q'.LiesOver p ↔ ∃ i, q i = q'))
    (hRT : ∀ p : PrimeSpectrum R,
      P.Holds.{u, u, v, 0} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) :
    ∀ q : PrimeSpectrum H,
      P.Holds.{u, u, v, 0} (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber T)) := by
  intro q
  let p := q.asIdeal.comap (algebraMap R H)
  obtain ⟨n, qs, hqs, hlo, hfields, -, hall⟩ := hdec p
  have : ∀ i, (qs i).IsPrime := hqs
  let : ∀ i, Algebra p.ResidueField (qs i).ResidueField := fun i =>
    (Ideal.ResidueField.map p (qs i) (algebraMap R H) (hlo i).over).toAlgebra
  obtain ⟨⟨e⟩, hsep, -⟩ := hfields
  have : IsArtinianRing (p.Fiber H) := e.symm.toRingEquiv.isArtinianRing
  have : IsReduced (p.Fiber H) := isReduced_of_injective e e.injective
  let : Algebra p.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p q.asIdeal (algebraMap R H) rfl).toAlgebra
  let : Algebra p.ResidueField (q.asIdeal.Fiber T) := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower p.ResidueField q.asIdeal.ResidueField (q.asIdeal.Fiber T) := inferInstance
  have : Algebra.IsSeparable p.ResidueField q.asIdeal.ResidueField := by
    obtain ⟨i, hi⟩ := (hall q.asIdeal q.isPrime).mp ⟨rfl⟩
    exact isSeparable_residueField_of_eq R H p (qs i) q.asIdeal (hlo i).over rfl hi (hsep i)
  have : IsNoetherianRing (p.Fiber T) := isNoetherianRing_fiber p
  have : IsNoetherianRing (q.asIdeal.Fiber T) := isNoetherianRing_fiber q.asIdeal
  obtain ⟨_, _, M, _⟩ := exists_fiber_localization R H T q.asIdeal p rfl
  exact holds_of_isSeparable P hE p.ResidueField q.asIdeal.ResidueField (q.asIdeal.Fiber T)
    (holds_of_isLocalization P hB p.ResidueField (p.Fiber T) (q.asIdeal.Fiber T) M
      (hRT ⟨p, inferInstance⟩))

private lemma formalFibersHave_henselizations
    (P : RingMapProperty.{max u w, max u w})
    (hB : ∀ (k R : Type (max u w))
      [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hC : ∀ (R S T : Type (max u w))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)))
    (hE : ∀ (k K R : Type (max u w))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (R Rh H : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [IsSepClosure (ResidueField R) L]
    [IsHenselization R (ResidueField R) Rh] [IsHenselization R L H]
    (hR : FormalFibersHaveAt.{u, w, 0} P R) :
    FormalFibersHaveAt.{u, w, 0} P Rh ∧
      FormalFibersHaveAt.{u, w, 0} P H := by
  have : IsNoetherianRing Rh :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := R) (B := Rh) (ResidueField R)
  have : IsNoetherianRing H := isNoetherianRing_strictHenselization R L H
  have : IsLocalHom (algebraMap R H) := IsHenselization.isLocalHom (L := L)
  have : HenselianLocalRing H := IsHenselization.henselian R L
  obtain ⟨_, _, _⟩ := exists_algebra_isLocalHom_henselization R Rh H
  obtain ⟨hRlocal, hRhlocal, hHlocal, hRhNoeth, hHNoeth, hRhComplete, hHComplete,
      e, he, hflatRh, hflatH, ⟨f, hf, hSmooth⟩, -⟩ :=
    (isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, u}
      R Rh H L).2 inferInstance
  let A := AdicCompletion (maximalIdeal R) R
  let B := AdicCompletion (maximalIdeal Rh) Rh
  let C := AdicCompletion (maximalIdeal H) H
  have : IsScalarTower R Rh B := inferInstance
  have : IsScalarTower R H C := inferInstance
  let E : A ≃ₐ[R] B := { e with commutes' := he }
  have hRB : ∀ p : PrimeSpectrum R,
      P.Holds.{u, u, w, 0} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := fun p =>
    holds_of_equiv.{u, u, w, 0} P _ _ (RingEquiv.refl _)
      (Algebra.TensorProduct.congr (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] _) E).toRingEquiv
      (by
        apply RingHom.ext
        intro a
        change a ⊗ₜ[R] E 1 = a ⊗ₜ[R] (1 : B)
        rw [map_one]) ((formalFibersHaveAt_iff P R).mp hR p)
  have hf' : f.comp (algebraMap R A) = (algebraMap H C).comp (algebraMap R H) := RingHom.ext hf
  have : IsLocalHom f := isLocalHom_completionMap (algebraMap R H) f hf'
  have hreg := isRegularRingHom_of_isFormallySmooth f hSmooth
  let : Algebra A C := f.toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' hf'.symm
  have hreg' := (isRegularRingHom_iff_of_eq_algebraMap f rfl).mp hreg
  have : Module.Flat A C := RingHom.flat_algebraMap_iff.mp hreg'.1
  have hRC := fibersHave_of_regularAscent P hC R A C
    ((formalFibersHaveAt_iff P R).mp hR) (fun q => (hreg'.2 q.asIdeal).2)
  exact ⟨(formalFibersHaveAt_iff P Rh).mpr <| fibersHave_of_fiber_decomposition P hB hE R Rh B
      (fun p _ => (henselization_fibres_equiv_pi_residueFields R Rh H L p).1) hRB,
    (formalFibersHaveAt_iff P H).mpr <| fibersHave_of_fiber_decomposition P hB hE R H C
      (fun p _ => (henselization_fibres_equiv_pi_residueFields R Rh H L p).2) hRC⟩

private lemma formalFibersHave_henselization
    (P : RingMapProperty.{max u v w, max u v w})
    (hB : ∀ (k R : Type (max u v w))
      [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hC : ∀ (R S T : Type (max u v w))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)))
    (hE : ∀ (k K R : Type (max u v w))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (R : Type u) (H : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsHenselization R (ResidueField R) H]
    (hR : FormalFibersHaveAt.{u, max v w, 0} P R) :
    FormalFibersHaveAt.{w, max u v, 0} P H := by
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H' ≃+* H := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsLocalRing H' := eH.symm.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R eR.symm
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') (ResidueField R) :=
    (ResidueField.mapEquiv eR).toRingHom.toAlgebra
  let : IsHenselization R' (ResidueField R) H' :=
    Stacks.Henselization.Shared.isHenselization_ulift R (ResidueField R) H
  let : IsHenselization R' (ResidueField R') H' :=
    Stacks.Henselization.Shared.isHenselization_of_residueFieldEquiv R' (ResidueField R)
      (ResidueField R') H' (ResidueField.mapEquiv eR) (fun r => rfl)
  have : IsLocalHom (algebraMap R' H') := IsHenselization.isLocalHom (L := ResidueField R')
  obtain ⟨Hsh, _, _, _, _, _, _, hh, -, hi, -, hr⟩ :=
    exists_strictHenselization R' H'
      (IsHenselization.ind_etale_of_universe_le.{max u w, max u w, 0}
        (R := R') (ResidueField R') (Rh := H'))
      (IsHenselization.residueField_map_bijective (R := R') (Rh := H')).2
      (SeparableClosure (ResidueField R'))
  let : IsHenselization R' (SeparableClosure (ResidueField R')) Hsh :=
    IsHenselization.of_ind_etale.{max u w, max u w, 0} hh hi hr
  have hR' : FormalFibersHaveAt.{max u w, v, 0} P R' :=
    formalFibersHaveAt_of_ringEquiv.{u, max u w, v, 0} P eR.symm hR
  have hH' := (formalFibersHave_henselizations P hB hC hE R' H' Hsh
    (SeparableClosure (ResidueField R')) hR').1
  exact formalFibersHaveAt_of_ringEquiv.{max u w, w, v, 0} P eH hH'

private lemma formalFibersHave_strictHenselization
    (P : RingMapProperty.{max u v w x, max u v w x})
    (hB : ∀ (k R : Type (max u v w x))
      [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hC : ∀ (R S T : Type (max u v w x))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)))
    (hE : ∀ (k K R : Type (max u v w x))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (R : Type u) (L : Type v) (H : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field L] [Algebra (ResidueField R) L] [IsSepClosure (ResidueField R) L]
    [CommRing H] [IsLocalRing H] [Algebra R H] [IsHenselization R L H]
    (hR : FormalFibersHaveAt.{u, max v w x, 0} P R) :
    FormalFibersHaveAt.{w, max u v x, 0} P H := by
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H' ≃+* H := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsLocalRing H' := eH.symm.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R eR.symm
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') L :=
    ((algebraMap (ResidueField R) L).comp (ResidueField.mapEquiv eR).toRingHom).toAlgebra
  let : IsHenselization R' L H' := Stacks.Henselization.Shared.isHenselization_ulift R L H
  have : IsSepClosure (ResidueField R') L :=
    { sep_closed := IsSepClosure.sep_closed (ResidueField R)
      separable := Algebra.IsSeparable.of_equiv_equiv
        (ResidueField.mapEquiv eR).symm (RingEquiv.refl L) (by
          ext a
          change algebraMap (ResidueField R) L
            ((ResidueField.mapEquiv eR) ((ResidueField.mapEquiv eR).symm a)) = _
          rw [RingEquiv.apply_symm_apply]
          rfl) }
  obtain ⟨Rh, _, _, _, hh⟩ := IsLocalRing.exists_isHenselization_residueField R'
  have hR' : FormalFibersHaveAt.{max u w, max v x, 0} P R' :=
    formalFibersHaveAt_of_ringEquiv.{u, max u w, max v x, 0} P eR.symm hR
  have hH' := (formalFibersHave_henselizations P hB hC hE R' Rh H' L hR').2
  exact formalFibersHaveAt_of_ringEquiv.{max u w, w, max v x, 0} P eH hH'

/-- The henselization and strict henselization of a local `P`-ring are `P`-rings when `P` is
local on the target, ascends along regular maps, descends along faithfully flat maps, and is
preserved by separable algebraic extensions of the ground field. -/
@[stacks 0C36, ega "IV 18.7.2" "partial"]
public theorem isPRing_henselization_and_strictHenselization
    (P : RingMapProperty.{max u (max v (max w x)), max u (max v (max w x))})
    (hB : ∀ (k R : Type (max u (max v (max w x))))
      [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ q : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k R))
    (hC : ∀ (R S T : Type (max u (max v (max w x))))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.Flat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) →
      (∀ q : PrimeSpectrum S,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)))
    (hD : ∀ (R S T : Type (max u (max v (max w x))))
      [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.FaithfullyFlat S T],
      (∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) →
      ∀ p : PrimeSpectrum R,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))
    (hE : ∀ (k K R : Type (max u (max v (max w x))))
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R]
      [IsNoetherianRing R],
      Algebra.IsAlgebraic k K → Algebra.IsSeparable k K →
        P (algebraMap k R) → P (algebraMap K R))
    (R : Type u) (Rh : Type w) (Rsh : Type x)
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField R) ksep]
    [IsSepClosure (ResidueField R) ksep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R ksep Rsh]
    (hR : IsPRingAt.{u, max v (max w x), max v (max w x)} P R) :
    IsPRingAt.{w, max u (max v x), max u (max v x)} P Rh ∧
      IsPRingAt.{x, max u (max v w), max u (max v w)} P Rsh := by
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing Rh :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := R) (B := Rh) (ResidueField R)
  have : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R ksep Rsh
  have hR₀ : FormalFibersHaveAt.{u, max v (max w x), max v (max w x)} P R :=
    (formalFibersHaveAt_localization_maximal_iff P R).mp
      (hR.2 ⟨maximalIdeal R, inferInstance⟩)
  suffices h :
      FormalFibersHaveAt.{w, max u (max v x), max u (max v x)} P Rh ∧
      FormalFibersHaveAt.{x, max u (max v w), max u (max v w)} P Rsh by
    refine ⟨(isPRing_iff_formalFibersHave_localization_maximal P hC hD).mpr fun m hm => ?_,
      (isPRing_iff_formalFibersHave_localization_maximal P hC hD).mpr fun m hm => ?_⟩
    · obtain rfl := eq_maximalIdeal hm
      exact (formalFibersHaveAt_localization_maximal_iff P Rh).mpr h.1
    · obtain rfl := eq_maximalIdeal hm
      exact (formalFibersHaveAt_localization_maximal_iff P Rsh).mpr h.2
  exact ⟨formalFibersHave_henselization.{u, max v x, w} P hB hC hE R Rh hR₀,
    formalFibersHave_strictHenselization.{u, v, x, w} P hB hC hE R ksep Rsh hR₀⟩

end

end

end
