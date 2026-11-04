module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Tor.Vanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.Construction
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.Construction

/-!
# Divided power envelopes: existence, factorization and quotients

This file transports the same-universe construction of divided power envelopes along universe
lifts to prove that the envelope exists (`Crystalline.dividedPowerEnvelope`), shows that the
quotient map `B → B ⧸ J` factors through the envelope with the divided power ideal as kernel
(`Crystalline.dividedPowerEnvelope_factorization`), and describes the envelope of a surjection
`B′ → B` as a quotient by `Crystalline.dividedPowerKernelIdeal`
(`Crystalline.dividedPowerEnvelope_quotient`).
-/

@[expose] public section

namespace Crystalline

section Envelope

universe u v w x

open CategoryTheory CategoryTheory.Limits

/-- Lift the base only inside the same-universe construction. -/
private noncomputable abbrev liftedBase (A : DividedPowerRing.{u}) :
    DividedPowerRing.{max u v} :=
  .of (ULift.{v} A) (A.ideal.map ULift.ringEquiv.symm.toRingHom)
    (DividedPowers.ofRingEquiv rfl A.dividedPowers)

private noncomputable def baseUp (A : DividedPowerRing.{u}) :
    DividedPowers.DPMorphism A.dividedPowers (liftedBase.{u, v} A).dividedPowers := by
  dsimp only [liftedBase]
  exact { toRingHom := (ULift.ringEquiv : ULift.{v} A ≃+* A).symm.toRingHom
          ideal_comp := le_rfl
          dpow_comp := fun _ _ => rfl }

private noncomputable def baseDown (A : DividedPowerRing.{u}) :
    DividedPowers.DPMorphism (liftedBase.{u, v} A).dividedPowers A.dividedPowers where
  toRingHom := ULift.ringEquiv.toRingHom
  ideal_comp := by
    change (A.ideal.map ULift.ringEquiv.symm.toRingHom).map
      ULift.ringEquiv.toRingHom ≤ A.ideal
    simp only [Ideal.map_map, RingEquiv.toRingHom_eq_coe,
      RingEquiv.comp_symm, Ideal.map_id, le_refl]
  dpow_comp _ _ := rfl

/-- The lifted ring map still carries the base ideal into the lifted ideal. -/
private theorem liftedMap_ideal (A : DividedPowerRing.{u}) {B : Type v} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) :
    (liftedBase.{u, v} A).ideal.map
        ((ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom.comp
          (f.comp (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom)) ≤
      J.map (ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  apply Ideal.mem_map_of_mem
  apply hJ
  apply Ideal.mem_map_of_mem
  exact (Ideal.symm_apply_mem_of_equiv_iff
    (I := A.ideal) (f := ULift.ringEquiv.symm)).mpr hx

/-- Descend the base and presentation maps of an envelope along the lift equivalences. -/
private noncomputable def envelopeOfLift (A : DividedPowerRing.{u}) {B : Type v}
    [CommRing B] (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (E : DividedPowerEnvelope (liftedBase.{u, v} A) (B := ULift.{u} B)
      ((ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom.comp
        (f.comp (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom))
      (J.map (ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom)
      (liftedMap_ideal A f J hJ)) :
    DividedPowerEnvelope A f J hJ := by
  let A' := liftedBase.{u, v} A
  let J' : Ideal (ULift.{u} B) :=
    J.map (ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom
  let f' : A' →+* ULift.{u} B :=
    (ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom.comp
      (f.comp (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom)
  have hJ' : A'.ideal.map f' ≤ J' := liftedMap_ideal A f J hJ
  let iA := baseUp.{u, v} A
  let dA := baseDown.{u, v} A
  let iB : IdealPair.Hom J J' :=
    IdealPair.Hom.ofRingHom (ULift.ringEquiv : ULift.{u} B ≃+* B).symm.toRingHom le_rfl
  let dB : IdealPair.Hom J' J :=
    IdealPair.Hom.ofRingHom (ULift.ringEquiv : ULift.{u} B ≃+* B).toRingHom (by
      dsimp [J']
      simp only [Ideal.map_map, RingEquiv.comp_symm, Ideal.map_id, le_refl])
  refine {
    object := E.object
    structureMap := E.structureMap.comp iA
    algebraMap := IdealPair.Hom.comp E.algebraMap iB
    algebraMap_comp := ?_
    homEquiv := fun C a => ?_
    homEquiv_apply := ?_ }
  · apply RingHom.ext
    intro x
    exact congrArg (fun g => g (ULift.up x)) E.algebraMap_comp
  · let sourceEquiv :
        {q : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers //
          q.comp (E.structureMap.comp iA) = a} ≃
        {q : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers //
          q.comp E.structureMap = a.comp dA} :=
      Equiv.subtypeEquivRight fun q => by
        constructor
        · intro h
          apply DividedPowers.DPMorphism.ext
          funext x
          exact congrArg (fun g => g x.down) h
        · intro h
          apply DividedPowers.DPMorphism.ext
          funext x
          exact congrArg (fun g => g (ULift.up x)) h
    let targetEquiv :
        IdealPair.HomOver (IdealPair.Hom.ofRingHom f' hJ')
          (IdealPair.Hom.ofDPMorphism (a.comp dA)) ≃
        IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ)
          (IdealPair.Hom.ofDPMorphism a) := {
      toFun := fun t => ⟨IdealPair.Hom.comp t.1 iB, by
        apply IdealPair.Hom.ext_toRingHom
        apply RingHom.ext
        intro x
        exact congrArg (fun g => g.toRingHom (ULift.up x)) t.2⟩
      invFun := fun t => ⟨IdealPair.Hom.comp t.1 dB, by
        apply IdealPair.Hom.ext_toRingHom
        apply RingHom.ext
        intro x
        exact congrArg (fun g => g.toRingHom x.down) t.2⟩
      left_inv := fun t => by
        apply Subtype.ext
        apply IdealPair.Hom.ext_toRingHom
        rfl
      right_inv := fun t => by
        apply Subtype.ext
        apply IdealPair.Hom.ext_toRingHom
        rfl }
    exact (sourceEquiv.trans (E.homEquiv C (a.comp dA))).trans targetEquiv
  · intro C a q
    have hq : q.1.comp E.structureMap = a.comp dA := by
      apply DividedPowers.DPMorphism.ext
      funext x
      exact congrArg (fun g => g x.down) q.2
    exact congrArg (fun t => IdealPair.Hom.comp t iB)
      (E.homEquiv_apply C (a.comp dA) ⟨q.1, hq⟩)

/-- The divided power envelope of an ideal containing the extension of the base divided power
ideal. Its fields give the structural divided power morphism and the functorial universal Hom
equivalence. -/
@[stacks 07H8,
  no_expose,
  stacks 07H9 "the divided power envelope D_{B,gamma}(J) of J in B relative to (A, I, gamma)"]
public noncomputable def dividedPowerEnvelope (A : DividedPowerRing.{u}) {B : Type v}
    [CommRing B] (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) :
    DividedPowerEnvelope A f J hJ :=
  envelopeOfLift A f J hJ (envelopeConstruction _ _ _ (liftedMap_ideal A f J hJ))

/-- **A divided power morphism out of an envelope is determined by its restrictions.**  Two
divided power morphisms out of `D_{B, γ}(J)` which agree on the base and on `B` are equal. -/
theorem envelopeHom_ext {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {J : Ideal B} {g : A →+* B} {hJ : A.ideal.map g ≤ J} (D : DividedPowerEnvelope A g J hJ)
    (E : DividedPowerRing.{max u v})
    (θ₁ θ₂ : DividedPowers.DPMorphism D.object.dividedPowers E.dividedPowers)
    (hstruct : θ₁.comp D.structureMap = θ₂.comp D.structureMap)
    (halg : θ₁.toRingHom.comp D.algebraMap.toRingHom =
      θ₂.toRingHom.comp D.algebraMap.toRingHom) :
    θ₁ = θ₂ := by
  classical
  set aE := θ₁.comp D.structureMap with haE
  have h1 : (⟨θ₁, rfl⟩ : {q : DividedPowers.DPMorphism D.object.dividedPowers E.dividedPowers //
      q.comp D.structureMap = aE}) = ⟨θ₂, hstruct.symm⟩ := by
    apply (D.homEquiv E aE).injective
    apply Subtype.ext
    apply IdealPair.Hom.ext_toRingHom
    rw [D.homEquiv_apply E aE ⟨θ₁, rfl⟩, D.homEquiv_apply E aE ⟨θ₂, hstruct.symm⟩]
    exact halg
  exact congrArg Subtype.val h1

end Envelope

section Factorization

universe u v w x

/-- A commutative ring with its zero ideal and the unique divided power structure on that
ideal, regarded as a divided power ring. -/
public noncomputable def botDPRing (R : Type w) [CommRing R] : DividedPowerRing.{w} where
  carrier := R
  commRing := inferInstance
  ideal := ⊥
  dividedPowers := _root_.dividedPowersBot R

/-- A ring homomorphism vanishing on a divided power ideal is a divided power morphism to the
zero ideal with its trivial divided powers. -/
public noncomputable def dpMorphismToBot {R : Type w} [CommRing R] {I : Ideal R}
    (hI : DividedPowers I) {S : Type x} [CommRing S] (g : R →+* S)
    (hg : ∀ z ∈ I, g z = 0) :
    DividedPowers.DPMorphism hI (botDPRing S).dividedPowers where
  toRingHom := g
  ideal_comp := by
    refine Ideal.map_le_iff_le_comap.2 ?_
    intro z hz
    exact Ideal.mem_bot.2 (hg z hz)
  dpow_comp := by
    intro n z hz
    change (_root_.dividedPowersBot S).dpow n (g z) = g (hI.dpow n z)
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hI.dpow_zero hz, map_one, hg z hz,
        (_root_.dividedPowersBot S).dpow_zero (Ideal.mem_bot.2 rfl)]
    · rw [hg z hz, hg _ (hI.dpow_mem hn hz)]
      exact Ideal.mem_bot.1
        ((_root_.dividedPowersBot S).dpow_mem hn (Ideal.mem_bot.2 rfl))

/-- A ring homomorphism vanishing on an ideal is a morphism of ring--ideal pairs to the zero
ideal of its target. -/
private def idealPairHomToBot {R : Type w} [CommRing R] (I : Ideal R) {S : Type x} [CommRing S]
    (g : R →+* S) (hg : ∀ z ∈ I, g z = 0) : IdealPair.Hom I (botDPRing S).ideal where
  toRingHom := g
  ideal_comp := by
    refine Ideal.map_le_iff_le_comap.2 ?_
    intro z hz
    exact Ideal.mem_bot.2 (hg z hz)

/-- The ring map underlying the preimage of a morphism of pairs under the envelope's universal
equivalence restricts along `algebraMap` to that morphism. -/
private lemma symm_homEquiv_toRingHom_comp {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J} (D : DividedPowerEnvelope A f J hJ)
    (C : DividedPowerRing.{max u v})
    (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers)
    (t : IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ) (IdealPair.Hom.ofDPMorphism a)) :
    ((D.homEquiv C a).symm t).1.toRingHom.comp D.algebraMap.toRingHom = t.1.toRingHom := by
  have h := D.homEquiv_apply C a ((D.homEquiv C a).symm t)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg IdealPair.Hom.toRingHom h.symm

/-- A ring map out of `B` killing `J` extends over the divided power envelope of `J`, by a map
killing the divided power ideal. -/
private lemma exists_ringHom_of_vanishing (A : DividedPowerRing.{u}) {B : Type v} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) (D : DividedPowerEnvelope A f J hJ)
    {S : Type max u v} [CommRing S] (g : B →+* S) (hg : ∀ z ∈ J, g z = 0) :
    ∃ q : D.object.carrier →+* S,
      q.comp D.algebraMap.toRingHom = g ∧ ∀ z ∈ D.object.ideal, q z = 0 := by
  have hgf : ∀ z ∈ A.ideal, (g.comp f) z = 0 :=
    fun z hz => hg _ (hJ (Ideal.mem_map_of_mem _ hz))
  let t := (D.homEquiv (botDPRing S) (dpMorphismToBot A.dividedPowers (g.comp f) hgf)).symm
    ⟨idealPairHomToBot J g hg, IdealPair.Hom.ext_toRingHom _ _ rfl⟩
  refine ⟨t.1.toRingHom, symm_homEquiv_toRingHom_comp D _ _ _, ?_⟩
  · intro z hz
    exact Ideal.mem_bot.1 (t.1.ideal_comp (Ideal.mem_map_of_mem _ hz))

/-- Two ring maps out of the divided power envelope of `J` which kill the divided power ideal
and agree on `B` are equal. -/
private lemma ringHom_eq_of_vanishing (A : DividedPowerRing.{u}) {B : Type v} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) (D : DividedPowerEnvelope A f J hJ)
    {S : Type max u v} [CommRing S] (q₁ q₂ : D.object.carrier →+* S)
    (h₁ : ∀ z ∈ D.object.ideal, q₁ z = 0) (h₂ : ∀ z ∈ D.object.ideal, q₂ z = 0)
    (hagree : q₁.comp D.algebraMap.toRingHom = q₂.comp D.algebraMap.toRingHom) :
    q₁ = q₂ := by
  have hstruct : (dpMorphismToBot D.object.dividedPowers q₁ h₁).comp D.structureMap =
      (dpMorphismToBot D.object.dividedPowers q₂ h₂).comp D.structureMap := by
    apply DividedPowers.DPMorphism.ext
    funext z
    show q₁ (D.structureMap.toRingHom z) = q₂ (D.structureMap.toRingHom z)
    rw [← D.algebraMap_comp]
    exact DFunLike.congr_fun hagree (f z)
  exact congrArg DividedPowers.DPMorphism.toRingHom
    (envelopeHom_ext D (botDPRing S) _ _ hstruct hagree)

/-- The divided power envelope `D` of an ideal `J ⊆ B` factors the quotient map of `B` by `J`
as `B ⟶ D ⟶ B ⧸ J` through maps over `A`: the canonical map from `B` carries `J` into the
divided power ideal of `D`, and that ideal is precisely the kernel of the second map, which is
the unique ring map to `B ⧸ J` with those two properties. -/
@[stacks 07HA]
public lemma dividedPowerEnvelope_factorization (A : DividedPowerRing.{u}) {B : Type v}
    [CommRing B] (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ) :
    J.map D.algebraMap.toRingHom ≤ D.object.ideal ∧
      ∃ p : D.object.carrier →+* B ⧸ J,
        p.comp D.algebraMap.toRingHom = Ideal.Quotient.mk J ∧
        p.comp D.structureMap.toRingHom = (Ideal.Quotient.mk J).comp f ∧
        Function.Surjective p ∧
        RingHom.ker p = D.object.ideal ∧
        ∀ p' : D.object.carrier →+* B ⧸ J,
          p'.comp D.algebraMap.toRingHom = Ideal.Quotient.mk J →
          D.object.ideal ≤ RingHom.ker p' → p' = p := by
  refine ⟨D.algebraMap.ideal_comp, ?_⟩
  obtain ⟨p, hp_alg, hp_zero⟩ :
      ∃ p : D.object.carrier →+* B ⧸ J,
        (∀ x : B, p (D.algebraMap.toRingHom x) = Ideal.Quotient.mk J x) ∧
        ∀ z ∈ D.object.ideal, p z = 0 := by
    obtain ⟨q, hq_alg, hq_zero⟩ := exists_ringHom_of_vanishing A f J hJ D
      ((ULift.ringEquiv : ULift.{u} (B ⧸ J) ≃+* (B ⧸ J)).symm.toRingHom.comp
        (Ideal.Quotient.mk J))
      fun z hz => by simp [Ideal.Quotient.eq_zero_iff_mem.2 hz]
    refine ⟨(ULift.ringEquiv : ULift.{u} (B ⧸ J) ≃+* (B ⧸ J)).toRingHom.comp q, ?_, ?_⟩
    · intro x
      have hx := DFunLike.congr_fun hq_alg x
      simp only [RingHom.coe_comp, Function.comp_apply] at hx ⊢
      rw [hx]
      simp
    · intro z hz
      simp only [RingHom.coe_comp, Function.comp_apply, hq_zero z hz, map_zero]
  obtain ⟨u, hu⟩ :
      ∃ u : (B ⧸ J) →+* D.object.carrier ⧸ D.object.ideal,
        ∀ x : B, u (Ideal.Quotient.mk J x) =
          Ideal.Quotient.mk D.object.ideal (D.algebraMap.toRingHom x) :=
    ⟨Ideal.Quotient.lift J ((Ideal.Quotient.mk D.object.ideal).comp D.algebraMap.toRingHom)
        fun z hz => Ideal.Quotient.eq_zero_iff_mem.2
          (D.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hz)),
      fun x => by simp⟩
  have hpc : p.comp D.algebraMap.toRingHom = Ideal.Quotient.mk J := RingHom.ext hp_alg
  have hmk : (Ideal.Quotient.mk D.object.ideal :
      D.object.carrier →+* D.object.carrier ⧸ D.object.ideal) = u.comp p := by
    refine ringHom_eq_of_vanishing A f J hJ D _ _
      (fun z hz => Ideal.Quotient.eq_zero_iff_mem.2 hz)
      (fun z hz => by
        simp only [RingHom.coe_comp, Function.comp_apply, hp_zero z hz, map_zero]) ?_
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hp_alg x, hu x]
  refine ⟨p, hpc, ?_, ?_, ?_, ?_⟩
  · rw [← D.algebraMap_comp, ← RingHom.comp_assoc, hpc]
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨D.algebraMap.toRingHom x, hp_alg x⟩
  · refine le_antisymm (fun z hz => ?_) fun z hz => RingHom.mem_ker.2 (hp_zero z hz)
    have h0 : Ideal.Quotient.mk D.object.ideal z = 0 := by
      rw [hmk]
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.mem_ker.1 hz, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  · intro p' hp'alg hp'ker
    obtain ⟨v, hv⟩ :
        ∃ v : D.object.carrier ⧸ D.object.ideal →+* B ⧸ J,
          ∀ z : D.object.carrier, v (Ideal.Quotient.mk D.object.ideal z) = p' z :=
      ⟨Ideal.Quotient.lift D.object.ideal p' fun z hz => RingHom.mem_ker.1 (hp'ker hz),
        fun z => by simp⟩
    have hvu : ∀ y : B ⧸ J, v (u y) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hu x, hv (D.algebraMap.toRingHom x)]
      simpa using DFunLike.congr_fun hp'alg x
    refine RingHom.ext fun z => ?_
    have hz := hv z
    rw [hmk] at hz
    simp only [RingHom.coe_comp, Function.comp_apply] at hz
    rw [← hz, hvu (p z)]

end Factorization

section Quotient

universe u v

/-- The ideal in a divided power envelope generated by all positive divided powers of the
images of elements in the kernel of a ring homomorphism. -/
public def dividedPowerKernelIdeal {B' B : Type u} [CommRing B'] [CommRing B]
    (phi : B' →+* B) {A : DividedPowerRing} {f' : A →+* B'} {J' : Ideal B'}
    {hJ' : A.ideal.map f' ≤ J'} (D' : DividedPowerEnvelope A f' J' hJ') :
    Ideal D'.object :=
  Ideal.span {x | ∃ (n : ℕ) (_ : 0 < n) (k : B'),
    k ∈ RingHom.ker phi ∧
      x = D'.object.dividedPowers.dpow n (D'.algebraMap.toRingHom k)}

/-- For a surjection `B' → B`, the canonical map from the divided power envelope of the
inverse image of `J` to the divided power envelope of `J` is surjective, and its kernel is
generated by the positive divided powers of the original kernel. -/
@[stacks 07HB]
public lemma dividedPowerEnvelope_quotient
    (A : DividedPowerRing) {B' B : Type u} [CommRing B'] [CommRing B]
    (f' : A →+* B') (f : A →+* B) (phi : B' →+* B)
    (hphi : phi.comp f' = f) (hphi_surjective : Function.Surjective phi)
    (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A f' (J.comap phi) (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hphi]
      exact hJ)) :
    ∃ q : DividedPowers.DPMorphism D'.object.dividedPowers D.object.dividedPowers,
      q.comp D'.structureMap = D.structureMap ∧
      q.toRingHom.comp D'.algebraMap.toRingHom = D.algebraMap.toRingHom.comp phi ∧
      Function.Surjective q ∧
      D'.object.ideal.map q.toRingHom = D.object.ideal ∧
      RingHom.ker q.toRingHom = dividedPowerKernelIdeal phi D' ∧
      (∀ q' : DividedPowers.DPMorphism D'.object.dividedPowers D.object.dividedPowers,
        q'.comp D'.structureMap = D.structureMap →
        q'.toRingHom.comp D'.algebraMap.toRingHom = D.algebraMap.toRingHom.comp phi →
        q' = q) := by
  classical
  have hkI : ∀ k ∈ RingHom.ker phi, D'.algebraMap.toRingHom k ∈ D'.object.ideal := fun k hk =>
    D'.algebraMap.ideal_comp (Ideal.mem_map_of_mem _
      (Ideal.mem_comap.2 (by simp [RingHom.mem_ker.mp hk])))
  let K' := dividedPowerKernelIdeal phi D'
  let S : Set D'.object := {x | ∃ (n : ℕ) (_ : 0 < n) (k : B'),
    k ∈ RingHom.ker phi ∧
      x = D'.object.dividedPowers.dpow n (D'.algebraMap.toRingHom k)}
  let hK' : DividedPowers.IsSubDPIdeal D'.object.dividedPowers K' := by
    show DividedPowers.IsSubDPIdeal D'.object.dividedPowers (Ideal.span S)
    have hS : S ⊆ D'.object.ideal := by
      rintro x ⟨n, hn, k, hk, rfl⟩
      exact D'.object.dividedPowers.dpow_mem (Nat.ne_of_gt hn) (hkI k hk)
    have hGen : ∀ {n : ℕ}, n ≠ 0 → ∀ x ∈ S,
        D'.object.dividedPowers.dpow n x ∈ Ideal.span S := by
      intro n hn x hx
      rcases hx with ⟨m, hm, k, hk, rfl⟩
      rw [D'.object.dividedPowers.dpow_comp (m := n) (n := m)
        (Nat.ne_of_gt hm) (hkI k hk)]
      apply Ideal.mul_mem_left
      exact Ideal.subset_span ⟨n * m, Nat.mul_pos (Nat.pos_of_ne_zero hn) hm, k, hk, rfl⟩
    exact (DividedPowers.span_isSubDPIdeal_iff (hI := D'.object.dividedPowers)
      hS).2 hGen
  have hKI : K' ≤ D'.object.ideal := hK'.isSubideal
  let hKInf : DividedPowers.IsSubDPIdeal D'.object.dividedPowers
      (K' ⊓ D'.object.ideal) := by
    simpa [inf_eq_left.mpr hKI] using hK'
  let C : DividedPowerRing :=
    { carrier := D'.object.carrier ⧸ K'
      commRing := inferInstance
      ideal := D'.object.ideal.map (Ideal.Quotient.mk K')
      dividedPowers := DividedPowers.Quotient.dividedPowers
        D'.object.dividedPowers hKInf }
  let piDP : DividedPowers.DPMorphism D'.object.dividedPowers C.dividedPowers :=
    DividedPowers.DPMorphism.mk'
      (DividedPowers.Quotient.isDPMorphism D'.object.dividedPowers hKInf)
  let pi : D'.object.carrier →+* C.carrier := Ideal.Quotient.mk K'
  have hpi_surj : Function.Surjective pi := Ideal.Quotient.mk_surjective
  let b' : B' →+* C.carrier := pi.comp D'.algebraMap.toRingHom
  have hb'ker : RingHom.ker phi ≤ RingHom.ker b' := by
    intro k hk
    show b' k = 0
    show pi (D'.algebraMap.toRingHom k) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show D'.algebraMap.toRingHom k ∈ K'
    rw [← D'.object.dividedPowers.dpow_one (hkI k hk)]
    exact Ideal.subset_span ⟨1, by decide, k, hk, rfl⟩
  let b : B →+* C.carrier :=
    (Ideal.Quotient.lift (RingHom.ker phi) b'
      (fun x hx => RingHom.mem_ker.mp (hb'ker hx))).comp
      (RingHom.quotientKerEquivOfSurjective hphi_surjective).symm.toRingHom
  have hb_comp : b.comp phi = b' := by
    ext x
    show (Ideal.Quotient.lift (RingHom.ker phi) b'
      (fun y hy => RingHom.mem_ker.mp (hb'ker hy)))
      ((RingHom.quotientKerEquivOfSurjective hphi_surjective).symm (phi x)) = b' x
    simp
  let a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers :=
    piDP.comp D'.structureMap
  have hb_ideal : J.map b ≤ C.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨x', rfl⟩ := hphi_surjective x
    show b (phi x') ∈ D'.object.ideal.map pi
    rw [← RingHom.comp_apply, hb_comp]
    exact Ideal.mem_map_of_mem pi (D'.algebraMap.ideal_comp
      (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr (by simpa using hx))))
  let bPair : IdealPair.Hom J C.ideal := IdealPair.Hom.ofRingHom b hb_ideal
  let basePair : IdealPair.Hom A.ideal C.ideal := IdealPair.Hom.ofDPMorphism a
  have hbOver : IdealPair.Hom.comp bPair (IdealPair.Hom.ofRingHom f hJ) = basePair := by
    apply IdealPair.Hom.ext_toRingHom
    show b.comp f = a.toRingHom
    calc
      b.comp f = b.comp (phi.comp f') := by rw [hphi]
      _ = (b.comp phi).comp f' := by ext x; rfl
      _ = b'.comp f' := by rw [hb_comp]
      _ = piDP.toRingHom.comp D'.structureMap.toRingHom := by
        show (pi.comp D'.algebraMap.toRingHom).comp f' =
          pi.comp D'.structureMap.toRingHom
        ext x
        calc
          pi (D'.algebraMap.toRingHom (f' x)) =
              (pi.comp (D'.algebraMap.toRingHom.comp f')) x := rfl
          _ = (pi.comp D'.structureMap.toRingHom) x := by rw [D'.algebraMap_comp]
          _ = pi (D'.structureMap x) := rfl
      _ = a.toRingHom := rfl
  let rData := (D.homEquiv C a).symm ⟨bPair, hbOver⟩
  let r : DividedPowers.DPMorphism D.object.dividedPowers C.dividedPowers := rData.1
  have hr_base : r.comp D.structureMap = a := rData.2
  have hr_alg : r.toRingHom.comp D.algebraMap.toRingHom = b :=
    symm_homEquiv_toRingHom_comp D C a ⟨bPair, hbOver⟩
  have hJ' : A.ideal.map f' ≤ J.comap phi := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hphi]
    exact hJ
  let gPair : IdealPair.Hom (J.comap phi) D.object.ideal :=
    IdealPair.Hom.ofRingHom (D.algebraMap.toRingHom.comp phi) (by
      rw [← Ideal.map_map]
      exact (Ideal.map_mono Ideal.map_comap_le).trans D.algebraMap.ideal_comp)
  have hgOver : IdealPair.Hom.comp gPair (IdealPair.Hom.ofRingHom f' hJ') =
      IdealPair.Hom.ofDPMorphism D.structureMap := by
    apply IdealPair.Hom.ext_toRingHom
    show (D.algebraMap.toRingHom.comp phi).comp f' = D.structureMap.toRingHom
    rw [RingHom.comp_assoc, hphi, D.algebraMap_comp]
  let qData := (D'.homEquiv D.object D.structureMap).symm ⟨gPair, hgOver⟩
  let q : DividedPowers.DPMorphism D'.object.dividedPowers D.object.dividedPowers := qData.1
  have hq_base : q.comp D'.structureMap = D.structureMap := qData.2
  have hq_alg : q.toRingHom.comp D'.algebraMap.toRingHom =
      D.algebraMap.toRingHom.comp phi := by
    exact symm_homEquiv_toRingHom_comp D' D.object D.structureMap ⟨gPair, hgOver⟩
  have hKker : K' ≤ RingHom.ker q.toRingHom := by
    show Ideal.span S ≤ RingHom.ker q.toRingHom
    rw [Ideal.span_le]
    rintro x ⟨n, hn, k, hk, rfl⟩
    show q.toRingHom (D'.object.dividedPowers.dpow n
      (D'.algebraMap.toRingHom k)) = 0
    rw [← q.dpow_comp (D'.algebraMap.toRingHom k) (hkI k hk)]
    have hqk : q.toRingHom (D'.algebraMap.toRingHom k) = 0 := by
      rw [← RingHom.comp_apply, hq_alg, RingHom.comp_apply,
        RingHom.mem_ker.mp hk, map_zero]
    rw [hqk, D.object.dividedPowers.dpow_eval_zero (Nat.ne_of_gt hn)]
  have hKker' : ∀ x : D'.object, x ∈ K' → q.toRingHom x = 0 :=
    fun x hx => RingHom.mem_ker.mp (hKker hx)
  let s : C.carrier →+* D.object.carrier := Ideal.Quotient.lift K' q.toRingHom hKker'
  have hs_pi : s.comp pi = q.toRingHom :=
    Ideal.Quotient.lift_comp_mk K' q.toRingHom hKker'
  let sDP : DividedPowers.DPMorphism C.dividedPowers D.object.dividedPowers :=
    DividedPowers.DPMorphism.mk' (f := s) (by
      refine ⟨?_, ?_⟩
      · show (D'.object.ideal.map pi).map s ≤ D.object.ideal
        rw [Ideal.map_map, hs_pi]
        exact q.ideal_comp
      · intro n x hx
        obtain ⟨y, hy, rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective pi hpi_surj).mp hx
        rw [DividedPowers.Quotient.dpow_apply D'.object.dividedPowers hKInf hy]
        show D.object.dividedPowers.dpow n (s (pi y)) =
          s (pi (D'.object.dividedPowers.dpow n y))
        rw [show s (pi y) = q.toRingHom y from
        RingHom.ext_iff.mp hs_pi y,
          q.dpow_comp y hy]
        exact (RingHom.ext_iff.mp hs_pi
          (D'.object.dividedPowers.dpow n y)).symm)
  have hs_alg : sDP.toRingHom.comp b = D.algebraMap.toRingHom := by
    ext x
    obtain ⟨x', rfl⟩ := hphi_surjective x
    show s (b (phi x')) = D.algebraMap.toRingHom (phi x')
    have hb : b (phi x') = b' x' := by
      simpa [RingHom.comp_apply] using (RingHom.ext_iff.mp hb_comp x')
    have hq : q.toRingHom (D'.algebraMap.toRingHom x') =
        D.algebraMap.toRingHom (phi x') := by
      simpa [RingHom.comp_apply] using (RingHom.ext_iff.mp hq_alg x')
    calc
      s (b (phi x')) = s (pi (D'.algebraMap.toRingHom x')) := by
        rw [hb]
        rfl
      _ = q.toRingHom (D'.algebraMap.toRingHom x') :=
        RingHom.ext_iff.mp hs_pi (D'.algebraMap.toRingHom x')
      _ = D.algebraMap.toRingHom (phi x') := hq
  let rq : DividedPowers.DPMorphism D'.object.dividedPowers C.dividedPowers := r.comp q
  have hrq_base : rq.comp D'.structureMap = a := by
    rw [show rq.comp D'.structureMap = r.comp (q.comp D'.structureMap) from rfl, hq_base, hr_base]
  have hrq_alg : rq.toRingHom.comp D'.algebraMap.toRingHom = b' := by
    show (r.toRingHom.comp q.toRingHom).comp D'.algebraMap.toRingHom = b'
    rw [RingHom.comp_assoc, hq_alg, ← RingHom.comp_assoc, hr_alg, hb_comp]
  have hrq_eq_pi : rq.toRingHom = pi :=
    congrArg DividedPowers.DPMorphism.toRingHom
      (envelopeHom_ext D' C rq piDP hrq_base hrq_alg)
  have hrs_id : r.toRingHom.comp sDP.toRingHom = RingHom.id C.carrier := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hpi_surj x
    exact (congrArg r.toRingHom (DFunLike.congr_fun hs_pi y)).trans
      (DFunLike.congr_fun hrq_eq_pi y)
  have hsr_id : sDP.toRingHom.comp r.toRingHom = RingHom.id D.object.carrier := by
    have ht_base : (sDP.comp r).comp D.structureMap = D.structureMap := by
      apply DividedPowers.DPMorphism.ext
      funext x
      exact (congrArg s (DFunLike.congr_fun hr_base x)).trans
        ((DFunLike.congr_fun hs_pi _).trans (DFunLike.congr_fun hq_base x))
    exact congrArg DividedPowers.DPMorphism.toRingHom
      (envelopeHom_ext D D.object (sDP.comp r) (.id _) ht_base (by
        show (sDP.toRingHom.comp r.toRingHom).comp D.algebraMap.toRingHom =
          (RingHom.id _).comp D.algebraMap.toRingHom
        rw [RingHom.comp_assoc, hr_alg, hs_alg, RingHom.id_comp]))
  have hsp : ∀ y, s (pi y) = q.toRingHom y := DFunLike.congr_fun hs_pi
  have hqy : ∀ x y, pi y = r.toRingHom x → q.toRingHom y = x := fun x y hy =>
    (hsp y).symm.trans <| (congrArg s hy).trans (DFunLike.congr_fun hsr_id x)
  have hq_surj : Function.Surjective q := fun x => by
    obtain ⟨y, hy⟩ := hpi_surj (r.toRingHom x)
    exact ⟨y, hqy x y hy⟩
  have hq_ideal : D'.object.ideal.map q.toRingHom = D.object.ideal := by
    refine le_antisymm q.ideal_comp fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective pi hpi_surj).mp
      (r.ideal_comp (Ideal.mem_map_of_mem _ hx))
    exact (Ideal.mem_map_iff_of_surjective q.toRingHom hq_surj).2 ⟨y, hy, hqy x y hxy⟩
  have hq_ker : RingHom.ker q.toRingHom = K' := by
    refine le_antisymm (fun x hx => ?_) hKker
    have hs_inj : Function.Injective sDP.toRingHom := fun y z hyz =>
      (DFunLike.congr_fun hrs_id y).symm.trans <|
        (congrArg r.toRingHom hyz).trans (DFunLike.congr_fun hrs_id z)
    refine Ideal.Quotient.eq_zero_iff_mem.mp (hs_inj ?_)
    rw [map_zero]
    exact (hsp x).trans (RingHom.mem_ker.mp hx)
  refine ⟨q, hq_base, hq_alg, hq_surj, hq_ideal, hq_ker, ?_⟩
  intro q' hq'base hq'alg
  exact envelopeHom_ext D' D.object q' q (hq'base.trans hq_base.symm) (hq'alg.trans hq_alg.symm)

end Quotient

end Crystalline

end
