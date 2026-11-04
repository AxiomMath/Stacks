module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Functoriality of divided power differentials

Let `A → B` be a ring map and let an ideal `J` of `B` carry divided powers `δ`.  A divided power
morphism `(B, J, δ) → (C, K, ε)` over `A` induces an additive map `Ω_{B/A, δ} → Ω_{C/A, ε}`,
semilinear over the morphism and determined by its effect on universal divided power
differentials.  This file constructs that map, proves it functorial, and derives the two
comparison statements used to identify differentials of quotients.

The first comparison says that for a sub-divided-power-ideal `K ⊆ J` whose universal
differentials already lie in `K · Ω_{B/A, δ}`, the differentials of the quotient divided power
ring are `Ω_{B/A, δ} / K · Ω_{B/A, δ}`.  The second transfers that statement along an arbitrary
surjective divided power morphism with kernel `K`.

## Main definitions

* `Crystalline.differentialsModPow` — the divided power differentials of `B` modulo `pᵉ`.
* `Crystalline.completedDifferentialsModPow` — the same for the `p`-adic completion of `B`.
* `Crystalline.mapDifferentialsOfDPMorphism` — the map induced by a divided power morphism.
* `Crystalline.mapDifferentialsOfDPMorphismₛₗ` — the same map, bundled as a semilinear map over
  the morphism.
* `Crystalline.mapDifferentialFormsOfDPMorphism` — **the comparison `Ωⁱ_{B/A,δ} → Ωⁱ_{C/A,ε}` of
  divided power differential forms in every degree**, the exterior power of the semilinear
  degree-one comparison.
* `Crystalline.differentialsQuotientEquiv`, `Crystalline.differentialsSurjectionEquiv` — the two
  quotient comparisons.
* `Crystalline.differentialsEquivOfAlgEquiv` — the equivalence induced by an isomorphism.

## Main results

* `Crystalline.mapDifferentialsOfDPMorphism_d`, `Crystalline.mapDifferentialsOfDPMorphism_smul`,
  `Crystalline.mapDifferentialsOfDPMorphism_comp`, `Crystalline.mapDifferentialsOfDPMorphism_id`
  — the defining formula and functoriality.
* `Crystalline.differentials_hom_ext` — two maps agreeing on universal differentials agree.
* `Crystalline.mapDifferentialFormsOfDPMorphism_ιMulti`,
  `Crystalline.mapDifferentialFormsOfDPMorphism_ιMulti_d`,
  `Crystalline.mapDifferentialFormsOfDPMorphism_ext` — the comparison of forms carries
  `d b₁ ∧ ⋯ ∧ d bᵢ` to `d f(b₁) ∧ ⋯ ∧ d f(bᵢ)`, and that determines it.
* `Crystalline.mapDifferentialFormsOfDPMorphism_id`,
  `Crystalline.mapDifferentialFormsOfDPMorphism_comp` — functoriality of the comparison of
  forms.

## Implementation notes

The induced map is additive rather than linear, because its source and target are modules over
different rings; the semilinearity statement supplies what is needed in practice.  It is built
from the universal property of Kähler differentials followed by the quotient presentation of
divided power differentials, so the only thing to check is that the defining relations of the
source are killed, which is exactly the compatibility of the morphism with divided powers.

Equivalences are returned as subtypes carrying their value on universal differentials, since
that value is what identifies them and `Crystalline.differentials_hom_ext` then makes the
identification unique.

## References

* [Stacks Project, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Crystalline

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-- The module of divided power differentials modulo `p ^ e`. -/
public abbrev differentialsModPow (e : ℕ) : Type v :=
  dividedPowerDifferentials (A := A) delta ⧸
    (DividedPowers.pAdicIdeal (A := B) p ^ e •
      (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)))

/-- The divided power differentials of the completion, modulo `p ^ e`. -/
public noncomputable abbrev completedDifferentialsModPow
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) (e : ℕ) : Type v :=
  dividedPowerDifferentials (A := A) (DividedPowers.completedDividedPowers J delta p hp).1 ⧸
    (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ e •
      (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1)))


/-- The additive map on modules of divided power differentials induced by a divided power
morphism. -/
public noncomputable def mapDifferentialsOfDPMorphism
    {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) :
    dividedPowerDifferentials (A := A) delta →+
      dividedPowerDifferentials (A := A) epsilon := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  letI : SMulCommClass A B C := ⟨fun a b c => by
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]⟩
  let T := dividedPowerDifferentials (A := A) epsilon
  letI : Module B T := Module.compHom T f.toRingHom
  letI : SMul B T := (inferInstance : Module B T).toDistribSMul.toSMul
  letI : IsScalarTower B C T := IsScalarTower.of_algebraMap_smul fun b t => rfl
  letI : Module B Ω[C⁄A] := instModuleKaehlerDifferentialOfSMulCommClass A C
  letI : SMul B Ω[C⁄A] := (inferInstance : Module B Ω[C⁄A]).toDistribSMul.toSMul
  letI : IsScalarTower B C Ω[C⁄A] := IsScalarTower.of_algebraMap_smul fun b t => by
    simp
  let qC : Ω[C⁄A] →ₗ[C] T :=
    (dividedPowerDifferentialRelations (A := A) epsilon).mkQ
  let qB : Ω[C⁄A] →ₗ[B] T := qC.restrictScalars B
  let L : Ω[B⁄A] →ₗ[B] T := qB ∘ₗ KaehlerDifferential.map A A B C
  have hrel : dividedPowerDifferentialRelations (A := A) delta ≤ L.ker := by
    change Submodule.span B
      (Set.range fun z : J × ℕ ↦ dividedPowerDifferentialRelation (A := A) delta z.1 z.2) ≤
        L.ker
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, n⟩, rfl⟩
    change L (KaehlerDifferential.D A B (delta.dpow (n + 1) x) -
      delta.dpow n x • KaehlerDifferential.D A B x) = 0
    dsimp [L, qB, qC]
    rw [map_sub, map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D]
    change dividedPowerDifferential (A := A) epsilon
        (f.toRingHom (delta.dpow (n + 1) x)) -
      delta.dpow n x • dividedPowerDifferential (A := A) epsilon (f.toRingHom x) = 0
    rw [← hf.dpow_comp (n := n + 1) x x.property]
    change dividedPowerDifferential (A := A) epsilon
        (epsilon.dpow (n + 1) (f x)) -
      delta.dpow n x • dividedPowerDifferential (A := A) epsilon (f x) = 0
    rw [dividedPowerDifferential_dpow (A := A) (hJ := epsilon)
      ⟨f x, hf.ideal_comp (Ideal.mem_map_of_mem f.toRingHom x.property)⟩ n]
    change epsilon.dpow n (f.toRingHom x) •
        dividedPowerDifferential (A := A) epsilon (f.toRingHom x) -
      delta.dpow n x • dividedPowerDifferential (A := A) epsilon (f x) = 0
    rw [hf.dpow_comp (n := n) x x.property]
    change algebraMap B C (delta.dpow n x) •
        dividedPowerDifferential (A := A) epsilon (f x) -
      delta.dpow n x • dividedPowerDifferential (A := A) epsilon (f x) = 0
    rw [IsScalarTower.algebraMap_smul (R := B) (A := C) (delta.dpow n x)]
    simp
  exact ((dividedPowerDifferentialRelations (A := A) delta).liftQ L hrel).toAddMonoidHom

/-- For nested subideals of a divided power ideal, the map between the two quotients is a divided
power morphism for the quotient divided powers. -/
public theorem quotientFactor_isDPMorphism
    {K K' : Ideal B} (hKK' : K ≤ K')
    (hK : K ≤ J) (hK' : K' ≤ J)
    (hSK : delta.IsSubDPIdeal K) (hSK' : delta.IsSubDPIdeal K') :
    DividedPowers.IsDPMorphism
      (DividedPowers.Quotient.dividedPowers (hI := delta) (J := K)
        (by simpa [inf_of_le_left hK] using hSK))
      (DividedPowers.Quotient.dividedPowers (hI := delta) (J := K')
        (by simpa [inf_of_le_left hK'] using hSK'))
      (Ideal.Quotient.factor hKK') := by
  let dK := DividedPowers.Quotient.dividedPowers (hI := delta) (J := K)
    (by simpa [inf_of_le_left hK] using hSK)
  let dK' := DividedPowers.Quotient.dividedPowers (hI := delta) (J := K')
    (by simpa [inf_of_le_left hK'] using hSK')
  have hqK : DividedPowers.IsDPMorphism delta dK (Ideal.Quotient.mk K) := by
    simpa [dK] using
      (DividedPowers.Quotient.isDPMorphism delta (J := K)
        (by simpa [inf_of_le_left hK] using hSK))
  have hqK' : DividedPowers.IsDPMorphism delta dK' (Ideal.Quotient.mk K') := by
    simpa [dK'] using
      (DividedPowers.Quotient.isDPMorphism delta (J := K')
        (by simpa [inf_of_le_left hK'] using hSK'))
  apply DividedPowers.IsDPMorphism.of_comp delta dK dK'
      (Ideal.Quotient.mk K) (Ideal.Quotient.factor hKK') ?_ hqK ?_
  · rfl
  · simpa [RingHom.comp_apply] using hqK'

/-- The induced map on divided power differentials carries the universal differential of an element
to the universal differential of its image. -/
public theorem mapDifferentialsOfDPMorphism_d
    {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) (b : B) :
    mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
      epsilon f hf (dividedPowerDifferential (A := A) delta b) =
      dividedPowerDifferential (A := A) epsilon (f b) := by
  classical
  let : Algebra B C := f.toRingHom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let : SMulCommClass A B C := ⟨fun a b c => by
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]⟩
  let T := dividedPowerDifferentials (A := A) epsilon
  let : Module B T := Module.compHom T f.toRingHom
  let : SMul B T := (inferInstance : Module B T).toDistribSMul.toSMul
  let : IsScalarTower B C T := IsScalarTower.of_algebraMap_smul fun b t => rfl
  let : Module B Ω[C⁄A] := instModuleKaehlerDifferentialOfSMulCommClass A C
  let : SMul B Ω[C⁄A] := (inferInstance : Module B Ω[C⁄A]).toDistribSMul.toSMul
  let : IsScalarTower B C Ω[C⁄A] := IsScalarTower.of_algebraMap_smul fun b t => by simp
  dsimp [mapDifferentialsOfDPMorphism, dividedPowerDifferential]
  rw [KaehlerDifferential.map_D A A B C b]
  rfl

/-- The induced map on divided power differentials is semilinear over the divided power
morphism. -/
public theorem mapDifferentialsOfDPMorphism_smul
    {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
    (b : B) (omega : dividedPowerDifferentials (A := A) delta) :
    letI : Module B (dividedPowerDifferentials (A := A) epsilon) :=
      Module.compHom _ f.toRingHom
    mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
      epsilon f hf (b • omega) =
    f b • mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
      epsilon f hf omega := by
  classical
  let : Algebra B C := f.toRingHom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let : SMulCommClass A B C := ⟨fun a b c => by
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]⟩
  let T := dividedPowerDifferentials (A := A) epsilon
  let : Module B T := Module.compHom T f.toRingHom
  let : SMul B T := (inferInstance : Module B T).toDistribSMul.toSMul
  let : IsScalarTower B C T := IsScalarTower.of_algebraMap_smul fun b t => rfl
  let : Module B Ω[C⁄A] := instModuleKaehlerDifferentialOfSMulCommClass A C
  let : SMul B Ω[C⁄A] := (inferInstance : Module B Ω[C⁄A]).toDistribSMul.toSMul
  let : IsScalarTower B C Ω[C⁄A] := IsScalarTower.of_algebraMap_smul fun b t => by simp
  dsimp [mapDifferentialsOfDPMorphism]
  exact map_smul _ b omega

/-- The universal divided power differential of a product with a scalar from the base is the scalar
multiple of the universal differential. -/
public theorem dividedPowerDifferential_algebraMap_mul (a : A) (b : B) :
    dividedPowerDifferential (A := A) delta (algebraMap A B a * b) =
      algebraMap A B a • dividedPowerDifferential (A := A) delta b := by
  show (dividedPowerDifferentialRelations (A := A) delta).mkQ
      (KaehlerDifferential.D A B (algebraMap A B a * b)) = _
  calc
    _ = (dividedPowerDifferentialRelations (A := A) delta).mkQ
          (a • KaehlerDifferential.D A B b) := by
            congr 1
            rw [← Algebra.smul_def]
            exact (KaehlerDifferential.D A B).map_smul a b
    _ = a • dividedPowerDifferential (A := A) delta b := by
          show a • (dividedPowerDifferentialRelations (A := A) delta).mkQ
            (KaehlerDifferential.D A B b) = _
          rfl
    _ = algebraMap A B a • dividedPowerDifferential (A := A) delta b := by
          rw [IsScalarTower.algebraMap_smul (R := A) (A := B)]

/-- The universal divided power differential of an element of `pⁿ B` lies in `pⁿ` times the module
of divided power differentials. -/
public theorem dividedPowerDifferential_mem_pAdicPow
    (n : ℕ) {b : B}
    (hb : b ∈ DividedPowers.pAdicIdeal (A := B) p ^ n) :
    dividedPowerDifferential (A := A) delta b ∈
      DividedPowers.pAdicIdeal (A := B) p ^ n •
        (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)) := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow] at hb
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (x := b) (y := (p : B) ^ n)).mp hb
  have hb' : b = (p : B) ^ n * c := by rw [← mul_comm, hc]
  have hcast : algebraMap A B ((p : A) ^ n) = (p : B) ^ n := by simp
  rw [hb', ← hcast, dividedPowerDifferential_algebraMap_mul]
  exact Submodule.smul_mem_smul
    (by simpa using Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : B)) n)
    Submodule.mem_top

/-- Two additive maps out of the module of divided power differentials agree as soon as they agree
on the universal differentials and are semilinear over a common ring map. -/
private theorem differentials_hom_ext_aux
    {C M : Type*} [CommRing C] [AddCommGroup M] [Module C M]
    (f : B →+* C) (F G : dividedPowerDifferentials (A := A) delta →+ M)
    (hF : ∀ b x, F (b • x) = f b • F x)
    (hG : ∀ b x, G (b • x) = f b • G x)
    (hd : ∀ b, F (dividedPowerDifferential (A := A) delta b) =
      G (dividedPowerDifferential (A := A) delta b)) : F = G := by
  ext x
  have hx : x ∈ Submodule.span B (Set.range (dividedPowerDifferential (A := A) delta)) := by
    rw [dividedPowerDifferentials_span (A := A) delta]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact hd b
  | zero => simp
  | add x y hx hy ex ey => simp [ex, ey]
  | smul b x hx ex => rw [hF, hG, ex]

/-- The induced maps on divided power differentials compose. -/
public theorem mapDifferentialsOfDPMorphism_comp
    {C D : Type*} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    {K : Ideal C} {L : Ideal D}
    (epsilon : DividedPowers K) (zeta : DividedPowers L)
    (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
    (hg : DividedPowers.IsDPMorphism epsilon zeta g.toRingHom) :
    (mapDifferentialsOfDPMorphism (A := A) (J := K) (delta := epsilon)
      zeta g hg).comp
      (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
        epsilon f hf) =
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
        zeta (g.comp f) (DividedPowers.IsDPMorphism.comp zeta hg hf) := by
  have hcomp : DividedPowers.IsDPMorphism delta zeta (g.comp f).toRingHom := by
    convert DividedPowers.IsDPMorphism.comp zeta hg hf using 1
    ext x
    rfl
  refine AddMonoidHom.ext fun omega ↦ DFunLike.congr_fun
    (differentials_hom_ext_aux (J := J) (delta := delta) (g.comp f).toRingHom _ _ ?_ ?_ ?_) omega
  · intro a x
    change (mapDifferentialsOfDPMorphism (A := A) (J := K) (delta := epsilon) zeta g hg)
        (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf (a • x)) = _
    rw [mapDifferentialsOfDPMorphism_smul (A := A) (B := B) (J := J) (delta := delta)
        epsilon f hf a x,
      mapDifferentialsOfDPMorphism_smul (A := A) (B := C) (J := K) (delta := epsilon)
        zeta g hg (f a)]
    rfl
  · exact mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta)
      zeta (g.comp f) hcomp
  · intro b
    change (mapDifferentialsOfDPMorphism (A := A) (J := K) (delta := epsilon) zeta g hg)
        (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf
          (dividedPowerDifferential (A := A) delta b)) = _
    rw [mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := delta) epsilon f hf b,
      mapDifferentialsOfDPMorphism_d (A := A) (J := K) (delta := epsilon) zeta g hg (f b),
      mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := delta) zeta (g.comp f) hcomp b]
    rfl

/-- The map induced by the identity divided power morphism is the identity. -/
public theorem mapDifferentialsOfDPMorphism_id :
    mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
      delta (AlgHom.id A B) (DividedPowers.DPMorphism.id delta).isDPMorphism =
      AddMonoidHom.id _ := by
  have hid : DividedPowers.IsDPMorphism delta delta (AlgHom.id A B).toRingHom := by
    convert (DividedPowers.DPMorphism.id delta).isDPMorphism using 1
    ext x
    rfl
  refine AddMonoidHom.ext fun omega ↦ DFunLike.congr_fun
    (differentials_hom_ext_aux (J := J) (delta := delta) (RingHom.id B) _ _ ?_ ?_ ?_) omega
  · exact mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta)
      delta (AlgHom.id A B) hid
  · intro b x
    rfl
  · exact mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := delta)
      delta (AlgHom.id A B) hid

/-- For a sub-divided-power-ideal `K` whose universal differentials lie in `K` times the
differentials, the divided power differentials of the quotient are the differentials modulo `K`,
by an equivalence determined by its value on universal differentials. -/
public noncomputable def differentialsQuotientEquiv
    (K : Ideal B) (hK : delta.IsSubDPIdeal K)
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) :
    let dq := DividedPowers.Quotient.dividedPowers delta
      (by simpa [inf_of_le_left hK.isSubideal] using hK)
    { E : (dividedPowerDifferentials (A := A) delta ⧸
        K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃ₗ[B]
        dividedPowerDifferentials (A := A) dq //
      ∀ b, E (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b)) =
        dividedPowerDifferential (A := A) dq (Ideal.Quotient.mk K b) } := by
  let M := dividedPowerDifferentials (A := A) delta
  let T := TensorProduct B (B ⧸ K) M
  let N : Submodule (B ⧸ K) T := Submodule.span (B ⧸ K)
    (Set.range fun k : K ↦ TensorProduct.tmul B (1 : B ⧸ K)
      (dividedPowerDifferential (A := A) delta k))
  let E := TensorProduct.quotTensorEquivQuotSMul M K
  have hN : N = ⊥ := by
    refine eq_bot_iff.mpr (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    apply E.injective
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hd k k.property)
  let F := dividedPowerDifferentialsQuotientEquiv
    (A := A) (DividedPowerRing.of B J delta) K hK
  refine ⟨E.symm.trans (((N.quotEquivOfEqBot hN).symm.restrictScalars B).trans
    (F.val.restrictScalars B)), ?_⟩
  intro b
  simpa [E, LinearEquiv.trans_apply, Submodule.quotEquivOfEqBot_symm_apply,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk] using F.property b

/-- An isomorphism of divided power rings induces an equivalence of their modules of divided power
differentials, carrying universal differentials to universal differentials. -/
public noncomputable def differentialsEquivOfAlgEquiv
    {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}
    (epsilon : DividedPowers K) (f : B ≃ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toAlgHom.toRingHom)
    (hJ : J.map f.toAlgHom.toRingHom = K) :
    { E : dividedPowerDifferentials (A := A) delta ≃+
        dividedPowerDifferentials (A := A) epsilon //
      E.toAddMonoidHom = mapDifferentialsOfDPMorphism (J := _) (delta := delta) epsilon
        f.toAlgHom hf } := by
  have hg : epsilon.IsDPMorphism delta f.symm.toAlgHom.toRingHom := by
    apply DividedPowers.IsDPMorphism.of_comp delta epsilon delta
      f.toAlgHom.toRingHom f.symm.toAlgHom.toRingHom hJ.symm hf
    have heq : f.symm.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom = RingHom.id B := by
      ext x
      exact f.symm_apply_apply x
    rw [heq]
    exact (DividedPowers.DPMorphism.id delta).isDPMorphism
  let F := mapDifferentialsOfDPMorphism (J := _) (delta := delta) epsilon f.toAlgHom hf
  let G := mapDifferentialsOfDPMorphism (J := _) (delta := epsilon) delta f.symm.toAlgHom hg
  have hGF : G.comp F = AddMonoidHom.id _ := by
    rw [mapDifferentialsOfDPMorphism_comp]
    have he : f.symm.toAlgHom.comp f.toAlgHom = AlgHom.id A B := by
      ext x
      simp
    simpa only [he] using mapDifferentialsOfDPMorphism_id (A := A) (J := _) (delta := delta)
  have hFG : F.comp G = AddMonoidHom.id _ := by
    rw [mapDifferentialsOfDPMorphism_comp]
    have he : f.toAlgHom.comp f.symm.toAlgHom = AlgHom.id A C := by
      ext x
      simp
    simpa only [he] using mapDifferentialsOfDPMorphism_id (A := A) (J := _) (delta := epsilon)
  exact ⟨{ F with invFun := G
                  left_inv := DFunLike.congr_fun hGF
                  right_inv := DFunLike.congr_fun hFG }, rfl⟩

/-- Two additive maps out of the module of divided power differentials agree as soon as they agree
on the universal differentials and are semilinear over a common ring map. -/
public theorem differentials_hom_ext
    {C M : Type*} [CommRing C] [AddCommGroup M] [Module C M]
    (f : B →+* C) (F G : dividedPowerDifferentials (A := A) delta →+ M)
    (hF : ∀ b x, F (b • x) = f b • F x)
    (hG : ∀ b x, G (b • x) = f b • G x)
    (hd : ∀ b, F (dividedPowerDifferential (A := A) delta b) =
      G (dividedPowerDifferential (A := A) delta b)) : F = G :=
  differentials_hom_ext_aux (J := J) (delta := delta) f F G hF hG hd

/-- The quotient equivalence sends the class of a universal differential to the universal
differential of the class. -/
public theorem differentialsQuotientEquiv_mk
    (K : Ideal B) (hK : delta.IsSubDPIdeal K)
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)))
    (x : dividedPowerDifferentials (A := A) delta) :
    (differentialsQuotientEquiv (A := A) J delta K hK hd).val (Submodule.Quotient.mk x) =
      mapDifferentialsOfDPMorphism (J := _) (delta := delta) _ (Ideal.Quotient.mkₐ A K)
        (DividedPowers.Quotient.isDPMorphism delta
          (by simpa [inf_of_le_left hK.isSubideal] using hK)) x := by
  let E := (differentialsQuotientEquiv (A := A) J delta K hK hd).val
  apply DFunLike.congr_fun (differentials_hom_ext (J := _) (delta := delta) (Ideal.Quotient.mk K)
    (E.toAddMonoidHom.comp (K • (⊤ : Submodule B _)).mkQ.toAddMonoidHom) _ ?_ ?_ ?_) x
  · intro b x
    show E (Submodule.Quotient.mk (b • x)) = _
    rw [Submodule.Quotient.mk_smul, E.map_smul]
    exact (IsScalarTower.algebraMap_smul (B ⧸ K) b _).symm
  · intro b x
    exact mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta) _ _ _ b x
  · intro b
    show E _ = _
    exact ((differentialsQuotientEquiv (A := A) J delta K hK hd).property b).trans
      (mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := delta)
        _ (Ideal.Quotient.mkₐ A K) _ b).symm

/-- For a surjective divided power morphism whose kernel `K` satisfies the hypotheses above, the
divided power differentials of the target are the differentials of the source modulo `K`. -/
public noncomputable def differentialsSurjectionEquiv
    {C : Type*} [CommRing C] [Algebra A C] {L : Ideal C}
    (epsilon : DividedPowers L) (f : B →ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toRingHom)
    (hs : Function.Surjective f) (hJ : J.map f.toRingHom = L)
    (K : Ideal B) (hker : K = RingHom.ker f.toRingHom) (hKJ : K ≤ J)
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) :
    { E : (dividedPowerDifferentials (A := A) delta ⧸
        K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃+
        dividedPowerDifferentials (A := A) epsilon //
      ∀ x, E (Submodule.Quotient.mk x) =
        mapDifferentialsOfDPMorphism (J := _) (delta := delta) epsilon f hf x } := by
  have hK : delta.IsSubDPIdeal K := by
    have H := delta.isSubDPIdeal_ker epsilon hf
    change delta.IsSubDPIdeal (RingHom.ker f.toRingHom ⊓ J) at H
    simpa only [← hker, inf_of_le_left hKJ] using H
  let dq := DividedPowers.Quotient.dividedPowers delta (J := K)
    (by simpa [inf_of_le_left hKJ] using hK)
  let q : B →ₐ[A] B ⧸ K := Ideal.Quotient.mkₐ A K
  have hq : delta.IsDPMorphism dq q.toRingHom :=
    DividedPowers.Quotient.isDPMorphism delta _
  let e : (B ⧸ K) ≃ₐ[A] C := (Ideal.quotientEquivAlgOfEq A hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hs)
  have heq : e.toAlgHom.comp q = f := by
    ext b
    change (Ideal.quotientKerAlgEquivOfSurjective hs)
      (Ideal.quotientEquivAlgOfEq A hker (Ideal.Quotient.mk K b)) = f b
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hs b
  have he : dq.IsDPMorphism epsilon e.toAlgHom.toRingHom := by
    apply DividedPowers.IsDPMorphism.of_comp delta dq epsilon q.toRingHom
      e.toAlgHom.toRingHom rfl hq
    change delta.IsDPMorphism epsilon (e.toAlgHom.comp q).toRingHom
    rwa [heq]
  have heJ : (J.map (Ideal.Quotient.mk K)).map e.toAlgHom.toRingHom = L := by
    rw [Ideal.map_map]
    change J.map (e.toAlgHom.comp q).toRingHom = L
    rw [heq, hJ]
  let E := differentialsQuotientEquiv (A := A) J delta K hK hd
  let F := differentialsEquivOfAlgEquiv (J := _) (delta := dq) epsilon e he heJ
  refine ⟨E.val.toAddEquiv.trans F.val, ?_⟩
  intro x
  change F.val (E.val (Submodule.Quotient.mk x)) = _
  rw [differentialsQuotientEquiv_mk]
  change F.val.toAddMonoidHom _ = _
  rw [F.property]
  simpa only [heq, AddMonoidHom.comp_apply] using DFunLike.congr_fun
    (mapDifferentialsOfDPMorphism_comp (J := _) (delta := delta) dq epsilon q e.toAlgHom hq he) x

/-! ### The comparison of divided power differential forms in every degree -/

section Forms

variable {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}

/-- **The map induced on divided power differentials by a divided power morphism, bundled as a
semilinear map.**  `Crystalline.mapDifferentialsOfDPMorphism` is additive, and
`Crystalline.mapDifferentialsOfDPMorphism_smul` says that it carries `b · ω` to `f(b) · f(ω)`;
that is exactly semilinearity over the ring map underlying `f`, and the source and target are
modules over the two different rings `B` and `C`, so no stronger form is available. -/
public noncomputable def mapDifferentialsOfDPMorphismₛₗ
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) :
    dividedPowerDifferentials (A := A) delta →ₛₗ[f.toRingHom]
      dividedPowerDifferentials (A := A) epsilon where
  toFun := mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf
  map_add' := map_add _
  map_smul' b omega :=
    mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta) epsilon f hf b omega

/-- The bundled semilinear map `Crystalline.mapDifferentialsOfDPMorphismₛₗ` acts as
`Crystalline.mapDifferentialsOfDPMorphism`. -/
@[simp] public theorem mapDifferentialsOfDPMorphismₛₗ_apply
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
    (omega : dividedPowerDifferentials (A := A) delta) :
    mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := delta) epsilon f hf omega =
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf omega :=
  rfl

/-- **The comparison `Ωⁱ_{B/A,δ} → Ωⁱ_{C/A,ε}` of divided power differential forms in every
degree**, induced by a divided power morphism `f : (B, J, δ) → (C, K, ε)` over `A`.

The two exterior powers are taken over the two *different* rings `B` and `C`, so the comparison
is semilinear over `f` and not linear: it is `ExteriorAlgebra.powMapₛₗ` of the degree-one
comparison `Crystalline.mapDifferentialsOfDPMorphismₛₗ`.  Mathlib's `exteriorPower.map` is
functoriality in the module variable with the base ring held fixed and does not apply.

In degree one this is the degree-one comparison itself, up to `exteriorPower.oneEquiv`; in
degree zero it is `f` itself, up to `exteriorPower.zeroEquiv`. -/
public noncomputable def mapDifferentialFormsOfDPMorphism
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) (i : ℕ) :
    dividedPowerDifferentialForms (A := A) delta i →ₛₗ[f.toRingHom]
      dividedPowerDifferentialForms (A := A) epsilon i :=
  ExteriorAlgebra.powMapₛₗ i f.toRingHom
    (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := delta) epsilon f hf)

/-- The comparison of forms, read inside the exterior algebra, is `ExteriorAlgebra.mapₛₗ` of
the degree-one comparison. -/
@[simp] public theorem mapDifferentialFormsOfDPMorphism_coe
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf i x :
        ExteriorAlgebra C (dividedPowerDifferentials (A := A) epsilon)) =
      ExteriorAlgebra.mapₛₗ f.toRingHom
        (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := delta) epsilon f hf) x :=
  rfl

/-- **The comparison carries a wedge of one-forms to the wedge of their images.**  The wedges
span `Ωⁱ_{B/A,δ}`, so this equation determines the comparison; see
`Crystalline.mapDifferentialFormsOfDPMorphism_ext`. -/
@[simp] public theorem mapDifferentialFormsOfDPMorphism_ιMulti
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) (i : ℕ)
    (omega : Fin i → dividedPowerDifferentials (A := A) delta) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf i
        (exteriorPower.ιMulti B i omega) =
      exteriorPower.ιMulti C i fun j ↦
        mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf (omega j) :=
  ExteriorAlgebra.powMapₛₗ_ιMulti i f.toRingHom _ omega

/-- **The comparison carries `d b₁ ∧ ⋯ ∧ d bᵢ` to `d f(b₁) ∧ ⋯ ∧ d f(bᵢ)`.**  This is the
formula the comparison is used through: together with semilinearity it computes the comparison
on the standard generators `b₀ · d b₁ ∧ ⋯ ∧ d bᵢ` of the divided power de Rham complex. -/
public theorem mapDifferentialFormsOfDPMorphism_ιMulti_d
    (epsilon : DividedPowers K) (f : B →ₐ[A] C)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom) (i : ℕ) (b : Fin i → B) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf i
        (exteriorPower.ιMulti B i fun j ↦ dividedPowerDifferential (A := A) delta (b j)) =
      exteriorPower.ιMulti C i fun j ↦
        dividedPowerDifferential (A := A) epsilon (f (b j)) := by
  rw [mapDifferentialFormsOfDPMorphism_ιMulti]
  exact congrArg _ (funext fun j ↦ mapDifferentialsOfDPMorphism_d (A := A) (J := J)
    (delta := delta) epsilon f hf (b j))

/-- **The comparison is determined by its values on wedges**, those wedges spanning
`Ωⁱ_{B/A,δ}`. -/
public theorem mapDifferentialFormsOfDPMorphism_ext
    (epsilon : DividedPowers K) (f : B →ₐ[A] C) (i : ℕ)
    {F G : dividedPowerDifferentialForms (A := A) delta i →ₛₗ[f.toRingHom]
      dividedPowerDifferentialForms (A := A) epsilon i}
    (h : ∀ omega : Fin i → dividedPowerDifferentials (A := A) delta,
      F (exteriorPower.ιMulti B i omega) = G (exteriorPower.ιMulti B i omega)) : F = G :=
  ExteriorAlgebra.powMapₛₗ_ext h

/-- The comparison of forms induced by the identity divided power morphism is the identity. -/
public theorem mapDifferentialFormsOfDPMorphism_id (i : ℕ)
    (hid : DividedPowers.IsDPMorphism delta delta (AlgHom.id A B).toRingHom)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) delta
      (AlgHom.id A B) hid i x = x := by
  refine ExteriorAlgebra.powMapₛₗ_eq_self i _ (fun _ ↦ rfl) (fun omega ↦ ?_) x
  exact DFunLike.congr_fun
    (mapDifferentialsOfDPMorphism_id (A := A) (J := J) (delta := delta)) omega

/-- The comparisons of forms induced by two composable divided power morphisms compose. -/
public theorem mapDifferentialFormsOfDPMorphism_comp
    {D : Type*} [CommRing D] [Algebra A D] {L : Ideal D}
    (epsilon : DividedPowers K) (zeta : DividedPowers L)
    (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
    (hg : DividedPowers.IsDPMorphism epsilon zeta g.toRingHom)
    (hgf : DividedPowers.IsDPMorphism delta zeta (g.comp f).toRingHom) (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) zeta (g.comp f) hgf i x =
      mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := epsilon) zeta g hg i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          epsilon f hf i x) := by
  refine ExteriorAlgebra.powMapₛₗ_eq_comp i _ _ _ (fun _ ↦ rfl) (fun omega ↦ ?_) x
  exact (DFunLike.congr_fun (mapDifferentialsOfDPMorphism_comp (A := A) (J := J) (delta := delta)
    epsilon zeta f g hf hg) omega).symm

end Forms

end Crystalline

end
