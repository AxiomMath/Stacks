module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Galois groups of separable closures

The absolute Galois group of a field does not depend, up to isomorphism of topological groups,
on the separable closure used to define it, nor on the field up to isomorphism: if `e : k ≃+* k'`
is an isomorphism of fields and `E`, `E'` are separable closures of `k` and `k'`, then `e` extends
to an isomorphism `E ≃+* E'`, and conjugation by it is an isomorphism of topological groups
`Gal(E/k) ≃ₜ* Gal(E'/k')` for the Krull topologies.

A closed subgroup `H` of `Gal(E/k)`, for a Galois extension `E/k`, is the Galois group of `E` over
the fixed field of `H`, again as a topological group.

Both statements rest on a continuity criterion: a homomorphism from a topological group into a
Galois group is continuous as soon as the stabilizer of every element is a neighbourhood of the
identity.

## Main definitions

* `IsSepClosure.galContinuousMulEquiv`: `Gal(E/k) ≃ₜ* Gal(E'/k')` for separable closures `E`,
  `E'` of isomorphic fields `k`, `k'`.
* `InfiniteGalois.fixedFieldGalContinuousMulEquiv`: `Gal(E / Eᴴ) ≃ₜ* H` for a closed subgroup `H`
  of the Galois group of a Galois extension.

## Main results

* `continuous_of_stabilizer_mem_nhds_one`: the continuity criterion.
* `stabilizer_mem_nhds_one`: in an algebraic extension, stabilizers of elements are open.
-/

@[expose] public noncomputable section

open IntermediateField Topology

/-- In an algebraic extension, the stabilizer of an element is a neighbourhood of the identity
for the Krull topology: it contains the fixing subgroup of the finite subextension the element
generates. -/
theorem stabilizer_mem_nhds_one {k E : Type*} [Field k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] (y : E) : {σ : Gal(E/k) | σ y = y} ∈ 𝓝 1 := by
  have : FiniteDimensional k k⟮y⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  exact Filter.mem_of_superset ((fixingSubgroup_isOpen k⟮y⟯).mem_nhds (one_mem _))
    fun σ hσ ↦ (mem_fixingSubgroup_iff _ σ).mp hσ y (mem_adjoin_simple_self k y)

/-- **Continuity criterion for homomorphisms into a Galois group.** A homomorphism from a
topological group into the Galois group of a field extension, with the Krull topology, is
continuous as soon as the stabilizer of every element of the extension is a neighbourhood of
the identity. -/
theorem continuous_of_stabilizer_mem_nhds_one {k E : Type*} [Field k] [Field E] [Algebra k E]
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (f : Γ →* Gal(E/k))
    (hf : ∀ x : E, {g : Γ | f g x = x} ∈ 𝓝 1) : Continuous f := by
  refine continuous_of_continuousAt_one f fun s hs ↦ ?_
  rw [map_one] at hs
  change f ⁻¹' s ∈ 𝓝 1
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff k E s).mp hs
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := k) (M := M)
  have hsub : (⋂ i, {g : Γ | f g (b i : E) = b i}) ⊆ f ⁻¹' s := by
    intro g hg
    apply hMs
    have key : ∀ y ∈ Submodule.span k (Set.range b), f g (y : E) = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Set.mem_iInter.mp hg i
      | zero => simp
      | add y z _ _ hy hz =>
        push_cast
        rw [map_add, hy, hz]
      | smul c y _ hy =>
        push_cast
        rw [map_smul, hy]
    exact (mem_fixingSubgroup_iff M (f g)).mpr fun x hx ↦ key ⟨x, hx⟩ (hb ▸ Submodule.mem_top)
  exact Filter.mem_of_superset (Filter.iInter_mem.2 fun _ ↦ hf _) hsub

/-- A homomorphism between Galois groups is continuous as soon as, for every `x`, some element `y`
of the source extension has a stabilizer contained in that of `x`. -/
private theorem continuous_of_forall_exists_fixing {k₁ E₁ k₂ E₂ : Type*} [Field k₁] [Field E₁]
    [Field k₂] [Field E₂] [Algebra k₁ E₁] [Algebra k₂ E₂] [Algebra.IsAlgebraic k₁ E₁]
    (f : Gal(E₁/k₁) →* Gal(E₂/k₂))
    (hf : ∀ x : E₂, ∃ y : E₁, ∀ σ : Gal(E₁/k₁), σ y = y → f σ x = x) : Continuous f :=
  continuous_of_stabilizer_mem_nhds_one f fun x ↦
    let ⟨y, hy⟩ := hf x
    Filter.mem_of_superset (stabilizer_mem_nhds_one y) hy

namespace IsSepClosure

variable {k k' : Type*} (E E' : Type*) [Field k] [Field k'] [Field E] [Field E'] [Algebra k E]
  [Algebra k' E'] [IsSepClosure k E] [IsSepClosure k' E'] (e : k ≃+* k')

/-- The structure of `k`-algebra on `E'` obtained through `e : k ≃+* k'`. -/
abbrev algebraOfRingEquiv : Algebra k E' := ((algebraMap k' E').comp e.toRingHom).toAlgebra

/-- With the `k`-algebra structure `algebraOfRingEquiv E' e`, `E'` is a separable closure of
`k`. -/
lemma isSepClosure_algebraOfRingEquiv :
    letI := algebraOfRingEquiv E' e
    IsSepClosure k E' := by
  let := algebraOfRingEquiv E' e
  exact ⟨IsSepClosure.sep_closed k', Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl E')
    (by ext x; simp [RingHom.algebraMap_toAlgebra])⟩

/-- The extension of `e : k ≃+* k'` to separable closures. -/
def ringEquivOfRingEquiv : E ≃+* E' :=
  letI := algebraOfRingEquiv E' e
  haveI := isSepClosure_algebraOfRingEquiv E' e
  (IsSepClosure.equiv k E E').toRingEquiv

/-- `ringEquivOfRingEquiv E E' e` extends `e`: it sends the image of `a : k` in `E` to the image
of `e a` in `E'`. -/
lemma ringEquivOfRingEquiv_algebraMap (a : k) :
    ringEquivOfRingEquiv E E' e (algebraMap k E a) = algebraMap k' E' (e a) := by
  let := algebraOfRingEquiv E' e
  have := isSepClosure_algebraOfRingEquiv E' e
  exact (IsSepClosure.equiv k E E').commutes a

/-- Conjugation by the extension of `e`, as an isomorphism of Galois groups. -/
def galMulEquiv : Gal(E/k) ≃* Gal(E'/k') where
  toFun σ := AlgEquiv.ofRingEquiv (f := (ringEquivOfRingEquiv E E' e).symm.trans
      (σ.toRingEquiv.trans (ringEquivOfRingEquiv E E' e))) fun b ↦ by
    obtain ⟨a, rfl⟩ := e.surjective b
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    rw [← ringEquivOfRingEquiv_algebraMap E E' e, RingEquiv.symm_apply_apply,
      AlgEquiv.commutes, ringEquivOfRingEquiv_algebraMap E E' e]
  invFun τ := AlgEquiv.ofRingEquiv (f := (ringEquivOfRingEquiv E E' e).trans
      (τ.toRingEquiv.trans (ringEquivOfRingEquiv E E' e).symm)) fun a ↦ by
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    rw [ringEquivOfRingEquiv_algebraMap E E' e, AlgEquiv.commutes,
      ← ringEquivOfRingEquiv_algebraMap E E' e, RingEquiv.symm_apply_apply]
  left_inv σ := by
    ext x
    simp
  right_inv τ := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp

/-- `galMulEquiv E E' e σ` is the conjugate of `σ` by `ringEquivOfRingEquiv E E' e`. -/
lemma galMulEquiv_apply (σ : Gal(E/k)) (x : E') :
    galMulEquiv E E' e σ x =
      ringEquivOfRingEquiv E E' e (σ ((ringEquivOfRingEquiv E E' e).symm x)) := rfl

/-- `galMulEquiv E E' e` is continuous for the Krull topologies. -/
lemma continuous_galMulEquiv : Continuous (galMulEquiv E E' e) := by
  refine continuous_of_forall_exists_fixing (galMulEquiv E E' e).toMonoidHom fun x ↦
    ⟨(ringEquivOfRingEquiv E E' e).symm x, fun σ hσ ↦ ?_⟩
  change galMulEquiv E E' e σ x = x
  rw [galMulEquiv_apply, hσ, RingEquiv.apply_symm_apply]

/-- The inverse of `galMulEquiv E E' e` is continuous for the Krull topologies. -/
lemma continuous_galMulEquiv_symm : Continuous (galMulEquiv E E' e).symm := by
  refine continuous_of_forall_exists_fixing (galMulEquiv E E' e).symm.toMonoidHom fun x ↦
    ⟨ringEquivOfRingEquiv E E' e x, fun τ hτ ↦ ?_⟩
  change (ringEquivOfRingEquiv E E' e).symm (τ (ringEquivOfRingEquiv E E' e x)) = x
  rw [hτ, RingEquiv.symm_apply_apply]

/-- **The absolute Galois group does not depend on the separable closure.** For an isomorphism
of fields `e : k ≃+* k'` and separable closures `E` of `k` and `E'` of `k'`, conjugation by an
extension of `e` to `E ≃+* E'` is an isomorphism of topological groups for the Krull
topologies. -/
def galContinuousMulEquiv : Gal(E/k) ≃ₜ* Gal(E'/k') :=
  { galMulEquiv E E' e with
    continuous_toFun := continuous_galMulEquiv E E' e
    continuous_invFun := continuous_galMulEquiv_symm E E' e }

end IsSepClosure

namespace InfiniteGalois

variable {k E : Type*} [Field k] [Field E] [Algebra k E] [IsGalois k E]
  (H : ClosedSubgroup Gal(E/k))

/-- The Galois group of `E` over the fixed field of a closed subgroup `H`, identified with `H`. -/
def fixedFieldGalMulEquiv : Gal(E/fixedField H.toSubgroup) ≃* H.toSubgroup :=
  (fixingSubgroupEquiv (fixedField H.toSubgroup)).symm.trans
    (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H))

/-- The image of `σ` under `fixedFieldGalMulEquiv H` acts on `E` as `σ` does. -/
lemma fixedFieldGalMulEquiv_apply (σ : Gal(E/fixedField H.toSubgroup)) (x : E) :
    (fixedFieldGalMulEquiv H σ : Gal(E/k)) x = σ x := rfl

/-- `fixedFieldGalMulEquiv H` is continuous for the Krull topologies. -/
lemma continuous_fixedFieldGalMulEquiv : Continuous (fixedFieldGalMulEquiv H) := by
  have : Algebra.IsAlgebraic (fixedField H.toSubgroup) E :=
    Algebra.IsAlgebraic.tower_top (K := k) (fixedField H.toSubgroup)
  exact Continuous.subtype_mk (continuous_of_forall_exists_fixing
    (H.toSubgroup.subtype.comp (fixedFieldGalMulEquiv H).toMonoidHom) fun x ↦ ⟨x, fun _ h ↦ h⟩) _

/-- **The Galois group over the fixed field of a closed subgroup is that subgroup**, as a
topological group: for a Galois extension `E/k` and a closed subgroup `H` of `Gal(E/k)`, the map
`Gal(E / Eᴴ) → H` is an isomorphism of topological groups. -/
def fixedFieldGalContinuousMulEquiv : Gal(E/fixedField H.toSubgroup) ≃ₜ* H.toSubgroup :=
  haveI : IsGalois (fixedField H.toSubgroup) E :=
    IsGalois.tower_top_of_isGalois k (fixedField H.toSubgroup) E
  let h := (continuous_fixedFieldGalMulEquiv H).homeoOfEquivCompactToT2
    (f := (fixedFieldGalMulEquiv H).toEquiv)
  { fixedFieldGalMulEquiv H with
    continuous_toFun := h.continuous
    continuous_invFun := h.symm.continuous }

end InfiniteGalois

end
