module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.DualNumberLift
public import StacksFrontier.Deformation.Examples.Linear.FiniteProjectiveRimSchlessinger
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.LiftsOfObjects.IdentityLifts
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# Infinitesimal automorphisms of the deformations of a finite-dimensional vector space

Let `V` be a finite-dimensional vector space over `k`. Its deformations form a deformation
category, and the infinitesimal automorphism group of that category — the automorphisms of a
lift of the trivial object to the dual numbers that become the identity after reduction — is
the additive group `Module.End k V` of linear endomorphisms of `V`.

The mechanism is the formula `γ(m) = m + ε·n`. A deformation `M` of `V` over an object `Aε`
identified with the dual numbers is a finite projective `k[ε]`-module with `M ⊗ k ≃ V`, that is
a `Deformation.Examples.DualNumberLift`. An automorphism of `M` inducing the identity on `V`
differs from the identity by a map killed by `ε`, so it factors through the reduction and is
read as an endomorphism `ψ` of `V` by `reduction n = ψ (reduction m)`. Composition of
automorphisms adds the corresponding endomorphisms, which is why the multiplicative group is
`Multiplicative (Module.End k V)`.

## Main results

* `Deformation.Examples.FiniteProjectiveModule.infinitesimalAutomorphismsEquivEnd`: the
  infinitesimal automorphism group of the deformations of `V` is `Module.End k V`, by a
  multiplicative isomorphism pinned by the formula `γ(m) = m + ε·n` above.
* `Deformation.Examples.FiniteProjectiveModule.nonempty_infinitesimalAutomorphismsEquivEnd`:
  the existence statement from which the chosen isomorphism is read off.
* `Deformation.Examples.FiniteProjectiveModule.exists_infinitesimalAutomorphismsLinearEquivEnd`:
  that group is `Module.End k V` as a `k`-vector space, and is finite-dimensional.

## Implementation notes

The isomorphism is specified, not merely asserted: the subtype in the statement carries the
pointwise formula relating an automorphism to its endomorphism, which is what makes the
identification canonical. Existence is proved first and the isomorphism is then chosen, so the
construction can be stated at an arbitrary chosen pushforward to the dual numbers rather than
at a preferred one.

The object `Aε` of `𝒞_Λ` is only *isomorphic* to the dual numbers, through the `iε` supplied by
`Deformation.IsCanonicalDualNumberPair`. That isomorphism is not canonical: it may twist the
coefficient field by an automorphism of `k` over `Λ`. `normalizedDualNumberEquiv` corrects it by
the induced automorphism of the residue field, producing the unique identification under which
the morphism down to the special fibre becomes the dual-number projection
`TrivSqZeroExt.fstHom`. It fixes `iε.symm DualNumber.eps`, which is why the statement's `ε` may
be written with the uncorrected `iε`.

Stacks 93.4 also computes the tangent space of this deformation category, which is
`Deformation.Examples.FiniteProjectiveModule.subsingleton_tangentSpace`.

The `k`-vector space structure the lemma asserts on the infinitesimal automorphisms is the one
Tag 06JV puts on the tangent space of the automorphism functor: addition is composition of
automorphisms, and scalar multiplication by `c` is induced by the dual-number scaling
`ε ↦ c·ε`. Nothing on this branch realizes the general construction of 06JV, so the structure
is here obtained by transport along the identification above and then *pinned*, which is what
makes the transport legitimate: `exists_infinitesimalAutomorphismsLinearEquivEnd` states that
its addition is the composition of automorphisms, and that its scalar multiplication satisfies
`(c · γ)(m) = m + ε·(cb·n)` whenever `γ(m) = m + ε·n` and `cb` is any element of the base
reducing to `c`. Scaling the infinitesimal coordinate of `k[ε]` has exactly that effect on
`γ = id + ε·ψ`, namely `ψ ↦ c·ψ`, so the two readings agree. The conclusion is pinned and not
merely asserted because `ε·n` depends on `n` only through its reduction, so the displayed
formula determines the scaled automorphism.

## References

* [Stacks Project, Tag 0DVQ](https://stacks.math.columbia.edu/tag/0DVQ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveModule

universe u v w t

private lemma dualNumber_fstHom_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    Function.Surjective (TrivSqZeroExt.fstHom Λ k k : DualNumber k →ₐ[Λ] k) :=
  fun a => ⟨algebraMap k (DualNumber k) a, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩

/-- The residue field of the dual numbers is `k`, identified through the projection. -/
private noncomputable def dualNumberResidueEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    IsLocalRing.ResidueField (DualNumber k) ≃ₐ[Λ] k :=
  residueEquivOfAugmentation (TrivSqZeroExt.fstHom Λ k k) dualNumber_fstHom_surjective

/-- The automorphism of `k` by which an identification of `A` with the dual numbers twists
the residue field: the composite of the residue identification of `A` with the one induced
on the dual numbers. -/
private noncomputable def dualNumberResidueCoordinate
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (i : A ≃ₐ[Λ] DualNumber k) : k ≃ₐ[Λ] k :=
  A.residueEquiv.symm.trans ((IsLocalRing.ResidueField.mapAlgEquiv i).trans
    dualNumberResidueEquiv)

/-- The coefficientwise twist fixes `ε`. -/
private lemma dualNumberCoefficientEquiv_eps
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) :
    dualNumberCoefficientEquiv σ (DualNumber.eps : DualNumber k) = DualNumber.eps := by
  apply TrivSqZeroExt.ext <;>
    simp [dualNumberCoefficientEquiv_fst, dualNumberCoefficientEquiv_snd]

private lemma dualNumberCoefficientEquiv_symm_symm_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (d : DualNumber k) :
    (dualNumberCoefficientEquiv σ.symm).symm d = dualNumberCoefficientEquiv σ d := by
  apply (dualNumberCoefficientEquiv σ.symm).injective
  rw [AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext <;>
    simp [dualNumberCoefficientEquiv_fst, dualNumberCoefficientEquiv_snd]

/-- An identification of `A` with the dual numbers, corrected by
`dualNumberResidueCoordinate` so that it is compatible with the residue identifications. -/
private noncomputable def normalizedDualNumberEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (i : A ≃ₐ[Λ] DualNumber k) : A ≃ₐ[Λ] DualNumber k :=
  i.trans (dualNumberCoefficientEquiv (dualNumberResidueCoordinate A i).symm)

/-- Normalizing does not move the infinitesimal element: it sends `i.symm ε` to `ε`. -/
private lemma normalizedDualNumberEquiv_eps
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (i : A ≃ₐ[Λ] DualNumber k) :
    normalizedDualNumberEquiv i (i.symm DualNumber.eps) = DualNumber.eps := by
  simp only [normalizedDualNumberEquiv, AlgEquiv.trans_apply, i.apply_symm_apply]
  exact dualNumberCoefficientEquiv_eps _

/-- Read through the normalized identification, a morphism from `A` down to the
residue-field object `k` is exactly the dual-number projection. This is the property that
pins the normalization, and it is why the statement may spell `ε` with the uncorrected
identification. -/
private lemma normalizedDualNumberEquiv_reductionHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (f : A ⟶ residueFieldBase Λ k)
    (i : A ≃ₐ[Λ] DualNumber k) :
    f.hom.comp (normalizedDualNumberEquiv i).symm.toAlgHom =
      TrivSqZeroExt.fstHom Λ k k := by
  apply AlgHom.ext
  intro d
  let σ := dualNumberResidueCoordinate A i
  let α := dualNumberCoefficientEquiv σ.symm
  let j := i.trans α
  have hres : A.residueEquiv (IsLocalRing.residue A (j.symm d)) =
      dualNumberResidueEquiv (Λ := Λ) (k := k)
        (IsLocalRing.residue (DualNumber k) d) := by
    apply σ.injective
    calc
      σ (A.residueEquiv (IsLocalRing.residue A (j.symm d))) =
          dualNumberResidueEquiv (Λ := Λ) (k := k)
            (IsLocalRing.residue (DualNumber k) (i (j.symm d))) := by
            simp only [σ, dualNumberResidueCoordinate, AlgEquiv.trans_apply,
              AlgEquiv.symm_apply_apply,
              IsLocalRing.ResidueField.mapAlgEquiv_residue]
      _ = σ (dualNumberResidueEquiv (Λ := Λ) (k := k)
            (IsLocalRing.residue (DualNumber k) d)) := by
            have hij : i (j.symm d) = α.symm d := by simp [j]
            rw [hij]
            change (α.symm d).fst = σ d.fst
            rw [dualNumberCoefficientEquiv_symm_symm_apply]
            exact dualNumberCoefficientEquiv_fst σ d
  have hf := f.residue_comm (j.symm d)
  rw [residueFieldBase_residueEquiv_residue Λ k (f.hom (j.symm d)), hres] at hf
  calc
    f.hom (j.symm d) = dualNumberResidueEquiv (Λ := Λ) (k := k)
        (IsLocalRing.residue (DualNumber k) d) := hf
    _ = TrivSqZeroExt.fst d := by
      simp [dualNumberResidueEquiv]

/-- Pointwise form of `normalizedDualNumberEquiv_reductionHom`. -/
private lemma normalizedDualNumberEquiv_symm_compat
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (f : A ⟶ residueFieldBase Λ k)
    (i : A ≃ₐ[Λ] DualNumber k) (d : DualNumber k) :
    f.hom ((normalizedDualNumberEquiv i).symm d) = (TrivSqZeroExt.fstHom k k k).toRingHom d :=
  congrArg (fun F : DualNumber k →ₐ[Λ] k => F d) (normalizedDualNumberEquiv_reductionHom A f i)

/-- The normalized identification sends `ε` back to the same element as `i`. -/
private lemma normalizedDualNumberEquiv_symm_eps
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (i : A ≃ₐ[Λ] DualNumber k) :
    (normalizedDualNumberEquiv i).symm DualNumber.eps = i.symm DualNumber.eps := by
  apply (normalizedDualNumberEquiv i).injective
  rw [AlgEquiv.apply_symm_apply, normalizedDualNumberEquiv_eps]

/-- An element of a lift reduces to zero exactly when it is `ε` times another element. -/
private lemma dualNumberLift_reduction_eq_zero_iff
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (m : X.carrier) :
    X.reduction m = 0 ↔
      ∃ n : X.carrier, (DualNumber.eps : DualNumber k) • n = m := by
  refine ⟨fun hm => ?_, ?_⟩
  · have hmem := DualNumberLift.reduction_kernel_mem X m hm
    rw [DualNumberLift.dualKernel_eq_span] at hmem
    apply Submodule.smul_induction_on
      (p := fun z => ∃ n : X.carrier,
        (DualNumber.eps : DualNumber k) • n = z) hmem
    · intro r hr x hx
      obtain ⟨b, hb⟩ : (DualNumber.eps : DualNumber k) ∣ r := by
        simpa [Ideal.mem_span_singleton] using hr
      exact ⟨b • x, by rw [hb, mul_smul]⟩
    · intro x y hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [smul_add]⟩
  · rintro ⟨n, rfl⟩
    simpa [DualNumberLift.dualProjection] using X.reduction.map_smul'
      (DualNumber.eps : DualNumber k) n

/-- Multiplication by `ε` kills an element of a lift exactly when that element reduces to
zero. A lift is free over `k[ε]` because `k[ε]` is local, so this is the coordinatewise
annihilator computation. -/
private lemma dualNumberLift_eps_smul_eq_zero_iff
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (m : X.carrier) :
    (DualNumber.eps : DualNumber k) • m = 0 ↔ X.reduction m = 0 := by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · let : Module.Free (DualNumber k) X.carrier :=
      Module.free_of_flat_of_isLocalRing
    classical
    let b := Module.Free.chooseBasis (DualNumber k) X.carrier
    have hcoord : (DualNumber.eps : DualNumber k) • b.repr m = 0 := by
      simpa only [map_smul, map_zero] using congrArg b.repr hm
    have hfst (i : Module.Free.ChooseBasisIndex (DualNumber k) X.carrier) :
        (b.repr m i).fst = 0 := by
      have hi := congrArg TrivSqZeroExt.snd (congrArg (fun f => f i) hcoord)
      simpa [DualNumber.snd_mul] using hi
    let c : Module.Free.ChooseBasisIndex (DualNumber k) X.carrier → DualNumber k :=
      fun i => Classical.choose (DualNumber.fst_eq_zero_iff_eps_dvd.mp (hfst i))
    have hc (i : Module.Free.ChooseBasisIndex (DualNumber k) X.carrier) :
        (DualNumber.eps : DualNumber k) * c i = b.repr m i :=
      (Classical.choose_spec (DualNumber.fst_eq_zero_iff_eps_dvd.mp (hfst i))).symm
    let : Fintype (Module.Free.ChooseBasisIndex (DualNumber k) X.carrier) :=
      Fintype.ofFinite _
    let z : Module.Free.ChooseBasisIndex (DualNumber k) X.carrier →₀ DualNumber k :=
      Finsupp.equivFunOnFinite.symm c
    have hz : b.repr m = (DualNumber.eps : DualNumber k) • z :=
      Finsupp.ext fun i => (hc i).symm
    have hm' : m = (DualNumber.eps : DualNumber k) • b.repr.symm z := by
      apply b.repr.injective
      simpa only [map_smul, b.repr.apply_symm_apply] using hz
    exact (dualNumberLift_reduction_eq_zero_iff X m).2 ⟨b.repr.symm z, hm'.symm⟩
  · obtain ⟨n, hn⟩ := dualNumberLift_reduction_eq_zero_iff X m |>.mp hm
    rw [← hn, smul_smul, DualNumber.eps_mul_eps, zero_smul]

/-- If `e` kills exactly the kernel of an additive map `r`, then `e •` identifies elements
with the same image under `r`. -/
private lemma smul_eq_smul_of_map_eq
    {R : Type*} {M N F : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] (e : R) (r : F)
    (hz : ∀ z, e • z = 0 ↔ r z = 0) {a b : M} (h : r a = r b) : e • a = e • b := by
  rw [← sub_eq_zero, ← smul_sub, hz, map_sub, h, sub_self]

/-- An automorphism of a lift inducing the identity on the special fibre has the form
`m ↦ m + ε · n`, where the reduction of `n` is a fixed endomorphism of `V` applied to the
reduction of `m`. That endomorphism is what the main identification assigns to the
automorphism; it exists because `ε` annihilates the difference from the identity, so the
difference factors through the reduction. -/
private lemma dualNumberLift_exists_endomorphism
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (f : X.carrier ≃ₗ[DualNumber k] X.carrier)
    (hred : ∀ m, X.reduction (f m) = X.reduction m) :
    ∃ ψ : Module.End k V, ∀ m : X.carrier, ∃ n : X.carrier,
      X.reduction n = ψ (X.reduction m) ∧
      f m = m + (DualNumber.eps : DualNumber k) • n := by
  classical
  let N : X.carrier →ₗ[DualNumber k] X.carrier :=
    f.toLinearMap - LinearMap.id
  let epsMap : X.carrier →ₗ[DualNumber k] X.carrier := {
    toFun := fun m => (DualNumber.eps : DualNumber k) • m
    map_add' := fun x y => smul_add _ _ _
    map_smul' := by
      intro r m
      simp [smul_smul, mul_comm] }
  have hNrange (m : X.carrier) : N m ∈ LinearMap.range epsMap := by
    have hzero : X.reduction (N m) = 0 := by
      change X.reduction (f m - m) = 0
      rw [map_sub, hred m, sub_self]
    exact (dualNumberLift_reduction_eq_zero_iff X (N m)).mp hzero
  let N' : X.carrier →ₗ[DualNumber k] LinearMap.range epsMap :=
    N.codRestrict _ hNrange
  let p : X.carrier →ₗ[DualNumber k] LinearMap.range epsMap := epsMap.rangeRestrict
  have hp : Function.Surjective p := fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩
  obtain ⟨q, hq'⟩ := Module.projective_lifting_property p N' hp
  have hq (m : X.carrier) :
      (DualNumber.eps : DualNumber k) • q m = N m :=
    congrArg Subtype.val (LinearMap.congr_fun hq' m)
  let : Module k X.carrier :=
    Module.compHom X.carrier (TrivSqZeroExt.inlAlgHom k k k).toRingHom
  let ρ : X.carrier →ₗ[k] V := {
    toFun := X.reduction
    map_add' := X.reduction.map_add
    map_smul' := by
      intro a m
      change X.reduction (TrivSqZeroExt.inlAlgHom k k k a • m) = _
      simpa [DualNumberLift.dualProjection] using
        X.reduction.map_smul' (TrivSqZeroExt.inlAlgHom k k k a) m }
  let qₖ : X.carrier →ₗ[k] X.carrier := {
    toFun := q
    map_add' := q.map_add
    map_smul' := by
      intro a m
      exact q.map_smul (TrivSqZeroExt.inlAlgHom k k k a) m }
  let f₀ : X.carrier →ₗ[k] V := ρ.comp qₖ
  have hker : LinearMap.ker ρ ≤ LinearMap.ker f₀ := by
    intro m hm
    obtain ⟨n, rfl⟩ := dualNumberLift_reduction_eq_zero_iff X m |>.mp hm
    change X.reduction (q ((DualNumber.eps : DualNumber k) • n)) = 0
    apply (dualNumberLift_eps_smul_eq_zero_iff X _).mp
    rw [hq, map_smul, ← hq n, smul_smul, DualNumber.eps_mul_eps, zero_smul]
  have hρ : Function.Surjective ρ := DualNumberLift.reduction_surjective X
  let E := ρ.quotKerEquivOfSurjective hρ
  let ψ : Module.End k V :=
    (LinearMap.ker ρ).liftQ f₀ hker |>.comp E.symm.toLinearMap
  refine ⟨ψ, fun m => ⟨q m, ?_, ?_⟩⟩
  · change ρ (q m) = ψ (ρ m)
    simp [ψ, E]
    rfl
  · have h : (DualNumber.eps : DualNumber k) • q m = f m - m := hq m
    rw [h]
    abel

/-- Conversely every endomorphism of `V` arises from an automorphism of the lift by the
formula `m ↦ m + ε · n`: lift the endomorphism along the surjective reduction and add
`ε` times the result to the identity. -/
@[sga "3 II 4.5.1" "special case"]
private lemma dualNumberLift_exists_linearEquiv_of_end
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (ψ : Module.End k V) :
    ∃ f : X.carrier ≃ₗ[DualNumber k] X.carrier,
      (∀ m, X.reduction (f m) = X.reduction m) ∧
      ∀ m, ∃ n, X.reduction n = ψ (X.reduction m) ∧
        f m = m + (DualNumber.eps : DualNumber k) • n := by
  classical
  let : Module k X.carrier :=
    Module.compHom X.carrier (TrivSqZeroExt.inlAlgHom k k k).toRingHom
  let : Module (DualNumber k) V :=
    Module.compHom V (DualNumberLift.dualProjection k).toRingHom
  let ρ : X.carrier →ₗ[DualNumber k] V := {
    toFun := X.reduction
    map_add' := X.reduction.map_add
    map_smul' := X.reduction.map_smul' }
  let σ : V →ₗ[DualNumber k] V := {
    toFun := ψ
    map_add' := ψ.map_add
    map_smul' := by
      intro r v
      change ψ ((DualNumberLift.dualProjection k).toRingHom r • v) = _
      exact ψ.map_smul _ _ }
  obtain ⟨q, hq⟩ := Module.projective_lifting_property ρ (σ.comp ρ)
    (DualNumberLift.reduction_surjective X)
  let T : X.carrier →ₗ[DualNumber k] X.carrier :=
    (LinearMap.lsmul (DualNumber k) X.carrier (DualNumber.eps : DualNumber k)).comp q
  have hT2 : T.comp T = 0 := by
    ext m
    change (DualNumber.eps : DualNumber k) • q
      ((DualNumber.eps : DualNumber k) • q m) = 0
    rw [q.map_smul, smul_smul, DualNumber.eps_mul_eps, zero_smul]
  let A : X.carrier →ₗ[DualNumber k] X.carrier := LinearMap.id + T
  let B : X.carrier →ₗ[DualNumber k] X.carrier := LinearMap.id - T
  have hTT (m : X.carrier) : T (T m) = 0 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hT2 m
  have hBA : B.comp A = LinearMap.id := by
    ext m
    change (m + T m) - T (m + T m) = m
    rw [map_add, hTT]
    abel
  have hAB : A.comp B = LinearMap.id := by
    ext m
    change (m - T m) + T (m - T m) = m
    rw [map_sub, hTT]
    abel
  let f : X.carrier ≃ₗ[DualNumber k] X.carrier := LinearEquiv.ofLinear A B hAB hBA
  refine ⟨f, fun m => ?_, fun m => ⟨q m, ?_, ?_⟩⟩
  · have hρT (m : X.carrier) : X.reduction (T m) = 0 :=
      (dualNumberLift_reduction_eq_zero_iff X _).mpr ⟨q m, rfl⟩
    change X.reduction (m + T m) = X.reduction m
    rw [map_add, hρT, add_zero]
  · change ρ (q m) = ψ (ρ m)
    simpa [ρ, σ, LinearMap.comp_apply] using
      congrArg (fun F : X.carrier →ₗ[DualNumber k] V => F m) hq
  · change A m = m + (DualNumber.eps : DualNumber k) • q m
    simp [A, T, LinearMap.comp_apply, LinearMap.lsmul_apply]

/-- The endomorphism of `V` attached to an automorphism of a lift by the formula
`m ↦ m + ε · n` is unique. -/
private lemma dualNumberLift_endomorphism_unique
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (f : X.carrier ≃ₗ[DualNumber k] X.carrier)
    (ψ η : Module.End k V)
    (hψ : ∀ m, ∃ n, X.reduction n = ψ (X.reduction m) ∧
      f m = m + (DualNumber.eps : DualNumber k) • n)
    (hη : ∀ m, ∃ n, X.reduction n = η (X.reduction m) ∧
      f m = m + (DualNumber.eps : DualNumber k) • n) :
    ψ = η := by
  classical
  ext v
  obtain ⟨m, hm⟩ := DualNumberLift.reduction_surjective X v
  obtain ⟨nψ, hrψ, hfψ⟩ := hψ m
  obtain ⟨nη, hrη, hfη⟩ := hη m
  have heq : (DualNumber.eps : DualNumber k) • nψ =
      (DualNumber.eps : DualNumber k) • nη :=
    add_left_cancel (hfψ.symm.trans hfη)
  have hzero : (DualNumber.eps : DualNumber k) • (nψ - nη) = 0 := by
    rw [smul_sub, heq, sub_self]
  have hred := (dualNumberLift_eps_smul_eq_zero_iff X (nψ - nη)).mp hzero
  have hcoeff : ψ (X.reduction m) = η (X.reduction m) := by
    rw [map_sub, hrψ, hrη] at hred
    exact sub_eq_zero.mp hred
  simpa only [hm] using hcoeff

/-- Automorphisms of a lift inducing the identity on the special fibre correspond
bijectively to endomorphisms of `V`. -/
@[sga "3 II 4.5.1" "special case"]
private noncomputable def dualNumberLift_endEquivOfReductionIdentity
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V) :
    {f : X.carrier ≃ₗ[DualNumber k] X.carrier //
      ∀ m, X.reduction (f m) = X.reduction m} ≃ Module.End k V := by
  classical
  let F := fun (f : {f : X.carrier ≃ₗ[DualNumber k] X.carrier //
      ∀ m, X.reduction (f m) = X.reduction m}) =>
    Classical.choose (dualNumberLift_exists_endomorphism X f.1 f.2)
  refine Equiv.ofBijective F ⟨fun f g hfg => ?_, fun ψ => ?_⟩
  · refine Subtype.ext (LinearEquiv.ext fun m => ?_)
    obtain ⟨nf, hnf, hfm⟩ := Classical.choose_spec
      (dualNumberLift_exists_endomorphism X f.1 f.2) m
    obtain ⟨ng, hng, hgm⟩ := Classical.choose_spec
      (dualNumberLift_exists_endomorphism X g.1 g.2) m
    change X.reduction nf = F f (X.reduction m) at hnf
    change X.reduction ng = F g (X.reduction m) at hng
    rw [hfm, hgm, smul_eq_smul_of_map_eq _ X.reduction
      (dualNumberLift_eps_smul_eq_zero_iff X)
      (a := nf) (b := ng) (by rw [hnf, hng, hfg])]
  · obtain ⟨g, hgfix, hg⟩ := dualNumberLift_exists_linearEquiv_of_end X ψ
    exact ⟨⟨g, hgfix⟩, dualNumberLift_endomorphism_unique X g _ ψ
      (Classical.choose_spec (dualNumberLift_exists_endomorphism X g hgfix)) hg⟩

/-- The automorphisms of a lift that induce the identity on the special fibre, as a
subgroup of its linear automorphism group. -/
private def dualNumberLift_reductionIdentitySubgroup
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V) :
    Subgroup (X.carrier ≃ₗ[DualNumber k] X.carrier) where
  carrier f := ∀ m, X.reduction (f m) = X.reduction m
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro f g hf hg m
    change X.reduction (f (g m)) = X.reduction m
    rw [hf, hg]
  inv_mem' := by
    intro f hf m
    simpa using (hf (f.symm m)).symm

/-- The correspondence with endomorphisms of `V`, read on the subgroup of reduction-fixing
automorphisms. -/
@[sga "3 II 4.5.1" "special case"]
private noncomputable def dualNumberLift_reductionIdentityEquiv
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V) :
    dualNumberLift_reductionIdentitySubgroup X ≃ Module.End k V :=
  dualNumberLift_endEquivOfReductionIdentity X

/-- Composing two reduction-fixing automorphisms adds the corresponding endomorphisms. -/
@[sga "3 II 4.5.1" "special case"]
private lemma dualNumberLift_reductionIdentityEquiv_mul
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V)
    (f g : dualNumberLift_reductionIdentitySubgroup X) :
    dualNumberLift_reductionIdentityEquiv X (f * g) =
      dualNumberLift_reductionIdentityEquiv X f +
        dualNumberLift_reductionIdentityEquiv X g := by
  classical
  let E := dualNumberLift_reductionIdentityEquiv X
  refine dualNumberLift_endomorphism_unique X (f.1 * g.1) (E (f * g)) (E f + E g)
    (Classical.choose_spec (dualNumberLift_exists_endomorphism X (f.1 * g.1) (f * g).2))
    fun m => ?_
  obtain ⟨ng, hrng, hg⟩ := Classical.choose_spec
    (dualNumberLift_exists_endomorphism X g.1 g.2) m
  obtain ⟨nf, hrnf, hf⟩ := Classical.choose_spec
    (dualNumberLift_exists_endomorphism X f.1 f.2) (g.1 m)
  refine ⟨ng + nf, ?_, ?_⟩
  · rw [map_add, hrng, hrnf, g.2, LinearMap.add_apply]
    exact add_comm _ _
  · change f.1 (g.1 m) = m + (DualNumber.eps : DualNumber k) • (ng + nf)
    rw [hf, hg, smul_add]
    abel

/-- The subgroup of reduction-fixing automorphisms of a lift is the additive group
`Module.End k V`, as a multiplicative isomorphism. -/
@[sga "3 II 4.5.1" "special case"]
private noncomputable def dualNumberLift_reductionIdentityMulEquiv
    {k : Type w} [Field k] {V : Type t} [AddCommGroup V] [Module k V]
    (X : DualNumberLift.{w, v, t} (k := k) V) :
    dualNumberLift_reductionIdentitySubgroup X ≃*
      Multiplicative (Module.End k V) where
  toEquiv := (dualNumberLift_reductionIdentityEquiv X).trans
    Multiplicative.ofAdd
  map_mul' f g := by
    change Multiplicative.ofAdd
        (dualNumberLift_reductionIdentityEquiv X (f * g)) =
      Multiplicative.ofAdd (dualNumberLift_reductionIdentityEquiv X f) *
        Multiplicative.ofAdd (dualNumberLift_reductionIdentityEquiv X g)
    rw [dualNumberLift_reductionIdentityEquiv_mul]
    rfl

/-- A linear automorphism of the module of an object satisfies the base-change condition
over the identity of the base. -/
private lemma homOfLinearEquiv_baseChange
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {M : FiniteProjectiveModule (Λ := Λ) (k := k)}
    (f : M.carrier ≃ₗ[M.base] M.carrier) :
    ∃ e : TensorProduct M.base M.base M.carrier ≃ₗ[M.base] M.carrier,
      ∀ m, e (TensorProduct.tmul M.base (1 : M.base) m) = f m := by
  let t := TensorProduct.congr (R := M.base) (R₂ := M.base)
    (σ₁₂ := RingHom.id M.base) (LinearEquiv.refl M.base M.base) f
  let e := t.trans (TensorProduct.lid M.base M.carrier)
  refine ⟨e, ?_⟩
  intro m
  simp [e, t]

/-- A linear automorphism of the module of an object, as a morphism of finite projective
modules whose base morphism is the identity. -/
private noncomputable def homOfLinearEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {M : FiniteProjectiveModule (Λ := Λ) (k := k)}
    (f : M.carrier ≃ₗ[M.base] M.carrier) : M.Hom M :=
  { base := 𝟙 M.base
    linear := f.toLinearMap
    baseChange := homOfLinearEquiv_baseChange f }


/-- Composing the morphisms attached to two mutually inverse linear automorphisms gives the
identity. -/
private lemma homEquiv_symm_homOfLinearEquiv_comp
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓖 : FiniteProjectiveModule.Family (Λ := Λ) (k := k))
    (M : FiniteProjectiveModule (Λ := Λ) (k := k))
    (f g : M.carrier ≃ₗ[M.base] M.carrier) (hfg : ∀ m, g (f m) = m) :
    letI := 𝓖.category
    (𝓖.homEquiv M M).symm (homOfLinearEquiv f) ≫
      (𝓖.homEquiv M M).symm (homOfLinearEquiv g) = 𝟙 M := by
  let := 𝓖.category
  let h := (𝓖.homEquiv M M).symm (homOfLinearEquiv f)
  let i := (𝓖.homEquiv M M).symm (homOfLinearEquiv g)
  have hh : (𝓖.homEquiv M M h) = homOfLinearEquiv f :=
    (𝓖.homEquiv M M).apply_symm_apply _
  have hii : (𝓖.homEquiv M M i) = homOfLinearEquiv g :=
    (𝓖.homEquiv M M).apply_symm_apply _
  apply (𝓖.homEquiv M M).injective
  have hb : ((𝓖.homEquiv M M) (h ≫ i)).base = 𝟙 M.base := by
    rw [𝓖.comp_base]
    simp [hh, hii, homOfLinearEquiv]
  apply FiniteProjectiveModule.Hom.ext_of_base_eq _ _ (hb.trans (𝓖.id_base M).symm)
  intro m
  rw [𝓖.comp_linear h i m, 𝓖.id_linear M m, hh, hii]
  exact hfg m

/-- A linear automorphism of the module of an object, as an automorphism of that object in
the category of finite projective modules. -/
private noncomputable def autOfLinearEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓖 : FiniteProjectiveModule.Family (Λ := Λ) (k := k))
    (M : FiniteProjectiveModule (Λ := Λ) (k := k))
    (f : M.carrier ≃ₗ[M.base] M.carrier) :
    letI := 𝓖.category
    Aut M :=
  letI := 𝓖.category
  ⟨_, _, homEquiv_symm_homOfLinearEquiv_comp 𝓖 M f f.symm f.symm_apply_apply,
    homEquiv_symm_homOfLinearEquiv_comp 𝓖 M f.symm f f.apply_symm_apply⟩

/-- A deformation of `V` whose base carries an identification with the dual numbers
compatible with its morphism down to the special fibre, read as a
`Deformation.Examples.DualNumberLift` of `V`. -/
private noncomputable def dualNumberLiftOfHomToSpecialFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type t} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (M : FiniteProjectiveModule (Λ := Λ) (k := k))
    (H : M.Hom (specialFiber (Λ := Λ) (k := k) V))
    (iε : M.base ≃ₐ[Λ] DualNumber k)
    (hcompat : ∀ d : DualNumber k,
      H.base.hom (iε.symm d) = (TrivSqZeroExt.fstHom k k k).toRingHom d) :
    DualNumberLift.{w, t, t} (k := k) V := by
  classical
  let S := specialFiber (Λ := Λ) (k := k) V
  letI : Module k S.carrier := S.module
  letI : Module (DualNumber k) M.carrier :=
    Module.compHom M.carrier iε.symm.toRingHom
  letI : RingHomInvPair iε.toRingHom iε.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv iε.toRingEquiv
  letI : RingHomInvPair iε.symm.toRingHom iε.toRingHom :=
    RingHomInvPair.of_ringEquiv iε.symm.toRingEquiv
  let eM : M.carrier ≃ₛₗ[iε.toRingHom] M.carrier := by
    refine LinearEquiv.ofBijective
      ({ toFun := id
         map_add' := fun _ _ => rfl
         map_smul' := ?_ } : M.carrier →ₛₗ[iε.toRingHom] M.carrier) ?_
    · intro a m
      change a • m = iε.symm (iε a) • m
      rw [iε.symm_apply_apply]
    · exact ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩
  letI : Module.Projective (DualNumber k) M.carrier := Module.Projective.of_equiv eM
  letI : Module.Finite (DualNumber k) M.carrier :=
    Module.Finite.of_surjective (eM : M.carrier →ₛₗ[iε.toRingHom] M.carrier)
      eM.surjective
  let red : M.carrier →ₛₗ[(TrivSqZeroExt.fstHom k k k).toRingHom] V := by
    refine { toFun := H.linear, map_add' := H.linear.map_add', map_smul' := ?_ }
    intro d m
    change H.linear (iε.symm d • m) =
      (TrivSqZeroExt.fstHom k k k).toRingHom d • H.linear m
    calc
      H.linear (iε.symm d • m) = H.base.hom (iε.symm d) • H.linear m :=
        H.linear.map_smulₛₗ _ _
      _ = (TrivSqZeroExt.fstHom k k k).toRingHom d • H.linear m := by
        rw [hcompat]
        rfl
  refine {
    carrier := M.carrier
    addCommGroup := inferInstance
    module := inferInstance
    finite := inferInstance
    projective := inferInstance
    reduction := red
    baseChange := ?_ }
  let : Algebra M.base S.base := H.base.hom.toRingHom.toAlgebra
  let : Module M.base S.base := Module.compHom S.base H.base.hom.toRingHom
  let : Algebra k S.base := by
    change Algebra k k
    exact Algebra.id k
  let : Algebra k M.base :=
    (iε.symm.toRingHom.comp (algebraMap k (DualNumber k))).toAlgebra
  let : Algebra (DualNumber k) k := TrivSqZeroExt.algebraBase k k
  let : Module (DualNumber k) k :=
    Module.compHom k (TrivSqZeroExt.fstHom k k k).toRingHom
  let : Module k M.carrier := Module.compHom M.carrier (algebraMap k M.base)
  obtain ⟨e₀, he₀⟩ := H.baseChange
  let eK : S.base ≃ₛₗ[iε.toRingHom] k := by
    refine LinearEquiv.ofBijective
      ({ toFun := fun a => a
         map_add' := fun _ _ => rfl
         map_smul' := ?_ } : S.base →ₛₗ[iε.toRingHom] k) ?_
    · intro a z
      change H.base.hom a • z =
        (TrivSqZeroExt.fstHom k k k).toRingHom (iε a) • z
      have hh : H.base.hom a = (TrivSqZeroExt.fstHom k k k).toRingHom (iε a) := by
        simpa using hcompat (iε a)
      rw [hh]
      rfl
    · exact ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩
  let eT := TensorProduct.congr eK eM
  let : SMulCommClass M.base k S.base := ⟨by
    intro a b z
    simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]⟩
  let : Module k (TensorProduct M.base S.base M.carrier) :=
    Module.compHom _ (algebraMap k S.base)
  let eTlin : (TensorProduct M.base S.base M.carrier) ≃ₗ[k]
      TensorProduct (DualNumber k) k M.carrier := by
    refine LinearEquiv.ofBijective
      ({ toFun := eT
         map_add' := eT.map_add
         map_smul' := ?_ } : TensorProduct M.base S.base M.carrier →ₗ[k]
           TensorProduct (DualNumber k) k M.carrier) ?_
    · intro c z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · calc
          eT (c • (0 : TensorProduct M.base S.base M.carrier)) = eT 0 :=
            congrArg eT (smul_zero c)
          _ = 0 := eT.map_zero
          _ = c • eT 0 := by
            have hz : c • (0 : TensorProduct (DualNumber k) k M.carrier) = 0 :=
              TensorProduct.smul_zero c
            simpa only [eT.map_zero] using hz.symm
      · intro a m
        change (eK (c • a)) ⊗ₜ[DualNumber k] (eM m) =
          c • ((eK a) ⊗ₜ[DualNumber k] (eM m))
        rw [TensorProduct.smul_tmul']
        congr 1
      · intro z₁ z₂ hz₁ hz₂
        calc
          eT (c • (z₁ + z₂)) = eT (c • z₁ + c • z₂) := by rw [smul_add]
          _ = eT (c • z₁) + eT (c • z₂) := eT.map_add _ _
          _ = c • eT z₁ + c • eT z₂ := by
            change eT (c • z₁) + eT (c • z₂) =
              (RingHom.id k) c • eT z₁ + (RingHom.id k) c • eT z₂
            exact congrArg₂ (· + ·) hz₁ hz₂
          _ = c • (eT z₁ + eT z₂) := by
            have hadd : c • (eT z₁ + eT z₂) = c • eT z₁ + c • eT z₂ :=
              TensorProduct.smul_add c _ _
            exact hadd.symm
          _ = c • eT (z₁ + z₂) := by rw [eT.map_add]
    · exact ⟨fun _ _ h => eT.injective h,
        fun z => ⟨eT.symm z, eT.apply_symm_apply z⟩⟩
  let e₀' : (TensorProduct M.base S.base M.carrier) ≃ₗ[k] V := by
    refine {
      toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }
    intro c z
    change e₀ ((algebraMap k S.base c) • z) = _
    exact e₀.map_smul _ _
  let e := eTlin.symm.trans e₀'
  refine ⟨e, ?_⟩
  intro m
  change e₀' (eTlin.symm (1 ⊗ₜ[DualNumber k] m)) = H.linear m
  have htmul : eTlin.symm (1 ⊗ₜ[DualNumber k] m) =
      (1 : S.base) ⊗ₜ[M.base] m := by
    apply eTlin.injective
    rw [eTlin.apply_symm_apply]
    change (1 : k) ⊗ₜ[DualNumber k] m = eK (1 : S.base) ⊗ₜ[DualNumber k] eM m
    rw [show eK (1 : S.base) = 1 by rfl, show eM m = m by rfl]
  rw [htmul]
  change e₀ ((1 : S.base) ⊗ₜ[M.base] m) = H.linear m
  exact he₀ m

/-- In a deformation whose base is identified with the dual numbers compatibly with its
morphism `H` down to the special fibre, multiplication by `ε` kills exactly the elements that
`H` kills, and `H` is surjective. Both facts are read off the attached
`Deformation.Examples.DualNumberLift`; the identification may be the uncorrected one, because
normalizing it fixes `ε`. -/
private lemma eps_smul_zero_iff_and_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type t} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (M : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
    (H : M.Hom (specialFiber (Λ := Λ) (k := k) V))
    (iε : M.base ≃ₐ[Λ] DualNumber k) :
    (∀ z : M.carrier, iε.symm DualNumber.eps • z = 0 ↔ H.linear z = 0) ∧
      Function.Surjective H.linear := by
  classical
  let X := dualNumberLiftOfHomToSpecialFiber M H (normalizedDualNumberEquiv iε)
    (normalizedDualNumberEquiv_symm_compat M.base H.base iε)
  refine ⟨fun z => ?_, DualNumberLift.reduction_surjective X⟩
  rw [← normalizedDualNumberEquiv_symm_eps iε]
  exact dualNumberLift_eps_smul_eq_zero_iff X z

/-- Transporting an identification with the dual numbers along an equality of objects
commutes with the induced `eqToHom`. -/
private lemma eqToHom_symm_hom_symm_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) (i : B ≃ₐ[Λ] DualNumber k)
    (z : DualNumber k) :
    (eqToHom h.symm).hom (i.symm z) = (h ▸ i).symm z := by
  cases h
  rfl

/-- An automorphism of an object whose base morphism is the identity, read as a linear
automorphism of its module. -/
private noncomputable def linearEquivOfAut
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓖 : FiniteProjectiveModule.Family (Λ := Λ) (k := k))
    (M : FiniteProjectiveModule (Λ := Λ) (k := k)) :
    letI := 𝓖.category
    ∀ φ : Aut M, (𝓖.homEquiv M M φ.hom).base = 𝟙 M.base →
      M.carrier ≃ₗ[M.base] M.carrier :=
  letI := 𝓖.category
  fun φ hb =>
  { toFun := (𝓖.homEquiv M M φ.hom).linear
    invFun := (𝓖.homEquiv M M φ.inv).linear
    left_inv := fun z => by
      have h := 𝓖.comp_linear φ.hom φ.inv z
      rw [φ.hom_inv_id, 𝓖.id_linear M z] at h
      exact h.symm
    right_inv := fun z => by
      have h := 𝓖.comp_linear φ.inv φ.hom z
      rw [φ.inv_hom_id, 𝓖.id_linear M z] at h
      exact h.symm
    map_add' := (𝓖.homEquiv M M φ.hom).linear.map_add
    map_smul' := fun c m => by
      have hc : (𝓖.homEquiv M M φ.hom).base.hom.toRingHom c = c := by
        rw [hb]
        rfl
      have hs := (𝓖.homEquiv M M φ.hom).linear.map_smulₛₗ c m
      rw [hc] at hs
      exact hs }

/-- A linear automorphism of a deformation compatible with its morphism to the special fibre
is an automorphism of that deformation in the fibre over its base. -/
private lemma exists_fiberAut_of_linearEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V]
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k} :
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let S := specialFiber (Λ := Λ) (k := k) V
    let p := objectsOverFunctor 𝓖.projection S
    ∀ (xε : p.Fiber Aε) (L : xε.1.left.carrier ≃ₗ[xε.1.left.base] xε.1.left.carrier),
      (∀ m, (𝓖.homEquiv xε.1.left S xε.1.hom).linear (L m) =
        (𝓖.homEquiv xε.1.left S xε.1.hom).linear m) →
      ∃ c : Aut xε, 𝓖.homEquiv xε.1.left xε.1.left c.hom.val.left = homOfLinearEquiv L := by
  dsimp only
  intro xε L hL
  let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
  let := 𝓖.category
  let S := specialFiber (Λ := Λ) (k := k) V
  let p := objectsOverFunctor 𝓖.projection S
  let M := xε.1.left
  let a := autOfLinearEquiv 𝓖 M L
  have ha : 𝓖.homEquiv M M a.hom = homOfLinearEquiv L := by
    change (𝓖.homEquiv M M)
      ((𝓖.homEquiv M M).symm (homOfLinearEquiv L)) = _
    exact (𝓖.homEquiv M M).apply_symm_apply _
  have hfix : a.hom ≫ xε.1.hom = xε.1.hom := by
    apply (𝓖.homEquiv M S).injective
    have hb : (𝓖.homEquiv M S (a.hom ≫ xε.1.hom)).base =
        (𝓖.homEquiv M S xε.1.hom).base := by
      rw [𝓖.comp_base, ha]
      simp [homOfLinearEquiv]
      rfl
    apply FiniteProjectiveModule.Hom.ext_of_base_eq _ _ hb
    intro m
    rw [𝓖.comp_linear, ha]
    change (𝓖.homEquiv M S xε.1.hom).linear (L m) = (𝓖.homEquiv M S xε.1.hom).linear m
    exact hL m
  let b : xε.1 ≅ xε.1 := Over.isoMk a hfix
  have hblift : p.IsHomLift (𝟙 Aε) b.hom := by
    have hmap : 𝓖.projection.map a.hom = 𝟙 (𝓖.projection.obj M) := by
      have hh := 𝓖.projection_map a.hom
      rw [ha] at hh
      have hbasea : (homOfLinearEquiv L).base = 𝟙 M.base := rfl
      rw [hbasea] at hh
      have h := congrArg (fun q : M.base ⟶ M.base =>
        eqToHom (𝓖.projection_obj M) ≫ q ≫
          eqToHom (𝓖.projection_obj M).symm) hh
      simpa [Category.assoc] using h
    apply IsHomLift.of_fac' p (𝟙 Aε) b.hom xε.2 xε.2
    change 𝓖.projection.map a.hom =
      eqToHom xε.2 ≫ 𝟙 Aε ≫ eqToHom xε.2.symm
    rw [hmap]
    simp only [Category.id_comp, eqToHom_trans,
      eqToHom_refl,
      objectsOverFunctor_obj]
    change 𝟙 (𝓖.projection.obj M) = 𝟙 (𝓖.projection.obj M)
    rfl
  let : p.IsHomLift (𝟙 Aε) b.hom := hblift
  let : p.IsHomLift (𝟙 Aε) b.inv :=
    IsHomLift.lift_id_inv p Aε b
  let c : Aut xε := {
    hom := ⟨b.hom, inferInstance⟩
    inv := ⟨b.inv, inferInstance⟩
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      exact b.hom_inv_id
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      exact b.inv_hom_id }
  exact ⟨c, ha⟩

/-- There exists a multiplicative isomorphism of the infinitesimal automorphism group of the
deformations of `V` with `Multiplicative (Module.End k V)` satisfying the pointwise formula
`γ(m) = m + ε·n` with `reduction n` the associated endomorphism applied to `reduction m`. The
chosen one is `infinitesimalAutomorphismsEquivEnd`. -/
public theorem nonempty_infinitesimalAutomorphismsEquivEnd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] : Nonempty (
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection
      (specialFiber (Λ := Λ) (k := k) V)
    let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
    let hp : IsPredeformationCategory p := hD.predeformation
    ∀ {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
      {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
      {xε : p.Fiber Aε}
      (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
      (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i),
      let iε : Aε ≃ₐ[Λ] DualNumber k :=
        Classical.choose (Classical.choose_spec hpair)
      let M := xε.1.left
      let hbase : M.base = Aε := (𝓖.projection_obj xε.1.left).symm.trans xε.2
      let ε : M.base := (eqToHom hbase.symm).hom (iε.symm DualNumber.eps)
      let r := 𝓖.homEquiv M
        (specialFiber (Λ := Λ) (k := k) V) xε.1.hom
      { E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
          Multiplicative (Module.End k V) //
        ∀ (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) (m : M.carrier),
          let a := 𝓖.homEquiv M M γ.val.hom.val.left
          ∃ n : M.carrier,
            r.linear n = (Multiplicative.toAdd (E γ)) (r.linear m) ∧
              a.linear m = m + ε • n }) := by
  constructor
  classical
  dsimp only
  intro Aε x₀ xε g e hpair i hi
  let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
  let := 𝓖.category
  let S := specialFiber (Λ := Λ) (k := k) V
  let p := objectsOverFunctor 𝓖.projection S
  let M := xε.1.left
  let : AddCommGroup M.carrier := M.addCommGroup
  let : Module M.base M.carrier := M.module
  let hbase : M.base = Aε := (𝓖.projection_obj xε.1.left).symm.trans xε.2
  let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
  let hp : IsPredeformationCategory
      (objectsOverFunctor 𝓖.projection S) :=
    hD.predeformation
  let iε : Aε ≃ₐ[Λ] DualNumber k := Classical.choose (Classical.choose_spec hpair)
  let iεM : M.base ≃ₐ[Λ] DualNumber k := hbase ▸ iε
  let jεM := normalizedDualNumberEquiv iεM
  let r := 𝓖.homEquiv M S xε.1.hom
  let X := dualNumberLiftOfHomToSpecialFiber M r jεM
    (normalizedDualNumberEquiv_symm_compat M.base r.base iεM)
  have heps : jεM.symm DualNumber.eps = iεM.symm DualNumber.eps :=
    normalizedDualNumberEquiv_symm_eps iεM
  have hepsBase : (eqToHom hbase.symm).hom (iε.symm DualNumber.eps) =
      iεM.symm DualNumber.eps :=
    eqToHom_symm_hom_symm_apply hbase iε DualNumber.eps
  have hbase_aut (ζ : infinitesimalAutomorphismGroup hp g e hpair i hi) :
      (𝓖.homEquiv M M ζ.val.hom.val.left).base = 𝟙 M.base := by
    have : p.IsHomLift (𝟙 Aε) ζ.val.hom.val := ζ.val.hom.property
    have hfac := IsHomLift.fac (p := p) (f := 𝟙 Aε) ζ.val.hom.val
    have h' := congrArg (fun q : Aε ⟶ Aε =>
      eqToHom hbase ≫ q ≫ eqToHom hbase.symm) hfac.symm
    simp only [p, objectsOverFunctor,
      Functor.comp_map, Over.forget_map, Category.assoc] at h'
    simp [hbase, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id] at h'
    simpa only [𝓖.projection_map] using h'
  let toL (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) :
      dualNumberLift_reductionIdentitySubgroup X := by
    let overHom := γ.val.hom.val
    let a := 𝓖.homEquiv M M overHom.left
    have hmember := γ.property
    rw [mem_infinitesimalAutomorphisms_iff] at hmember
    let ret := (canonicalRetraction hp.cofibered g e hpair.split i hi).1
    have hret : ret.left ≫ x₀.1.hom = xε.1.hom := ret.w
    have hleft : overHom.left ≫ ret.left = ret.left := by
      simpa only [Over.comp_left] using
        congrArg (fun q : xε.1 ⟶ x₀.1 => q.left) hmember
    have hfix : overHom.left ≫ xε.1.hom = xε.1.hom := by
      rw [← hret, ← Category.assoc, hleft]
    have hred : ∀ z, X.reduction (a.linear z) = X.reduction z := by
      intro z
      have hcomp := 𝓖.comp_linear overHom.left xε.1.hom z
      rw [hfix] at hcomp
      change r.linear z = r.linear (a.linear z) at hcomp
      change r.linear (a.linear z) = r.linear z
      exact hcomp.symm
    let L := linearEquivOfAut 𝓖 M
      ⟨overHom.left, γ.val.inv.val.left,
        congrArg (fun q : xε ⟶ xε => q.val.left) γ.val.hom_inv_id,
        congrArg (fun q : xε ⟶ xε => q.val.left) γ.val.inv_hom_id⟩ (hbase_aut γ)
    let : Module M.base X.carrier := M.module
    let : Module (DualNumber k) X.carrier :=
      Module.compHom X.carrier jεM.symm.toRingHom
    let f : X.carrier ≃ₗ[DualNumber k] X.carrier := {
      toFun := L
      invFun := L.symm
      left_inv := L.left_inv
      right_inv := L.right_inv
      map_add' := L.map_add
      map_smul' := by
        intro z m
        change L (jεM.symm z • m) = jεM.symm z • L m
        exact L.map_smul _ _ }
    exact ⟨f, hred⟩
  let F : infinitesimalAutomorphismGroup hp g e hpair i hi →*
      dualNumberLift_reductionIdentitySubgroup X := {
    toFun := toL
    map_one' := Subtype.ext <| LinearEquiv.ext fun m => by
      change (𝓖.homEquiv M M (𝟙 M)).linear m = m
      exact 𝓖.id_linear M m
    map_mul' γ δ := Subtype.ext <| LinearEquiv.ext fun m => by
      change (𝓖.homEquiv M M
          (δ.val.hom.val.left ≫ γ.val.hom.val.left)).linear m =
        (𝓖.homEquiv M M γ.val.hom.val.left).linear
          ((𝓖.homEquiv M M δ.val.hom.val.left).linear m)
      exact 𝓖.comp_linear _ _ m }
  let E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
      Multiplicative (Module.End k V) :=
    (MulEquiv.ofBijective F (by
      constructor
      · intro γ δ h
        apply Subtype.ext
        apply Aut.ext
        apply Functor.Fiber.hom_ext
        apply CostructuredArrow.hom_ext
        apply (𝓖.homEquiv M M).injective
        apply FiniteProjectiveModule.Hom.ext_of_base_eq _ _
          ((hbase_aut γ).trans (hbase_aut δ).symm)
        intro m
        exact congrArg (fun q : dualNumberLift_reductionIdentitySubgroup X => q.1 m) h
      · intro f
        let : Module M.base X.carrier := M.module
        let : Module (DualNumber k) X.carrier :=
          Module.compHom X.carrier jεM.symm.toRingHom
        let L : M.carrier ≃ₗ[M.base] M.carrier :=
          LinearEquiv.ofBijective
            ({ toFun := f.1
               map_add' := f.1.map_add
               map_smul' := by
                 intro c m
                 have hm := f.1.map_smul (jεM c) m
                 change f.1 (jεM.symm (jεM c) • m) =
                   jεM.symm (jεM c) • f.1 m at hm
                 rw [jεM.symm_apply_apply] at hm
                 change f.1 (c • m) = c • f.1 m
                 exact hm } :
              M.carrier →ₗ[M.base] M.carrier)
            f.1.bijective
        obtain ⟨c, hcL⟩ := exists_fiberAut_of_linearEquiv V xε L fun m => f.2 m
        have hs : Subsingleton (Aut x₀) :=
          let ⟨Q⟩ := hp.specialFiber
          ⟨fun d e => Aut.ext (Q.functor.map_injective (Subsingleton.elim _ _))⟩
        have hc : c ∈ infinitesimalAutomorphisms hp.cofibered
            g e hpair i hi := by
          change c ∈ relativeInfinitesimalAutomorphisms _ _ _ _
          rw [mem_relativeInfinitesimalAutomorphisms]
          exact hs.elim _ _
        refine ⟨⟨c, hc⟩, Subtype.ext (LinearEquiv.ext fun m => ?_)⟩
        change (𝓖.homEquiv M M c.hom.val.left).linear m = f.1 m
        rw [hcL]
        rfl)).trans
      (dualNumberLift_reductionIdentityMulEquiv X)
  refine ⟨E, fun γ m => ?_⟩
  obtain ⟨n, hnred, hnform⟩ := Classical.choose_spec
    (dualNumberLift_exists_endomorphism X (F γ).1 (F γ).2) m
  let nM : M.carrier := n
  refine ⟨nM, hnred, ?_⟩
  let : Module M.base X.carrier := M.module
  change (𝓖.homEquiv M M γ.val.hom.val.left).linear m =
    m + jεM.symm DualNumber.eps • nM at hnform
  change (𝓖.homEquiv M M γ.val.hom.val.left).linear m = m +
    (eqToHom hbase.symm).hom (iε.symm DualNumber.eps) • nM
  rw [hepsBase, ← heps]
  exact hnform

/-- Infinitesimal automorphisms of a finite-dimensional vector space are its
linear endomorphisms, with composition corresponding to addition. -/
@[stacks 0DVQ "infinitesimal_automorphisms"]
public noncomputable def infinitesimalAutomorphismsEquivEnd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection
      (specialFiber (Λ := Λ) (k := k) V)
    let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
    let hp : IsPredeformationCategory p := hD.predeformation
    ∀ {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
      {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
      {xε : p.Fiber Aε}
      (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
      (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i),
      let iε : Aε ≃ₐ[Λ] DualNumber k :=
        Classical.choose (Classical.choose_spec hpair)
      let M := xε.1.left
      let hbase : M.base = Aε := (𝓖.projection_obj xε.1.left).symm.trans xε.2
      let ε : M.base := (eqToHom hbase.symm).hom (iε.symm DualNumber.eps)
      let r := 𝓖.homEquiv M
        (specialFiber (Λ := Λ) (k := k) V) xε.1.hom
      { E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
          Multiplicative (Module.End k V) //
        ∀ (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) (m : M.carrier),
          let a := 𝓖.homEquiv M M γ.val.hom.val.left
          ∃ n : M.carrier,
            r.linear n = (Multiplicative.toAdd (E γ)) (r.linear m) ∧
              a.linear m = m + ε • n } :=
  @Classical.choice _ (by
    exact nonempty_infinitesimalAutomorphismsEquivEnd (Λ := Λ) (k := k) V)

/-- The infinitesimal automorphism group of the deformations of `V` is the `k`-vector space
`Module.End k V`, and is in particular finite-dimensional. The `k`-structure is the one of
Stacks 06JV: its addition is composition of automorphisms, and multiplying by `c` scales the
infinitesimal coordinate, which on the formula `γ(m) = m + ε·n` reads
`(c · γ)(m) = m + ε·(cb · n)` for any element `cb` of the base reducing to `c`. -/
@[stacks 0DVQ "infinitesimal_automorphisms"]
public theorem exists_infinitesimalAutomorphismsLinearEquivEnd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection
      (specialFiber (Λ := Λ) (k := k) V)
    let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
    let hp : IsPredeformationCategory p := hD.predeformation
    ∀ {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
      {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
      {xε : p.Fiber Aε}
      (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
      (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i),
      let iε : Aε ≃ₐ[Λ] DualNumber k :=
        Classical.choose (Classical.choose_spec hpair)
      let M := xε.1.left
      let hbase : M.base = Aε := (𝓖.projection_obj xε.1.left).symm.trans xε.2
      let ε : M.base := (eqToHom hbase.symm).hom (iε.symm DualNumber.eps)
      let r := 𝓖.homEquiv M
        (specialFiber (Λ := Λ) (k := k) V) xε.1.hom
      ∃ A : AddCommGroup (infinitesimalAutomorphismGroup hp g e hpair i hi),
        letI := A
        ∃ Mo : Module k (infinitesimalAutomorphismGroup hp g e hpair i hi),
          letI := Mo
          (∀ γ δ : infinitesimalAutomorphismGroup hp g e hpair i hi, γ + δ = γ * δ) ∧
          (∃ E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃ₗ[k] Module.End k V,
            (∀ (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) (m : M.carrier),
              ∃ n : M.carrier, r.linear n = E γ (r.linear m) ∧
                (𝓖.homEquiv M M γ.val.hom.val.left).linear m = m + ε • n) ∧
            ∀ (c : k) (cb : M.base), r.base.hom cb = c →
              ∀ (γ : infinitesimalAutomorphismGroup hp g e hpair i hi)
                (m n : M.carrier), r.linear n = E γ (r.linear m) →
                (𝓖.homEquiv M M γ.val.hom.val.left).linear m = m + ε • n →
                (𝓖.homEquiv M M (c • γ).val.hom.val.left).linear m =
                  m + ε • (cb • n)) ∧
          FiniteDimensional k (infinitesimalAutomorphismGroup hp g e hpair i hi) := by
  classical
  dsimp only
  intro Aε x₀ xε g e hpair i hi
  let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
  let := 𝓖.category
  let S := specialFiber (Λ := Λ) (k := k) V
  let : Module k S.carrier := S.module
  let p := objectsOverFunctor 𝓖.projection S
  let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
  let hp : IsPredeformationCategory p := hD.predeformation
  let M := xε.1.left
  let hbase : M.base = Aε := (𝓖.projection_obj xε.1.left).symm.trans xε.2
  let iε : Aε ≃ₐ[Λ] DualNumber k := Classical.choose (Classical.choose_spec hpair)
  let iεM : M.base ≃ₐ[Λ] DualNumber k := hbase ▸ iε
  let r := 𝓖.homEquiv M S xε.1.hom
  have hepsBase : (eqToHom hbase.symm).hom (iε.symm DualNumber.eps) =
      iεM.symm DualNumber.eps :=
    eqToHom_symm_hom_symm_apply hbase iε DualNumber.eps
  obtain ⟨hepsZero, -⟩ := eps_smul_zero_iff_and_surjective M r iεM
  have hz : ∀ z : M.carrier,
      ((eqToHom hbase.symm).hom (iε.symm DualNumber.eps) : M.base) • z = 0 ↔
        r.linear z = 0 := by
    intro z
    rw [hepsBase]
    exact hepsZero z
  let EE := infinitesimalAutomorphismsEquivEnd (Λ := Λ) (k := k) V g e hpair i hi
  let EM := EE.1
  have hEM := EE.2
  let eqv : infinitesimalAutomorphismGroup hp g e hpair i hi ≃ Module.End k V :=
    EM.toEquiv.trans Multiplicative.toAdd
  let A : AddCommGroup (infinitesimalAutomorphismGroup hp g e hpair i hi) :=
    eqv.addCommGroup
  let eadd : infinitesimalAutomorphismGroup hp g e hpair i hi ≃+ Module.End k V :=
    { toEquiv := eqv
      map_add' := fun x y => eqv.apply_symm_apply _ }
  let Mo : Module k (infinitesimalAutomorphismGroup hp g e hpair i hi) := eadd.module k
  let E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃ₗ[k] Module.End k V :=
    eadd.linearEquiv k
  refine ⟨A, Mo, ?_, ⟨E, ?_, ?_⟩, ?_⟩
  · intro γ δ
    apply eqv.injective
    have h₁ : eqv (γ + δ) = eqv γ + eqv δ := eadd.map_add γ δ
    have h₂ : eqv (γ * δ) = eqv γ + eqv δ := by
      change Multiplicative.toAdd (EM (γ * δ)) = _
      rw [EM.map_mul]
      rfl
    rw [h₁, h₂]
  · exact hEM
  · intro c cb hcb γ m n hn hform
    obtain ⟨n', hn', hform'⟩ := hEM (c • γ) m
    have hcb' : r.base.hom.toRingHom cb = c := hcb
    have hlin : r.linear (cb • n) = c • r.linear n :=
      (r.linear.map_smulₛₗ cb n).trans
        (congrArg (fun a : k => a • r.linear n) hcb')
    have hval : E (c • γ) (r.linear m) = c • E γ (r.linear m) :=
      (congrArg (fun f : Module.End k V => f (r.linear m)) (map_smul E c γ)).trans
        (LinearMap.smul_apply c (E γ) (r.linear m))
    have h₁ : r.linear n' = r.linear (cb • n) :=
      hn'.trans (hval.trans
        (((congrArg (fun v : V => c • v) hn).symm).trans hlin.symm))
    rw [hform', smul_eq_smul_of_map_eq _ r.linear hz h₁]
  · exact FiniteDimensional.of_injective E.toLinearMap E.injective

end Deformation.Examples.FiniteProjectiveModule
