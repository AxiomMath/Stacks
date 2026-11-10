module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Invariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.BrauerGroupConnectingMap
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.SplitCocycle
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.Classification
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.BrauerGroupConnectingMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Brauer group is the second Galois cohomology of the units

Let `K` be a field with separable algebraic closure `Kˢᵉᵖ`. The map

`δ : Br(K) → H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)`

of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.BrauerGroupConnectingMap` is a
group homomorphism; this file proves that it is bijective, so that it is an isomorphism of groups.

## Main definitions

* `Stacks.GaloisCohomology.brauerDeltaEquiv`: `δ` as an isomorphism of groups.

## Main results

* `Stacks.GaloisCohomology.brauerDelta_injective`: `δ` is injective.
* `Stacks.GaloisCohomology.brauerDelta_surjective`: `δ` is surjective.
* `Stacks.GaloisCohomology.brauerDelta_bijective`: `δ` is bijective.

## Implementation notes

Both directions go through the classification of degree-`d` central simple algebras by
`H¹(Gal(Kˢᵉᵖ/K), PGL_d(Kˢᵉᵖ))` of [Stacks, Tag 03R6](https://stacks.math.columbia.edu/tag/03R6),
which is already available as an equivalence; what has to be supplied is the behaviour of the
connecting map of the scalar extension in each direction.

*Injectivity.* A projective cocycle whose connecting class is trivial is cohomologous to the
trivial cocycle: multiplying a locally constant lift by the `1`-cochain trivialising its scalar
defect turns the lift into an honest `GL_d`-valued crossed homomorphism, and such a family is a
coboundary. That last step is Hilbert 90 for `GL_d`, `exists_eq_mul_map_of_isMulCocycle₁`, proved
here by semilinear descent: the twisted Galois action on `(Kˢᵉᵖ)^d` is smooth, so its invariants
span over `Kˢᵉᵖ`, and the matrix whose columns are a basis of invariants is the required
coboundary. The fixed algebra of the trivial cocycle is the matrix algebra over the ground field,
so a trivial class forces the representative to be split; applying this to `A ⊗ Bᵐᵒᵖ` makes two
algebras with the same class Brauer equivalent.

*Surjectivity.* A locally constant `2`-cocycle factors, in its second variable, through a finite
Galois level `Γ`, and the weighted permutation matrices `W σ = (c (σ, s γ)⁻¹)` indexed by `Γ` —
the matrices of the regular representation of the crossed product — form a family in
`GL_Γ(Kˢᵉᵖ)` whose scalar defect is the given cocycle. Their images in `PGL_Γ` form a projective
cocycle, and the classifying bijection of tag 03R6 produces a central simple algebra realising
the class.

No step produces a cohomology class from an existence statement: every class occurring is the
class of an explicitly written cocycle, and every algebra is the fixed algebra of an explicit
cocycle.

The private declarations of this file reach into those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology` and of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.BrauerGroupConnectingMap` through
`import all`, since neither the construction of the classifying bijection nor the cocycle formula
for `δ` is part of a public interface. A private import places those names in the private scope,
so none of them appears in the statement of a public declaration here.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public noncomputable section

open scoped Matrix MatrixGroups TensorProduct Topology

open groupCohomology

namespace Stacks.GaloisCohomology

section Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsSepClosure K L]

/-- **Smoothness forces the invariants to span.** For a semilinear action of `Gal(L/K)` on an
`L`-vector space in which every vector is fixed by an open subgroup, the `K`-invariants span the
space over `L`. If they did not, a nonzero `L`-linear functional would kill them, and averaging
`a • v` over a finite level through which the stabiliser of `v` factors would exhibit a
nontrivial `L`-linear relation between the distinct `K`-algebra maps of that level into `L`. -/
private theorem span_invariants_eq_top_of_smooth {V : Type*} [AddCommGroup V] [Module K V]
    [Module L V] (ρ : Representation K Gal(L/K) V)
    (hsemi : ∀ (σ : Gal(L/K)) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hsmooth : ∀ v : V, ∃ E : FiniteGaloisIntermediateField K L,
      ∀ σ : Gal(L/K), AlgEquiv.restrictNormalHom E σ = 1 → ρ σ v = v) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hf, hker⟩ := (Submodule.span L (ρ.invariants : Set V)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  apply hf
  ext v
  obtain ⟨E, hE⟩ := hsmooth v
  let r : Gal(L/K) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  obtain ⟨s, hs⟩ : ∃ s : (E ≃ₐ[K] E) → Gal(L/K), ∀ γ, r (s γ) = γ :=
    (AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E)).hasRightInverse
  have hfactor (σ τ : Gal(L/K)) (h : r σ = r τ) : ρ σ v = ρ τ v := by
    have he' := congrArg (ρ τ) (hE (τ⁻¹ * σ) (by change r (τ⁻¹ * σ) = 1; simp [h]))
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he'
  have hfactor_smul (σ τ : Gal(L/K)) (h : r σ = r τ) (a : E) :
      ρ σ ((a : L) • v) = ρ τ ((a : L) • v) := by
    rw [hsemi, hsemi, hfactor σ τ h]
    refine congrArg (fun x : L => x • ρ τ v) ?_
    have he := congrArg (fun γ : E ≃ₐ[K] E => (γ a : L)) h
    simpa [r, AlgEquiv.restrictNormalHom_apply] using he
  have hinv (a : E) : (∑ γ : E ≃ₐ[K] E, ρ (s γ) ((a : L) • v)) ∈ ρ.invariants := by
    rw [Representation.mem_invariants]
    intro σ
    rw [map_sum]
    calc
      _ = ∑ γ : E ≃ₐ[K] E, ρ (s (r σ * γ)) ((a : L) • v) := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hfactor_smul _ _ (by simp [hs]) a
      _ = _ := Fintype.sum_equiv (Equiv.mulLeft (r σ)) _ _ fun _ => rfl
  let j (γ : E ≃ₐ[K] E) : E →ₐ[K] L := E.toIntermediateField.val.comp γ.toAlgHom
  have hsum : ∑ γ : E ≃ₐ[K] E, f (ρ (s γ) v) • (j γ).toLinearMap = 0 := by
    ext a
    have hz : f (∑ γ : E ≃ₐ[K] E, ρ (s γ) ((a : L) • v)) = 0 :=
      hker (Submodule.subset_span (hinv a))
    have he (γ : E ≃ₐ[K] E) : s γ (a : L) = (γ a : L) := by
      have h := congrArg (fun δ : E ≃ₐ[K] E => (δ a : L)) (hs γ)
      simpa [r, AlgEquiv.restrictNormalHom_apply] using h
    simpa only [map_sum, hsemi, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, j, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      IntermediateField.coe_val, he, smul_eq_mul, mul_comm, LinearMap.zero_apply] using hz
  have hj : Function.Injective j := fun γ δ h =>
    AlgEquiv.ext fun a => Subtype.ext (congrArg (fun g : E →ₐ[K] L => g a) h)
  have hz := Fintype.linearIndependent_iff.mp
    ((linearIndependent_algHom_toLinearMap K E L).comp j hj) _ hsum 1
  rwa [hE (s 1) (hs 1)] at hz

/-- Entrywise application of the Galois action to a fixed vector is locally constant. -/
private theorem isLocallyConstant_galoisEvalPi {n : Type*} [Finite n] (v : n → L) :
    IsLocallyConstant fun σ : Gal(L/K) => (fun i => σ (v i) : n → L) := by
  classical
  have := Fintype.ofFinite n
  refine isLocallyConstant_of_finset (Finset.univ.image v) fun σ a ha => ?_
  funext i
  rw [AlgEquiv.mul_apply, ha (v i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]

/-- A locally constant function of two Galois automorphisms factors, in its second variable,
through a finite Galois level: the group is compact, so a neighbourhood of `1` translating every
value to itself contains the fixing subgroup of a finite Galois subextension. -/
private theorem exists_level_factor_snd {A : Type*} (c : Gal(L/K) × Gal(L/K) → A)
    (hc : IsLocallyConstant c) :
    ∃ E : FiniteGaloisIntermediateField K L, ∀ σ τ υ : Gal(L/K),
      AlgEquiv.restrictNormalHom E τ = AlgEquiv.restrictNormalHom E υ → c (σ, τ) = c (σ, υ) := by
  classical
  have hnear : ∀ᶠ η : Gal(L/K) in 𝓝 1, ∀ z : Gal(L/K) × Gal(L/K), c (z.1, z.2 * η) = c z := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := (1 : Gal(L/K)))
      (P := fun η (z : Gal(L/K) × Gal(L/K)) => c (z.1, z.2 * η) = c z) ?_
    · simpa using h
    · intro z _
      have h₁ : IsLocallyConstant
          fun p : Gal(L/K) × (Gal(L/K) × Gal(L/K)) => c (p.2.1, p.2.2 * p.1) :=
        hc.comp_continuous (continuous_snd.fst.prodMk (continuous_snd.snd.mul continuous_fst))
      have h₂ : IsLocallyConstant fun p : Gal(L/K) × (Gal(L/K) × Gal(L/K)) => c p.2 :=
        hc.comp_continuous continuous_snd
      have hn : ∀ᶠ p : Gal(L/K) × (Gal(L/K) × Gal(L/K)) in 𝓝 (1, z),
          (c (p.2.1, p.2.2 * p.1) = c p.2) = True :=
        ((h₁.comp₂ h₂ Eq).isOpen_fiber True).mem_nhds (by simp)
      exact hn.mono fun p hp => of_eq_true hp
  obtain ⟨E, hE⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (K := L) (k := K)
    {η : Gal(L/K) | ∀ z : Gal(L/K) × Gal(L/K), c (z.1, z.2 * η) = c z}).mp hnear
  refine ⟨E, fun σ τ υ h => ?_⟩
  have he : τ⁻¹ * υ ∈ E.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ E).2 (by simp [h])
  simpa using (hE he (σ, τ)).symm

/-- **Hilbert 90 for `GL_n`.** A locally constant crossed homomorphism of `Gal(L/K)` with values
in `GL_n(L)` is a coboundary: there is a `B` with `U σ · σ(B) = B` for every `σ`. The twisted
action `v ↦ U σ · σ(v)` on `L ^ n` is semilinear and smooth, so its invariants span by
`span_invariants_eq_top_of_smooth`, and the matrix whose columns are a basis of invariants is
such a `B`. -/
private theorem exists_eq_mul_map_of_isMulCocycle₁ {n : Type*} [Fintype n] [DecidableEq n]
    (U : Gal(L/K) → GL n L) (hUlc : IsLocallyConstant U)
    (hU : ∀ σ τ, U (σ * τ) = U σ *
      Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom Gal(L/K) L σ) (U τ)) :
    ∃ B : GL n L, ∀ σ : Gal(L/K),
      U σ * Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom Gal(L/K) L σ) B = B := by
  classical
  have hUone : U 1 = 1 := by
    have h := hU 1 1
    rw [one_mul] at h
    have hm : Matrix.GeneralLinearGroup.map
        (MulSemiringAction.toRingHom Gal(L/K) L (1 : Gal(L/K))) (U 1) = U 1 := Units.ext rfl
    rw [hm] at h
    exact mul_eq_left.mp h.symm
  let ρ : Representation K Gal(L/K) (n → L) :=
    { toFun := fun σ =>
        { toFun := fun v => (U σ : Matrix n n L) *ᵥ fun i => σ (v i)
          map_add' := fun v w => by
            simp only [Pi.add_apply, map_add]
            exact Matrix.mulVec_add _ _ _
          map_smul' := fun a v => by
            simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
            exact Matrix.mulVec_smul (U σ : Matrix n n L) a fun i => σ (v i) }
      map_one' := by
        refine LinearMap.ext fun v => ?_
        simp [hUone]
      map_mul' := fun σ τ => by
        refine LinearMap.ext fun v => funext fun i => ?_
        change ((U (σ * τ) : Matrix n n L) *ᵥ fun j => σ (τ (v j))) i =
          ((U σ : Matrix n n L) *ᵥ
            fun j => σ (((U τ : Matrix n n L) *ᵥ fun k => τ (v k)) j)) i
        rw [hU]
        simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.map_apply,
          Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
          map_sum, map_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        change (U σ : Matrix n n L) i j * σ ((U τ : Matrix n n L) j k) * σ (τ (v k)) = _
        ring }
  have hsemi (σ : Gal(L/K)) (a : L) (v : n → L) : ρ σ (a • v) = σ a • ρ σ v := by
    change (U σ : Matrix n n L) *ᵥ (fun i => σ (a * v i)) = _
    simp only [map_mul]
    exact Matrix.mulVec_smul (U σ : Matrix n n L) (σ a) fun i => σ (v i)
  have hsmooth (v : n → L) : ∃ E : FiniteGaloisIntermediateField K L,
      ∀ σ : Gal(L/K), AlgEquiv.restrictNormalHom E σ = 1 → ρ σ v = v := by
    have h : IsLocallyConstant fun σ => ρ σ v :=
      hUlc.comp₂ (isLocallyConstant_galoisEvalPi v) fun A x => (A : Matrix n n L) *ᵥ x
    obtain ⟨E, hE⟩ := exists_level_factor_snd (fun p : Gal(L/K) × Gal(L/K) => ρ p.2 v)
      (h.comp_continuous continuous_snd)
    exact ⟨E, fun σ hσ => by simpa using hE 1 σ 1 (by simpa using hσ)⟩
  have hspan := span_invariants_eq_top_of_smooth ρ hsemi hsmooth
  let b₀ := Module.Basis.ofSpan hspan.ge
  let b := b₀.reindex (b₀.indexEquiv (Pi.basisFun L n))
  have hb (i : n) : b i ∈ ρ.invariants :=
    Module.Basis.ofSpan_subset hspan.ge
      ⟨(b₀.indexEquiv (Pi.basisFun L n)).symm i, (b₀.reindex_apply _ i).symm⟩
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm), fun σ => ?_⟩
  have hB (i j : n) : ((Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm) :
        GL n L) : Matrix n n L) i j = b j i := by
    change Matrix.toLinAlgEquiv'.symm b.equivFun.symm.toLinearMap i j = _
    change b.equivFun.symm (Pi.single j 1) i = b j i
    rw [Module.Basis.equivFun_symm_apply]
    simp [Pi.single_apply, ite_apply]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hi := congrFun ((Representation.mem_invariants ρ (b j)).1 (hb j) σ) i
  simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.GeneralLinearGroup.map_apply,
    hB, Matrix.mulVec, dotProduct] at hi ⊢
  exact hi

end Hilbert90

section Factor

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsSepClosure K L]

/-- A locally constant function on the Galois group is determined by the action on a finite
subset of `L`: this is the form of continuity required by `PGLCocycle`. -/
private theorem exists_finset_determines {A : Type*} (f : Gal(L/K) → A)
    (hf : IsLocallyConstant f) :
    ∃ S : Finset L, ∀ σ τ : Gal(L/K), (∀ x ∈ S, σ x = τ x) → f σ = f τ := by
  classical
  obtain ⟨E, hE⟩ := exists_level_factor_snd (fun p : Gal(L/K) × Gal(L/K) => f p.2)
    (hf.comp_continuous continuous_snd)
  refine ⟨Finset.univ.image fun i => (Module.finBasis K E i : L), fun σ τ h => ?_⟩
  refine hE 1 σ τ (AlgEquiv.toLinearMap_injective
    ((Module.finBasis K E).ext fun i => Subtype.ext ?_))
  simpa only [AlgEquiv.toLinearMap_apply, AlgEquiv.restrictNormalHom_apply] using
    h (Module.finBasis K E i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end Factor

section WeightedPerm

variable {L n : Type*} [Field L] [Fintype n] [DecidableEq n]

/-- The invertible matrix sending the `j`-th basis vector to `w j` times the `p j`-th one: a
permutation matrix with unit weights. These are the matrices of the regular representation of a
crossed product. -/
private def weightedPerm (p : Equiv.Perm n) (w : n → Lˣ) : GL n L where
  val i j := if i = p j then w j else 0
  inv i j := if j = p i then (w i)⁻¹ else 0
  val_inv := by
    refine Matrix.ext fun i j => ?_
    change (∑ k, (if i = p k then (w k : L) else 0) *
      (if j = p k then ((w k)⁻¹ : L) else 0)) = _
    rw [Finset.sum_eq_single (p.symm i)]
    · by_cases h : i = j <;> simp [h, eq_comm, Matrix.one_apply]
    · intro k _ hk
      have h : i ≠ p k := fun he =>
        hk ((p.symm_apply_apply k).symm.trans (congrArg p.symm he).symm)
      simp [h]
    · simp
  inv_val := by
    refine Matrix.ext fun i j => ?_
    change (∑ k, (if k = p i then ((w i)⁻¹ : L) else 0) *
      (if k = p j then (w j : L) else 0)) = _
    rw [Finset.sum_eq_single (p i)]
    · by_cases h : i = j <;> simp [h, Matrix.one_apply]
    · intro k _ hk
      simp [hk]
    · simp

/-- Weighted permutation matrices multiply by composing the permutations and transporting the
weights. -/
private theorem weightedPerm_mul (p q : Equiv.Perm n) (w v : n → Lˣ) :
    weightedPerm p w * weightedPerm q v =
      weightedPerm (p * q) fun j => w (q j) * v j := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (∑ k, (if i = p k then (w k : L) else 0) *
    (if k = q j then (v j : L) else 0)) = _
  rw [Finset.sum_eq_single (q j)]
  · by_cases h : i = p (q j) <;> simp [weightedPerm, h, Equiv.Perm.mul_apply]
  · intro k _ hk
    simp [hk]
  · simp

/-- Entrywise application of a ring homomorphism acts on the weights only. -/
private theorem weightedPerm_map {M : Type*} [Field M] (p : Equiv.Perm n) (w : n → Lˣ)
    (σ : L →+* M) :
    Matrix.GeneralLinearGroup.map σ (weightedPerm p w) =
      weightedPerm p fun j => Units.map σ.toMonoidHom (w j) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change σ (if i = p j then (w j : L) else 0) = _
  by_cases h : i = p j <;> simp [weightedPerm, h]

/-- Scalar matrices are central, so a scalar may be pulled out of a product of two factors each
carrying one. -/
private theorem scalar_mul_mul_scalar_mul (a e : Lˣ) (x y : GL n L) :
    Matrix.GeneralLinearGroup.scalar n a * x *
        (Matrix.GeneralLinearGroup.scalar n e * y) =
      Matrix.GeneralLinearGroup.scalar n (a * e) * (x * y) := by
  have h : x * Matrix.GeneralLinearGroup.scalar n e =
      Matrix.GeneralLinearGroup.scalar n e * x := (scalar_comm e x).symm
  calc Matrix.GeneralLinearGroup.scalar n a * x * (Matrix.GeneralLinearGroup.scalar n e * y)
      = Matrix.GeneralLinearGroup.scalar n a * (x * Matrix.GeneralLinearGroup.scalar n e) * y := by
        group
    _ = Matrix.GeneralLinearGroup.scalar n a * (Matrix.GeneralLinearGroup.scalar n e * x) * y := by
        rw [h]
    _ = _ := by rw [map_mul]; group

/-- The same identity with the scalar of the second factor sitting inside the product. -/
private theorem scalar_mul_mul_scalar_mul' (a e : Lˣ) (x y : GL n L) :
    Matrix.GeneralLinearGroup.scalar n a *
        (x * Matrix.GeneralLinearGroup.scalar n e * y) =
      Matrix.GeneralLinearGroup.scalar n (a * e) * (x * y) := by
  rw [← scalar_mul_mul_scalar_mul a e x y]
  group

/-- Multiplying by a scalar matrix scales the weights. -/
private theorem scalar_mul_weightedPerm (a : Lˣ) (p : Equiv.Perm n) (w : n → Lˣ) :
    Matrix.GeneralLinearGroup.scalar n a * weightedPerm p w =
      weightedPerm p fun j => a * w j := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (Matrix.scalar n (a : L) * (weightedPerm p w : Matrix n n L)) i j = _
  simp only [Matrix.mul_apply, Matrix.scalar]
  by_cases h : i = p j <;> simp [weightedPerm, h]

end WeightedPerm

universe u v

section General

variable (K : Type u) [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

section Trivial

/-- The trivial projective Galois cocycle of degree `d`. -/
private def trivialPGLCocycle (d : ℕ) : PGLCocycle K Ksep d where
  toFun _ := 1
  map_mul _ _ := by simp
  continuous := ⟨∅, fun _ _ _ => rfl⟩

/-- A projective cocycle with trivial connecting class is cohomologous to the trivial cocycle.
Multiplying a locally constant lift by the `1`-cochain trivialising its scalar defect produces a
locally constant `GL_d`-valued crossed homomorphism, and Hilbert 90 makes that a coboundary. -/
private theorem pglCocycle_isCohomologous_trivial (d : ℕ) (hd : 0 < d)
    (g : PGLCocycle K Ksep d) (hg : pglConnectingMap hd (Quotient.mk _ g) = 1) :
    PGLCocycle.IsCohomologous g (trivialPGLCocycle K Ksep d) := by
  have hUmk : ∀ σ, Matrix.ProjGenLinGroup.mk (pglCocycleLift g σ) = g.toFun σ :=
    mk_pglCocycleLift g
  have hUlc : IsLocallyConstant (pglCocycleLift g) := isLocallyConstant_pglCocycleLift g
  have hc (σ τ : Gal(Ksep/K)) :
      Matrix.GeneralLinearGroup.scalar (Fin d)
          ((liftTwoCocycle hd g (pglCocycleLift g) hUmk hUlc :
            Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ)) =
        (pglCocycleLift g σ)⁻¹ * pglCocycleLift g (σ * τ) *
          Matrix.GeneralLinearGroup.map
            (MulSemiringAction.toRingHom Gal(Ksep/K) Ksep σ) (pglCocycleLift g τ)⁻¹ :=
    scalar_liftTwoCocycle hd g (pglCocycleLift g) hUmk hUlc σ τ
  obtain ⟨b, hblc, hb⟩ := (mem_twoCoboundaries_iff _).1 ((twoCohomologyClass_eq_one_iff _).1
    ((pglConnectingMap_mk hd g (pglCocycleLift g) hUmk hUlc).symm.trans hg))
  -- the rescaled lift `V σ = b σ · g̃_σ` is an honest `GL_d`-valued crossed homomorphism
  have hVlc : IsLocallyConstant fun σ : Gal(Ksep/K) =>
      Matrix.GeneralLinearGroup.scalar (Fin d) (b σ) * pglCocycleLift g σ :=
    hblc.comp₂ hUlc fun a x => Matrix.GeneralLinearGroup.scalar (Fin d) a * x
  have hV : ∀ σ τ : Gal(Ksep/K),
      Matrix.GeneralLinearGroup.scalar (Fin d) (b (σ * τ)) * pglCocycleLift g (σ * τ) =
        Matrix.GeneralLinearGroup.scalar (Fin d) (b σ) * pglCocycleLift g σ *
          Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom Gal(Ksep/K) Ksep σ)
            (Matrix.GeneralLinearGroup.scalar (Fin d) (b τ) * pglCocycleLift g τ) := by
    intro σ τ
    have hlift : pglCocycleLift g (σ * τ) = pglCocycleLift g σ *
        Matrix.GeneralLinearGroup.scalar (Fin d)
          ((liftTwoCocycle hd g (pglCocycleLift g) hUmk hUlc :
            Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ)) *
        Matrix.GeneralLinearGroup.map
          (MulSemiringAction.toRingHom Gal(Ksep/K) Ksep σ) (pglCocycleLift g τ) := by
      rw [hc σ τ, map_inv]
      group
    have hunits : b (σ * τ) *
        (liftTwoCocycle hd g (pglCocycleLift g) hUmk hUlc :
          Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ) = b σ * (σ • b τ) := by
      rw [← hb σ τ, div_eq_mul_inv]
      calc b (σ * τ) * (σ • b τ * (b (σ * τ))⁻¹ * b σ)
          = b (σ * τ) * (b (σ * τ))⁻¹ * (b σ * (σ • b τ)) := by ac_rfl
        _ = _ := by rw [mul_inv_cancel, one_mul]
    rw [hlift, map_mul, Matrix.GeneralLinearGroup.map_scalar, units_map_toRingHom,
      scalar_mul_mul_scalar_mul, scalar_mul_mul_scalar_mul', hunits]
  obtain ⟨B, hB⟩ := exists_eq_mul_map_of_isMulCocycle₁ _ hVlc hV
  refine ⟨Matrix.ProjGenLinGroup.mk B, fun σ => ?_⟩
  have hVmk : Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin d) (b σ) * pglCocycleLift g σ) = g.toFun σ := by
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul, hUmk]
  have h := congrArg Matrix.ProjGenLinGroup.mk (hB σ)
  rw [map_mul, ← Matrix.ProjGenLinGroup.map_mk, hVmk, toRingHom_eq] at h
  change (1 : PGL(Fin d, Ksep)) = _
  rw [mul_assoc, h]
  simp

/-- The fixed algebra of the trivial cocycle is the matrix algebra over the ground field. -/
private def fixedTrivialMatrixHom (d : ℕ) :
    Matrix (Fin d) (Fin d) K →ₐ[K]
      cocycleFixedMatrixAlgebra K Ksep d (trivialPGLCocycle K Ksep d) :=
  AlgHom.codRestrict (AlgHom.mapMatrix (Algebra.ofId K Ksep)) _ fun M => by
    rw [mem_cocycleFixedMatrixAlgebra_iff]
    intro σ
    refine Matrix.ext fun i j => ?_
    simp [cocycleMatrixGaloisAut, trivialPGLCocycle, matrixGaloisAut, σ.commutes]

private theorem fixedTrivialMatrixHom_bijective (d : ℕ) :
    Function.Bijective (fixedTrivialMatrixHom K Ksep d) := by
  classical
  refine ⟨fun M N h => Matrix.ext fun i j => (algebraMap K Ksep).injective
    (congrFun (congrFun (congrArg Subtype.val h) i) j), fun M => ?_⟩
  have h (i j : Fin d) :
      ∃ a : K, algebraMap K Ksep a = (M : Matrix (Fin d) (Fin d) Ksep) i j := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := Ksep) _).2 fun σ => ?_
    have hh := congrArg (fun T : Matrix (Fin d) (Fin d) Ksep => T i j)
      ((mem_cocycleFixedMatrixAlgebra_iff K Ksep d (trivialPGLCocycle K Ksep d) M.1).1 M.2 σ)
    simpa [cocycleMatrixGaloisAut, trivialPGLCocycle, matrixGaloisAut] using hh
  choose a ha using h
  exact ⟨a, Subtype.ext (Matrix.ext fun i j => ha i j)⟩

/-- A central simple algebra with trivial class is a matrix algebra over the ground field: its
projective cocycle is cohomologous to the trivial one, and the fixed algebra of the trivial
cocycle is a matrix algebra. -/
private theorem exists_matrix_algEquiv_of_brauerDeltaOfCSA_eq_one (A : CSA.{u, v} K)
    (hA : brauerDeltaOfCSA K Ksep A = 1) :
    ∃ d : ℕ, 0 < d ∧ Nonempty (A ≃ₐ[K] Matrix (Fin d) (Fin d) K) := by
  have hd : 0 < Algebra.IsCentralSimple.degree K A := Algebra.IsCentralSimple.degree_pos K A
  obtain ⟨e⟩ := centralSimpleAlgebraOfDegree_splitEquiv K Ksep
    (Algebra.IsCentralSimple.degree K A) ⟨A, rfl⟩
  rw [brauerDeltaOfCSA_eq_split K Ksep A _ hd e] at hA
  obtain ⟨b, hb⟩ := pglCocycle_isCohomologous_trivial K Ksep _ hd _ hA
  exact ⟨_, hd, ⟨(AlgEquiv.ofBijective (splitToFixedMatrixHom K Ksep A _ hd.ne' e)
    (splitToFixedMatrixHom_bijective K Ksep A _ hd.ne' e)).trans
    ((AlgEquiv.ofBijective (cohomologousFixedMatrixHom K Ksep _ _ _ b hb)
      (cohomologousFixedMatrixHom_bijective K Ksep _ _ _ b hb)).trans
      (AlgEquiv.ofBijective (fixedTrivialMatrixHom K Ksep _)
        (fixedTrivialMatrixHom_bijective K Ksep _)).symm)⟩⟩

end Trivial

section Realization

/-- **Every locally constant `2`-cocycle is the scalar defect of a projective cocycle.** The
cocycle factors in its second variable through a finite Galois level `Γ`; the weighted
permutation matrices of the regular representation of the crossed product, indexed by `Γ`, lift
the resulting projective cocycle with exactly the given scalar defect. -/
private theorem exists_pglCocycle_connectingMap_eq (c : twoCocycles K Ksep) :
    ∃ (d : ℕ) (hd : 0 < d) (g : PGLCocycle K Ksep d),
      pglConnectingMap hd (Quotient.mk _ g) = twoCohomologyClass c := by
  classical
  have hclc : IsLocallyConstant (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) :=
    isLocallyConstant_of_mem_twoCocycles c
  obtain ⟨E, hE⟩ := exists_level_factor_snd (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) hclc
  let r : Gal(Ksep/K) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  obtain ⟨s, hs⟩ : ∃ s : (E ≃ₐ[K] E) → Gal(Ksep/K), ∀ γ, r (s γ) = γ :=
    (AlgEquiv.restrictNormalHom_surjective Ksep (F := K) (K₁ := E)).hasRightInverse
  have hW : ∀ σ τ : Gal(Ksep/K),
      weightedPerm (Equiv.mulLeft (r (σ * τ)))
          (fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ * τ, s γ))⁻¹) =
        Matrix.GeneralLinearGroup.scalar (E ≃ₐ[K] E)
            ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ)) *
          (weightedPerm (Equiv.mulLeft (r σ))
              (fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹) *
            Matrix.GeneralLinearGroup.map
              (MulSemiringAction.toRingHom Gal(Ksep/K) Ksep σ)
              (weightedPerm (Equiv.mulLeft (r τ))
                fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (τ, s γ))⁻¹)) := by
    intro σ τ
    rw [weightedPerm_map, weightedPerm_mul, scalar_mul_weightedPerm]
    have hp : Equiv.mulLeft (r (σ * τ)) = Equiv.mulLeft (r σ) * Equiv.mulLeft (r τ) := by
      ext γ; simp
    rw [hp]
    refine congrArg _ (funext fun γ => ?_)
    have hf : (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s (r τ * γ)) =
        (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ * s γ) :=
      hE σ _ _ (by change r _ = r _; simp [hs])
    change ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ * τ, s γ))⁻¹ =
      (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ) *
        (((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s (r τ * γ)))⁻¹ *
          σ • ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (τ, s γ))⁻¹)
    rw [hf, smul_inv']
    calc
      _ = (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ) *
            ((σ • (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (τ, s γ)) *
              (c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ * s γ))⁻¹ := by
          rw [← isMulCocycle₂_of_mem_twoCocycles c σ τ (s γ)]; group
      _ = _ := by group
  have hWlc : IsLocallyConstant fun σ : Gal(Ksep/K) =>
      weightedPerm (Equiv.mulLeft (r σ))
        (fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹) := by
    have hrlc : IsLocallyConstant r :=
      (IsLocallyConstant.iff_continuous _).2
        (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
    have hwlc : IsLocallyConstant fun σ : Gal(Ksep/K) =>
        (fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹ :
          (E ≃ₐ[K] E) → Ksepˣ) :=
      (LocallyConstant.unflip fun γ : E ≃ₐ[K] E =>
        (⟨fun σ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹,
          (hclc.comp_continuous (continuous_id.prodMk continuous_const)).comp
            (Inv.inv : Ksepˣ → Ksepˣ)⟩ :
              LocallyConstant Gal(Ksep/K) Ksepˣ)).isLocallyConstant
    exact hrlc.comp₂ hwlc fun γ w => weightedPerm (Equiv.mulLeft γ) w
  have hUlc : IsLocallyConstant fun σ : Gal(Ksep/K) =>
      glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))
        (weightedPerm (Equiv.mulLeft (r σ))
          fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹) :=
    hWlc.comp (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E)))
  have hU : ∀ σ τ : Gal(Ksep/K),
      glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))
          (weightedPerm (Equiv.mulLeft (r (σ * τ)))
            fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ * τ, s γ))⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin (Fintype.card (E ≃ₐ[K] E)))
            ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, τ)) *
          (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))
              (weightedPerm (Equiv.mulLeft (r σ))
                fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹) *
            Matrix.GeneralLinearGroup.map
              (MulSemiringAction.toRingHom Gal(Ksep/K) Ksep σ)
              (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))
                (weightedPerm (Equiv.mulLeft (r τ))
                  fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (τ, s γ))⁻¹))) := by
    intro σ τ
    simpa only [map_mul, glReindex_scalar, glReindex_map] using
      congrArg (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))) (hW σ τ)
  refine ⟨Fintype.card (E ≃ₐ[K] E), Fintype.card_pos,
    { toFun := fun σ => Matrix.ProjGenLinGroup.mk
        (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E))
          (weightedPerm (Equiv.mulLeft (r σ))
            fun γ => ((c : Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ) (σ, s γ))⁻¹))
      map_mul := fun σ τ => by
        rw [hU, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul, map_mul,
          ← Matrix.ProjGenLinGroup.map_mk, toRingHom_eq]
      continuous := exists_finset_determines _ (hUlc.comp Matrix.ProjGenLinGroup.mk) },
    pglConnectingMap_eq_of_scalar_defect Fintype.card_pos _ _ (fun _ => rfl) hUlc c fun σ τ => ?_⟩
  have h := hU σ τ
  rw [← mul_assoc, scalar_comm _ (glReindex Ksep (Fintype.equivFin (E ≃ₐ[K] E)) _)] at h
  simp only [liftDefect]
  rw [h, map_inv]
  group

end Realization

section Bijective

/-- **`δ` is surjective.** Every class in `H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` is the class of a locally
constant cocycle, that cocycle is the scalar defect of a projective cocycle, and the
classification of tag 03R6 realises the projective class by a central simple algebra. -/
@[stacks 03R7 "δ is surjective", sga "4½ Arcata 3.1.2" "δ is surjective"]
theorem brauerDelta_surjective :
    Function.Surjective (brauerDelta K Ksep : BrauerGroup.{u, v} K → TwoCohomology K Ksep) := by
  intro x
  obtain ⟨c, rfl⟩ := twoCohomologyClass_surjective x
  obtain ⟨d, hd, g, hg⟩ := exists_pglCocycle_connectingMap_eq K Ksep c
  obtain ⟨a, ha⟩ := (centralSimpleAlgebraClassEquivPGLH1 K Ksep d hd.ne').surjective
    (Quotient.mk _ g)
  obtain ⟨A, rfl⟩ := Quotient.mk_surjective a
  refine ⟨Quotient.mk _ A.1, ?_⟩
  obtain ⟨e⟩ := centralSimpleAlgebraOfDegree_splitEquiv K Ksep d A
  rw [brauerDelta_mk, brauerDeltaOfCSA_eq_split K Ksep A.1 d hd e,
    ← classification_eq_split K Ksep d hd.ne' A e, ha, hg]

/-- A split central simple algebra has trivial class. -/
private theorem brauerDeltaOfCSA_eq_one_of_algEquiv_matrix (A : CSA.{u, v} K) (d : ℕ)
    (hd : 0 < d) (e : A ≃ₐ[K] Matrix (Fin d) (Fin d) K) :
    brauerDeltaOfCSA K Ksep A = 1 := by
  rw [brauerDeltaOfCSA_eq_split K Ksep A d hd
    ((tensorAlgEquivOfAlgEquiv K Ksep _ _ e).trans (matrixSplitEquiv K Ksep d))]
  have h : (Quotient.mk _ (splitPGLCocycle K Ksep d hd.ne' A
        ((tensorAlgEquivOfAlgEquiv K Ksep _ _ e).trans (matrixSplitEquiv K Ksep d))) :
          PGLH1 K Ksep d) =
      Quotient.mk _ (splitPGLCocycle K Ksep d hd.ne' (Matrix (Fin d) (Fin d) K)
        (matrixSplitEquiv K Ksep d)) := by
    refine Quotient.sound (Relation.EqvGen.rel _ _ ⟨1, fun σ => ?_⟩)
    simpa only [inv_one, one_mul, map_one, mul_one, splitPGLCocycle] using
      (splitTransportPGL_congr K Ksep d hd.ne' _ _ e (matrixSplitEquiv K Ksep d) σ).symm
  rw [h]
  exact pglConnectingMap_matrixSplit K Ksep d hd

/-- The opposite algebra has the inverse class, because `A ⊗ Aᵐᵒᵖ` is split. -/
private theorem brauerDeltaOfCSA_op (A : CSA.{u, v} K) :
    brauerDeltaOfCSA K Ksep (⟨.of K Aᵐᵒᵖ⟩ : CSA.{u, v} K) =
      (brauerDeltaOfCSA K Ksep A)⁻¹ := by
  have h := brauerDeltaOfCSA_eq_one_of_algEquiv_matrix K Ksep
    (⟨.of K (A ⊗[K] Aᵐᵒᵖ)⟩ : CSA.{u, v} K) (Module.finrank K A) Module.finrank_pos
    (centralSimpleTensorOp _ rfl)
  rw [brauerDeltaOfCSA_tensor K Ksep A (⟨.of K Aᵐᵒᵖ⟩ : CSA.{u, v} K)] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **`δ` is injective.** If two central simple algebras have the same class then `A ⊗ Bᵐᵒᵖ` has
trivial class, hence is a matrix algebra over `K`, and that exhibits a Brauer equivalence between
`A` and `B`. -/
@[stacks 03R7 "δ is injective", sga "4½ Arcata 3.1.2" "δ is injective"]
theorem brauerDelta_injective :
    Function.Injective (brauerDelta K Ksep : BrauerGroup.{u, v} K → TwoCohomology K Ksep) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun A B h => ?_
  rw [brauerDelta_mk, brauerDelta_mk] at h
  have hC : brauerDeltaOfCSA K Ksep (⟨.of K (A ⊗[K] Bᵐᵒᵖ)⟩ : CSA.{u, v} K) = 1 := by
    rw [brauerDeltaOfCSA_tensor K Ksep A (⟨.of K Bᵐᵒᵖ⟩ : CSA.{u, v} K),
      brauerDeltaOfCSA_op, h, mul_inv_cancel]
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_matrix_algEquiv_of_brauerDeltaOfCSA_eq_one K Ksep _ hC
  refine Quotient.sound ⟨Module.finrank K B, d, Module.finrank_pos.ne', hd.ne', ?_⟩
  exact ⟨(matrixEquivTensor (Fin (Module.finrank K B)) K A).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A)
      (opTensorCentralSimple (Module.finrank K B) rfl).symm).trans
      ((Algebra.TensorProduct.assoc K K K A Bᵐᵒᵖ B).symm.trans
        ((Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[K] B)).trans
          ((Algebra.TensorProduct.comm K (Matrix (Fin d) (Fin d) K) B).trans
            (matrixEquivTensor (Fin d) K B).symm))))⟩

/-- **The map `δ` of tag 03R7 is bijective.** -/
@[stacks 03R7 "δ is bijective"]
theorem brauerDelta_bijective :
    Function.Bijective (brauerDelta K Ksep : BrauerGroup.{u, v} K → TwoCohomology K Ksep) :=
  ⟨brauerDelta_injective K Ksep, brauerDelta_surjective K Ksep⟩

end Bijective

end General

section Bundled

variable (K : Type u) [Field K] (Ksep : Type u) [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- **Stacks Project, Tag 03R7.** The map `δ : Br(K) → H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` is an
isomorphism of groups. As for `brauerDeltaHom`, the commutative group structure on the Brauer
group is available for central simple algebras in the universe of the ground field, so this
bundling is stated with `Kˢᵉᵖ` in that universe too; `brauerDelta_injective` and
`brauerDelta_surjective` are the two halves without that restriction. -/
@[stacks 03R7 "δ is an isomorphism", sga "4½ Arcata 3.1.2" "δ is an isomorphism"]
def brauerDeltaEquiv : BrauerGroup.{u, u} K ≃* TwoCohomology K Ksep :=
  MulEquiv.ofBijective (brauerDeltaHom K Ksep) (brauerDelta_bijective K Ksep)

/-- The isomorphism `brauerDeltaEquiv` sends a Brauer class `x` to `brauerDelta K Ksep x`. -/
@[simp]
theorem brauerDeltaEquiv_apply (x : BrauerGroup.{u, u} K) :
    brauerDeltaEquiv K Ksep x = brauerDelta K Ksep x :=
  rfl

end Bundled

end Stacks.GaloisCohomology
