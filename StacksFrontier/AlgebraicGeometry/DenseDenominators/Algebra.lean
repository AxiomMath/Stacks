module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Ideal
public import StacksFrontier.RingTheory.FiniteAlgebraPresentation

/-!
# The algebra of denominators of a finite algebra over an open subset

Let `Y` be a scheme, `Ω` an open subset, and `S` an algebra over the sections of the structure
sheaf on `Ω`, presented by a finite spanning family `β` with structure constants and monic
equations. For an open `W` of `Y` this file builds the subring

  `𝒪(W) + ℐ(W)·β₁ + ⋯ + ℐ(W)·βₙ`

of the base change `𝒪(W ⊓ Ω) ⊗ S`, where `ℐ` is the ideal of denominators of the coefficients
occurring in the presentation. It is a subring because `ℐ` is an ideal and the structure
constants are among the sections whose denominators `ℐ` is made of; over an open subset of `Ω`
it is the whole base change.

## Main results

* `Stacks.DenseDenominators.sub` is the subring.
* `Stacks.DenseDenominators.sub_eq_top` identifies it with the whole base change over an open
  subset of `Ω`.
* `Stacks.DenseDenominators.ambRes_mem_sub` is its compatibility with restriction.

## Implementation notes

The base change is taken with the sections over `W ⊓ Ω` on the left, so that it is an algebra
over them and the commutative ring structure comes from `Mathlib.RingTheory.TensorProduct.Basic`
rather than being built by hand; the algebra structure of those sections over the sections on
`Ω` is restriction, installed as a local instance.

Working inside a ring that already exists is what makes the structure constants harmless. A
presentation chooses them, and different choices give different coefficient families, but no
identity among them ever has to be proved: associativity and commutativity are inherited from
the base change, and the structure constants enter only through the single statement that a
product of two generators is a combination of generators.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.FiniteAlgebraPresentation TensorProduct

universe u

namespace Stacks.DenseDenominators

variable {Y : Scheme.{u}} {Ω : Y.Opens}

/-- The sections over `W ⊓ Ω` form an algebra over the sections over `Ω`, by restriction. -/
local instance algebraInf (W : Y.Opens) : Algebra Γ(Y, Ω) Γ(Y, W ⊓ Ω) :=
  (resHom (inf_le_right : W ⊓ Ω ≤ Ω)).toAlgebra

/-- The algebra map from the sections over `Ω` to those over `W ⊓ Ω` is restriction. -/
lemma algebraMap_inf (W : Y.Opens) (a : Γ(Y, Ω)) :
    algebraMap Γ(Y, Ω) Γ(Y, W ⊓ Ω) a = resHom (inf_le_right : W ⊓ Ω ≤ Ω) a := rfl

/-- Scalar multiplication by a section over `Ω` is multiplication by its restriction. -/
lemma smul_inf (W : Y.Opens) (a : Γ(Y, Ω)) (t : Γ(Y, W ⊓ Ω)) :
    a • t = resHom (inf_le_right : W ⊓ Ω ≤ Ω) a * t := rfl

section Ambient

variable (Ω) (S : Type u) [CommRing S] [Algebra Γ(Y, Ω) S]

/-- The ambient ring over `W`: the base change of `S` to the sections over `W ⊓ Ω`. -/
abbrev amb (W : Y.Opens) : Type u := Γ(Y, W ⊓ Ω) ⊗[Γ(Y, Ω)] S

/-- Restriction of the sections over `W ⊓ Ω` along `V ≤ W`, as an algebra homomorphism over the
sections on `Ω`. -/
def resAlgHom {V W : Y.Opens} (h : V ≤ W) : Γ(Y, W ⊓ Ω) →ₐ[Γ(Y, Ω)] Γ(Y, V ⊓ Ω) where
  __ := resHom (inf_le_inf h (le_refl Ω))
  commutes' a := by
    simp only [algebraMap_inf]
    exact resHom_resHom _ _ a

/-- On sections, the restriction algebra homomorphism is restriction. -/
@[simp] lemma resAlgHom_apply {V W : Y.Opens} (h : V ≤ W) (t : Γ(Y, W ⊓ Ω)) :
    resAlgHom Ω h t = resHom (inf_le_inf h (le_refl Ω)) t := rfl

/-- Restriction in the ambient ring. -/
def ambRes {V W : Y.Opens} (h : V ≤ W) : amb Ω S W →+* amb Ω S V :=
  (Algebra.TensorProduct.map (resAlgHom Ω h) (AlgHom.id Γ(Y, Ω) S)).toRingHom

/-- Restriction in the ambient ring acts on a pure tensor through its first factor. -/
@[simp] lemma ambRes_tmul {V W : Y.Opens} (h : V ≤ W) (t : Γ(Y, W ⊓ Ω)) (s : S) :
    ambRes Ω S h (t ⊗ₜ s) = resHom (inf_le_inf h (le_refl Ω)) t ⊗ₜ s := rfl

/-- Restriction in the ambient ring along `W ≤ W` is the identity. -/
lemma ambRes_self {W : Y.Opens} (x : amb Ω S W) : ambRes Ω S (le_refl W) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul t s => rw [ambRes_tmul, resHom_self' _ t]
  | add x y hx hy => rw [map_add, hx, hy]

/-- Restriction in the ambient ring is compatible with composition of inclusions. -/
lemma ambRes_ambRes {U V W : Y.Opens} (h : V ≤ W) (h' : U ≤ V) (x : amb Ω S W) :
    ambRes Ω S h' (ambRes Ω S h x) = ambRes Ω S (h'.trans h) x := by
  induction x using TensorProduct.inductionOn with
  | tmul t s => rw [ambRes_tmul, ambRes_tmul, ambRes_tmul, resHom_resHom]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image of the sections over `W` in the ambient ring. -/
def toAmb (W : Y.Opens) : Γ(Y, W) →+* amb Ω S W :=
  (algebraMap Γ(Y, W ⊓ Ω) (amb Ω S W)).comp (resHom (inf_le_left : W ⊓ Ω ≤ W))

/-- The image of a section over `W` in the ambient ring is its restriction tensored with `1`. -/
lemma toAmb_apply (W : Y.Opens) (t : Γ(Y, W)) :
    toAmb Ω S W t = resHom (inf_le_left : W ⊓ Ω ≤ W) t ⊗ₜ (1 : S) := rfl

/-- The image of the sections in the ambient ring is compatible with restriction. -/
lemma ambRes_toAmb {V W : Y.Opens} (h : V ≤ W) (t : Γ(Y, W)) :
    ambRes Ω S h (toAmb Ω S W t) = toAmb Ω S V (resHom h t) := by
  rw [toAmb_apply, ambRes_tmul, toAmb_apply, resHom_resHom, resHom_resHom]

end Ambient

section Subring

variable {S : Type u} [CommRing S] [Algebra Γ(Y, Ω) S] (P : Presentation Γ(Y, Ω) S)

/-- A scalar from the sections over `Ω` moves across the tensor sign as its restriction. -/
private theorem tmul_smul_eq_resHom_mul_tmul {W : Y.Opens} (t : Γ(Y, W ⊓ Ω)) (a : Γ(Y, Ω))
    (s : S) : t ⊗ₜ[Γ(Y, Ω)] (a • s) = (resHom (inf_le_right : W ⊓ Ω ≤ Ω) a * t) ⊗ₜ s := by
  rw [← smul_tmul, smul_inf]

/-- Multiplication of a generator of the presentation by a section over `W`, as an additive map
into the ambient ring. -/
def genMul (W : Y.Opens) (l : P.L) : Γ(Y, W) →+ amb Ω S W where
  toFun ρ := resHom (inf_le_left : W ⊓ Ω ≤ W) ρ ⊗ₜ P.gen l
  map_zero' := by rw [map_zero, zero_tmul]
  map_add' ρ σ := by rw [map_add, add_tmul]

/-- The multiple of a generator by `ρ` is the restriction of `ρ` tensored with the generator. -/
lemma genMul_apply (W : Y.Opens) (l : P.L) (ρ : Γ(Y, W)) :
    genMul P W l ρ = resHom (inf_le_left : W ⊓ Ω ≤ W) ρ ⊗ₜ P.gen l := rfl

/-- The image of a section `u` times the multiple of a generator by `ρ` is its multiple by
`u * ρ`. -/
lemma toAmb_mul_genMul (W : Y.Opens) (u ρ : Γ(Y, W)) (l : P.L) :
    toAmb Ω S W u * genMul P W l ρ = genMul P W l (u * ρ) := by
  rw [toAmb_apply, genMul_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, genMul_apply,
    map_mul]

/-- Multiples of generators are compatible with restriction. -/
lemma ambRes_genMul {V W : Y.Opens} (h : V ≤ W) (ρ : Γ(Y, W)) (l : P.L) :
    ambRes Ω S h (genMul P W l ρ) = genMul P V l (resHom h ρ) := by
  rw [genMul_apply, ambRes_tmul, genMul_apply, resHom_resHom, resHom_resHom]

/-- **The product of two multiples of generators by denominators.** It is a combination of
multiples of generators by denominators, because the structure constants are among the sections
whose denominators the ideal is made of. -/
lemma exists_genMul_mul_genMul {W : Y.Opens} {ρ σ : Γ(Y, W)}
    (hρ : ρ ∈ denom P.coeffFamily W) (hσ : σ ∈ denom P.coeffFamily W) (l l' : P.L) :
    ∃ τ : P.L → Γ(Y, W), (∀ j, τ j ∈ denom P.coeffFamily W) ∧
      genMul P W l ρ * genMul P W l' σ = ∑ j, genMul P W j (τ j) := by
  choose s hs using fun j => hσ (.inl (l, l', j))
  simp only [Presentation.coeffFamily_inl] at hs
  refine ⟨fun j => ρ * s j, fun j => Ideal.mul_mem_right _ _ hρ, ?_⟩
  rw [genMul_apply, genMul_apply, Algebra.TensorProduct.tmul_mul_tmul, P.cst_spec l l',
    tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tmul_smul_eq_resHom_mul_tmul, genMul_apply, map_mul, hs j]
  ring_nf

/-- The underlying additive subgroup of the algebra of denominators over `W`: the sections over
`W`, plus the multiples of the generators of the presentation by denominators. -/
def subAdd (W : Y.Opens) : AddSubgroup (amb Ω S W) where
  carrier := {γ | ∃ (u : Γ(Y, W)) (ρ : P.L → Γ(Y, W)),
    (∀ l, ρ l ∈ denom P.coeffFamily W) ∧ γ = toAmb Ω S W u + ∑ l, genMul P W l (ρ l)}
  zero_mem' := ⟨0, 0, fun _ => Submodule.zero_mem _, by simp⟩
  add_mem' {γ δ} := by
    rintro ⟨u, ρ, hρ, rfl⟩ ⟨u', ρ', hρ', rfl⟩
    refine ⟨u + u', ρ + ρ', fun l => Submodule.add_mem _ (hρ l) (hρ' l), ?_⟩
    rw [map_add, show ∑ l, genMul P W l ((ρ + ρ') l)
        = (∑ l, genMul P W l (ρ l)) + ∑ l, genMul P W l (ρ' l)
      from by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]]
    ring
  neg_mem' {γ} := by
    rintro ⟨u, ρ, hρ, rfl⟩
    refine ⟨-u, -ρ, fun l => Submodule.neg_mem _ (hρ l), ?_⟩
    rw [map_neg, show ∑ l, genMul P W l ((-ρ) l) = -∑ l, genMul P W l (ρ l)
      from by simp only [Pi.neg_apply, map_neg, Finset.sum_neg_distrib]]
    ring

/-- Membership in the underlying additive subgroup of the algebra of denominators. -/
lemma mem_subAdd_iff (W : Y.Opens) (γ : amb Ω S W) :
    γ ∈ subAdd P W ↔ ∃ (u : Γ(Y, W)) (ρ : P.L → Γ(Y, W)),
      (∀ l, ρ l ∈ denom P.coeffFamily W) ∧ γ = toAmb Ω S W u + ∑ l, genMul P W l (ρ l) :=
  Iff.rfl

/-- The image of a section over `W` lies in the underlying additive subgroup. -/
lemma toAmb_mem_subAdd (W : Y.Opens) (u : Γ(Y, W)) : toAmb Ω S W u ∈ subAdd P W :=
  ⟨u, 0, fun _ => Submodule.zero_mem _, by simp⟩

/-- A multiple of a generator by a denominator lies in the underlying additive subgroup. -/
lemma genMul_mem_subAdd {W : Y.Opens} {ρ : Γ(Y, W)} (hρ : ρ ∈ denom P.coeffFamily W)
    (l : P.L) : genMul P W l ρ ∈ subAdd P W := by
  classical
  refine ⟨0, Function.update 0 l ρ, fun j => ?_, ?_⟩
  · by_cases h : j = l
    · subst h
      simpa using hρ
    · simp [Function.update_of_ne h]
  · rw [map_zero, zero_add, Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
    · rw [Function.update_self]
    · intro j _ hj
      rw [Function.update_of_ne hj, Pi.zero_apply, map_zero]

/-- The additive subgroup is closed under multiplication: the four kinds of product of its two
kinds of element are each again of one of those kinds. -/
lemma mul_mem_subAdd {W : Y.Opens} {γ δ : amb Ω S W} (hγ : γ ∈ subAdd P W)
    (hδ : δ ∈ subAdd P W) : γ * δ ∈ subAdd P W := by
  obtain ⟨u, ρ, hρ, rfl⟩ := hγ
  obtain ⟨u', ρ', hρ', rfl⟩ := hδ
  have h2 : ∀ l' : P.L, toAmb Ω S W u * genMul P W l' (ρ' l') ∈ subAdd P W := fun l' => by
    rw [toAmb_mul_genMul]
    exact genMul_mem_subAdd P (Ideal.mul_mem_left _ _ (hρ' l')) l'
  have h3 : ∀ l : P.L, genMul P W l (ρ l) * toAmb Ω S W u' ∈ subAdd P W := fun l => by
    rw [mul_comm, toAmb_mul_genMul]
    exact genMul_mem_subAdd P (Ideal.mul_mem_left _ _ (hρ l)) l
  have h4 : ∀ l l' : P.L, genMul P W l (ρ l) * genMul P W l' (ρ' l') ∈ subAdd P W :=
    fun l l' => by
      obtain ⟨τ, hτ, heq⟩ := exists_genMul_mul_genMul P (hρ l) (hρ' l') l l'
      rw [heq]
      exact AddSubgroup.sum_mem _ fun j _ => genMul_mem_subAdd P (hτ j) j
  rw [add_mul, mul_add, mul_add]
  refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) (AddSubgroup.add_mem _ ?_ ?_)
  · rw [← map_mul]
    exact toAmb_mem_subAdd P W _
  · rw [Finset.mul_sum]
    exact AddSubgroup.sum_mem _ fun l' _ => h2 l'
  · rw [Finset.sum_mul]
    exact AddSubgroup.sum_mem _ fun l _ => h3 l
  · rw [Finset.sum_mul]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    rw [Finset.mul_sum]
    exact AddSubgroup.sum_mem _ fun l' _ => h4 l l'

/-- **The algebra of denominators over `W`**: the sections over `W`, plus the multiples of the
generators of the presentation by denominators. -/
def sub (W : Y.Opens) : Subring (amb Ω S W) :=
  { subAdd P W with
    one_mem' := ⟨1, 0, fun _ => Submodule.zero_mem _, by simp⟩
    mul_mem' := fun hγ hδ => mul_mem_subAdd P hγ hδ }

/-- Membership in the algebra of denominators. -/
lemma mem_sub_iff (W : Y.Opens) (γ : amb Ω S W) :
    γ ∈ sub P W ↔ ∃ (u : Γ(Y, W)) (ρ : P.L → Γ(Y, W)),
      (∀ l, ρ l ∈ denom P.coeffFamily W) ∧ γ = toAmb Ω S W u + ∑ l, genMul P W l (ρ l) :=
  Iff.rfl

/-- The image of a section over `W` lies in the algebra of denominators. -/
lemma toAmb_mem_sub (W : Y.Opens) (u : Γ(Y, W)) : toAmb Ω S W u ∈ sub P W :=
  toAmb_mem_subAdd P W u

/-- A multiple of a generator by a denominator lies in the algebra of denominators. -/
lemma genMul_mem_sub {W : Y.Opens} {ρ : Γ(Y, W)} (hρ : ρ ∈ denom P.coeffFamily W) (l : P.L) :
    genMul P W l ρ ∈ sub P W :=
  genMul_mem_subAdd P hρ l

/-- The algebra of denominators is compatible with restriction. -/
lemma ambRes_mem_sub {V W : Y.Opens} (h : V ≤ W) {γ : amb Ω S W} (hγ : γ ∈ sub P W) :
    ambRes Ω S h γ ∈ sub P V := by
  obtain ⟨u, ρ, hρ, rfl⟩ := hγ
  refine ⟨resHom h u, fun l => resHom h (ρ l), fun l => denom_res _ h (hρ l), ?_⟩
  rw [map_add, ambRes_toAmb, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => ambRes_genMul P h (ρ l) l)

/-- **Over an open subset of `Ω` the algebra of denominators is the whole base change.** The
ideal of denominators is everything there, and the generators of the presentation span. -/
lemma sub_eq_top {W : Y.Opens} (hW : W ≤ Ω) : sub P W = ⊤ := by
  refine eq_top_iff.mpr fun γ _ => ?_
  induction γ using TensorProduct.inductionOn with
  | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  | tmul t s =>
      obtain ⟨c, hc⟩ := P.spans s
      have key : t ⊗ₜ[Γ(Y, Ω)] s = ∑ l, genMul P W l
          (resHom (le_inf (le_refl W) hW) (resHom inf_le_right (c l) * t)) := by
        rw [hc, tmul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [tmul_smul_eq_resHom_mul_tmul, genMul_apply, resHom_resHom, resHom_self']
      rw [key]
      refine Subring.sum_mem _ fun l _ => genMul_mem_sub P ?_ l
      rw [denom_eq_top _ hW]
      exact Submodule.mem_top

/-- Restriction in the algebra of denominators. -/
def subRes {V W : Y.Opens} (h : V ≤ W) : sub P W →+* sub P V where
  toFun γ := ⟨ambRes Ω S h γ.1, ambRes_mem_sub P h γ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Restriction in the algebra of denominators is restriction in the ambient ring. -/
@[simp] lemma subRes_coe {V W : Y.Opens} (h : V ≤ W) (γ : sub P W) :
    ((subRes P h γ : sub P V) : amb Ω S V) = ambRes Ω S h γ.1 := rfl

/-- The structure morphism of the algebra of denominators over `W`. -/
def toSub (W : Y.Opens) : Γ(Y, W) →+* sub P W where
  toFun u := ⟨toAmb Ω S W u, toAmb_mem_sub P W u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The structure morphism of the algebra of denominators is the map to the ambient ring. -/
@[simp] lemma toSub_coe (W : Y.Opens) (u : Γ(Y, W)) :
    ((toSub P W u : sub P W) : amb Ω S W) = toAmb Ω S W u := rfl

/-- The structure morphism of the algebra of denominators is compatible with restriction. -/
lemma subRes_toSub {V W : Y.Opens} (h : V ≤ W) (u : Γ(Y, W)) :
    subRes P h (toSub P W u) = toSub P V (resHom h u) :=
  Subtype.ext (ambRes_toAmb Ω S h u)

/-! ### Integrality -/

/-- **A multiple of a generator by a denominator is integral over the sections of the base.**
The monic equation is the one the presentation records for the generator, with its `i`-th
coefficient multiplied by the `(d - 1 - i)`-th power of the denominator — which is a section
over `W` because the coefficients of the monic equations are among the sections whose
denominators the ideal is made of. -/
lemma isIntegralElem_genMul {W : Y.Opens} {ρ : Γ(Y, W)} (hρ : ρ ∈ denom P.coeffFamily W)
    (l : P.L) : (toAmb Ω S W).IsIntegralElem (genMul P W l ρ) := by
  classical
  choose s hs using fun i : Fin (P.deg l) => hρ (.inr ⟨l, i⟩)
  simp only [Presentation.coeffFamily_inr] at hs
  refine ⟨Polynomial.X ^ P.deg l + ∑ i : Fin (P.deg l),
      Polynomial.C (ρ ^ (P.deg l - 1 - (i : ℕ)) * s i) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  have hpow : ∀ i : ℕ, genMul P W l ρ ^ i
      = (resHom (inf_le_left : W ⊓ Ω ≤ W) ρ ^ i) ⊗ₜ[Γ(Y, Ω)] (P.gen l ^ i) := fun i => by
    rw [genMul_apply, Algebra.TensorProduct.tmul_pow]
  have hgen : P.gen l ^ P.deg l = -∑ i : Fin (P.deg l), P.coeff l i • P.gen l ^ (i : ℕ) :=
    eq_neg_of_add_eq_zero_left (P.monic l)
  rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have key : ∀ i : Fin (P.deg l),
      toAmb Ω S W (ρ ^ (P.deg l - 1 - (i : ℕ)) * s i) * genMul P W l ρ ^ (i : ℕ)
        = (resHom (inf_le_right : W ⊓ Ω ≤ Ω) (P.coeff l i) *
            resHom (inf_le_left : W ⊓ Ω ≤ W) ρ ^ P.deg l) ⊗ₜ[Γ(Y, Ω)] (P.gen l ^ (i : ℕ)) := by
    intro i
    have hi : (i : ℕ) < P.deg l := i.isLt
    have hsum : P.deg l - 1 - (i : ℕ) + 1 + (i : ℕ) = P.deg l := by omega
    rw [hpow, toAmb_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_pow, hs i]
    congr 1
    conv_rhs => rw [← hsum]
    ring
  have keyd : genMul P W l ρ ^ P.deg l
      = -∑ i : Fin (P.deg l), (resHom (inf_le_right : W ⊓ Ω ≤ Ω) (P.coeff l i) *
          resHom (inf_le_left : W ⊓ Ω ≤ W) ρ ^ P.deg l) ⊗ₜ[Γ(Y, Ω)] (P.gen l ^ (i : ℕ)) := by
    rw [hpow, hgen, tmul_neg, tmul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [tmul_smul_eq_resHom_mul_tmul]
  rw [keyd, Finset.sum_congr rfl fun i _ => key i, neg_add_cancel]

/-- The algebra structure of the algebra of denominators over the sections of the base. -/
local instance algebraSub (W : Y.Opens) : Algebra Γ(Y, W) (sub P W) := (toSub P W).toAlgebra

/-- The algebra map to the algebra of denominators is its structure morphism. -/
lemma algebraMap_sub (W : Y.Opens) (u : Γ(Y, W)) :
    algebraMap Γ(Y, W) (sub P W) u = toSub P W u := rfl

/-- Integrality transfers from the ambient ring to the subring, the inclusion being injective. -/
lemma isIntegralElem_toSub {W : Y.Opens} (γ : sub P W)
    (h : (toAmb Ω S W).IsIntegralElem (γ : amb Ω S W)) : (toSub P W).IsIntegralElem γ := by
  obtain ⟨p, hp, hp0⟩ := h
  refine ⟨p, hp, Subtype.ext ?_⟩
  have hcomp : (Subring.subtype (sub P W)).comp (toSub P W) = toAmb Ω S W :=
    RingHom.ext fun u => rfl
  have h2 := Polynomial.hom_eval₂ p (toSub P W) (Subring.subtype (sub P W)) γ
  rw [hcomp] at h2
  rw [ZeroMemClass.coe_zero]
  exact h2.trans hp0

/-- **The algebra of denominators is integral over the sections of the base.** It is generated
by the sections over `W`, which are in the image, and the multiples of the generators of the
presentation by denominators, which are integral. -/
lemma isIntegral_sub {W : Y.Opens} (γ : sub P W) : IsIntegral Γ(Y, W) γ := by
  classical
  obtain ⟨u, ρ, hρ, hγ⟩ := γ.2
  rw [← mem_integralClosure_iff]
  rw [show γ = algebraMap Γ(Y, W) (sub P W) u
      + ∑ l, (⟨genMul P W l (ρ l), genMul_mem_sub P (hρ l) l⟩ : sub P W)
    from Subtype.ext (by push_cast; exact hγ)]
  refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u)
    (Subalgebra.sum_mem _ fun l _ => ?_)
  rw [mem_integralClosure_iff]
  exact isIntegralElem_toSub P _ (isIntegralElem_genMul P (hρ l) l)

/-! ### Injectivity of the structure morphism -/

/-- **The structure morphism of the algebra of denominators is injective.** This is where the
density of `Ω` in a reduced `Y` is used: a section over `W` is determined by its restriction to
`W ⊓ Ω`, and that restriction is recovered from its image in the base change by any linear
functional on `S` sending `1` to `1`. -/
lemma injective_toAmb [IsReduced Y] (hΩ : Dense (Ω : Set Y)) (W : Y.Opens)
    (φ : S →ₗ[Γ(Y, Ω)] Γ(Y, Ω)) (hφ : φ 1 = 1) : Function.Injective (toAmb Ω S W) := by
  have hdense : (W : Set Y) ⊆ closure ((W ⊓ Ω : Y.Opens) : Set Y) := by
    intro x hx
    rw [mem_closure_iff]
    intro N hN hxN
    obtain ⟨y, hy⟩ := hΩ.inter_open_nonempty (N ∩ (W : Set Y)) (hN.inter W.isOpen) ⟨x, hxN, hx⟩
    exact ⟨y, hy.1.1, hy.1.2, hy.2⟩
  have hres : Function.Injective (resHom (inf_le_left : W ⊓ Ω ≤ W)) :=
    Stacks.DenseRestriction.injective_res _ hdense
  intro u v huv
  refine hres ?_
  have hmap := congrArg
    ((TensorProduct.rid Γ(Y, Ω) Γ(Y, W ⊓ Ω)).toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.id : Γ(Y, W ⊓ Ω) →ₗ[Γ(Y, Ω)] Γ(Y, W ⊓ Ω)) φ) huv
  simpa only [LinearMap.coe_comp, Function.comp_apply, toAmb_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, hφ, LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul] using hmap

/-- The structure morphism into the algebra of denominators is injective, for `Ω` dense in a
reduced `Y`. -/
lemma injective_toSub [IsReduced Y] (hΩ : Dense (Ω : Set Y)) (W : Y.Opens)
    (φ : S →ₗ[Γ(Y, Ω)] Γ(Y, Ω)) (hφ : φ 1 = 1) : Function.Injective (toSub P W) :=
  fun _ _ huv => injective_toAmb hΩ W φ hφ (congrArg Subtype.val huv)

end Subring

end Stacks.DenseDenominators

end
