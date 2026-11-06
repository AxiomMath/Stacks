module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Asymptotic Riemann–Roch

[Stacks, Tag 0BJ8]: let `k` be a field, let `X` be a scheme proper over `k` of dimension `d` and
let `𝓛` be an ample invertible `𝒪_X`-module.  Then

`dim_k Γ(X, 𝓛^{⊗ n}) = deg_𝓛(X)/d! ⬝ n^d + lower order terms`,

and the leading coefficient `deg_𝓛(X)/d!` is positive.

The source's proof is "this follows from the definitions, [Stacks, Tag 0BEV] and the vanishing of
higher cohomology [Stacks, Tag 0B5U]".  Spelled out:

* By [Stacks, Tag 0BEM] there is a `p ∈ ℚ[t]`, of degree at most `d`, with
  `p(n) = χ(X, 𝓛^{⊗ n})` for every `n : ℤ`.
* The polynomial `P(n_1, …, n_d) = p(n_1 + ⋯ + n_d)` takes the twisted Euler characteristics
  `χ(X, 𝓛^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛^{⊗ n_d})` as its values, because the twist is `𝓛^{⊗ ∑ n_j}`, and its
  total degree is at most `d`.  So by [Stacks, Tag 0BEP] the self-intersection number
  `(𝓛^d ⬝ X) = deg_𝓛(X)` is the coefficient of `n_1 ⋯ n_d` in `P`, which is `d!` times the
  coefficient of `t^d` in `p`.
* [Stacks, Tag 0B5U] gives an `N` beyond which all the higher cohomology of `𝓛^{⊗ n}` vanishes,
  so there `χ(X, 𝓛^{⊗ n}) = dim_k Γ(X, 𝓛^{⊗ n})`.  Splitting off the leading term of `p` gives
  the formula, with `P = p - (coeff of t^d) ⬝ t^d` as the lower order terms.
* Positivity of `deg_𝓛(X)/d!` is [Stacks, Tag 0BEV].

## Main definitions

* `AlgebraicGeometry.globalSectionsOverField`: `Γ(X, ℱ)` as a vector space over the ground
  field, the degree-zero companion of `AlgebraicGeometry.cohomologyOverField`.

## Main results

* `AlgebraicGeometry.degreeWithRespectTo_div_factorial_pos`: the leading coefficient
  `deg_𝓛(X)/d!` is positive.
* `AlgebraicGeometry.exists_degree_lt_eventually_finrank_globalSections_eq`: the asymptotic
  formula.
* `AlgebraicGeometry.asymptotic_riemann_roch`: **[Stacks, Tag 0BJ8]**, the two together.

## Implementation notes

**`deg_𝓛(X)` is `deg_𝓛` of `X` as a closed subscheme of itself.**  The degree
`AlgebraicGeometry.degreeWithRespectTo` of [Stacks, Tag 0BEW] is attached to a closed immersion
`i : Z ⟶ X`; the source's `deg_𝓛(X)` is the case `i = 𝟙 X`, which is a closed immersion because
it is an isomorphism.  The twists in the definition of the intersection number are then twists by
`𝓛|_X = (𝟙 X)^*𝓛`, and `AlgebraicGeometry.Scheme.Modules.pullbackId` identifies that with `𝓛`.

**Global sections rather than `H⁰`.**  The source's left-hand side is `dim_k Γ(X, 𝓛^{⊗ n})`, so
that is what is stated; `AlgebraicGeometry.cohomologyOverFieldZeroIso` is the identification with
the degree-zero cohomology that the Euler characteristic is written in, and it is the canonical
one, `CategoryTheory.Functor.rightDerivedZeroIsoSelf` for the left exact functor of sections over
the whole space.

**The lower order terms.**  "l.o.t." is read as a rational polynomial of degree strictly less
than `d`, evaluated at `n`; the zero polynomial is allowed, which is what happens when `d = 0`.
The formula is asserted for all large `n`, which is the force of the source's `n ≫ 0`: it cannot
hold for every `n` because the higher cohomology need not vanish in small degrees.

## References

* [Stacks Project, Tag 0BJ8](https://stacks.math.columbia.edu/tag/0BJ8)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Filter
open Stacks.SheafOfModules.Invertible
  (tensorPower tensorPower_zero tensorPower_isInvertible tensorProductIso
    tensorPowerCoherence)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Global sections over the ground field -/

/-- **The global sections `Γ(X, ℱ)` of a module on a scheme over `k`, as a `k`-vector space.**
The sections over the whole space are a module over `Γ(X, 𝒪_X)`; restricting scalars along the
structure morphism makes them a `k`-vector space.  This is the degree-zero companion of
`AlgebraicGeometry.cohomologyOverField`, which derives the same functor. -/
@[ega "I 2.2.5" "field base"]
public noncomputable def globalSectionsOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)

/-- **Degree-zero cohomology is the global sections.**  Sections over the whole space is a left
exact functor, so the canonical map to its zeroth right derived functor is an isomorphism
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`); restricting scalars to the ground field
preserves it. -/
public noncomputable def cohomologyOverFieldZeroIso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) :
    cohomologyOverField k f F 0 ≅ globalSectionsOverField k f F :=
  (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
    ((SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app F)

/-- The dimension of the global sections is the dimension of degree-zero cohomology. -/
public theorem finrank_globalSectionsOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) :
    Module.finrank k (globalSectionsOverField k f F) =
      Module.finrank k (cohomologyOverField k f F 0) :=
  ((cohomologyOverFieldZeroIso k f F).toLinearEquiv.finrank_eq).symm

/-! ### Substituting a sum of variables into a univariate polynomial -/

/-- The polynomial `p(n_1 + ⋯ + n_d)` in `d` variables attached to a univariate `p` of degree at
most `d`, written out in the monomial basis so that its total degree and its coefficient of
`n_1 ⋯ n_d` can be read off. -/
private noncomputable def sumSubst (d : ℕ) (p : Polynomial ℚ) : MvPolynomial (Fin d) ℚ :=
  ∑ j ∈ Finset.range (d + 1),
    MvPolynomial.C (p.coeff j) * (∑ i, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) ^ j

private theorem sumSubst_totalDegree_le (d : ℕ) (p : Polynomial ℚ) :
    (sumSubst d p).totalDegree ≤ d := by
  classical
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun j hj => ?_)
  have hj' : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have hA : (∑ i, MvPolynomial.X i : MvPolynomial (Fin d) ℚ).totalDegree ≤ 1 :=
    le_trans (MvPolynomial.totalDegree_finsetSum _ _)
      (Finset.sup_le fun i _ => le_of_eq (MvPolynomial.totalDegree_X i))
  have h2 : ((∑ i, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) ^ j).totalDegree ≤ j :=
    le_trans (MvPolynomial.totalDegree_pow _ _) (by simpa using Nat.mul_le_mul_left j hA)
  have h1 : (MvPolynomial.C (p.coeff j) : MvPolynomial (Fin d) ℚ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  omega

private theorem sumSubst_eval (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree < d + 1)
    (g : Fin d → ℚ) :
    MvPolynomial.eval g (sumSubst d p) = p.eval (∑ i, g i) := by
  rw [Polynomial.eval_eq_sum_range' hp, sumSubst, map_sum]
  exact Finset.sum_congr rfl fun j _ => by simp

private theorem sumSubst_coeff (d : ℕ) (p : Polynomial ℚ) :
    (sumSubst d p).coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1) =
      (d.factorial : ℚ) * p.coeff d := by
  classical
  set m : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1 with hmdef
  have hmval : ∀ i, m i = 1 := fun i => rfl
  have hsum : (m.sum fun _ e => e) = d := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp [hmval]
  have hmult : m.multinomial = d.factorial := by
    rw [Finsupp.multinomial, Finsupp.sum_fintype _ _ (fun _ => rfl),
      Finsupp.prod_fintype _ _ (fun _ => rfl)]
    simp [hmval]
  rw [sumSubst, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single_of_mem d (Finset.self_mem_range_succ d)]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum_X_pow_of_fintype, hsum, hmult]
    simp [mul_comm]
  · intro j _ hjd
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum_X_pow_of_fintype, hsum]
    simp [Ne.symm hjd]

/-! ### Collapsing a twist by a constant family -/

/-- **Integer tensor powers depend only on the isomorphism class of the invertible module.**
An isomorphism `M ≅ N` makes the two tensoring autoequivalences `- ⊗ M` and `- ⊗ N` objectwise
isomorphic, and `Stacks.Equivalence.powIntertwineObj` carries that to every integer iterate,
the negative ones through the quasi-inverses. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{u}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- The fold over a list of indices of a constant family of invertible modules, started at a
tensor power, is the tensor power with the exponents added on. -/
private noncomputable def twistListTensorPowerIso {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (m : ℤ),
      twistList M n l (tensorPower X.presheaf X.ringCatSheaf.2 N m) ≅
        tensorPower X.presheaf X.ringCatSheaf.2 N (l.foldl (fun z i => z + n i) m) := by
  intro l
  induction l with
  | nil => exact fun m => Iso.refl _
  | cons i t ih =>
      exact fun m =>
        twistListIso M n t
            (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
                (tensorPowerIsoOfIso (M i) N (e i) (n i)) ≪≫
              (tensorPowerCoherence X.presheaf X.ringCatSheaf.2 N).mulIso m (n i)) ≪≫
          ih (m + n i)

private theorem finRange_foldl_add {r : ℕ} (n : Fin r → ℤ) (z : ℤ) :
    (List.finRange r).foldl (fun a i => a + n i) z = z + ∑ i, n i := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
      rw [ih (fun i => n i.succ) (z + n 0)]
      simp [Fin.sum_univ_succ, add_assoc]

/-- **A twist of the structure sheaf by a constant family is a single tensor power.**
`𝒪_X ⊗ M_1^{⊗ n_1} ⊗ ⋯ ⊗ M_r^{⊗ n_r} ≅ N^{⊗ (n_1 + ⋯ + n_r)}` whenever every `M_i` is
isomorphic to `N`. -/
private noncomputable def twistedSheafUnitIsoTensorPower {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N (∑ i, n i) :=
  have hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      tensorPower X.presheaf X.ringCatSheaf.2 N 0 := rfl
  have hfold : (List.finRange r).foldl (fun z i => z + n i) 0 = ∑ i, n i := by
    rw [finRange_foldl_add]; ring
  twistListIso M n (List.finRange r) (eqToIso hunit) ≪≫
    twistListTensorPowerIso M N e n (List.finRange r) 0 ≪≫
    eqToIso (congrArg (tensorPower X.presheaf X.ringCatSheaf.2 N) hfold)

/-- The Euler characteristic of a twist of the structure sheaf by a constant family is that of the
corresponding tensor power. -/
private theorem eulerCharacteristic_twistedSheaf_unit {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ)
    [(twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n).IsCoherent] :
    eulerCharacteristic k f (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n) =
      @eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.2 N (∑ i, n i))
        (SheafOfModules.isCoherent_of_isInvertible k f _) :=
  have := SheafOfModules.isCoherent_of_isInvertible k f
    (tensorPower X.presheaf X.ringCatSheaf.2 N (∑ i, n i))
  eulerCharacteristic_eq_of_iso k f (twistedSheafUnitIsoTensorPower M N e n)

/-! ### Tag 0BJ8 -/

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (d : ℕ) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
  (hL : Scheme.Modules.IsAmple X L)

include hdim hL in
/-- **[Stacks, Tag 0BJ8], the leading coefficient.**  For `X` proper over `k` of dimension `d`
and `𝓛` ample, the constant `deg_𝓛(X)/d!` is positive.  The degree `deg_𝓛(X)` is positive by
[Stacks, Tag 0BEV] and `d!` is positive. -/
@[stacks 0BJ8 "the leading coefficient deg_L(X)/d! is a positive constant"]
public theorem degreeWithRespectTo_div_factorial_pos :
    0 < (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) := by
  have hpos : (0 : ℤ) < degreeWithRespectTo k f (𝟙 X) d hdim L hL :=
    degreeWithRespectTo_pos k f (𝟙 X) d hdim L hL
  have hposQ : (0 : ℚ) < (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) := by
    exact_mod_cast hpos
  exact div_pos hposQ (by positivity)

include hdim in
/-- The Euler characteristics of the tensor powers of an invertible module on a proper scheme
over a field are the values of a univariate rational polynomial of degree at most the dimension
of the scheme.  This is [Stacks, Tag 0BEM] in one variable, read through
`AlgebraicGeometry.twistedSheafUnitIsoTensorPower` and
`MvPolynomial.uniqueAlgEquiv`. -/
@[sga "6 X 2.3.1" "special case", sga "6 XIII 3.7" "m = 0 restriction"]
private theorem exists_eulerPolynomial_tensorPower :
    ∃ p : Polynomial ℚ, p.degree ≤ (d : WithBot ℕ) ∧
      ∀ m : ℤ, p.eval (m : ℚ) =
        ((@eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.2 L m)
          (SheafOfModules.isCoherent_of_isInvertible k f
            (tensorPower X.presheaf X.ringCatSheaf.2 L m)) : ℤ) : ℚ) := by
  classical
  have hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have : ∀ _ : Fin 1, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    fun _ => inferInstance
  obtain ⟨q, hqdeg, hqeval⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f
    (fun _ : Fin 1 => L) (SheafOfModules.unit X.ringCatSheaf) hunit
  have hsupp : topologicalKrullDim
      (SheafOfModules.supp (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ≤
      (d : WithBot ℕ∞) := le_trans (topologicalKrullDim_subspace_le X _) (le_of_eq hdim)
  have htotal : q.totalDegree ≤ d := by
    rcases hqdeg with hzero | hdeg
    · simp [hzero]
    · exact_mod_cast le_trans hdeg hsupp
  refine ⟨MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) q, ?_, ?_⟩
  · refine (Polynomial.degree_le_iff_coeff_zero _ (d : WithBot ℕ)).2 fun s hs => ?_
    have hs' : d < s := by exact_mod_cast hs
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    by_contra hne
    have hmem : Finsupp.single (default : Fin 1) s ∈ q.support :=
      MvPolynomial.mem_support_iff.2 hne
    have hle := MvPolynomial.le_totalDegree hmem
    rw [Finsupp.sum_single_index rfl] at hle
    omega
  · intro m
    have he : ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) q : Polynomial ℚ)).eval₂
        (RingHom.id ℚ) (m : ℚ) = q.eval₂ (RingHom.id ℚ) (fun _ : Fin 1 => (m : ℚ)) :=
      MvPolynomial.eval₂_const_uniqueAlgEquiv
    rw [Polynomial.eval₂_id] at he
    rw [he, MvPolynomial.eval₂_id]
    have hval := hqeval (fun _ : Fin 1 => m)
    have hcast : (fun j : Fin 1 => ((m : ℤ) : ℚ)) = fun _ : Fin 1 => (m : ℚ) := rfl
    rw [hcast] at hval
    rw [hval]
    have : (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => L)
        (fun _ => m)).IsCoherent := twistedSheaf_isCoherent _ _ _
    have := SheafOfModules.isCoherent_of_isInvertible k f
      (tensorPower X.presheaf X.ringCatSheaf.2 L m)
    have h := eulerCharacteristic_twistedSheaf_unit (k := k) f (fun _ : Fin 1 => L) L
      (fun _ => Iso.refl L) (fun _ => m)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    exact congrArg _ h

include hdim in
/-- **The self-intersection number is `d!` times the leading coefficient of the Euler
polynomial.**  The polynomial `P(n_1, …, n_d) = p(n_1 + ⋯ + n_d)` takes the twisted Euler
characteristics as its values and has total degree at most `d`, so [Stacks, Tag 0BEP] identifies
`(𝓛^d ⬝ X)` with its coefficient of `n_1 ⋯ n_d`, which is `d! ⬝ p_d`. -/
private theorem selfIntersectionNumber_eq_factorial_mul_coeff (p : Polynomial ℚ)
    (hp : p.degree ≤ (d : WithBot ℕ))
    (hpeval : ∀ m : ℤ, p.eval (m : ℚ) =
      ((@eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.2 L m)
        (SheafOfModules.isCoherent_of_isInvertible k f
          (tensorPower X.presheaf X.ringCatSheaf.2 L m)) : ℤ) : ℚ)) :
    ((selfIntersectionNumber k f (𝟙 X) d hdim.le L : ℤ) : ℚ) =
      (d.factorial : ℚ) * p.coeff d := by
  classical
  have : ∀ _ : Fin d, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    fun _ => inferInstance
  have hnat : p.natDegree < d + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_degree_le.2 hp)
  have hkey := intersectionNumber_eq_coeff k f (𝟙 X) d hdim.le (fun _ : Fin d => L)
    (sumSubst d p) ?_ (sumSubst_totalDegree_le d p)
  · rw [selfIntersectionNumber_eq_intersectionNumber, hkey, sumSubst_coeff]
  · intro n
    rw [sumSubst_eval d p hnat]
    have hcast : (∑ j, ((n j : ℤ) : ℚ)) = (((∑ j, n j : ℤ)) : ℚ) := by push_cast; ring
    rw [hcast, hpeval (∑ j, n j)]
    have : (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun j : Fin d => (Scheme.Modules.pullback (𝟙 X)).obj L) n).IsCoherent :=
      isCoherent_twistedSheafUnitPullback k f (𝟙 X) (fun _ : Fin d => L) n
    have h := eulerCharacteristic_twistedSheaf_unit (k := k) (𝟙 X ≫ f)
      (fun _ : Fin d => (Scheme.Modules.pullback (𝟙 X)).obj L) L
      (fun _ => (Scheme.Modules.pullbackId X).app L) n
    simp only [Category.id_comp] at h
    exact (congrArg _ h).symm

include hdim hL in
/-- **[Stacks, Tag 0BJ8], the asymptotic formula.**  For `X` proper over `k` of dimension `d` and
`𝓛` ample, for all sufficiently large `n`

`dim_k Γ(X, 𝓛^{⊗ n}) = deg_𝓛(X)/d! ⬝ n^d + P(n)`

with `P` a rational polynomial of degree strictly less than `d`. -/
@[stacks 0BJ8 "the asymptotic formula for dim_k Γ(X, L^n)"]
public theorem exists_degree_lt_eventually_finrank_globalSections_eq :
    ∃ P : Polynomial ℚ, P.degree < (d : WithBot ℕ) ∧
      ∀ᶠ n : ℕ in atTop,
        (Module.finrank k (globalSectionsOverField k f
            (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) : ℚ) =
          (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) * (n : ℚ) ^ d +
            P.eval (n : ℚ) := by
  classical
  obtain ⟨p, hp, hpeval⟩ := exists_eulerPolynomial_tensorPower k f d hdim L
  have hcoeff := selfIntersectionNumber_eq_factorial_mul_coeff k f d hdim L p hp hpeval
  have hfac : (0 : ℚ) < (d.factorial : ℚ) := by positivity
  have hlead : p.coeff d =
      (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) := by
    rw [degreeWithRespectTo_eq_selfIntersectionNumber, hcoeff]
    field_simp
  refine ⟨p - Polynomial.C (p.coeff d) * Polynomial.X ^ d, ?_, ?_⟩
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro s hs
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le (by exact_mod_cast hs : (d : ℕ) ≤ s) with hsd | hsd
    · subst hsd
      simp
    · have hzero : p.coeff s = 0 :=
        (Polynomial.degree_le_iff_coeff_zero p (d : WithBot ℕ)).1 hp s (by exact_mod_cast hsd)
      have hne : s ≠ d := Nat.ne_of_gt hsd
      simp [hzero, hne]
  · -- the vanishing of higher cohomology for large `n`
    have hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
    have hinvRS : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L := ‹_›
    obtain ⟨N, hN⟩ :=
      Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f hL
        (SheafOfModules.unit X.ringCatSheaf) hunit
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hvan : ∀ r : ℕ, 0 < r →
        IsZero (cohomologyOverField k f
          (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)) r) := by
      intro r hr
      have h := hN n r hn hr
      have hiso : ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((SheafOfModules.unit X.ringCatSheaf))).obj
            ((tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L
            (n : ℤ)))) : X.Modules) ≅
          tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ) :=
        Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _
      have h2 : IsZero (((SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived r).obj
            (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) :=
        IsZero.of_iso h (((SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived r).mapIso hiso.symm)
      exact (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map_isZero h2
    have := SheafOfModules.isCoherent_of_isInvertible k f
      (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))
    have hchi : (@eulerCharacteristic k _ X f _
        (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))
        (SheafOfModules.isCoherent_of_isInvertible k f _) : ℤ) =
        (Module.finrank k (cohomologyOverField k f
          (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)) 0) : ℤ) :=
      finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k f _ hvan
    have hsplit : p.eval (n : ℚ) =
        (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) * (n : ℚ) ^ d +
          (p - Polynomial.C (p.coeff d) * Polynomial.X ^ d).eval (n : ℚ) := by
      rw [← hlead]
      simp
    have hgoal : (Module.finrank k (globalSectionsOverField k f
        (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) : ℚ) = p.eval (n : ℚ) := by
      have h := hpeval (n : ℤ)
      rw [Int.cast_natCast, hchi] at h
      rw [h]
      exact_mod_cast finrank_globalSectionsOverField k f _
    exact hgoal.trans hsplit

include hdim hL in
/-- **[Stacks, Tag 0BJ8] (Asymptotic Riemann–Roch).**  Let `k` be a field, let `X` be a scheme
proper over `k` of dimension `d` and let `𝓛` be an ample invertible `𝒪_X`-module.  Then

`dim_k Γ(X, 𝓛^{⊗ n}) = deg_𝓛(X)/d! ⬝ n^d + lower order terms`

for all sufficiently large `n`, and the leading constant `deg_𝓛(X)/d!` is positive. -/
@[stacks 0BJ8]
public theorem asymptotic_riemann_roch :
    0 < (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) ∧
      ∃ P : Polynomial ℚ, P.degree < (d : WithBot ℕ) ∧
        ∀ᶠ n : ℕ in atTop,
          (Module.finrank k (globalSectionsOverField k f
              (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) : ℚ) =
            (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) * (n : ℚ) ^ d +
              P.eval (n : ℚ) :=
  ⟨degreeWithRespectTo_div_factorial_pos k f d hdim L hL,
    exists_degree_lt_eventually_finrank_globalSections_eq k f d hdim L hL⟩

end

end AlgebraicGeometry

end
