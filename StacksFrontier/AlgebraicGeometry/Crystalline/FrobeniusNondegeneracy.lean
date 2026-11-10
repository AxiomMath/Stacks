module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# Nondegeneracy of an F-crystal and two-sided quasi-inverses

A one-sided quasi-inverse of a square matrix becomes two-sided after rescaling by a power of the
scalar: if `K * L = a • 1` for `r × r` matrices over a commutative ring, then `det K * det L = aʳ`
and the matrix `K' = aʳ • K` satisfies `K' * L = L * K' = aʳ⁺¹ • 1`.  Taking `a = pⁱ` this reads
`K' = p ^ (r * i) • K` and `K' * L = L * K' = p ^ (r * i + i) • 1`, and the exponent `r * i` may be
replaced by any `N ≥ r * i`.  The same computation, read through a pair of bases, turns a one-sided
quasi-inverse `V` of a map `F` of free modules of rank `r` into a two-sided one after rescaling.

For an F-crystal `(E, F_E)` the Frobenius structure map has a quasi-inverse up to a power of `p` on
one side exactly when the crystal is nondegenerate.  That one-sided identity already kills the
kernel of `F_E`, with no hypothesis on the rank.  The other side needs the rank of `E` to be
bounded.  It is obtained by globalising the matrix computation: the identity
`V' ≫ F_E = p ^ (N + i) • 𝟙` is an equality of morphisms of sheaves of modules, so it may be tested
on a covering sieve of each object of `CRIS(X/S)`, and on a suitable covering sieve both `E` and
its Frobenius pullback have free sections of one common rank, where the matrix computation applies.
The cokernel of `F_E` is then killed by the same power of `p`.

## Main results

* `Matrix.det_mul_det_and_two_sided_of_mul_eq_pow_smul_one` — the matrix computation of
  [Stacks, Tag 07N4]: for `r × r` matrices with `K L = pⁱ 1`, `det K det L = p ^ (r i)`, the
  adjugate identities for `L`, and `K' L = L K' = p ^ (r i + i) 1` for `K' = p ^ (r i) K`.
* `Matrix.mul_pow_smul_eq_smul_one_of_card_le` — the same for any exponent `N ≥ r * i`, which is
  the form in which a *bound* on the rank is used.
* `LinearMap.comp_pow_smul_eq_smul_id_of_card_le` — the same for maps between free modules of
  equal finite rank.
* `LinearMap.exists_comp_eq_smul_id_and_forall_comp_pow_smul_ne_smul_id` — equal rank is not
  removable: free `ℤ`-modules of ranks `1` and `2` carrying a one-sided scalar quasi-inverse which
  no rescaling makes two-sided.
* `SheafOfModules.nonempty_basis_of_isColimit_cofan_unit` — a sheaf of modules exhibited as a
  colimit of a finite cofan of copies of the structure sheaf has free sections of that rank over
  every object.
* `SheafOfModules.eq_of_isColimit_cofan_unit` — two such trivialisations, over objects that a
  single object with nontrivial commutative ring of sections maps to, have the same rank.
* `SheafOfModules.hom_ext_of_sieve` — two morphisms of sheaves of modules agreeing on sections
  over a covering sieve of each object are equal.
* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE` — a sheaf of modules of rank bounded
  by `r`, and its trivialising sieve `AlgebraicGeometry.RingedSite.trivialisedSieveLE`.
* `Crystalline.GlobalCrystallineSituation.crystallineRingedSite` — the big crystalline site as a
  ringed site, so that these rank conditions can be imposed on a crystal.
* `Crystalline.FCrystalSituation.freeFrobenius` — the absolute Frobenius of a scheme `U` over `X`
  as a morphism `(F_X)_cris (U, U, ∅) ⟶ (U, U, ∅)` of `CRIS(X/S)`.
* `Crystalline.FCrystal.HasBoundedCommonLocalRank` — a covering sieve over whose arrows `E` and
  `(F_X)_cris^* E` are free of one common rank `≤ rmax`.
* `Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE` — **a bound `rmax` on the rank of
  `E` gives a common local rank bounded by `rmax`**: the Frobenius pullback has the local rank of
  `E`.
* `Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank` — the same for constant rank.
* `Crystalline.FCrystal.exists_pow_nsmul_eq_zero_of_nondegenerate` — a nondegenerate F-crystal has
  the kernel of its Frobenius structure map killed by a power of `p`.
* `Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank`,
  `Crystalline.FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_boundedCommonLocalRank`,
  `Crystalline.FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_boundedCommonLocalRank` —
  the second-sided identity, the annihilation of the cokernel, and one power of `p` killing both
  the kernel and the cokernel, from a common local rank bounded by `rmax`, with the single
  exponent `rmax * i + i` for the whole site; the constant-rank forms carry the suffix `_of_rank`.

The forms of these results under the source's own hypothesis, a bound on the rank of `E`, are in
`StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusNondegeneracyBoundedRank`.

## Implementation notes

The matrix statements are given over an arbitrary finite index type, with the source's rank `r`
read as the cardinality of that type, and for an arbitrary ring scalar `a` in place of `pⁱ`.  The
hypothesis `r ≥ 1` of the source is not needed.

The kernel and cokernel of the Frobenius structure map are described by their universal
properties, as the maps which the structure map annihilates on either side, so that no
construction of kernels or cokernels of sheaves of modules is required.

The source's "the rank of `E` is bounded" is spelled
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE`: the rank clause of Stacks 0409 with
the rank only capped, imposed on `E.crystal` over the big crystalline site viewed as a ringed site.
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` fixes the rank, and the local-freeness
field of `Crystalline.FCrystal` caps nothing.

The source reads `F_E` and `V` over an object as two `r × r` matrices for one `r`, so it uses that
`(F_X)_cris^* E` has, locally, the rank of `E`.  This is proved in
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE`.  The sections of `(F_X)_cris^* E` over
`Z` are the sections of `E` over the Frobenius twist `u(Z)` of `Z`.  On the arrows of a covering
sieve, `Z` maps to an object over which `E` is free of rank `s` and `u(Z)` to one over which `E` is
free of rank `t`.  Let `W` be the trivial thickening of the thickened scheme of `Z`; it maps to
`Z`, and the absolute Frobenius is a morphism `u(W) ⟶ W`.  So `u(W)` maps to both objects, the
sections of `E` over `u(W)` are free of rank `s` and of rank `t`, and `s = t` as soon as the ring
of sections over `Z` is nontrivial; over the zero ring every module is free of every rank
(`Module.nonempty_basis_of_subsingleton`).

The bound is used only through `Matrix.mul_pow_smul_eq_smul_one_of_card_le`, which does not tie
the exponent to the size of the matrices, so one exponent `N ≥ rmax * i` serves every object of the
site at once.  The source's `N > i · rank(E)` is relaxed to `N ≥ rmax * i`.

## References

* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

universe u₁ v₁ w₁

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **The determinant of a one-sided scalar quasi-inverse.**  If `K * L` is the scalar matrix
`a • 1` of size `r`, then `det K * det L = a ^ r`. -/
theorem det_mul_det_of_mul_eq_smul_one {K L : Matrix n n R} {a : R}
    (h : K * L = a • (1 : Matrix n n R)) : K.det * L.det = a ^ Fintype.card n := by
  simpa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] using congrArg Matrix.det h

/-- **A one-sided scalar quasi-inverse stays one after rescaling.**  If `K * L = a • 1` for
matrices of size `r`, then `(a ^ r • K) * L = a ^ (r + 1) • 1`. -/
theorem pow_card_smul_mul_eq_smul_one {K L : Matrix n n R} {a : R}
    (h : K * L = a • (1 : Matrix n n R)) :
    (a ^ Fintype.card n • K) * L = a ^ (Fintype.card n + 1) • (1 : Matrix n n R) := by
  rw [Matrix.smul_mul, h, smul_smul, pow_succ]

/-- **Rescaling a one-sided scalar quasi-inverse makes it two-sided.**  If `K * L = a • 1` for
matrices of size `r`, then `L * (a ^ r • K) = a ^ (r + 1) • 1`: the adjugate of `K` turns the
hypothesis into `det K • (L * K) = (a * det K) • 1`, and multiplying by `det L` replaces
`det K * det L` by `a ^ r`. -/
theorem mul_pow_card_smul_eq_smul_one {K L : Matrix n n R} {a : R}
    (h : K * L = a • (1 : Matrix n n R)) :
    L * (a ^ Fintype.card n • K) = a ^ (Fintype.card n + 1) • (1 : Matrix n n R) := by
  have hdet : K.det * L.det = a ^ Fintype.card n := det_mul_det_of_mul_eq_smul_one h
  have key : K.det • (L * K) = (a * K.det) • (1 : Matrix n n R) := by
    calc K.det • (L * K) = K.adjugate * K * (L * K) := by
          rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = K.adjugate * (K * L) * K := by simp only [Matrix.mul_assoc]
      _ = K.adjugate * (a • (1 : Matrix n n R)) * K := by rw [h]
      _ = a • (K.adjugate * K) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (a * K.det) • (1 : Matrix n n R) := by rw [adjugate_mul, smul_smul]
  calc L * (a ^ Fintype.card n • K) = a ^ Fintype.card n • (L * K) := by rw [Matrix.mul_smul]
    _ = (K.det * L.det) • (L * K) := by rw [hdet]
    _ = L.det • (K.det • (L * K)) := by rw [smul_smul, mul_comm L.det K.det]
    _ = L.det • ((a * K.det) • (1 : Matrix n n R)) := by rw [key]
    _ = a ^ (Fintype.card n + 1) • (1 : Matrix n n R) := by
        rw [smul_smul]
        congr 1
        rw [pow_succ, ← hdet]
        ring

/-- **A bound on the size suffices.**  If `K * L = p ^ i • 1` for matrices of size `r` and
`N ≥ r * i`, then `L * (p ^ N • K) = p ^ (N + i) • 1`.  This is the form in which the source's
`N > i · rank(E)` is used: the exponent is not tied to the size of the matrices, only bounded
below in terms of it. -/
theorem mul_pow_smul_eq_smul_one_of_card_le {K L : Matrix n n R} {p : R} {i N : ℕ}
    (hcard : Fintype.card n * i ≤ N)
    (h : K * L = (p ^ i) • (1 : Matrix n n R)) :
    L * ((p ^ N) • K) = (p ^ (N + i)) • (1 : Matrix n n R) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcard
  have hmat : L * ((p ^ (Fintype.card n * i)) • K) =
      (p ^ (Fintype.card n * i + i)) • (1 : Matrix n n R) := by
    have h' := mul_pow_card_smul_eq_smul_one h
    rwa [← pow_mul, ← pow_mul, Nat.mul_comm i (Fintype.card n),
      Nat.mul_comm i (Fintype.card n + 1), Nat.succ_mul] at h'
  have e1 : p ^ N = p ^ d * p ^ (Fintype.card n * i) := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : p ^ d * p ^ (Fintype.card n * i + i) = p ^ (N + i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1, mul_smul, Matrix.mul_smul, hmat, smul_smul, e2]

/-- **The matrix computation of [Stacks, Tag 07N4].**  Let `R` be a commutative ring, `r` an
integer and `K, L` two `r × r` matrices over `R` with `K L = pⁱ 1`.  Then:

* `det(K) det(L) = p ^ (r i)`;
* the adjugate `L'` of `L` satisfies `L' L = L L' = det(L) 1`;
* `K' = p ^ (r i) K` satisfies `K' L = p ^ j 1` and `L K' = p ^ j 1`, where `j = r i + i`.

The second-sided identity `L K' = p ^ j 1` is the content: it is obtained, as in the source, from
the adjugate and the determinant identity.  The element `p` is arbitrary, and `r ≥ 1` is not
needed. -/
@[stacks 07N4 "the matrix computation: for r × r matrices K, L over a ring R with K L = p ^ i 1, \
det(K) det(L) = p ^ (r i), the adjugate L' of L satisfies L' L = L L' = det(L) 1, and \
K' = p ^ (r i) K satisfies K' L = p ^ j 1 and L K' = p ^ j 1 for j = r i + i"]
theorem det_mul_det_and_two_sided_of_mul_eq_pow_smul_one {r : ℕ}
    {K L : Matrix (Fin r) (Fin r) R} {p : R} {i : ℕ}
    (h : K * L = p ^ i • (1 : Matrix (Fin r) (Fin r) R)) :
    K.det * L.det = p ^ (r * i) ∧
      (L.adjugate * L = L.det • (1 : Matrix (Fin r) (Fin r) R) ∧
        L * L.adjugate = L.det • (1 : Matrix (Fin r) (Fin r) R)) ∧
      (p ^ (r * i) • K) * L = p ^ (r * i + i) • (1 : Matrix (Fin r) (Fin r) R) ∧
      L * (p ^ (r * i) • K) = p ^ (r * i + i) • (1 : Matrix (Fin r) (Fin r) R) := by
  refine ⟨?_, ⟨L.adjugate_mul, L.mul_adjugate⟩, ?_,
    mul_pow_smul_eq_smul_one_of_card_le (by simp) h⟩
  · rw [det_mul_det_of_mul_eq_smul_one h, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
  · rw [Matrix.smul_mul, h, smul_smul, pow_add]

end Matrix

namespace LinearMap

variable {ι R A B : Type*} [Fintype ι] [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- If the matrices of `V` and `F` satisfy `K * L = a • 1 → L * (c • K) = d • 1`, then
`V ∘ₗ F = a • id` gives `F ∘ₗ (c • V) = d • id`. -/
private theorem comp_smul_eq_smul_id_of_matrix [DecidableEq ι] (bA : Module.Basis ι R A)
    (bB : Module.Basis ι R B)
    {F : A →ₗ[R] B} {V : B →ₗ[R] A} {a c d : R} (h : V ∘ₗ F = a • LinearMap.id)
    (hm : ∀ {K L : Matrix ι ι R}, K * L = a • 1 → L * (c • K) = d • 1) :
    F ∘ₗ (c • V) = d • LinearMap.id := by
  refine (LinearMap.toMatrix bB bB).injective ?_
  rw [LinearMap.toMatrix_comp bB bA bB, map_smul, map_smul, LinearMap.toMatrix_id]
  refine hm ?_
  rw [← LinearMap.toMatrix_comp bA bB bA, h, map_smul, LinearMap.toMatrix_id]

/-- **Rescaling a one-sided quasi-inverse of a map of free modules makes it two-sided.**  Let
`F : A →ₗ[R] B` and `V : B →ₗ[R] A` with `V ∘ₗ F = a • id`, where `A` and `B` are free of the same
finite rank `r`.  Then `F ∘ₗ (a ^ r • V) = a ^ (r + 1) • id`. -/
theorem comp_pow_card_smul_eq_smul_id (bA : Module.Basis ι R A) (bB : Module.Basis ι R B)
    {F : A →ₗ[R] B} {V : B →ₗ[R] A} {a : R} (h : V ∘ₗ F = a • LinearMap.id) :
    F ∘ₗ (a ^ Fintype.card ι • V) = a ^ (Fintype.card ι + 1) • LinearMap.id := by
  classical
  exact comp_smul_eq_smul_id_of_matrix bA bB h Matrix.mul_pow_card_smul_eq_smul_one

/-- **The source's form of the rescaled quasi-inverse.**  Let `F : A →ₗ[R] B` and `V : B →ₗ[R] A`
with `V ∘ₗ F = p ^ i • id`, where `A` and `B` are free of the same finite rank `r`.  Then
`V' = p ^ (r * i) • V` satisfies `F ∘ₗ V' = p ^ (r * i + i) • id`. -/
theorem comp_pow_smul_eq_smul_id (bA : Module.Basis ι R A) (bB : Module.Basis ι R B)
    {F : A →ₗ[R] B} {V : B →ₗ[R] A} {p : R} {i : ℕ} (h : V ∘ₗ F = p ^ i • LinearMap.id) :
    F ∘ₗ (p ^ (Fintype.card ι * i) • V) =
      p ^ (Fintype.card ι * i + i) • LinearMap.id := by
  have h2 := comp_pow_card_smul_eq_smul_id bA bB h
  rwa [← pow_mul, ← pow_mul, Nat.mul_add, Nat.mul_one, Nat.mul_comm i (Fintype.card ι)] at h2

/-- **A bound on the rank suffices.**  Let `F : A →ₗ[R] B` and `V : B →ₗ[R] A` with
`V ∘ₗ F = p ^ i • id`, where `A` and `B` are free of the same finite rank `r`, and let
`N ≥ r * i`.  Then `V' = p ^ N • V` satisfies `F ∘ₗ V' = p ^ (N + i) • id`. -/
theorem comp_pow_smul_eq_smul_id_of_card_le (bA : Module.Basis ι R A) (bB : Module.Basis ι R B)
    {F : A →ₗ[R] B} {V : B →ₗ[R] A} {p : R} {i N : ℕ}
    (hcard : Fintype.card ι * i ≤ N) (h : V ∘ₗ F = p ^ i • LinearMap.id) :
    F ∘ₗ (p ^ N • V) = p ^ (N + i) • LinearMap.id := by
  classical
  exact comp_smul_eq_smul_id_of_matrix bA bB h
    (Matrix.mul_pow_smul_eq_smul_one_of_card_le hcard)

/-- **Equal rank cannot be dropped from
`LinearMap.comp_pow_smul_eq_smul_id_of_card_le`.**  Over `ℤ`, take `A = ℤ` and `B = ℤ × ℤ`, free
of ranks `1` and `2`, with `F x = (p * x, 0)` and `V (a, b) = a`.  Then `V ∘ₗ F = p • id` holds on
`A`, while `F ∘ₗ (p ^ N • V)` kills `(0, 1)` and `p ^ (N + 1) • id` does not, for any `N`.  So a
one-sided scalar quasi-inverse between free modules of *unequal* rank need not become two-sided
after any rescaling, and no bound on the rank of one side alone can replace the agreement of the
two ranks. -/
theorem exists_comp_eq_smul_id_and_forall_comp_pow_smul_ne_smul_id {p : ℤ} (hp : p ≠ 0) :
    ∃ (F : ℤ →ₗ[ℤ] ℤ × ℤ) (V : ℤ × ℤ →ₗ[ℤ] ℤ),
      V ∘ₗ F = p • LinearMap.id ∧
        ∀ N : ℕ, F ∘ₗ ((p ^ N) • V) ≠ (p ^ (N + 1)) • LinearMap.id := by
  refine ⟨(p • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).prod 0, LinearMap.fst ℤ ℤ ℤ, ?_, fun N h => ?_⟩
  · ext
    simp
  · have h2 := congrArg (fun f : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ => (f ((0 : ℤ), (1 : ℤ))).2) h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.fst_apply, LinearMap.prod_apply, LinearMap.zero_apply,
      LinearMap.id_apply, Prod.smul_snd, smul_eq_mul, mul_zero, mul_one,
      Function.prod] at h2
    exact pow_ne_zero (N + 1) hp h2.symm

end LinearMap

namespace Module

/-- **Over a ring with one element, every module is free of every rank.**  A module over a
subsingleton ring is a subsingleton, and any two subsingleton modules are isomorphic, so a basis
indexed by `Fin n` exists for every `n`.  This is the degenerate case that keeps the rank of a
module from being well defined: it is why a statement that two modules have a *common* local rank
is weaker than a statement that their ranks agree, the latter being false over the zero ring. -/
theorem nonempty_basis_of_subsingleton {R M : Type*} [Ring R] [Subsingleton R] [AddCommGroup M]
    [Module R M] (n : ℕ) : Nonempty (Module.Basis (Fin n) R M) := by
  have hM : Subsingleton M :=
    ⟨fun x y => by
      rw [← one_smul R x, ← one_smul R y, Subsingleton.elim (1 : R) 0, zero_smul, zero_smul]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map
    { toFun := fun _ => 0
      map_add' := fun _ _ => Subsingleton.elim _ _
      map_smul' := fun _ _ => Subsingleton.elim _ _
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }⟩

end Module

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w₁}}

/-- **A finite cofan of copies of the structure sheaf has free sections.**  If `M` is the colimit
of a cofan of `r` copies of `SheafOfModules.unit R`, then the sections of `M` over any object form
a free module of rank `r`.  The point is that a *finite* cofan is a biproduct, and evaluation at an
object is an additive functor and so preserves it; colimits of sheaves of modules are not in
general computed section by section. -/
theorem nonempty_basis_of_isColimit_cofan_unit {M : SheafOfModules.{w₁} R} {r : ℕ}
    (ι : ∀ _ : Fin r, SheafOfModules.unit R ⟶ M)
    (hc : IsColimit (Cofan.mk M ι)) (U : Cᵒᵖ) :
    Nonempty (Module.Basis (Fin r) (R.obj.obj U) (M.val.obj U)) := by
  classical
  let Ev := SheafOfModules.evaluation R U
  let : Ev.Additive := ⟨by intros; rfl⟩
  let D : Fin r → ModuleCat (R.obj.obj U) := fun _ => Ev.obj (SheafOfModules.unit R)
  have hc' : IsColimit (Cofan.mk (Ev.obj M) (fun j => Ev.map (ι j))) :=
    isColimitOfPreserves Ev hc
  let e : Ev.obj M ≅ ModuleCat.of (R.obj.obj U) (Fin r → R.obj.obj U) :=
    hc'.coconePointUniqueUpToIso (biproduct.isColimit D) ≪≫ ModuleCat.biproductIsoPi D
  exact ⟨(Pi.basisFun (R.obj.obj U) (Fin r)).map e.symm.toLinearEquiv⟩

/-- **Morphisms of sheaves of modules are determined locally.**  Two morphisms `φ, ψ : F ⟶ G`
which agree on sections over the source of every arrow of some covering sieve of every object are
equal.  This is separatedness of the underlying sheaf of abelian groups of `G`. -/
theorem hom_ext_of_sieve {F G : SheafOfModules.{w₁} R} {φ ψ : F ⟶ G}
    (h : ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃Z : C⦄ (f : Z ⟶ U), S f →
      ∀ x : F.val.obj (Opposite.op Z),
        (φ.val.app (Opposite.op Z)).hom x = (ψ.val.app (Opposite.op Z)).hom x) :
    φ = ψ := by
  ext U x
  obtain ⟨S, hS, hSeq⟩ := h U.unop
  have hP : Presheaf.IsSheaf J (G.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    Presheaf.isSheaf_comp_of_isSheaf J G.val.presheaf
      (CategoryTheory.forget AddCommGrpCat) G.isSheaf
  apply hP.isSeparated U.unop S hS
  intro Z f hf
  change G.val.map f.op ((φ.val.app U).hom x) = G.val.map f.op ((ψ.val.app U).hom x)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact hSeq f hf (F.val.map f.op x)

/-- **The two-sided identity on sections over one object.**  Let `f : G ⟶ F` and `g : F ⟶ G` with
`f ≫ g = p ^ i • 𝟙 G`, and suppose the sections of `F` and of `G` over `U` are both free of rank
`s` over the (commutative) ring of sections of the structure sheaf over `U`.  If `s * i ≤ N` then
`(p ^ N • g) ≫ f` and `p ^ (N + i) • 𝟙 F` agree on sections over `U`.  This is the matrix
computation, read through the two bases. -/
theorem nsmul_comp_val_app_apply {F G : SheafOfModules.{w₁} R} (U : Cᵒᵖ)
    (hcomm : ∀ a b : R.obj.obj U, a * b = b * a)
    {s : ℕ} (bF : Module.Basis (Fin s) (R.obj.obj U) (F.val.obj U))
    (bG : Module.Basis (Fin s) (R.obj.obj U) (G.val.obj U))
    {f : G ⟶ F} {g : F ⟶ G} {p i N : ℕ} (hs : s * i ≤ N)
    (h : f ≫ g = (p ^ i : ℕ) • 𝟙 G) (x : F.val.obj U) :
    ((((p ^ N : ℕ) • g) ≫ f).val.app U).hom x =
      (((p ^ (N + i) : ℕ) • (𝟙 F : F ⟶ F)).val.app U).hom x := by
  let : CommRing (R.obj.obj U) :=
    { toRing := (inferInstance : Ring (R.obj.obj U))
      mul_comm := hcomm }
  let Ev := SheafOfModules.evaluation R U
  let : Ev.Additive := ⟨by intros; rfl⟩
  have hlin : (g.val.app U).hom.comp (f.val.app U).hom =
      ((p : R.obj.obj U) ^ i) •
        (LinearMap.id : G.val.obj U →ₗ[R.obj.obj U] G.val.obj U) := by
    have hh := congrArg Ev.map h
    rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id] at hh
    have hh' := congrArg ModuleCat.Hom.hom hh
    simp only [ModuleCat.hom_comp, ModuleCat.hom_nsmul, ModuleCat.hom_id] at hh'
    change (g.val.app U).hom.comp (f.val.app U).hom =
      (p ^ i : ℕ) • (LinearMap.id : G.val.obj U →ₗ[R.obj.obj U] G.val.obj U) at hh'
    rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hrev := LinearMap.comp_pow_smul_eq_smul_id_of_card_le bG bF
    (F := (f.val.app U).hom) (V := (g.val.app U).hom) (p := (p : R.obj.obj U))
    (i := i) (N := N) (by simpa using hs) hlin
  have hrevNat : (f.val.app U).hom.comp ((p ^ N : ℕ) • (g.val.app U).hom) =
      (p ^ (N + i) : ℕ) • (LinearMap.id : F.val.obj U →ₗ[R.obj.obj U] F.val.obj U) := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hrev
  have hrevCat : Ev.map (((p ^ N : ℕ) • g) ≫ f) =
      Ev.map ((p ^ (N + i) : ℕ) • (𝟙 F : F ⟶ F)) := by
    rw [Functor.map_comp, Functor.map_nsmul, Functor.map_nsmul,
      CategoryTheory.Functor.map_id]
    exact ModuleCat.hom_ext hrevNat
  exact congrArg (fun φ => φ.hom x) hrevCat

/-- **Two trivialisations seen from one object have the same rank.**  Suppose `M` is exhibited,
over `B`, as a coproduct of `s` copies of the structure sheaf and, over `A`, as a coproduct of `t`
copies.  If some object `Y` maps to both `A` and `B` and the ring of sections of the structure
sheaf over `Y` is commutative and nontrivial, then `s = t`: both trivialisations give a basis of
the sections of `M` over `Y`, and a nontrivial commutative ring has invariant basis number. -/
theorem eq_of_isColimit_cofan_unit {M : SheafOfModules.{w₁} R} {A B Y : C} {s t : ℕ}
    (ιA : ∀ _ : Fin t, SheafOfModules.unit (R.over A) ⟶ M.over A)
    (hA : IsColimit (Cofan.mk (M.over A) ιA))
    (ιB : ∀ _ : Fin s, SheafOfModules.unit (R.over B) ⟶ M.over B)
    (hB : IsColimit (Cofan.mk (M.over B) ιB)) (a : Y ⟶ A) (b : Y ⟶ B)
    (hcomm : ∀ x y : R.obj.obj (Opposite.op Y), x * y = y * x)
    (hnt : Nontrivial (R.obj.obj (Opposite.op Y))) : s = t := by
  let : CommRing (R.obj.obj (Opposite.op Y)) :=
    { toRing := (inferInstance : Ring (R.obj.obj (Opposite.op Y)))
      mul_comm := hcomm }
  have : StrongRankCondition (R.obj.obj (Opposite.op Y)) := commRing_strongRankCondition _
  obtain ⟨bB⟩ := nonempty_basis_of_isColimit_cofan_unit ιB hB (Opposite.op (Over.mk b))
  obtain ⟨bA⟩ := nonempty_basis_of_isColimit_cofan_unit ιA hA (Opposite.op (Over.mk a))
  have bB' : Module.Basis (Fin s) (R.obj.obj (Opposite.op Y)) (M.val.obj (Opposite.op Y)) := bB
  have bA' : Module.Basis (Fin t) (R.obj.obj (Opposite.op Y)) (M.val.obj (Opposite.op Y)) := bA
  simpa using (Module.finrank_eq_card_basis bB').symm.trans (Module.finrank_eq_card_basis bA')

/-- **A sheaf of modules over an object with zero ring of sections is a coproduct of no copies of
the structure sheaf.**  If the ring of sections of the structure sheaf over `V` is zero, then so is
the ring over every object mapping to `V`, every module over it is zero, and the restriction of `M`
to `V` is the colimit of the empty cofan. -/
theorem nonempty_isColimit_cofan_fin_zero (M : SheafOfModules.{w₁} R) (V : C)
    (hV : Subsingleton (R.obj.obj (Opposite.op V)))
    (ι : ∀ _ : Fin 0, SheafOfModules.unit (R.over V) ⟶ M.over V) :
    Nonempty (IsColimit (Cofan.mk (M.over V) ι)) := by
  refine ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => Fin.elim0 j) (fun t m _ => ?_)⟩
  ext U x
  have hU : Subsingleton ((R.over V).obj.obj U) := by
    rw [← subsingleton_iff_zero_eq_one]
    have h : (0 : R.obj.obj (Opposite.op U.unop.left)) = 1 := by
      simpa using congrArg (R.obj.map U.unop.hom.op).hom
        (Subsingleton.elim (0 : R.obj.obj (Opposite.op V)) 1)
    exact h
  have : Subsingleton ((M.over V).val.obj U) := Module.subsingleton ((R.over V).obj.obj U) _
  obtain rfl : x = 0 := @Subsingleton.elim _ this x 0
  rw [map_zero, map_zero]

end SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u₁, v₁, w₁})
  (F : SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ)

/-- **The sieve of objects with free sections of rank `r`.**  Its arrows are those whose source
admits a morphism to an object over which `F` has a rank-`r` trivialisation; by
`AlgebraicGeometry.RingedSite.nonempty_basis_of_trivialisedSieve` the sections of `F` over the
source of such an arrow are then free of rank `r`.  Reachability, rather than the trivialisation
itself, is what makes this a sieve. -/
def trivialisedSieve (U : X.C) : Sieve U where
  arrows := fun Z _ => ∃ (A : X.C) (_ : Z ⟶ A),
    ∃ ι : ∀ _ : Fin r,
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over A) ⟶ F.over A,
      Nonempty (IsColimit (Cofan.mk (F.over A) ι))
  downward_closed := fun {_ _ _} h g => by
    obtain ⟨A, a, hA⟩ := h
    exact ⟨A, g ≫ a, hA⟩

/-- **The trivialising sieve of a module of rank `r` is covering.**  Each member of the
trivialising covering of `U` furnished by the rank condition of Stacks 0409 reaches itself, so the
sieve generated by that covering is contained in `trivialisedSieve`. -/
theorem trivialisedSieve_mem (h : IsFiniteLocallyFreeOfRank X F r) (U : X.C) :
    trivialisedSieve X F r U ∈ X.J U := by
  obtain ⟨I, V, f, hcov, hfree⟩ := h U
  refine X.J.superset_covering ?_ hcov
  intro Z k hk
  obtain ⟨j, q, _⟩ := Sieve.ofArrows.exists hk
  exact ⟨V j, q, hfree j⟩

/-- **Sections over an object reached by the trivialising sieve are free of rank `r`.**  A
trivialisation of `F` over `A` is a cofan of `r` copies of the structure sheaf of the localisation
at `A`, whose sections over the object `Z ⟶ A` of that localisation are the sections of `F`
over `Z`. -/
theorem nonempty_basis_of_trivialisedSieve {U Z : X.C} (k : Z ⟶ U)
    (hk : trivialisedSieve X F r U k) :
    Nonempty (Module.Basis (Fin r)
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op Z))
      (F.val.obj (Opposite.op Z))) := by
  obtain ⟨A, a, ι, ⟨hc⟩⟩ := hk
  exact SheafOfModules.nonempty_basis_of_isColimit_cofan_unit ι hc (Opposite.op (Over.mk a))

/-- **A sheaf of modules of rank bounded by `r`.**  Every object has a covering family on each
member of which the module is a coproduct of `s` copies of the structure sheaf for some `s ≤ r`,
the number `s` being allowed to vary from one member of the covering to the next.  This is the
source's hypothesis that the rank of `E` is bounded: it is the rank clause of Stacks 0409 with
the rank released from being one fixed number and only capped, and it is implied by
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` for every bound `≥ r`. -/
abbrev IsFiniteLocallyFreeOfRankLE : Prop :=
  ∀ U : X.C,
    ∃ (I : Type (max u₁ v₁)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      (Sieve.ofArrows V f ∈ X.J U) ∧
        ∀ i : I, ∃ s ≤ r,
          ∃ (ι : ∀ _ : Fin s,
              SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)) ⟶
                F.over (V i)),
            Nonempty (IsColimit (Cofan.mk (F.over (V i)) ι))

/-- **The sieve of objects with free sections of some rank `≤ r`.**  This is
`AlgebraicGeometry.RingedSite.trivialisedSieve` with the rank of the trivialisation existentially
quantified under the bound, so that it is the trivialising sieve belonging to a *bound* on the
rank rather than to a fixed rank. -/
def trivialisedSieveLE (U : X.C) : Sieve U where
  arrows := fun Z _ => ∃ (A : X.C) (_ : Z ⟶ A) (s : ℕ), s ≤ r ∧
    ∃ ι : ∀ _ : Fin s,
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over A) ⟶ F.over A,
      Nonempty (IsColimit (Cofan.mk (F.over A) ι))
  downward_closed := fun {_ _ _} h g => by
    obtain ⟨A, a, s, hs, hA⟩ := h
    exact ⟨A, g ≫ a, s, hs, hA⟩

/-- **The trivialising sieve of a module of rank bounded by `r` is covering.**  Each member of
the trivialising covering of `U` furnished by the bound reaches itself with the rank it carries
there. -/
theorem trivialisedSieveLE_mem (h : IsFiniteLocallyFreeOfRankLE X F r) (U : X.C) :
    trivialisedSieveLE X F r U ∈ X.J U := by
  obtain ⟨I, V, f, hcov, hfree⟩ := h U
  refine X.J.superset_covering ?_ hcov
  intro Z k hk
  obtain ⟨j, q, _⟩ := Sieve.ofArrows.exists hk
  obtain ⟨s, hs, hfree'⟩ := hfree j
  exact ⟨V j, q, s, hs, hfree'⟩

/-- **Sections over an object reached by the bounded trivialising sieve are free of some rank
`≤ r`.**  The rank is the one carried by the trivialisation reached, and so depends on the
arrow. -/
theorem exists_nonempty_basis_of_trivialisedSieveLE {U Z : X.C} (k : Z ⟶ U)
    (hk : trivialisedSieveLE X F r U k) :
    ∃ s ≤ r, Nonempty (Module.Basis (Fin s)
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op Z))
      (F.val.obj (Opposite.op Z))) := by
  obtain ⟨A, a, s, hs, ι, ⟨hc⟩⟩ := hk
  exact ⟨s, hs,
    SheafOfModules.nonempty_basis_of_isColimit_cofan_unit ι hc (Opposite.op (Over.mk a))⟩

end AlgebraicGeometry.RingedSite

namespace Crystalline

open GlobalCrystallineSituation

namespace GlobalCrystallineSituation

/-- **The big crystalline site as a ringed site.**  The underlying category is the category of
divided power thickenings, the topology is the crystalline Zariski topology, and the structure
sheaf is `𝒪_{X/S}` with its commutative ring structure retained.  Its `ringSheaf` is
`Crystalline.GlobalCrystallineSituation.crystallineStructureSheaf`, so a crystal is a sheaf of
modules on this ringed site and the rank condition of Stacks 0409 applies to it. -/
noncomputable def crystallineRingedSite (S : GlobalCrystallineSituation.{u}) :
    AlgebraicGeometry.RingedSite.{u + 1, u, u} where
  C := Thickening S
  J := topology S
  O := ⟨structureSheaf S, structureSheaf_isSheaf S⟩

/-- **The structure sheaf of rings of the crystalline ringed site is `𝒪_{X/S}`.** -/
theorem crystallineRingedSite_ringSheaf (S : GlobalCrystallineSituation.{u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (crystallineRingedSite S).O) =
      crystallineStructureSheaf S := rfl

/-- **Sections of `𝒪_{X/S}` commute.**  The structure sheaf of the big crystalline site is a sheaf
of commutative rings; this records the commutativity after the forgetful passage to rings, in the
form needed by the matrix computation. -/
theorem crystallineStructureSheaf_mul_comm (S : GlobalCrystallineSituation.{u})
    (U : (Thickening S)ᵒᵖ) (a b : (crystallineStructureSheaf S).obj.obj U) :
    a * b = b * a := by
  let : CommRing ((crystallineStructureSheaf S).obj.obj U) :=
    ((structureSheaf S).obj U).commRing
  exact mul_comm a b

end GlobalCrystallineSituation

variable {T : FCrystalSituation.{u}} (E : FCrystal T)

/-- **Rescaling a quasi-inverse of the Frobenius structure map.**  If
`F_E ≫ V = p ^ i • 𝟙` then `V' = p ^ N • V` satisfies `F_E ≫ V' = p ^ (N + i) • 𝟙`. -/
theorem FCrystal.frobenius_comp_nsmul {i N : ℕ}
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal)) :
    E.frobenius ≫ ((T.global.p ^ N) • V) =
      (T.global.p ^ (N + i)) • 𝟙 (T.frobeniusModulePullback.obj E.crystal) := by
  rw [Preadditive.comp_nsmul, hV, smul_smul, pow_add]

/-- A quasi-inverse `F_E ≫ V = p ^ i • 𝟙` kills every map into `(F_X)_cris^* E` that `F_E` kills. -/
private theorem FCrystal.pow_nsmul_eq_zero_of_comp_frobenius_eq_zero {i : ℕ}
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    {Q : SheafOfModules.{u} (crystallineStructureSheaf T.global)}
    (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal) (hq : q ≫ E.frobenius = 0) :
    (T.global.p ^ i) • q = 0 := by
  have h : q ≫ (E.frobenius ≫ V) = 0 := by rw [← Category.assoc, hq, zero_comp]
  rwa [hV, Preadditive.comp_nsmul, Category.comp_id] at h

/-- **The kernel of the Frobenius structure map of a nondegenerate F-crystal is killed by a power
of `p`.**  The kernel is described by its universal property: there is an `i` such that every map
into `(F_X)_cris^* E` which `F_E` sends to zero is killed by `p ^ i`.  No bound on the rank of the
crystal is needed. -/
theorem FCrystal.exists_pow_nsmul_eq_zero_of_nondegenerate (hE : E.Nondegenerate) :
    ∃ j : ℕ, ∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
      (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal),
      q ≫ E.frobenius = 0 → (T.global.p ^ j) • q = 0 := by
  obtain ⟨i, V, hV⟩ := hE
  exact ⟨i, fun Q q hq ↦ E.pow_nsmul_eq_zero_of_comp_frobenius_eq_zero hV q hq⟩

/-- **A quasi-inverse of the Frobenius structure map on the other side kills its cokernel.**  If
`V ≫ F_E = p ^ j • 𝟙` then every map out of `E` which kills the image of `F_E` is killed by
`p ^ j`, which is the universal property of the cokernel of `F_E`.

This is the last step of the source's argument.  Its input, the second-sided identity, is obtained
from nondegeneracy and a bound on the rank in
`Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank`. -/
theorem FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero {j : ℕ}
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : V ≫ E.frobenius = (T.global.p ^ j) • 𝟙 E.crystal)
    {Q : SheafOfModules.{u} (crystallineStructureSheaf T.global)} (q : E.crystal ⟶ Q)
    (hq : E.frobenius ≫ q = 0) : (T.global.p ^ j) • q = 0 := by
  have h : (V ≫ E.frobenius) ≫ q = 0 := by rw [Category.assoc, hq, comp_zero]
  rwa [hV, Preadditive.nsmul_comp, Category.id_comp] at h

section Rank

variable {r : ℕ}

/-- **On a covering sieve, the Frobenius pullback of a crystal of rank `r` has free sections of
rank `r`.**  The Frobenius pullback is restriction along the Frobenius endofunctor of
`CRIS(X/S)`, so its sections over `Z` are the sections of `E` over the image of `Z`; the sieve of
objects whose image is reached by the trivialising sieve of `E` is covering because that
endofunctor is cocontinuous. -/
theorem FCrystal.exists_sieve_nonempty_basis_frobeniusModulePullback
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r) (U : Thickening T.global) :
    ∃ S : Sieve U, S ∈ topology T.global U ∧ ∀ ⦃Z : Thickening T.global⦄ (k : Z ⟶ U), S k →
      Nonempty (Module.Basis (Fin r)
        ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
        ((T.frobeniusModulePullback.obj E.crystal).val.obj (Opposite.op Z))) := by
  refine ⟨(AlgebraicGeometry.RingedSite.trivialisedSieve (crystallineRingedSite T.global)
      E.crystal r ((T.frobeniusChangeBase).obj U)).functorPullback (T.frobeniusChangeBase),
    (T.frobeniusChangeBase).cover_lift (topology T.global) (topology T.global)
      (AlgebraicGeometry.RingedSite.trivialisedSieve_mem _ _ _ hE _), ?_⟩
  intro Z k hk
  exact AlgebraicGeometry.RingedSite.nonempty_basis_of_trivialisedSieve
    (crystallineRingedSite T.global) E.crystal r ((T.frobeniusChangeBase).map k) hk

/-- Every object has a covering sieve on which `E` and its Frobenius pullback are both free of
rank `r`. -/
private theorem FCrystal.exists_sieve_nonempty_basis_both
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r) (U : Thickening T.global) :
    ∃ S : Sieve U, S ∈ topology T.global U ∧ ∀ ⦃Z : Thickening T.global⦄ (k : Z ⟶ U), S k →
      Nonempty (Module.Basis (Fin r)
        ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
        (E.crystal.val.obj (Opposite.op Z))) ∧
      Nonempty (Module.Basis (Fin r)
        ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
        ((T.frobeniusModulePullback.obj E.crystal).val.obj (Opposite.op Z))) := by
  obtain ⟨S₂, hS₂, hb₂⟩ := E.exists_sieve_nonempty_basis_frobeniusModulePullback hE U
  exact ⟨AlgebraicGeometry.RingedSite.trivialisedSieve (crystallineRingedSite T.global)
      E.crystal r U ⊓ S₂,
    (topology T.global).intersection_covering
      (AlgebraicGeometry.RingedSite.trivialisedSieve_mem _ _ _ hE U) hS₂,
    fun Z k hk => ⟨AlgebraicGeometry.RingedSite.nonempty_basis_of_trivialisedSieve
      (crystallineRingedSite T.global) E.crystal r k hk.1, hb₂ k hk.2⟩⟩

/-- **The second-sided identity, Stacks 07N4.**  Let `(E, F_E)` be an F-crystal whose underlying
crystal has constant rank `r`, let `V` be a quasi-inverse of `F_E` on one side,
`F_E ≫ V = p ^ i • 𝟙`, and let `N ≥ r * i`.  Then `V' = p ^ N • V` is a quasi-inverse on the other
side as well: `V' ≫ F_E = p ^ (N + i) • 𝟙`.  The identity is an equality of morphisms of sheaves
of modules, so it is checked on a covering sieve of each object; on such a sieve both `E` and its
Frobenius pullback have free sections of rank `r`, and there the statement is the matrix identity
`L (p ^ N K) = p ^ (N + i) 1` of
`Matrix.mul_pow_smul_eq_smul_one_of_card_le`. -/
theorem FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rank {i N : ℕ}
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : r * i ≤ N) :
    ((T.global.p ^ N) • V) ≫ E.frobenius = (T.global.p ^ (N + i)) • 𝟙 E.crystal := by
  refine SheafOfModules.hom_ext_of_sieve (fun U => ?_)
  obtain ⟨S, hS, hb⟩ := E.exists_sieve_nonempty_basis_both hE U
  refine ⟨S, hS, fun Z k hk x => ?_⟩
  obtain ⟨⟨bF⟩, ⟨bG⟩⟩ := hb k hk
  exact SheafOfModules.nsmul_comp_val_app_apply (Opposite.op Z)
    (crystallineStructureSheaf_mul_comm T.global (Opposite.op Z)) bF bG hN hV x

/-- **The cokernel of the Frobenius structure map of a nondegenerate F-crystal of constant rank is
killed by a power of `p`, Stacks 07N4.**  This is
`Crystalline.FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero` with its hypothesis discharged: the
two-sided identity is not assumed but obtained from nondegeneracy and the rank condition by
`Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rank`. -/
theorem FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_rank {i N : ℕ}
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : r * i ≤ N)
    {Q : SheafOfModules.{u} (crystallineStructureSheaf T.global)} (q : E.crystal ⟶ Q)
    (hq : E.frobenius ≫ q = 0) : (T.global.p ^ (N + i)) • q = 0 :=
  FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero E
    (FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rank E hE hV hN) q hq

/-- **A single power of `p` kills both the kernel and the cokernel, Stacks 07N4.**  This is the
assertion the remark says is "what is needed for the result below": for a nondegenerate F-crystal
whose underlying crystal has constant rank, there is one integer `j ≥ 0` such that `p ^ j`
annihilates both the kernel and the cokernel of `F_E`, both described by their universal
properties.  No identity on the second side is assumed. -/
theorem FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r)
    (hnd : E.Nondegenerate) :
    ∃ j : ℕ,
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal),
        q ≫ E.frobenius = 0 → (T.global.p ^ j) • q = 0) ∧
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : E.crystal ⟶ Q), E.frobenius ≫ q = 0 → (T.global.p ^ j) • q = 0) := by
  obtain ⟨i, V, hV⟩ := hnd
  refine ⟨r * i + i, fun Q q hq => ?_, fun Q q hq => ?_⟩
  · rw [pow_add, mul_smul, E.pow_nsmul_eq_zero_of_comp_frobenius_eq_zero hV q hq, smul_zero]
  · exact FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_rank E hE hV le_rfl q hq

end Rank

section BoundedRank

/-- **A common local rank, bounded by `rmax`, for a crystal and for its Frobenius pullback.**
Every object of the big crystalline site has a covering sieve on the source of each of whose
arrows the sections of `E` and of `(F_X)_cris^* E` are *both* free of one rank `s ≤ rmax`, the
rank being allowed to vary from one arrow to the next.

This is exactly the local input the second-sided identity of Stacks 07N4 consumes: the matrix
computation is about square matrices, so it needs the two sides to have a common size over each
object, and it needs that size only to be bounded, not constant — the bound enters through
`Matrix.mul_pow_smul_eq_smul_one_of_card_le`, and one exponent `N ≥ rmax * i` serves every
object at once, so no maximum over the ranks occurring has to be taken.

The agreement of the two ranks over an arrow is what the computation consumes and cannot be
weakened to a bound on one side alone:
`LinearMap.exists_comp_eq_smul_id_and_forall_comp_pow_smul_ne_smul_id` exhibits free modules of
ranks `1` and `2` and a one-sided scalar quasi-inverse between them which no rescaling makes
two-sided.

A crystal of constant rank `r` satisfies this predicate with `rmax = r`
(`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`), and a crystal whose rank is bounded by
`rmax` satisfies it with that bound (`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE`).
-/
def FCrystal.HasBoundedCommonLocalRank (rmax : ℕ) : Prop :=
  ∀ U : Thickening T.global, ∃ S : Sieve U, S ∈ topology T.global U ∧
    ∀ ⦃Z : Thickening T.global⦄ (k : Z ⟶ U), S k → ∃ s ≤ rmax,
      Nonempty (Module.Basis (Fin s)
          ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
          (E.crystal.val.obj (Opposite.op Z))) ∧
        Nonempty (Module.Basis (Fin s)
          ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
          ((T.frobeniusModulePullback.obj E.crystal).val.obj (Opposite.op Z)))

/-- **A crystal of constant rank `r` has `r` as a common local rank, bounded by `r`.**  Both
halves are the two trivialising sieves already used for the constant-rank form of the identity:
the trivialising sieve of `E` itself and its Frobenius pullback. -/
theorem FCrystal.hasBoundedCommonLocalRank_of_rank {r : ℕ}
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (crystallineRingedSite T.global) E.crystal r) :
    E.HasBoundedCommonLocalRank r := by
  intro U
  obtain ⟨S, hS, hb⟩ := E.exists_sieve_nonempty_basis_both hE U
  exact ⟨S, hS, fun Z k hk => ⟨r, le_rfl, hb k hk⟩⟩

/-- **On a covering sieve, the Frobenius pullback of a crystal of rank bounded by `rmax` has free
sections of some rank `≤ rmax`.**  This is
`Crystalline.FCrystal.exists_sieve_nonempty_basis_frobeniusModulePullback` with the rank released
from being fixed and only bounded; the rank obtained over an object `Z` is the one `E` carries
over the image of `Z` under the Frobenius endofunctor, which is why it is not tied to the rank of
`E` over `Z` itself. -/
theorem FCrystal.exists_sieve_nonempty_basis_frobeniusModulePullback_le {rmax : ℕ}
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax) (U : Thickening T.global) :
    ∃ S : Sieve U, S ∈ topology T.global U ∧ ∀ ⦃Z : Thickening T.global⦄ (k : Z ⟶ U), S k →
      ∃ s ≤ rmax, Nonempty (Module.Basis (Fin s)
        ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
        ((T.frobeniusModulePullback.obj E.crystal).val.obj (Opposite.op Z))) := by
  refine ⟨(AlgebraicGeometry.RingedSite.trivialisedSieveLE (crystallineRingedSite T.global)
      E.crystal rmax ((T.frobeniusChangeBase).obj U)).functorPullback (T.frobeniusChangeBase),
    (T.frobeniusChangeBase).cover_lift (topology T.global) (topology T.global)
      (AlgebraicGeometry.RingedSite.trivialisedSieveLE_mem _ _ _ hE _), ?_⟩
  intro Z k hk
  exact AlgebraicGeometry.RingedSite.exists_nonempty_basis_of_trivialisedSieveLE
    (crystallineRingedSite T.global) E.crystal rmax ((T.frobeniusChangeBase).map k) hk

/-- **An object of `CRIS(X/S)` with nontrivial ring of sections has a nonempty thickened
scheme.**  A nontrivial ring of global sections forces the ambient scheme `T` to be nonempty, and
the immersion `U ⟶ T` of a thickening is surjective. -/
theorem GlobalCrystallineSituation.Thickening.nonempty_source {S : GlobalCrystallineSituation.{u}}
    (Z : Thickening S) [Nontrivial Γ(Z.thickening.target.scheme, ⊤)] :
    Nonempty Z.thickening.source := by
  have hT : Nonempty Z.thickening.target.scheme := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton Γ(Z.thickening.target.scheme, ⊤) inferInstance
  obtain ⟨y⟩ := hT
  obtain ⟨x, -⟩ := Z.thickening.isThickening.2 y
  exact ⟨x⟩

/-- **An object of `CRIS(X/S)` with nontrivial ring of sections has a thickened scheme with
nontrivial global sections**, the thickened scheme being nonempty. -/
theorem GlobalCrystallineSituation.Thickening.nontrivial_source {S : GlobalCrystallineSituation.{u}}
    (Z : Thickening S) [Nontrivial Γ(Z.thickening.target.scheme, ⊤)] :
    Nontrivial Γ(Z.thickening.source, ⊤) := by
  obtain ⟨x⟩ := Z.nonempty_source
  have : Nonempty (⊤ : Z.thickening.source.Opens) := ⟨⟨x, trivial⟩⟩
  infer_instance

/-- **A scheme over `X` is in characteristic `p`**, `p` vanishing on `X` already. -/
theorem FCrystalSituation.isInCharacteristic_left (T : FCrystalSituation.{u})
    (Y : Over T.global.X) : Stacks.Frobenius.IsInCharacteristic Y.left T.global.p :=
  AlgebraicGeometry.isInCharacteristic_of_hom Y.hom T.global.p T.isInCharacteristic

/-- **The absolute Frobenius of a scheme over `X`, as a morphism of `CRIS(X/S)`.**  For a scheme
`U` over `X`, the absolute Frobenius `F_U` is a morphism from the Frobenius twist
`(F_X)_cris (U, U, ∅)` of the trivial thickening `(U, U, ∅)` to `(U, U, ∅)` itself: it is a divided
power morphism because both divided power ideals are zero, it lies over `X` because the absolute
Frobenius is natural, `F_U ≫ (U ⟶ X) = (U ⟶ X) ≫ F_X`, and it lies over the divided power base
because `Spec(σ)` lifts the absolute Frobenius of the closed fibre `S₀`.  No such lift exists on a
general object of `CRIS(X/S)`; on a trivial thickening it does. -/
noncomputable def FCrystalSituation.freeFrobenius (T : FCrystalSituation.{u})
    (Y : Over T.global.X) :
    T.frobeniusChangeBase.obj ((free T.global).obj Y) ⟶ (free T.global).obj Y where
  sourceHom := Stacks.Frobenius.absoluteFrobenius Y.left T.global.p (T.isInCharacteristic_left Y)
  targetHom :=
    { hom := Stacks.Frobenius.absoluteFrobenius Y.left T.global.p (T.isInCharacteristic_left Y)
      compatible := isDPMorphism_trivial_trivial
        (Stacks.Frobenius.absoluteFrobenius Y.left T.global.p (T.isInCharacteristic_left Y)) }
  immersion_naturality := (Category.id_comp _).trans (Category.comp_id _).symm
  base_naturality := by
    refine DividedPowerScheme.Hom.ext ?_
    have h1 := DividedPowerScheme.closedFiberMap_comp_closedFiberι T.specSigma
    have h2 := T.toClosedFiber_comp_closedFiberMap_specSigma
    have h3 := Stacks.Frobenius.absoluteFrobenius_naturality Y.hom T.global.p
      (T.isInCharacteristic_left Y) T.isInCharacteristic
    change Stacks.Frobenius.absoluteFrobenius Y.left T.global.p (T.isInCharacteristic_left Y) ≫
        (Y.hom ≫ T.global.toClosedFiber ≫ DividedPowerScheme.closedFiberι T.global.S) =
      (Y.hom ≫ T.global.toClosedFiber ≫ DividedPowerScheme.closedFiberι T.global.S) ≫
        T.specSigma.hom
    rw [← Category.assoc, h3, Category.assoc, Category.assoc, Category.assoc, ← h1,
      ← Category.assoc T.global.toClosedFiber, h2, FCrystalSituation.frobenius,
      Category.assoc]
  toX_naturality :=
    Stacks.Frobenius.absoluteFrobenius_naturality Y.hom T.global.p (T.isInCharacteristic_left Y)
      T.isInCharacteristic

/-- **A crystal of rank bounded by `rmax` has a bounded common local rank with its Frobenius
pullback.**  The source reads `F_E` and `V` over an object as two `r × r` matrices; this is the
statement that this is legitimate.

The covering sieve is the intersection of the trivialising sieve of `E` and the pullback, along the
cocontinuous Frobenius endofunctor `u` of `CRIS(X/S)`, of the trivialising sieve of `E` over the
image of the object.  Over an arrow `Z ⟶ U` of it, `E` is free of some rank `s ≤ rmax` over `Z`,
being a coproduct of `s` copies of `𝒪_{X/S}` over some `B` that `Z` maps to, and
`(F_X)_cris^* E` is free of some rank `t ≤ rmax` over `Z`, `E` being a coproduct of `t` copies over
some `A` that `u(Z)` maps to.  The two ranks agree as soon as the ring of sections over `Z` is
nontrivial, and they are compared on a single object: the Frobenius twist `u(W)` of the trivial
thickening `W = (U', U', ∅)` of the thickened scheme `U'` of `Z`.  It maps to `A` through
`u(W ⟶ Z) : u(W) ⟶ u(Z)`, and to `B` through the absolute Frobenius
`Crystalline.FCrystalSituation.freeFrobenius : u(W) ⟶ W` followed by `W ⟶ Z`, so the sections of
`E` over `u(W)` are free of rank `t` and of rank `s` over the ring of global sections of `U'`,
which is nontrivial. -/
theorem FCrystal.hasBoundedCommonLocalRank_of_rankLE {rmax : ℕ}
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax) :
    E.HasBoundedCommonLocalRank rmax := by
  intro U
  refine ⟨AlgebraicGeometry.RingedSite.trivialisedSieveLE (crystallineRingedSite T.global)
      E.crystal rmax U ⊓
      (AlgebraicGeometry.RingedSite.trivialisedSieveLE (crystallineRingedSite T.global)
        E.crystal rmax ((T.frobeniusChangeBase).obj U)).functorPullback (T.frobeniusChangeBase),
    (topology T.global).intersection_covering
      (AlgebraicGeometry.RingedSite.trivialisedSieveLE_mem _ _ _ hE U)
      ((T.frobeniusChangeBase).cover_lift (topology T.global) (topology T.global)
        (AlgebraicGeometry.RingedSite.trivialisedSieveLE_mem _ _ _ hE _)), ?_⟩
  rintro Z k ⟨⟨B, b, s, hs, ιB, ⟨hB⟩⟩, ⟨A, a, t, -, ιA, ⟨hA⟩⟩⟩
  have hbs : Nonempty (Module.Basis (Fin s)
      ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
      (E.crystal.val.obj (Opposite.op Z))) :=
    SheafOfModules.nonempty_basis_of_isColimit_cofan_unit ιB hB (Opposite.op (Over.mk b))
  have hbt : Nonempty (Module.Basis (Fin t)
      ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
      ((T.frobeniusModulePullback.obj E.crystal).val.obj (Opposite.op Z))) :=
    SheafOfModules.nonempty_basis_of_isColimit_cofan_unit ιA hA (Opposite.op (Over.mk a))
  by_cases hnt : Nontrivial ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z))
  · have : Nontrivial Γ(Z.thickening.target.scheme, ⊤) := hnt
    have : Nontrivial Γ(Z.thickening.source, ⊤) := Z.nontrivial_source
    let W : Thickening T.global := (free T.global).obj ((forget T.global).obj Z)
    let ιW : W ⟶ Z := (freeForgetAdjunction T.global).counit.app Z
    have : Nontrivial ((crystallineStructureSheaf T.global).obj.obj
        (Opposite.op ((T.frobeniusChangeBase).obj W))) :=
      (inferInstance : Nontrivial Γ(Z.thickening.source, ⊤))
    obtain rfl : s = t := SheafOfModules.eq_of_isColimit_cofan_unit ιA hA ιB hB
      ((T.frobeniusChangeBase).map ιW ≫ a)
      (T.freeFrobenius ((forget T.global).obj Z) ≫ ιW ≫ b)
      (crystallineStructureSheaf_mul_comm T.global _) this
    exact ⟨s, hs, hbs, hbt⟩
  · have : Subsingleton ((crystallineStructureSheaf T.global).obj.obj (Opposite.op Z)) :=
      not_nontrivial_iff_subsingleton.mp hnt
    exact ⟨s, hs, hbs, Module.nonempty_basis_of_subsingleton s⟩

/-- **The second-sided identity from a bounded common local rank, Stacks 07N4.**  Let `(E, F_E)`
be an F-crystal, let `V` be a quasi-inverse of `F_E` on one side, `F_E ≫ V = p ^ i • 𝟙`, suppose
`E` and `(F_X)_cris^* E` have a common local rank bounded by `rmax`, and let `N ≥ rmax * i`.
Then `V' = p ^ N • V` is a quasi-inverse on the other side as well:
`V' ≫ F_E = p ^ (N + i) • 𝟙`.

Only a *bound* on that common rank is used, as in the source only a bound on the rank enters: the
identity is checked on the covering sieve supplied by the hypothesis, and over an arrow of that
sieve both sides are free of one rank `s ≤ rmax`, so `s * i ≤ rmax * i ≤ N` and the matrix
identity `Matrix.mul_pow_smul_eq_smul_one_of_card_le` applies with the same exponent `N` at every
object.  The hypothesis is weaker than constant rank, which implies it by
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`, so this is more general than
`Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rank`.

The agreement of the two ranks over each arrow is not a removable convenience: by
`LinearMap.exists_comp_eq_smul_id_and_forall_comp_pow_smul_ne_smul_id` a one-sided scalar
quasi-inverse between free modules of unequal rank need not become two-sided after any
rescaling. -/
theorem FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank {i N rmax : ℕ}
    (hE : E.HasBoundedCommonLocalRank rmax)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : rmax * i ≤ N) :
    ((T.global.p ^ N) • V) ≫ E.frobenius = (T.global.p ^ (N + i)) • 𝟙 E.crystal := by
  refine SheafOfModules.hom_ext_of_sieve (fun U => ?_)
  obtain ⟨S, hS, hb⟩ := hE U
  refine ⟨S, hS, ?_⟩
  intro Z k hk x
  obtain ⟨s, hs, ⟨bF⟩, ⟨bG⟩⟩ := hb k hk
  exact SheafOfModules.nsmul_comp_val_app_apply (Opposite.op Z)
    (crystallineStructureSheaf_mul_comm T.global (Opposite.op Z)) bF bG
    ((Nat.mul_le_mul hs (le_refl i)).trans hN) hV x

/-- **The cokernel of the Frobenius structure map is killed by a power of `p` under a bounded
common local rank, Stacks 07N4.**  This is
`Crystalline.FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero` with its hypothesis discharged
from nondegeneracy and a bound `rmax` on the common local rank of `E` and `(F_X)_cris^* E`.  It
is more general than `Crystalline.FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_rank`,
constant rank implying the hypothesis by
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`. -/
theorem FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_boundedCommonLocalRank
    {i N rmax : ℕ} (hE : E.HasBoundedCommonLocalRank rmax)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : rmax * i ≤ N)
    {Q : SheafOfModules.{u} (crystallineStructureSheaf T.global)} (q : E.crystal ⟶ Q)
    (hq : E.frobenius ≫ q = 0) : (T.global.p ^ (N + i)) • q = 0 :=
  FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero E
    (FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank E hE hV hN) q hq

/-- **A single power of `p` kills both the kernel and the cokernel, under a bounded common local
rank, Stacks 07N4.**  The exponent is `rmax * i + i`, with `rmax` the bound and `p ^ i` the
scalar furnished by nondegeneracy; it is one exponent for the whole site, the bound making a
maximum over the ranks that occur unnecessary.  The kernel half needs no rank hypothesis at all
(`Crystalline.FCrystal.exists_pow_nsmul_eq_zero_of_nondegenerate`); the common local rank is used
only for the cokernel half. -/
theorem FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_boundedCommonLocalRank {rmax : ℕ}
    (hE : E.HasBoundedCommonLocalRank rmax) (hnd : E.Nondegenerate) :
    ∃ j : ℕ,
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal),
        q ≫ E.frobenius = 0 → (T.global.p ^ j) • q = 0) ∧
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : E.crystal ⟶ Q), E.frobenius ≫ q = 0 → (T.global.p ^ j) • q = 0) := by
  obtain ⟨i, V, hV⟩ := hnd
  refine ⟨rmax * i + i, fun Q q hq => ?_, fun Q q hq => ?_⟩
  · rw [pow_add, mul_smul, E.pow_nsmul_eq_zero_of_comp_frobenius_eq_zero hV q hq, smul_zero]
  · exact FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_boundedCommonLocalRank E hE hV
      le_rfl q hq

end BoundedRank

end Crystalline

end
