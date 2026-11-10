module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheoryChow
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme

/-!
# Graded pieces, codimension Chow groups and the pushforward of cycles for Weil cohomology

Helpers for stating the axioms of Section 45.9 (Tag 0FHA) and Section 45.14 (Tag 0FID) of the
Stacks Project on data `Stacks.WeilCohomology.FirstChernClassData` (D0), (D1), (D2'). Definition
0FI2 itself is `Stacks.WeilCohomology.WeilCohomologyTheory`
(`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/WeilCohomologyTheory.lean`), and the
point `Spec k` is `Stacks.WeilCohomology.SmoothProjectiveScheme.point`
(`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/WeilData.lean`).

## Main definitions

* `Stacks.WeilCohomology.gradedPieceMul`, `gradedPieceCast`, `gradedPieceMap`, `gradedCrossMul`:
  the cup product, the identification of equal degrees, pullback and the cross product on the
  graded pieces `H^n(X)` of a graded algebra.
* `Stacks.WeilCohomology.chowCodimTotal`, `chowCodimPart`: the two canonical maps between
  `CH^i(X) = ∏_d CH_{d-i}(X_d)` (`Stacks.Chow.codimensionChowGroup`, Section 0FE2) and
  `CH_*(X)`.
* `Stacks.WeilCohomology.chowCodimFundamental`: `[X] ∈ CH^0(X)` with coordinates `[X_d]`.
* `Stacks.WeilCohomology.chowCodimPushforward`: proper pushforward `f_* : CH^r(X) → CH^s(Y)` of
  Stacks 02R4 for any proper morphism of schemes smooth over `k`, read through those maps.

## References

* [Stacks Project, Section 0FHA](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Section 0FE2](https://stacks.math.columbia.edu/tag/0FE2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

/-! ### Graded pieces -/

section Graded

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A] (𝒜 : ℤ → Submodule F A)
  [_root_.GradedAlgebra 𝒜]

/-- The cup product `H^a × H^b → H^{a+b}` on graded pieces. -/
def gradedPieceMul (a b : ℤ) : 𝒜 a →ₗ[F] 𝒜 b →ₗ[F] 𝒜 (a + b) :=
  LinearMap.mk₂ F (fun x y ↦ ⟨x * y, SetLike.GradedMul.mul_mem x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

/-- The identification `H^a = H^b` of graded pieces of equal degree. -/
def gradedPieceCast {a b : ℤ} (h : a = b) : 𝒜 a ≃ₗ[F] 𝒜 b :=
  LinearEquiv.ofEq _ _ (congrArg 𝒜 h)

end Graded

/-- The restriction `H^n(Y) → H^n(X)` of a map of graded algebras to the degree-`n` piece. -/
def gradedPieceMap {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B]
    [Algebra F B] (𝒜 : ℤ → Submodule F A) (ℬ : ℤ → Submodule F B) (φ : A →ₐ[F] B)
    (hφ : ∀ n a, a ∈ 𝒜 n → φ a ∈ ℬ n) (n : ℤ) : 𝒜 n →ₗ[F] ℬ n :=
  φ.toLinearMap.restrict (hφ n)

/-- The cross product `H^a(X) × H^b(Y) → H^{a+b}(P)`, `(x, y) ↦ p^*x ∪ q^*y`, for maps of
graded algebras `p^* : H^*(X) → H^*(P)` and `q^* : H^*(Y) → H^*(P)`. -/
def gradedCrossMul {F : Type*} [Field F] {A B C : Type*} [Ring A] [Algebra F A] [Ring B]
    [Algebra F B] [Ring C] [Algebra F C] (𝒜 : ℤ → Submodule F A) (ℬ : ℤ → Submodule F B)
    (𝒞 : ℤ → Submodule F C) [_root_.GradedAlgebra 𝒞] (p : A →ₐ[F] C) (q : B →ₐ[F] C)
    (hp : ∀ n a, a ∈ 𝒜 n → p a ∈ 𝒞 n) (hq : ∀ n b, b ∈ ℬ n → q b ∈ 𝒞 n) (a b : ℤ) :
    𝒜 a →ₗ[F] ℬ b →ₗ[F] 𝒞 (a + b) :=
  (gradedPieceMul 𝒞 a b).compl₁₂ (gradedPieceMap 𝒜 𝒞 p hp a) (gradedPieceMap ℬ 𝒞 q hq b)

/-! ### Chow groups of codimension `i` of a smooth scheme over `k` -/

section Chow

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]

/-- **The class `α_{(n)} ∈ CH_n(X)` of dimension `n` of a codimension-`i` class `α`**: its
restriction to `X_d` is `α_d` when `d - i = n`, and zero otherwise. -/
def chowCodimTotal (i : ℕ) (n : ℤ) :
    codimensionChowGroup k sX i →+ chowGroup (fieldChowSituation k) sX n where
  toFun α := (chowGroupDimPartEquiv k sX n).symm fun d ↦
    if h : (d.down : ℤ) - i = n then chowGroupDegreeEquiv (fieldChowSituation k) _ h (α d.down)
    else 0
  map_zero' := by
    rw [AddEquiv.symm_apply_eq, map_zero]
    funext d
    split_ifs <;> simp
  map_add' α β := by
    rw [AddEquiv.symm_apply_eq, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    funext d
    simp only [Pi.add_apply]
    split_ifs <;> simp

/-- **The codimension-`j` part of a family of classes `β_n ∈ CH_n(X)`, one in each dimension**:
its coordinate on `X_d` is the restriction of `β_{d-j}`. -/
def chowCodimPart (β : ∀ n : ℤ, chowGroup (fieldChowSituation k) sX n) (j : ℕ) :
    codimensionChowGroup k sX j := fun d ↦
  chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl _ (β _)

/-- The fundamental class `[X] ∈ CH^0(X)`, whose coordinate on `X_d` is `[X_d]`. -/
def chowCodimFundamental : codimensionChowGroup k sX ((0 : ℕ) : ℤ) := fun d ↦
  fundamentalChowClass (fieldChowSituation k) (partBase sX d) _

/-- **The proper pushforward `f_* : CH^r(X) → CH^*(Y)`**, read in codimension `s`, of a proper
morphism `f : X ⟶ Y` of schemes smooth over `k`: proper pushforward `CH_n(X) → CH_n(Y)` of
Stacks 02R4 (descended to Chow groups by Stacks 02S2) in each dimension, and the
codimension-`s` part of the result. -/
def chowCodimPushforward (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ)
    (α : codimensionChowGroup k sX r) : codimensionChowGroup k sY s :=
  chowCodimPart k sY (fun n ↦ properChowPushforward (fieldChowSituation k) sX sY f hf n
    (properPushforwardDescends _ _ _ _ _ _) (chowCodimTotal k sX r n α)) s

end Chow

/-! ### Smooth projective schemes -/

open SmoothProjectiveScheme

/-- A morphism `f : X ⟶ Y` of smooth projective schemes over `k` is proper as a morphism of
schemes. -/
instance SmoothProjectiveScheme.isProper_map {k : Type u} [Field k]
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    IsProper ((toScheme k).map f) := by
  have := (isProjective X).isProper
  have := (isProjective Y).isProper
  have : IsProper ((toScheme k).map f ≫ Y.obj.hom) := by rw [w f]; infer_instance
  exact IsProper.of_comp _ Y.obj.hom

end Stacks.WeilCohomology

end
