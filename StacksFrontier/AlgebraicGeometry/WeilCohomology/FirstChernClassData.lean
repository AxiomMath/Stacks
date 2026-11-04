module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality

/-!
# Weil cohomology theories, III: the data and the first four axioms

Section 45.14 of the Stacks Project (Tag 0FID) fixes a field `k` and a field `F` of
characteristic zero, and the data

* (D0) a one-dimensional `F`-vector space `F(1)`;
* (D1) a contravariant functor `H^*` from the category of smooth projective schemes over `k` to
  the category of graded commutative `F`-algebras;
* (D2') for every smooth projective scheme `X` over `k` a homomorphism of abelian groups
  `c₁^H : Pic(X) → H^2(X)(1)`,

subject to the axioms

* (A1) `H^*` is compatible with finite coproducts: `H^*(∅) = 0` and `(i^*, j^*)` identifies
  `H^*(X ⨿ Y)` with `H^*(X) × H^*(Y)`;
* (A2) `c₁^H` is compatible with pullbacks;
* (A3) the projective bundle formula: for `ℰ` locally free of rank `r ≥ 1` on `X` with
  `p : P = 𝐏(ℰ) → X`, the map `⨁_{i < r} H^*(X)(-i) → H^*(P)`,
  `(a_i) ↦ ∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)` is an isomorphism;
* (A4) for an effective Cartier divisor `i : Y → X` with `X`, `Y` smooth projective over `k` and
  `a ∈ H^*(X)` with `i^*a = 0`, one has `a ∪ c₁^H(𝒪_X(Y)) = 0`.

This file writes the data and the axioms down.

## The formalization

* Graded commutative `F`-algebras are graded by `𝐙`, as in the conventions of the chapter: an
  `F`-algebra `H` with a `GradedAlgebra` structure `H = ⨁_{n ∈ 𝐙} H^n` and the Koszul rule
  `a ∪ b = (-1)^{nm} b ∪ a` for `a ∈ H^n`, `b ∈ H^m`. Nothing forces `H^n = 0` for `n < 0`.
* The Tate twists of (D0) are the tensor-defined twists `Stacks.WeilCohomology.tateTwist` of
  Section 45.9: `V(n) = V ⊗_F F(n)` with `F(n) = F(1)^{⊗ n}` or `F(-1)^{⊗ -n}`. A twisted class of
  `H^n(X)(m)` is an element of `H^*(X)(m)` lying in the image of `H^n(X)(m)`, and the products
  `U(n) × V(m) → W(n + m)` of the source are `Stacks.WeilCohomology.tateCup`, built from the
  canonical multiplication of the Tate lines, which exists because `F(1)` is one-dimensional.
* The category of smooth projective schemes over `k` is
  `Stacks.WeilCohomology.SmoothProjectiveScheme k`; its schemes need be neither irreducible nor
  nonempty.
* `𝒪_P(1)` is `Stacks.Chow.bundleTwist`, and `𝒪_X(Y)` for an effective Cartier divisor is
  `Stacks.Divisors.divisorSheaf`.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData`: the data (D0), (D1), (D2').
* `Stacks.WeilCohomology.FirstChernClassData.CoproductAxiom`: axiom (A1).
* `Stacks.WeilCohomology.FirstChernClassData.PullbackAxiom`: axiom (A2).
* `Stacks.WeilCohomology.FirstChernClassData.ProjectiveBundleAxiom`: axiom (A3).
* `Stacks.WeilCohomology.FirstChernClassData.DivisorAxiom`: axiom (A4).

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

/-! ### Coordinates on the Tate twists

The cup products `Stacks.WeilCohomology.tateCup` on the tensor-defined twists are defined through
the coordinates `Stacks.WeilCohomology.tateTwistCoordinates` attached to a coordinate on the
one-dimensional line, and do not depend on it. These are the identities that read them in that
coordinate. -/

section Coordinates

variable {F : Type*} [Field F] {L : Type*} [AddCommGroup L] [Module F L]
  {U V W : Type*} [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- The coordinates in twist zero are the canonical identification `V(0) = V`. -/
theorem tateTwistCoordinates_zero (c : L ≃ₗ[F] F) (x : tateTwist F L V 0) :
    tateTwistCoordinates c 0 x = tateTwistZero x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v l =>
    rw [tateTwistCoordinates_tmul]
    show _ = (TensorProduct.rid F V) (v ⊗ₜ (TensorPower.algebraMap₀ (R := F) (M := L)).symm l)
    rw [TensorProduct.rid_tmul]
    congr 1
    induction l using PiTensorProduct.induction_on with
    | smul_tprod a f =>
      rw [show tateLineCoordinates c 0 = tensorPowerCoordinates c 0 from rfl]
      simp [tensorPowerCoordinates, TensorPower.algebraMap₀,
        PiTensorProduct.constantBaseRingEquiv_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The cup product read in coordinates. -/
theorem tateTwistCoordinates_tateCup (hL : Module.finrank F L = 1)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (h : n + m = k) (u : tateTwist F L U n)
    (v : tateTwist F L V m) :
    tateTwistCoordinates (tateLineCoordinate hL) k (tateCup hL cup n m k h u v) =
      cup (tateTwistCoordinates (tateLineCoordinate hL) n u)
        (tateTwistCoordinates (tateLineCoordinate hL) m v) := by
  simp [tateCup, tateCupWith]

/-- The cup product with an untwisted first argument read in coordinates. -/
theorem tateTwistCoordinates_tateCupLeft (c : L ≃ₗ[F] F) (cup : U →ₗ[F] V →ₗ[F] W) (n : ℤ)
    (u : U) (v : tateTwist F L V n) :
    tateTwistCoordinates c n (tateCupLeft cup n u v) = cup u (tateTwistCoordinates c n v) :=
  tateTwistCoordinates_map c n (cup u) v

end Coordinates

/-- **The data (D0), (D1), (D2') of Section 45.14.** A one-dimensional `F`-vector space `F(1)`;
a contravariant functor `X ↦ H^*(X)` from smooth projective schemes over `k` to `𝐙`-graded
graded commutative `F`-algebras; and for every `X` an additive map `c₁^H : Pic(X) → H^2(X)(1)`,
`H^2(X)(1)` being read inside the tensor-defined twist `H^*(X)(1)`. -/
structure FirstChernClassData (k : Type u) [Field k] (F : Type w) [Field F] where
  /-- (D0) The Tate line `F(1)`. -/
  tate : Type w
  [addCommGroup_tate : AddCommGroup tate]
  [module_tate : Module F tate]
  /-- (D0) `F(1)` is one-dimensional. -/
  finrank_tate : Module.finrank F tate = 1
  /-- (D1) The cohomology `H^*(X)`. -/
  H : (SmoothProjectiveScheme k).FullSubcategory → Type w
  [ring : ∀ X, Ring (H X)]
  [algebra : ∀ X, Algebra F (H X)]
  /-- (D1) The grading `H^*(X) = ⨁_{n ∈ 𝐙} H^n(X)`. -/
  grade : ∀ X, ℤ → Submodule F (H X)
  [gradedAlgebra : ∀ X, _root_.GradedAlgebra (grade X)]
  /-- (D1) The cup product is graded commutative. -/
  graded_comm : ∀ (X) (i j : ℤ) (a b : H X), a ∈ grade X i → b ∈ grade X j →
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a)
  /-- (D1) The pullback `f^* : H^*(Y) → H^*(X)`. -/
  pull : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory}, (X ⟶ Y) → (H Y →ₐ[F] H X)
  pull_id : ∀ X, pull (𝟙 X) = AlgHom.id F (H X)
  pull_comp : ∀ {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull (f ≫ g) = (pull f).comp (pull g)
  /-- (D1) Pullback is a map of graded algebras. -/
  pull_grade : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : H Y), a ∈ grade Y n → pull f a ∈ grade X n
  /-- (D2') The first Chern class in cohomology `c₁^H : Pic(X) → H^2(X)(1)`, with values in
  `H^*(X)(1)`. -/
  c₁ : ∀ X, ((toScheme k).obj X).picardGroup →+ tateTwist F tate (H X) 1
  /-- (D2') Its values lie in `H^2(X)(1)`. -/
  c₁_mem : ∀ X L, c₁ X L ∈ LinearMap.range (tateTwistMap (L := tate) (grade X 2).subtype 1)

attribute [instance] FirstChernClassData.addCommGroup_tate FirstChernClassData.module_tate
  FirstChernClassData.ring FirstChernClassData.algebra FirstChernClassData.gradedAlgebra

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- The pullback `f^*` on twisted classes. -/
abbrev pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ) :
    tateTwist F 𝔇.tate (𝔇.H Y) n →ₗ[F] tateTwist F 𝔇.tate (𝔇.H X) n :=
  tateTwistMap (𝔇.pull f).toLinearMap n

/-- The cup product of `H^*(X)`. -/
abbrev cup (X : (SmoothProjectiveScheme k).FullSubcategory) : 𝔇.H X →ₗ[F] 𝔇.H X →ₗ[F] 𝔇.H X :=
  LinearMap.mul F (𝔇.H X)

/-- The unit `1 ∈ H^0(X)(0)`. -/
def unitTw (X : (SmoothProjectiveScheme k).FullSubcategory) : tateTwist F 𝔇.tate (𝔇.H X) 0 :=
  tateTwistZero.symm 1

/-- **The powers `x^n ∈ H^*(X)(n)` of a twisted class `x ∈ H^*(X)(1)`**, by the cup product. -/
def twistPow (X : (SmoothProjectiveScheme k).FullSubcategory) (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n
  | 0 => 𝔇.unitTw X
  | n + 1 => tateCup 𝔇.finrank_tate (𝔇.cup X) n 1 (n + 1) (by ring) (twistPow X x n) x

/-- **The cup product of `∏_{i ≥ 0} H^*(X)(i)`**: `(a ∪ b)_n = ∑_{i + j = n} a_i ∪ b_j`. -/
def cupConv (X : (SmoothProjectiveScheme k).FullSubcategory)
    (a b : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  fun n => ∑ i : Fin (n + 1), tateCup 𝔇.finrank_tate (𝔇.cup X) (i : ℕ) (n - i : ℕ) n
    (by have := i.2; omega) (a i) (b (n - i))

/-- **The unit of `∏_{i ≥ 0} H^*(X)(i)`**, `1 ∈ H^0(X)(0)`. -/
def oneConv (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  Pi.single (M := fun n : ℕ => tateTwist F 𝔇.tate (𝔇.H X) n) 0 (𝔇.unitTw X)

/-- **`exp(x) = ∑_n (1/n!) x^n`** in `∏_{n ≥ 0} H^*(X)(n)`, for `x ∈ H^*(X)(1)`. -/
def expTw (X : (SmoothProjectiveScheme k).FullSubcategory) (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  fun n => ((n.factorial : F)⁻¹) • 𝔇.twistPow X x n

/-- **Axiom (A1)**: `H^*` is compatible with finite coproducts. `H^*(∅) = 0`, and for a
coproduct `X ⨿ Y` of schemes with coprojections `i`, `j` the map
`(i^*, j^*) : H^*(X ⨿ Y) → H^*(X) × H^*(Y)` is bijective. -/
def CoproductAxiom : Prop :=
  (∀ X, IsEmpty ((toScheme k).obj X) → Subsingleton (𝔇.H X)) ∧
    ∀ (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) (i : X ⟶ Z) (j : Y ⟶ Z),
      Nonempty (IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map j))) →
        Function.Bijective fun a : 𝔇.H Z => (𝔇.pull i a, 𝔇.pull j a)

/-- **Axiom (A2)**: `c₁^H` is compatible with pullbacks, `f^*c₁^H(ℒ) = c₁^H(f^*ℒ)`. -/
def PullbackAxiom : Prop :=
  ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (L : ((toScheme k).obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj Y).presheaf
      ((toScheme k).obj Y).ringCatSheaf.2 L),
    𝔇.pullTw f 1 (𝔇.c₁ Y (picardClassOf _ L hL)) =
      𝔇.c₁ X (picardClassOf _ ((Scheme.Modules.pullback ((toScheme k).map f)).obj L)
        (isInvertible_pullback_obj _ L hL))

/-- `c₁^H(𝒪_P(1))` for the projective bundle `P = 𝐏(ℰ)`. -/
def bundleClass (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    tateTwist F 𝔇.tate (𝔇.H (bundle X E r)) 1 :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  𝔇.c₁ (bundle X E r) (picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
    (Stacks.Chow.isInvertible_bundleTwist E))

/-- The projective bundle formula's map `(a_i) ↦ ∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)` from
`⨁_{i ≤ r} H^*(X)(-i)` to `H^*(P) = H^*(P)(0)`. -/
def bundleFormula (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (a : ∀ i : Fin (r + 1), tateTwist F 𝔇.tate (𝔇.H X) (-(i : ℤ))) :
    tateTwist F 𝔇.tate (𝔇.H (bundle X E r)) 0 :=
  ∑ i : Fin (r + 1), tateCup 𝔇.finrank_tate (𝔇.cup _) (i : ℕ) (-(i : ℤ)) 0 (by ring)
    (𝔇.twistPow _ (𝔇.bundleClass X E r) i) (𝔇.pullTw (bundleProj X E r) _ (a i))

/-- **Axiom (A3)**, the projective bundle formula: for `ℰ` locally free of rank `r + 1 ≥ 1` on
`X` and `p : P = 𝐏(ℰ) → X`, the map
`⨁_{i = 0, …, r} H^*(X)(-i) → H^*(P)`, `(a_i) ↦ ∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)` is bijective. -/
def ProjectiveBundleAxiom : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
    (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    Function.Bijective (𝔇.bundleFormula X E r)

/-- **Axiom (A4)**: let `i : Y → X` be the inclusion of an effective Cartier divisor, with `X` and
`Y` smooth projective over `k`. For `a ∈ H^*(X)` with `i^*a = 0` we have
`a ∪ c₁^H(𝒪_X(Y)) = 0`.

"`i` is the inclusion of the divisor `D`" is an isomorphism `e` of the scheme of `Y` with the
closed subscheme `D`, under which `i` is the closed immersion of `D`. -/
def DivisorAxiom : Prop :=
  ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i : Y ⟶ X)
    (D : ((toScheme k).obj X).IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (e : (toScheme k).obj Y ≅ D.subscheme), e.hom ≫ D.subschemeι = (toScheme k).map i →
    ∀ a : 𝔇.H X, 𝔇.pull i a = 0 →
      tateCupLeft (L := 𝔇.tate) (𝔇.cup X) 1 a
          (𝔇.c₁ X (haveI := hD; picardClassOf _ (Stacks.Divisors.divisorSheaf D)
            (Stacks.Divisors.isInvertible_divisorSheaf D))) = 0

end FirstChernClassData

end Stacks.WeilCohomology

end
