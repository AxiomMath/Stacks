module

public import StacksFrontier.AlgebraicGeometry.Chow.SelfIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.RationalPointExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose

/-!
# Composition of correspondences, and their action on Chow groups

Let `k` be a field and let `X`, `Y`, `Z` be schemes locally of finite type over `k`, of
dimensions `d`, `e` and `f` (each of constant relative dimension over `k`, as an equidimensional
part `X_d` of a smooth projective scheme is). Section 0FFZ of the Stacks Project defines, for
`c ∈ Corrʳ(X, Y) = CH^{d+r}(X × Y) ⊗ ℚ = CH_{e-r}(X × Y) ⊗ ℚ` and `c' ∈ Corrˢ(Y, Z)`:

* the **pullback** `c^*(β) = pr₁,*(c · pr₂^* β) ∈ CH_{m-r}(X) ⊗ ℚ` of `β ∈ CH_m(Y) ⊗ ℚ`;
* the **pushforward** `c_*(α) = pr₂,*(c · pr₁^* α) ∈ CH^{i+r}(Y) ⊗ ℚ` of `α ∈ CH^i(X) ⊗ ℚ`;
* the **composition** `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c') ∈ Corr^{r+s}(X, Z)`.

This file constructs the three of them, from flat pullback along the projections (Stacks 02S1,
unconditional here: `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`), the
intersection product of Stacks 0FC0 on `X × Y` and on `X × Y × Z`
(`Stacks.Chow.selfIntersectionProduct`), and proper pushforward along the projections forgetting
a proper factor (Stacks 02S2, unconditional here: `Stacks.Chow.properPushforwardDescends`).

## Main definitions

* `Stacks.WeilCohomology.pr₁₂`, `Stacks.WeilCohomology.pr₂₃`, `Stacks.WeilCohomology.pr₁₃`: the
  three projections of `X × Y × Z = (X ×_S Y) ×_S Z`, with the cartesian squares exhibiting each
  as a base change (`isPullback_snd_pr₁₂`, `isPullback_pr₁₂_pr₂₃`, `isPullback_pr₁₂_pr₁₃`), hence
  `pr₁₂` and `pr₂₃` flat of relative dimension `f` and `d`, and `pr₁₃` proper when `Y` is.
* `Stacks.WeilCohomology.compositionInt`: composition on integral Chow groups, `ℤ`-bilinear.
* `Stacks.WeilCohomology.composition`: composition of rational correspondences, `ℚ`-bilinear.
* `Stacks.WeilCohomology.correspondencePullback` and
  `Stacks.WeilCohomology.correspondencePushforward`: the two actions, `ℚ`-bilinear.

## Implementation notes

**The Gysin classes of diagonals are an argument.** The intersection product of Stacks 0FC0 on a
scheme `W` smooth over `k` is `Δ^!(α × β)` for the Gysin class `Δ^!` of the diagonal of `W`
(Stacks 0FBR). The constructions below take a whole family of such classes,
`Stacks.WeilCohomology.DiagonalClassFamily`, one for every scheme of constant dimension over `k`,
so that they are available for the canonical family once it is constructed (the virtual normal
Gysin class of Stacks 0FBK at the diagonal, `c(Δ, 𝒞_Δ^∨)`). Nothing about the family is assumed,
and no property of composition is proved here: bilinearity holds by construction, but
associativity (Stacks 0FG0 (1)), the compatibilities of Stacks 0FG0 (2), (3) and (4), and the unit
laws of Stacks 0FG2 are statements about the *canonical* class and depend on Stacks 0FC1, 0FFB
and 0FFC. Accordingly no declaration in this file carries a `@[stacks]` attribute.

**Dimensions are parameters.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose`, a correspondence of
degree `r` to `Y` of dimension `e` is an element of `Stacks.WeilCohomology.Correspondence`, that
is of `CH_{e-r}(X × Y) ⊗ ℚ`. The relative dimensions of `X → Spec k` and `Z → Spec k` enter as
the relative dimensions of the flat projections `pr₂₃` and `pr₁₂`. A general smooth projective
scheme is the disjoint union of its equidimensional parts, and the source's correspondences
decompose accordingly.

**The Gysin system.** Bivariant classes are stated against a `Stacks.Chow.GysinSystem`; here it
is `Stacks.Chow.gysinSystemOfInvertible`, the genuine first Chern class rule of Stacks 02SO with
the unconditional vanishing of Stacks 02TO.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u


namespace Stacks.WeilCohomology

section Products

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)

/-- The structure morphism `X ×_S Y ⟶ S`. -/
abbrev prodBase : (pullback sX sY : Scheme.{u}) ⟶ S := pullback.fst sX sY ≫ sX

/-- The triple product `(X ×_S Y) ×_S Z`. -/
abbrev tripleProduct : Scheme.{u} := pullback (prodBase sX sY) sZ

/-- The structure morphism of the triple product. -/
abbrev tripleBase : tripleProduct sX sY sZ ⟶ S :=
  pullback.fst (prodBase sX sY) sZ ≫ prodBase sX sY

/-- The projection `pr₁₂ : X × Y × Z ⟶ X × Y`. -/
abbrev pr₁₂ : tripleProduct sX sY sZ ⟶ pullback sX sY := pullback.fst (prodBase sX sY) sZ

/-- The two morphisms `X × Y × Z ⟶ S` through `Y` and through `Z` agree. -/
theorem pr₁₂_snd_comp : pr₁₂ sX sY sZ ≫ pullback.snd sX sY ≫ sY =
    pullback.snd (prodBase sX sY) sZ ≫ sZ := by
  rw [← pullback.condition, ← pullback.condition]

/-- The projection `pr₂₃ : X × Y × Z ⟶ Y × Z`. -/
def pr₂₃ : tripleProduct sX sY sZ ⟶ pullback sY sZ :=
  pullback.lift (pr₁₂ sX sY sZ ≫ pullback.snd sX sY) (pullback.snd (prodBase sX sY) sZ)
    (by rw [Category.assoc, pr₁₂_snd_comp])

/-- The projection `pr₁₃ : X × Y × Z ⟶ X × Z`. -/
def pr₁₃ : tripleProduct sX sY sZ ⟶ pullback sX sZ :=
  pullback.lift (pr₁₂ sX sY sZ ≫ pullback.fst sX sY) (pullback.snd (prodBase sX sY) sZ)
    (by rw [Category.assoc, pullback.condition])

/-- The `Y`-component of `pr₂₃` is the `Y`-component of `pr₁₂`. -/
@[reassoc (attr := simp)]
theorem pr₂₃_fst : pr₂₃ sX sY sZ ≫ pullback.fst sY sZ = pr₁₂ sX sY sZ ≫ pullback.snd sX sY :=
  pullback.lift_fst _ _ _

/-- The `Z`-component of `pr₂₃` is the projection `X × Y × Z ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem pr₂₃_snd : pr₂₃ sX sY sZ ≫ pullback.snd sY sZ = pullback.snd (prodBase sX sY) sZ :=
  pullback.lift_snd _ _ _

/-- The `X`-component of `pr₁₃` is the `X`-component of `pr₁₂`. -/
@[reassoc (attr := simp)]
theorem pr₁₃_fst : pr₁₃ sX sY sZ ≫ pullback.fst sX sZ = pr₁₂ sX sY sZ ≫ pullback.fst sX sY :=
  pullback.lift_fst _ _ _

/-- The `Z`-component of `pr₁₃` is the projection `X × Y × Z ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem pr₁₃_snd : pr₁₃ sX sY sZ ≫ pullback.snd sX sZ = pullback.snd (prodBase sX sY) sZ :=
  pullback.lift_snd _ _ _

/-- `pr₁₂` is a morphism over `S`. -/
theorem pr₁₂_comp_prodBase : pr₁₂ sX sY sZ ≫ prodBase sX sY = tripleBase sX sY sZ := rfl

/-- `pr₂₃` is a morphism over `S`. -/
theorem pr₂₃_comp_prodBase : pr₂₃ sX sY sZ ≫ prodBase sY sZ = tripleBase sX sY sZ := by
  simp only [prodBase, tripleBase, pr₂₃_fst_assoc, ← pullback.condition]

/-- `pr₁₃` is a morphism over `S`. -/
theorem pr₁₃_comp_prodBase : pr₁₃ sX sY sZ ≫ prodBase sX sZ = tripleBase sX sY sZ := by
  simp only [prodBase, tripleBase, pr₁₃_fst_assoc]

/-- `pr₁₂` is the base change of `Z ⟶ S` along `X × Y ⟶ S`. -/
theorem isPullback_snd_pr₁₂ :
    IsPullback (pullback.snd (prodBase sX sY) sZ) (pr₁₂ sX sY sZ) sZ (prodBase sX sY) :=
  (IsPullback.of_hasPullback (prodBase sX sY) sZ).flip

/-- `pr₂₃` is the base change of `pr₂ : X × Y ⟶ Y` along `pr₁ : Y × Z ⟶ Y`. -/
theorem isPullback_pr₁₂_pr₂₃ :
    IsPullback (pr₁₂ sX sY sZ) (pr₂₃ sX sY sZ) (pullback.snd sX sY) (pullback.fst sY sZ) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd sY sZ) (v₁₃ := sZ)
    (h₂₂ := sY) ?_ (pr₂₃_fst sX sY sZ) (IsPullback.of_hasPullback sY sZ).flip).flip
  rw [pr₂₃_snd, ← pullback.condition]
  exact isPullback_snd_pr₁₂ sX sY sZ

/-- `pr₁₃` is the base change of `pr₁ : X × Y ⟶ X` along `pr₁ : X × Z ⟶ X`. -/
theorem isPullback_pr₁₂_pr₁₃ :
    IsPullback (pr₁₂ sX sY sZ) (pr₁₃ sX sY sZ) (pullback.fst sX sY) (pullback.fst sX sZ) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd sX sZ) (v₁₃ := sZ)
    (h₂₂ := sX) ?_ (pr₁₃_fst sX sY sZ) (IsPullback.of_hasPullback sX sZ).flip).flip
  rw [pr₁₃_snd]
  exact isPullback_snd_pr₁₂ sX sY sZ

end Products

end Stacks.WeilCohomology

namespace Stacks.Chow

/-- The rational extension of a `ℤ`-bilinear map: `ℚ ⊗ M × ℚ ⊗ N ⟶ ℚ ⊗ P`,
`(q ⊗ a, q' ⊗ b) ↦ q q' ⊗ B a b`. -/
def rationalBilin {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] P) :
    TensorProduct ℤ ℚ M →ₗ[ℚ] TensorProduct ℤ ℚ N →ₗ[ℚ] TensorProduct ℤ ℚ P :=
  TensorProduct.curry ((TensorProduct.lift B).baseChange ℚ ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ M N).symm.toLinearMap)

/-- `rationalBilin B (q ⊗ a) (q' ⊗ b) = q q' ⊗ B a b`. -/
theorem rationalBilin_tmul {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] P) (q q' : ℚ) (a : M) (b : N) :
    rationalBilin B (q ⊗ₜ[ℤ] a) (q' ⊗ₜ[ℤ] b) = (q * q') ⊗ₜ[ℤ] B a b := by
  simp [rationalBilin]

end Stacks.Chow

namespace Stacks.WeilCohomology

section Calculus

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]

/-- `pr₂₃` is locally of finite type, as a base change of `X × Y ⟶ Y`. -/
instance : LocallyOfFiniteType (pr₂₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₂₃ sX sY sZ) inferInstance

/-- `pr₂₃` is flat, as a base change of `X × Y ⟶ Y`. -/
instance : Flat (pr₂₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₂₃ sX sY sZ) inferInstance

/-- `pr₁₃` is proper when `Y` is proper, as a base change of `X × Y ⟶ X`. -/
instance [IsProper sY] : IsProper (pr₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₁₃ sX sY sZ) inferInstance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- `pr₁₂ : X × Y × Z ⟶ X × Y` has relative dimension `f` when `Z` has dimension `f`. -/
theorem relativeDimension_pr₁₂ {f : ℕ} (hZ : RelativeDimension sZ f) :
    RelativeDimension (pr₁₂ sX sY sZ) f :=
  RelativeDimension.of_isPullback (isPullback_snd_pr₁₂ sX sY sZ) hZ

omit [LocallyOfFiniteType sY] in
/-- `pr₂ : X × Y ⟶ Y` has relative dimension `d` when `X` has dimension `d`. -/
theorem relativeDimension_snd {d : ℕ} (hX : RelativeDimension sX d) :
    RelativeDimension (pullback.snd sX sY) d :=
  RelativeDimension.of_isPullback (IsPullback.of_hasPullback sX sY) hX

omit [LocallyOfFiniteType sX] in
/-- `pr₁ : X × Y ⟶ X` has relative dimension `e` when `Y` has dimension `e`. -/
theorem relativeDimension_fst {e : ℕ} (hY : RelativeDimension sY e) :
    RelativeDimension (pullback.fst sX sY) e :=
  RelativeDimension.of_isPullback (IsPullback.of_hasPullback sX sY).flip hY

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ] in
/-- `pr₂₃ : X × Y × Z ⟶ Y × Z` has relative dimension `d` when `X` has dimension `d`. -/
theorem relativeDimension_pr₂₃ {d : ℕ} (hX : RelativeDimension sX d) :
    RelativeDimension (pr₂₃ sX sY sZ) d :=
  RelativeDimension.of_isPullback (isPullback_pr₁₂_pr₂₃ sX sY sZ) (relativeDimension_snd k sX sY hX)

/-- The Gysin system of the field situation: the genuine first Chern class rule of Stacks 02SO
with the unconditional vanishing of Stacks 02TO. -/
abbrev fieldGysinSystem : GysinSystem (fieldChowSituation k) :=
  gysinSystemOfInvertible (fieldChowSituation k)

/-- A choice, for every scheme `W` smooth over `k` and of constant dimension `n`, of a Gysin
class `Δ^! ∈ A^n(W ⟶ W ×_k W)` of its diagonal, as in Stacks 0FBR; the intersection product of
Stacks 0FC0 on `W` is formed with it. -/
abbrev DiagonalClassFamily : Type (u + 1) :=
  ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (n : ℕ),
    RelativeDimension sW n →
      BivariantClass (fieldChowSituation k) (fieldGysinSystem k) sW
        (selfProductStructure (fieldChowSituation k) sW) (pullback.diagonal sW)
        (diagonal_comp_selfProductStructure (fieldChowSituation k) sW) (n : ℤ)

/-- `X × Y` has dimension `e + d` when `X` and `Y` have dimensions `d` and `e`. -/
theorem relativeDimension_prodBase {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) : RelativeDimension (prodBase sX sY) (e + d) := by
  have : Flat (pullback.fst sX sY) := inferInstance
  exact RelativeDimension.comp_of_flat _ _ (relativeDimension_fst k sX sY hY) hX

/-- `X × Y × Z` has dimension `f + (e + d)`. -/
theorem relativeDimension_tripleBase {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) :
    RelativeDimension (tripleBase sX sY sZ) (f + (e + d)) := by
  have : Flat (pr₁₂ sX sY sZ) := inferInstance
  exact RelativeDimension.comp_of_flat _ _ (relativeDimension_pr₁₂ k sX sY sZ hZ)
    (relativeDimension_prodBase k sX sY hX hY)

variable [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ]
    [IsSeparated sZ] (Δ : DiagonalClassFamily k)

/-- The class `pr₁₂^* c · pr₂₃^* c'` on `X × Y × Z`, before the pushforward to `X × Z`, as a
`ℤ`-bilinear map, the product being formed with the diagonal class `Δ` of `X × Y × Z`. -/
def compositionCycle {d e f : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (hZ : RelativeDimension sZ f) (r s : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r) →ₗ[ℤ]
      chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s) →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (tripleBase sX sY sZ) ((f : ℤ) - (r + s)) :=
  ((selfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (tripleBase sX sY sZ) _
      (Δ _ _ (relativeDimension_tripleBase k sX sY sZ hX hY hZ)) (((e : ℤ) - r) + f)
      (((f : ℤ) - s) + d)).compl₁₂
    (flatPullbackChow (fieldChowSituation k) (tripleBase sX sY sZ) (prodBase sX sY)
      (pr₁₂ sX sY sZ) (pr₁₂_comp_prodBase sX sY sZ) f (relativeDimension_pr₁₂ k sX sY sZ hZ) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap
    (flatPullbackChow (fieldChowSituation k) (tripleBase sX sY sZ) (prodBase sY sZ)
      (pr₂₃ sX sY sZ) (pr₂₃_comp_prodBase sX sY sZ) d (relativeDimension_pr₂₃ k sX sY sZ hX) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap
    ).compr₂
    (chowGroupDegreeEquiv (fieldChowSituation k) (tripleBase sX sY sZ)
      (by push_cast; ring)).toIntLinearEquiv.toLinearMap

/-- **Composition of correspondences**, `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, on integral
Chow groups, as a `ℤ`-bilinear map in `c` and `c'`. -/
def compositionInt [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r) →ₗ[ℤ]
      chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s) →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (prodBase sX sZ) ((f : ℤ) - (r + s)) :=
  (compositionCycle k sX sY sZ Δ hX hY hZ r s).compr₂
    (properChowPushforward (fieldChowSituation k) (tripleBase sX sY sZ) (prodBase sX sZ)
      (pr₁₃ sX sY sZ) (pr₁₃_comp_prodBase sX sY sZ) _
      (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap

/-- The class `c · pr₂^* β` on `X × Y` for `c ∈ A_{e-r}(X × Y)` and `β ∈ CH_m(Y)`. -/
def pullbackCycle {d e : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (r m : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r) →ₗ[ℤ]
      chowGroup (fieldChowSituation k) sY m →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (prodBase sX sY) (m - r) :=
  ((selfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (prodBase sX sY) _ (Δ _ _ (relativeDimension_prodBase k sX sY hX hY))
      ((e : ℤ) - r) (m + d)).compr₂
    (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
      (by push_cast; ring)).toIntLinearEquiv.toLinearMap).compl₂
    (flatPullbackChow (fieldChowSituation k) (prodBase sX sY) sY (pullback.snd sX sY)
      pullback.condition.symm d (relativeDimension_snd k sX sY hX) m
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap

/-- The class `c · pr₁^* α` on `X × Y` for `c ∈ A_{e-r}(X × Y)` and `α ∈ A_{d-i}(X) = CH^i(X)`. -/
def pushforwardCycle {d e : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (r i : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r) →ₗ[ℤ]
      chowGroup (fieldChowSituation k) sX ((d : ℤ) - i) →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - (i + r)) :=
  ((selfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (prodBase sX sY) _ (Δ _ _ (relativeDimension_prodBase k sX sY hX hY))
      ((e : ℤ) - r) (((d : ℤ) - i) + e)).compr₂
    (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
      (by push_cast; ring)).toIntLinearEquiv.toLinearMap).compl₂
    (flatPullbackChow (fieldChowSituation k) (prodBase sX sY) sX (pullback.fst sX sY) rfl e
      (relativeDimension_fst k sX sY hY) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap

/-- **Composition of correspondences** `Corrʳ(X, Y) × Corrˢ(Y, Z) ⟶ Corr^{r+s}(X, Z)`,
`(c, c') ↦ c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, as a `ℚ`-bilinear map, for `X`, `Y`, `Z` of
dimensions `d`, `e`, `f`. -/
def composition [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ) :
    Correspondence (fieldChowSituation k) sX sY e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) sY sZ f s →ₗ[ℚ]
        Correspondence (fieldChowSituation k) sX sZ f (r + s) :=
  rationalBilin (compositionInt k sX sY sZ Δ hX hY hZ r s)

/-- **Pullback by a correspondence**, `c^*(β) = pr₁,*(c · pr₂^* β) ∈ CH_{m-r}(X) ⊗ ℚ` for
`c ∈ Corrʳ(X, Y)` and `β ∈ CH_m(Y) ⊗ ℚ`, as a `ℚ`-bilinear map. -/
def correspondencePullback [IsProper sY] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (r m : ℤ) :
    Correspondence (fieldChowSituation k) sX sY e r →ₗ[ℚ]
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m) →ₗ[ℚ]
        TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (m - r)) :=
  rationalBilin ((pullbackCycle k sX sY Δ hX hY r m).compr₂
    (properChowPushforward (fieldChowSituation k) (prodBase sX sY) sX (pullback.fst sX sY) rfl _
      (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap)

/-- **Pushforward by a correspondence**, `c_*(α) = pr₂,*(c · pr₁^* α) ∈ CH^{i+r}(Y) ⊗ ℚ` for
`c ∈ Corrʳ(X, Y)` and `α ∈ CH^i(X) ⊗ ℚ`, as a `ℚ`-bilinear map; codimension in `X` and `Y` is
dimension `d - i` and `e - (i + r)`. -/
def correspondencePushforward [IsProper sX] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (r i : ℤ) :
    Correspondence (fieldChowSituation k) sX sY e r →ₗ[ℚ]
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX ((d : ℤ) - i)) →ₗ[ℚ]
        TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY ((e : ℤ) - (i + r))) :=
  rationalBilin ((pushforwardCycle k sX sY Δ hX hY r i).compr₂
    (properChowPushforward (fieldChowSituation k) (prodBase sX sY) sY (pullback.snd sX sY)
      pullback.condition.symm _ (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap)

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- On pure tensors, `composition` is `compositionInt` with the rational coefficients
multiplied. -/
@[simp]
theorem composition_tmul [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ) (q q' : ℚ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s)) :
    composition k sX sY sZ Δ hX hY hZ r s (q ⊗ₜ[ℤ] c) (q' ⊗ₜ[ℤ] c') =
      (q * q') ⊗ₜ[ℤ] compositionInt k sX sY sZ Δ hX hY hZ r s c c' :=
  rationalBilin_tmul _ _ _ _ _

/-- Transport of correspondences along an equality of degrees,
`Corrʳ(X, Y) ≃ Corr^{r'}(X, Y)` for `r = r'`. -/
def correspondenceCongr {e r r' : ℤ} (h : r = r') :
    Correspondence (fieldChowSituation k) sX sY e r ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) sX sY e r' :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
      (by rw [h])).toIntLinearEquiv

omit [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] in
/-- On pure tensors, `correspondenceCongr` transports the Chow class along the equality of
degrees. -/
@[simp]
theorem correspondenceCongr_tmul {e r r' : ℤ} (h : r = r') (q : ℚ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) (e - r)) :
    correspondenceCongr k sX sY h (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY) (by rw [h]) c :=
  rfl

end Calculus

/-! ### The laws of Stacks 0FG0 as properties of a family of diagonal classes -/

/-- **Associativity of composition of correspondences** (the second half of Stacks 0FG0 (1)) for
the products formed with the family `Δ`: `c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c` for correspondences
between schemes of constant dimension, the two sides compared through the identification of
the degrees `(r + s) + t = r + (s + t)`.

For the canonical family this is the content of Stacks 0FG0 (1); it is a property of `Δ`, which
Stacks derives from 0FC1, 0FFB, 0FFC and 02RG. -/
def DiagonalClassFamily.CompositionAssoc {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) (sZ : Z ⟶ (fieldChowSituation k).S)
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sW] [Smooth sX] [IsSeparated sX] [Smooth sY]
    [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]
    [Smooth sW] [IsSeparated sW] [IsProper sY] [IsProper sZ] {d e f g : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (hW : RelativeDimension sW g) (r s t : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY e r)
    (c' : Correspondence (fieldChowSituation k) sY sZ f s)
    (c'' : Correspondence (fieldChowSituation k) sZ sW g t),
    correspondenceCongr k sX sW (add_assoc r s t)
        (composition k sX sZ sW Δ hX hZ hW (r + s) t
          (composition k sX sY sZ Δ hX hY hZ r s c c') c'') =
      composition k sX sY sW Δ hX hY hW r (s + t) c
        (composition k sY sZ sW Δ hY hZ hW s t c' c'')

end Stacks.WeilCohomology
