module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionNormalize

/-!
# The Chow-theoretic maps attached to the diagram of Tag 0F97

In the situation of [Stacks, Tag 0F97], with the diagram

  `D₁ --i₁--> L <--i₂-- D₂`,  `p : L ⟶ Y`,  `pᵢ : Dᵢ ⟶ D`,  `i : D ⟶ Y`,

this file defines the four maps on Chow groups between which [Stacks, Tag 0F98] asserts an
identity. They are defined for an arbitrary diagram
`R : Stacks.Chow.TensorZeroScheme.Decomposition` read at `R.normalize`, whose first branch is the
zero scheme of `s₁`. Flat pullback along `p` and along `p₁` is
`Stacks.Chow.flatPullbackChowOfRelativeDimension`, and the Gysin maps of `i : D ⟶ Y` and
`i₁ : D₁ ⟶ L` are `Stacks.Chow.gysinChowOfInvertible` at the presentations `D = Z(s)` and
`D₁ = Z(s₁)`. Both composites `i₁^* ∘ p^*` and `p₁^* ∘ i^*` land in the Chow group of `D₁` over
the base along `i₁ ≫ p`, which agrees with `p₁ ≫ i` by
`Stacks.Chow.TensorZeroScheme.proj₁_comp_zeroIdeal_subschemeι_comp`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.gysinChowZeroIdeal` — `i^* : A_{k+1}(Y) ⟶ A_k(D)`.
* `Stacks.Chow.TensorZeroScheme.flatPullbackChowProj` — `p^* : A_{k}(Y) ⟶ A_{k+1}(L)`.
* `Stacks.Chow.TensorZeroScheme.gysinChowBranch₁` — `i₁^* : A_{k+1}(L) ⟶ A_k(D₁)`.
* `Stacks.Chow.TensorZeroScheme.flatPullbackChowProj₁` — `p₁^* : A_k(D) ⟶ A_{k+1}(D₁)`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-! ### The structure morphisms of the diagram over the base situation -/

include h₁ h₂ in
/-- **The two structure morphisms of `D₁` over the base situation agree**:
`p₁ ≫ (i ≫ sY) = i₁ ≫ (p ≫ sY)`. -/
theorem proj₁_comp_zeroIdeal_subschemeι_comp :
    R.normalize.p₁ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY =
      R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY := by
  rw [← Category.assoc, ← R.normalize.comm₁, Category.assoc]

/-! ### The four maps -/

include h₁ h₂ in
/-- **The Gysin map `i^* : A_{k+1}(Y) ⟶ A_k(D)` of the divisor `D = Z(s)` of Tag 0F97.**

`D` is the zero scheme of the global section `s` of the invertible module `L₁ ⊗ L₂` by definition
of `Stacks.Chow.TensorZeroScheme.zeroIdeal`, so this is
`Stacks.Chow.gysinChowOfInvertible` — Stacks 02TO with no hypothesis — at that presentation. -/
def gysinChowZeroIdeal (k : ℤ) :
    Stacks.Chow.chowGroup C sY (k + 1) →+
      Stacks.Chow.chowGroup C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k :=
  Stacks.Chow.gysinChowOfInvertible C sY k (Stacks.Divisors.tensorModules L₁ L₂) s

include h₁ h₂ in
/-- **The flat pullback `p^* : A_k(Y) ⟶ A_{k+1}(L)` along the morphism `p` of Tag 0F97.**

`p` is flat, locally of finite type and of relative dimension one — condition (2) of the tag,
`Stacks.Chow.TensorZeroScheme.flat_proj`, `locallyOfFiniteType_proj` and
`relativeDimension_proj` — so this is `Stacks.Chow.flatPullbackChowOfRelativeDimension`, Stacks
0FVK with Stacks 02S1 discharged. -/
def flatPullbackChowProj (k : ℤ) :
    Stacks.Chow.chowGroup C sY k →+
      Stacks.Chow.chowGroup C (R.normalize.p ≫ sY) (k + ((1 : ℕ) : ℤ)) :=
  Stacks.Chow.flatPullbackChowOfRelativeDimension C (R.normalize.p ≫ sY) sY R.normalize.p rfl
    1 R.normalize.p_relativeDimension k

include h₁ h₂ in
/-- **The Gysin map `i₁^* : A_{k+1}(L) ⟶ A_k(D₁)` of the first branch of Tag 0F97.**

`D₁` is the zero scheme of the global section `s₁` of the invertible module `p^*L₁` — condition
(3) of the tag, `Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme` — so this is
`Stacks.Chow.gysinChowOfInvertible` at that presentation. Its target is `D₁` over the base
situation along `i₁ ≫ (p ≫ sY)`. -/
def gysinChowBranch₁ (k : ℤ) :
    Stacks.Chow.chowGroup C (R.normalize.p ≫ sY) (k + 1) →+
      Stacks.Chow.chowGroup C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) k :=
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible
      R.normalize.total.sheaf.obj
      R.normalize.total.ringCatSheaf.property
      ((Scheme.Modules.pullback R.normalize.p).obj L₁) :=
    Stacks.Divisors.pullback_isInvertible _ _
  Stacks.Chow.gysinChowOfInvertible C (R.normalize.p ≫ sY) k
    ((Scheme.Modules.pullback R.normalize.p).obj L₁) R.normalize.s₁

include h₁ h₂ in
/-- **The flat pullback `p₁^* : A_k(D) ⟶ A_{k+1}(D₁)` along the first projection of Tag 0F97.**

`p₁` is flat, locally of finite type and of relative dimension one by
`Stacks.Chow.TensorZeroScheme.flat_proj₁`, `locallyOfFiniteType_proj₁` and
`relativeDimension_proj₁`. Its target is `D₁` over the base situation along `i₁ ≫ (p ≫ sY)`,
which is where the Gysin map of `i₁` lands as well; the identification of that composite with
`p₁ ≫ (i ≫ sY)` is `Stacks.Chow.TensorZeroScheme.proj₁_comp_zeroIdeal_subschemeι_comp`. -/
def flatPullbackChowProj₁ (k : ℤ) :
    Stacks.Chow.chowGroup C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k →+
      Stacks.Chow.chowGroup C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        (k + ((1 : ℕ) : ℤ)) :=
  Stacks.Chow.flatPullbackChowOfRelativeDimension C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
    (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
    ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k

end Stacks.Chow.TensorZeroScheme

end
