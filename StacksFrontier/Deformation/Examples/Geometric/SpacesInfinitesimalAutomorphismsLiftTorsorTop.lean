module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMoveAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovePrecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftTrivialTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceUndeformedTarget

/-!
# Lifts into an algebraic space across a first order thickening form a torsor

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `q : W ⟶ T`
be a morphism of algebraic spaces and let `a : Z ⟶ W` be a morphism which extends to a morphism
`c : X ⟶ W`.  The *lifts* of `a` over `T` are the morphisms `b : X ⟶ W` with `b|_Z = a` and
`b ≫ q = c ≫ q`.  Read with the trivial thickening `W ⊂ W` as target, the action `θ · b` of
[Stacks Project, Tag 0CK6] of the `𝒪_Z`-linear maps `θ : a^*Ω_{W/T} ⟶ 𝒞_{Z/X}` on the lifts is
simply transitive ([Stacks Project, Tag 061D]); this file records that globally, as a
bijection between the maps `θ` and the lifts.  The conormal-module condition of
[Stacks Project, Tag 0618] is vacuous here, the conormal module of `W ⊂ W` being zero.

The morphism `a` is presented through the top closed subspace `W ⊂ W`, as everywhere in the
library's deformation theory of maps; `e₀ : Z ⟶ ⊤` is its factorization.

## Main definitions

* `AlgebraicGeometry.Space.TopLifts`: the lifts.
* `AlgebraicGeometry.Space.topLiftsEquiv`: the bijection `θ ↦ θ · c` with the lifts.

## Main results

* `AlgebraicGeometry.Space.topLiftsEquiv_add`: the bijection turns addition of maps into the
  iterated action.
* `AlgebraicGeometry.Space.comp_derivationMove_top`: precomposition with a self-map of `X` which
  restricts to the identity of `Z` and has the conormal map of the identity commutes with the
  action.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The top closed subspace of an algebraic space. -/
abbrev topSubspace (W : AlgebraicSpaces B S hS) : ClosedSubspaces B S hS W.1 :=
  ⟨⊤, isClosedSubspace_top B S hS W⟩

/-- The top closed subspace is a first order thickening. -/
theorem isFirstOrderThickening_topSubspace (W : AlgebraicSpaces B S hS) :
    IsFirstOrderThickening B S hS W (topSubspace B S hS W).1 :=
  isFirstOrderThickening_of_eq_top B S hS (isThickening_top B S hS W) rfl

variable {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1) (q : W ⟶ T)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨(topSubspace B S hS W).1.toFunctor, (topSubspace B S hS W).2.1⟩ : AlgebraicSpaces B S hS))
  (c : X ⟶ W)
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W))

/-- **The lifts of `a` over `T`**: the morphisms `b : X ⟶ W` restricting to `a` on `Z` (through
`e₀`) and agreeing with `c` over `T`. -/
def TopLifts : Type _ :=
  {b : X ⟶ W // subspaceInclusion B S hS X Z ≫ b =
      e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W) ∧ b ≫ q = c ≫ q}

/-- Two lifts are equal as soon as their underlying morphisms are. -/
theorem TopLifts.ext {b b' : TopLifts B S hS Z q e₀ c} (h : b.1 = b'.1) : b = b' :=
  Subtype.ext h

/-- The action `θ · c`, as a lift. -/
def topLiftsMove
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z) :
    TopLifts B S hS Z q e₀ c :=
  ⟨derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c hc θ (c ≫ q) rfl, by
    obtain ⟨hb, hbq, -, -⟩ := derivationMove_spec B S hS Z (topSubspace B S hS W) e₀ q hZ
      (isFirstOrderThickening_topSubspace B S hS W) c hc θ (c ≫ q) rfl
    exact ⟨hb, hbq⟩⟩

/-- **The lifts are a torsor under the `𝒪_Z`-linear maps `a^*Ω_{W/T} ⟶ 𝒞_{Z/X}`**
([Stacks Project, Tag 061D], globally): `θ ↦ θ · c` is a bijection.  Injectivity is the
freeness of the action; surjectivity is [Stacks Project, Tag 0618], whose conormal condition is
vacuous because `𝒞_{W/W} = 0`. -/
def topLiftsEquiv :
    ((modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z) ≃ TopLifts B S hS Z q e₀ c :=
  Equiv.ofBijective (topLiftsMove B S hS Z hZ q e₀ c hc) ⟨fun θ θ' h =>
    derivationMove_injective B S hS Z (topSubspace B S hS W) e₀ q hZ
      (isFirstOrderThickening_topSubspace B S hS W) c hc (c ≫ q) rfl θ θ'
      (congrArg Subtype.val h),
    fun b => by
      obtain ⟨θ, hθ⟩ := exists_derivationMove_eq B S hS Z (topSubspace B S hS W) e₀ q hZ
        (isFirstOrderThickening_topSubspace B S hS W) c hc (c ≫ q) rfl b.1 b.2.1 b.2.2
        ((eq_zero_of_isZero_conormalModule_top B S hS Z e₀ _).trans
          (eq_zero_of_isZero_conormalModule_top B S hS Z e₀ _).symm)
      exact ⟨θ, TopLifts.ext B S hS Z q e₀ c hθ⟩⟩

/-- The underlying morphism of the lift `topLiftsEquiv θ` is the action `θ · c`. -/
theorem topLiftsEquiv_apply_val
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z) :
    (topLiftsEquiv B S hS Z hZ q e₀ c hc θ).1 =
      derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c hc θ (c ≫ q) rfl :=
  rfl

/-- The base point of the torsor is the image of `0`. -/
theorem topLiftsEquiv_zero :
    (topLiftsEquiv B S hS Z hZ q e₀ c hc 0).1 = c :=
  derivationMove_zero B S hS Z (topSubspace B S hS W) e₀ q hZ
    (isFirstOrderThickening_topSubspace B S hS W) c hc (c ≫ q) rfl

/-- The action `θ · c` depends on `θ`, `c` and the base morphism `p` only through their values. -/
theorem derivationMove_congr_of_eq
    {θ θ' : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z} (hθ : θ = θ')
    {c c' : X ⟶ W} (hcc : c = c')
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W))
    (hc' : subspaceInclusion B S hS X Z ≫ c' =
      e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W))
    {p p' : X ⟶ T} (hp : p = p') (hcq : c ≫ q = p) (hcq' : c' ≫ q = p') :
    derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c hc θ p hcq =
      derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c' hc' θ' p' hcq' := by
  subst hθ hcc hp
  rfl

/-- **Precomposition with a self-map of `X` fixing `Z` commutes with the action**, as soon as the
self-map has the conormal map of the identity: `a ≫ (θ · c) = θ · (a ≫ c)`.  This is
[Stacks Project, Tag 0CK6] under precomposition
(`AlgebraicGeometry.Space.comp_derivationMove`), at `a` and at the identity: the two pulled-back
maps agree because the conormal maps do, and at the identity the pulled-back map is `θ` itself
by freeness of the action. -/
theorem comp_derivationMove_top (a : X ⟶ X)
    (ha : subspaceInclusion B S hS X Z ≫ a = 𝟙 _ ≫ subspaceInclusion B S hS X Z)
    (hid : subspaceInclusion B S hS X Z ≫ 𝟙 X = 𝟙 _ ≫ subspaceInclusion B S hS X Z)
    (hcm : conormalMap B S hS Z Z a (𝟙 _) ha = conormalMap B S hS Z Z (𝟙 X) (𝟙 _) hid)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hac : subspaceInclusion B S hS X Z ≫ a ≫ c =
      e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W)) :
    a ≫ derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c hc θ (c ≫ q) rfl =
      derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ (a ≫ c) hac θ ((a ≫ c) ≫ q) rfl := by
  have hW := isFirstOrderThickening_topSubspace B S hS W
  have h1 := comp_derivationMove B S hS Z Z (topSubspace B S hS W) a (𝟙 _) e₀ ha q hZ hZ hW
    c hc θ (c ≫ q) rfl
  have h4 := comp_derivationMove B S hS Z Z (topSubspace B S hS W) (𝟙 X) (𝟙 _) e₀ hid q hZ hZ
    hW (a ≫ c) hac θ ((a ≫ c) ≫ q) rfl
  refine h1.trans (Eq.trans ?_ (h4.symm.trans (Category.id_comp _)))
  apply derivationMove_congr_of_eq
  · rw [hcm]
  · exact (Category.id_comp (a ≫ c)).symm
  · rw [Category.id_comp, Category.assoc]

end AlgebraicGeometry.Space

end
