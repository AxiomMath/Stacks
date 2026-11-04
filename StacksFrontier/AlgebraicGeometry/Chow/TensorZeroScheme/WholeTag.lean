module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchBundle
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension

/-!
# The decomposition of the zero scheme of a section of a tensor product of two line bundles

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. [Stacks, Tag 0F97] asserts the
existence of a commutative diagram

  `D₁ --i₁--> L <--i₂-- D₂`
  `|          |          |`
  `p₁         p         p₂`
  `v          v          v`
  `D --i-->   Y   <--i-- D`

together with sections `sᵢ` of `p^*Lᵢ` satisfying seven conditions, and asserts that the whole
diagram and the two sections are compatible with arbitrary base change.

This file carries the **statement** of the whole tag: `Decomposition` is the diagram, the two
sections and the seven conditions, and `Decomposition.IsStableUnderBaseChange` is the
base-change clause, as a property of a diagram. The diagram is assembled from the construction
in `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Existence`, and the base-change clause is
proved — for an arbitrary diagram, not only for that one — in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionTransport`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.squarePullbackMap`: the canonical identification, along a
  commutative square, of the two ways of pulling a module on the lower-right corner back to the
  upper-left corner. This is what the base-change clause reads the two sections through.
* `Stacks.Chow.TensorZeroScheme.Decomposition`: **the diagram, the two sections and the seven
  conditions of [Stacks, Tag 0F97].**

## Implementation notes

Closed subschemes are `AlgebraicGeometry.Scheme.IdealSheafData`. Scheme-theoretic union is the
meet `D₁ ⊓ D₂` and scheme-theoretic intersection the join `D₁ ⊔ D₂` of ideal sheaves, since the
order on `Scheme.IdealSheafData` is the order on ideals, which is opposite to inclusion of
subschemes. The inverse image `p^{-1}D` is `Scheme.IdealSheafData.comap`, and
`Scheme.IdealSheafData.inclusion` supplies the canonical closed immersions `D₁ ∩ D₂ ⟶ Dᵢ`.

Finite type is expressed as locally of finite type together with quasi-compactness, and relative
dimension one by `AlgebraicGeometry.RelativeDimension`, which is this repository's reading of
[Stacks, Tag 02NJ].

The line bundle of condition (4) is `Stacks.Chow.TensorZeroScheme.branchSituation`; the source
writes its module as `L_{1-i}^{⊗ -1}|_D`, and as its own proof and the proof of [Stacks, Tag
0F98] make explicit the index is the *other* one, so `D₁` uses `L₂` and `D₂` uses `L₁`. The zero
section of condition (7) is `Stacks.LineBundle.Situation.zeroSection` of that same situation; no
second zero-section morphism is introduced, so condition (7) is not weakened to an arbitrary
section.

The maps `pᵢ : Dᵢ ⟶ D` are determined by the commuting squares, because `i` is a closed immersion
and hence a monomorphism; so the base-change clause constrains only the total space, the two
ideal sheaves and the two sections. For the same reason the map `D₁ ∩ D₂ ⟶ D` through `p₂` agrees
with the one through `p₁`, and condition (6) is stated once.

The tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`, ascribed through
`Stacks.Divisors.tensorModules`, and the product of two sections is
`Stacks.Divisors.tensorSection`; this is the spelling the canonical pullback comparison of
[Stacks, Tag 01CD] is available at, so condition (1) and the base-changed section `g^*s` are
stated with that canonical comparison and not with an arbitrary chosen isomorphism.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

/-- The canonical identification, along a commutative square `h ≫ f = f' ≫ g`, of the two ways of
pulling a module on the lower-right corner back to the upper-left corner. -/
def squarePullbackMap {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} (w : h ≫ f = f' ≫ g) (M : Y.Modules) :
    (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp h f).hom.app M ≫
    (Scheme.Modules.pullbackCongr w).hom.app M ≫
      (Scheme.Modules.pullbackComp f' g).inv.app M

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-- **[Stacks, Tag 0F97]: the diagram, the two sections and the seven conditions.** For a global
section `s` of `L₁ ⊗ L₂` on a scheme `Y` with zero scheme `i : D → Y`, this records a scheme
`total` over `Y`, two closed subschemes `D₁`, `D₂` of it over `D`, two sections `sᵢ` of
`p^*Lᵢ`, and the seven numbered assertions of the source. -/
structure Decomposition (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) where
  /-- The total space `L` of the diagram. -/
  total : Scheme.{u}
  /-- The projection `p : L ⟶ Y`. -/
  p : total ⟶ Y
  /-- The closed subscheme `D₁ ⊆ L`, as ideal sheaf data. -/
  D₁ : total.IdealSheafData
  /-- The closed subscheme `D₂ ⊆ L`, as ideal sheaf data. -/
  D₂ : total.IdealSheafData
  /-- The map `p₁ : D₁ ⟶ D`. -/
  p₁ : D₁.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme
  /-- The map `p₂ : D₂ ⟶ D`. -/
  p₂ : D₂.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme
  /-- The left-hand square of the diagram commutes: `i₁ ≫ p = p₁ ≫ i`. -/
  comm₁ : D₁.subschemeι ≫ p = p₁ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι
  /-- The right-hand square of the diagram commutes: `i₂ ≫ p = p₂ ≫ i`. -/
  comm₂ : D₂.subschemeι ≫ p = p₂ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι
  /-- The section `s₁` of `p^*L₁`. -/
  s₁ : Γ((Scheme.Modules.pullback p).obj L₁, ⊤)
  /-- The section `s₂` of `p^*L₂`. -/
  s₂ : Γ((Scheme.Modules.pullback p).obj L₂, ⊤)
  /-- **Tag 0F97(1)**: `p^*s = s₁ ⊗ s₂`. -/
  pullback_section_eq :
    pullbackTensorSection p L₁ L₂ s =
      Stacks.Divisors.tensorSection ((Scheme.Modules.pullback p).obj L₁)
        ((Scheme.Modules.pullback p).obj L₂) ⊤ s₁ s₂
  /-- **Tag 0F97(2)**: `p` is locally of finite type. -/
  p_locallyOfFiniteType : LocallyOfFiniteType p
  /-- **Tag 0F97(2)**: `p` is quasi-compact; with the previous field, `p` is of finite type. -/
  p_quasiCompact : QuasiCompact p
  /-- **Tag 0F97(2)**: `p` is flat. -/
  p_flat : AlgebraicGeometry.Flat p
  /-- **Tag 0F97(2)**: `p` has relative dimension one. -/
  p_relativeDimension : letI : LocallyOfFiniteType p := p_locallyOfFiniteType
    AlgebraicGeometry.RelativeDimension p 1
  /-- **Tag 0F97(3)**: `D₁` is the zero scheme of `s₁`. -/
  zeroScheme₁ :
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible total.sheaf.obj
        total.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L₁) :=
      Stacks.Divisors.pullback_isInvertible p L₁
    D₁ = Stacks.Divisors.zeroScheme total ((Scheme.Modules.pullback p).obj L₁) s₁
  /-- **Tag 0F97(3)**: `D₂` is the zero scheme of `s₂`. -/
  zeroScheme₂ :
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible total.sheaf.obj
        total.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L₂) :=
      Stacks.Divisors.pullback_isInvertible p L₂
    D₂ = Stacks.Divisors.zeroScheme total ((Scheme.Modules.pullback p).obj L₂) s₂
  /-- **Tag 0F97(4)**: `D₁` is the line bundle `Spec_D(Sym^*(L₂^{⊗ -1}|_D))`. -/
  branch₁ : D₁.subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace
  /-- **Tag 0F97(4)**: that identification is one of schemes over `D`. -/
  branch₁_toBase :
    branch₁.hom ≫ (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase = p₁
  /-- **Tag 0F97(4)**: `D₂` is the line bundle `Spec_D(Sym^*(L₁^{⊗ -1}|_D))`. -/
  branch₂ : D₂.subscheme ≅ (branchSituation Y L₁ L₂ s L₁).totalSpace
  /-- **Tag 0F97(4)**: that identification is one of schemes over `D`. -/
  branch₂_toBase :
    branch₂.hom ≫ (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase = p₂
  /-- **Tag 0F97(5)**: `p^{-1}D = D₁ ∪ D₂`, the scheme-theoretic union. -/
  preimage_eq_union : (zeroIdeal Y L₁ L₂ s).comap p = D₁ ⊓ D₂
  /-- **Tag 0F97(6)**: the scheme-theoretic intersection `D₁ ∩ D₂` maps isomorphically to `D`. -/
  intersection_isIso :
    IsIso (Scheme.IdealSheafData.inclusion (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ p₁)
  /-- **Tag 0F97(7)**: `D₁ ∩ D₂ ⟶ D₁` is the zero section of the line bundle `D₁ ⟶ D`. -/
  intersection_zeroSection₁ :
    Scheme.IdealSheafData.inclusion (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ branch₁.hom =
      (Scheme.IdealSheafData.inclusion (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ p₁) ≫
        (branchSituation Y L₁ L₂ s L₂).zeroSection
  /-- **Tag 0F97(7)**: `D₁ ∩ D₂ ⟶ D₂` is the zero section of the line bundle `D₂ ⟶ D`. -/
  intersection_zeroSection₂ :
    Scheme.IdealSheafData.inclusion (le_sup_right : D₂ ≤ D₁ ⊔ D₂) ≫ branch₂.hom =
      (Scheme.IdealSheafData.inclusion (le_sup_right : D₂ ≤ D₁ ⊔ D₂) ≫ p₂) ≫
        (branchSituation Y L₁ L₂ s L₁).zeroSection

/-- **Tag 0F97, the base-change clause**, as a property of a decomposition: for every morphism
`g : Y' ⟶ Y` there is a decomposition of the base-changed section whose total space is the fibre
product, whose two closed subschemes are the inverse images of `D₁` and `D₂`, and whose two
sections are the pullbacks of `s₁` and `s₂`. -/
def Decomposition.IsStableUnderBaseChange {s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)}
    (R : Decomposition Y L₁ L₂ s) : Prop :=
  ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj L₁) := Stacks.Divisors.pullback_isInvertible g L₁
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj L₂) := Stacks.Divisors.pullback_isInvertible g L₂
    ∃ (R' : Decomposition Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s))
      (h : R'.total ⟶ R.total) (w : h ≫ R.p = R'.p ≫ g),
      IsPullback h R'.p R.p g ∧
        R'.D₁ = R.D₁.comap h ∧
        R'.D₂ = R.D₂.comap h ∧
        R'.s₁ = (squarePullbackMap w L₁).app ⊤
          (AlgebraicGeometry.pullbackGlobalSections h
            ((Scheme.Modules.pullback R.p).obj L₁) R.s₁) ∧
        R'.s₂ = (squarePullbackMap w L₂).app ⊤
          (AlgebraicGeometry.pullbackGlobalSections h
            ((Scheme.Modules.pullback R.p).obj L₂) R.s₂)

end Stacks.Chow.TensorZeroScheme

end
