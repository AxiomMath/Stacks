module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible

/-!
# A meromorphic section honest on a chart that `c_ξ` factors through lies in `ℒ_ξ`

Let `X` be a decent algebraic space over `S`, let `Z ⊆ X` be a prime divisor with generic point
`ξ`, let `ℒ` be an `𝒪_X`-module and let `s` be a meromorphic section of `ℒ`.  The germ of `s` at
`ξ` is the value over the identity étale chart of `Spec(𝒪^h_{X, ξ})` of the pullback of `s`
along `c_ξ`, and `AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk` asks it to be the
image of a section of `ℒ_ξ = c_ξ^*ℒ`.

This file discharges that condition from a *presentation of `s` as an honest section of `ℒ`*
over an étale chart `V` of `X` which the canonical morphism `c_ξ` factors through: the
evaluation lemma `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram` computes
the germ as the chartwise pullback of the pure meromorphic section `1 ⊗ e`, and
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul` evaluates that as
`1 ⊗ c_ξ^*e`, which is the pure meromorphic section of a section of `ℒ_ξ`.

## Main results

* `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_toMeromorphicSectionValue`: **the
  global pullback of an honest section is an honest section.**  If a meromorphic section `s` of
  `M` is, over the chart `V` of a commuting square `d` of étale charts over `f`, the image of a
  section `e` of `M`, then `f^*s` is, over the chart `U` of `d`, the image of the section
  `f^*e` of `f^*M`.
* `AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq`: if `s` is over an
  étale chart `V` of `X` the image of an honest section `e` of `ℒ`, and the canonical morphism
  `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` factors through `V` in a commuting square of étale charts whose
  chart of `Spec(𝒪^h_{X, ξ})` is the identity one, then `s` lies in `ℒ_ξ`.

## Implementation notes

The hypothesis is the *square*, not just the morphism `Spec(𝒪^h_{X, ξ}) ⟶ V` of schemes: a
`AlgebraicGeometry.Space.ChartDiagram` records the morphism of objects of the big fppf site
together with the commutation over `X`, and the evaluation lemma of Stacks 0ENC, part (1) is
stated at such a square.  The chart of the source is the identity one, which is where
`AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalk` is read; the lemma therefore says
nothing about any other chart of `Spec(𝒪^h_{X, ξ})`, and producing the square is exactly the
geometric content that remains for Stacks 0EPS — a lift of `c_ξ` through `V`.

The section of `ℒ_ξ` produced is `AlgebraicGeometry.Space.modulePullbackChartFMap`, the chart
component of the unit of the Stacks 03D7 adjunction, applied to `e` along the square; that is
the formal meaning of `c_ξ^*e`.  The coefficient `1` of the pure meromorphic section is carried
to `1` because the chartwise pullback of meromorphic functions is a ring homomorphism.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global pullback of a meromorphic section carries an honest section to an honest
section.**  Let `d` be a commuting square of étale scheme charts over a morphism `f` of
algebraic spaces for which pullbacks of meromorphic functions are defined, and suppose the
meromorphic section `s` of `M` is over the chart `d.V` of the target the image of a section `e`
of `M` under the canonical map `M ⟶ 𝒦(M)`.  Then `f^*s` is over the chart `d.U` of the source
the image of the section `f^*e` of `f^*M`.

This is `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram` at the pure
meromorphic section `1 ⊗ e`, whose chartwise pullback is `f^♯1 ⊗ f^*e` by
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul`, and `f^♯1 = 1` because the
chartwise pullback of meromorphic functions is a ring homomorphism. -/
theorem pullbackMeromorphicSection_eval_toMeromorphicSectionValue
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
    (M : Modules.{u, u} B S hS Ys.1 Ys.2) (hf : PullbacksMeromorphicSections B S hS f.hom)
    (s : MeromorphicSection.{u, u} B S hS Ys.1 Ys.2 M)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) (e : M.val.obj (op d.V))
    (he : s.eval (op d.V) = toMeromorphicSectionValue B S hS Ys.1 Ys.2 M d.V e) :
    (pullbackMeromorphicSection B S hS f M hf s).eval (op d.U) =
      toMeromorphicSectionValue B S hS Xs.1 Xs.2 ((modulePullback B S hS f).obj M) d.U
        ((modulePullbackChartFMap B S hS f M).app d e) := by
  rw [toMeromorphicSectionValue_eq B S hS Xs.1 Xs.2 ((modulePullback B S hS f).obj M) d.U]
  refine (pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s d
    (pureMeromorphicSection B S hS Ys.1 Ys.2 M d.V e) he).trans ?_
  refine congrArg (toMeromorphicSectionSheaf B S hS Xs.1 Xs.2
    ((modulePullback B S hS f).obj M) d.U) ?_
  refine (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hf d
    (1 : (meromorphicChartSheaf B S hS Ys.1 Ys.2).obj.obj (op d.V)) e).trans ?_
  exact congrArg (fun z : (meromorphicChartSheaf B S hS Xs.1 Xs.2).obj.obj (op d.U) ↦
      (z ⊗ₜ[chartRing B S hS Xs.1 Xs.2 d.U]
          ((modulePullbackChartFMap B S hS f M).app d e) :
        (meromorphicSectionModule B S hS Xs.1 Xs.2 ((modulePullback B S hS f).obj M)).obj
          (op d.U)))
    (map_one (chartMeromorphicPullbackHom B S hS f hf d))

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- **A meromorphic section which is an honest section over a chart that `c_ξ` factors through
lies in `ℒ_ξ`.**  Let `V` be an étale chart of `X` over which the meromorphic section `s` of `ℒ`
is the image of a section `e` of `ℒ`, and suppose the canonical morphism
`c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` factors through `V` in a commuting square of étale charts whose
chart of `Spec(𝒪^h_{X, ξ})` is the identity one.  Then the germ of `s` at `ξ` is the image of a
section of `ℒ_ξ`, that is `s` lies in `ℒ_ξ`.

This is `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_toMeromorphicSectionValue` at
that square: the germ of `s` at `ξ` is by definition the value of `c_ξ^*s` over the identity
chart of `Spec(𝒪^h_{X, ξ})`, and the comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ` is by definition the canonical
map `ℒ_ξ ⟶ 𝒦(ℒ_ξ)` over that chart. -/
theorem PrimeDivisor.memGenericModuleStalk_of_eval_eq (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (g : (SmallEtale.toOver B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj).obj
        (Z.genericHenselianChart B S hS hX hdec R hR) ⟶
      (SmallEtale.toOver B S hS X).obj V)
    (hcomm : (Z.genericHenselianChart B S hS hX hdec R hR).1.hom ≫
        (Z.genericHenselianMorphism B S hS hX hdec R hR).hom =
      yoneda.map g ≫ V.1.hom)
    (e : L.val.obj (op V))
    (he : s.eval (op V) = toMeromorphicSectionValue B S hS X hX L V e) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s :=
  ⟨(modulePullbackChartFMap B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L).app
      ⟨Z.genericHenselianChart B S hS hX hdec R hR, V, g, hcomm⟩ e,
    (pullbackMeromorphicSection_eval_toMeromorphicSectionValue B S hS
      (Z.genericHenselianMorphism B S hS hX hdec R hR) L
      (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s
      ⟨Z.genericHenselianChart B S hS hX hdec R hR, V, g, hcomm⟩ e he).symm⟩

/-- **A meromorphic section which is an honest section over the generic chart of a prime divisor
lies in `ℒ_ξ`.**  The canonical morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` factors through the
generic chart `AlgebraicGeometry.Space.PrimeDivisor.genericEtaleChart` by
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianMorphism_hom`, and the factorization is a
commuting square of étale charts whose chart of `Spec(𝒪^h_{X, ξ})` is the identity one, the
structure morphism of that chart being the identity.

So no lift of `c_ξ` through an arbitrary chart is needed: for the first collection of
Stacks 0EPS it suffices to present `s` as an honest section of `ℒ` over the generic chart of the
prime divisor, which is a statement on the small étale site of `X` alone. -/
theorem PrimeDivisor.memGenericModuleStalk_of_eval_genericEtaleChart_eq
    (L : Modules.{u, u} B S hS X hX) (s : MeromorphicSection.{u, u} B S hS X hX L)
    (e : L.val.obj (op (Z.genericEtaleChart B S hS hX hdec)))
    (he : s.eval (op (Z.genericEtaleChart B S hS hX hdec)) =
      toMeromorphicSectionValue B S hS X hX L (Z.genericEtaleChart B S hS hX hdec) e) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s :=
  Z.memGenericModuleStalk_of_eval_eq B S hS hX hdec R hR L s
    (Z.genericEtaleChart B S hS hX hdec)
    ((Z.genericChart B S hS hX hdec).toSchemeHom R hR)
    ((Category.id_comp (Z.genericHenselianMorphism B S hS hX hdec R hR).hom).trans
      (Z.genericHenselianMorphism_hom B S hS hX hdec R hR)) e he

/-- **A meromorphic section of an invertible module whose pullback to `Spec(𝒪^h_{X, ξ})` is an
honest section on a covering sieve of the identity chart lies in `ℒ_ξ`.**

The pullback `ℒ_ξ = c_ξ^*ℒ` is again invertible, by Stacks 0B8P on the small étale sites
(`AlgebraicGeometry.Space.isInvertible_modulePullback_obj`), so lying in `ℒ_ξ` is a local
condition on a section of `𝒦(ℒ_ξ)` by
`AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionValue_of_sieve`, and the germ at `ξ`
is the value of `c_ξ^*s` over the identity chart.

Together with
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq` this is the descent form
of the first collection of Stacks 0EPS: a presentation of `s` as an honest section over *any*
étale chart `V` of `X` makes `c_ξ^*s` honest over the base change
`Spec(𝒪^h_{X, ξ}) ×_X V`, and it suffices that those base changes cover
`Spec(𝒪^h_{X, ξ})` — no lift of `c_ξ` through `V` is needed. -/
theorem PrimeDivisor.memGenericModuleStalk_of_sieve (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (T : Sieve (Z.genericHenselianChart B S hS hX hdec R hR))
    (hT : T ∈ SmallEtale.topology B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianChart B S hS hX hdec R hR))
    (hloc : ∀ ⦃W : SmallEtale B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj⦄
      (k : W ⟶ Z.genericHenselianChart B S hS hX hdec R hR), T k →
      ∃ e : (Z.genericHenselianPullback B S hS hX hdec R hR L).val.obj (op W),
        (pullbackMeromorphicSection B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L
              (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR)
              s).eval (op W) =
          toMeromorphicSectionValue B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L) W e) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s := by
  obtain ⟨e, he⟩ := exists_eval_eq_toMeromorphicSectionValue_of_sieve B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR)
    (Z.genericHenselianPullback B S hS hX hdec R hR L)
    (isInvertible_modulePullback_obj B S hS
      (Z.genericHenselianMorphism B S hS hX hdec R hR) L hL)
    (pullbackMeromorphicSection B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L
      (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s)
    (Z.genericHenselianChart B S hS hX hdec R hR) T hT hloc
  exact ⟨e, he.symm⟩

end Generic

end AlgebraicGeometry.Space

end
