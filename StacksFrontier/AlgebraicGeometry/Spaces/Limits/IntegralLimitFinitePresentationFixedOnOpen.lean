module

public import Mathlib.CategoryTheory.Filtered.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlgebraDirectedColimitIsoOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralFiniteSystemFixedOnOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraChartIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraFiniteOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFiniteFinitePresentation

/-!
# An integral morphism as a limit of finite morphisms of finite presentation, fixed over an open

Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated, and let `V ⊂ Y` be a quasi-compact open subspace such that `f⁻¹(V) ⟶ V` is finite
and of finite presentation. Then `X = lim X_i` is a directed limit of algebraic spaces
`f_i : X_i ⟶ Y` finite and of finite presentation over `Y`, such that `f⁻¹(V) ⟶ f_i⁻¹(V)` is an
isomorphism for every `i`.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecPointsπNatTrans`: The projections of the relative spectra of
  a diagram of algebras, as a natural transformation to the constant diagram on the base.

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_finite_finitePresentation_fixedOnOpen`: An integral
  morphism of algebraic spaces with quasi-compact quasi-separated target, finite and of finite
  presentation over a quasi-compact open `V`, is a directed limit of finite morphisms of finite
  presentation, each inducing an isomorphism over `V`.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projections of the relative spectra of a diagram of algebras, as a natural transformation
to the constant diagram on the base. -/
@[simps]
def relativeSpecPointsπNatTrans {Y : AlgebraicSpaces B S hS} {I : Type*} [Category I]
    (E : I ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    E.op ⋙ relativeSpecPointsFunctor B S hS Y ⟶ (Functor.const Iᵒᵖ).obj Y.1 where
  app i := relativeSpecPointsπ B S hS (E.obj i.unop)
  naturality i j g := by
    change relativeSpecPointsMap B S hS (E.map g.unop) ≫ relativeSpecPointsπ B S hS _ =
      relativeSpecPointsπ B S hS _ ≫ 𝟙 _
    rw [relativeSpecPointsMap_comp_π, Category.comp_id]

/-- An integral morphism `f : X ⟶ Y` of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated, which is finite and of finite presentation over a quasi-compact open subspace `V`
of `Y` (that is, `f⁻¹(V) = X ×_Y V ⟶ V` is), is the limit of a directed inverse system, indexed by
a nonempty directed preorder in the universe of the schemes, of algebraic spaces `D i` with
morphisms `t i : D i ⟶ Y` finite and of finite presentation, the limiting cone `p` having vertex
`X` and lying over `Y`; and for every `i` the square formed by `X ×_Y V ⟶ X ⟶ D i`, `X ×_Y V ⟶ V`,
`t i` and `V ⟶ Y` is cartesian, that is `f⁻¹(V) ⟶ f_i⁻¹(V)` is an isomorphism. -/
@[stacks 0GUM]
theorem exists_isLimit_finite_finitePresentation_fixedOnOpen
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsIntegralHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hfVfinite : IsFinite B S hS (pullback.snd f V.ι))
    (hfVfp : IsFinitePresentation B S hS (pullback.snd f V.ι)) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
      (∀ i, IsFinite B S hS (t.app i)) ∧
      (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
      Nonempty (IsLimit (Cone.mk X p)) ∧
      (∀ i, IsPullback (pullback.fst f V.ι ≫ p.app i) (pullback.snd f V.ι) (t.app i) V.ι) := by
  let Ya : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Xa : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let fa : Xa ⟶ Ya := ObjectProperty.homMk f
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isIntegralHom B S hS fa hf
  have haff : IsAffineHom B S hS f := isAffineHom_of_isIntegralHom f hf
  let A := pushforwardAlgebra B S hS (Over.mk fa)
  have hfqc : IsQuasiCompact B S hS f := isQuasiCompact_of_isAffineHom' B S hS f hX hY haff
  have hfqs : IsQuasiSeparated B S hS f := isQuasiSeparated_of_isAffineHom B S hS f hX hY haff
  have hA : A.IsQuasicoherent := isQuasicoherent_pushforwardAlgebra B S hS fa hfqc hfqs
    fun h₁ h₂ F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS fa h₁ h₂ F hF
  have hint : A.IsIntegral := isIntegral_pushforwardAlgebra_of_isIntegralHom B S hS fa hf
  have hfinfp := fun U hU hUV =>
    finite_and_finitePresentation_pushforwardAlgebra_algebraMap_of_range_le B S hS fa hrep hV.2
      hfVfinite hfVfp U hU hUV
  obtain ⟨I, instI, hne, hdir, E, tA, htA, hE⟩ :=
    exists_directed_isColimit_isFinite_isIsoOver B S hS Ya hYqc hYqs A hA hint hV.2 hVqc
      (fun U hU hUV => (hfinfp U hU hUV).1) (fun U hU hUV => (hfinfp U hU hUV).2)
  have : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have : IsConnected I := IsFiltered.isConnected I
  obtain ⟨⟨hlim⟩, hcomp, hpb⟩ := isLimit_toRelativeSpecPointsCone_and_isPullback B S hS fa hV.2
    tA haff htA fun i => (hE i).2.2.2
  have hspec : ∀ i : I, IsAlgebraicSpace B S hS (relativeSpecPoints B S hS (E.obj i)) ∧
      IsFinite B S hS (relativeSpecPointsπ B S hS (E.obj i)) ∧
      IsFinitePresentation B S hS (relativeSpecPointsπ B S hS (E.obj i)) := fun i =>
    isAlgebraicSpace_isFinite_isFinitePresentation_relativeSpecPointsπ B S hS (E.obj i) (hE i).1
      (hE i).2.1 (hE i).2.2.1
  exact ⟨I, instI, hne, hdir, E.op ⋙ relativeSpecPointsFunctor B S hS Ya,
    (toRelativeSpecPointsCone B S hS fa tA).π, relativeSpecPointsπNatTrans B S hS E,
    fun i => (hspec i.unop).1, fun i => (hspec i.unop).2.1, fun i => (hspec i.unop).2.2,
    NatTrans.ext (funext fun i => hcomp i.unop), ⟨hlim⟩, fun i => hpb i.unop⟩

end AlgebraicGeometry.Space

end
