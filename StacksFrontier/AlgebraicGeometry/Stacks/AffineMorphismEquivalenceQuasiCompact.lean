module

public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineDiagonalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Equivalences are affine, and affine 1-morphisms are quasi-compact

Two facts about affine 1-morphisms of algebraic stacks (**Stacks 0CHQ**) used by the proof of
**Stacks 076Z**.

* A 1-morphism whose underlying functor is an equivalence is affine in the sense of Properties
  of Stacks, Section 04XB. Every base change of it along a scheme-valued point `y` of the target
  is a category fibred in groupoids whose fibres are nonempty (the functor is essentially
  surjective) and connected (it is fully faithful, **Stacks 003Z**); so a presheaf representing
  it has exactly one section over every object, and its structural morphism to the representable
  presheaf of the point is an isomorphism, which is affine.
* An affine 1-morphism is quasi-compact (**Stacks 050U**): each represented base change is an
  affine morphism of algebraic spaces, hence quasi-compact (**Stacks 03HE**), and the two notions
  of quasi-compactness agree for a 1-morphism representable by algebraic spaces (**Stacks 050T**).

A 1-morphism representable by algebraic spaces with affine relative diagonal is quasi-separated,
by the same passage on the diagonal (**Stacks 04YT**).

## Main results

* `AlgebraicGeometry.Stack.isAffineHom_of_isEquivalence`
* `AlgebraicGeometry.Stack.isQuasiCompact_catFibered_of_isAffineHom`
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_of_isAffineHom`
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_hasAffineDiagonal`
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism whose underlying functor is an equivalence is affine** in the sense of
Properties of Stacks, Section 04XB. At a scheme-valued point `y` of the target over `U`, the
fibres of `(Sch/U)_fppf ×_𝒴 𝒳 ⟶ (Sch/U)_fppf` are connected because the functor is fully faithful
(`AlgebraicGeometry.Stack.subsingleton_representing_of_full_and_faithful`) and nonempty because a
quasi-inverse over the site (**Stacks 003Z (2)**) supplies an object of `𝒳` with a vertical
isomorphism to the image of `y`. A representing presheaf therefore has exactly one section over
every object, its structural morphism to `h_U` is bijective on sections, and an isomorphism of
algebraic spaces is affine. -/
theorem isAffineHom_of_isEquivalence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : (CatFiberedInGroupoids.homFunctor j).IsEquivalence) : IsAffineHom B S hS j := by
  intro U y hy F hF he
  have hsub := subsingleton_representing_of_full_and_faithful B S hS j inferInstance
    inferInstance U y F he
  obtain ⟨e⟩ := he
  obtain ⟨G, hG, -, ε, -, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over 𝒳.val.p
    𝒴.val.p 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor j)
    (CatFiberedInGroupoids.homFunctor_comp_p j) hj
  have hne : ∀ V : BigFppfOver B U.left.1 U.left.2, Nonempty (F.obj (op V)) := by
    intro V
    have h1 : 𝒴.val.p.obj (y.obj V) = (Over.map U.hom).obj V := Functor.congr_obj hy V
    have hlift := hε (y.obj V)
    rw [h1] at hlift
    have hlift' : 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj V)) (ε.app (y.obj V)).hom := hlift
    have hinv : 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj V)) (ε.app (y.obj V)).inv :=
      IsHomLift.lift_id_inv 𝒴.val.p _ (ε.app (y.obj V))
    let P : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor j) :=
      { base := (Over.map U.hom).obj V
        x := V
        y := G.obj (y.obj V)
        hx := rfl
        hy := (Functor.congr_obj hG (y.obj V)).trans h1
        iso := (ε.app (y.obj V)).symm
        vertical := hinv }
    exact ⟨PresheafOfCategories.elementsFiberEquiv F V
      ((PresheafOfCategories.fiberFunctorOfComp e.hom.w V).obj ⟨P, rfl⟩)⟩
  let Fy := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
  have hiso : IsIso (algebraicSpaceMap B S hS U Fy).hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    rw [isIso_iff_bijective]
    refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF hsub) W), fun v => ?_⟩
    obtain ⟨t⟩ := hne (Over.mk v.left)
    refine ⟨((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app
      (⟨F, hF⟩ : AlgebraicSpaces B U.left.1 U.left.2)).app W ⟨⟨v.left, t⟩, Over.w v⟩, ?_⟩
    exact (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS
      U.hom ⟨F, hF⟩ W ⟨⟨v.left, t⟩, Over.w v⟩).trans (Over.OverMorphism.ext rfl)
  exact Space.isAffineHom_of_isIso (algebraicSpaceMap B S hS U Fy).hom

/-- **An affine 1-morphism is quasi-compact**, in the sense of Properties of Stacks,
Section 04XB: each represented base change is an affine morphism of algebraic spaces, hence a
quasi-compact one (**Stacks 03HE**). -/
theorem isQuasiCompact_catFibered_of_isAffineHom
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsAffineHom B S hS f) : IsQuasiCompact B S hS f :=
  fun U y hy F hF he =>
    Space.isQuasiCompact_of_isAffineHom' B S hS _
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
      (isAlgebraicSpace_yoneda B S hS _) (hf U y hy F hF he)

namespace AlgebraicStacks

/-- **An affine 1-morphism of algebraic stacks is quasi-compact** (**Stacks 050U**): it is
quasi-compact in the sense of Section 04XB by
`AlgebraicGeometry.Stack.isQuasiCompact_catFibered_of_isAffineHom`, and **Stacks 050T** identifies
the two
notions for a 1-morphism representable by algebraic spaces. -/
theorem isQuasiCompactMorphism_of_isAffineHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsAffineHom B S hS f) : IsQuasiCompactMorphism.{u, w} B S hS f :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS f hf.1).1
    (Stack.isQuasiCompact_catFibered_of_isAffineHom B S hS f.hom hf.2)

/-- **A 1-morphism representable by algebraic spaces with affine relative diagonal is
quasi-separated** (**Stacks 04YW**): its diagonal is affine, hence quasi-compact, and for such a
1-morphism quasi-separatedness is quasi-compactness of the diagonal (**Stacks 04YT**). -/
theorem isQuasiSeparated_of_hasAffineDiagonal {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hf : HasAffineDiagonal B S hS f) : IsQuasiSeparated B S hS f :=
  (isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS f hrep).2
    (Stack.isQuasiCompact_catFibered_of_isAffineHom B S hS _ hf)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
