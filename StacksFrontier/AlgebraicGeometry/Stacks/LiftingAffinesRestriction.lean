module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesChart
public import StacksFrontier.AlgebraicGeometry.Stacks.InnerSquareOfOuterTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Restricting along a thickening, read on algebraic spaces

Let `ι : 𝒳 ⟶ 𝒳'` be a 1-morphism of algebraic stacks and `U = U' ×_{𝒳'} 𝒳` the 2-fibre product
along a 1-morphism `b` out of an algebraic space `U'`, an algebraic space with a morphism
`iU : U ⟶ U'`. Two facts used by Stacks 0CJV:

* a morphism `T ⟶ U'` factors through `iU` exactly when its composite with `b` lifts to `𝒳`, so
  the factorization depends only on the 2-isomorphism class of that composite;
* if `T ×_{𝒳'} U'` is represented by an algebraic space `K'` and `T ⟶ 𝒳'` factors through `ι`
  along a relatively smooth `x_T : T ⟶ 𝒳`, then `K' ⟶ U'` factors through `iU` by a smooth
  morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory Bicategory

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The relative property of the second leg, read on a first leg out of an algebraic
space.** -/
theorem prop_representingMap_fst_of_isTwoFibreProduct
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V I : AlgebraicSpaces B S hS}
    {x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳}
    {y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳}
    {fst : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).obj U}
    {snd : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).obj V}
    {γ : fst ≫ x ≅ snd ≫ y}
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    (hy : HasRelativeProperty.{u, u, u + 1, v} B S hS P y.hom
      (isRepresentableByAlgebraicSpaces_of_space_source y)) :
    P (ObjectProperty.homMk (representingMap B S hS _ _ I.obj U.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) fst.hom) : I ⟶ U) := by
  let Q := (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y).underlying
  exact prop_representingMap_of_hasRelativeProperty.{u, v} B S hS P y.hom
    (isRepresentableByAlgebraicSpaces_of_space_source y) hy
    ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U).val x.hom Q
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _ hP) I.obj U.obj I.property
    U.property (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- **Factorization through a base change of `ι` depends only on the 2-isomorphism class of the
composite.** Let `U₁ = U₁' ×_{𝒳'} 𝒳` and `U₂ = U₂' ×_{𝒳'} 𝒳` be 2-fibre products of algebraic
spaces along `b₁`, `b₂`, and let `e₁ : T ⟶ U₁'`, `e₂ : T ⟶ U₂'` have 2-isomorphic composites with
`b₁`, `b₂`. If `e₁` factors through `U₁` then `e₂` factors through `U₂`. -/
theorem exists_factor_of_twoIso {U₁' U₂' U₁ U₂ T : AlgebraicSpaces B S hS}
    {b₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U₁' ⟶ 𝒳'}
    {b₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U₂' ⟶ 𝒳'}
    {iU₁ : U₁ ⟶ U₁'} {iU₂ : U₂ ⟶ U₂'}
    {a₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U₁ ⟶ 𝒳}
    {a₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U₂ ⟶ 𝒳}
    (γ₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU₁ ≫ b₁ ≅ a₁ ≫ ι)
    {γ₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU₂ ≫ b₂ ≅ a₂ ≫ ι}
    (h₂ : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ₂⟩ : Bicategory.TwoCommSq b₂ ι))
    (e₁ : T ⟶ U₁') (e₂ : T ⟶ U₂')
    (η : (algebraicSpaceStackFunctor.{u, w} B S hS).map e₁ ≫ b₁ ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e₂ ≫ b₂)
    (k₁ : T ⟶ U₁) (hk₁ : k₁ ≫ iU₁ = e₁) :
    ∃ k₂ : T ⟶ U₂, k₂ ≫ iU₂ = e₂ ∧
      Nonempty ((algebraicSpaceStackFunctor.{u, w} B S hS).map k₁ ≫ a₁ ≅
        (algebraicSpaceStackFunctor.{u, w} B S hS).map k₂ ≫ a₂) := by
  subst hk₁
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let N : Bicategory.TwoCommSq b₂ ι :=
    { pt := F.obj T
      fst := F.map e₂
      snd := F.map k₁ ≫ a₁
      iso := η.symm ≪≫ eqToIso (by rw [Functor.map_comp]) ≪≫ α_ _ _ _ ≪≫
        whiskerLeftIso (F.map k₁) γ₁ ≪≫ (α_ _ _ _).symm }
  let m := Bicategory.twoFibreProductPreHom h₂ N
  have he : F.map e₂ = m.hom ≫ F.map iU₂ := eq_of_hom₂_algebraicSpaceStackFunctor_obj m.isoFst.hom
  let k₂ : T ⟶ U₂ := ObjectProperty.homMk (representingMap B S hS _ _ T.obj U₂.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) m.hom.hom)
  have hk₂ : F.map k₂ = m.hom := algebraicSpaceStackFunctor_map_homMk_representingMap m.hom
  refine ⟨k₂, ?_, ⟨m.isoSnd ≪≫ eqToIso (by rw [hk₂])⟩⟩
  apply algebraicSpaceStackFunctor_map_injective
  rw [Functor.map_comp, hk₂, he]

/-- **The base change of a relatively smooth `x_T` along the thickened chart, recognised on a
2-fibre product over `𝒳'`.** Let `U = U' ×_{𝒳'} 𝒳` be a 2-fibre product of algebraic spaces along
`b`, let `x_T : T ⟶ 𝒳` be relatively smooth and `G ≅ x_T ≫ ι`, and let `K = U' ×_{𝒳'} T` be a
2-fibre product of algebraic spaces along `(b, G)` with first projection `k₁ : K ⟶ U'`. Then `k₁`
factors through `U ⟶ U'` by a smooth morphism of algebraic spaces. -/
theorem exists_smooth_factor_of_isTwoFibreProduct {U' U T K : AlgebraicSpaces B S hS}
    {b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U' ⟶ 𝒳'} {iU : U ⟶ U'}
    {a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳}
    {γU : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι}
    (hU : Bicategory.IsTwoFibreProduct (⟨_, _, _, γU⟩ : Bicategory.TwoCommSq b ι))
    (xT : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒳)
    (hxT : IsRelativelySmooth.{u, u, u + 1} B S hS xT.hom)
    {G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒳'} (θ : xT ≫ ι ≅ G)
    {k₁ : K ⟶ U'} {k₂ : K ⟶ T}
    {γN : (algebraicSpaceStackFunctor.{u, w} B S hS).map k₁ ≫ b ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map k₂ ≫ G}
    (hN : Bicategory.IsTwoFibreProduct (⟨_, _, _, γN⟩ : Bicategory.TwoCommSq b G)) :
    ∃ m : K ⟶ U, m ≫ iU = k₁ ∧ Space.IsSmooth B S hS m.hom := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let P : Bicategory.TwoCommSq b ι := ⟨_, _, _, γU⟩
  let N : Bicategory.TwoCommSq b G := ⟨_, _, _, γN⟩
  let inner := innerSquareOfOuter B S hS P hU θ N
  let m : K ⟶ U := ObjectProperty.homMk (representingMap B S hS _ _ K.obj U.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) inner.fst.hom)
  have hm : F.map m = inner.fst := algebraicSpaceStackFunctor_map_homMk_representingMap inner.fst
  refine ⟨m, ?_, ?_⟩
  · apply algebraicSpaceStackFunctor_map_injective
    rw [Functor.map_comp, hm]
    exact (eq_of_hom₂_algebraicSpaceStackFunctor_obj
      (innerSquareOfOuter_fst_comp_iso B S hS P hU θ N).hom).symm
  · exact prop_representingMap_fst_of_isTwoFibreProduct.{u, w, u + 1}
      (Space.smoothMorphismProperty B S hS) (x := a) (y := xT) (fst := inner.fst)
      (snd := inner.snd) (γ := inner.iso)
      (isTwoFibreProduct_innerSquareOfOuter B S hS P hU θ N hN) hxT.2

/-- **A 2-fibre product stays one when its legs are replaced by 2-isomorphic ones.** -/
noncomputable def isTwoFibreProduct_ofComparison_id {𝒜 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒜 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P)
    {a : P.pt ⟶ 𝒜} {b : P.pt ⟶ 𝒴} (ea : a ≅ 𝟙 P.pt ≫ P.fst) (eb : b ≅ 𝟙 P.pt ≫ P.snd) :
    Bicategory.IsTwoFibreProduct (P.ofComparison (𝟙 P.pt) ea eb) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (isTwoFibreProduct_underlying_algebraicStacks B S hS P hP)
      (Bicategory.TwoCommSq.PreHom.ofComparison P (𝟙 P.pt) ea eb).underlying
      (inferInstanceAs (𝟭 _).IsEquivalence))

/-- **A pullback square of algebraic spaces is a 2-fibre product of algebraic stacks.** -/
noncomputable def isTwoFibreProduct_of_isPullback {T P Q R : AlgebraicSpaces B S hS}
    {p : T ⟶ P} {q : T ⟶ Q} {a : P ⟶ R} {c : Q ⟶ R} (h : IsPullback p.hom q.hom a.hom c.hom) :
    Bicategory.IsTwoFibreProduct (⟨(algebraicSpaceStackFunctor.{u, w} B S hS).obj T,
      (algebraicSpaceStackFunctor.{u, w} B S hS).map p,
      (algebraicSpaceStackFunctor.{u, w} B S hS).map q,
      Bicategory.InducedBicategory.isoMk (fibredCategorySquare h.w).iso⟩ :
        Bicategory.TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map a)
          ((algebraicSpaceStackFunctor.{u, w} B S hS).map c)) :=
  Bicategory.isTwoFibreProduct_of_underlying (isTwoFibreProduct_fibredCategorySquare h)

end AlgebraicGeometry.Stack

end
