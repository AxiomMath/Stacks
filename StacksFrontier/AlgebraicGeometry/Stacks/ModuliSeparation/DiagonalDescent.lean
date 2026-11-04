module

public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Universal closedness of relative diagonals descends along surjections

Let `f : 𝒳 ⟶ 𝒴` be a surjective universally closed 1-morphism of algebraic stacks and let
`h : 𝒴 ⟶ 𝒯`. If the relative diagonal of `f ≫ h` is universally closed, then so is the relative
diagonal of `h`. The relative diagonals are related by `Δ_{f ≫ h} ≫ (f × f) = f ≫ Δ_h`, where
`f × f : 𝒳 ×_𝒯 𝒳 ⟶ 𝒴 ×_𝒯 𝒴` is universally closed when `f` is.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.mapSnd`: the 1-morphism `𝒰 ×_𝒵 𝒳 ⟶ 𝒰 ×_𝒵 𝒴` induced
  by `f : 𝒳 ⟶ 𝒴` on the second factor.
* `AlgebraicGeometry.Stack.AlgebraicStacks.swapHom`: the exchange of factors of a 2-fibre product
  of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_id`: the identity 1-morphism of an
  algebraic stack is universally closed.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_comparisonCospanRight`: `f × f` is
  universally closed when `f` is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp_comparisonCospanRight`:
  `Δ_{f ≫ h} ≫ (f × f) = f ≫ Δ_h`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_relativeDiagonal_of_comp`: universal
  closedness of a relative diagonal descends along a surjective universally closed 1-morphism.
* `AlgebraicStacks.universallyClosed_relativeDiagonalAlgebraicStacks_of_isSeparated`: the
  relative diagonal of a separated 1-morphism is universally closed.

## References

* [Stacks Project, Tag 0515](https://stacks.math.columbia.edu/tag/0515)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
* [Stacks Project, Tag 0DUY](https://stacks.math.columbia.edu/tag/0DUY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The identity 1-morphism of an algebraic stack is universally closed.** -/
theorem universallyClosed_id (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) :
    UniversallyClosed B S hS (𝟙 𝒴) := by
  intro 𝒵 g
  have hE := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) g
  set E := Stack.twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) g
  have hhom : @IsHomeomorph _ _ (pointTopology B S hS E.swap.pt.val)
      (pointTopology B S hS 𝒵.val)
      (Stack.pointsMap B S hS E.swap.pt.val.val E.swap.pt.val.property 𝒵.val.property
        E.swap.fst.hom.hom) :=
    isHomeomorph_pointsMap_of_isEquivalence B S hS E.pt.val 𝒵.val E.snd.hom.hom
      (sectionSecondProjection_isEquivalence B S hS g)
  have h := Stack.isHomeomorph_pointsMap_fst_congr B S hS E.swap.underlying
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g (𝟙 𝒴)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Bicategory.isTwoFibreProduct_swap hE))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g (𝟙 𝒴))) hhom
  let := pointTopology B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g (𝟙 𝒴)).underlying.pt
  let := pointTopology B S hS 𝒵.val
  exact h.isClosedMap

/-- **A 1-morphism with a strict two-sided inverse is universally closed.** -/
theorem universallyClosed_of_comp_eq_id {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (σ : 𝒳 ⟶ 𝒴) (τ : 𝒴 ⟶ 𝒳) (hστ : σ ≫ τ = 𝟙 𝒳) (hτσ : τ ≫ σ = 𝟙 𝒴) :
    UniversallyClosed B S hS σ := by
  refine universallyClosed_of_surjective_comp B S hS τ σ ?_ ?_
  · exact hτσ ▸ universallyClosed_id B S hS 𝒴
  · refine fun x => ⟨pointsMap B S hS σ x, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS τ), ← pointsMap_comp B S hS σ τ, hστ,
      pointsMap_id]
    rfl

section MapSnd

variable {𝒰 𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (z : 𝒰 ⟶ 𝒵) (f : 𝒳 ⟶ 𝒴)
  (g : 𝒴 ⟶ 𝒵)

/-- The 1-morphism `𝒰 ×_{z, 𝒵, f ≫ g} 𝒳 ⟶ 𝒰 ×_{z, 𝒵, g} 𝒴` induced by `f` on the second
factor: it sends `(U, u, x, φ)` to `(U, u, f x, φ)`. -/
def mapSnd :
    twoFibreProductAlgebraicStack B S hS z (f ≫ g) ⟶ twoFibreProductAlgebraicStack B S hS z g :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.splitSnd 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
          𝒵.val.val.p z.hom.hom.toFunctor f.hom.hom.toFunctor g.hom.hom.toFunctor
          f.hom.hom.w ⋙
        TwoFibreProductOver.fst _ _ _ _ _
      w := rfl })

/-- The square exhibiting `AlgebraicGeometry.Stack.AlgebraicStacks.mapSnd` as a base change of
`f` along the second projection of `𝒰 ×_𝒵 𝒴`. -/
def mapSndSquare :
    Bicategory.TwoCommSq (Stack.twoFibreProductSquareAlgebraicStacks B S hS z g).snd f where
  pt := twoFibreProductAlgebraicStack B S hS z (f ≫ g)
  fst := mapSnd B S hS z f g
  snd := (Stack.twoFibreProductSquareAlgebraicStacks B S hS z (f ≫ g)).snd
  iso := Iso.refl _

/-- **`f` on the second factor is a base change of `f`**: the square
`AlgebraicGeometry.Stack.AlgebraicStacks.mapSndSquare` is a 2-fibre product. -/
noncomputable def isTwoFibreProduct_mapSndSquare :
    Bicategory.IsTwoFibreProduct (mapSndSquare B S hS z f g) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS z g).snd.hom f.hom)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1}
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS z g).snd.hom f.hom
        (mapSndSquare B S hS z f g).underlying)
      (TwoFibreProductOver.isEquivalence_splitSnd 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        𝒵.val.val.p z.hom.hom.toFunctor f.hom.hom.toFunctor g.hom.hom.toFunctor
        f.hom.hom.w g.hom.hom.w))

/-- `f` on the second factor is universally closed when `f` is (Stacks 0513 and 050S). -/
theorem universallyClosed_mapSnd (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS (mapSnd B S hS z f g) :=
  universallyClosed_baseChange_of_isTwoFibreProduct B S hS (mapSndSquare B S hS z f g)
    (isTwoFibreProduct_mapSndSquare B S hS z f g) hf

end MapSnd

section Swap

variable {𝒜 ℬ 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ 𝒵) (b : ℬ ⟶ 𝒵)

/-- The exchange of factors `𝒜 ×_{a, 𝒵, b} ℬ ⟶ ℬ ×_{b, 𝒵, a} 𝒜`, as a 1-morphism of algebraic
stacks: `CategoryTheory.TwoFibreProductOver.swap`, which is strictly over the site. -/
def swapHom : twoFibreProductAlgebraicStack B S hS a b ⟶ twoFibreProductAlgebraicStack B S hS b a :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.swap _ _ _ _ _
      w := rfl })

/-- Exchanging the factors twice is the identity, on the nose. -/
theorem swapHom_comp_swapHom : swapHom B S hS a b ≫ swapHom B S hS b a = 𝟙 _ := rfl

/-- The exchange of factors is universally closed. -/
theorem universallyClosed_swapHom : UniversallyClosed B S hS (swapHom B S hS a b) :=
  universallyClosed_of_comp_eq_id B S hS _ _ (swapHom_comp_swapHom B S hS a b)
    (swapHom_comp_swapHom B S hS b a)

end Swap

section Product

variable {𝒳 𝒴 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **`f × f` factors through the two one-sided products.** The 1-morphism
`𝒳 ×_𝒯 𝒳 ⟶ 𝒴 ×_𝒯 𝒴` applying `f` to both factors is `f` on the second factor, an exchange of
factors, `f` on the (new) second factor, and an exchange back. -/
theorem comparisonCospanRight_eq (f : 𝒳 ⟶ 𝒴) (h : 𝒴 ⟶ 𝒯) :
    comparisonCospanRight B S hS f f h =
      mapSnd B S hS (f ≫ h) f h ≫ swapHom B S hS (f ≫ h) h ≫ mapSnd B S hS h f h ≫
        swapHom B S hS h h := rfl

/-- **`f × f` is universally closed when `f` is.** -/
theorem universallyClosed_comparisonCospanRight (f : 𝒳 ⟶ 𝒴) (h : 𝒴 ⟶ 𝒯)
    (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS (comparisonCospanRight B S hS f f h) := by
  rw [comparisonCospanRight_eq]
  refine universallyClosed_comp B S hS _ _ (universallyClosed_mapSnd B S hS _ f h hf) ?_
  refine universallyClosed_comp B S hS _ _ (universallyClosed_swapHom B S hS _ _) ?_
  exact universallyClosed_comp B S hS _ _ (universallyClosed_mapSnd B S hS _ f h hf)
    (universallyClosed_swapHom B S hS _ _)

/-- **The square of diagonals.** For `f : 𝒳 ⟶ 𝒴` and `h : 𝒴 ⟶ 𝒯`,
`Δ_{f ≫ h} ≫ (f × f) = f ≫ Δ_h` as 1-morphisms `𝒳 ⟶ 𝒴 ×_𝒯 𝒴`. -/
theorem relativeDiagonal_comp_comparisonCospanRight (f : 𝒳 ⟶ 𝒴) (h : 𝒴 ⟶ 𝒯) :
    relativeDiagonalAlgebraicStacks B S hS (f ≫ h) ≫ comparisonCospanRight B S hS f f h =
      f ≫ relativeDiagonalAlgebraicStacks B S hS h := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedCategory.BasedFunctor.ext'
  have hobj : ∀ x : 𝒳.val.val.obj,
      ((TwoFibreProductOver.diagonal (f ≫ h).hom.hom.w) ⋙
        TwoFibreProductOver.mapBothOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p 𝒯.val.val.p
          f.hom.hom.toFunctor f.hom.hom.toFunctor h.hom.hom.toFunctor f.hom.hom.w
          f.hom.hom.w).obj x =
        (f.hom.hom.toFunctor ⋙ TwoFibreProductOver.diagonal h.hom.hom.w).obj x :=
    fun x => TwoFibreProductOver.ext_of_heq_iso
      (Functor.congr_obj f.hom.hom.w x).symm rfl rfl HEq.rfl
  refine CategoryTheory.Functor.ext hobj fun x y φ => ?_
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · show f.hom.hom.toFunctor.map φ =
      (eqToHom (hobj x)).a ≫ f.hom.hom.toFunctor.map φ ≫ (eqToHom (hobj y).symm).a
    rw [TwoFibreProductOver.fibreEqToHom_a (hobj x),
      TwoFibreProductOver.fibreEqToHom_a (hobj y).symm]
    show _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    simp
  · show f.hom.hom.toFunctor.map φ =
      (eqToHom (hobj x)).b ≫ f.hom.hom.toFunctor.map φ ≫ (eqToHom (hobj y).symm).b
    rw [TwoFibreProductOver.fibreEqToHom_b (hobj x),
      TwoFibreProductOver.fibreEqToHom_b (hobj y).symm]
    show _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    simp

end Product

section Descent

variable {𝒳 𝒴 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Universal closedness of a relative diagonal descends along a surjective universally closed
1-morphism.** Let `f : 𝒳 ⟶ 𝒴` be surjective and universally closed and let `h : 𝒴 ⟶ 𝒯`. If the
relative diagonal of `f ≫ h` is universally closed, then so is the relative diagonal of `h`. -/
theorem universallyClosed_relativeDiagonal_of_comp (f : 𝒳 ⟶ 𝒴) (h : 𝒴 ⟶ 𝒯)
    (hf : UniversallyClosed B S hS f) (hsurj : Stack.IsSurjective B S hS f)
    (hfh : UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS (f ≫ h))) :
    UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS h) := by
  refine universallyClosed_of_surjective_comp B S hS f _ ?_ hsurj
  rw [← relativeDiagonal_comp_comparisonCospanRight]
  exact universallyClosed_comp B S hS _ _ hfh
    (universallyClosed_comparisonCospanRight B S hS f h hf)

/-- **The relative diagonal of a separated 1-morphism is universally closed** in the sense of
Stacks 0513. -/
theorem universallyClosed_relativeDiagonalAlgebraicStacks_of_isSeparated (p : 𝒳 ⟶ 𝒴)
    (hp : IsSeparated B S hS p) :
    UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS p) :=
  (Stack.representable_universallyClosed_iff_closedMap_baseChange B S hS
    (relativeDiagonalAlgebraicStacks B S hS p)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS p)).1
      (Stack.universallyClosed_of_isProper B S hS _ hp)

end Descent

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
