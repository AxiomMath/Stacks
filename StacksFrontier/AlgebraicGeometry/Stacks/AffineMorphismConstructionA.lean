module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine 1-morphisms and Construction A

Let `g : S ⟶ S'` be a morphism of schemes of a big fppf site. Construction A of Stacks 04X5 views
a category fibred in groupoids over `(Sch/S)_{fppf}` as one over `(Sch/S')_{fppf}`. This file
shows that a 1-morphism is affine in the sense of Stacks 04XB (and of Stacks 0CHQ) exactly when
its image under Construction A is, and derives from it the absolute form of Stacks 0GQE used by
Stacks 0GRK: a 1-morphism from an affine scheme to an algebraic stack whose absolute diagonal is
affine is affine.

The key point is that affineness of the structural morphism of an algebraic space `F` over a
scheme `T`, read as a morphism of algebraic spaces over a base `S` that `T` lies over, does not
depend on `S`: it says that `F` is represented by a scheme affine over `T`
(`AlgebraicGeometry.Stack.isAffineHom_algebraicSpaceMap_iff`).

## Main results

* `AlgebraicGeometry.Stack.isAffineHom_algebraicSpaceMap_iff`: the base-free description.
* `AlgebraicGeometry.Stack.isAffineHom_changeBaseHom_iff`: Stacks 04XB affineness is unchanged
  by Construction A.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_constructionA_iff`: the same for affine
  1-morphisms of algebraic stacks (Stacks 0CHQ).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_schemeStackMap`: a morphism of the site
  with affine underlying morphism of schemes induces an affine 1-morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_structureMorphism_viewOverIntegers`: an
  affine scheme is affine over `Spec ℤ`, as an algebraic stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers`:
  a 1-morphism from an affine scheme to an algebraic stack with affine absolute diagonal is
  affine (Stacks 0GQE over `Spec ℤ`).

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0GQE](https://stacks.math.columbia.edu/tag/0GQE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

/-! ### Affineness of the structural morphism of an algebraic space, independently of the base -/

section Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affineness of an algebraic space over `T` does not depend on the base.** Let `T` be a scheme
over `S` and `A` an algebraic space over `T`. Its structural morphism, read as a morphism of
algebraic spaces over `S`, is affine exactly when `A` is represented on the big fppf site of `T` by
a scheme affine over `T`. The forward implication is
`AlgebraicGeometry.Stack.exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap`; conversely the
structural morphism is then, up to isomorphism, the morphism of representable presheaves induced
by an affine morphism of schemes. -/
theorem isAffineHom_algebraicSpaceMap_iff (T : BigFppfOver B S hS)
    (A : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hA : IsAlgebraicSpace B T.left.1 T.left.2 A) :
    Space.IsAffineHom B S hS (algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩)).hom ↔
      ∃ Z : BigFppfOver B T.left.1 T.left.2, Nonempty (A ≅ yoneda.obj Z) ∧
        _root_.AlgebraicGeometry.IsAffineHom (B.inclusion.map Z.hom) := by
  constructor
  · intro h
    obtain ⟨_, _, hiA, hPaff⟩ :=
      exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap B S hS T A hA h
    exact ⟨_, hiA, hPaff⟩
  · rintro ⟨Z, ⟨e⟩, hZ⟩
    let E := smallerBasePresheafEquivalence B T.left.1 S T.left.2 hS T.hom
    let P := ((Over.iteratedSliceBackward (Over.mk T.hom)).obj Z).hom
    let i : A ≅ E.inverse.obj (Over.mk (yoneda.map P)) :=
      e ≪≫ (fiberYonedaMapIso B S hS T P).symm
    let j : E.functor.obj A ≅ Over.mk (yoneda.map P) :=
      E.functor.mapIso i ≪≫ E.counitIso.app _
    have hw : j.hom.left ≫ yoneda.map P = (E.functor.obj A).hom := Over.w j.hom
    have hP : Space.IsAffineHom B S hS (yoneda.map P) :=
      Space.isAffineHom_of_presheaf
        ((Space.presheaf_yoneda_map_iff B S hS isAffineHom_isStableUnderBaseChange P).2 hZ)
    have hj : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso j).hom)
    have := Space.isAffineHom_comp B S hS _ _ (Space.isAffineHom_of_isIso j.hom.left) hP
    rwa [hw] at this

end Space

/-! ### Construction A on affine 1-morphisms -/

section ConstructionA

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Affineness in the sense of Stacks 04XB is unchanged by Construction A.** A 1-morphism of
categories fibred in groupoids over the big fppf site of `S` is affine in the sense of Stacks 04XB
exactly when the 1-morphism over the big fppf site of `S'` produced by Construction A is.

The proof is that of `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`: the
scheme-valued points and the 2-fibre products match up exactly as there, so the representing
algebraic space is the same object on both sides, and its structural morphism is affine over `S`
exactly when it is affine over `S'` by
`AlgebraicGeometry.Stack.isAffineHom_algebraicSpaceMap_iff`. -/
theorem isAffineHom_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    Stack.IsAffineHom B S' hS' (changeBaseHom B S S' hS hS' g f) ↔
      Stack.IsAffineHom B S hS f := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    have key := hbig ((Over.map g).obj U) y
      (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
      ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
    exact ((isAffineHom_algebraicSpaceMap_iff B S' hS' ((Over.map g).obj U) F hF).trans
      (isAffineHom_algebraicSpaceMap_iff B S hS U F hF).symm).1 key
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    have key := hsmall (Over.mk h₀) y hy F hF
      ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩
    exact ((isAffineHom_algebraicSpaceMap_iff B S' hS' U' F hF).trans
      (isAffineHom_algebraicSpaceMap_iff B S hS (Over.mk h₀) F hF).symm).2 key

/-- **Stacks 0CHQ is unchanged by Construction A.** A 1-morphism of algebraic stacks over `S` is
affine exactly when its image under the bijection on 1-morphisms of Stacks 04X5 is affine over
`S'`: representability by algebraic spaces is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`, and the
condition of Stacks 04XB is `AlgebraicGeometry.Stack.isAffineHom_changeBaseHom_iff`. -/
theorem AlgebraicStacks.isAffineHom_constructionA_iff {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsAffineHom B S' hS'
        (Bicategory.InducedBicategory.mkHom
          (algebraicStackConstructionHomEquiv.{u, w} B S S' hS hS' g 𝒳 𝒴 f).val :
          (algebraicStackConstructionA B S S' hS hS' g 𝒳).1 ⟶
            (algebraicStackConstructionA B S S' hS hS' g 𝒴).1) ↔
      AlgebraicStacks.IsAffineHom B S hS f :=
  and_congr (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f.hom.hom)
    (isAffineHom_changeBaseHom_iff B S S' hS hS' g f.hom)

end ConstructionA

/-! ### Affine 1-morphisms between represented algebraic stacks -/

section SchemeStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the site with affine underlying morphism of schemes induces an affine
1-morphism of the represented algebraic stacks** (Stacks 0CHQ). Affineness of morphisms of
algebraic spaces is stable under base change and fppf local on the target (**Stacks 041Z**), so
by `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap` it suffices that the
morphism of representable algebraic spaces is affine, which is
`AlgebraicGeometry.Space.isAffineHom_of_presheaf`. -/
theorem AlgebraicStacks.isAffineHom_schemeStackMap {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map φ)) :
    AlgebraicStacks.IsAffineHom B S hS (schemeStackMap.{u, w} B S hS φ) := by
  have _haffBC : (Space.affineMorphismProperty B S hS).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg => Space.isAffineHom_hom_of_isPullback sq hg }
  have _haffLoc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, w} B S hS) :=
    have _hfpqc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fpqc.precoverage.{u, w} B S hS) :=
      Space.isLocalAtTarget_isAffineHom_fpqc.{u, w} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact ⟨isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS φ,
    hasRelativeProperty_schemeFibredCategoryMap.{u, w} B S hS (Space.affineMorphismProperty B S hS)
      φ (Space.isAffineHom_of_presheaf
        ((Space.presheaf_yoneda_map_iff B S hS isAffineHom_isStableUnderBaseChange φ).2 hφ))⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An affine scheme, as an algebraic stack, is affine over `Spec ℤ`.** For an object `U` of the
big fppf site of `S` with affine underlying scheme, the structure morphism of Stacks 050D of the
view of the algebraic stack of `U` over the terminal scheme is affine.

The view of the algebraic stack of `U` over `Spec ℤ` is equivalent, compatibly with the structure
functors, to the algebraic stack over `Spec ℤ` of `U` itself
(`AlgebraicGeometry.Stack.factorSliceInverse`). Every 1-morphism to the stack of the terminal
scheme is the structure morphism (`AlgebraicGeometry.Stack.eq_structureMorphism`), so the square
formed with the 1-morphism induced by `U ⟶ Spec ℤ` commutes strictly; that 1-morphism is affine
since `U` and `Spec ℤ` are affine, and affineness passes along the square by Stacks 0457. -/
theorem AlgebraicStacks.isAffineHom_structureMorphism_viewOverIntegers (U : BigFppfOver B S hS)
    (hU : IsAffineOver B S hS U) :
    AlgebraicStacks.IsAffineHom B (⊤_ Scheme.{u}) hZ
      (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ
        (AlgebraicStacks.viewOverIntegers B S hS hZ (schemeStack.{u, w} B S hS U))) := by
  let g₀ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let U' : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map g₀).obj U
  let φ : U' ⟶ Over.mk (𝟙 (B.obj hZ)) := Over.homMk U'.hom (Category.comp_id _)
  have hφaff : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map φ) :=
    have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U') := hU
    have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (Over.mk (𝟙 (B.obj hZ)))) := inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
    isAffineHom_of_isAffine _
  have hφ := isAffineHom_schemeStackMap.{u, w} B (⊤_ Scheme.{u}) hZ φ hφaff
  let 𝒱 := AlgebraicStacks.viewOverIntegers B S hS hZ (schemeStack.{u, w} B S hS U)
  let a : (schemeFibredCategory B (⊤_ Scheme.{u}) hZ U').val ⥤ᵇ 𝒱.val.val :=
    factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g₀ U
  have ha : Functor.IsEquivalence a.toFunctor :=
    isEquivalence_factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g₀ U
  have hstr : (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp a (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒱).hom.hom)) :
        schemeStack.{u, w} B (⊤_ Scheme.{u}) hZ U' ⟶ _) =
      schemeStackMap.{u, w} B (⊤_ Scheme.{u}) hZ φ :=
    (eq_structureMorphism _ _ _ _ _).trans (eq_structureMorphism _ _ _ _ _).symm
  have hα : BasedFunctor.comp a (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒱).hom.hom =
      BasedFunctor.comp (schemeStackMap.{u, w} B (⊤_ Scheme.{u}) hZ φ).hom.hom
        (BasedFunctor.id _) := by
    rw [← hstr]
    rfl
  have hb : Functor.IsEquivalence (BasedFunctor.id
      (schemeStack.{u, w} B (⊤_ Scheme.{u}) hZ (Over.mk (𝟙 (B.obj hZ)))).val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B (⊤_ Scheme.{u}) hZ
      (schemeStackMap.{u, w} B (⊤_ Scheme.{u}) hZ φ).hom.hom
      (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒱).hom.hom a (BasedFunctor.id _)
      (eqToIso hα)).2 hφ.1,
    relativeProperty_of_equivalences_symm B (⊤_ Scheme.{u}) hZ
      (Space.affineMorphismProperty B (⊤_ Scheme.{u}) hZ)
      (schemeStackMap.{u, w} B (⊤_ Scheme.{u}) hZ φ).hom.hom
      (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒱).hom.hom a (BasedFunctor.id _)
      (eqToIso hα) hφ.2⟩

/-- **Stacks 0GQE over `Spec ℤ`, for a 1-morphism out of an affine scheme.** Let `𝒳` be an
algebraic stack over `S` whose absolute diagonal, the diagonal of its view over the terminal
scheme `Spec ℤ` (Stacks 050D), is affine, and let `U` be an object of the big fppf site of `S`
with affine underlying scheme. Then every 1-morphism `g` from the algebraic stack of `U` to `𝒳` is
affine.

Over `Spec ℤ` the structure morphism of `U` is affine
(`AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_structureMorphism_viewOverIntegers`) and
the relative diagonal of the structure morphism of `𝒳` is its absolute diagonal
(`AlgebraicGeometry.Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism`), so
Stacks 0GQE makes the view of `g` affine over `Spec ℤ`; and affineness descends along
Construction A (`AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_constructionA_iff`). -/
@[ega "II 1.2.3" "more general"]
theorem AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers
    {U : BigFppfOver B S hS} (hU : IsAffineOver B S hS U) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) hZ
      (diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) hZ
        (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳).val))
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    AlgebraicStacks.IsAffineHom B S hS g := by
  let 𝒳' := AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳
  let g' := viewOverIntegersHom B S hS hZ g
  have hrel : Stack.IsAffineHom B (⊤_ Scheme.{u}) hZ
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) hZ
        (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳')).hom :=
    (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B (⊤_ Scheme.{u}) hZ 𝒳'
      (fun _ _ f => Space.IsAffineHom B (⊤_ Scheme.{u}) hZ f.hom)).mp hΔ
  have hg' : AlgebraicStacks.IsAffineHom B (⊤_ Scheme.{u}) hZ g' :=
    isAffineHom_of_comp_of_isAffineHom_relativeDiagonal B (⊤_ Scheme.{u}) hZ g'
      (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ
        (AlgebraicStacks.viewOverIntegers B S hS hZ (schemeStack.{u, w} B S hS U)))
      (structureMorphism.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳')
      (eqToIso (comp_structureMorphism B (⊤_ Scheme.{u}) hZ g').symm)
      (isAffineHom_structureMorphism_viewOverIntegers.{u, w} B S hS hZ U hU) hrel
  exact (isAffineHom_constructionA_iff B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) g).1 hg'

end SchemeStack

end AlgebraicGeometry.Stack

end
