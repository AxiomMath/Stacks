module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesSmallHoms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStackLocallySmall
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The stack of curves over an algebraic space

For an algebraic space `A`, the category `(Sch/A)` of schemes over `A` is an algebraic stack, and
the families of curves over `A` are equivalent, over the big fppf site of `Spec(ℤ)`, to the
2-fibre product of the families of curves with `(Sch/A)` over the final object. Consequently, if
the stack `Curves` is algebraic, then so is the stack `A-Curves` of families of curves over `A`.

## Main results

* `AlgebraicGeometry.isAlgebraicStack_schemesOverSpace`: `(Sch/A)` is an algebraic stack.
* `AlgebraicGeometry.CurveFamilyOver.isEquivalence_toCurvesTwoFibreProduct`: the families of
  curves over `A` are equivalent to the 2-fibre product of the families of curves with `(Sch/A)`.
* `AlgebraicGeometry.curveFamilyOver_isAlgebraicStack_of_isAlgebraicStack`: if `Curves` is an
  algebraic stack, so is `A-Curves` for every algebraic space `A`.

## References

* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0D54](https://stacks.math.columbia.edu/tag/0D54)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

section SchemesOverSpace

variable (S : Scheme.{u}) (hS : B.Contains S) (A : AlgebraicSpaces B S hS)

/-- The category of schemes over the algebraic space `A`, as a category over the big fppf site
of `S`. -/
abbrev schemesOverAlgebraicSpaceBased : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (CostructuredArrow.proj (schemeSpaceFunctor B S hS) A)

/-- The structure morphism of a scheme over the algebraic space `A`, as a morphism of presheaves
out of the represented presheaf. -/
def yonedaHom (Z : SchemesOverSpace B S hS A) : yoneda.obj Z.left ⟶ A.obj := Z.hom.hom

/-- A scheme over the algebraic space `A`, read as an element of `A`: the section of `A`
corresponding to its structure morphism by the Yoneda lemma. -/
def schemesOverSpaceToElements :
    SchemesOverSpace B S hS A ⥤ (Stack.fibredCategory B S hS A.obj).val.obj where
  obj Z := ⟨Z.left, Discrete.mk (yonedaEquiv (yonedaHom B S hS A Z))⟩
  map {Z Z'} m := ⟨m.left, Discrete.eqToHom (by
    change yonedaEquiv (yonedaHom B S hS A Z) =
      A.obj.map m.left.op (yonedaEquiv (yonedaHom B S hS A Z'))
    rw [yonedaEquiv_naturality]
    exact congrArg yonedaEquiv (congrArg (fun q => q.hom) (CostructuredArrow.w m)).symm)⟩
  map_id _ := PresheafOfCategories.elements_hom_ext _ _ rfl
  map_comp _ _ := PresheafOfCategories.elements_hom_ext _ _ rfl

/-- The functor `schemesOverSpaceToElements` commutes with the projections to the big fppf site
of `S`. -/
theorem schemesOverSpaceToElements_comp :
    schemesOverSpaceToElements B S hS A ⋙ (Stack.fibredCategory B S hS A.obj).val.p =
      CostructuredArrow.proj (schemeSpaceFunctor B S hS) A := rfl

/-- The functor `schemesOverSpaceToElements` is faithful. -/
instance : (schemesOverSpaceToElements B S hS A).Faithful where
  map_injective h := CostructuredArrow.hom_ext _ _
    (congrArg (fun q => Pseudofunctor.CoGrothendieck.Hom.base q) h)

/-- The functor `schemesOverSpaceToElements` is full. -/
instance : (schemesOverSpaceToElements B S hS A).Full where
  map_surjective {Z Z'} u := by
    let g : Z.left ⟶ Z'.left := u.base
    have hu : yonedaEquiv (yonedaHom B S hS A Z) =
        A.obj.map g.op (yonedaEquiv (yonedaHom B S hS A Z')) :=
      Discrete.eq_of_hom u.fiber
    refine ⟨CostructuredArrow.homMk g (ObjectProperty.hom_ext _ ?_), ?_⟩
    · apply yonedaEquiv.injective
      change yonedaEquiv (yoneda.map g ≫ yonedaHom B S hS A Z') =
        yonedaEquiv (yonedaHom B S hS A Z)
      rw [hu, yonedaEquiv_naturality]
    · exact PresheafOfCategories.elements_hom_ext _ _ rfl

/-- The functor `schemesOverSpaceToElements` is essentially surjective. -/
instance : (schemesOverSpaceToElements B S hS A).EssSurj where
  mem_essImage W := by
    refine ⟨CostructuredArrow.mk (Y := W.base)
      (ObjectProperty.homMk (yonedaEquiv.symm W.fiber.as) :
        (schemeSpaceFunctor B S hS).obj W.base ⟶ A), ⟨?_⟩⟩
    refine PresheafOfCategories.elementsIsoOfBaseIso (Iso.refl _) ?_
    change yonedaEquiv (yonedaEquiv.symm W.fiber.as) = A.obj.map (𝟙 W.base).op W.fiber.as
    simp

/-- The functor `schemesOverSpaceToElements` is an equivalence of categories. -/
instance : (schemesOverSpaceToElements B S hS A).IsEquivalence where

/-- **The schemes over an algebraic space form an algebraic stack.** The category `(Sch/A)` of
schemes over the algebraic space `A` is equivalent over the big fppf site of `S` to the category
fibred in groupoids of the presheaf `A`, which is an algebraic stack. -/
theorem isAlgebraicStack_schemesOverSpace :
    Stack.IsAlgebraicStack.{u, w} B S hS (schemesOverAlgebraicSpaceBased B S hS A) := by
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) A)
    (Stack.fibredCategory B S hS A.obj).isFiberedInGroupoids
    (schemesOverSpaceToElements B S hS A) (schemesOverSpaceToElements_comp B S hS A)
    inferInstance
  exact Stack.isAlgebraicStack_of_equivalenceOver B S hS e.symm
    (Stack.isAlgebraicStack_fibredCategory B S hS A.obj A.property)

end SchemesOverSpace

namespace CurveFamilyOver

variable (A : AlgebraicSpaces B integerBase hZ)

/-- The 2-fibre product, over the final object of the categories over the big fppf site of
`Spec(ℤ)`, of the families of curves with the schemes over `A`. -/
abbrev curvesTwoFibreProduct :=
  TwoFibreProductOver (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
    (𝟭 (BigFppfOver B integerBase hZ)) (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)

/-- The canonical comparison from families of curves over `A` to the 2-fibre product over the
final object of the families of curves with the schemes over `A`. -/
def toCurvesTwoFibreProduct : CurveFamilyOver B hZ A ⥤ curvesTwoFibreProduct B hZ A :=
  TwoFibreProductOver.lift (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
    (𝟭 (BigFppfOver B integerBase hZ)) (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
    (CostructuredArrow.proj (curveBaseSpace B hZ) A ⋙ curvesProjectionOver B hZ)
    (CostructuredArrow.proj (curveBaseSpace B hZ) A)
    (CostructuredArrow.pre (curvesProjectionOver B hZ) (schemeSpaceFunctor B integerBase hZ) A)
    rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The comparison `toCurvesTwoFibreProduct` commutes with the projections to the big fppf site
of `Spec(ℤ)`. -/
theorem toCurvesTwoFibreProduct_comp_structureFunctor :
    toCurvesTwoFibreProduct B hZ A ⋙ TwoFibreProductOver.structureFunctor
        (curvesProjectionOver B hZ)
        (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
        (𝟭 (BigFppfOver B integerBase hZ)) (curvesProjectionOver B hZ)
        (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A) =
      CostructuredArrow.proj (curveBaseSpace B hZ) A ⋙ curvesProjectionOver B hZ := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The comparison `toCurvesTwoFibreProduct` is an equivalence. -/
theorem isEquivalence_toCurvesTwoFibreProduct :
    (toCurvesTwoFibreProduct B hZ A).IsEquivalence := by
  have hfaithful : (toCurvesTwoFibreProduct B hZ A).Faithful :=
    ⟨fun h => CostructuredArrow.hom_ext _ _ (congrArg TwoFibreProductOver.Hom.a h)⟩
  have hfull : (toCurvesTwoFibreProduct B hZ A).Full := by
    constructor
    intro X Y m
    have hbase : CurveFamily.Hom.baseMap m.a = m.b.left := by
      have hw := m.w
      change CurveFamily.Hom.baseMap m.a ≫ 𝟙 _ = 𝟙 _ ≫ m.b.left at hw
      simpa only [Category.comp_id, Category.id_comp] using hw
    have hspace : (curveBaseSpace B hZ).map m.a =
        (schemeSpaceFunctor B integerBase hZ).map m.b.left :=
      congrArg (schemeSpaceFunctor B integerBase hZ).map hbase
    refine ⟨{ left := m.a, right := 𝟙 X.right, w := ?_ }, ?_⟩
    · change (curveBaseSpace B hZ).map m.a ≫ Y.hom = X.hom
      rw [hspace]
      exact m.b.w
    · apply TwoFibreProductOver.Hom.ext'
      · rfl
      · exact CostructuredArrow.hom_ext _ _ hbase
  have hessSurj : (toCurvesTwoFibreProduct B hZ A).EssSurj := by
    constructor
    intro P
    have hbase : P.x.base = P.y.left := P.hx.trans P.hy.symm
    have hspace := congrArg (schemeSpaceFunctor B integerBase hZ).obj hbase
    let Z : CurveFamilyOver B hZ A := CostructuredArrow.mk (eqToHom hspace ≫ P.y.hom)
    have hmap : (schemeSpaceFunctor B integerBase hZ).map (eqToHom hbase) = eqToHom hspace := by
      simp [eqToHom_map]
    let bIso : ((toCurvesTwoFibreProduct B hZ A).obj Z).y ≅ P.y :=
      CostructuredArrow.isoMk (eqToIso hbase) (by
        change (schemeSpaceFunctor B integerBase hZ).map (eqToHom hbase) ≫ P.y.hom =
          eqToHom hspace ≫ P.y.hom
        rw [hmap])
    have hbmap : (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A).map bIso.hom =
        eqToHom hbase := rfl
    have hvertical : P.iso.hom = eqToHom P.hx ≫ eqToHom P.hy.symm := by
      have := P.vertical
      simpa using IsHomLift.fac' (𝟭 (BigFppfOver B integerBase hZ)) (𝟙 P.base) P.iso.hom
    have hbaseMap :
        eqToHom ((toCurvesTwoFibreProduct B hZ A).obj Z).hy.symm ≫
            (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A).map bIso.hom ≫
              eqToHom P.hy =
          eqToHom ((toCurvesTwoFibreProduct B hZ A).obj Z).hx.symm ≫
            (curvesProjectionOver B hZ).map (𝟙 P.x) ≫ eqToHom P.hx := by
      change (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A).map bIso.hom ≫
        eqToHom P.hy = eqToHom P.hx
      rw [hbmap]
      exact eqToHom_trans _ _
    have hw : (curvesProjectionOver B hZ).map (𝟙 P.x) ≫ P.iso.hom =
        ((toCurvesTwoFibreProduct B hZ A).obj Z).iso.hom ≫
          (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A).map bIso.hom := by
      change P.iso.hom =
        (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A).map bIso.hom
      rw [hvertical, hbmap]
      exact eqToHom_trans _ _
    let f : (toCurvesTwoFibreProduct B hZ A).obj Z ⟶ P :=
      TwoFibreProductOver.Hom.mk' (𝟙 P.x) bIso.hom hbaseMap hw
    have : IsIso f := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ f
      (inferInstanceAs (IsIso (𝟙 P.x))) (inferInstanceAs (IsIso bIso.hom))
    exact ⟨Z, ⟨asIso f⟩⟩
  exact { }

end CurveFamilyOver

open CurveFamilyOver

/-- The category of families of curves over the algebraic space `A`, as a category over the big
fppf site of `Spec(ℤ)`. -/
abbrev curveFamilyOverBased (A : AlgebraicSpaces B integerBase hZ) :
    BasedCategory (BigFppfOver B integerBase hZ) :=
  BasedCategory.ofFunctor
    (CostructuredArrow.proj (curveBaseSpace B hZ) A ⋙ curvesProjectionOver B hZ)

/-- If the stack `Curves` is an algebraic stack, then for every algebraic space `A` the stack
`A-Curves` of families of curves over `A` is an algebraic stack. -/
theorem curveFamilyOver_isAlgebraicStack_of_isAlgebraicStack
    (A : AlgebraicSpaces B integerBase hZ)
    (hcurves : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curveFamilyOverBased B hZ A) := by
  obtain ⟨hTfib, hTst, hTdiag, -⟩ := Stack.isAlgebraicStack_terminal.{u, w} B integerBase hZ
  have : LocallySmall.{u} (curvesFiberedCategory B hZ).val.obj := locallySmall_curveFamily B hZ
  have h₀ := Stack.isAlgebraicStack_twoFibreProduct_of_locallySmall.{u, w} B integerBase hZ
    (curvesFiberedCategory B hZ).val (schemesOverAlgebraicSpaceBased B integerBase hZ A)
    (BasedCategory.ofFunctor (𝟭 (BigFppfOver B integerBase hZ)))
    ⟨curvesProjectionOver B hZ, rfl⟩
    ⟨CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A, rfl⟩
    hTst hTdiag hcurves (isAlgebraicStack_schemesOverSpace.{u, w} B integerBase hZ A)
  have h₁ : (CostructuredArrow.proj (curveBaseSpace B hZ) A ⋙
      curvesProjectionOver B hZ).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.costructuredArrow_proj _ A)
      (curvesFiberedCategory B hZ).property
  have h₂ := TwoFibreProductOver.isFiberedInGroupoids (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
    (𝟭 (BigFppfOver B integerBase hZ)) (curvesProjectionOver B hZ)
    (CostructuredArrow.proj (schemeSpaceFunctor B integerBase hZ) A)
    (curvesFiberedCategory B hZ).property
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj _ A) hTfib rfl rfl
  have := isEquivalence_toCurvesTwoFibreProduct B hZ A
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (toCurvesTwoFibreProduct B hZ A) (toCurvesTwoFibreProduct_comp_structureFunctor B hZ A)
    inferInstance
  exact Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ e.symm h₀

end AlgebraicGeometry

end
