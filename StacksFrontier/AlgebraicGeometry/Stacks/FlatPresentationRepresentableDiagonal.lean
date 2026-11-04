module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SetoidRepresentabilityModel
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.TwoFibreProductSetoid
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidToSets

/-!
# The diagonal of a stack with a flat presentation is representable

Let `u : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, with `𝒳` a stack, `𝒰` representable by an algebraic space and `u` representable by
algebraic spaces, surjective, flat and locally of finite presentation. Then the diagonal of `𝒳`
is representable by algebraic spaces.

## Main definitions

* `CategoryTheory.Functor.isoClassPresheafModelMap`: the map of `Type w` models of the
  presheaves of isomorphism classes induced by a functor over the base.
* `AlgebraicGeometry.Stack.Bootstrap04S6Spaces`: the assertion that a sheaf receiving a
  surjective, flat, locally finitely presented morphism representable by algebraic spaces from an
  algebraic space is an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_isoClassPresheafModel`: the `Type u` model of the presheaf
  of isomorphism classes of a stack in setoids is a sheaf.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_flatPresentation`: a stack in groupoids
  admitting such a 1-morphism `u` has diagonal representable by algebraic spaces.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04TC](https://stacks.math.columbia.edu/tag/04TC)
* [Stacks Project, Tag 05UJ](https://stacks.math.columbia.edu/tag/05UJ)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe w v₁ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮]
  [Category.{v₁} 𝒯]

/-- The map of `Type w` models of the presheaves of isomorphism classes induced by a functor
`G` over `𝒞` between two categories fibred in setoids: on classes it is `[x] ↦ [G x]`. -/
noncomputable def isoClassPresheafModelMap (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞)
    [p.IsFibered] [q.IsFibered] [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]
    [FunctorToTypes.Small.{w} p.isoClassPresheaf]
    [FunctorToTypes.Small.{w} q.isoClassPresheaf]
    {G : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) :
    isoClassPresheafModel.{w} p ⟶ isoClassPresheafModel.{w} q where
  app U := ↾fun z => isoClassPresheafModelEquiv.{w} q U
    ((isoClassMapOfCompEq hG : p.isoClassPresheaf ⟶ q.isoClassPresheaf).app U
      ((isoClassPresheafModelEquiv.{w} p U).symm z))
  naturality U V f := by
    ext z
    have h₁ : (isoClassPresheafModelEquiv.{w} p V).symm
        ((isoClassPresheafModel.{w} p).map f z)
        = p.isoClassPresheaf.map f ((isoClassPresheafModelEquiv.{w} p U).symm z) := by
      rw [Equiv.symm_apply_eq, isoClassPresheafModelEquiv_naturality.{w} p f,
        Equiv.apply_symm_apply]
    change isoClassPresheafModelEquiv.{w} q V
        ((isoClassMapOfCompEq hG : p.isoClassPresheaf ⟶ q.isoClassPresheaf).app V
          ((isoClassPresheafModelEquiv.{w} p V).symm ((isoClassPresheafModel.{w} p).map f z)))
      = (isoClassPresheafModel.{w} q).map f
          (isoClassPresheafModelEquiv.{w} q U
            ((isoClassMapOfCompEq hG : p.isoClassPresheaf ⟶ q.isoClassPresheaf).app U
              ((isoClassPresheafModelEquiv.{w} p U).symm z)))
    rw [h₁, ← isoClassPresheafModelEquiv_naturality.{w} q f,
      NatTrans.naturality_apply
        (isoClassMapOfCompEq hG : p.isoClassPresheaf ⟶ q.isoClassPresheaf) f]

/-- `CategoryTheory.Functor.isoClassPresheafModelMap` sends the model of the class of `x` to
the model of the class of the image of `x` under the induced functor of fibres. -/
theorem isoClassPresheafModelMap_app_isoClassMk (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞)
    [p.IsFibered] [q.IsFibered] [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]
    [FunctorToTypes.Small.{w} p.isoClassPresheaf]
    [FunctorToTypes.Small.{w} q.isoClassPresheaf]
    {G : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) {U : 𝒞} (x : p.Fiber U) :
    (isoClassPresheafModelMap.{w} p q hG).app (op U)
        (isoClassPresheafModelEquiv.{w} p (op U) (isoClassMk p x))
      = isoClassPresheafModelEquiv.{w} q (op U)
        (isoClassMk q ((Fiber.mapOfComp p q G hG U).obj x)) := by
  have h : (isoClassPresheafModelMap.{w} p q hG).app (op U)
      (isoClassPresheafModelEquiv.{w} p (op U) (isoClassMk p x))
      = isoClassPresheafModelEquiv.{w} q (op U)
        ((isoClassMapOfCompEq hG : p.isoClassPresheaf ⟶ q.isoClassPresheaf).app (op U)
          (isoClassMk p x)) := by
    simp [isoClassPresheafModelMap]
  rw [h, isoClassMap_app_isoClassMk]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `Type u` model of the presheaf of isomorphism classes of a stack in setoids over the big
fppf site of `S` is a sheaf. -/
theorem isSheaf_isoClassPresheafModel {D : Type (u + 1)} [Category.{u} D]
    (p : D ⥤ BigFppfOver B S hS) [p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} p.isoClassPresheaf]
    (h : p.IsStackInSetoids (BigFppfOver.topology B S hS)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} p) := by
  have : (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} p).p.IsFiberedInSetoids :=
    inferInstanceAs p.IsFiberedInSetoids
  have : (presheafOfCategories
      (CategoryTheory.Functor.isoClassPresheafModel.{u} p ⋙ typeToCat)).p.IsFiberedInSets :=
    PresheafOfCategories.isFiberedInSets_discreteProjection _
  have h' := (BasedCategory.isStackInSetoids_iff_isSheaf_objPresheaf_of_equivalence
      (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
        (𝒴 := presheafOfCategories
          (CategoryTheory.Functor.isoClassPresheafModel.{u} p ⋙ typeToCat))
        (𝒳 := BasedCategory.ofFunctor p) (isoClassEquivalenceOverModel B S hS p))
      (BigFppfOver.topology B S hS)).1 h
  rwa [Presheaf.isSheaf_of_iso_iff
      (PresheafOfCategories.objPresheafIso
        (CategoryTheory.Functor.isoClassPresheafModel.{u} p)),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type] at h'

/-- Over the big fppf site of `S`, a sheaf which receives a morphism from an algebraic space that
is representable by algebraic spaces, surjective, flat and locally of finite presentation is an
algebraic space. -/
abbrev Bootstrap04S6Spaces : Prop :=
  ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ F),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F →
    IsAlgebraicSpace B S hS G →
    ∀ hg : Space.IsRepresentableByAlgebraicSpaces B S hS g,
      Space.HasProperty B S hS
          (Space.surjectiveMorphismProperty B S hS) g hg →
        Space.HasProperty B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom) g hg →
        Space.HasProperty B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
            Space.IsLocallyOfFinitePresentation B S hS k.hom) g hg →
        IsAlgebraicSpace B S hS F

variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- Let `u : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the
big fppf site of `S` with `𝒳` a stack, `𝒰` representable by an algebraic space and `u`
representable by algebraic spaces, surjective, flat and locally of finite presentation. Then
the diagonal of `𝒳` is representable by algebraic spaces. -/
@[stacks 05XW]
theorem hasRepresentableDiagonal_of_flatPresentation (u : 𝒰 ⟶ 𝒳)
    (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (hsurj : HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) u hu)
    (hflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS)
      ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
      𝒰 𝒳 u hu)
    (hlfp : HasRelativeProperty B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) u hu) :
    HasRepresentableDiagonal B S hS 𝒳 := by
  have h04S6 : Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS :=
    Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS
      (Space.bootstrap04S6QuotientSheaf B S hS)
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  refine hasRepresentableDiagonal_of_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳 ?_
  intro U V x y
  let 𝒯₁ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS U
  let 𝒯₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS V
  let x' : 𝒯₁ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom x
  let y' : 𝒯₂ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom y
  have h𝒯₁ : IsRepresentableByAlgebraicSpace B S hS 𝒯₁ :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have h𝒯₂ : IsRepresentableByAlgebraicSpace B S hS 𝒯₂ :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V
  have hℛ : IsRepresentableByAlgebraicSpace B S hS
      (schemePointProductBaseChangeSquare B S hS u x' y').pt :=
    isRepresentableByAlgebraicSpace_schemePointProductBaseChangeSquare_pt B S hS u x' y'
      hu h𝒰 h𝒯₁ h𝒯₂
  have hq : IsRepresentableByAlgebraicSpaces B S hS
      (schemePointProductBaseChangeSquare B S hS u x' y').fst.hom :=
    isRepresentableByAlgebraicSpaces_schemePointProductBaseChange B S hS u x' y' hu
  obtain ⟨hRset, hRiso⟩ := (isRepresentableByAlgebraicSpace_iff B S hS
    (schemePointProductBaseChangeSquare B S hS u x' y').pt).1 hℛ
  have hPstack : (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.IsStackInSetoids
      (BigFppfOver.topology B S hS) :=
    Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids
      (BigFppfOver.topology B S hS)
      (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒯₁ h𝒯₁)
      (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒯₂ h𝒯₂) h𝒳
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.isFiberedInGroupoids x.w)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.isFiberedInGroupoids y.w)
  have hPset : (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.IsFiberedInSetoids :=
    ⟨(twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).isFiberedInGroupoids, hPstack.fiber_isThin⟩
  have : (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.IsFibered :=
    (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u}
      (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.isoClassPresheaf :=
    small_isoClassPresheaf_twoFibreProduct_schemePoints B S hS U V x y
  have : (schemePointProductBaseChangeSquare B S hS u x' y').pt.val.p.IsFibered :=
    (schemePointProductBaseChangeSquare B S hS u x' y').pt.isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u}
      (schemePointProductBaseChangeSquare B S hS u x' y').pt.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf B S hS _ hRiso
  have hRmodel : IsAlgebraicSpace B S hS (CategoryTheory.Functor.isoClassPresheafModel.{u}
      (schemePointProductBaseChangeSquare B S hS u x' y').pt.val.p) :=
    (isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel B S hS _).1 hRiso
  have hPsheaf := isSheaf_isoClassPresheafModel B S hS
    (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p hPstack
  let Pset : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val hPset
  let Rset : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk
      (schemePointProductBaseChangeSquare B S hS u x' y').pt.val hRset
  let qset : Rset ⟶ Pset := Bicategory.InducedBicategory.mkHom
    (schemePointProductBaseChangeSquare B S hS u x' y').fst.hom
  let a := CategoryTheory.Functor.isoClassPresheafModelMap.{u} Rset.val.p Pset.val.p
    (CatFiberedInGroupoids.homFunctor_comp_p qset)
  have ha : IsoClassCompatible B S hS qset
      (CategoryTheory.Functor.isoClassPresheafModel.{u} Rset.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} Pset.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} Rset.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} Pset.val.p) a := fun W z =>
    CategoryTheory.Functor.isoClassPresheafModelMap_app_isoClassMk.{u} Rset.val.p Pset.val.p _ z
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map qset).hom := hq
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff_model.{u, u, u + 1}
    B S hS qset a ha).2 hqrep
  have key : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)],
      HasRelativeProperty B S hS P u hu → Space.HasProperty B S hS P a harep :=
    fun P _ _ hP =>
      (isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS qset P a ha
        hqrep).2 (hasRelativeProperty_schemePointProductBaseChange B S hS P u x' y' hu hP)
  refine (isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel B S hS
    (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y)).2 ⟨hPset, ?_⟩
  exact h04S6 a hPsheaf hRmodel harep (key _ hsurj) (key _ hflat) (key _ hlfp)

end AlgebraicGeometry.Stack

end
