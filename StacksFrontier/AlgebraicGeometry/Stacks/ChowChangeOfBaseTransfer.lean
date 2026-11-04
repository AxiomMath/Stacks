module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionAQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone

/-!
# Change of base of separated morphisms of finite type to the base `Spec ℤ`

Construction A of Stacks 04X5 views an algebraic stack over `S` as one over `S'` along
`g : S ⟶ S'`. This file collects what the reduction of Chow's lemma for algebraic stacks
(Stacks 0CQ8) to the base `Spec ℤ` uses of it: quasi-compactness of an algebraic stack is
unchanged, quasi-compactness of a 1-morphism descends along it, local finite type of a 1-morphism
to the stack of an algebraic space passes along it, and the view of the stack of an algebraic
space `Y` is equivalent to the stack of the lower-shriek extension `Λ_g Y`.

Each declaration below is named by its content, so that the reduction can quote it directly:
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_id_algebraicStack` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_isEquivalence_homFunctor` for the
identity 1-morphism and for equivalences;
`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStacks_iff` and
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_changeBaseHomAlgebraicStacks` for
quasi-compactness;
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_changeBaseHomAlgebraicStacks` for
local finite type; and `AlgebraicGeometry.Stack.viewAlgebraicSpaceStackToRelocalized` with
`AlgebraicGeometry.Stack.relocalizedToViewAlgebraicSpaceStack` and
`AlgebraicGeometry.Stack.viewAlgebraicSpaceStackRoundTripIso` for the equivalence with the
lower-shriek extension.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

namespace Stack

/-! ### Equivalences are of finite presentation -/

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity 1-morphism of an algebraic stack is quasi-compact**: the base change of the
identity along a 1-morphism `k : 𝒵 ⟶ 𝒴` is `𝒵` itself, by the 2-fibre product of the identity
cospan. -/
theorem isQuasiCompactMorphism_id_algebraicStack (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsQuasiCompactMorphism B S hS (𝟙 𝒴) := fun _ k h𝒵 =>
  isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_idCospan k))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (𝟙 𝒴)) h𝒵

/-- **An equivalence is a monomorphism** (Stacks 04ZZ): its underlying functor is fully
faithful. -/
theorem isMonomorphism_of_isEquivalence_homFunctor {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (e : 𝒳 ⟶ 𝒴) (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom)) :
    AlgebraicStacks.IsMonomorphism B S hS e :=
  isMonomorphism_of_full_and_faithful B S hS e inferInstance inferInstance

/-- **An equivalence is of finite presentation.** Let `e : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` whose underlying functor is an equivalence. Then `e` is locally of finite
presentation, being the identity precomposed with an equivalence; quasi-compact, since a
quasi-inverse `e'` is surjective and `e' ≫ e ≅ 𝟙` is quasi-compact (Stacks 050X); and
quasi-separated, since it is a monomorphism, being fully faithful (Stacks 04ZZ). -/
theorem isFinitePresentation_of_isEquivalence_homFunctor {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (e : 𝒳 ⟶ 𝒴) (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom)) :
    IsFinitePresentation B S hS e := by
  obtain ⟨F, hF, η, ε, -, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor e.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p e.hom) he
  have hFe : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk F (CatFiberedInGroupoids.homFunctor e.hom) ε.symm
      η).isEquivalence_functor
  let e' : 𝒴 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩)
  have hiso : e' ≫ e ≅ 𝟙 𝒴 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso (F := BasedFunctor.comp ⟨F, hF⟩ e.hom.hom)
        (G := BasedFunctor.id 𝒴.val.val) ε hε))
  have hsurj : IsSurjective B S hS e' := by
    have : F.EssSurj := inferInstance
    exact pointsMap_surjective_of_essSurj B S hS _ _ e'.hom.hom
  exact ⟨isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS e (𝟙 𝒴) he
      (isLocallyOfFinitePresentation_id B S hS 𝒴),
    isQuasiCompactMorphism_of_comp_of_isSurjective B S hS e' (𝟙 𝒴) e hiso hsurj
      (isQuasiCompactMorphism_id_algebraicStack B S hS 𝒴),
    isQuasiSeparated_of_isMonomorphism B S hS e
      (isMonomorphism_of_isEquivalence_homFunctor B S hS e he)⟩

end AlgebraicStacks

/-! ### Construction A -/

section ChangeOfBase

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- An algebraic stack is quasi-compact if a scheme-stack on a compact scheme maps to it by a
1-morphism that is surjective on objects. -/
private theorem isQuasiCompactStack_of_compactSpace_of_isSurjectiveOnObjects
    {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (h : IsSurjectiveOnObjects B S hS (schemeStack.{u, w} B S hS U).val.val.p 𝒳.val.val.p
      a.hom.hom.toFunctor) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  isQuasiCompactStack_of_isSurjective B S hS a
    (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS U hU)
    (pointsMap_surjective_of_isSurjectiveOnObjects B S hS a h)

/-- **Quasi-compactness of an algebraic stack is unchanged by Construction A.** Both directions
go through an affine smooth surjective chart (Stacks 04YC); only its surjectivity is used. An
affine chart `U ⟶ 𝒳` over `S` is, after Construction A and the identification
`AlgebraicGeometry.Stack.factorSliceInverse` of slices, an affine chart of the view of `𝒳` over
`S'`. Conversely an affine chart `U' ⟶ 𝒳` over `S'` is a scheme-valued point of `𝒳` over `S'`,
hence of `𝒳` over a factorization `U' ⟶ S` of its structure morphism
(`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`), and the chart over `S` it defines
becomes the given one after Construction A and `AlgebraicGeometry.Stack.factorSliceFunctor`.
Surjectivity on objects is unchanged by Construction A
(`AlgebraicGeometry.Stack.isSurjectiveOnObjects_changeBaseHom_iff`). -/
theorem isQuasiCompactStack_changeBaseAlgebraicStacks_iff (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsQuasiCompactStack.{u, w} B S' hS'
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).val
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).property ↔
      IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property := by
  constructor
  · intro h
    obtain ⟨U', hU', a', ha'surj, -⟩ :=
      (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S' hS' _).1 h
    have hy : (Over.iteratedSliceBackward U' ⋙ a'.hom.hom.toFunctor) ⋙
        (changeBase B S S' hS hS' g 𝒳.val.val).p = Over.map U'.hom :=
      (Functor.assoc _ _ _).trans ((congrArg (Over.iteratedSliceBackward U' ⋙ ·)
        a'.hom.hom.w).trans (Over.iteratedSliceBackward_forget U'))
    obtain ⟨h₀, hy₀, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒳.val.val U' _ hy
    let U : BigFppfOver B S hS := Over.mk h₀
    let a : schemeStack.{u, w} B S hS U ⟶ 𝒳 :=
      Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
        ⟨Over.iteratedSliceForward U ⋙ (Over.iteratedSliceBackward U' ⋙ a'.hom.hom.toFunctor),
          (Functor.assoc _ _ _).trans ((congrArg (Over.iteratedSliceForward U ⋙ ·) hy₀).trans
            (Over.iteratedSliceForward_comp_map U))⟩)
    have : CompactSpace ((BigFppfOver.toScheme B S' hS').obj U') := inferInstance
    refine isQuasiCompactStack_of_compactSpace_of_isSurjectiveOnObjects B S hS a this ?_
    refine (isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g a.hom).1 ?_
    exact isSurjectiveOnObjects_comp B S' hS' _ _ _
      (factorSliceFunctor B S S' hS hS' g hg).toFunctor a'.hom.hom.toFunctor a'.hom.hom.w
      (isSurjectiveOnObjects_of_isEquivalence B S' hS'
        (Bicategory.InducedBicategory.mkHom (factorSliceFunctor B S S' hS hS' g hg))
        (isEquivalence_factorSliceFunctor B S S' hS hS' g hg))
      (isSurjectiveOnObjects_of_pointsMap_surjective B S' hS' a' ha'surj)
  · intro h
    obtain ⟨U, hU, a, hasurj, -⟩ :=
      (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h
    let a' : schemeStack.{u, w} B S' hS' ((Over.map g).obj U) ⟶
        changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳 :=
      Bicategory.InducedBicategory.mkHom
        (Bicategory.InducedBicategory.mkHom (factorSliceInverse B S S' hS hS' g U) ≫
          changeBaseHom B S S' hS hS' g a.hom)
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
    refine isQuasiCompactStack_of_compactSpace_of_isSurjectiveOnObjects B S' hS' a' this ?_
    exact isSurjectiveOnObjects_comp B S' hS' _ _ _
      (factorSliceInverse B S S' hS hS' g U).toFunctor a.hom.hom.toFunctor
      (changeBaseFunctor B S S' hS hS' g a.hom.hom).w
      (isSurjectiveOnObjects_of_isEquivalence B S' hS'
        (Bicategory.InducedBicategory.mkHom (factorSliceInverse B S S' hS hS' g U))
        (isEquivalence_factorSliceInverse B S S' hS hS' g U))
      ((isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g a.hom).2
        (isSurjectiveOnObjects_of_pointsMap_surjective B S hS a hasurj))

/-- **Quasi-compactness of a 1-morphism of algebraic stacks descends along Construction A.** A
base change of `f : 𝒳 ⟶ 𝒴` by a quasi-compact `𝒵 ⟶ 𝒴` over `S` is, after Construction A, the
base change over `S'` of the view of `f` by the view of `𝒵`, which is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStacks_iff`: the two 2-fibre
products are compared by `CategoryTheory.TwoFibreProductOver.unrelocalizeBase`, an
equivalence. -/
theorem isQuasiCompactMorphism_of_changeBaseHomAlgebraicStacks
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f)) :
    IsQuasiCompactMorphism B S hS f := by
  intro 𝒵 k h𝒵
  have hP := hf _ (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g k)
    ((isQuasiCompactStack_changeBaseAlgebraicStacks_iff B S S' hS hS' g 𝒵).2 h𝒵)
  refine (isQuasiCompactStack_changeBaseAlgebraicStacks_iff B S S' hS hS' g
    (twoFibreProductAlgebraicStack B S hS k f)).1 ?_
  have key := TwoFibreProductOver.unrelocalizeBase_comp_relocalizeBase g
    (F := k.hom.hom.toFunctor) (G := f.hom.hom.toFunctor) k.hom.hom.w f.hom.hom.w
  let c : twoFibreProductAlgebraicStack B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g k)
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) ⟶
      changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (twoFibreProductAlgebraicStack B S hS k f) :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      ⟨TwoFibreProductOver.unrelocalizeBase g k.hom.hom.w f.hom.hom.w, by
        have h2 : TwoFibreProductOver.unrelocalizeBase g k.hom.hom.w f.hom.hom.w ⋙
            (TwoFibreProductOver.relocalizeBase g ⋙
              TwoFibreProductOver.structureFunctor (𝒵.val.val.p ⋙ Over.map g)
                (𝒳.val.val.p ⋙ Over.map g) (𝒴.val.val.p ⋙ Over.map g)
                k.hom.hom.toFunctor f.hom.hom.toFunctor) =
            TwoFibreProductOver.structureFunctor (𝒵.val.val.p ⋙ Over.map g)
                (𝒳.val.val.p ⋙ Over.map g) (𝒴.val.val.p ⋙ Over.map g)
                k.hom.hom.toFunctor f.hom.hom.toFunctor := by
          rw [← Functor.assoc, key, Functor.id_comp]
        exact h2⟩)
  have : c.hom.hom.toFunctor.EssSurj :=
    (TwoFibreProductOver.relocalizeBaseEquivalence g k.hom.hom.w
      f.hom.hom.w).isEquivalence_inverse.essSurj
  exact isQuasiCompactStack_of_essSurj B S' hS' c hP

/-! ### Local finite type and local finite presentation -/

/-- **Relative smoothness is unchanged by Construction A**: representability by algebraic spaces
and the relative property of Stacks 03YK at smoothness both are. -/
theorem isRelativelySmooth_changeBaseHom_of_isRelativelySmooth
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒳 ⟶ 𝒴)
    (ha : IsRelativelySmooth B S hS a) :
    IsRelativelySmooth B S' hS' (changeBaseHom B S S' hS hS' g a) :=
  ⟨(isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g a.hom).2 ha.1,
    (hasRelativeProperty_smooth_changeBaseHom_iff B S S' hS hS' g
      (@AlgebraicGeometry.Smooth.{u}) a ha.1).2 ha.2⟩

/-- **The morphism of representing presheaves of a 1-morphism between categories of elements,
after Construction A**, is the lower-shriek extension `Λ_g` of the original one, the categories
of elements of `Λ_g W` and `Λ_g Y` being identified with Construction A of those of `W` and `Y`
by `CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`. Up to
2-isomorphism the 1-morphism is the associated 1-morphism of its representing map (Stacks 0458),
and for that one the identification commutes on the nose with the induced functors of
categories of elements. -/
theorem representingMap_changeBaseHom_eq_relocalizeMap (W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (q : fibredCategory B S hS W ⟶ fibredCategory B S hS Y) :
    representingMap B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS W))
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS Y))
        ((OverShriek.relocalizePresheafFunctor g).obj W)
        ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g W)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
        (changeBaseHom B S S' hS hS' g q) =
      (OverShriek.relocalizePresheafFunctor g).map
        (representingMap B S hS (fibredCategory B S hS W) (fibredCategory B S hS Y) W Y
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) q) := by
  set m := representingMap B S hS (fibredCategory B S hS W) (fibredCategory B S hS Y) W Y
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) q
  obtain ⟨θ⟩ := nonempty_twoIso_associatedMap_representingMap B S hS W Y q
  have h1 : representingMap B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS W))
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS Y))
        ((OverShriek.relocalizePresheafFunctor g).obj W)
        ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g W)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
        (changeBaseHom B S S' hS hS' g (associatedMap B S hS m).1) =
      representingMap B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS W))
        (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS Y))
        ((OverShriek.relocalizePresheafFunctor g).obj W)
        ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g W)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
        (changeBaseHom B S S' hS hS' g q) := by
    let e := CatFiberedInGroupoids.underlyingIso θ
    refine congrArg (morphismSpaceEquiv B S' hS' _ _ _ _ _ _) (Quotient.sound ?_)
    exact ⟨e, fun x =>
      (Functor.isHomLift_overMap_iff (fibredCategory B S hS Y).val.p g
        (𝟙 ((fibredCategory B S hS W).val.p.obj x)) _
        (BasedFunctor.w_obj (associatedMap B S hS m).1.hom x)
        (BasedFunctor.w_obj q.hom x)).2 (θ.hom.hom.isHomLift' x)⟩
  rw [← h1]
  exact morphismSpaceEquiv_eq_of_comp_eq B S' hS' _ _ _ _ _ _ _ _ rfl

/-- **Local finite type passes along Construction A**, for a 1-morphism to the algebraic stack of
an algebraic space. Let `a : U ⟶ 𝒳` be a smooth chart, surjective on objects. Then `a ≫ f` is
locally of finite type, so its representing map `h : U ⟶ Y` is (Stacks 06FM for represented
source and target); the lower-shriek extension `Λ_g h` is locally of finite type
(`AlgebraicGeometry.Space.isLocallyOfFiniteType_relocalize_iff`) and represents the view of
`a ≫ f` (`AlgebraicGeometry.Stack.representingMap_changeBaseHom_eq_relocalizeMap`), and the view
of `a` is a smooth chart of the view of `𝒳`, surjective on objects. -/
theorem AlgebraicStacks.isLocallyOfFiniteType_changeBaseHomAlgebraicStacks
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    AlgebraicStacks.IsLocallyOfFiniteType B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) := by
  obtain ⟨U, hU, a, ha, hasurj⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒳.property
  let a' : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom a
  have haf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (a' ≫ f) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS a' f
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a'
        (isSmooth_of_isRelativelySmooth B S hS a' ha)) hf
  have hP := prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS
    (𝒳 := fibredCategory B S hS U) (𝒴 := fibredCategory B S hS Y)
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) U Y hU hY
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (a ≫ f.hom)
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (algebraicSpaceStack.{u, w} B S hS U hU).property
      (algebraicSpaceStack.{u, w} B S hS Y hY).property (a' ≫ f).hom).1 haf)
  have hP' := (Space.isLocallyOfFiniteType_relocalize_iff B S hS S' hS' g _).2 hP
  rw [← representingMap_changeBaseHom_eq_relocalizeMap B S S' hS hS' g U Y (a ≫ f.hom)] at hP'
  have hsome := hasPropertyOnSomeSmoothDiagram_of_prop_representingMap B S' hS'
    (𝒳 := changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS U))
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS Y))
    (fun _ _ h => Space.IsLocallyOfFiniteType B S' hS' h) _ _
    (isAlgebraicSpace_viewOver B S S' hS hS' g U hU)
    (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g U)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
    (changeBaseHom B S S' hS hS' g (a ≫ f.hom)) hP'
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S' hS' _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S' hS')
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).property
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
      (algebraicSpaceStack.{u, w} B S hS Y hY)).property _).2 ?_
  exact hasPropertyOnSomeSmoothDiagram_of_comp_surjective B S' hS' _
    (changeBaseHom B S S' hS hS' g a) (changeBaseHom B S S' hS hS' g f.hom)
    (isRelativelySmooth_changeBaseHom_of_isRelativelySmooth B S S' hS hS' g a ha)
    ((isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g a).2 hasurj) hsome

/-! ### The view of the algebraic stack of an algebraic space -/

/-- The comparison of the view over `S'` of the algebraic stack of an algebraic space `Y` over `S`
with the algebraic stack of the lower-shriek extension `Λ_g Y`: the forward functor of
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`. -/
noncomputable def viewAlgebraicSpaceStackToRelocalized (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B S hS Y) :
    changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS Y hY) ⟶
      algebraicSpaceStack.{u, w} B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY) :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).hom.functor
      w := (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).hom.w })

/-- The comparison in the other direction: the backward functor of
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`. -/
noncomputable def relocalizedToViewAlgebraicSpaceStack (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B S hS Y) :
    algebraicSpaceStack.{u, w} B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY) ⟶
      changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS Y hY) :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).inv.functor
      w := (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).inv.w })

/-- The two comparisons compose to the identity of the view of the algebraic stack of `Y`, up to
the unit of `CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`, whose
components are identities. -/
noncomputable def viewAlgebraicSpaceStackRoundTripIso
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y) :
    viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY ≫
        relocalizedToViewAlgebraicSpaceStack.{u, w} B S S' hS hS' g Y hY ≅ 𝟙 _ :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).unitIso.symm
      fun a =>
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y).isHomLift_unitIso_inv_app a))

/-- **Both comparisons are of finite presentation and monomorphisms**, being equivalences. -/
theorem isFinitePresentation_viewAlgebraicSpaceStackComparisons
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y) :
    AlgebraicStacks.IsFinitePresentation B S' hS'
        (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY) ∧
      AlgebraicStacks.IsMonomorphism B S' hS'
        (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY) ∧
      AlgebraicStacks.IsFinitePresentation B S' hS'
        (relocalizedToViewAlgebraicSpaceStack.{u, w} B S S' hS hS' g Y hY) ∧
      AlgebraicStacks.IsMonomorphism B S' hS'
        (relocalizedToViewAlgebraicSpaceStack.{u, w} B S S' hS hS' g Y hY) := by
  have he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY).hom) :=
    StacksRepresentableCFG.EquivalenceOver.isEquivalence_hom_functor
      (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
  have he' : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (relocalizedToViewAlgebraicSpaceStack.{u, w} B S S' hS hS' g Y hY).hom) :=
    StacksRepresentableCFG.EquivalenceOver.isEquivalence_inv_functor
      (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
  exact ⟨AlgebraicStacks.isFinitePresentation_of_isEquivalence_homFunctor B S' hS' _ he,
    AlgebraicStacks.isMonomorphism_of_isEquivalence_homFunctor B S' hS' _ he,
    AlgebraicStacks.isFinitePresentation_of_isEquivalence_homFunctor B S' hS' _ he',
    AlgebraicStacks.isMonomorphism_of_isEquivalence_homFunctor B S' hS' _ he'⟩

end ChangeOfBase

end Stack

end AlgebraicGeometry

end
