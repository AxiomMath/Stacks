module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# The category `𝒮_Y` of test schemes over an algebraic space as a category of elements

For an algebraic space `Y` over `S`, `AlgebraicGeometry.Space.baseBasedCategory Y` is the category
`𝒮_Y` of pairs `(T, g)` of a scheme `T` of the site and a morphism `g : T ⟶ Y`, in the form the
base-change squares of Stacks 08LP and Remark 0DLI use. `AlgebraicGeometry.Stack.fibredCategory`
is the category of elements of the presheaf `Y`, in the form Stacks 0458 and 045A use. The
Yoneda lemma identifies the two over the big fppf site of `S`.

That identification carries Stacks 045A over to `𝒮_Y`. For a morphism `g : T ⟶ Y` from a scheme,
the 1-morphism `𝒮_T ⟶ 𝒮_Y` of `AlgebraicGeometry.Space.baseBasedMap` is representable by
algebraic spaces and has every property, stable under base change, that `g` has. For an étale
atlas of `Y` it is therefore surjective and étale.

## Main definitions

* `AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver`: `𝒮_Y` is equivalent over the site
  to the category of elements of `Y`.
* `AlgebraicGeometry.Space.baseFibredCategory`: `𝒮_Y` as a category fibred in groupoids.
* `AlgebraicGeometry.Space.baseFibredMap`: the 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` of categories fibred in
  groupoids attached to `g : Y' ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.baseBasedCategory_isFiberedInGroupoids`: `𝒮_Y` is fibred in groupoids.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_baseBasedMap_schemeSpace`: for `g`
  out of a scheme, `𝒮_T ⟶ 𝒮_Y` is representable by algebraic spaces.
* `AlgebraicGeometry.Space.prop_baseBasedMap_schemeSpace`: it has every property of morphisms of
  algebraic spaces, stable under base change, which `g` has, in the sense of Stacks 03YK.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Elements

variable (Y : AlgebraicSpaces B S hS)

/-- The element of `Y(T)` that a test scheme `(T, g)` over `Y` names by the Yoneda lemma. -/
abbrev schemesOverElement (A : SchemesOver Y) : Y.obj.obj (Opposite.op A.left) :=
  yonedaEquiv (A.hom.hom : yoneda.obj A.left ⟶ Y.obj)

/-- The elements named by two test schemes over `Y` related by a morphism of test schemes are
related by restriction along the underlying morphism of schemes. -/
theorem schemesOverElement_eq_map {A A' : SchemesOver Y} (h : A ⟶ A') :
    schemesOverElement Y A = Y.obj.map h.left.op (schemesOverElement Y A') := by
  have h₁ : (A.hom.hom : yoneda.obj A.left ⟶ Y.obj) =
      yoneda.map h.left ≫ (A'.hom.hom : yoneda.obj A'.left ⟶ Y.obj) :=
    congrArg (fun k : (schemeSpaceFunctor B S hS).obj A.left ⟶ Y => k.hom)
      (CostructuredArrow.w h).symm
  exact (congrArg yonedaEquiv h₁).trans (yonedaEquiv_naturality _ _).symm

/-- The test scheme `(T, g)` over `Y` whose morphism `g` is the one an element of `Y(T)` names by
the Yoneda lemma. -/
abbrev elementSchemesOver (T : BigFppfOver B S hS) (x : Y.obj.obj (Opposite.op T)) :
    SchemesOver Y :=
  CostructuredArrow.mk (S := schemeSpaceFunctor B S hS) (T := Y) (Y := T)
    (ObjectProperty.homMk (yonedaEquiv.symm x : yoneda.obj T ⟶ Y.obj) :
      (schemeSpaceFunctor B S hS).obj T ⟶ Y)

/-- A morphism of schemes along which one element of `Y` restricts to another is a morphism of
the test schemes over `Y` they name. -/
def elementSchemesOverHom {T T' : BigFppfOver B S hS} (b : T ⟶ T')
    {x : Y.obj.obj (Opposite.op T)} {x' : Y.obj.obj (Opposite.op T')}
    (hx : x = Y.obj.map b.op x') : elementSchemesOver Y T x ⟶ elementSchemesOver Y T' x' :=
  CostructuredArrow.homMk b (by
    apply ObjectProperty.hom_ext
    change yoneda.map b ≫ yonedaEquiv.symm x' = yonedaEquiv.symm x
    rw [hx, yonedaEquiv_symm_map, Quiver.Hom.unop_op])

/-- A test scheme over `Y` is recovered from the element of `Y` it names. -/
theorem schemeSpaceMap_id_comp_elementSchemesOver_hom (A : SchemesOver Y) :
    (schemeSpaceFunctor B S hS).map (𝟙 A.left) ≫
        (elementSchemesOver Y A.left (schemesOverElement Y A)).hom = A.hom := by
  apply ObjectProperty.hom_ext
  show yoneda.map (𝟙 A.left) ≫
      yonedaEquiv.symm (yonedaEquiv (A.hom.hom : yoneda.obj A.left ⟶ Y.obj)) =
    (A.hom.hom : yoneda.obj A.left ⟶ Y.obj)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Equiv.symm_apply_apply _ _

/-- A test scheme `(T, g)` over `Y`, read as the element of `Y(T)` that `g` names by the Yoneda
lemma. -/
def baseObjectsToElements :
    BaseObjects Y ⥤ (presheafOfCategories (Y.obj ⋙ typeToCat)).obj where
  obj A := ⟨A.objDown.left, Discrete.mk (schemesOverElement Y A.objDown)⟩
  map h := ⟨h.down.left, Discrete.eqToHom (schemesOverElement_eq_map Y h.down)⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- An element of `Y(T)`, read as the test scheme `(T, g)` over `Y` with `g` the morphism it names
by the Yoneda lemma. -/
def elementsToBaseObjects :
    (presheafOfCategories (Y.obj ⋙ typeToCat)).obj ⥤ BaseObjects Y where
  obj Z := ULiftHom.objUp (elementSchemesOver Y Z.base Z.fiber.as)
  map u := ULift.up (elementSchemesOverHom Y u.base (Discrete.eq_of_hom u.fiber))
  map_id _ := ULift.ext (CostructuredArrow.hom_ext _ _ rfl)
  map_comp _ _ := ULift.ext (CostructuredArrow.hom_ext _ _ rfl)

/-- An isomorphism of test schemes over `Y`, read in `𝒮_Y`, whose hom-sets are raised. -/
def baseObjectsIsoUp {A A' : SchemesOver Y} (e : A ≅ A') :
    (ULiftHom.objUp A : BaseObjects Y) ≅ ULiftHom.objUp A' where
  hom := ULift.up e.hom
  inv := ULift.up e.inv
  hom_inv_id := ULift.ext e.hom_inv_id
  inv_hom_id := ULift.ext e.inv_hom_id

/-- **`𝒮_Y` is the category of elements of `Y`, over the site.** The Yoneda lemma, as an
equivalence over the big fppf site of `S` between `AlgebraicGeometry.Space.baseBasedCategory` and
the category of elements of the presheaf `Y`. -/
def baseBasedElementsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (baseBasedCategory Y).p
      (presheafOfCategories (Y.obj ⋙ typeToCat)).p where
  hom := ⟨baseObjectsToElements Y, rfl⟩
  inv := ⟨elementsToBaseObjects Y, rfl⟩
  unitIso := NatIso.ofComponents
    (fun A => baseObjectsIsoUp Y (A := ULiftHom.objDown.{u + 1, u + 1} A)
      (CostructuredArrow.isoMk (Iso.refl _)
        (schemeSpaceMap_id_comp_elementSchemesOver_hom Y (ULiftHom.objDown.{u + 1, u + 1} A))))
    (fun {A A'} h => by
      apply ULift.ext
      apply CostructuredArrow.hom_ext
      change h.down.left ≫ 𝟙 _ = 𝟙 _ ≫ h.down.left
      simp)
  counitIso := NatIso.ofComponents
    (fun Z => elementsIsoOfBaseIso (Z := (baseObjectsToElements Y).obj
        ((elementsToBaseObjects Y).obj Z)) (W := Z) (Iso.refl Z.base) (by
      change yonedaEquiv (yonedaEquiv.symm Z.fiber.as) = Y.obj.map (𝟙 _) Z.fiber.as
      rw [Equiv.apply_symm_apply, Functor.map_id_apply]))
    (fun {Z W} u => elements_hom_ext _ _ (by
      change u.base ≫ 𝟙 _ = 𝟙 _ ≫ u.base
      simp))
  unit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    exact fun _ => IsHomLift.of_fac' _ _ _ rfl rfl
      (by simp only [eqToHom_refl, Category.id_comp]; rfl)
  counit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    exact fun _ => IsHomLift.of_fac' _ _ _ rfl rfl
      (by simp only [eqToHom_refl, Category.id_comp]; rfl)

/-- `𝒮_Y` is fibred in groupoids over the big fppf site of `S`: it is equivalent over the site to
the category of elements of `Y`. -/
theorem baseBasedCategory_isFiberedInGroupoids :
    (baseBasedCategory Y).p.IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (baseBasedElementsEquivalenceOver Y)
    (Stack.fibredCategory B S hS Y.obj).isFiberedInGroupoids

/-- `𝒮_Y` as a category fibred in groupoids over the big fppf site of `S`. -/
abbrev baseFibredCategory : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (baseBasedCategory Y) (baseBasedCategory_isFiberedInGroupoids Y)

/-- The 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` of categories fibred in groupoids attached to a morphism of
algebraic spaces. -/
abbrev baseFibredMap {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    baseFibredCategory Y' ⟶ baseFibredCategory Y :=
  Bicategory.InducedBicategory.mkHom (baseBasedMap g)

end Elements

section SchemePoint

variable {Y : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
  (g : (schemeSpaceFunctor B S hS).obj T ⟶ Y)

/-- `𝒮_T`, for a scheme `T` of the site, read as the slice of the site over `T`: the composite of
the Yoneda identification of `AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver` with the
identification of the elements of the presheaf represented by `T` with the slice over `T`. -/
abbrev baseToSlice :
    (baseBasedCategory ((schemeSpaceFunctor B S hS).obj T)) ⥤ᵇ
      (Stack.schemeFibredCategory B S hS T).val :=
  BasedFunctor.comp
    ⟨(baseBasedElementsEquivalenceOver ((schemeSpaceFunctor B S hS).obj T)).hom.functor,
      (baseBasedElementsEquivalenceOver ((schemeSpaceFunctor B S hS).obj T)).hom.w⟩
    ⟨(sliceElementsEquivalenceOver T).inv.functor, (sliceElementsEquivalenceOver T).inv.w⟩

/-- The identification of `𝒮_T` with the slice over `T` is an equivalence. -/
instance baseToSlice_isEquivalence : (baseToSlice (T := T)).toFunctor.IsEquivalence := by
  have := (baseBasedElementsEquivalenceOver
    ((schemeSpaceFunctor B S hS).obj T)).isEquivalence_hom_functor
  have := (sliceElementsEquivalenceOver T).isEquivalence_inv_functor
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ ‹_› ‹_›

/-- The Yoneda identification of `𝒮_Y` with the category of elements of `Y`, as a 1-morphism. -/
abbrev baseToElements (Y : AlgebraicSpaces B S hS) :
    (baseBasedCategory Y) ⥤ᵇ (Stack.fibredCategory B S hS Y.obj).val :=
  ⟨(baseBasedElementsEquivalenceOver Y).hom.functor, (baseBasedElementsEquivalenceOver Y).hom.w⟩

/-- The Yoneda identification of `𝒮_Y` with the category of elements of `Y` is an equivalence. -/
instance baseToElements_isEquivalence (Y : AlgebraicSpaces B S hS) :
    (baseToElements Y).toFunctor.IsEquivalence :=
  (baseBasedElementsEquivalenceOver Y).isEquivalence_hom_functor

/-- The square comparing `𝒮_T ⟶ 𝒮_Y` with the 1-morphism `(Sch/T)_fppf ⟶ 𝒮_Y` of Stacks 045A
commutes on the nose. -/
def baseBasedMapSquare :
    BasedFunctor.comp baseToSlice (Stack.presentationBasedFunctor B S hS T g.hom) ≅
      BasedFunctor.comp (baseBasedMap g) (baseToElements Y) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun A => Iso.refl ((BasedFunctor.comp baseToSlice
        (Stack.presentationBasedFunctor B S hS T g.hom)).toFunctor.obj A))
      (fun _ => elements_hom_ext _ _ (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        simp only [Category.comp_id]
        rfl)))
    (fun _ => IsHomLift.id rfl)

/-- **The 1-morphism `𝒮_T ⟶ 𝒮_Y` attached to a morphism from a scheme is representable by
algebraic spaces.** -/
theorem isRepresentableByAlgebraicSpaces_baseBasedMap_schemeSpace :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (baseBasedMap g) :=
  (Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (𝒳' := baseFibredCategory ((schemeSpaceFunctor B S hS).obj T))
    (𝒴' := baseFibredCategory Y)
    (𝒳 := Stack.schemeFibredCategory B S hS T) (𝒴 := Stack.fibredCategory B S hS Y.obj)
    (baseBasedMap g) (Stack.presentationBasedFunctor B S hS T g.hom) baseToSlice
    (baseToElements Y) (baseBasedMapSquare g)).mp
    (Stack.isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS _
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Y.obj Y.2) T _)

/-- **The 1-morphism `𝒮_T ⟶ 𝒮_Y` has every property of `g`.** Let `P` be a property of morphisms
of algebraic spaces over `S` which is stable under base change. If `g : T ⟶ Y` has `P`, then
every algebraic space representing a base change of `𝒮_T ⟶ 𝒮_Y` along a scheme-valued point of
`𝒮_Y` has structural morphism with `P`. -/
theorem prop_baseBasedMap_schemeSpace (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] (hg : P g) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (baseBasedCategory Y).obj)
      (_hy : y ⋙ (baseBasedCategory Y).p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (baseBasedCategory ((schemeSpaceFunctor B S hS).obj T)).p (baseBasedCategory Y).p y
          (baseBasedMap g).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  Stack.relativeProperty_of_equivalences B S hS P
    (𝒳' := baseFibredCategory ((schemeSpaceFunctor B S hS).obj T))
    (𝒴' := baseFibredCategory Y)
    (𝒳 := Stack.schemeFibredCategory B S hS T) (𝒴 := Stack.fibredCategory B S hS Y.obj)
    (baseBasedMap g) (Stack.presentationBasedFunctor B S hS T g.hom) baseToSlice
    (baseToElements Y) (baseBasedMapSquare g)
    (Stack.prop_presentationBasedFunctor B S hS P T Y.2 g.hom hg)

end SchemePoint

end AlgebraicGeometry.Space

end
