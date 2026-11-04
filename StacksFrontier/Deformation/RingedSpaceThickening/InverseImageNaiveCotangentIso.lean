module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageThickeningPushoutClass
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPushforwardStalk
import StacksCore.Tactic.StacksAttribute

/-!
# The identification `g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` of Stacks 0GQ2

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces and
`π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)` the projection (`inverseImageProj g`). **Stacks 0GQ2** identifies
the naive cotangent complex `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` of the ringed space `(Y, g⁻¹𝒪_X)` over `S`
with `g⁻¹𝖭𝖫_{X/S}` (**Stacks 08TM**). The base ring of `(Y, g⁻¹𝒪_X)` over `S` is the inverse
image `(g ∘ f)⁻¹𝒪_S` along the composite, which is not literally `g⁻¹f⁻¹𝒪_S`; this file proves
that the canonical map `π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}`
(`AlgebraicGeometry.RingedSpaceThickening.pullbackNaiveCotangentMap` for `π`) is an isomorphism
of complexes, by the stalk argument of Stacks 08TM over a changed base, and states the class of the
pushout extension `𝒪'₁` of Stacks 0GQ2 directly in `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`.

## Main results

* `baseRingComparisonIso`: `g⁻¹f⁻¹𝒪_S ≅ (g ∘ f)⁻¹𝒪_S`.
* `bijective_stalkRingMapAlong_canonicalPushMap`: the map of canonical presentations
  `f⁻¹𝒪_S[𝒪_X] ⟶ π_*((g ∘ f)⁻¹𝒪_S[g⁻¹𝒪_X])` is bijective on stalks.
* `isIso_pullbackNaiveCotangentMap` and `inverseImageNaiveCotangentIso`: the canonical map
  `g⁻¹𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` is an isomorphism.
* `isomorphismClassesEquivExt_inverseImagePushout`: the class of `𝒪'₁` is the image of `ξ`.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.FreeAlgebra

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- The comparison `g⁻¹f⁻¹𝒪_S ⟶ (g ∘ f)⁻¹𝒪_S` of the iterated inverse image of the structure
sheaf of `S` with the inverse image along the composite: the transpose of
`f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S`. -/
def baseRingComparison :
    (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f) ⟶
      inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g) :=
  ((adjP g.hom.base).homEquiv _ _).symm (baseRingPushMap (inverseImageProj g) f)

/-- The inverse comparison `(g ∘ f)⁻¹𝒪_S ⟶ g⁻¹f⁻¹𝒪_S`: the transpose of the composite unit
`𝒪_S ⟶ f_*f⁻¹𝒪_S ⟶ f_*g_*g⁻¹f⁻¹𝒪_S`. -/
def baseRingComparisonInv :
    inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g) ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f) :=
  ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _).symm
    ((adjP f.hom.base).unit.app S.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
      ((adjP g.hom.base).unit.app (inverseImageBaseRing f)))

/-- The transpose of `baseRingComparison` is `baseRingPushMap`. -/
theorem homEquiv_baseRingComparison :
    (adjP g.hom.base).homEquiv _ _ (baseRingComparison f g) =
      baseRingPushMap (inverseImageProj g) f :=
  Equiv.apply_symm_apply _ _

/-- `baseRingComparisonInv` is a left inverse of `baseRingComparison`. -/
theorem baseRingComparisonInv_comp :
    baseRingComparisonInv f g ≫ baseRingComparison f g = 𝟙 _ := by
  refine ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _).injective ?_
  refine ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (inverseImageProj g ≫ f).hom.base).map (baseRingComparison f g))
    (((adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _).apply_symm_apply _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((adjP f.hom.base).unit.app S.sheaf ≫ ·)
    ((Functor.map_comp (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base) _ _).symm.trans
      (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        ((((adjP g.hom.base).homEquiv_unit _ _ _).symm.trans
          (homEquiv_baseRingComparison f g)))))).trans ?_
  refine ((((adjP f.hom.base).homEquiv_unit _ _ _).symm.trans
    (homEquiv_baseRingPushMap (inverseImageProj g) f))).trans ?_
  exact ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv_id _).symm

/-- `baseRingComparisonInv` is a right inverse of `baseRingComparison`. -/
theorem baseRingComparison_comp :
    baseRingComparison f g ≫ baseRingComparisonInv f g = 𝟙 _ := by
  refine ((adjP g.hom.base).homEquiv _ _).injective ?_
  refine ((adjP f.hom.base).homEquiv _ _).injective ?_
  refine (congrArg ((adjP f.hom.base).homEquiv _ _)
    ((adjP g.hom.base).homEquiv_naturality_right _ _)).trans ?_
  refine ((adjP f.hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
    ((TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (baseRingComparisonInv f g)))
    ((congrArg ((adjP f.hom.base).homEquiv _ _) (homEquiv_baseRingComparison f g)).trans
      (homEquiv_baseRingPushMap (inverseImageProj g) f))).trans ?_
  have hu : (adjP (inverseImageProj g ≫ f).hom.base).unit.app S.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g ≫ f).hom.base).map
        (baseRingComparisonInv f g) =
      (adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _ (baseRingComparisonInv f g) :=
    ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv_unit _ _ _).symm
  refine hu.trans ?_
  refine (((adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _).apply_symm_apply _).trans ?_
  refine Eq.trans ?_ (congrArg ((adjP f.hom.base).homEquiv _ _)
    ((adjP g.hom.base).homEquiv_id _)).symm
  exact ((adjP f.hom.base).homEquiv_unit _ _ _).symm

/-- The comparison `g⁻¹f⁻¹𝒪_S ⟶ (g ∘ f)⁻¹𝒪_S` is an isomorphism. -/
instance : IsIso (baseRingComparison f g) :=
  ⟨⟨baseRingComparisonInv f g, baseRingComparison_comp f g, baseRingComparisonInv_comp f g⟩⟩

/-- **The inverse image along `g` of the inverse image along `f` of the structure sheaf of `S`
is its inverse image along the composite.** -/
def baseRingComparisonIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f) ≅
      inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g) :=
  asIso (baseRingComparison f g)

/-- The map `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S` is bijective on stalks. -/
theorem bijective_stalkRingMapAlong_baseRingPushMap (w : Y.carrier) :
    Function.Bijective (Stacks.SheafOfModules.stalkRingMapAlong g.hom.base
      (A₁ := inverseImageBaseRing f)
      (A₂ := inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (baseRingPushMap (inverseImageProj g) f) w) :=
  Stacks.SheafOfModules.bijective_stalkRingMapAlong g.hom.base _ w
    (Functor.map_isIso (TopCat.Presheaf.stalkFunctor CommRingCat.{u} w)
      ((TopCat.Sheaf.forget CommRingCat.{u} Y.carrier).map (baseRingComparison f g)))

/-! ### The canonical presentations -/

/-- The map `f⁻¹𝒪_S[𝒪_X] ⟶ π_*((g ∘ f)⁻¹𝒪_S[g⁻¹𝒪_X])` of canonical presentations along `π`. -/
abbrev canonicalPushMap :=
  Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageProj g).hom.base (inverseImageBaseRing f)
    (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf)
    (baseRingPushMap (inverseImageProj g) f)
    (Functor.whiskerRight (structureComorphism (inverseImageProj g)).hom (forget CommRingCat.{u}))

/-- The change of coefficients `(g⁻¹f⁻¹𝒪_S)[g⁻¹𝒪_X] ⟶ ((g ∘ f)⁻¹𝒪_S)[g⁻¹𝒪_X]`. -/
abbrev coefficientChange :
    freeAlgebraSheaf (Opens.grothendieckTopology Y.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
        (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)) ⟶
      freeAlgebraSheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf) :=
  freeAlgebraSheafDesc _ _ _ _
    (baseRingComparison f g ≫ freeAlgebraSheafCoefficientMap
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageRingedSpace g).sheaf))
    (freeAlgebraSheafVariable (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageRingedSpace g).sheaf))

/-- The inverse change of coefficients. -/
abbrev coefficientChangeInv :
    freeAlgebraSheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf) ⟶
      freeAlgebraSheaf (Opens.grothendieckTopology Y.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
        (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)) :=
  freeAlgebraSheafDesc _ _ _ _
    (baseRingComparisonInv f g ≫ freeAlgebraSheafCoefficientMap
      (Opens.grothendieckTopology Y.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
      (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)))
    (freeAlgebraSheafVariable (Opens.grothendieckTopology Y.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
      (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)))

/-- Changing coefficients along mutually inverse maps `φ`, `ψ` gives mutually inverse maps of
free algebra sheaves. -/
private theorem freeAlgebraSheafDesc_comp_desc_eq_id {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{u}]
    (A₁ A₂ : Sheaf J CommRingCat.{u}) (E : Functor Cᵒᵖ (Type u)) (φ : A₁ ⟶ A₂) (ψ : A₂ ⟶ A₁)
    (h : φ ≫ ψ = 𝟙 _) :
    freeAlgebraSheafDesc J A₁ (freeAlgebraSheaf J A₂ E) E
        (φ ≫ freeAlgebraSheafCoefficientMap J A₂ E) (freeAlgebraSheafVariable J A₂ E) ≫
      freeAlgebraSheafDesc J A₂ (freeAlgebraSheaf J A₁ E) E
        (ψ ≫ freeAlgebraSheafCoefficientMap J A₁ E) (freeAlgebraSheafVariable J A₁ E) = 𝟙 _ := by
  refine freeAlgebraSheaf_hom_ext J A₁ _ E ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_desc, Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc, ← Category.assoc, h, Category.id_comp,
      Category.comp_id]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc, freeAlgebraSheafVariable_comp_desc]
    simp

/-- `coefficientChangeInv` is a right inverse of `coefficientChange`. -/
theorem coefficientChange_comp_inv :
    coefficientChange f g ≫ coefficientChangeInv f g = 𝟙 _ :=
  freeAlgebraSheafDesc_comp_desc_eq_id _ _ _ _ _ _ (baseRingComparison_comp f g)

/-- `coefficientChangeInv` is a left inverse of `coefficientChange`. -/
theorem coefficientChangeInv_comp :
    coefficientChangeInv f g ≫ coefficientChange f g = 𝟙 _ :=
  freeAlgebraSheafDesc_comp_desc_eq_id _ _ _ _ _ _ (baseRingComparisonInv_comp f g)

/-- The change of coefficients `(g⁻¹f⁻¹𝒪_S)[g⁻¹𝒪_X] ⟶ ((g ∘ f)⁻¹𝒪_S)[g⁻¹𝒪_X]` is an
isomorphism. -/
instance : IsIso (coefficientChange f g) :=
  ⟨⟨coefficientChangeInv f g, coefficientChange_comp_inv f g, coefficientChangeInv_comp f g⟩⟩

/-- **The transpose of the map of canonical presentations is the identification
`g⁻¹(f⁻¹𝒪_S[𝒪_X]) ≅ (g⁻¹f⁻¹𝒪_S)[g⁻¹𝒪_X]` followed by the change of coefficients.** -/
theorem homEquiv_symm_canonicalPushMap :
    ((adjP g.hom.base).homEquiv _ _).symm (canonicalPushMap f g) =
      (underlyingInverseImageIso g.hom.base (inverseImageBaseRing f) X.sheaf).hom ≫
        coefficientChange f g := by
  refine freeAlgebraSheaf_inverseImage_hom_ext g.hom.base (inverseImageBaseRing f) _ ?_ ?_
  · refine ((adjP g.hom.base).homEquiv_naturality_left_symm _ _).symm.trans ?_
    refine (congrArg ((adjP g.hom.base).homEquiv _ _).symm
      (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap
        (inverseImageProj g).hom.base (inverseImageBaseRing f)
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf)
        (baseRingPushMap (inverseImageProj g) f)
        (Functor.whiskerRight (structureComorphism (inverseImageProj g)).hom
          (forget CommRingCat.{u})))).trans ?_
    refine ((adjP g.hom.base).homEquiv_naturality_right_symm _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ coefficientChange f g)
      (map_freeAlgebraSheafCoefficientMap_comp_underlyingInverseImageIso g.hom.base
        (inverseImageBaseRing f) X.sheaf)).symm
    exact (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _).symm
  · apply ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u)
      g.hom.base).homEquiv _ _).injective
    refine (freeAlgebraSheafVariable_comp_homEquiv g.hom.base (inverseImageBaseRing f) _ _
      (((adjP g.hom.base).homEquiv _ _).symm (canonicalPushMap f g))).symm.trans ?_
    have e1 := Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap
        (inverseImageProj g).hom.base (inverseImageBaseRing f)
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf)
        (baseRingPushMap (inverseImageProj g) f)
        (Functor.whiskerRight (structureComorphism (inverseImageProj g)).hom
          (forget CommRingCat.{u}))
    have e2 := inverseImageVariable_comp_inverseImageHom_map_comp g.hom.base
      (inverseImageBaseRing f)
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) _
      (toUnderlyingInverseImage g.hom.base X.sheaf) _ (coefficientChange f g)
    have e3 := freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology Y.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
      (freeAlgebraSheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf))
      (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf))
      (baseRingComparison f g ≫ freeAlgebraSheafCoefficientMap
        (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf))
      (freeAlgebraSheafVariable (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf))
    have e4 := toUnderlyingInverseImage_comp_homEquiv g.hom.base X.sheaf _
      (freeAlgebraSheafVariable (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf))
    refine Eq.trans ?_ (congrArg ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u)
      g.hom.base).homEquiv _ _)
        (e2.trans (congrArg (toUnderlyingInverseImage g.hom.base X.sheaf ≫ ·) e3))).symm
    refine Eq.trans ?_ e4.symm
    refine Eq.trans ?_ e1
    exact congrArg (fun t => freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) ≫
        Functor.whiskerRight ((sheafToPresheaf _ _).map t) (forget CommRingCat.{u}))
      (((adjP g.hom.base).homEquiv _ _).apply_symm_apply _)

/-- The change of coefficients, as an isomorphism of sheaves of rings on `Y`. -/
def coefficientChangeIso :
    (freeAlgebraSheaf (Opens.grothendieckTopology Y.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing f))
        (underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)) :
        TopCat.Sheaf CommRingCat.{u} Y.carrier) ≅
      freeAlgebraSheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf) where
  hom := coefficientChange f g
  inv := coefficientChangeInv f g
  hom_inv_id := coefficientChange_comp_inv f g
  inv_hom_id := coefficientChangeInv_comp f g

/-- The map of canonical presentations along `π` is bijective on stalks. -/
theorem bijective_stalkRingMapAlong_canonicalPushMap (w : Y.carrier) :
    Function.Bijective (Stacks.SheafOfModules.stalkRingMapAlong g.hom.base
      (canonicalPushMap f g) w) := by
  refine Stacks.SheafOfModules.bijective_stalkRingMapAlong g.hom.base _ w ?_
  have h : ((adjP g.hom.base).homEquiv _ _).symm (canonicalPushMap f g) =
      ((underlyingInverseImageIso g.hom.base (inverseImageBaseRing f) X.sheaf) ≪≫
        coefficientChangeIso f g).hom :=
    homEquiv_symm_canonicalPushMap f g
  rw [h]
  exact ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} w).mapIso
    ((TopCat.Sheaf.forget CommRingCat.{u} Y.carrier).mapIso
      ((underlyingInverseImageIso g.hom.base (inverseImageBaseRing f) X.sheaf) ≪≫
        coefficientChangeIso f g))).isIso_hom

/-! ### The comparison `g⁻¹𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` is an isomorphism -/

/-- In degree `-1`, the map `π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` is the transpose of the
degree `-1` part of `naiveCotangentPushMap`. -/
theorem pullbackNaiveCotangentMap_f_negOne :
    (pullbackNaiveCotangentMap (inverseImageProj g) f).f (-1) =
      ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
        ((naiveCotangentPushMap (inverseImageProj g) f).f (-1)) :=
  mapHomologicalComplex_homEquiv_symm_f _ _

/-- In degree `0`, the map `π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` is the transpose of the
degree `0` part of `naiveCotangentPushMap`. -/
theorem pullbackNaiveCotangentMap_f_zero :
    (pullbackNaiveCotangentMap (inverseImageProj g) f).f 0 =
      ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
        ((naiveCotangentPushMap (inverseImageProj g) f).f 0) :=
  mapHomologicalComplex_homEquiv_symm_f _ _

/-- The degree `-1` part of `𝖭𝖫_{X/S} ⟶ π_*𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}`: the map of conormal
sheaves. -/
abbrev conormalPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  Stacks.SheafOfModules.presentationConormalPushMap (inverseImageProj g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
    (underlyingPresheafMap_comp (inverseImageProj g))

/-- The degree `-1` part of `naiveCotangentPushMap` is `conormalPushMap`, up to the
identifications of the degree `-1` terms with the conormal sheaves. -/
theorem naiveCotangentPushMap_f_negOne :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    (naiveCotangentPushMap (inverseImageProj g) f).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) _ (𝟙 _)) ≫
        conormalPushMap f g ≫
        (modulePushforward (inverseImageProj g)).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
            (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g)) _
            (𝟙 _)).symm) :=
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne (inverseImageProj g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
    (underlyingPresheafMap_comp (inverseImageProj g))

/-- The canonical presentation of `𝒪_X` over `f⁻¹𝒪_S`. -/
abbrev sourceCanonicalPresentation :=
  Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _)

/-- The canonical presentation of `g⁻¹𝒪_X` over `(g ∘ f)⁻¹𝒪_S`, read as a presentation of the
inverse image `g⁻¹𝒪_X`. -/
abbrev targetCanonicalPresentation :
    freeAlgebraSheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf) ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  Stacks.SheafOfModules.presentation
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (𝟙 _)

/-- The map of canonical presentations is compatible with the presentations
`sourceCanonicalPresentation` and `targetCanonicalPresentation` and the unit
`𝒪_X ⟶ g_*g⁻¹𝒪_X`. -/
theorem canonicalPushMap_comp_presentation :
    canonicalPushMap f g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        (targetCanonicalPresentation f g) =
      sourceCanonicalPresentation f ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).unit.app X.sheaf :=
  Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation (inverseImageProj g).hom.base
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
    (underlyingPresheafMap_comp (inverseImageProj g))

/-- The canonical presentation of `𝒪_X` over `f⁻¹𝒪_S` is locally surjective. -/
theorem isLocallySurjective_sourceCanonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (sourceCanonicalPresentation f).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The canonical presentation of `g⁻¹𝒪_X` over `(g ∘ f)⁻¹𝒪_S` is locally surjective. -/
theorem isLocallySurjective_targetCanonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (targetCanonicalPresentation f g).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The transpose `π^*` of the map of conormal sheaves `conormalPushMap` is an isomorphism. -/
instance isIso_homEquiv_symm_conormalPushMap :
    IsIso (((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
      (conormalPushMap f g)) :=
  @Stacks.SheafOfModules.isIso_inverseImageConormalMapAlong _ _ g.hom.base X.sheaf _ _
    (sourceCanonicalPresentation f) (targetCanonicalPresentation f g) (canonicalPushMap f g)
    (canonicalPushMap_comp_presentation f g)
    (isLocallySurjective_sourceCanonicalPresentation f)
    (isLocallySurjective_targetCanonicalPresentation f g)
    (bijective_stalkRingMapAlong_canonicalPushMap f g)

/-- The degree `0` part of `𝖭𝖫_{X/S} ⟶ π_*𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}`: the map of the scalar
extensions of the differentials. -/
abbrev tensorPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  Stacks.SheafOfModules.presentationTensorPushMap (inverseImageProj g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
    (underlyingPresheafMap_comp (inverseImageProj g))

/-- The degree `0` part of `naiveCotangentPushMap` is `tensorPushMap`, up to the
identifications of the degree `0` terms with the scalar extensions of the differentials. -/
theorem naiveCotangentPushMap_f_zero :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    (naiveCotangentPushMap (inverseImageProj g) f).f 0 =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) _ (𝟙 _)) ≫
        tensorPushMap f g ≫
        (modulePushforward (inverseImageProj g)).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
            (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g)) _
            (𝟙 _)).symm) :=
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_zero (inverseImageProj g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
    (underlyingPresheafMap_comp (inverseImageProj g))

/-- The map of canonical presentations restricts on coefficients to
`baseRingPushMap : f⁻¹𝒪_S ⟶ π_*(g ∘ f)⁻¹𝒪_S`. -/
theorem canonicalPushMap_coefficient :
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) :
        (inverseImageBaseRing f : TopCat.Sheaf CommRingCat.{u} X.carrier) ⟶ _) ≫
        canonicalPushMap f g =
      baseRingPushMap (inverseImageProj g) f ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
          (freeAlgebraSheafCoefficientMap
            (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
            (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
              (inverseImageRingedSpace g).sheaf)) :=
  Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap _ _ _ _ _ _ _

/-- The comparison of the scalar extensions of the differentials for the canonical
presentations. -/
def canonicalTensorMap :=
  (@Stacks.SheafOfModules.inverseImageTensorMapPush _ _ g.hom.base X.sheaf _ _
    (sourceCanonicalPresentation f) (targetCanonicalPresentation f g) (canonicalPushMap f g)
    (inverseImageBaseRing f)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageRingedSpace g).sheaf))
    (baseRingPushMap (inverseImageProj g) f)
    (canonicalPushMap_coefficient f g)
    (canonicalPushMap_comp_presentation f g)
    (isLocallySurjective_sourceCanonicalPresentation f)
    (isLocallySurjective_targetCanonicalPresentation f g))

/-- The comparison `canonicalTensorMap` of scalar extensions of differentials is an
isomorphism. -/
theorem isIso_canonicalTensorMap : IsIso (canonicalTensorMap f g) := by
  have := isLocallySurjective_sourceCanonicalPresentation f
  have := isLocallySurjective_targetCanonicalPresentation f g
  exact Stacks.SheafOfModules.isIso_inverseImageTensorMapPush g.hom.base _ _ _ _ _ _ _ _ _ _ _
    (bijective_stalkRingMapAlong_canonicalPushMap f g)
    (bijective_stalkRingMapAlong_baseRingPushMap f g)

/-- The transpose of `tensorPushMap` is an isomorphism. -/
instance isIso_homEquiv_symm_tensorPushMap :
    IsIso (((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
      (tensorPushMap f g)) :=
  isIso_canonicalTensorMap f g

/-- The transpose of a map `ℳ ⟶ π_*𝒩` framed by two transport isomorphisms is invertible as soon
as the transpose of the middle map is. -/
theorem isIso_homEquiv_symm_eqToHom_comp {M M' : SheafOfModules.{u} (structureSheafRing X)}
    {N N' : SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g))} (h : M = M')
    (h' : N' = N) (m : M' ⟶ (modulePushforward (inverseImageProj g)).obj N')
    [IsIso (((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm m)] :
    IsIso (((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
      (eqToHom h ≫ m ≫ (modulePushforward (inverseImageProj g)).map (eqToHom h'))) := by
  subst h h'
  simpa using (inferInstance : IsIso
    (((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm m))

/-- **Stacks 08TM over the composite base.** The canonical map
`g⁻¹𝖭𝖫_{X/S} = π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` is an isomorphism of complexes. -/
instance isIso_pullbackNaiveCotangentMap :
    IsIso (pullbackNaiveCotangentMap (inverseImageProj g) f) := by
  have h : ∀ k : ℤ, IsIso ((pullbackNaiveCotangentMap (inverseImageProj g) f).f k) := by
    intro k
    by_cases h₁ : k = -1
    · subst h₁
      rw [pullbackNaiveCotangentMap_f_negOne]
      have e := naiveCotangentPushMap_f_negOne f g
      rw [e]
      exact isIso_homEquiv_symm_eqToHom_comp _ _ _ _
    by_cases h₀ : k = 0
    · subst h₀
      rw [pullbackNaiveCotangentMap_f_zero]
      have e := naiveCotangentPushMap_f_zero f g
      rw [e]
      exact isIso_homEquiv_symm_eqToHom_comp _ _ _ _
    refine ⟨0, ?_, ?_⟩
    · exact (Functor.map_isZero (modulePullback (inverseImageProj g))
        (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) k h₁ h₀)).eq_of_src _ _
    · exact (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u}
        (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (inverseImageRingedSpace g).sheaf
        (structureRingMap (inverseImageSpaceHom f g)) k h₁ h₀).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The identification `g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}`: the canonical map
`π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(g ∘ f)⁻¹𝒪_S}` of naive cotangent complexes, as an isomorphism of
complexes of `g⁻¹𝒪_X`-modules. -/
@[stacks 0GQ2]
def inverseImageNaiveCotangentIso :
    ((modulePullback (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
          PresentedSquareZeroExtension.relativeComplex f) ≅
      (show CochainComplex
            (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g))) ℤ from
          PresentedSquareZeroExtension.relativeComplex (inverseImageProj g ≫ f)) :=
  asIso (pullbackNaiveCotangentMap (inverseImageProj g) f)

/-- The forward map of `inverseImageNaiveCotangentIso` is `pullbackNaiveCotangentMap`. -/
@[simp]
theorem inverseImageNaiveCotangentIso_hom :
    (inverseImageNaiveCotangentIso f g).hom = pullbackNaiveCotangentMap (inverseImageProj g) f :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard

section PushoutClass

variable {f g} {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}

/-- **The image of `ξ`** in `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`: `g⁻¹ξ` pushed along
`c^♭ : g⁻¹ℱ ⟶ 𝒢` (`inverseImagePushoutExtMap`), read on `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` through the
identification `g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` (`inverseImageNaiveCotangentIso`). -/
def inverseImageXiMap (c : F ⟶ (modulePushforward g).obj G) (z : extOneNaiveCotangent f F) :
    extOneNaiveCotangent (inverseImageSpaceHom f g) (restrictedModule g G) :=
  (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫
    inverseImagePushoutExtMap c z

/-- **The class of `𝒪'₁` is the image of `ξ`**, in `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`. -/
theorem extClass_inverseImagePushout_eq (P : SquareZeroAlgebraExtension f F)
    (c : F ⟶ (modulePushforward g).obj G) :
    (inverseImagePushout G P c).extClass = inverseImageXiMap c P.extClass :=
  (Iso.eq_inv_comp _).2 (extClass_inverseImagePushout P c)

/-- The class, under the bijection of **Stacks 0GPZ** for the ringed space `(Y, g⁻¹𝒪_X)` over `S`,
of the pushout `𝒪'₁` of `0 ⟶ g⁻¹ℱ ⟶ g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X ⟶ 0` along `c : g⁻¹ℱ ⟶ 𝒢` is the image
of the class `ξ` of `𝒪_{X'}` (under the bijection of **Stacks 0GPZ** for `X` over `S`): `g⁻¹ξ`
pushed along `c^♭ : g⁻¹ℱ ⟶ 𝒢`, read in `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)` through the
identification `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} = g⁻¹𝖭𝖫_{X/S}` of **Stacks 08TM**. -/
@[stacks 0GQ2]
theorem isomorphismClassesEquivExt_inverseImagePushout (P : SquareZeroAlgebraExtension f F)
    (c : F ⟶ (modulePushforward g).obj G) :
    SquareZeroAlgebraExtension.isomorphismClassesEquivExt (inverseImageSpaceHom f g)
        (restrictedModule g G) (Quotient.mk _ (inverseImagePushout G P c)) =
      inverseImageXiMap c
        (SquareZeroAlgebraExtension.isomorphismClassesEquivExt f F (Quotient.mk _ P)) :=
  extClass_inverseImagePushout_eq P c

end PushoutClass

end AlgebraicGeometry.RingedSpaceThickening
