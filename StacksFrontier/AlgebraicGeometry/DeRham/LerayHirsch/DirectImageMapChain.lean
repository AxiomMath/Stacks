module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.BaseMapRelativeBase
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle

/-!
# The canonical map `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` in its two spellings

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S`, the canonical map of Section 07HX
`c : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` occurs in the library twice: as
`AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap f g`, the map the Leray--Hirsch
morphism of [Stacks, Tag 0FMR] is built from, a map into the derived direct image along
`AlgebraicGeometry.DeRhamLerayHirsch.baseMap f g`; and as the canonical map of the triangle of
[Stacks, Tag 0FUV], `Stacks.DeRham.BlowupTriangle.chain f g` followed by the unit of the derived
direct image along `Stacks.DeRhamSmooth.relativeBase f g`. The two morphisms of ringed spaces are
equal (`AlgebraicGeometry.DeRhamLerayHirsch.baseMap_eq_relativeBase`); this file proves that the
two canonical maps agree across that equality.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamPushforwardChain_comp_eqToHom`: the two maps of
  `ℕ`-indexed de Rham complexes agree.
* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamPushforwardInt_comp_eqToHom`: so do their
  extensions by zero.
* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap_comp_eqToHom`: the two canonical maps
  of derived categories agree.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open scoped Stacks.StandardDerivedModel

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

namespace AlgebraicGeometry.DeRhamLerayHirsch

/-- The identification of the direct images along two equal morphisms is the identity on
sections. -/
theorem eqToHom_pushforward_val_app_heq {A B : RingedSpace.{u, u}} {a b : A ⟶ B} (e : a = b)
    (M : SheafOfModules.{u} (structureSheafRing A)) (U) (x) :
    HEq ((eqToHom (congrArg (fun h => (modulePushforward h).obj M) e)).val.app U x) x := by
  subst e
  rfl

/-- Two morphisms into equal complexes of sheaves of modules are equal when they agree on
sections. -/
theorem hom_heq_of_val_app_heq {A : RingedSpace.{u, u}}
    {K L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℕ} (e : L = L')
    (φ : K ⟶ L) (ψ : K ⟶ L')
    (h : ∀ n U x, HEq ((φ.f n).val.app U x) ((ψ.f n).val.app U x)) : HEq φ ψ := by
  subst e
  refine heq_of_eq (HomologicalComplex.hom_ext _ _ fun n => ?_)
  ext U x
  exact eq_of_heq (h n U x)

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The two canonical maps of `ℕ`-indexed de Rham complexes `Ω^•_{Y/S} ⟶ f_*Ω^•_{X/S}`
agree**, across `baseMap f g = relativeBase f g`. -/
theorem deRhamPushforwardChain_heq :
    HEq (Stacks.DeRhamBaseChange.deRhamPushforwardChain f (f ≫ g) g (𝟙 S)
        (Category.comp_id _).symm)
      (Stacks.DeRhamPullback.deRhamPushforwardChain f g) := by
  refine hom_heq_of_val_app_heq (congrArg (fun h : inverseImageBase (f ≫ g) ⟶ inverseImageBase g =>
    ((_root_.pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Scheme.Hom.deRhamComplex (f ≫ g))) (baseMap_eq_relativeBase f g)) _ _ fun n U x => ?_
  have h2 := heq_of_eq (Stacks.DeRhamBaseChange.pushforwardSquareIso_inv_val_app f (f ≫ g) g (𝟙 S)
    (Category.comp_id _).symm _ U
    (((_root_.pushforward (toInverseImageBase g)).map
      (formsAdjoint f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm n)).val.app U x))
  have h3 := heq_of_eq (Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app f g _ U
    (((_root_.pushforward (toInverseImageBase g)).map
      (Stacks.DeRhamPullback.formsPushforwardComponent f g n)).val.app U x))
  have h4 := congrArg (fun φ => (((_root_.pushforward (toInverseImageBase g)).map φ).val.app U) x)
    (formsAdjoint_eq_deRhamFormsPushforwardHom f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm n)
  exact h2.trans ((heq_of_eq h4).trans h3.symm)

/-- The two comparisons of the extension by zero of a complex with an additive functor applied
termwise agree. -/
theorem mapExtendIso_eq_mapHomologicalComplexExtendIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
    (e : c.Embedding c') (K : HomologicalComplex C c) :
    Stacks.DerivedIndexing.mapExtendIso F e K =
      HomologicalComplex.mapHomologicalComplexExtendIso F K e := by
  refine Iso.ext (HomologicalComplex.hom_ext _ _ fun i' => ?_)
  cases hi : e.r i' with
  | none => exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X' e i' hi).eq_of_src _ _
  | some a =>
      have h : e.f a = i' := e.f_eq_of_r_eq_some hi
      rw [Stacks.DerivedIndexing.mapExtendIso_hom_f_eq F e K h,
        HomologicalComplex.mapHomologicalComplexExtendIso_hom_f F K e h]

/-- Extending by zero two corresponding maps into the direct images along two equal morphisms
gives corresponding maps. -/
theorem extendMap_comp_heq {A B : RingedSpace.{u, u}} {a b : A ⟶ B} (e : a = b)
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing B)) ℕ}
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℕ}
    (φ : K ⟶ ((modulePushforward a).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (ψ : K ⟶ ((modulePushforward b).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (h : HEq φ ψ) :
    HEq (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (modulePushforward a) L
          ComplexShape.embeddingUpNat).hom)
      (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫
        (Stacks.DerivedIndexing.mapExtendIso (modulePushforward b) ComplexShape.embeddingUpNat
          L).hom) := by
  subst e
  obtain rfl := eq_of_heq h
  rw [mapExtendIso_eq_mapHomologicalComplexExtendIso]

/-- **The two canonical maps of extended de Rham complexes `Ω^•_{Y/S} ⟶ f_*Ω^•_{X/S}` agree**,
across `baseMap f g = relativeBase f g`. -/
theorem deRhamPushforwardInt_heq :
    HEq (deRhamPushforwardInt f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm)
      (Stacks.DeRham.BlowupTriangle.chain f g) := by
  rw [deRhamPushforwardInt_eq]
  exact extendMap_comp_heq (baseMap_eq_relativeBase f g) _ _ (deRhamPushforwardChain_heq f g)

/-- The comparison `h_* ⟶ Rh_*` read on a complex is the unit of the derived direct image. -/
theorem pushforwardComparisonQ_eq_unit {A B : RingedSpace.{u, u}} (h : A ⟶ B)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℤ) :
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h K =
      Stacks.DeRham.BlowupTriangle.unit h K := by
  have e : DerivedCategory.Qh.map
      (((modulePushforward h).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) =
        𝟙 _ := DerivedCategory.Qh.map_id _
  simp only [Stacks.DeRham.BlowupTriangle.unit, StacksDraft.DerivedUnitSquare.unitQ, e]
  exact Eq.trans rfl (congrArg (_ ≫ ·) (Category.id_comp _).symm)

/-- The canonical map into a direct image, transported along an equality of the morphisms. -/
theorem map_comp_pushforwardComparisonQ_comp_eqToHom {A B : RingedSpace.{u, u}} {a b : A ⟶ B}
    (e : a = b) {K : CochainComplex (SheafOfModules.{u} (structureSheafRing B)) ℤ}
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℤ}
    (φ : K ⟶ ((modulePushforward a).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (ψ : K ⟶ ((modulePushforward b).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (h : HEq φ ψ) :
    DerivedCategory.Q.map φ ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ a L ≫
          eqToHom (congrArg (fun k => (derivedPushforward k).obj (DerivedCategory.Q.obj L)) e) =
      DerivedCategory.Q.map ψ ≫ Stacks.DeRham.BlowupTriangle.unit b L := by
  subst e
  obtain rfl := eq_of_heq h
  exact congrArg (DerivedCategory.Q.map φ ≫ ·)
    ((Category.comp_id _).trans (pushforwardComparisonQ_eq_unit a L))

/-- **The two canonical maps `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` agree**: the one of the Leray--Hirsch
morphism, read across `baseMap f g = relativeBase f g`, is the canonical map of the triangle of
[Stacks, Tag 0FUV]. -/
theorem deRhamDirectImageMap_comp_eqToHom :
    deRhamDirectImageMap f g ≫
        eqToHom (congrArg (fun k => (derivedPushforward k).obj (deRhamObject (f ≫ g)))
          (baseMap_eq_relativeBase f g)) =
      DerivedCategory.Q.map (Stacks.DeRham.BlowupTriangle.chain f g) ≫
        Stacks.DeRham.BlowupTriangle.unit (Stacks.DeRhamSmooth.relativeBase f g)
          (deRhamCochainComplex (f ≫ g)) :=
  (Category.assoc _ _ _).trans
    (map_comp_pushforwardComparisonQ_comp_eqToHom (baseMap_eq_relativeBase f g) _ _
      (deRhamPushforwardInt_heq f g))

end AlgebraicGeometry.DeRhamLerayHirsch

end
