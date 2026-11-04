module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalStalkCondition
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerSquare

/-!
# The base change map of `NL` and the comparison of presentations, on conormal classes

Let `g' ≫ (i ≫ h) = (i' ≫ h') ≫ g` and `i' ≫ p = g' ≫ i` be commutative squares of schemes with
`i`, `i'` immersions.  The proof of [Stacks Project, Tag 0FV9] identifies the map induced on
`H^{-1}` by the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of [Stacks Project, Tag 0FV5]
through the polynomial presentations of `𝒪_X` and `𝒪_{X'}` on the sections of `i⁻¹𝒪_P` and
`i'⁻¹𝒪_{P'}`, by
`Stacks.NaiveCotangentPulledImmersion.homologyMap_inv_homologyNegOneι_eq_of_degreewise`.
That needs the degree `-1` components of all the maps involved on the classes of polynomial
relations, which this file computes.

A map out of the conormal sheaf `I/I²` of a presentation is determined by its values on the
conormal classes of local sections of `I`, and a map out of a pullback `(g')^*(I/I²)` by its
values on the images under the unit of such classes
(`Stacks.NaiveCotangentPulledImmersion.twoStepPullback_hom_ext_conormalClassX`).  On these:

* the canonical chain map of [Stacks Project, Tag 08TX] attached to a square of sheaves of rings
  sends the class of `t` to the class of the image of `t` in the free algebra of the target
  (`naiveCotangentComplexMapOfSquare_f_negOne_conormalClassX`);
* the inverse-image comparison of [Stacks Project, Tag 08TM] sends the unit image of the class of
  `t` to the class of the inverse-image section of `t`
  (`naiveCotangentComplexInverseImageMap_f_negOne_unit_conormalClassX`);
* the base change map of [Stacks Project, Tag 0FV5] sends the unit image of the class of `t` to
  the class of the image of `t` under the comparison of base rings and the structure map of `g'`
  (`baseChangeMapOfComparison_f_negOne_unit_conormalClassX`);
* the comparisons of `NL_{X/Y}` with the polynomial presentation, and its pullback, send the
  class of a relation to the class of its evaluation
  (`presentationToNaiveCotangent_f_negOne_conormalClassX`,
  `pulled_presentationToNaiveCotangent_f_negOne_unit`);
* the degree `-1` comparison of the pulled-back presentations sends the unit image of the class
  of a relation to the class of its image under the morphism of presentations
  (`pulledPresentationNegOne_unit_conormalClassX`).

The two ways of turning a relation over `i⁻¹h⁻¹𝒪_Y` into a polynomial over `(i' ≫ h')⁻¹𝒪_{Y'}`
agree as morphisms of sheaves of rings (`presentationRingMap_comp_evaluation`).

## Implementation notes

Unit images are compared through `Stacks.NaiveCotangentPulledImmersion.twoStepCompAdjunction`,
whose unit is explicit on sections.  The base change map is folded into the composite whose
last factor is a map of squares (`eqToHom_comp_spaceRelativeNaiveCotangentComplexMap`) by
`Eq.mpr` along a definitional equation, never by conversion: two morphisms of these complexes
that differ by an unfolding are compared by descending through every degree.  Values of
composites of chain maps are computed by `comp_f_val_app`, with the two factors given
explicitly; elaborating such a composite from the goal is not feasible.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

universe u

noncomputable section

section PartP1

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace Stacks.NaiveCotangentPulledImmersion

section RestrictClass

variable {T : TopCat.{u}} {B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u}}
  (β : B ⟶ B')

/-- Restriction of scalars along `β` of the transport `eqToHom e` along an equality of sheaves
of modules acts on sections as `eqToHom e`. -/
theorem restrictScalars_map_eqToHom_val_app
    {M N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B')} (e : M = N) (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    (((_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHomOfSite
      (J := Opens.grothendieckTopology T) β)).map (eqToHom e)).val.app U x : N.val.obj U) =
      (eqToHom e).val.app U x := by
  subst e
  rfl

variable {R A R' A' : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
  (a : R ⟶ A) (φ : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom]
  (a' : R' ⟶ A') (φ' : A' ⟶ B') [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ'.hom]

/-- A map from a degree `-1` term identified with a conormal sheaf to the restriction of scalars
of another, which is up to the identifications a map `c` of conormal sheaves, carries a conormal
class to the class `c` carries it to. -/
theorem map_conormalClassX_of_restrictScalars {K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    {L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B')) ℤ}
    (eK : K.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R A B a φ).X₁)
    (eL : L.X (-1) =
      (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R' A' B' a' φ').X₁)
    (m : K.X (-1) ⟶ (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHomOfSite (J :=
        Opens.grothendieckTopology T) β)).obj
      (L.X (-1)))
    (c : conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology T) A B φ ⟶
      (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHomOfSite
        (J := Opens.grothendieckTopology T) β)).obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology T) A' B' φ'))
    (hm : m = eqToHom eK ≫ c ≫
      (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHomOfSite (J :=
          Opens.grothendieckTopology T) β)).map
        (eqToHom eL.symm))
    (U : (Opens T)ᵒᵖ) (s : kernelIdeal φ.hom U) (t : kernelIdeal φ'.hom U)
    (hc : c.val.app U (conormalClass.{u, u, u, u} _ R A B a φ U s) =
      conormalClass.{u, u, u, u} _ R' A' B' a' φ' U t) :
    (m.val.app U (conormalClassX a φ eK U s) : (L.X (-1)).val.obj U) =
      conormalClassX a' φ' eL U t := by
  subst hm
  show ((_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHomOfSite (J :=
      Opens.grothendieckTopology T) β)).map
    (eqToHom eL.symm)).val.app U (c.val.app U ((eqToHom eK).val.app U _)) = _
  rw [eqToHom_val_app_conormalClassX, hc, restrictScalars_map_eqToHom_val_app]
  rfl

end RestrictClass

section SquareClass

variable {T : TopCat.{u}} (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u})
  (a : A ⟶ B) (A' B' : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a' : A' ⟶ B') (f : A ⟶ A') (β : B ⟶ B') (hsq : a ≫ β = f ≫ a')

/-- In degree `-1`, the map of naive cotangent complexes attached to a commutative square of
sheaves of rings sends the conormal class of `t` to the conormal class of the image of `t` in the
free algebra of the target. -/
theorem naiveCotangentComplexMapOfSquare_f_negOne_conormalClassX (U : (Opens T)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology T) A B a).hom U) :
    ((naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T) A B a A' B'
        a' f β hsq).f (-1)).val.app U
      (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A _)
        (canonicalPresentation (Opens.grothendieckTopology T) A B a)
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A B a) U t) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A' _)
        (canonicalPresentation (Opens.grothendieckTopology T) A' B' a')
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A' B' a') U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A' B B' f β).hom.app U
          t, kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ A A' B B' a a' f β hsq)) U t.2⟩ :=
                by
  have hm := naiveCotangentComplexMapOfSquare_f_negOne.{u, u, u, u} (Opens.grothendieckTopology T)
    A B a A' B' a' f β hsq
  unfold naiveCotangentConormalMapOfSquare at hm
  refine map_conormalClassX_of_restrictScalars β _ _ _ _ _ _ _ _ hm U t _ ?_
  have hc := (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} (Opens.grothendieckTopology T) A
      A'
      (freeAlgebraSheaf (Opens.grothendieckTopology T) A (underlyingPresheaf _ B))
      (freeAlgebraSheaf (Opens.grothendieckTopology T) A' (underlyingPresheaf _ B')) B B'
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A (underlyingPresheaf _ B))
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A' (underlyingPresheaf _ B'))
      (canonicalPresentation (Opens.grothendieckTopology T) A B a)
      (canonicalPresentation (Opens.grothendieckTopology T) A' B' a')
      (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A' B B' f β) β
      (freeAlgebraMapOfSquare_comp_canonicalPresentation _ A A' B B' a a' f β hsq) U t)
  convert hc using 2

end SquareClass

end Stacks.NaiveCotangentPulledImmersion

end PartP1

section PartP2

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)

namespace Stacks.NaiveCotangentPulledImmersion

section PullbackClass

variable {X Y : TopCat.{u}} (f : Y ⟶ X) {B : TopCat.Sheaf CommRingCat.{u} X}
  {R A : TopCat.Sheaf CommRingCat.{u} X} (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom]
  {R' A' : TopCat.Sheaf CommRingCat.{u} Y} (a' : R' ⟶ A')
  (φ' : A' ⟶ (TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ'.hom]

/-- Naturality of the unit of an adjunction of categories of sheaves of modules on sections: `G F v`
carries the unit image of `x` to the unit image of `v x`. -/
private theorem adjunction_map_unit_val_app {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    {R₁ : Sheaf J₁ RingCat.{u}} {R₂ : Sheaf J₂ RingCat.{u}}
    {F : _root_.SheafOfModules.{u} R₁ ⥤ _root_.SheafOfModules.{u} R₂}
    {G : _root_.SheafOfModules.{u} R₂ ⥤ _root_.SheafOfModules.{u} R₁} (adj : F ⊣ G)
    {M M' : _root_.SheafOfModules.{u} R₁} (v : M ⟶ M') (U : C₁ᵒᵖ) (x : M.val.obj U) :
    (G.map (F.map v)).val.app U ((adj.unit.app M).val.app U x) =
      (adj.unit.app M').val.app U (v.val.app U x) :=
  (congrArg (fun t => t.val.app U x) (adj.unit.naturality v)).symm

/-- A map out of the inverse image of a degree `-1` term identified with a conormal sheaf,
which is up to the identifications a map `c` of conormal sheaves, carries the image under the
unit of a conormal class to the class `c` carries it to. -/
theorem map_unit_conormalClassX {K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology X) B)) ℤ}
    {L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) ℤ}
    (eK : K.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) R A B a φ).X₁)
    (eL : L.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y) R' A' _ a'
      φ').X₁)
    (m : (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj (K.X (-1)) ⟶ L.X (-1))
    (c : (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A B φ) ⟶
      conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) A' _ φ')
    (hm : m = (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map (eqToHom eK) ≫
      c ≫ eqToHom eL.symm)
    (U : (Opens X)ᵒᵖ) (s : kernelIdeal φ.hom U) (t : kernelIdeal φ'.hom ((Opens.map f).op.obj U))
    (hc : c.val.app ((Opens.map f).op.obj U)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (inverseImageRingHom f
            B)).unit.app
          (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A B φ)).val.app U
          (conormalClass.{u, u, u, u} _ R A B a φ U s)) =
      conormalClass.{u, u, u, u} _ R' A' _ a' φ' _ t) :
    m.val.app ((Opens.map f).op.obj U)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (inverseImageRingHom f
            B)).unit.app
          (K.X (-1))).val.app U (conormalClassX a φ eK U s)) = conormalClassX a' φ' eL _ t := by
  subst hm
  have h2 := (adjunction_map_unit_val_app (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
    (inverseImageRingHom f B)) (eqToHom eK) U (conormalClassX a φ eK U s)).trans
    (congrArg (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (inverseImageRingHom f B)).unit.app _).val.app U).hom
      (eqToHom_val_app_conormalClassX a φ eK U s))
  exact congrArg ((eqToHom eL.symm).val.app _).hom ((congrArg (c.val.app _).hom h2).trans hc)

end PullbackClass

section InverseImageClass

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (A B : TopCat.Sheaf CommRingCat.{u} X) (a : A ⟶ B)

/-- In degree `-1`, the inverse-image comparison of naive cotangent complexes along `f` sends the
image under the unit of the conormal class of `t` to the conormal class of the inverse-image
section of `t`. -/
theorem naiveCotangentComplexInverseImageMap_f_negOne_unit_conormalClassX (U : (Opens X)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X) A B a).hom U) :
    ((naiveCotangentComplexInverseImageMap f A B a).f (-1)).val.app ((Opens.map f).op.obj U)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (inverseImageRingHom f
            B)).unit.app
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X
              (-1))).val.app
            U (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A _)
              (canonicalPresentation (Opens.grothendieckTopology X) A B a)
              (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A B a) U t)) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) _)
        (canonicalPresentation (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) ((Opens.map f).op.obj U)
        ⟨(sectionsMapAlong f (inverseImagePresentationHom f A B) U).hom t,
          kernelIdeal_le_comap_inverseImagePresentationHom f A B a U t.2⟩ := by
  refine map_unit_conormalClassX f _ _ _ _ _ _ _ _
    (naiveCotangentComplexInverseImageMap_f_negOne f A B a) U t _ ?_
  refine (Stacks.SheafOfModules.inverseImageAdjunction_homEquiv_symm_val_app_unit f B
    (inverseImageConormalPushforwardMap f A B a) U _).trans ?_
  exact conormalSheafMapAlong_conormalClass f B _ _ _
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a) A _ _ U t

end InverseImageClass

end Stacks.NaiveCotangentPulledImmersion

end PartP2

section PartP3

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)

namespace Stacks.NaiveCotangentPulledImmersion

section Tower

variable {T : TopCat.{u}} (B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u})
  (b : B ⟶ C)

/-- The unit of extension and restriction of scalars along `b`, on a section, as a section of the
extension of scalars. -/
def towerUnitVal (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)) (V : (Opens T)ᵒᵖ) (y : M.val.obj V) :
    ((towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b).obj M).val.obj V :=
  ((towerExtendRestrictAdjunction.{u, u, u} (Opens.grothendieckTopology T) B C b).unit.app
    M).val.app V y

/-- Extension of scalars along `b` of a map `m` sends the unit image of a section `y` to the unit
image of `m y`. -/
theorem towerExtendScalars_map_towerUnitVal
    {M M' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)} (m : M ⟶ M') (V : (Opens T)ᵒᵖ) (y : M.val.obj V) :
    ((towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b).map m).val.app V
        (towerUnitVal B C b M V y) = towerUnitVal B C b M' V (m.val.app V y) :=
  adjunction_map_unit_val_app
    (towerExtendRestrictAdjunction.{u, u, u} (Opens.grothendieckTopology T) B C b) m V y

/-- The degree `i` component of the extension of scalars of a chain map `φ` is the extension of
scalars of `φ.f i`, on sections. -/
theorem towerExtendScalarsComplexes_map_f_val_app
    {K L : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)) ℤ} (φ : K ⟶ L) (i : ℤ) (V : (Opens T)ᵒᵖ)
    (x : (((towerExtendScalarsComplexes.{u, u, u} (Opens.grothendieckTopology T) B C b).obj
      K).X i).val.obj V) :
    (((towerExtendScalarsComplexes.{u, u, u} (Opens.grothendieckTopology T) B C b).map φ).f
        i).val.app V x =
      ((towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b).map (φ.f i)).val.app V
        x :=
  rfl

/-- The counit of extension and restriction of scalars along `b` sends the unit image of a
section `y` back to `y`. -/
theorem towerCounit_f_towerUnitVal
    (K : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) C)) ℤ) (i : ℤ) (V : (Opens T)ᵒᵖ)
    (y : (((towerRestrictScalarsComplexes.{u, u, u} (Opens.grothendieckTopology T) B C b).obj
      K).X i).val.obj V) :
    ((towerCounit.{u, u, u} (Opens.grothendieckTopology T) B C b K).f i).val.app V
      (towerUnitVal B C b _ V y) = y :=
  congrArg (fun t => t.val.app V y)
    ((towerExtendRestrictAdjunction.{u, u, u} (Opens.grothendieckTopology T) B C
      b).right_triangle_components (K.X i))

/-- The extension of scalars of a chain map `φ` followed by the counit sends the unit image of a
section `y` to `φ y`. -/
theorem extendScalars_comp_counit_f_towerUnitVal
    {K : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)) ℤ}
    {L : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) C)) ℤ}
    (φ : K ⟶ (towerRestrictScalarsComplexes.{u, u, u} (Opens.grothendieckTopology T) B C b).obj L)
    (i : ℤ) (V : (Opens T)ᵒᵖ) (y : (K.X i).val.obj V) :
    (((towerExtendScalarsComplexes.{u, u, u} (Opens.grothendieckTopology T) B C b).map φ ≫
        towerCounit.{u, u, u} (Opens.grothendieckTopology T) B C b L).f i).val.app V
      (towerUnitVal B C b _ V y) = (φ.f i).val.app V y :=
  (congrArg (((towerCounit.{u, u, u} (Opens.grothendieckTopology T) B C b L).f i).val.app V).hom
    (towerExtendScalars_map_towerUnitVal B C b (φ.f i) V y)).trans
    (towerCounit_f_towerUnitVal B C b L i V _)

end Tower

section CompValue

/-- The degree `i` component of a composite `φ ≫ ψ` of chain maps of sheaves of modules acts on
sections as `ψ.f i` after `φ.f i`. -/
theorem comp_f_val_app {T : TopCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {inst : HasZeroMorphisms (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B))}
    {K L M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (i : ℤ) (U : (Opens T)ᵒᵖ) (x : (K.X i).val.obj U) :
    ((φ ≫ ψ).f i).val.app U x = (ψ.f i).val.app U ((φ.f i).val.app U x) :=
  rfl


variable {T : TopCat.{u}} {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

variable (A C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})

end CompValue

section Transport

variable {T : TopCat.{u}} (A C : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u})

end Transport

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

section SpaceBaseChange

variable {T : TopCat.{u}} (A B C B'' : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (bc : A ⟶ B'') (s' : B'' ⟶ C) (h : a ≫ b = bc ≫ s')

/-- In degree `-1`, the base change map along `b` followed by the map of the square
`(a ≫ b) ≫ 𝟙 C = bc ≫ s'` sends the unit image of the conormal class of `t` to the conormal
class of `t'`, the image of `t` in the free algebra of the target. -/
theorem spaceBaseChange_comp_square_f_negOne_towerUnitVal (U : (Opens T)ᵒᵖ)
    (hsq : (a ≫ b) ≫ 𝟙 C = bc ≫ s')
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology T) A B a).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology T) B'' C s').hom U)
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A B'' C C bc
        (𝟙 C)).hom.app U
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A B C (𝟙 A) b).hom.app U
        t)) :
    ((spaceBaseChangeNaiveCotangentMap A B C a b ≫
        spaceNaiveCotangentComplexMapOfSquare A B'' C C (a ≫ b) s' bc (𝟙 C) hsq).f (-1)).val.app U
      (towerUnitVal B C b _ U
        (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A _)
          (canonicalPresentation (Opens.grothendieckTopology T) A B a)
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A B a) U t)) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) B'' _)
        (canonicalPresentation (Opens.grothendieckTopology T) B'' C s')
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ B'' C s') U t' := by
  refine (comp_f_val_app _ _ _ _ _).trans ?_
  have h1 : ((spaceBaseChangeNaiveCotangentMap A B C a b).f (-1)).val.app U
      (towerUnitVal B C b _ U
        (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A _)
          (canonicalPresentation (Opens.grothendieckTopology T) A B a)
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A B a) U t)) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A _)
        (canonicalPresentation (Opens.grothendieckTopology T) A C (a ≫ b))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ A C (a ≫ b)) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A B C (𝟙 A) b).hom.app U
          t, kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ A A B C a (a ≫ b) (𝟙 A) b
              (Category.id_comp (a ≫ b)).symm)) U t.2⟩ := by
    unfold spaceBaseChangeNaiveCotangentMap baseChangeNaiveCotangentMap
    refine (extendScalars_comp_counit_f_towerUnitVal B C b _ (-1) U _).trans ?_
    exact naiveCotangentComplexMapOfSquare_f_negOne_conormalClassX _ _ _ _ _ _ _ _ _ _ _
  refine (congrArg _ h1).trans ?_
  unfold spaceNaiveCotangentComplexMapOfSquare
  refine (naiveCotangentComplexMapOfSquare_f_negOne_conormalClassX _ _ _ _ _ _ _ _ _ _ _).trans ?_
  exact congrArg (conormalClassX _ _ _ U) (Subtype.ext ht'.symm)

end SpaceBaseChange

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

open Stacks.NaiveCotangentFlatBaseChange

section BaseChangeMap

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
    (hbc : inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom)

/-- In degree `-1`, the composite of the pulled-back comparison, the base change map along the
structure map of `g'` and the map of the square through `bc` sends the unit image of the
conormal class of `t` to the conormal class of `t'`, the image of `t` under the inverse image,
the structure map of `g'` and `bc`. -/
theorem baseChangeComposite_f_negOne_unit_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
      (ringedSpaceStructureMap f.toLRSHom.toShHom)).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) X'.sheaf
      (ringedSpaceStructureMap f'.toLRSHom.toShHom)).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    ((((pulledNaiveCotangentComparison g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom ≫
        spaceBaseChangeNaiveCotangentMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫ spaceNaiveCotangentComplexMapOfSquare
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
          X'.toRingedSpace.sheaf X'.toRingedSpace.sheaf
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
            ringedSpaceStructureMap g'.toLRSHom.toShHom)
          (ringedSpaceStructureMap f'.toLRSHom.toShHom) bc (𝟙 _)
          (comp_id_eq_of_tower _ _ _ _ _ _ _ _ hbc)).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
              (ringedSpaceStructureMap f.toLRSHom.toShHom))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) X'.sheaf
          (ringedSpaceStructureMap f'.toLRSHom.toShHom))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' := by
  refine (comp_f_val_app _ _ _ _ _).trans ?_
  have hP := (congrArg (((pulledNaiveCotangentComparison g'.toLRSHom.toShHom
      f.toLRSHom.toShHom).hom.f (-1)).val.app ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj
          U)).hom
    (twoStepCompAdjunction_unit_val_app g'.toLRSHom.toShHom _ U
      (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
              (ringedSpaceStructureMap f.toLRSHom.toShHom))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t))).trans
    ((towerExtendScalars_map_towerUnitVal _ _ _ _ _ _).trans
      (congrArg (towerUnitVal _ _ _ _ _)
        (naiveCotangentComplexInverseImageMap_f_negOne_unit_conormalClassX
          g'.toLRSHom.toShHom.hom.base _ _ _ U t)))
  refine (congrArg _ hP).trans ?_
  exact spaceBaseChange_comp_square_f_negOne_towerUnitVal _ _ _ _ _ _ _ _ _ _ _ _ ht'

/-- In degree `-1`, the base change map `baseChangeMapOfComparison f f' g' bc hbc` sends the unit
image of the conormal class of `t` to the conormal class of `t'`, the image of `t` under the
inverse image, the structure map of `g'` and the comparison `bc` of base rings. -/
theorem baseChangeMapOfComparison_f_negOne_unit_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
      (ringedSpaceStructureMap f.toLRSHom.toShHom)).hom U)
    (t' : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) X'.sheaf
      (ringedSpaceStructureMap f'.toLRSHom.toShHom)).hom
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U))
    (ht' : t'.1 = (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
        X'.sheaf X'.sheaf bc (𝟙 _)).hom.app _
      ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom)).hom.app _
        ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base (inverseImagePresentationHom
          g'.toLRSHom.toShHom.hom.base
          (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf) U).hom t))) :
    (((baseChangeMapOfComparison f f' g' bc hbc).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
              (ringedSpaceStructureMap f.toLRSHom.toShHom))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) _)
        (canonicalPresentation (Opens.grothendieckTopology X'.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom) X'.sheaf
          (ringedSpaceStructureMap f'.toLRSHom.toShHom))
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) _ t' := by
  have hc := baseChangeComposite_f_negOne_unit_conormalClassX f f' g' bc hbc U t t' ht'
  refine Eq.mpr (congrArg (fun χ => ((χ.f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
              (ringedSpaceStructureMap f.toLRSHom.toShHom))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) = _)
    (show baseChangeMapOfComparison f f' g' bc hbc = (pulledNaiveCotangentComparison
        g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom ≫ spaceBaseChangeNaiveCotangentMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫
        eqToHom (congrArg
          (naiveCotangentComplex.{u, u, u, u}
            (Opens.grothendieckTopology X'.toRingedSpace.carrier)
            (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
            X'.toRingedSpace.sheaf) hbc) ≫
        spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
          X'.toRingedSpace.sheaf bc (ringedSpaceStructureMap f'.toLRSHom.toShHom) from rfl)) ?_
  refine Eq.mpr (congrArg (fun χ => ((((pulledNaiveCotangentComparison g'.toLRSHom.toShHom
      f.toLRSHom.toShHom).hom ≫ spaceBaseChangeNaiveCotangentMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫ χ).f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) _)
            (canonicalPresentation (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRingOnMiddle f.toLRSHom.toShHom) X.sheaf
              (ringedSpaceStructureMap f.toLRSHom.toShHom))
            (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t)) : _) = _)
    (eqToHom_comp_spaceRelativeNaiveCotangentComplexMap
    (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (inverseImageMiddleRing g'.toLRSHom.toShHom)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f'.toLRSHom.toShHom)
    X'.toRingedSpace.sheaf (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (ringedSpaceStructureMap g'.toLRSHom.toShHom) bc
    (ringedSpaceStructureMap f'.toLRSHom.toShHom) hbc)) ?_
  exact hc

end BaseChangeMap

end Stacks.NaiveCotangentPulledImmersion

end PartP3

section PartP5

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)

namespace Stacks.NaiveCotangentPulledImmersion

section PulledExt

variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)
  {R A : CategoryTheory.Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
  (a : R ⟶ A) (φ : A ⟶ X.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) φ.hom]

/-- **Maps out of the pullback of a degree `-1` term identified with a conormal sheaf are
determined by their values on the images under the unit of conormal classes.** -/
theorem twoStepPullback_hom_ext_conormalClassX {K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ}
    (e : K.X (-1) = (conormalSequence.{u, u, u, u} _ R A X.sheaf a φ).X₁)
    {N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X'.carrier) X'.sheaf)}
    {f₁ f₂ : (twoStepPullback g').obj (K.X (-1)) ⟶ N}
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U),
      f₁.val.app ((Opens.map g'.hom.base).op.obj U)
          (((twoStepCompAdjunction g').unit.app _).val.app U (conormalClassX a φ e U s)) =
        f₂.val.app ((Opens.map g'.hom.base).op.obj U)
          (((twoStepCompAdjunction g').unit.app _).val.app U (conormalClassX a φ e U s))) :
    f₁ = f₂ := by
  apply ((twoStepCompAdjunction g').homEquiv _ _).injective
  refine (cancel_epi (eqToHom e.symm)).mp ?_
  refine conormal_hom_ext φ _ (fun U s => ?_)
  exact ((twoStepCompAdjunction_homEquiv_val_app g' _ _ f₁ U (conormalClassX a φ e U s)).trans
    (h U s)).trans (twoStepCompAdjunction_homEquiv_val_app g' _ _ f₂ U _).symm

end PulledExt

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

section RestrictId

variable {T : TopCat.{u}} (B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})

/-- Composing a chain map `φ` with the identification of the restriction of scalars along
`𝟙 B` with the identity does not change its values on sections. -/
theorem comp_eqToHom_restrictScalars_id_f_val_app
    {M K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    (φ : M ⟶ ((_root_.SheafOfModules.restrictScalars
        (underlyingRingHomOfSite.{u, u, u} (𝟙 B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
    (i : ℤ) (U : (Opens T)ᵒᵖ)
    (x : (M.X i).val.obj U) :
    ((φ ≫ eqToHom (mapHomologicalComplex_restrictScalars_id B K)).f i).val.app U x =
      ((φ.f i).val.app U x : (K.X i).val.obj U) :=
  rfl

end RestrictId

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

section SchemePresentation

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [SurjectiveOnStalks i]

/-- The kernel ideal of the canonical presentation of `𝒪_X` over `(i ≫ h)⁻¹𝒪_Y` is carried
into that over `i⁻¹h⁻¹𝒪_Y` by the comparison of base rings. -/
theorem schemePresentationIso_hom_f_negOne_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))).hom U) :
    (((Stacks.NaiveCotangentTower.schemePresentationIso i h).hom.f (-1)).val.app U
        (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t) : _) =
      conormalClassX (canonicalCoefficientMap i h) (towerCanonicalPresentation i h)
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageSheaf (ringedSpaceHom (i ≫ h)))
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).hom (𝟙 _)).hom.app U t,
          kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ _ _ _ _ _ _ _ _
              ((Category.comp_id _).trans
                (inverseImageCompIso_hom_comp (ringedSpaceHom i) (ringedSpaceHom h)).symm))) U
            t.2⟩ := by
  unfold Stacks.NaiveCotangentTower.schemePresentationIso naiveCotangentComplexCompIsoOfEq
    naiveCotangentComplexCompIso
  simp only [Iso.trans_hom, eqToIso.hom]
  refine (comp_f_val_app _ _ _ _ _).trans ?_
  refine (comp_eqToHom_restrictScalars_id_f_val_app _ _ _ _ _).trans ?_
  exact naiveCotangentComplexMapOfSquare_f_negOne_conormalClassX _ _ _ _ _ _ _ _ _ _ _

end SchemePresentation

end Stacks.NaiveCotangentPulledImmersion

end PartP5

section PartP6

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

namespace Stacks.NaiveCotangentPulledImmersion

section Bare

/-- A composite of two maps read through a functor, after a map into the source, in a bare
category. -/
theorem comp_map_comp_eq {S T : Type*} [Category S] [Category T] (F : S ⥤ T) {E E' : T}
    {B₁ B₂ B₃ : S} (v : E ⟶ F.obj B₁) (a : B₁ ⟶ B₂) (b : B₂ ⟶ B₃) (v' : E ⟶ F.obj B₂)
    (e : E ⟶ E') (w : E' ⟶ F.obj B₃) (ha : v ≫ F.map a = v') (hb : v' ≫ F.map b = e ≫ w) :
    v ≫ F.map (a ≫ b) = e ≫ w := by
  rw [F.map_comp, ← Category.assoc, ha, hb]

/-- The transpose of `F e⁻¹ ≫ b ≫ e'` followed by `G e'⁻¹` is `e⁻¹` followed by the unit and
`G b`, in bare categories. -/
theorem homEquiv_comp_map_inv_eq {D D' : Type*} [Category D] [Category D'] {F : D ⥤ D'}
    {G : D' ⥤ D} (adj : F ⊣ G) {R S : D} (e : S ≅ R) {R' S' : D'} (e' : S' ≅ R')
    (b : F.obj S ⟶ S') :
    adj.homEquiv _ _ (F.map e.inv ≫ b ≫ e'.hom) ≫ G.map e'.inv =
      e.inv ≫ adj.unit.app S ≫ G.map b := by
  rw [Adjunction.homEquiv_unit, Category.assoc, ← G.map_comp, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, G.map_comp, ← Category.assoc, Adjunction.unit_naturality,
    Category.assoc]

/-- The coefficient chain of `presentationRingMap_comp_evaluation`, in a bare category. -/
theorem coeff_chain_eq {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {R S RX SX : D} {R' S' T' FS Z' : D'} (btm : R ⟶ G.obj R') (ei' : R' ⟶ S') (cS' : S' ⟶ T')
    (cX : R ⟶ RX) (κ : RX ⟶ SX) (ι : SX ⟶ G.obj Z') (Φ : Z' ⟶ T') (ei : R ⟶ S)
    (cS : S ⟶ SX) (u : S ⟶ G.obj FS) (cFS : FS ⟶ Z') (bc : FS ⟶ S')
    (hbtm : btm ≫ G.map ei' = ei ≫ u ≫ G.map bc) (h₁ : cX ≫ κ = ei ≫ cS)
    (h₂ : cS ≫ ι = u ≫ G.map cFS) (h₃ : cFS ≫ Φ = bc ≫ cS') :
    btm ≫ G.map (ei' ≫ cS') = cX ≫ κ ≫ ι ≫ G.map Φ := by
  rw [G.map_comp, ← Category.assoc, hbtm, ← Category.assoc cX, h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, ← G.map_comp cFS, h₃, G.map_comp]

/-- Two composable maps in a row, each of which is known on a map into its source, in a bare
category. -/
theorem comp_comp_eq_of_parts {D : Type*} [Category D] {A B C E E' : D} (v : A ⟶ B)
    (k₁ : B ⟶ C) (k₂ : C ⟶ E) (w₁ : A ⟶ C) (x : A ⟶ E') (w₂ : E' ⟶ E) (h₁ : v ≫ k₁ = w₁)
    (h₂ : w₁ ≫ k₂ = x ≫ w₂) : v ≫ k₁ ≫ k₂ = x ≫ w₂ := by
  rw [← Category.assoc, h₁, h₂]

/-- The variable chain of `presentationRingMap_comp_evaluation`, in a bare category. -/
theorem var_chain_eq {S T : Type*} [Category S] [Category T] (F : S ⥤ T) {RX SX Z W : S}
    {E EX M N N' : T} (tg : E ⟶ EX) (vX : EX ⟶ F.obj RX) (κ : RX ⟶ SX) (ι : SX ⟶ Z)
    (Φ : Z ⟶ W) (v₁ : E ⟶ M) (a' : M ⟶ F.obj W) (vS : EX ⟶ F.obj SX) (u : EX ⟶ N)
    (pv : N ⟶ F.obj Z) (ps : N ⟶ N') (pv' : N' ⟶ F.obj W) (su : EX ⟶ N')
    (hκ : vX ≫ F.map κ = vS) (hι : vS ≫ F.map ι = u ≫ pv) (hΦ : pv ≫ F.map Φ = ps ≫ pv')
    (hsu : u ≫ ps = su) (hL : v₁ ≫ a' = tg ≫ su ≫ pv') :
    v₁ ≫ a' = (tg ≫ vX) ≫ F.map (κ ≫ ι ≫ Φ) := by
  rw [hL, Category.assoc, F.map_comp, F.map_comp, ← Category.assoc vX, hκ, ← Category.assoc vS, hι,
    Category.assoc, hΦ, ← Category.assoc u, hsu]

/-- A commutative square read through a functor, in a bare category. -/
theorem map_comp_map_eq {T T' : Type*} [Category T] [Category T'] (PF : T' ⥤ T) {A B C D : T'}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D) (d : D ⟶ C) (h : a ≫ b = c ≫ d) :
    PF.map a ≫ PF.map b = PF.map c ≫ PF.map d := by
  rw [← PF.map_comp, h, PF.map_comp]

end Bare

section FreeAlgebraSquares

variable {T : TopCat.{u}} (R S B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u})
  (E : (Opens T)ᵒᵖ ⥤ Type u)

/-- Evaluating the variables and then changing the coefficients along `e` is `e` on
coefficients. -/
theorem coefficientMap_comp_freeAlgebraMap_comp_square (τ : E ⟶
      underlyingPresheaf (Opens.grothendieckTopology T) B) (e : R ⟶ S) :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R E ≫
        freeAlgebraMap (Opens.grothendieckTopology T) R E
          (underlyingPresheaf (Opens.grothendieckTopology T) B) τ ≫
        canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R S B B e (𝟙 B) =
      e ≫ freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) S
        (underlyingPresheaf (Opens.grothendieckTopology T) B) := by
  rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
    freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare]

/-- Changing the coefficients along `e` fixes the variables. -/
theorem variable_comp_square_id (e : R ⟶ S) :
    freeAlgebraSheafVariable (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) B) ≫
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology T) CommRingCat.{u}).map
          (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R S B B e (𝟙 B)))
          (forget CommRingCat.{u}) =
      freeAlgebraSheafVariable (Opens.grothendieckTopology T) S
        (underlyingPresheaf (Opens.grothendieckTopology T) B) := by
  rw [freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, underlyingPresheafMap,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.whiskerRight_id']
  exact Category.id_comp _

/-- Evaluating the variables along `τ` and then changing the coefficients sends the variable
`[x]` to the variable `[τ x]`. -/
theorem variable_comp_freeAlgebraMap_comp_square (τ : E ⟶
      underlyingPresheaf (Opens.grothendieckTopology T) B) (e : R ⟶ S) :
    freeAlgebraSheafVariable (Opens.grothendieckTopology T) R E ≫
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology T) CommRingCat.{u}).map
          (freeAlgebraMap (Opens.grothendieckTopology T) R E
            (underlyingPresheaf (Opens.grothendieckTopology T) B) τ ≫
          canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R S B B e (𝟙 B)))
          (forget CommRingCat.{u}) =
      τ ≫ freeAlgebraSheafVariable (Opens.grothendieckTopology T) S
        (underlyingPresheaf (Opens.grothendieckTopology T) B) := by
  rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
    freeAlgebraSheafVariable_comp_freeAlgebraMap, Category.assoc, variable_comp_square_id]

/-- Changing the variables along `β` and then the coefficients along `e` is `e` on
coefficients. -/
theorem coefficientMap_comp_square_comp_square (β : B ⟶ B') (e : R ⟶ S) :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) B) ≫
        canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R R B B' (𝟙 R) β ≫
        canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R S B' B' e (𝟙 B') =
      e ≫ freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) S
        (underlyingPresheaf (Opens.grothendieckTopology T) B') := by
  rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
    Category.id_comp, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare]

/-- Changing the variables along `β` and then the coefficients sends the variable `[b]` to the
variable `[β b]`. -/
theorem variable_comp_square_comp_square (β : B ⟶ B') (e : R ⟶ S) :
    freeAlgebraSheafVariable (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) B) ≫
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology T) CommRingCat.{u}).map
          (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R R B B' (𝟙 R) β ≫
          canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) R S B' B' e (𝟙 B')))
          (forget CommRingCat.{u}) =
      underlyingPresheafMap (Opens.grothendieckTopology T) B B' β ≫
        freeAlgebraSheafVariable (Opens.grothendieckTopology T) S
          (underlyingPresheaf (Opens.grothendieckTopology T) B') := by
  rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
    freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, Category.assoc, variable_comp_square_id]

end FreeAlgebraSquares

section InverseImageVariable

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (A B : TopCat.Sheaf CommRingCat.{u} X)

/-- The transposed identification `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])` carries the variable `[b]` to the
variable at the inverse-image section of `b`. -/
theorem freeAlgebraSheafVariable_comp_inverseImagePresentationHom :
    freeAlgebraSheafVariable (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map
          (inverseImagePresentationHom f A B)) (forget CommRingCat.{u}) =
      Functor.whiskerRight
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom
          (forget CommRingCat.{u}) ≫
        (TopCat.Presheaf.pushforward (Type u) f).map
          (freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            (underlyingPresheaf (Opens.grothendieckTopology Y)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) := by
  refine (freeAlgebraSheafVariable_comp_homEquiv f A
    (underlyingPresheaf (Opens.grothendieckTopology X) B) _ (underlyingInverseImageIso f A
        B).hom).trans
    ?_
  refine (congrArg ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _)
    (comp_map_comp_eq (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget CommRingCat.{u})) _ _ _ _ _ _
      (inverseImageVariable_comp_inverseImageHom f A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (freeAlgebraSheafVariable_comp_map (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) (toUnderlyingInverseImage f B)))).trans ?_
  exact toUnderlyingInverseImage_comp_homEquiv f B _ _

end InverseImageVariable

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

section RingIdentity

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

omit [IsImmersion i] [IsImmersion i'] in
/-- **The ring identity behind the degree `-1` comparison of the base change map with the
polynomial presentations.**  The two ways of sending a polynomial over `i⁻¹h⁻¹𝒪_Y` in the
sections of `i⁻¹𝒪_P` to a polynomial over `(i' ≫ h')⁻¹𝒪_{Y'}` in the sections of `𝒪_{X'}`
agree: through the morphism of presentations of the square followed by evaluation in `𝒪_{X'}`
and the comparison of base rings, or through evaluation in `𝒪_X`, the comparison of base rings,
the inverse image and the two maps of canonical presentations making up the base change map. -/
theorem presentationRingMap_comp_evaluation (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    presentationRingMap i h i' h' g' p g hip w ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
          (evaluationRingMap i' h' ≫
            canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
              (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
              (inverseImageSheaf (ringedSpaceHom (i' ≫ h'))) X'.sheaf X'.sheaf
              (inverseImageCompIso (ringedSpaceHom i') (ringedSpaceHom h')).inv (𝟙 _)) =
      evaluationRingMap i h ≫
        canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _) ≫
        inverseImagePresentationHom g'.base (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
          (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
              (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
              (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
              (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.sheaf (𝟙 _)
              (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫
            canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X'.carrier)
              (inverseImageBaseRing g'.toLRSHom.toShHom (i ≫ h).toLRSHom.toShHom)
              (inverseImageSheaf (ringedSpaceHom (i' ≫ h'))) X'.sheaf X'.sheaf
              (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
              (𝟙 _)) := by
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · exact coeff_comp_eq_of_parts (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _) _
      (coefficientMap_comp_freeAlgebraMap_comp_square _ _ _ _ _ _) _
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap _ _ _ _ _)
      (coeff_chain_eq (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base)
        _ _ _ _ _ _ _ _ _ _ _ _
        (homEquiv_comp_map_inv_eq
          (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base)
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageCompIso (ringedSpaceHom i') (ringedSpaceHom h'))
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w))
        (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare _ _ _ _ _ _ _)
        (freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom _ _ _)
        (coefficientMap_comp_square_comp_square _ _ _ _ _ _))
  · refine var_comp_eq_of_parts
      (sheafToPresheaf _ CommRingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget CommRingCat.{u}))
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _) _
      ((Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg (Functor.whiskerLeft _)
        (variable_comp_freeAlgebraMap_comp_square _ _ _ _ _ _)))
      _ (freeAlgebraSheafVariable_comp_freeAlgebraMap _ _ _ _ _) ?_
    refine var_chain_eq (sheafToPresheaf _ CommRingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget CommRingCat.{u}))
      (W := (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom (i' ≫ h')))
          (underlyingPresheaf (Opens.grothendieckTopology X'.carrier) X'.sheaf)))
      _ _ _ _ _ _ _ _ _ _
      ((TopCat.Presheaf.pushforward (Type u) g'.base).map
        (underlyingPresheafMap (Opens.grothendieckTopology X'.carrier)
          (inverseImageMiddleRing (ringedSpaceHom g')) X'.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom g'))))
      ((TopCat.Presheaf.pushforward (Type u) g'.base).map
        (freeAlgebraSheafVariable (Opens.grothendieckTopology X'.carrier)
          (inverseImageSheaf (ringedSpaceHom (i' ≫ h')))
          (underlyingPresheaf (Opens.grothendieckTopology X'.carrier) X'.sheaf)))
      (Functor.whiskerRight (Stacks.Sheaves.RingedSpaceDifferentials.structureSheafMap
        (ringedSpaceHom g')).hom (forget CommRingCat.{u}))
      (variable_comp_square_id _ _ _ _)
      (freeAlgebraSheafVariable_comp_inverseImagePresentationHom _ _ _) ?_ ?_ ?_
    · exact map_comp_map_eq (TopCat.Presheaf.pushforward (Type u) g'.base) _ _ _ _
        (variable_comp_square_comp_square _ _ _ _ _ _)
    · exact (Functor.whiskerRight_comp _ _ _).symm.trans (congrArg (fun t =>
        Functor.whiskerRight t.hom (forget CommRingCat.{u}))
        (unit_comp_map_ringedSpaceStructureMap (ringedSpaceHom g')))
    · exact (congrArg (_ ≫ ·) (Functor.whiskerLeft_comp _ _ _)).trans
        (comp_comp_eq_of_parts _ _ _ _ _ _
          ((Functor.whiskerRight_comp _ _ _).symm.trans ((congrArg (fun t =>
            Functor.whiskerRight t.hom (forget CommRingCat.{u}))
            (middleRingMap_comp i i' g' p hip)).trans (Functor.whiskerRight_comp _ _ _)))
          (Category.assoc _ _ _))

end RingIdentity

end Stacks.NaiveCotangentPulledImmersion

end PartP6

section PartP7

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

namespace Stacks.NaiveCotangentPulledImmersion

section UnitClass

variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)
  {R A : CategoryTheory.Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
  (a : R ⟶ A) (φ : A ⟶ X.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) φ.hom]
  {R' A' : CategoryTheory.Sheaf (Opens.grothendieckTopology X'.carrier) CommRingCat.{u}}
  (a' : R' ⟶ A') (φ' : A' ⟶ X'.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier) φ'.hom]

/-- A map out of the two-step pullback of a degree `-1` term identified with a conormal sheaf,
which is up to the identifications a map `c` of conormal sheaves, carries the image under the
unit of a conormal class to the class `c` carries it to. -/
theorem map_unitC_conormalClassX {K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ}
    {L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.carrier) X'.sheaf)) ℤ}
    (eK : K.X (-1) = (conormalSequence.{u, u, u, u} _ R A X.sheaf a φ).X₁)
    (eL : L.X (-1) = (conormalSequence.{u, u, u, u} _ R' A' X'.sheaf a' φ').X₁)
    (m : (twoStepPullback g').obj (K.X (-1)) ⟶ L.X (-1))
    (c : (twoStepPullback g').obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier) A X.sheaf φ) ⟶
      conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) A' X'.sheaf φ')
    (hm : m = (twoStepPullback g').map (eqToHom eK) ≫ c ≫ eqToHom eL.symm)
    (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal φ.hom U)
    (t : kernelIdeal φ'.hom ((Opens.map g'.hom.base).op.obj U))
    (hc : c.val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app _).val.app U
          (conormalClass.{u, u, u, u} _ R A X.sheaf a φ U s)) =
      conormalClass.{u, u, u, u} _ R' A' X'.sheaf a' φ' _ t) :
    m.val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app _).val.app U (conormalClassX a φ eK U s)) =
      conormalClassX a' φ' eL _ t := by
  subst hm
  have h2 := (twoStepPullback_map_unit_val_app g' (eqToHom eK) U (conormalClassX a φ eK U s)).trans
    (congrArg (((twoStepCompAdjunction g').unit.app _).val.app U).hom
      (eqToHom_val_app_conormalClassX a φ eK U s))
  exact congrArg ((eqToHom eL.symm).val.app _).hom ((congrArg (c.val.app _).hom h2).trans hc)

end UnitClass

section Generic

/-- If an isomorphism `e` of complexes sends `x` to `y` in degree `i`, then `e.inv` sends `y` to
`x`. -/
theorem iso_inv_f_val_app_of_hom {T : TopCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    (e : K ≅ L) (i : ℤ) (U : (Opens T)ᵒᵖ) (x : (K.X i).val.obj U) (y : (L.X i).val.obj U)
    (h : (e.hom.f i).val.app U x = y) : (e.inv.f i).val.app U y = x := by
  subst h
  exact congrArg (fun φ => (φ.f i).val.app U x) e.hom_inv_id

/-- A composite `f ≫ g` of maps of sheaves of modules acts on sections as `g` after `f`. -/
theorem comp_val_app {T : TopCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {M N Q : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)}
    (f : M ⟶ N) (g : N ⟶ Q) (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) :=
  rfl

/-- The pullback along `g'` of a chain map `φ` sends the unit image of a section `x` to the unit
image of `φ x`. -/
theorem pulledComplexFunctor_map_f_unitC {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)
    {K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ}
    (φ : K ⟶ L) (i : ℤ) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X i).val.obj U) :
    (((pulledComplexFunctor g').map φ).f i).val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app _).val.app U x) =
      ((twoStepCompAdjunction g').unit.app _).val.app U ((φ.f i).val.app U x) :=
  twoStepPullback_map_unit_val_app g' (φ.f i) U x

end Generic

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

section SchemePresentationInv

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [SurjectiveOnStalks i]

/-- Changing the coefficients of a polynomial along `e.inv` and then along `e.hom` returns it. -/
theorem canonicalFreeAlgebraMapOfSquare_inv_hom_apply {T : TopCat.{u}}
    {A A' B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}} (e : A ≅ A')
    (U : (Opens T)ᵒᵖ) (t : (freeAlgebraSheaf (Opens.grothendieckTopology T) A'
      (underlyingPresheaf (Opens.grothendieckTopology T) B)).obj.obj U) :
    (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A' B B e.hom (𝟙 B)).hom.app U
        ((canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A' A B B e.inv
          (𝟙 B)).hom.app U t) = t := by
  have h := canonicalFreeAlgebraMapOfSquare_comp (Opens.grothendieckTopology T) A' A A' B B B
    e.inv e.hom (𝟙 B) (𝟙 B)
  rw [e.inv_hom_id, Category.comp_id, canonicalFreeAlgebraMapOfSquare_id] at h
  exact congrArg (fun φ => (φ.hom.app U).hom t) h

omit [SurjectiveOnStalks i] in
/-- The structure map of `𝒪_X` over `i⁻¹h⁻¹𝒪_Y` factors through the inverse of the comparison
`(i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y` and the structure map over `(i ≫ h)⁻¹𝒪_Y`. -/
theorem inverseImageCompIso_inv_square :
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
        ringedSpaceStructureMap (ringedSpaceHom i)) ≫ 𝟙 X.sheaf =
      (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv ≫
        ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)) :=
  (Category.comp_id _).trans ((Iso.inv_hom_id_assoc
    (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)) _).symm.trans
      (congrArg (fun t => (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv ≫ t)
        (inverseImageCompIso_hom_comp (ringedSpaceHom i) (ringedSpaceHom h))))

/-- The inverse of `Stacks.NaiveCotangentTower.schemePresentationIso` in degree `-1` on conormal
classes. -/
theorem schemePresentationIso_inv_f_negOne_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (t : kernelIdeal (towerCanonicalPresentation i h).hom U) :
    (((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv.f (-1)).val.app U
        (conormalClassX (canonicalCoefficientMap i h) (towerCanonicalPresentation i h)
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U t) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U t,
          kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ _ _ _ _ _ _ _ _
              (inverseImageCompIso_inv_square i h))) U t.2⟩ := by
  refine iso_inv_f_val_app_of_hom _ _ _ _ _ ?_
  refine (schemePresentationIso_hom_f_negOne_conormalClassX i h U _).trans ?_
  exact congrArg (conormalClassX _ _ _ U) (Subtype.ext
    (canonicalFreeAlgebraMapOfSquare_inv_hom_apply _ U t.1))

end SchemePresentationInv

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

section PulledPresentationClass

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- **The degree `-1` comparison of the pulled-back presentations on unit classes**: it carries
the image under the unit of the class of a polynomial relation `s` to the class of the image of
`s` under the morphism of presentations of the square. -/
theorem pulledPresentationNegOne_unit_conormalClassX (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    ((pulledPresentationNegOne i h i' h' g' p g hip w).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
            (towerPresentationComplex_X_negOne i h) U s)) : _) =
      conormalClassX (towerCoefficientMap i' h') (towerPresentation i' h')
        (towerPresentationComplex_X_negOne i' h') _
        ⟨(presentationRingComparison i h i' h' g' p g hip w).hom.app _
            ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                g'.toLRSHom.toShHom.hom.base).unit.app _) U).hom s.1),
          kernelIdeal_le_comap_square _ _ _ _
            (hom_of_square (presentationRingComparison_comp i h i' h' g' p g hip w)) _
            (kernelIdeal_le_comap_sectionsMapAlong g'.toLRSHom.toShHom.hom.base X.sheaf _ _ _
              (unit_comp_pushforward_pullback_map g'.toLRSHom.toShHom _) U s.2)⟩ :=
  map_unitC_conormalClassX g'.toLRSHom.toShHom _ _ _ _ _ _ _ _ rfl U s _
    (pulledConormalSheafMap_unit_conormalClass g'.toLRSHom.toShHom (towerPresentation i h)
      (towerPresentation i' h') (presentationRingComparison i h i' h' g' p g hip w)
      (presentationRingComparison_comp i h i' h' g' p g hip w) _ (towerCoefficientMap i h) _
      (towerCoefficientMap i' h') U s)

end PulledPresentationClass

end Stacks.NaiveCotangentPulledImmersion

end PartP7

section PartP8

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.NaiveCotangentFlatBaseChange

namespace Stacks.NaiveCotangentPulledImmersion

section PresentationToNaiveCotangent

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i]

/-- The evaluation of a polynomial relation `s`, read over `(i ≫ h)⁻¹𝒪_Y`, lies in the kernel
ideal of the canonical presentation of `𝒪_X` over `(i ≫ h)⁻¹𝒪_Y`. -/
theorem evaluation_comp_inv_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
            ((evaluationRingMap i h).hom.app U s) ∈
      kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.carrier)
        (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))).hom U :=
  kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
    (freeAlgebraMapOfSquare_comp_canonicalPresentation _ _ _ _ _ _ _ _ _
      (inverseImageCompIso_inv_square i h))) U (evaluationRingMap_mem_kernelIdeal i h U s)

/-- The comparison of the polynomial presentation with `NL_{X/Y}` in degree `-1` on conormal
classes: the class of a polynomial relation goes to the class of its evaluation, read over
`(i ≫ h)⁻¹𝒪_Y`. -/
theorem presentationToNaiveCotangent_f_negOne_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    (((presentationToNaiveCotangent i h).f (-1)).val.app U
        (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
          (towerPresentationComplex_X_negOne i h) U s) : _) =
      conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
            ((evaluationRingMap i h).hom.app U s),
          kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ _ _ _ _ _ _ _ _
              (inverseImageCompIso_inv_square i h))) U
            (evaluationRingMap_mem_kernelIdeal i h U s)⟩ :=
  (comp_f_val_app (presentationComparison i h)
    (Stacks.NaiveCotangentTower.schemePresentationIso i h).inv (-1) U _).trans
    ((congrArg _ (presentationComparison_conormalClassX i h U s)).trans
      (schemePresentationIso_inv_f_negOne_conormalClassX i h U
        ⟨(evaluationRingMap i h).hom.app U s, evaluationRingMap_mem_kernelIdeal i h U s⟩))

variable {X' : Scheme.{u}} (g' : X' ⟶ X)

/-- The pullback along `g'` of `presentationToNaiveCotangent` in degree `-1` on unit classes. -/
theorem pulled_presentationToNaiveCotangent_f_negOne_unit (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    ((((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h) ≫
          (pulledComplexFunctor g'.toLRSHom.toShHom).map
            ((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv :
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
                ringedSpaceStructureMap (ringedSpaceHom i)) ⟶
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))) :
          (pulledComplexFunctor g'.toLRSHom.toShHom).obj (towerPresentationComplex i h) ⟶
            Stacks.NaiveCotangentFlatBaseChange.pulledComplex (i ≫ h) g').f (-1)).val.app
        ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U)
        (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
          (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
            (towerPresentationComplex_X_negOne i h) U s)) : _) =
      ((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U
        (conormalClassX (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) _)
          (canonicalPresentation (Opens.grothendieckTopology X.carrier)
            (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))
          (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf X.sheaf
          (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv (𝟙 _)).hom.app U
            ((evaluationRingMap i h).hom.app U s),
          kernelIdeal_le_comap_square _ _ _ _ (hom_of_square
            (freeAlgebraMapOfSquare_comp_canonicalPresentation _ _ _ _ _ _ _ _ _
              (inverseImageCompIso_inv_square i h))) U
            (evaluationRingMap_mem_kernelIdeal i h U s)⟩) :=
  (comp_f_val_app ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h))
    ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      ((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv :
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
                ringedSpaceStructureMap (ringedSpaceHom i)) ⟶
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h))))) (-1)
    ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U) _).trans
    ((congrArg _ ((pulledComplexFunctor_map_f_unitC g'.toLRSHom.toShHom
        (presentationComparison i h) (-1) U _).trans
      (congrArg _ (presentationComparison_conormalClassX i h U s)))).trans
    ((pulledComplexFunctor_map_f_unitC g'.toLRSHom.toShHom
        ((Stacks.NaiveCotangentTower.schemePresentationIso i h).inv :
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
                ringedSpaceStructureMap (ringedSpaceHom i)) ⟶
            naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
              (inverseImageSheaf (ringedSpaceHom (i ≫ h))) X.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom (i ≫ h)))) (-1) U _).trans
      (congrArg _ (schemePresentationIso_inv_f_negOne_conormalClassX i h U
        ⟨(evaluationRingMap i h).hom.app U s, evaluationRingMap_mem_kernelIdeal i h U s⟩))))

end PresentationToNaiveCotangent

section PulledRelation

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- The image of a polynomial relation under the morphism of presentations of the square. -/
def pulledRelation (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g)
    (U : (Opens X.carrier)ᵒᵖ) (s : kernelIdeal (towerPresentation i h).hom U) :
    kernelIdeal (towerPresentation i' h').hom ((Opens.map g'.toLRSHom.toShHom.hom.base).op.obj U) :=
  ⟨(presentationRingComparison i h i' h' g' p g hip w).hom.app _
            ((sectionsMapAlong g'.toLRSHom.toShHom.hom.base
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                g'.toLRSHom.toShHom.hom.base).unit.app _) U).hom s.1),
          kernelIdeal_le_comap_square _ _ _ _
            (hom_of_square (presentationRingComparison_comp i h i' h' g' p g hip w)) _
            (kernelIdeal_le_comap_sectionsMapAlong g'.toLRSHom.toShHom.hom.base X.sheaf _ _ _
              (unit_comp_pushforward_pullback_map g'.toLRSHom.toShHom _) U s.2)⟩

end PulledRelation

end Stacks.NaiveCotangentPulledImmersion

end PartP8

end
