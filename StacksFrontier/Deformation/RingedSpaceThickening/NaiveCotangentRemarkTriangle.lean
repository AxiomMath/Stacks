module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangle
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackNaiveCotangentMap
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTriangleObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentRemarkConditional
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
import StacksCore.Tactic.StacksAttribute

/-!
# The maps of Stacks 0GQ4 are close to forming a distinguished triangle

In the situation of **Stacks 0GQ3** (a first order thickening `t : S ⟶ S'` and `f : X ⟶ S`),
**Stacks 0GQ4** displays the maps `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` (the source's
`𝖭𝖫_{S'/S}` is a typo for `𝖭𝖫_{S/S'}`) and says they are close to forming a distinguished
triangle, by **Stacks 0E1Z**.  This file states and proves what that means:
`naiveCotangentRemark_closeToDistinguishedTriangle`.

The first map is the canonical map of **Stacks 0GQ1** (`derivedPullbackNaiveCotangentMap`), built
from the presentations by all sections; **Stacks 0E1Z** is built from the canonical
presentations through **Stacks 08TM**.  The main work is the comparison
`pulledNaiveCotangentModelIso_hom_comp_pulledNaiveCotangentMap` of the two canonical maps
`f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, degree by degree on generating sections.

## References

* [Stacks Project, Tag 0GQ4](https://stacks.math.columbia.edu/tag/0GQ4)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace CochainComplex
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)

universe u

attribute [local instance 10000] HasDerivedCategory.standard


namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')

/-- `𝖭𝖫_{S/S'}`, the naive cotangent complex of the base thickening, as a complex. -/
abbrev baseNaiveCotangent : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ :=
  (show CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ from
        PresentedSquareZeroExtension.relativeComplex t)

/-- The degreewise pullback `f^*𝖭𝖫_{S/S'}` along `f^*` is, termwise through
`modulePullbackIsoTwoStep`, the model `pulledNaiveCotangentComplex f t` of **Stacks 0E1Z**. -/
def pulledNaiveCotangentModelIso :
    ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (baseNaiveCotangent t) ≅
      Stacks.SheafOfModules.pulledNaiveCotangentComplex f t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (modulePullbackIsoTwoStep f).app ((baseNaiveCotangent t).X i))
    (fun i j _ => ((modulePullbackIsoTwoStep f).hom.naturality ((baseNaiveCotangent t).d i j)).symm)


section E2gen

variable {T : TopCat.{u}} {A₀ A' B C : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

/-- A change of base ring followed by the relative map of a tower is the relative map of the
factorised tower. -/
theorem mapOfSquare_comp_relative_of_fac (a₀ : A₀ ⟶ B) (a' : A' ⟶ B) (b : B ⟶ C) (s : A₀ ⟶ C)
    (ι : A₀ ⟶ A') (hs : s = a₀ ≫ b) (hι : ι ≫ a' = a₀)
    (hsq : s ≫ 𝟙 C = ι ≫ a' ≫ b) :
    Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u}
        (Opens.grothendieckTopology T) A₀ C s A' C (a' ≫ b) ι (𝟙 C) hsq ≫
      eqToHom (Stacks.SheafOfModules.mapHomologicalComplex_restrictScalars_id C _) ≫
      Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap A' B C a' b =
      eqToHom (congrArg (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology T) A₀ C) hs) ≫
        Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap A₀ B C a₀ b := by
  subst hs
  subst hι
  rw [eqToHom_refl, Category.id_comp]
  have key := Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_comp.{u, u, u, u}
    (Opens.grothendieckTopology T) A₀ C _ A' C (a' ≫ b) ι (𝟙 C) hsq B C b a' (𝟙 C)
    (Stacks.SheafOfModules.comp_id_eq_comp_of_fac _ _ _ _ _ _ _ rfl)
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ i) key
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f] at this ⊢
  exact this

end E2gen

/-- The transpose of `inverseImageCompIso` along `(f ≫ t)⁻¹ ⊣ (f ≫ t)_*` is the unit of the
composite adjunction. -/
private theorem homEquiv_inverseImageCompIso_hom :
    (Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction (f ≫ t)).homEquiv _ _
        (Stacks.SheafOfModules.inverseImageCompIso f t).hom =
      ((Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction t).comp
        (Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction f)).unit.app S'.sheaf :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _

open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap
  structureSheafMap_comp homEquiv_inverseImageStructureMap) in
/-- The identification `(f ≫ t)⁻¹𝒪_{S'} ≅ f⁻¹t⁻¹𝒪_{S'}` followed by `f⁻¹` of the structure map of
`t` is the ring map `baseInverseImageRingMap f t` through which `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` is
taken. -/
theorem inverseImageCompIso_hom_comp_inverseImageFirstRingMap :
    (Stacks.SheafOfModules.inverseImageCompIso f t).hom ≫
        Stacks.SheafOfModules.inverseImageFirstRingMap f t = baseInverseImageRingMap f t := by
  apply ((sheafAdjunction (f ≫ t)).homEquiv S'.sheaf (inverseImageSheaf f)).injective
  rw [baseInverseImageRingMap, Equiv.apply_symm_apply]
  refine ((sheafAdjunction (f ≫ t)).homEquiv_naturality_right _ _).trans ?_
  have h1 := homEquiv_inverseImageCompIso_hom f t
  refine (congrArg (· ≫ _) h1).trans ?_
  rw [Adjunction.comp_unit_app]
  have h2 := (sheafAdjunction f).unit.naturality (Stacks.SheafOfModules.ringedSpaceStructureMap t)
  have h3 := Stacks.SheafOfModules.unit_comp_map_ringedSpaceStructureMap t
  change (sheafAdjunction t).unit.app S'.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((sheafAdjunction f).unit.app _ ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            (Stacks.SheafOfModules.inverseImageFirstRingMap f t)) = _
  rw [show (sheafAdjunction f).unit.app _ ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            (Stacks.SheafOfModules.inverseImageFirstRingMap f t) =
        Stacks.SheafOfModules.ringedSpaceStructureMap t ≫ (sheafAdjunction f).unit.app S.sheaf
      from h2.symm, Functor.map_comp, ← Category.assoc]
  exact congrArg (· ≫ _) h3

open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction) in
/-- The canonical `t⁻¹𝒪_{S'} ⟶ f_*(f ≫ t)⁻¹𝒪_{S'}` followed by `f_*` of the identification
`(f ≫ t)⁻¹𝒪_{S'} ≅ f⁻¹t⁻¹𝒪_{S'}` is the unit of `f⁻¹ ⊣ f_*`. -/
theorem baseRingPushMap_comp_inverseImageCompIso_hom :
    baseRingPushMap f t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (Stacks.SheafOfModules.inverseImageCompIso f t).hom =
      (sheafAdjunction f).unit.app (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) := by
  apply ((sheafAdjunction t).homEquiv _ _).injective
  refine ((sheafAdjunction t).homEquiv_naturality_right _ _).trans ?_
  rw [homEquiv_baseRingPushMap]
  have h1 := homEquiv_inverseImageCompIso_hom f t
  rw [Adjunction.homEquiv_unit] at h1
  refine h1.trans ?_
  rw [Adjunction.comp_unit_app, Adjunction.homEquiv_unit]

/-- The identification of `𝖭𝖫_{X/S'}` with the naive cotangent complex over `f⁻¹t⁻¹𝒪_{S'}`
used in **Stacks 0E1Z**, followed by the map of **Stacks 0E1Z** to `𝖭𝖫_{X/S}`, is the remark's
second map `naiveCotangentCompComplexMap`. -/
theorem naiveCotangentComplexCompIso_hom_comp_relativeNaiveCotangentMap :
    (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom ≫
        Stacks.NaiveCotangentCompositionTriangle.relativeNaiveCotangentMap f t =
      naiveCotangentCompComplexMap f t := by
  refine (Category.assoc _ _ _).trans ((mapOfSquare_comp_relative_of_fac
    (baseInverseImageRingMap f t) (Stacks.SheafOfModules.inverseImageFirstRingMap f t)
    (Stacks.SheafOfModules.ringedSpaceStructureMap f) _
    (Stacks.SheafOfModules.inverseImageCompIso f t).hom
    (baseInverseImageRingMap_comp f t).symm
    (inverseImageCompIso_hom_comp_inverseImageFirstRingMap f t) _).trans ?_)
  rfl




section Ext

variable {T : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (a : A ⟶ B)

/-- The canonical presentation of a sheaf of rings on a space is locally surjective. -/
instance canonicalPresentation_isLocallySurjective_top (A₀ B₀ : TopCat.Sheaf CommRingCat.{u} T)
    (a₀ : A₀ ⟶ B₀) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation (Opens.grothendieckTopology T)
        A₀ B₀ a₀).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective _ A₀ B₀ a₀)

/-- Maps out of a conormal sheaf on a space agree when they agree on conormal classes. -/
theorem conormalSheaf_hom_ext_opens {T : TopCat.{u}}
    (A' B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
    (φ : A' ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    {g₁ g₂ :
      Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology T) A' B φ ⟶ G}
    (h : ∀ (U : (Opens T)ᵒᵖ) (x : ↥(Stacks.Sites.Conormal.kernelIdeal φ.hom U)),
      g₁.val.app U (Stacks.Sites.Conormal.toAssociatedModule.{u, u, u, u}
        (Opens.grothendieckTopology T) A' B φ (Stacks.Sites.Conormal.conormalPresheaf φ.hom) U
          ((Stacks.Sites.Conormal.kernelIdeal φ.hom U).toCotangent x)) =
        g₂.val.app U (Stacks.Sites.Conormal.toAssociatedModule.{u, u, u, u}
          (Opens.grothendieckTopology T) A' B φ (Stacks.Sites.Conormal.conormalPresheaf φ.hom) U
          ((Stacks.Sites.Conormal.kernelIdeal φ.hom U).toCotangent x))) :
    g₁ = g₂ :=
  Stacks.Sites.Conormal.conormal_hom_ext (J := Opens.grothendieckTopology T) (A := A') (B := B)
    (φ := φ) (h := h)

/-- Maps out of `B ⊗ Ω` of a presentation on a space agree when they agree on `1 ⊗ d x`. -/
theorem conormalSequence_X₂_hom_ext_opens {T : TopCat.{u}}
    (R A' B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
    (r : R ⟶ A') (φ : A' ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    {g₁ g₂ : (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T)
      R A' B r φ).X₂ ⟶ G}
    (h : ∀ (U : (Opens T)ᵒᵖ) (x : A'.obj.obj U),
      g₁.val.app U (Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u}
        (Opens.grothendieckTopology T) R A' B r φ U x) =
        g₂.val.app U (Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u}
          (Opens.grothendieckTopology T) R A' B r φ U x)) :
    g₁ = g₂ :=
  Stacks.Sites.Conormal.tensorSheaf_hom_ext (J := Opens.grothendieckTopology T) (h := h)

end Ext

section InverseImageTranspose

variable {T T' : TopCat.{u}} (g : T' ⟶ T) (A B : TopCat.Sheaf CommRingCat.{u} T) (a : A ⟶ B)

open Stacks.SheafOfModules in
/-- The transpose along `g⁻¹ ⊣ g_*` of the degree `-1` part of **Stacks 08TM**, followed by a
map `h`, is the comparison of conormal sheaves along `g` followed by `g_*h`. -/
theorem homEquiv_inverseImageMap_f_negOne
    {N : SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B))}
    (h : (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a)).X (-1) ⟶ N) :
    (AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _
        ((naiveCotangentComplexInverseImageMap g A B a).f (-1) ≫ h) =
      eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology T) A B a) ≫
        inverseImageConormalPushforwardMap g A B a ≫
        (SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).map
          (eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a)).symm ≫ h) := by
  refine (congrArg ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _)
    ((congrArg (· ≫ h) (naiveCotangentComplexInverseImageMap_f_negOne g A B a)).trans
      (Category.assoc _ _ _))).trans ?_
  refine ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv_naturality_left
    _ _).trans ?_
  refine congrArg _ ?_
  refine (congrArg ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _)
    (Category.assoc _ _ _)).trans ?_
  refine ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv_naturality_right
    _ _).trans ?_
  exact congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)

open Stacks.SheafOfModules in
/-- The transpose along `g⁻¹ ⊣ g_*` of the degree `0` part of **Stacks 08TM**, followed by a
map `h`, is the comparison of the scalar extensions of differentials along `g` followed by
`g_*h`. -/
theorem homEquiv_inverseImageMap_f_zero
    {N : SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B))}
    (h : (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a)).X 0 ⟶ N) :
    (AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _
        ((naiveCotangentComplexInverseImageMap g A B a).f 0 ≫ h) =
      eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology T) A B a) ≫
        inverseImageTensorPushforwardMap g A B a ≫
        (SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).map
          (eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a)).symm ≫ h) := by
  refine (congrArg ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _)
    ((congrArg (· ≫ h) (naiveCotangentComplexInverseImageMap_f_zero g A B a)).trans
      (Category.assoc _ _ _))).trans ?_
  refine ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv_naturality_left
    _ _).trans ?_
  refine congrArg _ ?_
  refine (congrArg ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv _ _)
    (Category.assoc _ _ _)).trans ?_
  refine ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction g B).homEquiv_naturality_right
    _ _).trans ?_
  exact congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)

end InverseImageTranspose

section Generic

open Stacks.Sites.Conormal Stacks.SheafOfModules Stacks.Sites.FreeAlgebra

variable {T T' : TopCat.{u}} (g : T' ⟶ T) (R₁ B : TopCat.Sheaf CommRingCat.{u} T) (a : R₁ ⟶ B)
  (C A₀ : TopCat.Sheaf CommRingCat.{u} T') (b : (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B ⟶ C)
  (ι : A₀ ⟶ (TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) (str : A₀ ⟶ C)
  (hstr : ι ≫ (TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b = str)
  (ρ : R₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g).obj A₀)
  (hρ : ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map ι =
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app R₁)
  (bR : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g).obj C)
  (hbR : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b = bR)

include hρ hbR in
/-- The two maps of polynomial presentations `R₁[B] ⟶ g_*((g⁻¹R₁)[C])` agree: through `g⁻¹B`
and through `A₀`. -/
theorem inverseImagePresentationHom_comp_freeAlgebraMapOfSquare_eq :
    inverseImagePresentationHom g R₁ B ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map
        (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b) =
      freeAlgebraPushMap g R₁ (underlyingPresheaf (Opens.grothendieckTopology T) B) A₀
          (underlyingPresheaf (Opens.grothendieckTopology T') C) ρ
          (Functor.whiskerRight bR.hom (forget CommRingCat.{u})) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g).map
          (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T') A₀
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C C ι (𝟙 _)) := by
  subst hbR
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · have h1 := freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom g R₁ B
    have h2 := freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology T') ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) _ _ (𝟙 _)
      (underlyingPresheafMap _ _ _ b)
    have h3 := freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap g R₁
      (underlyingPresheaf (Opens.grothendieckTopology T) B) A₀
      (underlyingPresheaf (Opens.grothendieckTopology T') C) ρ
      (Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}))
    have h4 := freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology T') A₀ ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) _ _ ι
      (underlyingPresheafMap _ _ _ (𝟙 C))
    calc _ = (freeAlgebraSheafCoefficientMap _ R₁ _ ≫ inverseImagePresentationHom g R₁ B) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g).map
            (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b) :=
          (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ _) h1
      _ = _ := Category.assoc _ _ _
      _ = _ := congrArg (_ ≫ ·)
        (((TopCat.Sheaf.pushforward CommRingCat.{u} g).map_comp _ _).symm.trans
          (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} g).map h2))
      _ = _ := congrArg (_ ≫ ·) (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} g).map
          (Category.id_comp _))
      _ = _ := congrArg (· ≫ _) hρ.symm
      _ = _ := Category.assoc _ _ _
      _ = _ := congrArg (_ ≫ ·)
        (((TopCat.Sheaf.pushforward CommRingCat.{u} g).map_comp _ _).symm.trans
          (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} g).map h4.symm))
      _ = _ := congrArg (_ ≫ ·) ((TopCat.Sheaf.pushforward CommRingCat.{u} g).map_comp _ _)
      _ = _ := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ _) h3.symm
      _ = _ := Category.assoc _ _ _
  · have hL1 : inverseImagePresentationHom g R₁ B ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map
          (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b) =
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).homEquiv _ _
          ((underlyingInverseImageIso g R₁ B).hom ≫
            canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b) :=
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).homEquiv_naturality_right
        _ _).symm
    have hL2 := freeAlgebraSheafVariable_comp_homEquiv g R₁
      (underlyingPresheaf (Opens.grothendieckTopology T) B)
      (freeAlgebraSheaf (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
        (underlyingPresheaf (Opens.grothendieckTopology T') C))
      ((underlyingInverseImageIso g R₁ B).hom ≫
            canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b)
    have hL3 := inverseImageVariable_comp_inverseImageHom_map_comp g R₁
      (underlyingPresheaf (Opens.grothendieckTopology T) B)
      _ (toUnderlyingInverseImage g B) _
      (canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T')
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
              ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C (𝟙 _) b)
    have hL4 := freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology T') ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) _ _ (𝟙 _)
      (underlyingPresheafMap _ _ _ b)
    have hL5 := toUnderlyingInverseImage_comp_homEquiv g B _
      (underlyingPresheafMap _ _ _ b ≫ freeAlgebraSheafVariable (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
        (underlyingPresheaf (Opens.grothendieckTopology T') C))
    have hR1 := freeAlgebraSheafVariable_comp_freeAlgebraPushMap g R₁
      (underlyingPresheaf (Opens.grothendieckTopology T) B) A₀
      (underlyingPresheaf (Opens.grothendieckTopology T') C) ρ
      (Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}))
    have hR2 := freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology T') A₀ ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) _ _ ι
      (underlyingPresheafMap _ _ _ (𝟙 C))
    refine (congrArg (fun k => freeAlgebraSheafVariable _ R₁ _ ≫ Functor.whiskerRight
      ((sheafToPresheaf _ CommRingCat.{u}).map k) (forget CommRingCat.{u})) hL1).trans ?_
    refine hL2.trans ?_
    refine (congrArg ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) g).homEquiv _ _)
      (hL3.trans (congrArg _ hL4))).trans ?_
    refine hL5.trans ?_
    refine Eq.trans ?_ (show (freeAlgebraSheafVariable _ R₁ _ ≫ Functor.whiskerRight
        ((sheafToPresheaf _ CommRingCat.{u}).map (freeAlgebraPushMap g R₁
          (underlyingPresheaf (Opens.grothendieckTopology T) B) A₀
          (underlyingPresheaf (Opens.grothendieckTopology T') C) ρ
          (Functor.whiskerRight
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}))))
        (forget CommRingCat.{u})) ≫ Functor.whiskerRight ((sheafToPresheaf _ CommRingCat.{u}).map
          ((TopCat.Sheaf.pushforward CommRingCat.{u} g).map (canonicalFreeAlgebraMapOfSquare
            (Opens.grothendieckTopology T') A₀
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C C ι (𝟙 _))))
          (forget CommRingCat.{u}) = _ from rfl)
    refine Eq.trans ?_ (congrArg (· ≫ _) hR1.symm)
    refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}) ≫
          Functor.whiskerLeft (Opens.map g).op k) hR2).symm
    rfl

/-- The presentation by all sections of a sheaf of rings on a space is locally surjective. -/
instance presentation_underlying_isLocallySurjective {T₀ : TopCat.{u}}
    (A₀' B₀ : TopCat.Sheaf CommRingCat.{u} T₀) (a₀ : A₀' ⟶ B₀) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T₀)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology T₀) A₀' B₀ a₀
        (underlyingPresheaf (Opens.grothendieckTopology T₀) B₀)
        (𝟙 (underlyingPresheaf (Opens.grothendieckTopology T₀) B₀))).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

include hstr in
/-- The square of rings `A₀ ⟶ C`, `g⁻¹R₁ ⟶ C` commuting along `ι`. -/
theorem remarkCanonicalSquare :
    str ≫ 𝟙 C = ι ≫ (TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b := by
  rw [Category.comp_id, hstr]

include hstr hρ in
/-- The square of rings `R₁ ⟶ g_*C`, `R₁ ⟶ g_*A₀ ⟶ g_*C` commuting. -/
theorem remarkPresentationSquare :
    a ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b =
    ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map str := by
  rw [← hstr, Functor.map_comp, Functor.map_comp, ← Category.assoc ρ, hρ, ← Category.assoc]
  exact congrArg (fun k => k ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.naturality a)

/-- Two successive transports along equalities of sheaves of modules are one transport. -/
theorem SheafOfModules.eqToHom_val_app_eqToHom_val_app {𝒞 : Type*} [Category 𝒞]
    {K : GrothendieckTopology 𝒞}
    {R : Sheaf K RingCat.{u}} {M₁ M₂ M₃ : SheafOfModules.{u} R} (h₁ : M₁ = M₂) (h₂ : M₂ = M₃)
    (U : 𝒞ᵒᵖ) (y : M₁.val.obj U) :
    (eqToHom h₂).val.app U ((eqToHom h₁).val.app U y) = (eqToHom (h₁.trans h₂)).val.app U y := by
  subst h₁ h₂
  rfl


include hstr hρ in
/-- Degree `-1`: the transpose of **Stacks 08TM** followed by the base change square is the map of
presentations along `g` followed by the change of base ring. -/
theorem homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_negOne :
    (SheafOfModules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).homEquiv
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X (-1))
      ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X (-1)))
      ((naiveCotangentComplexInverseImageMap g R₁ B a).f (-1) ≫
        (baseChangeSquareMap.{u, u, u} (Opens.grothendieckTopology T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) b).f (-1)) =
      (((presentationNaiveCotangentPushMap g (A₁ := R₁) (B₁ := B) (a₁ := a)
          (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _)
          (A₂ := A₀) (B₂ := C) (a₂ := str)
          (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
          (remarkPresentationSquare g R₁ B a C A₀ b ι str hstr ρ hρ)
          (b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b)
          (ε := Functor.whiskerRight
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}))
          rfl).f (-1) ≫
        (SheafOfModules.pushforward.{u} (pushforwardRingHom g
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b))).map
          ((naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
            (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)).f (-1))) :
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X (-1) ⟶
        (SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X (-1)))) := by
  refine (cancel_epi (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology T) R₁ B a).symm)).1 ?_
  refine (congrArg _ (homEquiv_inverseImageMap_f_negOne g R₁ B a _)).trans ?_
  rw [naiveCotangentComplexMapOfSquare_f_negOne.{u, u, u, u} (Opens.grothendieckTopology T') _ _
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) _ _
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) (𝟙 _) b (Category.id_comp _).symm,
    presentationNaiveCotangentPushMap_f_negOne g (A₁ := R₁) (B₁ := B) (a₁ := a)
      (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _) (A₂ := A₀) (B₂ := C)
      (a₂ := str) (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
      (remarkPresentationSquare g R₁ B a C A₀ b ι str hstr ρ hρ)
      (b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b)
      (ε := Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u})) rfl,
    naiveCotangentComplexMapOfSquare_f_negOne.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
      _ _ ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
      (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)]
  refine conormalSheaf_hom_ext_opens _ _ _ fun U x =>
    Eq.symm ((SheafOfModules.comp_val_app_apply _ _ U _).trans ?_)
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (congrArg _ (SheafOfModules.comp_val_app_apply _ _ U _)).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ U _))).trans ?_
  refine (congrArg _ (SheafOfModules.comp_val_app_apply _ _ U _)).trans ?_
  refine (congrArg _ (congrArg _
    (conormalSheafMapPush_toAssociatedModule _ _ _ _ _ _ _ _ _ _))).trans ?_
  refine (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _).trans ?_
  refine (congrArg _ (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _)).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ _ _))).trans ?_
  have hls₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T')
      (canonicalPresentation (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
        C ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).hom :=
    canonicalPresentation_isLocallySurjective_top _ C _
  refine (congrArg _ (conormalSheafMapOfSquare_toAssociatedModule.{u, u, u, u}
    (Opens.grothendieckTopology T') _ _ _ _ _ _ _ _ _ _ _)).trans ?_
  refine Eq.symm ((SheafOfModules.comp_val_app_apply _ _ U _).trans ?_)
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ U _))).trans ?_
  refine (congrArg _ (conormalSheafMapAlong_toAssociatedModule _ _ _ _ _ _ U _)).trans ?_
  refine (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ _ _))).trans ?_
  refine (congrArg _ (conormalSheafMapOfSquare_toAssociatedModule.{u, u, u, u}
    (Opens.grothendieckTopology T') _ _ _ _ _ _ _ _ _ _ _)).trans ?_
  exact congrArg _ (congrArg _ (congrArg (Ideal.toCotangent _) (Subtype.ext (a1 := ⟨_, _⟩)
    (a2 := ⟨_, _⟩) (congrArg (fun t => (t.hom.app U).hom x.1)
      (inverseImagePresentationHom_comp_freeAlgebraMapOfSquare_eq g R₁ B C A₀ b ι ρ hρ _ rfl)))))

include hstr hρ in
/-- Degree `0`: the transpose of **Stacks 08TM** followed by the base change square is the map of
presentations along `g` followed by the change of base ring. -/
theorem homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_zero :
    (SheafOfModules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).homEquiv
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X 0)
      ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X 0))
      ((naiveCotangentComplexInverseImageMap g R₁ B a).f 0 ≫
        (baseChangeSquareMap.{u, u, u} (Opens.grothendieckTopology T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) b).f 0) =
      (((presentationNaiveCotangentPushMap g (A₁ := R₁) (B₁ := B) (a₁ := a)
          (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _)
          (A₂ := A₀) (B₂ := C) (a₂ := str)
          (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
          (remarkPresentationSquare g R₁ B a C A₀ b ι str hstr ρ hρ)
          (b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b)
          (ε := Functor.whiskerRight
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u}))
          rfl).f 0 ≫
        (SheafOfModules.pushforward.{u} (pushforwardRingHom g
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b))).map
          ((naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
            (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)).f 0)) :
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X 0 ⟶
        (SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X 0))) := by
  refine (cancel_epi (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology T) R₁ B a).symm)).1 ?_
  refine (congrArg _ (homEquiv_inverseImageMap_f_zero g R₁ B a _)).trans ?_
  rw [naiveCotangentComplexMapOfSquare_f_zero.{u, u, u, u} (Opens.grothendieckTopology T') _ _
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) _ _
      ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) (𝟙 _) b (Category.id_comp _).symm,
    presentationNaiveCotangentPushMap_f_zero g (A₁ := R₁) (B₁ := B) (a₁ := a)
      (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _) (A₂ := A₀) (B₂ := C)
      (a₂ := str) (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
      (remarkPresentationSquare g R₁ B a C A₀ b ι str hstr ρ hρ)
      (b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b)
      (ε := Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b).hom (forget CommRingCat.{u})) rfl,
    naiveCotangentComplexMapOfSquare_f_zero.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
      _ _ ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
      (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)]
  refine conormalSequence_X₂_hom_ext_opens _ _ _ _ _ fun U x =>
    Eq.symm ((SheafOfModules.comp_val_app_apply _ _ U _).trans ?_)
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (congrArg _ (SheafOfModules.comp_val_app_apply _ _ U _)).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ U _))).trans ?_
  refine (congrArg _ (SheafOfModules.comp_val_app_apply _ _ U _)).trans ?_
  refine (congrArg _ (congrArg _
    (tensorSheafMapPush_tensorDifferential _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))).trans ?_
  refine (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _).trans ?_
  refine (congrArg _ (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _)).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ _ _))).trans ?_
  have hls₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T')
      (canonicalPresentation (Opens.grothendieckTopology T')
        ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
        C ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).hom :=
    canonicalPresentation_isLocallySurjective_top _ C _
  refine (congrArg _ (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u}
    (Opens.grothendieckTopology T') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).trans ?_
  refine Eq.symm ((SheafOfModules.comp_val_app_apply _ _ U _).trans ?_)
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ U _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ U _))).trans ?_
  refine (congrArg _ (tensorSheafMapAlong_tensorDifferential _ _ _ _ _ _ _ _ _ _ U _)).trans ?_
  refine (Stacks.SectionsComponents.pushforward_map_val_app _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (congrArg _ (SheafOfModules.eqToHom_val_app_eqToHom_val_app _ _ _ _))).trans ?_
  refine (congrArg _ (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u}
    (Opens.grothendieckTopology T') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).trans ?_
  exact congrArg _ (congrArg _ (congrArg (fun t => (t.hom.app U).hom x)
    (inverseImagePresentationHom_comp_freeAlgebraMapOfSquare_eq g R₁ B C A₀ b ι ρ hρ _ rfl)))

include hstr hρ in
/-- `remarkPresentationSquare` for any map equal to `unit ≫ g_*b`. -/
theorem remarkPresentationSquareOfEq (bR : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g).obj C)
    (hbR : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b = bR) :
    a ≫ bR = ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g).map str :=
  hbR ▸ remarkPresentationSquare g R₁ B a C A₀ b ι str hstr ρ hρ

include hstr hρ in
/-- `homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_negOne`, read along any map equal to
`unit ≫ g_*b`. -/
theorem homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_negOne_of_eq
    (bR : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g).obj C)
    (hbR : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b = bR)
    (h₁ : (SheafOfModules.pushforward.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X (-1))) =
      (SheafOfModules.pushforward.{u} (pushforwardRingHom g bR)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := C) (O' := C) (𝟙 C))).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X (-1)))) :
    (SheafOfModules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).homEquiv
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X (-1))
      ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X (-1)))
      ((naiveCotangentComplexInverseImageMap g R₁ B a).f (-1) ≫
        (baseChangeSquareMap.{u, u, u} (Opens.grothendieckTopology T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) b).f (-1)) ≫ eqToHom h₁ =
      (presentationNaiveCotangentPushMap g (A₁ := R₁) (B₁ := B) (a₁ := a)
          (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _)
          (A₂ := A₀) (B₂ := C) (a₂ := str)
          (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
          (remarkPresentationSquareOfEq g R₁ B a C A₀ b ι str hstr ρ hρ bR hbR) (b := bR)
          (ε := Functor.whiskerRight bR.hom (forget CommRingCat.{u})) rfl).f (-1) ≫
        (SheafOfModules.pushforward.{u} (pushforwardRingHom g bR)).map
          ((naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
            (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)).f (-1)) := by
  subst hbR
  refine (congrArg (· ≫ eqToHom h₁)
    (homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_negOne g R₁ B a C A₀ b ι str hstr
      ρ hρ)).trans ?_
  exact Category.comp_id _

include hstr hρ in
/-- `homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_zero`, read along any map equal to
`unit ≫ g_*b`. -/
theorem homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_zero_of_eq
    (bR : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g).obj C)
    (hbR : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app B ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g).map b = bR)
    (h₁ : (SheafOfModules.pushforward.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X 0)) =
      (SheafOfModules.pushforward.{u} (pushforwardRingHom g bR)).obj
          ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := C) (O' := C) (𝟙 C))).obj
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X 0))) :
    (SheafOfModules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom g B)).homEquiv
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R₁ B a).X 0)
      ((SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := (TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) (O' := C) b)).obj
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T')
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b)).X 0))
      ((naiveCotangentComplexInverseImageMap g R₁ B a).f 0 ≫
        (baseChangeSquareMap.{u, u, u} (Opens.grothendieckTopology T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁)
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj B) C
          ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a) b).f 0) ≫ eqToHom h₁ =
      (presentationNaiveCotangentPushMap g (A₁ := R₁) (B₁ := B) (a₁ := a)
          (E₁ := underlyingPresheaf (Opens.grothendieckTopology T) B) (α₁ := 𝟙 _)
          (A₂ := A₀) (B₂ := C) (a₂ := str)
          (E₂ := underlyingPresheaf (Opens.grothendieckTopology T') C) (α₂ := 𝟙 _) (ρ := ρ)
          (remarkPresentationSquareOfEq g R₁ B a C A₀ b ι str hstr ρ hρ bR hbR) (b := bR)
          (ε := Functor.whiskerRight bR.hom (forget CommRingCat.{u})) rfl).f 0 ≫
        (SheafOfModules.pushforward.{u} (pushforwardRingHom g bR)).map
          ((naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T') A₀ C str
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj R₁) C
            ((TopCat.Sheaf.pullback CommRingCat.{u} g).map a ≫ b) ι (𝟙 C)
            (remarkCanonicalSquare g R₁ B a C A₀ b ι str hstr)).f 0) := by
  subst hbR
  refine (congrArg (· ≫ eqToHom h₁)
    (homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_zero g R₁ B a C A₀ b ι str hstr
      ρ hρ)).trans ?_
  exact Category.comp_id _

end Generic

section Transpose

/-- Transporting an adjunction along an equality of right adjoints changes its `homEquiv` by
an `eqToHom`. -/
theorem Adjunction.homEquiv_mpr_rightAdjoint_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G G' : D ⥤ C}
    (h : G = G') (adj : F ⊣ G') (M : C) (N : D) (φ : F.obj M ⟶ N) :
    ((Eq.mpr (congrArg (fun K => F ⊣ K) h) adj : F ⊣ G).homEquiv M N φ) =
      adj.homEquiv M N φ ≫ eqToHom (congrArg (fun K : D ⥤ C => K.obj N) h).symm := by
  subst h
  simp

/-- The composite adjunction of the two steps of `f^*`. -/
abbrev twoStepAdjunctionComp : twoStepPullback f ⊣ (SheafOfModules.restrictScalars
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
            (O := Stacks.SheafOfModules.inverseImageMiddleRing f) (O' := X.sheaf)
            (Stacks.SheafOfModules.ringedSpaceStructureMap f)) ⋙
        SheafOfModules.pushforward
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)) :=
  (SheafOfModules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)).comp
    (Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
      (Opens.grothendieckTopology (X : TopCat))
      (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
      (Stacks.SheafOfModules.ringedSpaceStructureMap f))

/-- `twoStepPullbackAdjunction` is the composite adjunction transported along
`modulePushforward_eq`. -/
theorem twoStepPullbackAdjunction_eq_mpr :
    twoStepPullbackAdjunction f =
      Eq.mpr (congrArg (fun K => twoStepPullback f ⊣ K) (modulePushforward_eq f))
        (twoStepAdjunctionComp f) := rfl

/-- Transposes along `f^* ⊣ f_*` of maps out of `f^*M` read through `modulePullbackIsoTwoStep`. -/
theorem modulePullbackPushforwardAdjunction_homEquiv_twoStep
    (M : SheafOfModules.{u} (structureSheafRing S))
    (N : SheafOfModules.{u} (structureSheafRing X)) (φ : (twoStepPullback f).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction f).homEquiv _ _
        ((modulePullbackIsoTwoStep f).hom.app M ≫ φ) =
      (twoStepAdjunctionComp f).homEquiv M N φ ≫
        eqToHom (congrArg (fun K : _ ⥤ _ => K.obj N) (modulePushforward_eq f)).symm := by
  refine ((modulePullbackPushforwardAdjunction f).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (modulePushforward f).map φ)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ M)).trans ?_
  refine ((twoStepPullbackAdjunction f).homEquiv_unit M N φ).symm.trans ?_
  rw [twoStepPullbackAdjunction_eq_mpr]
  exact Adjunction.homEquiv_mpr_rightAdjoint_eq (modulePushforward_eq f)
    (twoStepAdjunctionComp f) M N φ

/-- The composite adjunction applied to the inverse transpose along the second step. -/
theorem twoStepAdjunctionComp_homEquiv_symm (M : SheafOfModules.{u} (structureSheafRing S))
    (N : SheafOfModules.{u} (structureSheafRing X)) (v) :
    (twoStepAdjunctionComp f).homEquiv M N
        (((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology (X : TopCat))
          (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
          (Stacks.SheafOfModules.ringedSpaceStructureMap f)).homEquiv _ _).symm v) =
      (SheafOfModules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)).homEquiv
          _ _ v := by
  change (SheafOfModules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)).homEquiv _ _
        ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology (X : TopCat))
          (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
          (Stacks.SheafOfModules.ringedSpaceStructureMap f)).homEquiv _ _
        (((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology (X : TopCat))
          (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
          (Stacks.SheafOfModules.ringedSpaceStructureMap f)).homEquiv _ _).symm v)) = _
  exact congrArg _ (Equiv.apply_symm_apply _ v)

end Transpose

/-- The unit of `f⁻¹ ⊣ f_*` at `𝒪_S` followed by `f_*` of the structure map of `f` is the
structure comorphism of `f`. -/
private theorem unit_comp_map_ringedSpaceStructureMap_eq :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app S.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (Stacks.SheafOfModules.ringedSpaceStructureMap f) = structureComorphism f :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv_unit
    _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- Degree `-1` of `naiveCotangentComplexCompIso`. -/
theorem naiveCotangentComplexCompIso_hom_f_negOne :
    (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom.f (-1) =
      (Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageSheaf (f ≫ t)) X.sheaf
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
        (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
        (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
          Stacks.SheafOfModules.ringedSpaceStructureMap f)
        (Stacks.SheafOfModules.inverseImageCompIso f t).hom (𝟙 _)
        ((Category.comp_id _).trans
          (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f t).symm)).f (-1) ≫
        eqToHom (congrArg (fun K => HomologicalComplex.X K (-1))
          (Stacks.SheafOfModules.mapHomologicalComplex_restrictScalars_id X.sheaf _)) :=
  (HomologicalComplex.comp_f _ _ _).trans (congrArg _ (HomologicalComplex.eqToHom_f
    (Stacks.SheafOfModules.mapHomologicalComplex_restrictScalars_id X.sheaf _) _))

/-- Degree `-1` of the comparison of the two canonical maps `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`. -/
theorem homEquiv_pulledNaiveCotangentMap_f_negOne :
    (SheafOfModules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)).homEquiv
        ((baseNaiveCotangent t).X (-1))
        ((_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
              (O := Stacks.SheafOfModules.inverseImageMiddleRing f) (O' := X.sheaf)
              (Stacks.SheafOfModules.ringedSpaceStructureMap f))).obj
          ((Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
            (Opens.grothendieckTopology X.carrier)
              (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
              (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
                Stacks.SheafOfModules.ringedSpaceStructureMap f)).X (-1)))
        ((Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap f.hom.base
            (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) S.sheaf
            (Stacks.SheafOfModules.ringedSpaceStructureMap t)).f (-1) ≫
          (Stacks.SheafOfModules.baseChangeSquareMap.{u, u, u}
            (Opens.grothendieckTopology X.carrier)
            (Stacks.SheafOfModules.inverseImageBaseRing f t)
              (Stacks.SheafOfModules.inverseImageMiddleRing f)
            X.sheaf (Stacks.SheafOfModules.inverseImageFirstRingMap f t)
            (Stacks.SheafOfModules.ringedSpaceStructureMap f)).f (-1)) ≫
      eqToHom (congrArg (fun K : _ ⥤ _ => K.obj
        ((Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier)
              (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
              (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
                Stacks.SheafOfModules.ringedSpaceStructureMap f)).X (-1)))
                  (modulePushforward_eq f)).symm =
    (naiveCotangentPushMap f t).f (-1) ≫
      (modulePushforward f).map
        ((Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom.f (-1)) := by
  refine (homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_negOne_of_eq f.hom.base
    (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) S.sheaf
    (Stacks.SheafOfModules.ringedSpaceStructureMap t) X.sheaf (inverseImageSheaf (f ≫ t))
    (Stacks.SheafOfModules.ringedSpaceStructureMap f)
      (Stacks.SheafOfModules.inverseImageCompIso f t).hom
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
    (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f t) (baseRingPushMap f t)
      (baseRingPushMap_comp_inverseImageCompIso_hom f t)
    (structureComorphism f) (unit_comp_map_ringedSpaceStructureMap_eq f) _).trans ?_
  refine Eq.trans ?_ (congrArg (fun g => _ ≫ (modulePushforward f).map g)
    (naiveCotangentComplexCompIso_hom_f_negOne f t)).symm
  simp
  rfl

/-- Degree `0` of `naiveCotangentComplexCompIso`. -/
theorem naiveCotangentComplexCompIso_hom_f_zero :
    (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom.f 0 =
      (Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageSheaf (f ≫ t)) X.sheaf
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
        (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
        (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
          Stacks.SheafOfModules.ringedSpaceStructureMap f)
        (Stacks.SheafOfModules.inverseImageCompIso f t).hom (𝟙 _)
        ((Category.comp_id _).trans
          (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f t).symm)).f 0 ≫
        eqToHom (congrArg (fun K => HomologicalComplex.X K 0)
          (Stacks.SheafOfModules.mapHomologicalComplex_restrictScalars_id X.sheaf _)) :=
  (HomologicalComplex.comp_f _ _ _).trans (congrArg _ (HomologicalComplex.eqToHom_f
    (Stacks.SheafOfModules.mapHomologicalComplex_restrictScalars_id X.sheaf _) _))

/-- Degree `0` of the comparison of the two canonical maps `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`. -/
theorem homEquiv_pulledNaiveCotangentMap_f_zero :
    (SheafOfModules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f.hom.base S.sheaf)).homEquiv
        ((baseNaiveCotangent t).X 0)
        ((_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite
              (O := Stacks.SheafOfModules.inverseImageMiddleRing f) (O' := X.sheaf)
              (Stacks.SheafOfModules.ringedSpaceStructureMap f))).obj
          ((Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
            (Opens.grothendieckTopology X.carrier)
              (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
              (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
                Stacks.SheafOfModules.ringedSpaceStructureMap f)).X 0))
        ((Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap f.hom.base
            (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) S.sheaf
            (Stacks.SheafOfModules.ringedSpaceStructureMap t)).f 0 ≫
          (Stacks.SheafOfModules.baseChangeSquareMap.{u, u, u}
            (Opens.grothendieckTopology X.carrier)
            (Stacks.SheafOfModules.inverseImageBaseRing f t)
              (Stacks.SheafOfModules.inverseImageMiddleRing f)
            X.sheaf (Stacks.SheafOfModules.inverseImageFirstRingMap f t)
            (Stacks.SheafOfModules.ringedSpaceStructureMap f)).f 0) ≫
      eqToHom (congrArg (fun K : _ ⥤ _ => K.obj
        ((Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier)
              (Stacks.SheafOfModules.inverseImageBaseRing f t) X.sheaf
              (Stacks.SheafOfModules.inverseImageFirstRingMap f t ≫
                Stacks.SheafOfModules.ringedSpaceStructureMap f)).X 0))
                  (modulePushforward_eq f)).symm =
    (naiveCotangentPushMap f t).f 0 ≫
      (modulePushforward f).map
        ((Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom.f 0) := by
  refine (homEquiv_inverseImageMap_comp_baseChangeSquareMap_f_zero_of_eq f.hom.base
    (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) S.sheaf
    (Stacks.SheafOfModules.ringedSpaceStructureMap t) X.sheaf (inverseImageSheaf (f ≫ t))
    (Stacks.SheafOfModules.ringedSpaceStructureMap f)
      (Stacks.SheafOfModules.inverseImageCompIso f t).hom
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
    (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f t) (baseRingPushMap f t)
      (baseRingPushMap_comp_inverseImageCompIso_hom f t)
    (structureComorphism f) (unit_comp_map_ringedSpaceStructureMap_eq f) _).trans ?_
  refine Eq.trans ?_ (congrArg (fun g => _ ≫ (modulePushforward f).map g)
    (naiveCotangentComplexCompIso_hom_f_zero f t)).symm
  simp
  rfl

/-- **The two canonical maps `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` agree**: the one of **Stacks 0E1Z**
(through **Stacks 08TM**) and the one of **Stacks 0GQ1**, up to the identifications of the
models of `f^*𝖭𝖫_{S/S'}` and of `𝖭𝖫_{X/S'}`. -/
theorem pulledNaiveCotangentModelIso_hom_comp_pulledNaiveCotangentMap :
    (pulledNaiveCotangentModelIso f t).hom ≫
        Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap f t =
      pullbackNaiveCotangentMap f t ≫
        (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  apply ((modulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  refine Eq.trans ?_ ((modulePullbackPushforwardAdjunction f).homEquiv_naturality_right _ _).symm
  have hR : (modulePullbackPushforwardAdjunction f).homEquiv _ _
        ((pullbackNaiveCotangentMap f t).f i) =
      (naiveCotangentPushMap f t).f i :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ i)
      (((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction f)
        (ComplexShape.up ℤ)).homEquiv _ _).apply_symm_apply (naiveCotangentPushMap f t))
  rw [hR]
  have hL : ((pulledNaiveCotangentModelIso f t).hom ≫
        Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap f t).f i =
      (modulePullbackIsoTwoStep f).hom.app _ ≫
        ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology (X : TopCat))
          (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
          (Stacks.SheafOfModules.ringedSpaceStructureMap f)).homEquiv _ _).symm
          ((Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap f.hom.base
              (Stacks.SheafOfModules.inverseImageBaseRingOnMiddle t) S.sheaf
              (Stacks.SheafOfModules.ringedSpaceStructureMap t)).f i ≫
            (Stacks.SheafOfModules.baseChangeSquareMap.{u, u, u}
              (Opens.grothendieckTopology (X : TopCat))
              (Stacks.SheafOfModules.inverseImageBaseRing f t)
              (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
              (Stacks.SheafOfModules.inverseImageFirstRingMap f t)
              (Stacks.SheafOfModules.ringedSpaceStructureMap f)).f i) := by
    refine Eq.trans ?_ (congrArg _ ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology (X : TopCat))
          (Stacks.SheafOfModules.inverseImageMiddleRing f) X.sheaf
          (Stacks.SheafOfModules.ringedSpaceStructureMap f)).homEquiv_counit _ _ _).symm)
    refine Eq.trans ?_ (congrArg _ (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm))
    rfl
  refine (congrArg _ hL).trans ?_
  refine (modulePullbackPushforwardAdjunction_homEquiv_twoStep f _ _ _).trans ?_
  refine (congrArg (· ≫ _) (twoStepAdjunctionComp_homEquiv_symm f _ _ _)).trans ?_
  by_cases h1 : i = -1
  · subst h1
    exact homEquiv_pulledNaiveCotangentMap_f_negOne f t
  by_cases h0 : i = 0
  · subst h0
    exact homEquiv_pulledNaiveCotangentMap_f_zero f t
  exact (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u}
    (Opens.grothendieckTopology S.carrier) _ _ _ i h1 h0).eq_of_src _ _


/-! ### What 0E1Z gives for the remark's two maps -/

section CloseToTriangle

open Stacks.NaiveCotangentCompositionTriangle

/-- `f^*NL_{S/S'}`, the degreewise pullback, in `D(𝒪_X)`. -/
abbrev pulledBaseNaiveCotangentObj : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  DerivedCategory.Q.obj (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (baseNaiveCotangent t))

/-- The comparison `Lf^*NL_{S/S'} ⟶ f^*NL_{S/S'}` of Stacks 06YJ. -/
abbrev remarkPullbackComparison :
    derivedPullbackNaiveCotangent f t ⟶ pulledBaseNaiveCotangentObj f t :=
  Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f (baseNaiveCotangent t)

/-- The canonical map `f^*NL_{S/S'} ⟶ NL_{X/S'}` of Stacks 0GQ1, in `D(𝒪_X)`. -/
abbrev remarkPulledMap :
    pulledBaseNaiveCotangentObj f t ⟶ relativeNaiveCotangentObj (f ≫ t) :=
  DerivedCategory.Q.map (pullbackNaiveCotangentMap f t)

/-- The canonical map `f^*NL_{S/S'} ⟶ C(NL_{X/S'} ⟶ NL_{X/S})[-1]` of Stacks 0E1Z, in
`D(𝒪_X)`. -/
abbrev remarkConeMap :
    pulledBaseNaiveCotangentObj f t ⟶ (triangle f t).obj₁ :=
  DerivedCategory.Q.map ((pulledNaiveCotangentModelIso f t).hom ≫
    Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t)

/-- The triangle `C(NL_{X/S'} ⟶ NL_{X/S})[-1] ⟶ NL_{X/S'} ⟶ NL_{X/S} ⟶` of `D(𝒪_X)` on the
remark's second map. -/
def remarkConeTriangle : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  Triangle.mk (-((triangle f t).mor₁ ≫
      DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).inv))
    (relativeNaiveCotangentObjMap f t) (-(triangle f t).mor₃)

/-- The iso `-𝟙` on the first vertex. -/
def remarkNegIdIso (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) : Y ≅ Y where
  hom := -𝟙 Y
  inv := -𝟙 Y

/-- The triangle on the remark's second map with the cocone as first vertex is distinguished. -/
theorem remarkConeTriangle_distinguished :
    remarkConeTriangle f t ∈ distTriang _ := by
  refine isomorphic_distinguished _ (triangle_distinguished f t) _ ?_
  refine Triangle.isoMk _ _ (remarkNegIdIso _)
    (DerivedCategory.Q.mapIso (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t)) (Iso.refl _)
    ?_ ?_ ?_
  · refine (Preadditive.neg_comp _ _).trans ?_
    refine Eq.trans ?_ (Preadditive.neg_comp _ _).symm
    refine congrArg Neg.neg ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    refine (congrArg (_ ≫ ·) ((Functor.map_comp DerivedCategory.Q _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (Iso.inv_hom_id _)).trans
        (CategoryTheory.Functor.map_id _ _)))).trans ?_
    exact Category.comp_id _
  · refine (Category.comp_id _).trans ?_
    exact (congrArg DerivedCategory.Q.map
      (naiveCotangentComplexCompIso_hom_comp_relativeNaiveCotangentMap f t).symm).trans
        (Functor.map_comp _ _ _)
  · refine Eq.trans ?_ (Category.id_comp _).symm
    refine (congrArg (_ ≫ ·) ((Functor.map_neg _).trans
      (congrArg Neg.neg (CategoryTheory.Functor.map_id _ _)))).trans ?_
    refine (Preadditive.comp_neg _ _).trans ?_
    refine (congrArg Neg.neg ((Category.comp_id _))).trans ?_
    exact neg_neg _

/-- The canonical map of **Stacks 0E1Z** lifts `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` along the cocone. -/
theorem remarkConeMap_comp_mor₁ :
    remarkConeMap f t ≫ (remarkConeTriangle f t).mor₁ = remarkPulledMap f t := by
  have h1 : DerivedCategory.Q.map ((pulledNaiveCotangentModelIso f t).hom ≫
        Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) ≫
        DerivedCategory.Q.map (mappingCocone.fst (relativeNaiveCotangentMap f t)) =
      -(DerivedCategory.Q.map (pullbackNaiveCotangentMap f t ≫
        (Stacks.SheafOfModules.naiveCotangentComplexCompIso f t).hom)) := by
    refine (Functor.map_comp DerivedCategory.Q _ _).symm.trans ?_
    refine (congrArg DerivedCategory.Q.map ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (coneMap_comp_fst f t)))).trans ?_
    refine (Functor.map_comp DerivedCategory.Q _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Functor.map_neg DerivedCategory.Q)).trans ?_
    refine (Preadditive.comp_neg _ _).trans ?_
    exact congrArg Neg.neg ((Functor.map_comp DerivedCategory.Q _ _).symm.trans
      (congrArg DerivedCategory.Q.map
        (pulledNaiveCotangentModelIso_hom_comp_pulledNaiveCotangentMap f t)))
  refine (Preadditive.comp_neg _ _).trans ?_
  refine (congrArg Neg.neg ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1))).trans ?_
  refine (congrArg Neg.neg (Preadditive.neg_comp _ _)).trans ?_
  refine (neg_neg _).trans ?_
  refine (Functor.map_comp DerivedCategory.Q _ _).symm.trans ?_
  refine congrArg DerivedCategory.Q.map ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))

/-- The remark's first map is the comparison `Lf^* ⟶ f^*` followed by the canonical map. -/
theorem remarkPullbackComparison_comp_pulledMap :
    remarkPullbackComparison f t ≫ remarkPulledMap f t = derivedPullbackNaiveCotangentMap f t :=
  (derivedPullbackNaiveCotangentMap_eq f).symm

/-- `Hⁿ` of the canonical map of **Stacks 0E1Z**, read on complexes. -/
theorem homologyFunctor_map_remarkConeMap (n : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n).map
        (remarkConeMap f t) =
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing X)) n).hom.app _ ≫
        HomologicalComplex.homologyMap ((pulledNaiveCotangentModelIso f t).hom ≫
          Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) n ≫
        (DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (structureSheafRing X)) n).inv.app _ :=
  (NatIso.naturality_2 (DerivedCategory.homologyFunctorFactors
    (SheafOfModules.{u} (structureSheafRing X)) n) _).symm

/-- The canonical map of **Stacks 0E1Z** is an isomorphism on `H⁰`. -/
instance isIso_homologyFunctor_zero_remarkConeMap :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
      (remarkConeMap f t)) := by
  rw [homologyFunctor_map_remarkConeMap]
  have : IsIso (HomologicalComplex.homologyMap ((pulledNaiveCotangentModelIso f t).hom ≫
      Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) 0) := by
    refine (HomologicalComplex.homologyMap_comp (pulledNaiveCotangentModelIso f t).hom
      (Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) 0).symm ▸ ?_
    exact IsIso.comp_isIso' (Iso.isIso_hom ((HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) 0).mapIso
        (pulledNaiveCotangentModelIso f t)))
      (Stacks.SheafOfModules.isIso_homologyMap_ringedSpaceNaiveCotangentConeMap_zero f t)
  exact IsIso.comp_isIso' (Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (structureSheafRing X)) 0).app _))
    (IsIso.comp_isIso' this (Iso.isIso_inv ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (structureSheafRing X)) 0).app _)))

/-- The canonical map of **Stacks 0E1Z** is surjective on `H⁻¹`. -/
instance epi_homologyFunctor_negOne_remarkConeMap :
    Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) (-1)).map
      (remarkConeMap f t)) := by
  rw [homologyFunctor_map_remarkConeMap]
  have : Epi (HomologicalComplex.homologyMap ((pulledNaiveCotangentModelIso f t).hom ≫
      Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) (-1)) := by
    refine (HomologicalComplex.homologyMap_comp (pulledNaiveCotangentModelIso f t).hom
      (Stacks.SheafOfModules.ringedSpaceNaiveCotangentConeMap f t) (-1)).symm ▸ ?_
    have := Stacks.SheafOfModules.epi_homologyMap_ringedSpaceNaiveCotangentConeMap_negOne f t
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) (-1)).mapIso
        (pulledNaiveCotangentModelIso f t))))
      (Stacks.SheafOfModules.epi_homologyMap_ringedSpaceNaiveCotangentConeMap_negOne f t)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
    (Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (structureSheafRing X)) (-1)).app _)))
    (epi_comp' this (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.isIso_inv ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (structureSheafRing X)) (-1)).app _))))

/-- `𝖭𝖫_{S/S'}` lives in degrees `≤ 0`. -/
instance baseNaiveCotangent_isStrictlyLE : (baseNaiveCotangent t).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
    Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u} _ _ _ _ i (by omega)
      (by omega)

/-- The comparison `Lf^*𝖭𝖫_{S/S'} ⟶ f^*𝖭𝖫_{S/S'}` is an isomorphism on `H⁰`. -/
instance isIso_homologyFunctor_zero_remarkPullbackComparison :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
      (remarkPullbackComparison f t)) := by
  open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
  have := isIso_homologyFunctor_map_derivedPullbackComparison_app
    f (baseNaiveCotangent t) 0 inferInstance
  refine (congrArg (fun k => IsIso k)
    ((Functor.map_comp (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) 0)
    _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·)
      (Functor.map_comp _ _ _)))))).mpr ?_
  exact IsIso.comp_isIso' (Iso.isIso_hom
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
        ((derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso _).app _).symm)))
    (IsIso.comp_isIso' this (IsIso.comp_isIso' (Iso.isIso_hom
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
        (DerivedCategory.Qh.mapIso
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _))))
      (Iso.isIso_hom ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
        ((DerivedCategory.quotientCompQhIso _).app _)))))

/-- The remark's two maps compose to zero in `D(𝒪_X)`. -/
theorem derivedPullbackNaiveCotangentMap_comp_relativeNaiveCotangentObjMap :
    derivedPullbackNaiveCotangentMap f t ≫ relativeNaiveCotangentObjMap f t = 0 := by
  refine (congrArg (· ≫ relativeNaiveCotangentObjMap f t)
    ((remarkPullbackComparison_comp_pulledMap f t).symm.trans
      (congrArg (_ ≫ ·) (remarkConeMap_comp_mor₁ f t).symm))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (comp_distTriang_mor_zero₁₂ _ (remarkConeTriangle_distinguished f t))))).trans ?_
  exact (congrArg (_ ≫ ·) comp_zero).trans comp_zero

/-- **Stacks Project, Tag 0GQ4**, what the remark's two maps
`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` satisfy: they are *close to* forming a distinguished
triangle, by **Stacks 0E1Z**.  Precisely:

* the composite `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` vanishes in `D(𝒪_X)`;
* the first map factors as the comparison `Lf^*𝖭𝖫_{S/S'} ⟶ f^*𝖭𝖫_{S/S'}` of **Stacks 06YJ**
  (an isomorphism on `H⁰`) followed by the canonical map `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`;
* the second map sits in a distinguished triangle `C[-1] ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S} ⟶ C`, with
  `C` the cone of `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`;
* the canonical map `f^*𝖭𝖫_{S/S'} ⟶ C[-1]` of **Stacks 0E1Z** lifts `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`
  along `C[-1] ⟶ 𝖭𝖫_{X/S'}`, is an isomorphism on `H⁰` and is surjective on `H⁻¹`.

So the maps form a distinguished triangle exactly when the comparison with the cone is an
isomorphism; the remark only says they are close to one, and nothing more is claimed. -/
@[stacks 0GQ4]
theorem naiveCotangentRemark_closeToDistinguishedTriangle :
    derivedPullbackNaiveCotangentMap f t ≫ relativeNaiveCotangentObjMap f t = 0 ∧
    remarkPullbackComparison f t ≫ remarkPulledMap f t = derivedPullbackNaiveCotangentMap f t ∧
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
      (remarkPullbackComparison f t)) ∧
    remarkConeTriangle f t ∈ distTriang _ ∧
    (remarkConeTriangle f t).mor₂ = relativeNaiveCotangentObjMap f t ∧
    remarkConeMap f t ≫ (remarkConeTriangle f t).mor₁ = remarkPulledMap f t ∧
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
      (remarkConeMap f t)) ∧
    Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) (-1)).map
      (remarkConeMap f t)) :=
  ⟨derivedPullbackNaiveCotangentMap_comp_relativeNaiveCotangentObjMap f t,
    remarkPullbackComparison_comp_pulledMap f t, inferInstance,
    remarkConeTriangle_distinguished f t, rfl, remarkConeMap_comp_mor₁ f t, inferInstance,
    inferInstance⟩

end CloseToTriangle

end AlgebraicGeometry.RingedSpaceThickening

end
