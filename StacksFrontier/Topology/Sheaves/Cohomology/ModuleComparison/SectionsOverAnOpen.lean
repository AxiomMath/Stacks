module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a sheaf of modules over an open agrees with that of its underlying abelian sheaf

Let `X` be a topological space and let `R` be a sheaf of rings on `X`, so that
`SheafOfModules R` is the category of sheaves of `R`-modules.  For an open `U` of `X` the
cohomology of an `R`-module sheaf over `U` may be computed in two ways: derive the
module-valued sections functor `Γ(U, -) : SheafOfModules R ⥤ ModuleCat (R(U))` and then forget
the module structure, or forget the coefficient sheaf to a sheaf of abelian groups and derive
sections there.  The two agree, naturally in the module sheaf.

This file supplies the two halves out of which the comparison is assembled; the comparison
itself, together with its degree-zero normalization, is
`StacksDraft.Ch20.Sec12.Tag01F1Part1`.  The remaining three comparisons packaged in Tag 01F1
(higher direct images, and the two comparisons for bounded below complexes on
`DerivedCategory.Plus`) are *not* covered here.

## Main results

* `rightDerivedCompIso`: for an additive functor `F` and an exact additive functor `G`, the
  right derived functors of `F` composed with `G` agree with the right derived functors of the
  composite.  This is pure homological algebra and is stated for arbitrary abelian categories.
* `rightDerivedEvaluationForgetIso`: the instance of the previous isomorphism which says that
  deriving module-valued sections over `U` and then forgetting agrees with deriving the
  underlying abelian-group-valued sections functor.  This is the canonical half of the
  comparison; no choices are involved.
* `underlyingSectionsIso` and `underlyingSectionsIso_zero`: the comparison of Tag 03FD,
  specialized to the site of a topological space, together with its degree-zero normalization.

## Implementation notes

The mathematics is not redone here.  For a Grothendieck topology `J` on a small category `C`
and a sheaf of rings `R` for `J`, `ModuleSheafCohomology.sectionsComparisonIso` already
proves — by the `δ`-functor argument of Tag 03FD — that
`(SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat).obj (op U)).rightDerived n` is
naturally isomorphic to `SheafOfModules.toSheaf R ⋙ ((sheafSections J AddCommGrpCat).obj
(op U)).rightDerived n`, normalized in degree zero.  Since `Opens X` is a small category and
`Opens.grothendieckTopology X` is a Grothendieck topology on it, that result applies verbatim
to the site of a topological space; all of its hypotheses are discharged by the instances
recorded below, and for a ringed space in the sense of `AlgebraicGeometry.RingedSpace` one
takes `R` to be `structureSheafRing X`.  That isomorphism is *named*, not
chosen: `underlyingSectionsIso` is its instance at the site of opens, and nothing here goes
through `ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`, the existence form of
Tag 03FD, whose `Exists.choose` satisfies no equation beyond the normalization it was chosen
with.

What that leaves is the difference between the two shapes.  The source result derives the
*composite* `SheafOfModules.toSheaf R ⋙ Γ(U, -)`, which is `Tag01E3`'s `(secF R U).rightDerived n`;
Tag 01F1 states the comparison with the module-valued sections derived first and the module
structure forgotten only at the end.  The functor `SheafOfModules.evaluation R (op U)` followed by
`forget₂ (ModuleCat (R(U))) AddCommGrpCat` *is* `SheafOfModules.toSheaf R ⋙ Γ(U, -)`, by
definitional unfolding, and this is recorded as `evaluationCompForgetIso`; but deriving and then
forgetting is a genuinely different functor from deriving the composite, and the comparison
between them is `rightDerivedCompIso`, proved here from scratch by comparing injective
resolutions degreewise.  Mathlib has no such lemma; the argument is the dual of the
`leftDerived` one in `StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

/-! ### An exact functor commutes with right derived functors -/

section Derived

variable {A B D : Type*} [Category A] [Category B] [Category D]

/-- An exact additive functor `G` commutes with the degree `n` homology of cochain complexes:
on a complex `K` the comparison is `ShortComplex.mapHomologyIso` applied to the short complex
of `K` in degree `n`. -/
noncomputable def homologyMapFunctorIso [Abelian B] [Abelian D] (G : B ⥤ D) [G.Additive]
    [G.PreservesHomology] (n : ℕ) :
    G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n ≅
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n ⋙ G :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso G)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) n).map f) G)

/-- Given `e : F ⋙ G ≅ H` with `G` exact, applying `F` degreewise, taking degree `n` homology
and then applying `G` agrees with applying `H` degreewise and taking degree `n` homology.  This
is the complex-level form of `rightDerivedCompIso`. -/
noncomputable def mapComplexHomologyIso [Abelian A] [Abelian B] [Abelian D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    [G.PreservesHomology] (e : F ⋙ G ≅ H) (n : ℕ) :
    F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n ⋙ G ≅
      H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n :=
  Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℕ))
      (homologyMapFunctorIso G n).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ))
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n)

/-- **An exact functor commutes with right derived functors.**  If `G` is additive and exact
and `e : F ⋙ G ≅ H`, then deriving `F` and then applying `G` agrees with deriving `H`,
naturally in the object.  Both sides are computed on the chosen injective resolution, where the
comparison is `mapComplexHomologyIso`; naturality holds because a morphism descends to a map of
injective resolutions. -/
noncomputable def rightDerivedCompIso [Abelian A] [HasInjectiveResolutions A] [Abelian B]
    [Abelian D] (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    [G.PreservesHomology] (e : F ⋙ G ≅ H) (n : ℕ) :
    F.rightDerived n ⋙ G ≅ H.rightDerived n := by
  refine NatIso.ofComponents (fun M =>
    G.mapIso ((injectiveResolution M).isoRightDerivedObj F n) ≪≫
      (mapComplexHomologyIso F G H e n).app _ ≪≫
      ((injectiveResolution M).isoRightDerivedObj H n).symm) ?_
  intro M N f
  have hc : (injectiveResolution M).ι.f 0 ≫
      (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M)).f 0 =
        f ≫ (injectiveResolution N).ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f (injectiveResolution N) (injectiveResolution M)
  have hE : ∀ {Z : D} (k : (H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
          (injectiveResolution N).cocomplex ⟶ Z),
      G.map ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map
            (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M))) ≫
        ((mapComplexHomologyIso F G H e n).hom.app (injectiveResolution N).cocomplex ≫ k) =
          (mapComplexHomologyIso F G H e n).hom.app (injectiveResolution M).cocomplex ≫
            ((H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
                (InjectiveResolution.desc f (injectiveResolution N)
                  (injectiveResolution M)) ≫ k) := by
    have hnat : G.map ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map
            (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M))) ≫
        (mapComplexHomologyIso F G H e n).hom.app (injectiveResolution N).cocomplex =
          (mapComplexHomologyIso F G H e n).hom.app (injectiveResolution M).cocomplex ≫
            (H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
                (InjectiveResolution.desc f (injectiveResolution N)
                  (injectiveResolution M)) :=
      (mapComplexHomologyIso F G H e n).hom.naturality _
    intro Z k
    rw [← Category.assoc, hnat, Category.assoc]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.comp_map, Iso.app_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f (injectiveResolution M)
      (injectiveResolution N) _ hc F n, Functor.map_comp_assoc,
    InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution M)
      (injectiveResolution N) _ hc H n, hE]

end Derived

/-! ### The site of a topological space -/

section Space

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X)

attribute [local instance] ModuleSheafCohomology.toSheaf_preservesFiniteColimits

/-- Sections over an open of an abelian sheaf form an additive functor. -/
instance sheafSections_additive :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Sections over an open of an abelian sheaf are left exact: the functor is isomorphic to
evaluation of the underlying presheaf, which preserves finite limits. -/
instance sheafSections_preservesFiniteLimits :
    PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation (Opens.grothendieckTopology X) AddCommGrpCat.{u}).symm

/-- Module-valued sections over an open form an additive functor. -/
instance moduleEvaluation_additive : (SheafOfModules.evaluation R (op U)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Module-valued sections over an open, followed by forgetting the module structure, *is* the
functor obtained by forgetting the coefficient sheaf to an abelian sheaf and taking sections
over the open: the two functors are definitionally equal. -/
def evaluationCompForgetIso :
    SheafOfModules.evaluation R (op U) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U) :=
  Iso.refl _

/-- Deriving module-valued sections over `U` and then forgetting the module structure agrees
with deriving the underlying abelian-group-valued sections functor, naturally in the module
sheaf.  This is the canonical half of the comparison of Tag 01F1 part (1); its target is the
cohomology functor `H^n(U, -)` of Tag 01E3. -/
noncomputable def rightDerivedEvaluationForgetIso (n : ℕ) :
    (SheafOfModules.evaluation R (op U)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} ≅
      (SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).rightDerived n :=
  rightDerivedCompIso _ _ _ (evaluationCompForgetIso R U) n

/-- The comparison supplied by Tag 03FD at the site of a topological space: deriving the
sections of the underlying abelian sheaf agrees, in every degree, with forgetting and then
deriving.  This is `ModuleSheafCohomology.sectionsComparisonIso`, which is constructed and not
chosen, so statements relating the comparisons for two different opens are meaningful. -/
noncomputable def underlyingSectionsIso : ∀ n : ℕ,
    (SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).rightDerived n ≅
      SheafOfModules.toSheaf R ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).rightDerived n :=
  ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X) R U

/-- The degree-zero normalization of `underlyingSectionsIso`, as supplied by Tag 03FD. -/
theorem underlyingSectionsIso_zero :
    (SheafOfModules.toSheaf R ⋙
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op U)).toRightDerivedZero ≫ (underlyingSectionsIso R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf R)
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).toRightDerivedZero :=
  ModuleSheafCohomology.toRightDerivedZero_comp_sectionsComparisonIso
    (Opens.grothendieckTopology X) R U

end Space

end Stacks.Cohomology.ModuleComparison

end
