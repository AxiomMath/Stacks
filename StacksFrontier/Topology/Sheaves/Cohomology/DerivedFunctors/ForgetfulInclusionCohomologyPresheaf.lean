module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.StacksAttribute

/-!
# Derived functors of the inclusion of sheaves of modules into presheaves of modules

Let `O` be a sheaf of rings on a topological space `X`. The inclusion
`Mod(O) ⟶ PMod(O)` of sheaves of modules into presheaves of modules is left exact, so it has
right derived functors, and Tag 01ER identifies their values: the presheaf
`R^p ι (F)` evaluated at an open `U` is `H^p(U, F)`, compatibly with restriction between
opens.

The identification is an instance of a general fact: for a left exact `F : A ⥤ B` and an
*exact* `G : B ⥤ C`, one has `F.rightDerived p ⋙ G ≅ (F ⋙ G).rightDerived p`, because both
sides are computed from the same injective resolution and `G` commutes with taking homology.
Here `G` is evaluation at `U`, which is exact on presheaves of modules, resp. evaluation at
`U` after forgetting to abelian groups. Compatibility with restriction is then naturality of
that comparison in `G`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Cohomology.DerivedForget.rightDerivedForgetEvaluationIso`: the value on `U` of the
  `p`-th right derived functor of the inclusion is the `p`-th right derived functor of
  sections on `U`, naturally in the coefficient sheaf.
* `Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso`: after forgetting the
  module structure, that value is `H^p(U, -)`.
* `Stacks.Cohomology.DerivedForget.rightDerivedForgetCohomologyIso_naturality_open`: the
  identification commutes with restriction from `V` to `U ≤ V`, the restriction map on the
  right-hand side being `Hrestrict` of Tag 01E2.

## Implementation notes

Left exactness of the inclusion is Mathlib's instance
`SheafOfModules.Finite.forgetPreservesFiniteLimits`, recorded here with the tag.

The comparison is stated as an isomorphism of *functors* in the coefficient sheaf rather than
objectwise, which is what makes the naturality statement expressible. The standard
Grothendieck-category instances supply sheafification and enough injectives for sheaves of
modules on a space, so these are not extra hypotheses on `X`.

## References

* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace Stacks.Cohomology.DerivedForget

add_to_stacks 01ER "left exact" SheafOfModules.Finite.forgetPreservesFiniteLimits

variable {X : Type u} [TopologicalSpace X]
variable (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- For a left exact functor `F` and an exact functor `G`, the `p`-th right derived functor of
`F` followed by `G` is the `p`-th right derived functor of `F ⋙ G`: both are computed from the
same injective resolution, and `G` commutes with taking homology. -/
noncomputable def rightDerivedCompIso
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [G.PreservesHomology] [(F ⋙ G).Additive] (p : ℕ) :
    F.rightDerived p ⋙ G ≅ (F ⋙ G).rightDerived p := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
      HomotopyCategory.homologyFunctor
    exact (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((injectiveResolutions A).obj X).as).sc p).mapHomologyIso G |>.symm
  · intro X Y f
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
      ((injectiveResolutions A).map f)
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    simp only [Functor.comp_map]
    rw [← hg]
    unfold HomotopyCategory.homologyFunctor
    dsimp [Functor.comp_map, Functor.mapHomotopyCategory,
      HomologicalComplex.homologyFunctor]
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) p).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

/-- Evaluation of sheaves of modules on an open subset is additive. -/
instance evaluation_additive (U : Opens X) :
    (SheafOfModules.evaluation O (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- **Stacks 01ER.** The value on `U` of the `p`-th right derived functor of the inclusion
`Mod(O) ⟶ PMod(O)` is canonically the `p`-th right derived functor of sections on `U`. The
isomorphism is natural in the coefficient sheaf. -/
@[stacks 01ER "right derived functors"]
noncomputable def rightDerivedForgetEvaluationIso (U : Opens X) (p : ℕ) :
    (SheafOfModules.forget O).rightDerived p ⋙
        PresheafOfModules.evaluation O.obj (op U) ≅
      (SheafOfModules.evaluation O (op U)).rightDerived p := by
  have : (PresheafOfModules.evaluation O.obj (op U)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact rightDerivedCompIso (SheafOfModules.forget O) _ p

/-- **Stacks 01ER.** After forgetting the module structure, the value on `U` of the `p`-th
right derived functor of `Mod(O) ⟶ PMod(O)` is canonically `H^p(U, -)`. This is an isomorphism
of functors in the coefficient sheaf. -/
@[stacks 01ER "cohomology presheaf"]
noncomputable def rightDerivedForgetCohomologyIso (U : Opens X) (p : ℕ) :
    (SheafOfModules.forget O).rightDerived p ⋙
        PresheafOfModules.toPresheaf O.obj ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U) ≅
      Hfunctor O U p := by
  have : (PresheafOfModules.toPresheaf O.obj ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact rightDerivedCompIso (A := SheafOfModules.{u} O)
    (B := PresheafOfModules.{u} O.obj) (C := AddCommGrpCat.{u})
    (SheafOfModules.forget O) _ p

/-- **Stacks 01ER.** The canonical identification of the derived presheaf with
`U ↦ H^p(U, -)` commutes with restriction from an open subset `V` to an open subset `U`. -/
@[stacks 01ER "compatibility with restriction"]
lemma rightDerivedForgetCohomologyIso_naturality_open
    {U V : Opens X} (h : U ≤ V) (p : ℕ) (F : SheafOfModules O) :
    ((PresheafOfModules.toPresheaf O.obj).obj
          (((SheafOfModules.forget O).rightDerived p).obj F)).map (homOfLE h).op ≫
        (rightDerivedForgetCohomologyIso O U p).hom.app F =
      (rightDerivedForgetCohomologyIso O V p).hom.app F ≫ Hrestrict O h p F := by
  let GV : PresheafOfModules.{u} O.obj ⥤ AddCommGrpCat.{u} :=
    PresheafOfModules.toPresheaf O.obj ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)
  let GU : PresheafOfModules.{u} O.obj ⥤ AddCommGrpCat.{u} :=
    PresheafOfModules.toPresheaf O.obj ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)
  let α : GV ⟶ GU := Functor.whiskerLeft (PresheafOfModules.toPresheaf O.obj)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map (homOfLE h).op)
  have : GV.PreservesHomology := GV.preservesHomologyOfExact
  have : GU.PreservesHomology := GU.preservesHomologyOfExact
  change α.app (((SheafOfModules.forget O).rightDerived p).obj F) ≫
      (rightDerivedCompIso (SheafOfModules.forget O) GU p).hom.app F =
    (rightDerivedCompIso (SheafOfModules.forget O) GV p).hom.app F ≫
      (NatTrans.rightDerived (Functor.whiskerLeft (SheafOfModules.forget O) α) p).app F
  unfold rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  let K := ((SheafOfModules.forget O).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions (SheafOfModules O)).obj F).as
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_obj]
  unfold HomotopyCategory.homologyFunctor
  change α.app (K.sc p).homology ≫ ((K.sc p).mapHomologyIso GU).inv =
    ((K.sc p).mapHomologyIso GV).inv ≫
      ShortComplex.homologyMap ((K.sc p).mapNatTrans α)
  simp only [NatTrans.app_homology, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Stacks.Cohomology.DerivedForget
