module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PreimageSectionsShiftedHomRestrict

/-!
# The value identification of Tag 0D66(2) is compatible with restriction

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K`, `L` be objects of the
unbounded derived category `D(𝒪_X)`. By [Stacks, Tag 0D66] part (2) the presheaf of
`𝒪_Y`-modules `V ↦ H^0(f⁻¹ V, RSheafHom(K, L))` is a sheaf, and
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv` identifies its
value on `V` with the group `Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` of morphisms of the restrictions. This
file proves that this identification carries the restriction maps of the presheaf to the
restriction of morphisms of derived categories, `AlgebraicGeometry.RingedSite.restrictDerivedHom`.

## Main results

* `Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`: the
  value identification commutes with restriction along `V' ≤ V`.
* `Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso_restrict_forget₂`:
  the restriction square of `preimageCohomologyEvaluationIso`, read as a square of abelian groups.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections
  derivedPreimageSectionsRestrictHomology)
open Stacks.SheafOfModules (homSheafObject ringedSite)

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits
attribute [local instance] isGrothendieckAbelian_moduleSheaves

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
variable (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-! ### Forgetting module structures -/

/-- If `p ≫ q = p' ≫ q'` for morphisms of abelian groups, then `q (p a) = q' (p' a)`. -/
private theorem apply_of_comp_eq {A B B' C : AddCommGrpCat.{u}}
    {p : A ⟶ B} {q : B ⟶ C} {p' : A ⟶ B'} {q' : B' ⟶ C}
    (h : p ≫ q = p' ≫ q') (a : A) : q (p a) = q' (p' a) := by
  simpa only [CategoryTheory.comp_apply] using congrArg (fun (φ : A ⟶ C) => φ a) h

/-- A functor carries a commutative square to a commutative square. -/
private theorem map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c d : C} {p : a ⟶ b} {q : b ⟶ d} {p' : a ⟶ c} {q' : c ⟶ d} (h : p ≫ q = p' ≫ q') :
    F.map p ≫ F.map q = F.map p' ≫ F.map q' := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- On morphisms, restricting scalars along `Γ(V, 𝒪_Y) → Γ(V', 𝒪_Y)` and then forgetting the
module structure is forgetting it. -/
theorem forget₂_restrictScalars_map {V V' : Opens Y.carrier} (hV : V' ≤ V)
    {A B : ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))} (φ : A ⟶ B) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
        ((ModuleCat.restrictScalars
          ((structureSheafRing Y).obj.map hV.hom.op).hom).map φ) =
      (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))) AddCommGrpCat.{u}).map
        φ :=
  rfl

/-- The restriction map of the underlying presheaf of abelian groups is the forgetful image of the
restriction of the presheaf of modules. -/
theorem forget₂_restriction_app (P : PresheafOfModules.{u} (structureSheafRing Y).obj)
    {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
        ((PresheafOfModules.restriction (structureSheafRing Y).obj hV.hom.op).app P) =
      P.presheaf.map hV.hom.op :=
  rfl

/-! ### The evaluation square, read in abelian groups -/

/-- The square of
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso_restrict`, read as a
square of abelian groups: the restriction of scalars on its lower right becomes the forgetful
functor over `V'`, and the restriction of the presheaf of modules on its lower left becomes the
restriction map of the underlying presheaf. -/
theorem preimageCohomologyEvaluationIso_restrict_forget₂ {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (i : ℤ) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
          ((preimageCohomologyEvaluationIso f V i).hom.app M) ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
          ((derivedPreimageSectionsRestrictHomology f hV i).app M) =
      ((derivedPreimageCohomologyPresheaf f M i).presheaf.map hV.hom.op) ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))) AddCommGrpCat.{u}).map
          ((preimageCohomologyEvaluationIso f V' i).hom.app M) := by
  refine (map_square
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u})
    (preimageCohomologyEvaluationIso_restrict f hV i M)).trans ?_
  rw [forget₂_restrictScalars_map hV]
  rfl

/-! ### The value identification is compatible with restriction -/

/-- Applying the forgetful image of a morphism of modules to an element is applying the
morphism. -/
private theorem forget₂_apply {V : Opens Y.carrier}
    {A B : ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))} (φ : A ⟶ B) (x : A) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map φ x =
      φ x :=
  rfl

/-- The value identification `derivedPreimageHomPresheafValueEquiv` is the evaluation comparison
`preimageCohomologyEvaluationIso` followed by the identification
`preimageSectionsHomologyEquivShiftedHom` of the hypercohomology of the internal Hom complex with
the `Ext` group. -/
theorem derivedPreimageHomPresheafValueEquiv_apply (V : Opens Y.carrier)
    (s : ((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf.obj
      (op V) : Type u)) :
    derivedPreimageHomPresheafValueEquiv f K L V s =
      Linear.homCongr ℤ (Iso.refl _)
          ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V).obj L))
        (preimageSectionsHomologyEquivShiftedHom f K L V 0
          ((forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))
              AddCommGrpCat.{u}).map
            ((preimageCohomologyEvaluationIso f V 0).hom.app
              (homSheafObject X.sheaf K L)) s)) :=
  rfl

/-- The value identification of [Stacks, Tag 0D66] part (2) is compatible with restriction: for
`V' ≤ V`, restricting a section of the presheaf `V ↦ H^0(f⁻¹ V, RSheafHom(K, L))` to `V'` and
then reading it as a morphism `K|_{f⁻¹ V'} ⟶ L|_{f⁻¹ V'}` gives the same morphism as reading it
over `V` and restricting the resulting morphism of derived categories along `f⁻¹ V' ⟶ f⁻¹ V`. -/
theorem derivedPreimageHomPresheafValueEquiv_map {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (s : ((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf.obj
      (op V) : Type u)) :
    derivedPreimageHomPresheafValueEquiv f K L V'
        (((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L)
            0).presheaf.map hV.hom.op) s) =
      AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite X.sheaf)
        ((opensMap f).map hV.hom) K L
        (derivedPreimageHomPresheafValueEquiv f K L V s) := by
  have h₃ := apply_of_comp_eq
    (preimageCohomologyEvaluationIso_restrict_forget₂ f hV 0 (homSheafObject X.sheaf K L)) s
  have h₁₂ := preimageSectionsHomologyEquivShiftedHom_zero_restrict f K L hV
    ((forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
      ((preimageCohomologyEvaluationIso f V 0).hom.app (homSheafObject X.sheaf K L)) s)
  refine (derivedPreimageHomPresheafValueEquiv_apply f K L V'
    (((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L)
      0).presheaf.map hV.hom.op) s)).trans ?_
  refine Eq.trans ?_ (congrArg (AlgebraicGeometry.RingedSite.restrictDerivedHom
      (ringedSite X.sheaf) ((opensMap f).map hV.hom) K L)
    (derivedPreimageHomPresheafValueEquiv_apply f K L V s).symm)
  refine Eq.trans ?_ h₁₂.symm
  refine congrArg (fun z => Linear.homCongr ℤ (Iso.refl _)
      ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V').obj L))
      (preimageSectionsHomologyEquivShiftedHom f K L V' 0 z)) ?_
  exact h₃.symm.trans (forget₂_apply _ _)

end Stacks.Cohomology.UnboundedHigherDirectImage

end
