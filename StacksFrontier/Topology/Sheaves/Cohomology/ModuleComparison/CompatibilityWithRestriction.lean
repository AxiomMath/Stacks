module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of module and abelian-sheaf cohomology is compatible with restriction

For a sheaf of rings `R` on a site and an object `U` of the site,
`ModuleSheafCohomology.sectionsComparisonIso` is the comparison of Stacks 03FD as a *named*
isomorphism: deriving the sections over `U` of the underlying abelian sheaf of a sheaf of
`R`-modules agrees, in every degree, with forgetting to an abelian sheaf and deriving sections
over `U` there.  Because it is named and not chosen, asking how the comparisons for two
different objects of the site are related is a meaningful question, and this file answers it.

## Main results

* `sectionsRestriction`: restriction of sections of abelian sheaves along a morphism of the
  site.
* `evaluationRepresentation_naturality`: the corepresentation of sections over `U` by the
  sheafification of the free abelian presheaf on `yoneda.obj U`
  (`ModuleSheafCohomology.evaluationRepresentation`) is natural in `U`, against restriction of
  sections on one side and the induced map of corepresenting objects on the other.
* `sectionsComparisonIso_naturality`: **the compatibility with restriction.**  For `f : U ⟶ V`
  the comparisons for `U` and for `V` commute, in every degree, with the maps that
  `NatTrans.rightDerived` induces from restriction of sections.
* `canonicalSectionsForgetIso`: the comparison of Stacks 01F1 part (1) over a topological space,
  in the shape of the statement — module-valued sections derived first, the module structure
  forgotten only at the end — built from `sectionsComparisonIso` and therefore constructive in
  every degree.
* `canonicalSectionsForgetIso_naturality_open`: the restriction compatibility for that
  comparison, which is the clause *part (1), compatibility with restriction* of Stacks 01F1.

## Implementation notes

The homological algebra is already done: `ModuleSheafCohomology.comparisonIso_naturality` proves
the compatibility in full generality, for any transformation `ρ : G' ⟶ G` of corepresented
functors whose corepresentations are matched by maps `x` and `y` of corepresenting objects.  What
this file supplies is the site-level instantiation, namely the two compatibilities that the
general statement consumes:

* `evaluationRepresentation_naturality` — for `f : U ⟶ V` the corepresentation of sections is
  natural in `U`.  Both sides are read through the sheafification adjunction, where the statement
  is `Adjunction.homEquiv_naturality_left` together with the computation of
  `ModuleSheafCohomology.freeEvaluationHomAddEquiv` on a generator: the generator `𝟙 U` of the
  free abelian group on `yoneda.obj U` evaluated at `U` and the generator `𝟙 V` of the free
  abelian group on `yoneda.obj V` evaluated at `U` both map to the generator `f`.
* `ModuleSheafCohomology.tensorSheafHomIso_naturality` — the identification of morphisms out of
  the sheafified extension of scalars with morphisms out of the sheafification is natural in the
  abelian presheaf.  That one is proved where the extension-of-scalars adjunction lives, because
  its proof needs the private adjunction data of that file.

The comparison `canonicalSectionsForgetIso` **is** the comparison that Stacks 01F1 part (1) is
tagged on.  `underlyingSectionsIso` is `ModuleSheafCohomology.sectionsComparisonIso`, built
without choice from the constructive Stacks 03FD of `ModuleCohomologyComparisonDef`.  This
matters: a comparison obtained as `Exists.choose` of the existence form of Stacks 03FD satisfies
no equation beyond the degree-zero normalization it was chosen with, so nothing relating the
comparisons for two different opens could be proved about it.  As it is,
`canonicalSectionsForgetIso = rightDerivedEvaluationForgetIso ≪≫ underlyingSectionsIso` holds in
*every* degree, and all three part-(1) clauses are tagged on this one object.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

open ModuleSheafCohomology

attribute [local instance] ModuleSheafCohomology.toSheaf_preservesFiniteColimits

/-! ### Naturality of the corepresentation of sections in the object of the site -/

section Site

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})

/-- Taking sections over an object `U` of the site is an additive functor on abelian sheaves. -/
local instance sheafSectionsSite_additive (U : C) :
    ((sheafSections J Ab.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Taking sections over an object `U` of the site preserves finite limits of abelian sheaves. -/
local instance sheafSectionsSite_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits ((sheafSections J Ab.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J Ab.{u}).symm

/-- The morphism of free abelian presheaves on representables induced by `f : U ⟶ V`. -/
abbrev freeYonedaMap {U V : C} (f : U ⟶ V) :
    yoneda.obj U ⋙ AddCommGrpCat.free ⟶ yoneda.obj V ⋙ AddCommGrpCat.free :=
  Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free

/-- The morphism of the objects corepresenting sections induced by `f : U ⟶ V`: the
sheafification of `freeYonedaMap`. -/
abbrev freeYonedaSheafMap {U V : C} (f : U ⟶ V) :
    (presheafToSheaf J Ab.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶
      (presheafToSheaf J Ab.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf J Ab.{u}).map (freeYonedaMap f)

/-- Restriction of sections of abelian sheaves along `f : U ⟶ V`. -/
abbrev sectionsRestriction {U V : C} (f : U ⟶ V) :
    (sheafSections J Ab.{u}).obj (op V) ⟶ (sheafSections J Ab.{u}).obj (op U) :=
  (sheafSections J Ab.{u}).map f.op

/-- A square of morphisms between isomorphic pairs commutes for the forward isomorphisms
exactly when it commutes for the inverse ones. -/
private theorem comp_hom_eq_hom_comp_iff {D : Type*} [Category D] {X Y X' Y' : D}
    {e : X ≅ Y} {e' : X' ≅ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'} :
    a ≫ e'.hom = e.hom ≫ b ↔ b ≫ e'.inv = e.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact eq_comm

/-- **The corepresentation of sections is natural in the object of the site**, in the direction
in which it is an identification of morphisms out of the corepresenting object with sections.
Read on a sheaf `F`, both sides send a morphism `g` out of the corepresenting object of `U` to
the section `g` corresponds to over `U`, restricted along `f`; the two computations of that
section differ by which generator of a free abelian group the restriction is applied to, and the
two generators — `𝟙 U` in the presheaf on `yoneda.obj U` and `𝟙 V` in the presheaf on
`yoneda.obj V` — both go to the generator `f`. -/
theorem evaluationRepresentation_inv_naturality {U V : C} (f : U ⟶ V) :
    preadditiveCoyoneda.map (freeYonedaSheafMap J f).op ≫ (evaluationRepresentation J U).inv =
      (evaluationRepresentation J V).inv ≫ sectionsRestriction J f := by
  refine NatTrans.ext (funext fun F => ?_)
  ext g
  change ((presheafToSheaf J Ab.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ F) at g
  show freeEvaluationHomAddEquiv U F.obj
      ((sheafificationAdjunction J Ab.{u}).homEquiv
        (yoneda.obj U ⋙ AddCommGrpCat.free) F (freeYonedaSheafMap J f ≫ g)) =
    F.obj.map f.op (freeEvaluationHomAddEquiv V F.obj
      ((sheafificationAdjunction J Ab.{u}).homEquiv (yoneda.obj V ⋙ AddCommGrpCat.free) F g))
  rw [Adjunction.homEquiv_naturality_left]
  set k := (sheafificationAdjunction J Ab.{u}).homEquiv (yoneda.obj V ⋙ AddCommGrpCat.free) F g
    with hk
  have hgen : (freeYonedaMap f).app (op U) (FreeAbelianGroup.of (𝟙 U)) =
      (yoneda.obj V ⋙ AddCommGrpCat.free).map f.op (FreeAbelianGroup.of (𝟙 V)) := by
    show FreeAbelianGroup.map _ (FreeAbelianGroup.of (𝟙 U)) =
      FreeAbelianGroup.map _ (FreeAbelianGroup.of (𝟙 V))
    simp
  show k.app (op U) ((freeYonedaMap f).app (op U) (FreeAbelianGroup.of (𝟙 U))) = _
  exact (congrArg (fun z => k.app (op U) z) hgen).trans
    (NatTrans.naturality_apply k f.op (FreeAbelianGroup.of (𝟙 V)))

/-- **The first compatibility consumed by the naturality of Stacks 03FD.** The corepresentation
of sections over an object of the site is natural in that object: restriction of sections along
`f : U ⟶ V` corresponds, under the corepresentations, to precomposition with the induced map
`freeYonedaSheafMap` of corepresenting objects. -/
theorem evaluationRepresentation_naturality {U V : C} (f : U ⟶ V) :
    sectionsRestriction J f ≫ (evaluationRepresentation J U).hom =
      (evaluationRepresentation J V).hom ≫
        preadditiveCoyoneda.map (freeYonedaSheafMap J f).op := by
  exact comp_hom_eq_hom_comp_iff.2 (evaluationRepresentation_inv_naturality J f)

/-- **Stacks 03FD is compatible with restriction of sections.** For `f : U ⟶ V` the comparisons
of `ModuleSheafCohomology.sectionsComparisonIso` for `U` and for `V` commute, in every degree,
with the maps `NatTrans.rightDerived` induces from restriction of sections.

This is `ModuleSheafCohomology.comparisonIso_naturality` — where the mathematics is: both sides
are morphisms out of a universal `δ`-functor, so Stacks 010S reduces the claim to degree zero —
instantiated at the site.  The two compatibilities it consumes are
`evaluationRepresentation_naturality` for the corepresentation of sections and
`ModuleSheafCohomology.tensorSheafHomIso_naturality` for the corepresentation of the composite;
the second is turned from naturality in the abelian presheaf into the shape of
`ModuleSheafCohomology.compCorepresentation` by cancelling the corepresentation of sections. -/
theorem sectionsComparisonIso_naturality {U V : C} (f : U ⟶ V) (n : ℕ) :
    NatTrans.rightDerived (Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
          (sectionsRestriction J f)) n ≫ (sectionsComparisonIso J R U n).hom =
      (sectionsComparisonIso J R V n).hom ≫
        Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
          (NatTrans.rightDerived (sectionsRestriction J f) n) := by
  refine comparisonIso_naturality (SheafOfModules.toSheaf.{u} R) (sectionsRestriction J f)
    (freeYonedaSheafMap J f) (evaluationRepresentation J U) (evaluationRepresentation J V)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).map
      (tensorPresheafMap R.obj (freeYonedaMap f)))
    (tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free))
    (tensorSheafHomIso J R (yoneda.obj V ⋙ AddCommGrpCat.free))
    (fun I _ index extension => ext_eq_zero_of_injective_toSheaf J R I U index extension)
    (fun I _ index extension => ext_eq_zero_of_injective_toSheaf J R I V index extension)
    (evaluationRepresentation_naturality J f) ?_ n
  have hb := tensorSheafHomIso_naturality J R (freeYonedaMap f)
  have hxb := comp_hom_eq_hom_comp_iff.1 hb
  simp only [compCorepresentation, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, evaluationRepresentation_naturality,
    Functor.whiskerLeft_comp, Category.assoc, hxb, Category.assoc]

end Site

/-! ### The comparison of Stacks 01F1 part (1) without a choice, and its restriction clause -/

section Space

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Stacks 01F1, part (1), as a constructive comparison.** Cohomology over an open `U`,
computed by deriving module-valued sections and then forgetting the module structure, agrees
naturally with cohomology computed after forgetting the coefficient sheaf to an abelian sheaf.

This is the statement of `Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`, but
built in every degree from `ModuleSheafCohomology.sectionsComparisonIso` rather than, in positive
degree, from the `Exists.choose` of the existence form of Stacks 03FD.  That is what makes
`canonicalSectionsForgetIso_naturality_open` provable; see the module docstring for the
relationship between the two comparisons. -/
def canonicalSectionsForgetIso (U : Opens X) (n : ℕ) :
    (SheafOfModules.evaluation R (op U)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf R ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).rightDerived n :=
  rightDerivedEvaluationForgetIso R U n ≪≫
    sectionsComparisonIso (Opens.grothendieckTopology X) R U n

/-- The comparison `canonicalSectionsForgetIso` is `ModuleSheafCohomology.sectionsComparisonIso`
read through the canonical identification `rightDerivedEvaluationForgetIso` of the module-valued
side with the derived composite.  This is the form in which the restriction clause uses it. -/
theorem rightDerivedEvaluationForgetIso_inv_comp_canonicalSectionsForgetIso
    (U : Opens X) (n : ℕ) :
    (rightDerivedEvaluationForgetIso R U n).inv ≫ (canonicalSectionsForgetIso R U n).hom =
      (sectionsComparisonIso (Opens.grothendieckTopology X) R U n).hom := by
  rw [canonicalSectionsForgetIso, Iso.trans_hom, Iso.inv_hom_id_assoc]

/-- **Stacks 01F1, part (1), compatibility with restriction.** The comparison of cohomology over
an open subset commutes with restriction to a smaller open subset.  The left-hand restriction is
derived from the underlying abelian-group-valued module sections; `rightDerivedEvaluationForgetIso`
identifies it with module-valued cohomology.

Through that identification the comparison is `ModuleSheafCohomology.sectionsComparisonIso`, and
the statement is `sectionsComparisonIso_naturality` for the morphism `homOfLE h : U ⟶ V` of the
site of opens, read at the module sheaf `M`. -/
@[stacks 01F1 "part (1), compatibility with restriction"]
theorem canonicalSectionsForgetIso_naturality_open {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (M : SheafOfModules.{u} R) :
    (NatTrans.rightDerived
          (Functor.whiskerLeft (SheafOfModules.toSheaf R)
            (sectionsRestriction (Opens.grothendieckTopology X) (homOfLE h))) n).app M ≫
        (rightDerivedEvaluationForgetIso R U n).inv.app M ≫
        (canonicalSectionsForgetIso R U n).hom.app M =
      (rightDerivedEvaluationForgetIso R V n).inv.app M ≫
        (canonicalSectionsForgetIso R V n).hom.app M ≫
        (NatTrans.rightDerived
          (sectionsRestriction (Opens.grothendieckTopology X) (homOfLE h)) n).app
          ((SheafOfModules.toSheaf R).obj M) := by
  have key := sectionsComparisonIso_naturality (Opens.grothendieckTopology X) R (homOfLE h) n
  have hU := rightDerivedEvaluationForgetIso_inv_comp_canonicalSectionsForgetIso R U n
  have hV := rightDerivedEvaluationForgetIso_inv_comp_canonicalSectionsForgetIso R V n
  have hcomp : ∀ (W : Opens X) (e : (rightDerivedEvaluationForgetIso R W n).inv ≫
        (canonicalSectionsForgetIso R W n).hom =
        (sectionsComparisonIso (Opens.grothendieckTopology X) R W n).hom),
      (rightDerivedEvaluationForgetIso R W n).inv.app M ≫
          (canonicalSectionsForgetIso R W n).hom.app M =
        (sectionsComparisonIso (Opens.grothendieckTopology X) R W n).hom.app M :=
    fun W e => NatTrans.congr_app e M
  rw [hcomp U hU, ← Category.assoc, hcomp V hV]
  exact NatTrans.congr_app key M

end Space

end Stacks.Cohomology.ModuleComparison

end
