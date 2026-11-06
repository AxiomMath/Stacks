module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical comparison of module and abelian-sheaf cohomology

This file supplies the *acyclicity* input behind Stacks Tag 01F1 part (1) and uses it to prove
the bounded-below comparison of Tag 01F1.

Let `J` be a Grothendieck topology on a small category `C`, let `R` be a sheaf of rings for `J`
and let `U` be an object of `C`.  The content is that the underlying abelian sheaf of an
injective `R`-module sheaf is *right acyclic* for sections over `U` in the sense of
[Stacks, Tag 0157]: the single complex on it computes the right derived functor of `Γ(U, -)` on
`D⁺(Sh(J, Ab))`.

## Main results

* `rightAcyclic_toSheaf_obj_of_injective`: the acyclicity statement just described.
* `rightDerivedFunctorPlus_sections_forget_iso` and
  `rightDerivedFunctorPlus_sections_forget_iso_unit`: Tag 01F1 part (1) for bounded below
  complexes, together with the equation pinning the comparison as the canonical one.

## Implementation notes

The acyclicity is obtained from [Stacks, Tag 05T8]
(`CategoryTheory.Functor.le_rightAcyclic`) applied to the class `ExtVanishing J U` of abelian
sheaves against which the corepresenting object of `Γ(U, -)` has no higher `Ext`.  The two
hypotheses of that criterion are:

* every abelian sheaf embeds in one of the class — an injective sheaf is in it; and
* the class is stable under the quotient of a short exact sequence whose first two terms are in
  it, and `Γ(U, -)` carries such a sequence to a short exact sequence.

Both come from the covariant long exact sequence for `Ext`
(`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`) once sections over `U` are identified
with `Hom` out of the corepresenting object, and that identification is
`ModuleSheafCohomology.evaluationRepresentation`.  That the underlying abelian sheaf of an
injective module sheaf lies in the class is
`ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf`, which is the torsion-free/extension-of-
scalars argument of Tag 03FD.

The bounded-below comparison is then [Stacks, Tag 015M]
(`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective`) applied twice: once to the pair
`(Γ(U, -) on modules, forget₂)`, whose acyclicity hypothesis is free because `forget₂` is exact,
and once to the pair `(toSheaf, Γ(U, -) on abelian sheaves)`, whose acyclicity hypothesis is the
theorem above.  The two canonical maps have the *same* source, because the two composites are
the same functor `Γ(U, -) ∘ toSheaf` by definitional unfolding (`evaluationCompForgetIso` of
`StacksDraft.Ch20.Sec12.Tag01F1Sections` records this), so the comparison is the composite of
one inverse with the other, and the unit equation is then formal.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModuleComparison

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Acyclicity of the underlying abelian sheaf of an injective module sheaf -/

section Site

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Sections over an object of the site are left exact: the functor is isomorphic to evaluation
of the underlying presheaf, which preserves finite limits. -/
instance siteSections_preservesFiniteLimits :
    PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{u}).symm

/-- Sections over an object of the site are additive. -/
instance siteSections_additive :
    ((sheafSections J AddCommGrpCat.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- The abelian sheaf corepresenting sections over `U`: the sheafification of the free abelian
presheaf on `yoneda.obj U`. -/
abbrev freeSectionsSheaf : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The abelian sheaves against which the corepresenting object of `Γ(U, -)` has no higher
`Ext`.  This is the class of objects adapted to `Γ(U, -)` in the sense of [Stacks, Tag 05T8]. -/
def ExtVanishing : ObjectProperty (Sheaf J AddCommGrpCat.{u}) :=
  fun F => ∀ (n : ℕ) (e : Ext.{u} (freeSectionsSheaf J U) F (n + 1)), e = 0

/-- Every abelian sheaf embeds into one with no higher `Ext` out of the corepresenting object:
an injective sheaf will do. -/
theorem exists_mono_extVanishing (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ (G : Sheaf J AddCommGrpCat.{u}) (_ : ExtVanishing J U G) (i : F ⟶ G), Mono i :=
  ⟨Injective.under F, fun _ e => Ext.eq_zero_of_injective e, Injective.ι F, inferInstance⟩

/-- Sections over `U` of a short exact sequence whose first term has no higher `Ext` out of the
corepresenting object form a short exact sequence: left exactness gives everything but
surjectivity, and surjectivity is the vanishing of `Ext¹` out of the corepresenting object. -/
theorem epi_sections_map_of_extVanishing (S : ShortComplex (Sheaf J AddCommGrpCat.{u}))
    (hS : S.ShortExact) (h₁ : ExtVanishing J U S.X₁) :
    Epi (((sheafSections J AddCommGrpCat.{u}).obj (op U)).map S.g) := by
  have hrep := ModuleSheafCohomology.evaluationRepresentation J U
  have hnat := hrep.hom.naturality S.g
  have hcoy : Epi ((preadditiveCoyoneda.obj (op (freeSectionsSheaf J U))).map S.g) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro h
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS (Ext.mk₀ h)
      (show 0 + 1 = 1 from rfl) (h₁ 0 _)
    obtain ⟨k, rfl⟩ := (Ext.mk₀_bijective (freeSectionsSheaf J U) S.X₂).2 x₂
    refine ⟨k, ?_⟩
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact (Ext.mk₀_bijective (freeSectionsSheaf J U) S.X₃).1 hx₂
  have heq : ((sheafSections J AddCommGrpCat.{u}).obj (op U)).map S.g =
      hrep.hom.app S.X₂ ≫
        (preadditiveCoyoneda.obj (op (freeSectionsSheaf J U))).map S.g ≫
        hrep.inv.app S.X₃ := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [heq]
  infer_instance

/-- The class `ExtVanishing J U` is adapted to sections over `U` in the sense of
[Stacks, Tag 05T8]: it is stable under the quotient of a short exact sequence whose first two
terms belong to it, and sections over `U` carry such a sequence to a short exact sequence. -/
theorem extVanishing_shortExact (S : ShortComplex (Sheaf J AddCommGrpCat.{u}))
    (hS : S.ShortExact) (h₁ : ExtVanishing J U S.X₁) (h₂ : ExtVanishing J U S.X₂) :
    ExtVanishing J U S.X₃ ∧
      (S.map ((sheafSections J AddCommGrpCat.{u}).obj (op U))).ShortExact := by
  refine ⟨fun n e => ?_, ?_⟩
  · obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS e
      (show n + 1 + 1 = n + 2 from rfl) (h₁ (n + 1) _)
    rw [← hx₂, h₂ n x₂, Ext.zero_comp]
  · have hlex := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      ((sheafSections J AddCommGrpCat.{u}).obj (op U))).mp inferInstance S hS
    exact
      { exact := hlex.1
        mono_f := hlex.2
        epi_g := epi_sections_map_of_extVanishing J U S hS h₁ }

/-- **The acyclicity input of Stacks 01F1 part (1).**  The underlying abelian sheaf of an
injective sheaf of `R`-modules is right acyclic for sections over an object `U` of the site:
the single complex on it computes the right derived functor of `Γ(U, -)` on `D⁺(Sh(J, Ab))`.

This is [Stacks, Tag 05T8] for the class of abelian sheaves with no higher `Ext` out of the
object corepresenting `Γ(U, -)`; membership of the underlying abelian sheaf of an injective
module sheaf in that class is the torsion-free argument of Tag 03FD. -/
theorem rightAcyclic_toSheaf_obj_of_injective (R : Sheaf J RingCat.{u})
    (I : SheafOfModules.{u} R) (hI : Injective I) :
    ((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightAcyclic
      ((SheafOfModules.toSheaf R).obj I) := by
  have := hI
  refine Functor.le_rightAcyclic _ (ExtVanishing J U) (exists_mono_extVanishing J U)
    (fun S hS h₁ h₂ => extVanishing_shortExact J U S hS h₁ h₂) _ ?_
  intro n e
  exact ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf J R I U n e

end Site

/-! ### Every object is right acyclic for an exact functor -/

section Exact

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- Every object of the source is right acyclic for an exact additive functor: the class of all
objects is adapted to it in the sense of [Stacks, Tag 05T8]. -/
@[sga "4½ Etat_0 4.2.3.2" "special case"]
theorem rightAcyclic_of_exact (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : A) : F.rightAcyclic M :=
  Functor.le_rightAcyclic F ⊤ (fun X => ⟨X, trivial, 𝟙 X, inferInstance⟩)
    (fun _ hS _ _ => ⟨trivial, hS.map_of_exact F⟩) M trivial

end Exact

/-! ### Stacks 01F1 part (1) for bounded below complexes -/

section Cohomology

variable (X : RingedSpace.{u, u})

/-- The unit from ordinary module-valued sections, with the underlying abelian group, to
the composite of the two bounded-below right derived functors. -/
def moduleSectionsDerivedUnit (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
          forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
            AddCommGrpCat.{u}))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).mapHomotopyCategoryPlus
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerivedFunctorPlusUnith
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).rightDerivedFunctorPlus

/-- The unit from ordinary sections after forgetting the coefficient sheaf to the
composite of the corresponding bounded-below right derived functors. -/
def abelianSectionsDerivedUnit (U : Opens X.carrier) :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙
      (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (op U)).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
          (op U)).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategoryPlus
      ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (op U)).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlusUnith
      ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (op U)).rightDerivedFunctorPlus

/-- The canonical map of [Stacks, Tag 015M] for module-valued sections over `U` followed by
forgetting the module structure. -/
def moduleSectionsComparison (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus ⟶
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) _
    (moduleSectionsDerivedUnit X U)

/-- The canonical map of [Stacks, Tag 015M] for forgetting the coefficient sheaf followed by
sections over `U`.  Its source is the same functor as that of `moduleSectionsComparison`. -/
def abelianSectionsComparison (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus ⟶
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
          (op U)).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) _
    (abelianSectionsDerivedUnit X U)

/-- The derived unit of sections over `U` followed by `moduleSectionsComparison` is
`moduleSectionsDerivedUnit`. -/
theorem moduleSectionsComparison_fac (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (moduleSectionsComparison X U) =
        moduleSectionsDerivedUnit X U :=
  Functor.rightDerived_fac _ _ _ _ _

/-- The derived unit of sections over `U` followed by `abelianSectionsComparison` is
`abelianSectionsDerivedUnit`. -/
theorem abelianSectionsComparison_fac (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (abelianSectionsComparison X U) =
        abelianSectionsDerivedUnit X U :=
  Functor.rightDerived_fac _ _ _ _ _

/-- The comparison map `moduleSectionsComparison` is an isomorphism. -/
instance isIso_moduleSectionsComparison (U : Opens X.carrier) :
    IsIso (moduleSectionsComparison X U) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective _ _ _
    (moduleSectionsComparison_fac X U)).2
    fun _I _ => rightAcyclic_of_exact _ _

/-- The comparison map `abelianSectionsComparison` is an isomorphism. -/
instance isIso_abelianSectionsComparison (U : Opens X.carrier) :
    IsIso (abelianSectionsComparison X U) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective
      (SheafOfModules.toSheaf (structureSheafRing X))
      ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U))
      (abelianSectionsComparison X U) (abelianSectionsComparison_fac X U)).2
    fun I hI => rightAcyclic_toSheaf_obj_of_injective _ U (structureSheafRing X) I hI

/-- The comparison between module and abelian-sheaf cohomology is valid for bounded below
complexes and is natural in the complex. -/
@[stacks 01F1 "bounded below complexes, part (1)", ega "0 12.2.1" "H^p(U,F) comparison"]
def rightDerivedFunctorPlus_sections_forget_iso (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus ≅
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
          (op U)).rightDerivedFunctorPlus :=
  (asIso (moduleSectionsComparison X U)).symm ≪≫ asIso (abelianSectionsComparison X U)

/-- The bounded-below sections comparison is the canonical one: it intertwines the two
units from ordinary sections. -/
@[stacks 01F1 "bounded below complexes, part (1), canonical comparison"]
lemma rightDerivedFunctorPlus_sections_forget_iso_unit (U : Opens X.carrier) :
    moduleSectionsDerivedUnit X U ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (rightDerivedFunctorPlus_sections_forget_iso X U).hom =
      abelianSectionsDerivedUnit X U := by
  rw [← moduleSectionsComparison_fac X U, ← abelianSectionsComparison_fac X U]
  dsimp only [rightDerivedFunctorPlus_sections_forget_iso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv]
  rw [Category.assoc, ← Functor.whiskerLeft_comp, IsIso.hom_inv_id_assoc]

end Cohomology

end Stacks.Cohomology.ModuleComparison

end
