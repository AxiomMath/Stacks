module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite diagrams of modules as colimits of their finitely generated subdiagrams

Every finite diagram of `A`-modules is the filtered colimit of the finite subdiagrams spanned by
finitely many chosen elements of each object, closed up under the arrows of the diagram. This
gives right exactness of a filtered-colimit-preserving functor from the right exactness of its
restriction to finite modules, with no relation between the universe of the ring and the
universe of the modules.

## Main results

* `ModuleCat.preservesFiniteColimits_of_finiteModuleRestriction`: a filtered-colimit-preserving
  functor between module categories whose restriction to finite modules preserves finite
  colimits preserves finite colimits.

## Implementation notes

The index category of the subdiagrams is the product over the objects of the diagram of the
finite subsets of each, ordered by inclusion; it is a filtered preorder, and the colimit
comparison map is an isomorphism on each subdiagram because each subdiagram takes values in
finite modules.

No Noetherian hypothesis on `A` is needed once the filtered-colimit-preserving functor is
given.

## References

* [Stacks Project, Tag 0GNL](https://stacks.math.columbia.edu/tag/0GNL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {A : Type u} [Ring A] {J : Type v} [SmallCategory J] [FinCategory J]
variable (D : J ⥤ ModuleCat.{v} A)

private abbrev GeneratorIndex := (j : J) → Finset (D.obj j)

@[instance_reducible]
private instance generatorIndexCategory : SmallCategory (GeneratorIndex D) :=
  Preorder.smallCategory _

/-- Close finitely many generators under all the arrows of a finite diagram. -/
private def generatedSubmodule (s : GeneratorIndex D) (j : J) : Submodule A (D.obj j) :=
  Submodule.span A (Set.range (fun p : Σ i, (i ⟶ j) × s i => D.map p.2.1 p.2.2))

private lemma generatedSubmodule_fg (s : GeneratorIndex D) (j : J) :
    (generatedSubmodule D s j).FG :=
  Submodule.fg_span (Set.finite_range _)

omit [FinCategory J] in
private lemma generatedSubmodule_mono {s t : GeneratorIndex D} (h : s ≤ t) (j : J) :
    generatedSubmodule D s j ≤ generatedSubmodule D t j := by
  apply Submodule.span_mono
  rintro _ ⟨⟨i, f, x⟩, rfl⟩
  exact ⟨⟨i, f, ⟨x, h i x.property⟩⟩, rfl⟩

omit [FinCategory J] in
private lemma generatedSubmodule_map (s : GeneratorIndex D) {i j : J} (f : i ⟶ j) :
    generatedSubmodule D s i ≤ (generatedSubmodule D s j).comap (D.map f).hom := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨k, g, x⟩, rfl⟩
  exact Submodule.subset_span ⟨⟨k, g ≫ f, x⟩, by simp⟩

private def generatedDiagram (s : GeneratorIndex D) : J ⥤ ModuleCat.{v} A where
  obj j := ModuleCat.of A (generatedSubmodule D s j)
  map f := ModuleCat.ofHom ((D.map f).hom.restrict (generatedSubmodule_map D s f))
  map_id j := by ext x; simp
  map_comp f g := by ext x; simp

private def finiteSubdiagrams : GeneratorIndex D ⥤ J ⥤ ModuleCat.{v} A where
  obj s := generatedDiagram D s
  map {s t} h :=
    { app j := ModuleCat.ofHom (Submodule.inclusion (generatedSubmodule_mono D (leOfHom h) j))
      naturality := by intros; ext x; rfl }

private def finiteSubdiagramsCocone : Cocone (finiteSubdiagrams D) where
  pt := D
  ι :=
    { app s :=
        { app j := ModuleCat.ofHom (generatedSubmodule D s j).subtype
          naturality := by intros; ext x; rfl } }

/-- Each object is the directed union of these finite subdiagrams. -/
private noncomputable def finiteSubdiagramsIsColimit :
    IsColimit (finiteSubdiagramsCocone D) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro j
  let G : GeneratorIndex D → Type v := fun s => generatedSubmodule D s j
  let f : (s t : GeneratorIndex D) → s ≤ t → G s →ₗ[A] G t :=
    fun s t h => Submodule.inclusion (generatedSubmodule_mono D h j)
  letI : DirectedSystem G (fun {s t} h => f s t h) :=
    { map_self := by intros; rfl
      map_map := by intros; rfl }
  let l : Module.DirectLimit G f →ₗ[A] D.obj j :=
    Module.DirectLimit.lift A _ G f (fun s => (generatedSubmodule D s j).subtype)
      (by intros; rfl)
  have hl : Function.Bijective l := by
    refine ⟨Module.DirectLimit.lift_injective _ _ fun _ => Subtype.val_injective, fun x => ?_⟩
    let s : GeneratorIndex D := Function.update (fun _ => ∅) j {x}
    have hx : x ∈ generatedSubmodule D s j :=
      Submodule.subset_span ⟨⟨j, 𝟙 j, ⟨x, by simp [s]⟩⟩, by simp⟩
    exact ⟨Module.DirectLimit.of A _ G f s ⟨x, hx⟩, Module.DirectLimit.lift_of ..⟩
  apply IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit (R := A) G f)
  refine Cocone.ext (LinearEquiv.ofBijective l hl).toModuleIso fun s =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change l (Module.DirectLimit.of A _ G f s x) = x.val
  exact Module.DirectLimit.lift_of ..

/-- A filtered-colimit-preserving functor whose restriction to finite modules preserves
finite colimits itself preserves finite colimits, with independent ring and module universes. -/
public theorem preservesFiniteColimits_of_finiteModuleRestriction
    (A : Type u) [Ring A] (B : Type w) [Ring B]
    (F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B)
    (E : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    [PreservesFilteredColimitsOfSize.{v, v} E]
    (e : forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E ≅
      F ⋙ forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B))
    [PreservesFiniteColimits F] : PreservesFiniteColimits E := by
  classical
  apply preservesFiniteColimits_of_preservesFiniteColimitsOfSize.{v}
  intro J _ _
  constructor
  intro D
  let ι := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  have : PreservesFiniteColimits
      (F ⋙ forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B)) :=
    comp_preservesFiniteColimits F _
  have : PreservesFiniteColimits (ι ⋙ E) := preservesFiniteColimits_of_natIso e.symm
  have hstage (s : GeneratorIndex D) : PreservesColimit (generatedDiagram D s) E := by
    let D' : J ⥤ FGModuleCat.{v} A := (ModuleCat.isFG A).lift (generatedDiagram D s)
      (fun j => Module.Finite.of_fg (generatedSubmodule_fg D s j))
    exact preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves ι (colimit.isColimit D'))
      (isColimitOfPreserves (ι ⋙ E) (colimit.isColimit D'))
  -- The colimit comparison is an isomorphism on each finite subdiagram. Both sides
  -- preserve filtered colimits, so it is also an isomorphism on their colimit.
  let L : (J ⥤ ModuleCat.{v} A) ⥤ ModuleCat.{v} B :=
    (Functor.whiskeringRight J (ModuleCat.{v} A) (ModuleCat.{v} B)).obj E ⋙ colim
  let L' : (J ⥤ ModuleCat.{v} A) ⥤ ModuleCat.{v} B := colim ⋙ E
  let α : L ⟶ L' :=
    { app K := colimit.post K E
      naturality := by intro K K' f; exact (colimit.map_post f E).symm }
  have : PreservesColimitsOfShape (GeneratorIndex D) E :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  have (s : GeneratorIndex D) : IsIso ((Functor.whiskerLeft (finiteSubdiagrams D) α).app s) := by
    have := hstage s
    exact inferInstanceAs (IsIso (colimit.post (generatedDiagram D s) E))
  have : IsIso (Functor.whiskerLeft (finiteSubdiagrams D) α) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (colimit.post D E) :=
    isIso_app_coconePt_of_preservesColimit (finiteSubdiagrams D) α
      (finiteSubdiagramsCocone D) (finiteSubdiagramsIsColimit D)
  exact preservesColimit_of_isIso_post E D

end ModuleCat
