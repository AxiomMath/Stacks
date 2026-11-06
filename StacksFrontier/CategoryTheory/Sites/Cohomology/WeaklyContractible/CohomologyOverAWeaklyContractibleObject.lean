module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.LocalImageSheaf

/-!
# Cohomology over a weakly contractible object

Let `(C, J)` be a site and `U` a weakly contractible object of it: every covering sieve of `U`
admits a section, equivalently every locally surjective morphism of sheaves of sets is
surjective on sections over `U`. Then

1. evaluation at `U` is an exact functor `Ab(C) ⥤ Ab`,
2. `Hᵖ(U, F) = 0` for every abelian sheaf `F` and every `p ≥ 1`, and
3. every torsor under a sheaf of groups has a section over `U`.

## Main results

* `Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible`: evaluation of abelian
  sheaves at `U` is exact.
* `Stacks.WeaklyContractible.subsingleton_cohomology_of_isWeaklyContractible`: the
  positive-degree cohomology of an abelian sheaf over `U` vanishes.
* `Stacks.WeaklyContractible.nonempty_sections_of_isWeaklyContractible_of_isTorsor`: every torsor
  has a section over `U`.

## References

* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

universe w' w v u

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private theorem torsor_small_sections
    (G : SheafOfGroups.{v, v, u} (C := C) J)
    (F : PseudoTorsor.{w, v, u} (C := C) G) :
    FunctorToTypes.Small.{v} F.presheaf := by
  intro X
  by_cases h : Nonempty (F.presheaf.obj X)
  · exact small_of_surjective (f := fun g : G.presheaf.obj X => F.act X g (Classical.choice h))
      fun t => (F.simplyTransitive X h _ t).exists
  · have := not_nonempty_iff.mp h
    infer_instance

private theorem torsor_shrink_isSheaf
    (G : SheafOfGroups.{v, v, u} (C := C) J)
    (F : PseudoTorsor.{w, v, u} (C := C) G)
    (hsmall : FunctorToTypes.Small.{v} F.presheaf) :
    Presheaf.IsSheaf J (FunctorToTypes.shrink.{v} F.presheaf) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact (Presieve.isSheaf_iff_of_nat_equiv
    (P₁ := F.presheaf) (P₂ := FunctorToTypes.shrink.{v} F.presheaf)
    (fun _ => equivShrink.{v} _) (by intros; simp [FunctorToTypes.shrink_map])).mp
    ((isSheaf_iff_isSheaf_of_type J F.presheaf).mp F.isSheaf)

private noncomputable def freeRepresentableSheaf
    [HasSheafify J AddCommGrpCat.{v}] (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

private noncomputable def freeRepresentableSectionEquiv
    [HasSheafify J AddCommGrpCat.{v}] (U : C)
    (Y : Sheaf J AddCommGrpCat.{v}) :
    (freeRepresentableSheaf J U ⟶ Y) ≃ Y.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ Y).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ Y.obj).trans yonedaEquiv)

private theorem freeRepresentableSectionEquiv_comp
    [HasSheafify J AddCommGrpCat.{v}] (U : C)
    {X Y : Sheaf J AddCommGrpCat.{v}}
    (a : freeRepresentableSheaf J U ⟶ X) (f : X ⟶ Y) :
    freeRepresentableSectionEquiv J U Y (a ≫ f) =
      f.hom.app (op U) (freeRepresentableSectionEquiv J U X a) :=
  rfl

private theorem freeRepresentableSheaf_projective
    [HasSheafify J AddCommGrpCat.{v}] (U : C)
    (he : ((sheafSections J AddCommGrpCat.{v}).obj (op U)).PreservesEpimorphisms) :
    Projective (freeRepresentableSheaf J U) := by
  constructor
  intro X Y f e _
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective (e.hom.app (op U))).mp
    (inferInstanceAs (Epi (((sheafSections J AddCommGrpCat.{v}).obj (op U)).map e)))
    (freeRepresentableSectionEquiv J U Y f)
  refine ⟨(freeRepresentableSectionEquiv J U X).symm s,
    (freeRepresentableSectionEquiv J U Y).injective ?_⟩
  rw [freeRepresentableSectionEquiv_comp, Equiv.apply_symm_apply, hs]

/-- Evaluation of abelian sheaves at a weakly contractible object is exact, with weak
contractibility tested in the value universe `w`. -/
@[stacks 0946 "part (1)"]
theorem exact_sheafSections_of_isWeaklyContractible
    [HasSheafify J AddCommGrpCat.{w}]
    (U : C)
    (hU : ∀ (F G : Sheaf J (Type w)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) AddCommGrpCat.{w}
      ((sheafSections J AddCommGrpCat.{w}).obj (op U)) := by
  let E := (sheafSections J AddCommGrpCat.{w}).obj (op U)
  have hLim : PreservesFiniteLimits E :=
    preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{w} (X := U)).symm
  have : HasFiniteLimits (Sheaf J AddCommGrpCat.{w}) := inferInstance
  have : HasBinaryProducts (Sheaf J AddCommGrpCat.{w}) := inferInstance
  have : PreservesLimitsOfShape (Discrete WalkingPair) E := inferInstance
  have : E.Additive := E.additive_of_preserves_binary_products
  have : E.PreservesEpimorphisms := by
    constructor
    intro X Y f _
    let S := sheafCompose J (forget AddCommGrpCat.{w})
    have : Presheaf.IsLocallySurjective J f.hom := Stacks.Sites.LocalImage.epi_localSurjective J f
    have hlocS : Sheaf.IsLocallySurjective (S.map f) := by
      show Presheaf.IsLocallySurjective J (whiskerRight f.hom (forget AddCommGrpCat.{w}))
      infer_instance
    show Epi (f.hom.app (op U))
    exact (AddCommGrpCat.epi_iff_surjective _).2 (hU (S.obj X) (S.obj Y) (S.map f) hlocS)
  have : E.PreservesHomology := E.preservesHomology_of_preservesEpis_and_kernels
  exact ⟨hLim, E.preservesFiniteColimits_of_preservesHomology⟩

/-- The positive-degree cohomology of an abelian sheaf over a weakly contractible object
vanishes. -/
@[stacks 0946 "part (2)"]
theorem subsingleton_cohomology_of_isWeaklyContractible
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (U : C) (hU : J.IsWeaklyContractible U)
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H'.{w', v} F p U) := by
  have : PreservesFiniteColimits ((sheafSections J AddCommGrpCat.{v}).obj (op U)) :=
    (exact_sheafSections_of_isWeaklyContractible.{v} J U hU).2
  have := freeRepresentableSheaf_projective J U inferInstance
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : p ≠ 0)
  exact Abelian.Ext.subsingleton_of_projective (freeRepresentableSheaf J U) F n

/-- Every torsor has a section over a weakly contractible object. -/
@[stacks 0946 "part (3)"]
theorem nonempty_sections_of_isWeaklyContractible_of_isTorsor
    (U : C) (hU : J.IsWeaklyContractible U)
    (G : SheafOfGroups.{v, v, u} (C := C) J)
    (F : PseudoTorsor (C := C) G) (hF : F.IsTorsor) :
    Nonempty (F.presheaf.obj (op U)) := by
  let := torsor_small_sections J G F
  let SF : Sheaf J (Type v) := ⟨FunctorToTypes.shrink.{v} F.presheaf,
    torsor_shrink_isSheaf J G F (torsor_small_sections J G F)⟩
  let T : Sheaf J (Type v) := Sheaf.terminal J Types.isTerminalPUnit
  let φ : SF ⟶ T := (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from SF
  have hφ : Sheaf.IsLocallySurjective φ := by
    constructor
    intro V s
    obtain ⟨S, hS, hsec⟩ := hF V
    refine J.superset_covering (fun W f hf => ?_) hS
    obtain ⟨x⟩ := hsec hf
    refine ⟨equivShrink.{v} _ x, ?_⟩
    dsimp [T, Sheaf.terminal] at s ⊢
  obtain ⟨x, -⟩ := hU SF T φ hφ PUnit.unit
  exact ⟨(equivShrink.{v} _).symm x⟩

end Stacks.WeaklyContractible

end
