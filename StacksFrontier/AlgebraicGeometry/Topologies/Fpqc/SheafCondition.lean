module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The fpqc sheaf condition on a big fppf site

An algebraic space over a scheme `S` is by definition a sheaf for the fppf topology of the big fppf
category over `S`. The fpqc topology on that category is the one pulled back along the canonical
functor to schemes from `AlgebraicGeometry.Scheme.fpqcPrecoverage`; it is strictly finer than the
fppf topology. An algebraic space is separated for every fpqc covering: two sections which agree on
an fpqc covering family agree.

## Main results

* `AlgebraicGeometry.isSheaf_fpqc_of_isSheafFor`: the fpqc sheaf condition on the big fppf category
  over `S` follows from the sheaf condition for the covering presieves themselves.
* `AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`: an algebraic space is separated for
  every fpqc covering presieve of the big fppf category over `S`.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_exists_isAmalgamation`: an algebraic space
  satisfies the fpqc sheaf condition as soon as every compatible family on an fpqc covering
  presieve has an amalgamation.

## References

* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A presheaf on the big fppf category over `S` is a sheaf for the fpqc topology as soon as
it satisfies the sheaf condition for every fpqc covering presieve. -/
theorem isSheaf_fpqc_of_isSheafFor {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ∀ ⦃X : BigFppfOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X →
      Presieve.IsSheafFor F R) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  exact h

namespace IsAlgebraicSpace

/-- Two sections of an algebraic space over an object of the big fppf category over `S` which agree
on the members of an fpqc covering presieve of that object are equal. -/
theorem isSeparatedFor_fpqc {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {X : BigFppfOver B S hS} {R : Presieve X}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X) :
    Presieve.IsSeparatedFor F R := by
  intro x t₁ t₂ h₁ h₂
  set a : yoneda.obj X ⟶ F := yonedaEquiv.symm t₁ with ha
  set b : yoneda.obj X ⟶ F := yonedaEquiv.symm t₂ with hb
  have key : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ X), R f →
      yoneda.map f ≫ a = yoneda.map f ≫ b := by
    intro Z f hf
    rw [ha, hb, yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left,
      h₁ f hf, h₂ f hf]
  have hrep : yoneda.relativelyRepresentable (diag F) := hF.diagonal_representable
  set E := hrep.pullback (prod.lift a b) with hE
  set p : E ⟶ X := hrep.snd (prod.lift a b) with hp
  have hpb := hrep.isPullback (prod.lift a b)
  have : IsSplitMono (diag F) := IsSplitMono.mk' ⟨prod.fst, by simp⟩
  have : Mono (yoneda.map p) := hpb.mono_snd_of_mono
  have hmono : Mono p := yoneda.mono_of_mono_map this
  have hfac : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ X), R f → ∃ l : Z ⟶ E, l ≫ p = f := by
    intro Z f hf
    refine ⟨hrep.lift (yoneda.map f ≫ a) f ?_, hrep.lift_snd _ _ _⟩
    apply prod.hom_ext <;> simp [key f hf]
  have hbc : ∀ ⦃Z : BigFppfOver B S hS⦄ (v : Z ⟶ X), R v →
      MorphismProperty.isomorphisms Scheme.{u}
        (pullback.snd ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map v)) := by
    intro Z v hv
    obtain ⟨l, hl⟩ := hfac v hv
    have : Mono (pullback.snd p v) := (IsPullback.of_hasPullback p v).mono_snd_of_mono
    have hsec : pullback.lift l (𝟙 Z) (by simp [hl]) ≫ pullback.snd p v = 𝟙 Z :=
      pullback.lift_snd _ _ _
    have : IsSplitEpi (pullback.snd p v) := IsSplitEpi.mk' ⟨_, hsec⟩
    have : IsIso (pullback.snd p v) := isIso_of_mono_of_isSplitEpi _
    have hcomp : IsIso (pullbackComparison (BigFppfOver.toScheme B S hS) p v ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map v)) := by
      rw [pullbackComparison_comp_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (pullbackComparison (BigFppfOver.toScheme B S hS) p v) _
  have hiso : MorphismProperty.isomorphisms Scheme.{u}
      ((BigFppfOver.toScheme B S hS).map p) := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Scheme.fpqcPrecoverage) hR ?_
    intro U g _ hg
    obtain ⟨hv⟩ := hg
    exact hbc _ hv
  have : IsIso ((BigFppfOver.toScheme B S hS).map p) := hiso
  have : IsIso (B.inclusion.map ((BigFppfOver.forget B S hS).map p)) := this
  have : IsIso ((BigFppfOver.forget B S hS).map p) := isIso_of_reflects_iso _ B.inclusion
  have : IsIso p := isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have : IsIso (yoneda.map p) := inferInstance
  have hab : prod.lift a b = (inv (yoneda.map p) ≫ hrep.fst (prod.lift a b)) ≫ diag F := by
    rw [Category.assoc, hpb.w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hfst := congrArg (fun φ ↦ φ ≫ (prod.fst : F ⨯ F ⟶ F)) hab
  have hsnd := congrArg (fun φ ↦ φ ≫ (prod.snd : F ⨯ F ⟶ F)) hab
  simp only [prod.lift_fst, prod.lift_snd, Category.assoc, diag] at hfst hsnd
  exact yonedaEquiv.symm.injective (hfst.trans hsnd.symm)

/-- An algebraic space is a sheaf for the fpqc topology of the big fppf category over `S` as soon
as every compatible family of sections on an fpqc covering presieve has an amalgamation. -/
theorem isSheaf_fpqc_of_exists_isAmalgamation {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ ⦃X : BigFppfOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X →
      ∀ x : Presieve.FamilyOfElements F R, x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine isSheaf_fpqc_of_isSheafFor ?_
  intro X R hR
  exact (hF.isSeparatedFor_fpqc hR).isSheafFor (h R hR)

end IsAlgebraicSpace

end AlgebraicGeometry

end
