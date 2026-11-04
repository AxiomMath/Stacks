module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma

/-!
# How the standard ph refinement consumes Chow's lemma

Stacks 0DBF part (2) refines the composite of two successive standard ph coverings of an affine
scheme `T` by a single standard ph covering. Its proof applies Chow's lemma (Stacks 0202) to the
proper surjective morphism `W ⟶ Uⱼ` presenting the inner covering over an affine member `Uⱼ` of
the outer one, and then compactifies: the scheme-theoretic closure of `W` inside `ℙⁿ_U` is proper
over the whole source `U` of the outer covering's proper surjection.

Two steps of that argument are silent in the Stacks text and are carried out here, so that the
only thing still owed is Chow's lemma itself.

* The conclusion of Chow's lemma is an **immersion** into `ℙⁿ_{Uⱼ}`, while the compactification
  step needs a **closed** immersion. The upgrade is automatic: the modification `W' ⟶ Uⱼ` is
  proper and `ℙⁿ_{Uⱼ} ⟶ Uⱼ` is separated, so the immersion is proper, hence closed.
* `ℙⁿ_{Uⱼ}` has to be viewed as the part of `ℙⁿ_U` lying over `Uⱼ`. Base change along the open
  immersion `Uⱼ ⟶ U` provides that identification.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.baseChangeMap` is the morphism `ℙⁿ_S ⟶ ℙⁿ_T` induced by a
  morphism `S ⟶ T` of base schemes.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper`: a proper immersion is a
  closed immersion.
* `AlgebraicGeometry.ProjectiveSpace.isOpenImmersion_baseChangeMap` and
  `AlgebraicGeometry.ProjectiveSpace.range_baseChangeMap`: over an open subscheme of the base,
  projective space is the part of projective space over the ambient base lying over it.
* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_hasChowModification`: the form
  of Chow's lemma that Stacks 0DBF part (2) actually consumes, derived from the conclusion of
  Chow's lemma as stated by `AlgebraicGeometry.HasChowModification`.

## Implementation notes

Nothing here proves Chow's lemma. The point of the last result is that its hypothesis is
literally `HasChowModification`, so when Chow's lemma lands the wiring into Stacks 0DBF part (2)
is a single application with no side conditions: all of `IsSeparated`, `LocallyOfFiniteType`,
`QuasiCompact`, `CompactSpace` and `QuasiSeparatedSpace` that Stacks 0202 asks for are supplied
by instance search from `IsProper (W ⟶ Uⱼ)` and `IsAffine Uⱼ`.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- A proper immersion is a closed immersion: its range is closed because a proper morphism is
universally closed, and an immersion is a preimmersion. -/
theorem isClosedImmersion_of_isImmersion_of_isProper {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsImmersion i] [IsProper i] : IsClosedImmersion i :=
  IsClosedImmersion.of_isPreimmersion i <| by
    simpa only [Set.image_univ] using i.isClosedMap _ isClosed_univ

namespace ProjectiveSpace

variable (n : ℕ)

/-- The morphism `ℙⁿ_S ⟶ ℙⁿ_T` induced by a morphism `g : S ⟶ T` of base schemes: the first
projection of `ℙⁿ_T ×_T S`, read through the identification of that fibre product with
`ℙⁿ_S`. -/
noncomputable def baseChangeMap {S T : Scheme.{u}} (g : S ⟶ T) :
    ProjectiveSpace n S ⟶ ProjectiveSpace n T :=
  (baseChangeIso n g).inv ≫ pullback.fst (ProjectiveSpace n T ↘ T) g

/-- The induced morphism of projective spaces lies over the morphism of base schemes. -/
theorem baseChangeMap_over {S T : Scheme.{u}} (g : S ⟶ T) :
    baseChangeMap n g ≫ (ProjectiveSpace n T ↘ T) = (ProjectiveSpace n S ↘ S) ≫ g := by
  rw [baseChangeMap, Category.assoc, pullback.condition, ← baseChangeIso_hom_over n g,
    ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Over an open subscheme of the base, projective space includes as an open subscheme of
projective space over the ambient base. -/
instance isOpenImmersion_baseChangeMap {S T : Scheme.{u}} (g : S ⟶ T) [IsOpenImmersion g] :
    IsOpenImmersion (baseChangeMap n g) := by
  rw [baseChangeMap]
  infer_instance

/-- The part of `ℙⁿ_T` lying over the range of `g : S ⟶ T` is the range of the induced morphism
`ℙⁿ_S ⟶ ℙⁿ_T`. -/
theorem range_baseChangeMap {S T : Scheme.{u}} (g : S ⟶ T) :
    Set.range (baseChangeMap n g) = (ProjectiveSpace n T ↘ T) ⁻¹' Set.range g := by
  rw [baseChangeMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso (baseChangeIso n g).inv.base).2.range_eq,
    Set.image_univ, Scheme.Pullback.range_fst]

end ProjectiveSpace

/-- **The form of Chow's lemma that Stacks 0DBF part (2) consumes.** Let `g : W ⟶ Uⱼ` be proper
and suppose Chow's lemma holds for it. Then there are a proper surjective modification
`p : W' ⟶ W` and a *closed* immersion `i : W' ⟶ ℙⁿ_{Uⱼ}` over `Uⱼ`.

Chow's lemma (`AlgebraicGeometry.HasChowModification`, Stacks 0202) only provides an immersion.
Properness of `g` upgrades it: `W' ⟶ Uⱼ` is then proper and `ℙⁿ_{Uⱼ} ⟶ Uⱼ` is separated, so `i`
is proper, hence closed. The compactification step of Stacks 0DBF part (2) needs the closed
form, because it identifies `W'` with the part over `Uⱼ` of the scheme-theoretic closure of `W'`
in `ℙⁿ_U`, and the scheme-theoretic image of a closed immersion is its own target subscheme. -/
theorem exists_isClosedImmersion_projectiveSpace_of_hasChowModification {W Uj : Scheme.{u}}
    (g : W ⟶ Uj) [IsProper g] (h : HasChowModification g) :
    ∃ (n : ℕ) (W' : Scheme.{u}) (p : W' ⟶ W) (i : W' ⟶ ProjectiveSpace n Uj),
      IsProper p ∧ Surjective p ∧ IsClosedImmersion i ∧
        p ≫ g = i ≫ (ProjectiveSpace n Uj ↘ Uj) := by
  obtain ⟨n, W', p, i, hp, hps, hi, hcomm⟩ := h
  refine ⟨n, W', p, i, hp, hps, ?_, hcomm⟩
  have : IsProper p := hp
  have : IsImmersion i := hi
  have hprop : IsProper (i ≫ (ProjectiveSpace n Uj ↘ Uj)) := by rw [← hcomm]; infer_instance
  have : IsProper i := IsProper.of_comp i (ProjectiveSpace n Uj ↘ Uj)
  exact isClosedImmersion_of_isImmersion_of_isProper i

end AlgebraicGeometry

end
