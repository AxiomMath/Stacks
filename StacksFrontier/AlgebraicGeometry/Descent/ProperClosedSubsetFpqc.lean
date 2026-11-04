module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset

/-!
# Descent of properness of a closed subset along an fpqc covering

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type and let `Z` be a closed subset
of `X`. If the inverse image of `Z` is proper over every member of an fpqc covering of `Y`, then
`Z` is proper over `Y`.

## Main results

* `AlgebraicGeometry.isProperOver_of_fpqc`: properness over the base of a closed subset descends
  along an fpqc covering of the base.

## Implementation notes

An fpqc covering of `Y` is represented by membership of the presieve of its family in
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, and the inverse image of `Z` on a base change is the
preimage of `Z` under the projection to `X`.

The proof reduces the statement about the closed subset to one about a morphism of schemes:
the reduced induced subscheme of the preimage of `Z` is a closed subscheme structure on that
preimage, so by Tag 0CYL it is proper over the base change exactly when the pullback of the
reduced subscheme of `Z` is, and properness of morphisms is fpqc local on the target (Tag 02L1).
The three isomorphism steps at the end identify the pullback of `(vanishingIdeal Z).subschemeι ≫ f`
along a member of the covering with the pullback of `(vanishingIdeal Z).subschemeι` along the
projection, which is the morphism whose properness has just been established.

## References

* [Stacks Project, Tag 0F4J](https://stacks.math.columbia.edu/tag/0F4J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0F4J.** Properness over a base of a closed subset descends along an fpqc covering
of the base. -/
@[stacks 0F4J]
public theorem isProperOver_of_fpqc {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (Z : Closeds X)
    (h : ∃ (ι : Type v) (Y' : ι → Scheme.{u}) (g : ∀ i, Y' i ⟶ Y),
      Presieve.ofArrows Y' g ∈ Scheme.fpqcPrecoverage Y ∧
        ∀ i, IsProperOver (pullback.snd f (g i))
          (Z.preimage (pullback.fst f (g i)).continuous)) :
    IsProperOver f Z := by
  obtain ⟨ι, Y', g, hg, hY'⟩ := h
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hg
  rintro U g' _ ⟨i⟩
  let p := pullback.fst f (g i)
  let q := pullback.snd f (g i)
  let W := Z.preimage p.continuous
  let I' := I.comap p
  have hsupport : I'.support = W :=
    Closeds.ext (by simp [I', I, W, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal])
  have hI' : IsProper (I'.subschemeι ≫ q) :=
    (exists_isProper_iff_forall_isProper q W).mp
      ⟨_, Closeds.ext (by
        simp [W, p, Scheme.IdealSheafData.coe_support_vanishingIdeal]), hY' i⟩ I' hsupport
  have hP₁ : IsProper (pullback.fst p I.subschemeι ≫ q) := by
    rw [← Scheme.IdealSheafData.comapIso_inv_subschemeι I p, Category.assoc]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hI'
  have hP₂ : IsProper (pullback.snd I.subschemeι p ≫ q) := by
    simpa using MorphismProperty.comp_mem @IsProper (pullbackSymmetry p I.subschemeι).inv _
      inferInstance hP₁
  simpa [← pullbackRightPullbackFstIso_hom_snd, p, q] using MorphismProperty.comp_mem @IsProper
    (pullbackRightPullbackFstIso f (g i) I.subschemeι).inv _ inferInstance hP₂

end AlgebraicGeometry

end

