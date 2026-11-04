module

public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Local injectivity of sheafification in a coefficient universe unrelated to the site

Let `(C, J)` be a site. The unit `P ⟶ P^#` of sheafification of a presheaf of sets is locally
injective: two sections with the same image agree on a covering sieve. Mathlib knows this for
sections in the universe `max u v` fixed by the site, which is not the situation of the big sites
and of the small étale site, where the coefficient universe is unrelated to the universe of the
objects. The two instances are reproved here under `UnivLE`, which is all the plus construction
needs.

This is the local-injectivity companion of
`Stacks.Sheafification.isLocallySurjective_toSheafify_type`, whose hypothesis-free proof through
the subpresheaf of locally-reached sections has no analogue for injectivity; the argument here is
Mathlib's, run at a weaker universe hypothesis.

## Main results

* `Stacks.Sheafification.isLocallyInjective_toPlus_type` — the unit of the plus construction is
  locally injective.
* `Stacks.Sheafification.isLocallyInjective_toSheafify_type` — the sheafification map is locally
  injective.

## References

* [Stacks Project, Tag 00WK](https://stacks.math.columbia.edu/tag/00WK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology.Plus

universe v w z

namespace Stacks.Sheafification

/-- **The unit of the plus construction is locally injective**, with no relation assumed between
the coefficient universe and the site: two sections with the same image agree on a covering sieve.

This is `CategoryTheory.Presheaf.isLocallyInjective_toPlus` with the universe hypothesis relaxed
to `UnivLE`. -/
public theorem isLocallyInjective_toPlus_type
    {C : Type z} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max z w, v}] (P : Cᵒᵖ ⥤ Type v) :
    Presheaf.IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {_} x y h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, _, _, eq⟩ := h
    exact J.superset_covering
      (fun Y f hf ↦ congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

/-- **The sheafification map of a presheaf of sets is locally injective**, with no relation
assumed between the coefficient universe and the site.

Sheafification is the twofold plus construction composed with
`CategoryTheory.plusPlusIsoSheafify`, which is an isomorphism. -/
public instance isLocallyInjective_toSheafify_type
    {C : Type z} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max z w, v}] (P : Cᵒᵖ ⥤ Type v) :
    Presheaf.IsLocallyInjective J (toSheafify J P) := by
  have h1 : Presheaf.IsLocallyInjective J (J.toSheafify P) := by
    dsimp [GrothendieckTopology.toSheafify]
    rw [GrothendieckTopology.plusMap_toPlus]
    let := isLocallyInjective_toPlus_type J P
    let := isLocallyInjective_toPlus_type J (J.plusObj P)
    exact Presheaf.isLocallyInjective_comp J (J.toPlus P) (J.toPlus (J.plusObj P))
  rw [← toSheafify_plusPlusIsoSheafify_hom J (Type v) P]
  infer_instance

end Stacks.Sheafification

end
