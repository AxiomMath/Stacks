module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.CategoryTheory.Sites.Representable.LocalSurjectivityFromSiteMorphisms

/-!
# Products and equalizers of sheafified representables on the fppf site of a stack

Conditions (3) and (4) of **Stacks 0GN4** for the fppf site of a category fibred in groupoids over
the big fppf category of a scheme, read as conditions on the morphisms of that site.

The criterion of Stacks 0GN4 asks, for two objects `x`, `x'` of the site, for a finite family of
objects whose sheafified representables jointly surject onto `h_x^# ⨯ h_{x'}^#`, and for two
parallel morphisms `a, b : x ⟶ x'` for such a family surjecting onto the equalizer of `h_a^#` and
`h_b^#`. Surjectivity of sheaves of sets is a local condition on sections, and a section of a
sheaf over an object of the site is a morphism out of its sheafified representable, so both
conditions follow from conditions mentioning nothing but the hom-sets of the site:

* for (3), that every *pair* of morphisms `α : y ⟶ x`, `β : y ⟶ x'` factors, after passing to a
  covering of `y`, through one member of the family compatibly with `α` and with `β`;
* for (4), that every morphism `α : y ⟶ x` *equalizing `a` and `b`* factors, after passing to a
  covering of `y`, through one member of the family.

That reduction is
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering` and
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_equalizerLift_of_exists_covering`; this file
records it at the fppf site of Stacks 06TP, in the exact shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes.

## Main results

* `AlgebraicGeometry.Stack.isLocallySurjective_prodLift_fppfTopology_of_exists_covering`:
  condition (3) of Stacks 0GN4 for the fppf site, from a condition on pairs of morphisms.
* `AlgebraicGeometry.Stack.isLocallySurjective_equalizerLift_fppfTopology_of_exists_covering`:
  condition (4) of Stacks 0GN4 for the fppf site, from a condition on morphisms.

## What remains

Neither statement has any geometric content: the geometry is exactly the production of the finite
family. For an algebraic stack the source produces it from the 2-fibre product
`U ×_{x, 𝒳, x'} U'`, which is a quasi-compact algebraic stack by Stacks 075S part (3)
(`AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`) and hence
has an affine smooth presentation by Stacks 04YC
(`AlgebraicGeometry.Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation`). What is missing is
the dictionary between the morphisms of the site this file quantifies over and the objects of that
2-fibre product: a pair of morphisms `α : y ⟶ x`, `β : y ⟶ x'` is the same thing as an object of
`U ×_{x, 𝒳, x'} U'` over the scheme `y` lies over, and no form of that correspondence is available.
For condition (4) the family is cut out by the locus where an automorphism of an object of the site
is trivial, which needs the algebraic space
`AlgebraicGeometry.Stack.isomSpace` of Stacks 04YP in addition.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₀ u₀

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Condition (3) of Stacks 0GN4 for the fppf site, from a condition on pairs of morphisms of
the site.** Let `V_i` be a finite family of objects of the fppf site of `𝒳` with morphisms
`p_i : V_i ⟶ x` and `q_i : V_i ⟶ x'`, and suppose every pair of morphisms `α : y ⟶ x`,
`β : y ⟶ x'` of the site factors, after passing to a covering of `y`, through some `(p_i, q_i)`.
Then `∐_i h_{V_i}^# ⟶ h_x^# ⨯ h_{x'}^#` is a surjection of fppf sheaves of sets.

This is `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering` at the
fppf topology of Stacks 06TP; the universe of the sheaves of sets is the join `u + 1` of the two
universes of that site, as it is throughout the proof of Stacks 0GQV. -/
theorem isLocallySurjective_prodLift_fppfTopology_of_exists_covering
    {x x' : 𝒳.val.obj} {m : ℕ} (V : Fin m → 𝒳.val.obj)
    (p : ∀ i, V i ⟶ x) (q : ∀ i, V i ⟶ x')
    (h : ∀ (y : 𝒳.val.obj) (α : y ⟶ x) (β : y ⟶ x'),
      ∃ T ∈ fppfTopology B S hS 𝒳 y, ∀ ⦃z : 𝒳.val.obj⦄ (g : z ⟶ y), T.arrows g →
        ∃ (i : Fin m) (r : z ⟶ V i), r ≫ p i = g ≫ α ∧ r ≫ q i = g ≫ β) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
      prod.lift ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (p i))
        ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (q i))) :=
  Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering V p q h

/-- **Condition (4) of Stacks 0GN4 for the fppf site, from a condition on morphisms of the site.**
Let `a, b : x ⟶ x'` be two morphisms of the fppf site of `𝒳` and let `V_i` be a finite family of
objects with morphisms `p_i : V_i ⟶ x` equalizing `a` and `b`, and suppose every morphism
`α : y ⟶ x` with `α ≫ a = α ≫ b` factors, after passing to a covering of `y`, through some `p_i`.
Then `∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` is a surjection of fppf sheaves of sets.

This is `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_equalizerLift_of_exists_covering` at
the fppf topology of Stacks 06TP. The hypothesis is about morphisms of the site satisfying the
*strict* equation `α ≫ a = α ≫ b`, not merely a local one: the sheafification map
`h_x ⟶ h_x^#` is locally injective, so a section of the equalizer is, locally, a morphism of the
site that equalizes `a` and `b` on the nose. -/
theorem isLocallySurjective_equalizerLift_fppfTopology_of_exists_covering
    {x x' : 𝒳.val.obj} (a b : x ⟶ x') {m : ℕ} (V : Fin m → 𝒳.val.obj)
    (p : ∀ i, V i ⟶ x) (hp : ∀ i, p i ≫ a = p i ≫ b)
    (h : ∀ (y : 𝒳.val.obj) (α : y ⟶ x), α ≫ a = α ≫ b →
      ∃ T ∈ fppfTopology B S hS 𝒳 y, ∀ ⦃z : 𝒳.val.obj⦄ (g : z ⟶ y), T.arrows g →
        ∃ (i : Fin m) (r : z ⟶ V i), r ≫ p i = g ≫ α) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
      equalizer.lift
        (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map a)
        (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map b)
        ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (p i)) (by
          simpa only [Functor.map_comp] using
            congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (hp i))) :=
  Sheaf.isLocallySurjective_sigmaDesc_equalizerLift_of_exists_covering a b V p hp h

end AlgebraicGeometry.Stack

end
