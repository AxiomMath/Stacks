module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionRelation

/-!
# Restricting a groupoid whose arrows are an equivalence relation

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose associated pre-relation `j = (t, s)`
is an equivalence relation, and let `g : U' ⟶ U` be any morphism of schemes over `S`. Then the
restriction of the groupoid along `g` again has `(t, s)` an equivalence relation.

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_iff_mono_prodLift`: a pair of parallel morphisms of
  schemes over `S` is an internal equivalence relation exactly when the morphism it induces to
  the product is a monomorphism and a pre-equivalence relation.
* `AlgebraicGeometry.mono_prodLift_restrictionTarget_restrictionSource`: the target and source
  maps of the canonical arrow scheme of a restriction are jointly monic.
* `AlgebraicGeometry.mono_groupoidPreRelation_restriction`: the same for any groupoid scheme
  realizing the restriction, in particular for `AlgebraicGeometry.GroupoidScheme.restrict`.
* `AlgebraicGeometry.restriction_isEquivalenceRelation`: the target and source maps of any
  groupoid scheme realizing the restriction are an equivalence relation.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
* [Stacks Project, Tag 02V8](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 02VD](https://stacks.math.columbia.edu/tag/02VD)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-! ### The pre-relation criterion, read off a pair of parallel maps -/

/-- A pair of parallel morphisms of schemes over `S` is an internal equivalence relation
exactly when the morphism to the product that it induces is a monomorphism and a
pre-equivalence relation. This is
`Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` stated for the
two maps instead of for the morphism to the product. -/
theorem isEquivalenceRelation_iff_mono_prodLift {R U : Over S} (t s : R ⟶ U) :
    IsEquivalenceRelation t s ↔
      (Mono (prod.lift t s) ∧ IsPreEquivalenceRelation (prod.lift t s)) := by
  have h := Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (prod.lift t s : PreRelation R U)
  rwa [show PreRelation.target (prod.lift t s : PreRelation R U) = t from prod.lift_fst t s,
    show PreRelation.source (prod.lift t s : PreRelation R U) = s from prod.lift_snd t s] at h

/-! ### Joint monicity of the restricted target and source -/

variable (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)

/-- **The target and source of a restriction are jointly monic.** If the target and source maps
of `G` are an internal equivalence relation, then the target and source maps of the canonical
arrow scheme of the restriction of `G` along `g` are jointly monic, for any `g`. -/
theorem mono_prodLift_restrictionTarget_restrictionSource
    [IsEquivalenceRelation G.target G.source] :
    Mono (prod.lift (restrictionTarget G g) (restrictionSource G g)) := by
  have _ : Mono (groupoidPreRelation G) :=
    ((isEquivalenceRelation_iff_mono_prodLift G.target G.source).1 inferInstance).1
  have _ : Mono (PreRelation.restrict (groupoidPreRelation G) g) :=
    inferInstanceAs (Mono (pullback.fst (prod.map g g) (groupoidPreRelation G)))
  rw [← restrictionIso_relation G g]
  infer_instance

/-- If the target and source maps of `G` are an internal equivalence relation, then the
pre-relation of any groupoid scheme realizing the restriction of `G` along `g` is a
monomorphism. -/
theorem mono_groupoidPreRelation_restriction (R : GroupoidScheme.Restriction G g)
    [IsEquivalenceRelation G.target G.source] :
    Mono (groupoidPreRelation R.groupoid) := by
  have _ := mono_prodLift_restrictionTarget_restrictionSource G g
  have h : groupoidPreRelation R.groupoid = eqToHom R.arrows_eq ≫
      prod.lift (restrictionTarget G g) (restrictionSource G g) ≫
        prod.map (eqToHom R.objects_eq.symm) (eqToHom R.objects_eq.symm) := by
    ext <;> simp [R.target_eq, R.source_eq]
  rw [h]
  infer_instance

/-! ### The restriction is again an equivalence relation -/

/-- **Restricting a groupoid preserves being an equivalence relation.** If the target and
source maps of `G` are an internal equivalence relation then so are those of any groupoid
scheme realizing the restriction of `G` along `g`, in particular those of
`AlgebraicGeometry.GroupoidScheme.restrict`. -/
theorem restriction_isEquivalenceRelation (R : GroupoidScheme.Restriction G g)
    [IsEquivalenceRelation G.target G.source] :
    IsEquivalenceRelation R.groupoid.target R.groupoid.source :=
  (isEquivalenceRelation_iff_mono_prodLift R.groupoid.target R.groupoid.source).2
    ⟨mono_groupoidPreRelation_restriction G g R,
      groupoidPreRelation_isPreEquivalenceRelation R.groupoid⟩

end AlgebraicGeometry

end
