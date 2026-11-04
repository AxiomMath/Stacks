module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.OneIsNeverZero

/-!
# Restricting a ringed site to a dense subsite

Let `X` be a ringed site and let `G : C ⥤ X.C` exhibit `(C, J)` as a dense subsite of
`(X.C, X.J)`. Restricting the structure sheaf along `G` makes `(C, J)` a ringed site, whose
three universes are those of `C`, of its morphisms, and of the sections of the structure sheaf
of `X`. This is the construction that transports statements about a ringed site whose underlying
category is too large to a small model of it.

## Main definitions and results

* `AlgebraicGeometry.RingedSite.denseRestrict`: the restricted ringed site.
* `AlgebraicGeometry.RingedSite.unitsAddSheaf_denseRestrict`: restriction carries the additive
  sheaf of units to the additive sheaf of units, on the nose.
* `AlgebraicGeometry.RingedSite.isLocallyRinged_denseRestrict`: the restriction of a locally
  ringed site is locally ringed.
* `AlgebraicGeometry.RingedSite.hasSheafify_denseRestrict` carries sheafification of abelian
  presheaves over to the projection spelling of the restricted site's topology.

## Implementation notes

`AlgebraicGeometry.RingedSite.denseRestrict` is not reducible: instances for the Picard group
of a ringed site, such as `Stacks.Cohomology.Torsors.Generators.picardGroupAddCommGroup`, are
keyed on the pattern `?X.O.obj`, which an unfolded restriction would no longer match.

Both conjuncts of `AlgebraicGeometry.RingedSite.IsLocallyRinged` transport by a sections-level
argument, because the sections of the restricted structure sheaf over `U` are literally the
sections of `X.O` over `G.obj U`, with literally the same restriction maps.

For the nonvanishing of `1` this uses the criterion
`Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff`, which applies to
`AlgebraicGeometry.RingedSite.oneIsNeverZero` because the two spellings of the canonical map out
of the empty sheaf agree definitionally. The covering hypothesis then transports because the
empty sieve pushes forward to the empty sieve, so `functorPushforward_mem_iff` says an object of
the subsite is covered by the empty sieve exactly when its image is.

For the local-unit condition the covering is pulled back: a dense subsite functor is
cocontinuous, so `CategoryTheory.Functor.cover_lift` turns a covering sieve of `G.obj U` into
one of `U`, and membership of an arrow `g` in the pulled-back sieve is membership of `G.map g`
in the original.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 05D7](https://stacks.math.columbia.edu/tag/05D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ v₁ u₂ v₂

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

namespace AlgebraicGeometry.RingedSite

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (X : RingedSite.{u₂, v₂, w}) (G : C ⥤ X.C) [G.IsDenseSubsite J X.J]

/-- **A ringed site restricted to a dense subsite.** The underlying site is `(C, J)` and the
structure sheaf is the restriction of `X.O` along `G`. -/
def denseRestrict : RingedSite.{u₁, v₁, w} where
  C := C
  J := J
  O := (G.sheafPushforwardContinuous CommRingCat.{w} J X.J).obj X.O

/-- The underlying category of the restricted ringed site is `C`. -/
@[simp]
theorem denseRestrict_C : (denseRestrict J X G).C = C := rfl

/-- The topology of the restricted ringed site is `J`. -/
@[simp]
theorem denseRestrict_J : (denseRestrict J X G).J = J := rfl

/-- The structure sheaf of the restricted ringed site is the restriction of `X.O` along `G`. -/
@[simp]
theorem denseRestrict_O :
    (denseRestrict J X G).O = (G.sheafPushforwardContinuous CommRingCat.{w} J X.J).obj X.O :=
  rfl

/-- Sheafification on the restricted ringed site, at the projection spelling of its topology.

The topology of `AlgebraicGeometry.RingedSite.denseRestrict J X G` is `J`, but only
definitionally, so instance search does not carry a hypothesis on `J` over to it. -/
instance hasSheafify_denseRestrict [HasSheafify J AddCommGrpCat.{w}] :
    HasSheafify (denseRestrict J X G).J AddCommGrpCat.{w} :=
  inferInstanceAs (HasSheafify J AddCommGrpCat.{w})

/-- The sections of the restricted structure sheaf over an object of the subsite are the
sections of the original structure sheaf over its image. -/
theorem denseRestrict_O_obj_obj (U : Cᵒᵖ) :
    (denseRestrict J X G).O.obj.obj U = X.O.obj.obj (G.op.obj U) := rfl

/-- **Restriction to a dense subsite carries the additive sheaf of units to the additive sheaf
of units.** Both are the sheaf of units of the sections, formed objectwise, so restricting the
structure sheaf and then taking units is taking units and then restricting. -/
theorem unitsAddSheaf_denseRestrict :
    (G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).obj
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf X) =
      Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (denseRestrict J X G) :=
  rfl

/-- The empty sieve covers an object of a dense subsite exactly when it covers its image. -/
theorem bot_mem_iff_bot_mem (U : C) :
    (⊥ : Sieve U) ∈ J U ↔ (⊥ : Sieve (G.obj U)) ∈ X.J (G.obj U) := by
  rw [← Sieve.functorPushforward_bot G U]
  exact (G.functorPushforward_mem_iff J X.J).symm

/-- **The nonvanishing of `1` transports to a dense subsite.** -/
theorem isIso_oneIsNeverZero_denseRestrict (hX : IsIso (oneIsNeverZero X)) :
    IsIso (oneIsNeverZero (denseRestrict J X G)) :=
  (Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff
      (J := (denseRestrict J X G).J) (denseRestrict J X G).O).2 fun U hU =>
    (Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff (J := X.J) X.O).1 hX (G.obj U)
      fun h => hU ((bot_mem_iff_bot_mem J X G U).2 h)

/-- **The local-unit condition transports to a dense subsite.** -/
theorem locallyEitherUnit_denseRestrict (hX : LocallyEitherUnit X.O) :
    LocallyEitherUnit (denseRestrict J X G).O := by
  intro U f
  obtain ⟨S, hS, hP⟩ := hX (G.obj U) f
  refine ⟨S.functorPullback G, G.cover_lift J X.J hS, fun {V} g hg => ?_⟩
  exact hP (G.map g) hg

/-- **Stacks 04EU on a dense subsite.** The restriction of a locally ringed site to a dense
subsite is locally ringed. -/
theorem isLocallyRinged_denseRestrict (hX : IsLocallyRinged X) :
    IsLocallyRinged (denseRestrict J X G) :=
  ⟨isIso_oneIsNeverZero_denseRestrict J X G hX.1,
    locallyEitherUnit_denseRestrict J X G hX.2⟩

end AlgebraicGeometry.RingedSite

end
