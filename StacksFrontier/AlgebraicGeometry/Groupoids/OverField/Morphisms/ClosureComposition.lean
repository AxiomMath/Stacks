module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.PairGroupoidRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.ReducedClosureGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.ArrowImageOverField

/-!
# The relation of a groupoid scheme over a field

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` the spectrum of a field and let
`j = (t, s) : R ⟶ U ×_S U` be its relation.  The closure `Z` of the image of `j` is stable
under the composition law `pr₀₂` of `U ×_S U`, and for `U` the spectrum of a perfect field
the reduced closed subscheme on `Z`, respectively the scheme-theoretic image of `j` when `R` is
quasi-compact, is the scheme of arrows of a groupoid scheme on `U`.

## Main results

* `AlgebraicGeometry.comp_mapsTo_closure_range_groupoidPreRelation`: `pr₀₂` maps
  `Z ×_{pr₁, U, pr₀} Z` into `Z`.
* `AlgebraicGeometry.quasiCompact_left_groupoidPreRelation`: the relation of a groupoid scheme
  over a field with quasi-compact scheme of arrows is a quasi-compact morphism.
* `AlgebraicGeometry.reducedClosureGroupoidPreRelation`: the groupoid scheme on the reduced
  closed subscheme supported on `Z`, over a perfect field.
* `AlgebraicGeometry.exists_groupoidScheme_image_groupoidPreRelation`: the groupoid scheme on
  the scheme-theoretic image of `j`, for `R` quasi-compact.

## Implementation notes

All three are the corresponding statements for a morphism of groupoid schemes over a field
which is the identity on objects, applied to `j` viewed as a morphism from the groupoid into
the pair groupoid `(U, U ×_S U, pr₁, pr₀, pr₀₂)`.  The first is set theoretic, so `Z` appears
as the closure of the range of `j` on underlying topological spaces and no subscheme structure
on it is needed.

The source lists the restricted structure maps in the order `(pr₀|_Z, pr₁|_Z)`, which is the
opposite of the order in which they appear in the pair groupoid; the composition `pr₀₂` is
defined on `Z ×_{pr₁, U, pr₀} Z` in both, so the source and target are taken here to be
`pr₁|_Z` and `pr₀|_Z`, as they are in the pair groupoid.

Quasi-compactness of `R` is recorded as quasi-compactness of its underlying space, from which
quasi-compactness of `j` follows because `s` factors through it and `pr₁` is quasi-separated,
being a base change of the morphism from the spectrum of a field to `S`.

## References

* [Stacks Project, Tag 04QB](https://stacks.math.columbia.edu/tag/04QB)
* [Stacks Project, Tag 04QC](https://stacks.math.columbia.edu/tag/04QC)
* [Stacks Project, Tag 04QD](https://stacks.math.columbia.edu/tag/04QD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
  (hfield : G.objects.left = Spec (.of k))

include hfield

/-- **Stacks Project, Tag 04QB.** Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U`
the spectrum of a field, and let `Z` be the closure of the image of `j = (t, s)` in `U ×_S U`.
Then `pr₀₂` maps `Z ×_{pr₁, U, pr₀} Z` into `Z`. -/
@[stacks 04QB]
theorem comp_mapsTo_closure_range_groupoidPreRelation :
    Set.MapsTo
      (prod.lift
        (pullback.fst (prod.snd : G.objects ⨯ G.objects ⟶ G.objects) prod.fst ≫ prod.fst)
        (pullback.snd (prod.snd : G.objects ⨯ G.objects ⟶ G.objects) prod.fst
          ≫ prod.snd)).left.base
      ((pullback.fst (prod.snd : G.objects ⨯ G.objects ⟶ G.objects) prod.fst).left.base ⁻¹'
          closure (Set.range (groupoidPreRelation G).left.base) ∩
        (pullback.snd (prod.snd : G.objects ⨯ G.objects ⟶ G.objects) prod.fst).left.base ⁻¹'
          closure (Set.range (groupoidPreRelation G).left.base))
      (closure (Set.range (groupoidPreRelation G).left.base)) :=
  comp_mapsTo_closure_range_mapArrows (k := k) (groupoidPreRelationHom G) rfl hfield rfl

/-- **Stacks Project, Tag 04QC.** For a groupoid scheme `(U, R, s, t, c)` over `S` with `U` the
spectrum of a perfect field, the reduced closed subscheme `Z` of `U ×_S U` supported on the
closure of the image of `j = (t, s)` is the scheme of arrows of a groupoid scheme on `U` whose
structure maps are the restrictions of `pr₁`, `pr₀` and `pr₀₂`. -/
@[stacks 04QC]
noncomputable def reducedClosureGroupoidPreRelation [PerfectField k] :
    GroupoidScheme.ReducedClosureImage (groupoidPreRelationHom G) :=
  GroupoidScheme.reducedClosureImage (k := k) (groupoidPreRelationHom G) rfl hfield rfl

/-- The relation `j = (t, s)` of a groupoid scheme whose scheme of objects is the spectrum of a
field and whose scheme of arrows is quasi-compact is a quasi-compact morphism. -/
theorem quasiCompact_left_groupoidPreRelation [CompactSpace G.arrows.left] :
    QuasiCompact (groupoidPreRelation G).left := by
  have hqs : QuasiSeparatedSpace G.objects.left := by rw [hfield]; infer_instance
  have hpb : IsPullback (prod.fst (X := G.objects) (Y := G.objects)).left
      (prod.snd (X := G.objects) (Y := G.objects)).left G.objects.hom G.objects.hom :=
    Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
      (prodIsProd G.objects G.objects)
  have hqsnd : QuasiSeparated (prod.snd (X := G.objects) (Y := G.objects)).left :=
    MorphismProperty.of_isPullback hpb (QuasiSeparated.of_quasiSeparatedSpace _)
  have heq : (groupoidPreRelation G).left ≫
      (prod.snd (X := G.objects) (Y := G.objects)).left = G.source.left := by
    rw [← Over.comp_left]; simp [groupoidPreRelation]
  have : QuasiCompact ((groupoidPreRelation G).left ≫
      (prod.snd (X := G.objects) (Y := G.objects)).left) := by
    rw [heq]; exact quasiCompact_of_compactSpace _
  exact QuasiCompact.of_comp _ (prod.snd (X := G.objects) (Y := G.objects)).left

/-- **Stacks Project, Tag 04QD.** For a groupoid scheme `(U, R, s, t, c)` over `S` with `U` the
spectrum of a field and `R` quasi-compact, the scheme-theoretic image of `j = (t, s)` in
`U ×_S U` is the scheme of arrows of a groupoid scheme on `U` whose structure maps are the
restrictions of `pr₁`, `pr₀` and `pr₀₂`. -/
@[stacks 04QD]
theorem exists_groupoidScheme_image_groupoidPreRelation [CompactSpace G.arrows.left] :
    ∃ (H : GroupoidScheme S) (ι : GroupoidScheme.Hom H (prodPairGroupoid G.objects))
      (hHobjects : H.objects = G.objects)
      (hHarrows : H.arrows = Over.mk ((groupoidPreRelation G).left.imageι ≫
        (G.objects ⨯ G.objects).hom)),
        (ι.mapObjects = eqToHom hHobjects) ∧
        (ι.mapArrows.left =
          eqToHom (congrArg Over.left hHarrows) ≫ (groupoidPreRelation G).left.imageι) :=
  have : QuasiCompact (groupoidPreRelationHom G).mapArrows.left :=
    quasiCompact_left_groupoidPreRelation (k := k) G hfield
  exists_groupoidScheme_image (k := k) (groupoidPreRelationHom G) rfl hfield rfl

end AlgebraicGeometry

end
