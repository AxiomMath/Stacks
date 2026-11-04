module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness and finite local freeness, with or without a rank, are fpqc local on the base

`StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget` proves that finiteness and
finite local freeness of a morphism of schemes are local on the base for the fpqc topology *as
soon as affineness is*, carrying the assertion of Tag 02L5 as a hypothesis, and its
implementation notes say that assertion "is not available".

It is available: `Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc` in
`StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine` is Tag 02L5, proved
unconditionally and carrying `@[stacks 02L5]`. Feeding it to those reductions makes Tag 02LA
and the first assertion of Tag 02VO unconditional, and the *fixed-degree* assertion of Tag 02VO
follows too, because the rank criterion
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq` turns it into a statement
about the rank function, which is compatible with base change.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc`: **Tag 02LA.** Finiteness of a morphism of
  schemes is fpqc local on the base.
* `Stacks.Morphisms.isFiniteLocallyFree_descendsAlong` and
  `Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc`: the descent step and the first
  assertion of **Tag 02VO.** Being finite locally free is fpqc local on the base.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_descendsAlong` and
  `Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`: the descent step and the
  second assertion of **Tag 02VO.** Being finite locally free of a fixed degree is fpqc local
  on the base.

## Implementation notes

**How the fixed-degree assertion is proved.** The source reads the degree off the fibre
`(f_*𝒪_Z)_u ⊗_{𝒪_{U,u}} κ(u)` of the direct image. Here that fibre is Mathlib's
`AlgebraicGeometry.Scheme.Hom.finrank`, and
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq` says a finite flat morphism
is finite locally free of degree `r` exactly when that function is constantly `r`. The rank
function is compatible with base change — `AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback`
— so if the base change along a surjective morphism has constant rank `r`, then so does the
morphism itself, surjectivity being what lets every point of the target be reached. The
finiteness and flatness that the criterion needs of the descended morphism come from the
degree-free case.

**Nothing is re-proved.** The descent step of Tag 02LA is already in the library, untagged, as
`AlgebraicGeometry.Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact`
(`StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal`); it is used rather than
re-derived, which is why this module imports a module of chapter 68 even though its own content
belongs to chapter 35.

**These are stated as theorems, not instances.**
`CategoryTheory.MorphismProperty.IsLocalAtTarget` and
`CategoryTheory.MorphismProperty.DescendsAlong` are classes, so all six results could be
instances; they are not, because an instance for a property as widely used as
`AlgebraicGeometry.IsFinite` can hijack unification away from the spellings that existing lemmas
elsewhere use. Consumers supply them with `have`, which is the pattern
`StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification` already expects of its
`h02LA` and `h02VO` hypotheses.

**Chapter.** Tags 02LA and 02VO belong to chapter 35, *Descent*, not to chapter 68. They are
proved here because the fibre-degree stratification of Tag 086T carries both as hypotheses and
all the ingredients for discharging them were already present and unnoticed.

## References

* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 02L9](https://stacks.math.columbia.edu/tag/02L9)
* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- **Stacks Project, Tag 02LA.** Finiteness of a morphism of schemes is local on the base for
the fpqc topology.

A finite morphism is an integral morphism which is locally of finite type, integrality is
universal closedness together with affineness, and of those three constituents only affineness
was missing; it is Tag 02L5, `Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc`. So this is
`Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom` with its hypothesis
discharged. -/
@[stacks 02LA,
  ega "II 6.3.10" "Locality on X",
  ega "IV 2.7.1" "(xv)",
  sga "1 VIII 5.7" "more general",
  sga "4 IV 8.5.5"]
theorem isFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsFinite.{u} : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  isFinite_isLocalAtTarget_fpqc_of_isAffineHom Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc

/-- **The first assertion of Stacks Project, Tag 02VO**, the descent step. Finite locally free
morphisms satisfy fpqc descent: if the base change of `g` along a surjective flat quasi-compact
morphism is finite locally free, then so is `g`.

Being finite locally free is being finite, flat and locally of finite presentation, and each
factor descends: the first is
`AlgebraicGeometry.Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact`, which is
the descent step of Tag 02LA, and the other two are Mathlib's. -/
@[stacks 02VO "the descent step, finite locally free", sga "1 VIII 5.7" "partial"]
theorem isFiniteLocallyFree_descendsAlong :
    MorphismProperty.DescendsAlong
      (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      ((@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u})) := by
  have hprop : (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) =
      (@IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
    ext X S f
    rw [isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  have _ := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have _ :=
    AlgebraicGeometry.Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  rw [hprop]
  have _ : MorphismProperty.DescendsAlong
      ((@IsFinite.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}))
      ((@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.DescendsAlong.inf
  exact MorphismProperty.DescendsAlong.inf

/-- **The second assertion of Stacks Project, Tag 02VO**, the descent step. Morphisms which are
finite locally free of a fixed degree `r` satisfy fpqc descent: if the base change of `g` along
a surjective flat quasi-compact morphism is finite locally free of degree `r`, then so is `g`.

The degree-free case makes `g` finite, flat and locally of finite presentation, so the rank
criterion `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq` applies to both `g`
and its base change and turns the statement into one about the rank function
`AlgebraicGeometry.Scheme.Hom.finrank`. That function is compatible with base change by
`AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback`, and the covering morphism is surjective
on points, so the rank of `g` at an arbitrary point of its target is the rank of the base
change at a point above it, which is `r`. -/
@[stacks 02VO "the descent step, fixed degree", sga "1 VIII 5.7" "special case"]
theorem isFiniteLocallyFreeOfRank_descendsAlong (r : ℕ) :
    MorphismProperty.DescendsAlong (IsFiniteLocallyFreeOfRank.property.{u} r)
      ((@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u})) := by
  have _ := isFiniteLocallyFree_descendsAlong.{u}
  refine ⟨fun {A X Y Z fst snd f g} hpb hQf hfst => ?_⟩
  have hfstr : IsFiniteLocallyFreeOfRank fst r := hfst
  have hflf : IsFiniteLocallyFree fst := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree fst r
  obtain ⟨_, _, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation fst).mp hflf
  have hgflf : IsFiniteLocallyFree g :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})) hpb hQf hflf
  obtain ⟨_, _, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp hgflf
  have hrk : ∀ x : X, Scheme.Hom.finrank fst x = r :=
    (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq fst r).mp hfstr
  refine (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g r).mpr fun z => ?_
  obtain ⟨x, hx⟩ := (show Function.Surjective f.base from hQf.1.1.1) z
  have h1 : Scheme.Hom.finrank fst x = Scheme.Hom.finrank g (f.base x) :=
    Scheme.Hom.finrank_of_isPullback snd fst g f hpb.flip x
  rw [← hx, ← h1]
  exact hrk x

/-! ### The fpqc-locality statements of Tag 02VO

Both are `instance`s in `StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget`,
which this file imports directly:
`Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc` and, for a fixed degree,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`. This file supplies the
descent steps they rest on — `isFiniteLocallyFree_descendsAlong` and
`isFiniteLocallyFreeOfRank_descendsAlong` above — and deliberately does not restate the
conclusions. The latter is the hypothesis `h02VO` of
`AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge`, which resolves to
the imported instance under the same fully-qualified name.
-/

end Stacks.Morphisms

end
