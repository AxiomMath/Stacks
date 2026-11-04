module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The degree of an invertible sheaf is unchanged by extension of the ground field

Let `k'/k` be an extension of fields, let `X` be a proper scheme of dimension at most one over
`k` and let `ℒ` be an invertible `𝒪_X`-module. Then the degree of `ℒ/X/k` equals the degree of
`ℒ_{k'}/X_{k'}/k'`. This is [Stacks, Tag 0B59] at the degree
`AlgebraicGeometry.invertibleCurveDegree` of an invertible module, which is the spelling in which
the vanishing results of Section [Stacks, Tag 0B5B] state their degree hypotheses.

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_baseChange_field`: [Stacks, Tag 0B59] for an
  invertible module.
* `AlgebraicGeometry.invertibleCurveDegree_baseChange_field_pullback`: the same statement for the
  chosen categorical base change.

## Implementation notes

`AlgebraicGeometry.invertibleCurveDegree` is not literally the rank-one specialisation of
`AlgebraicGeometry.curveDegree`: the two agree by
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree`, but that identification asks for
`SheafOfModules.IsFiniteLocallyFreeOfRank L 1`, which invertibility of `ℒ` supplies only through
a second spelling of invertibility. Since both degrees are alternating sums of the same
cohomological dimensions, it is shorter to run the argument of
`AlgebraicGeometry.curveDegree_baseChange_field` again than to translate: degreewise the
comparison is `AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`, part (2) of
[Stacks, Tag 02KH] for an extension of the ground field, and that is the only input the source's
proof uses.

Three instances of the statement upstairs are supplied rather than assumed, none of them a
hypothesis of the tag: properness is stable under base change ([Stacks, Tag 01W4]), the dimension
is unchanged by `AlgebraicGeometry.topologicalKrullDim_baseChange` ([Stacks, Tag 0BY9]), and the
inverse image of an invertible module is invertible
(`Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry`, [Stacks, Tag 0B8L]). All
three are explicit arguments of `AlgebraicGeometry.invertibleCurveDegree`, which is why the
statement is spelled with `@`.

The base change is given as an arbitrary cartesian square over `Spec k' ⟶ Spec k`, matching
`AlgebraicGeometry.curveDegree_baseChange_field`; the specialisation to the chosen categorical
pullback follows by `CategoryTheory.IsPullback.of_hasPullback`.

## References

* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0B59] for an invertible module.** Let `k'/k` be an extension of fields, let `X`
be a proper scheme of dimension at most one over `k` and let `ℒ` be an invertible `𝒪_X`-module.
Then the degree of `ℒ` over `k` equals the degree of its inverse image on the base change
`X_{k'}` over `k'`.

[Stacks, Tag 0B59] (not registered here: this is not the whole statement of the tag): the
invertible case, at invertibleCurveDegree
-/
theorem invertibleCurveDegree_baseChange_field (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    @invertibleCurveDegree k' _ X' f'
        (MorphismProperty.of_isPullback (P := @IsProper) h inferInstance)
        ((topologicalKrullDim_baseChange k k' g' f' f h).trans_le hdim)
        ((Scheme.Modules.pullback g').obj L)
        (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
          g'.toLRSHom.toShHom L hL) =
      invertibleCurveDegree k f hdim L := by
  have key : ∀ (M' : X'.Modules) (M : X.Modules) [M.IsQuasicoherent],
      (M' ≅ (Scheme.Modules.pullback g').obj M) → ∀ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k' (cohomologyOverField k' f' M' n) : ℤ) =
      (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f M n) : ℤ) := fun M' M _ e n => by
    rw [finrank_cohomologyOverField_eq_of_iso k' f' e n,
      finrank_cohomologyOverField_baseChange_field k k' g' f' f h M n]
  unfold invertibleCurveDegree
  rw [finsum_congr (key _ L (Iso.refl _)),
    finsum_congr (key (SheafOfModules.unit X'.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g').symm)]

/-- The degree of an invertible sheaf on a proper scheme of dimension at most one over a field is
unchanged by extension of the ground field, stated for the chosen categorical base change. -/
theorem invertibleCurveDegree_baseChange_field_pullback (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    @invertibleCurveDegree k' _ (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        (MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
          inferInstance)
        ((topologicalKrullDim_baseChange k k' _ _ f
          (IsPullback.of_hasPullback _ _)).trans_le hdim)
        ((Scheme.Modules.pullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj L)
        (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
          (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).toLRSHom.toShHom L hL) =
      invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_baseChange_field k k' _ _ f (IsPullback.of_hasPullback _ _) hdim L

end AlgebraicGeometry

end
