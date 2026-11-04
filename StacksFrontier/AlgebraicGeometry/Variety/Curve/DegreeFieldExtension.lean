module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a locally free sheaf is unchanged by extension of the ground field

Let `k'/k` be an extension of fields, let `X` be a proper scheme of dimension at most one over
`k` and let `ℰ` be a finite locally free `𝒪_X`-module of constant rank `n`. Then the degree of
`ℰ/X/k` equals the degree of `ℰ_{k'}/X_{k'}/k'`.

## Main results

* `AlgebraicGeometry.curveDegree_baseChange_field`: [Stacks, Tag 0B59].
* `AlgebraicGeometry.curveDegree_baseChange_field_pullback`: the same statement for the chosen
  categorical base change.

## Implementation notes

The degree is `AlgebraicGeometry.curveDegree`, an alternating sum of the dimensions over the
ground field of the cohomology of `ℰ` minus the rank times the same sum for the structure sheaf.
Both sums are compared degreewise with
`AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`, which is [Stacks, Tag 02KH]
part (2) for an extension of the ground field: it is the only input the source's proof uses.
Two bookkeeping steps separate the two sums from that comparison. The comparison produces the
inverse image of the structure sheaf of `X`, whereas the degree upstairs is written with the
structure sheaf of `X_{k'}`; the two are identified by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` and the dimension is transported along that
identification by `AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso`. And the degree
upstairs needs its own properness, dimension bound and constant-rank instances; none of these is
a hypothesis of the tag, so each is supplied in the statement rather than assumed. Properness is
stable under base change, the dimension is unchanged by
`AlgebraicGeometry.topologicalKrullDim_baseChange` ([Stacks, Tag 0BY9]), and the inverse image of
a finite locally free sheaf of rank `n` is again one by
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback`. The three are passed as explicit
arguments of `AlgebraicGeometry.curveDegree`, which is why the statement is spelled with `@`.

The base change is given as an arbitrary cartesian square over `Spec k' ⟶ Spec k`, matching the
shape of the cohomological input and of the clauses of [Stacks, Tag 0BY9] in
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/BaseChange.lean`. The specialisation to the
chosen categorical pullback follows by `CategoryTheory.IsPullback.of_hasPullback`.

## References

* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B59.** Let `k'/k` be an extension of fields, let `X` be a proper
scheme of dimension at most one over `k` and let `ℰ` be a finite locally free `𝒪_X`-module of
constant rank. Then the degree of `ℰ` over `k` equals the degree of its inverse image on the
base change `X_{k'}` over `k'`. -/
@[stacks 0B59]
theorem curveDegree_baseChange_field (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    @curveDegree k' _ X' f' (MorphismProperty.of_isPullback (P := @IsProper) h inferInstance)
        ((topologicalKrullDim_baseChange k k' g' f' f h).trans_le hdim)
        ((Scheme.Modules.pullback g').obj E) rank
        (isFiniteLocallyFreeOfRank_pullback g' E rank) =
      curveDegree k f hdim E rank := by
  have hlf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E rank
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hO (n : ℕ) : Module.finrank k'
      (cohomologyOverField k' f' (SheafOfModules.unit X'.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
    (finrank_cohomologyOverField_eq_of_iso k' f' (Scheme.Modules.pullbackUnitIso g') n).symm.trans
      (finrank_cohomologyOverField_baseChange_field k k' g' f' f h
        (SheafOfModules.unit X.ringCatSheaf) n)
  unfold curveDegree
  simp only [finrank_cohomologyOverField_baseChange_field k k' g' f' f h E, hO]

/-- The degree of a finite locally free sheaf of constant rank on a proper scheme of dimension at
most one over a field is unchanged by extension of the ground field, stated for the chosen
categorical base change. -/
theorem curveDegree_baseChange_field_pullback (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    @curveDegree k' _ (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        (MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
          inferInstance)
        ((topologicalKrullDim_baseChange k k' _ _ f (IsPullback.of_hasPullback _ _)).trans_le hdim)
        ((Scheme.Modules.pullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj E) rank
        (isFiniteLocallyFreeOfRank_pullback _ E rank) =
      curveDegree k f hdim E rank :=
  curveDegree_baseChange_field k k' _ _ f (IsPullback.of_hasPullback _ _) hdim E rank

end AlgebraicGeometry

end
