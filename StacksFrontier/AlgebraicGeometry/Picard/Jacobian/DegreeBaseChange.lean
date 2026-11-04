module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The degree on the Picard group is invariant under extension of the ground field

Let `k'/k` be an extension of fields and `X` a proper scheme of dimension at most one over `k`,
with base change `X' = X ×_k k'`.  Pulling Picard classes back along `X' ⟶ X` preserves the
degree of `Stacks.Picard.ofSchemeDegree`: the Euler characteristic of a quasi-coherent module
does not change under flat base change to `k'` ([Stacks, Tag 02KH], in the form
`AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`), and neither does that of the
structure sheaf.  This is [Stacks, Tag 0B59] read on the Picard group.

## Main results

* `Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isPullback`.

## References

* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **The degree of a Picard class is unchanged by extension of the ground field.** For a
cartesian square `X' ⟶ X` over `Spec k' ⟶ Spec k` with `X` proper of dimension at most one over
`k`, the degree over `k'` of the pullback to `X'` of a class of `Pic(X)` is its degree over `k`. -/
theorem ofSchemeDegree_schemePullbackClass_of_isPullback (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k'))
    (f : X ⟶ Spec (.of k)) (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [IsProper f] [IsProper f'] (hX : topologicalKrullDim X ≤ 1) (hX' : topologicalKrullDim X' ≤ 1)
    (c : ofScheme X) :
    ofSchemeDegree k' f' hX' (schemePullbackClass g' c) = ofSchemeDegree k f hX c := by
  obtain ⟨L, hL, rfl⟩ : ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L),
      Stacks.SheafOfModules.picardClass X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL = c :=
    ⟨_, _, classOf_picardRepresentative X.toRingedSpace c⟩
  have hpb := pullbackClass_classOf g'.toLRSHom.toShHom L hL
  show ofSchemeDegree k' f' hX' (pullbackClass g'.toLRSHom.toShHom _) = _
  rw [hpb]
  refine (ofSchemeDegree_picardClass k' f' hX' _ _).trans
    (Eq.trans ?_ (ofSchemeDegree_picardClass k f hX L hL).symm)
  let := isInvertible_ringCatSheaf_of_isInvertible L hL
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have : L.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree L
  have hunit : (Scheme.Modules.pullback g').obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X'.ringCatSheaf := Scheme.Modules.pullbackUnitIso g'
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by
      rw [show (Stacks.RingedSpace.pullbackFunctor g'.toLRSHom.toShHom).obj L =
        (Scheme.Modules.pullback g').obj L from rfl,
        finrank_cohomologyOverField_baseChange_field k k' g' f' f h L n]
  · exact finsum_congr fun n => by
      rw [(finrank_cohomologyOverField_eq_of_iso k' f' hunit n).symm.trans
        (finrank_cohomologyOverField_baseChange_field k k' g' f' f h
          (SheafOfModules.unit X.ringCatSheaf) n)]

end Stacks.Picard

end
