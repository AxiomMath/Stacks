module

public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeFieldExtension
import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# The degree of a Picard class on a relative curve commutes with base change

Let `π : Y ⟶ T` be a proper relative curve and let `g : T' ⟶ T` be a morphism, with base change
`π' : Y' ⟶ T'` and `g' : Y' ⟶ Y`. For a Picard class `x` on `Y` and a point `t'` of `T'`, the
degree of the pulled-back class `g'^* x` on the fibre `Y'_{t'}` equals the degree of `x` on the
fibre `Y_{g(t')}`:

`deg_{t'}(g'^* x) = deg_{g(t')}(x)`.

In other words the degree function `Pic(Y) ⟶ (T → ℤ)` of
`StacksFrontier/AlgebraicGeometry/Picard/RelativeCurveDegree.lean` is natural in the base. This is
what makes the degree components `Pic^d` of the Picard functor of a relative curve subfunctors,
the first step of clause (1) of [Stacks, Tag 0BA0].

## Main results

* `AlgebraicGeometry.invertibleCurveDegreeHom_schemePullbackClass_of_isPullback` — the degree of a
  Picard class on a proper curve over a field is unchanged by extension of the ground field: the
  invertible, Picard-class form of [Stacks, Tag 0B59].
* `AlgebraicGeometry.relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback` — the degree
  at `t'` of `g'^* x` is the degree at `g(t')` of `x`.
* `AlgebraicGeometry.relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback` — the same as
  an identity of degree functions: `deg(g'^* x) = deg(x) ∘ g`.

## Implementation notes

The fibre `Y'_{t'}` is the base change of the fibre `Y_{g(t')}` along
`Spec κ(t') ⟶ Spec κ(g(t'))` (Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback`), and
restricting `g'^* x` to `Y'_{t'}` is pulling back the restriction of `x` to `Y_{g(t')}` along that
base change, by functoriality of pullback of Picard classes. So the relative statement is the
field-extension statement at the residue field extension `κ(t')/κ(g(t'))`, made into an algebra by
the residue field map.

## References

* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace AlgebraicGeometry

/-- **The degree of a Picard class is invariant under extension of the ground field.** Let `k'/k`
be a field extension, let `X` be proper of dimension at most one over `k` and let `X'` be its base
change to `k'`. The degree on `X'` of the pullback of a Picard class `x` on `X` is the degree of
`x`. This is the invertible case of [Stacks, Tag 0B59], read on Picard classes. -/
theorem invertibleCurveDegreeHom_schemePullbackClass_of_isPullback (k k' : Type u) [Field k]
    [Field k'] [Algebra k k'] {X' X : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of k')}
    {f : X ⟶ Spec (.of k)} (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [hf : IsProper f] [hf' : IsProper f'] (hdim : topologicalKrullDim X ≤ 1)
    (hdim' : topologicalKrullDim X' ≤ 1) (x : Stacks.Picard.ofScheme X) :
    invertibleCurveDegreeHom k' f' hdim' (Stacks.Picard.schemePullbackClass g' x) =
      invertibleCurveDegreeHom k f hdim x := by
  set L := Stacks.Picard.picardRepresentative X.toRingedSpace x
  have e1 := Stacks.Picard.pullbackClass_classOf g'.toLRSHom.toShHom L.obj L.property
  rw [Stacks.Picard.classOf_picardRepresentative] at e1
  refine (congrArg (invertibleCurveDegreeHom k' f' hdim') e1).trans
    ((invertibleCurveDegreeHom_picardClass k' f' hdim' _ _).trans ?_)
  refine Eq.trans ?_ (congrArg (invertibleCurveDegreeHom k f hdim)
    (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x))
  refine Eq.trans ?_ (invertibleCurveDegreeHom_picardClass k f hdim _ _).symm
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L.obj := L.property
  have := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L.obj
  have : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Stacks.RingedSpace.pullbackFunctor g'.toLRSHom.toShHom).obj L.obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of g'.toLRSHom.toShHom _ L.property
  exact (invertibleCurveDegree_eq_curveDegree_one k' f' hdim' _).trans
    ((curveDegree_baseChange_field k k' g' f' f h hdim L.obj 1).trans
      (invertibleCurveDegree_eq_curveDegree_one k f hdim _).symm)

variable {Y T Y' T' : Scheme.{u}} {g' : Y' ⟶ Y} {π' : Y' ⟶ T'} {π : Y ⟶ T} {g : T' ⟶ T}

/-- **The degree of a Picard class on a relative curve commutes with base change, pointwise.**
For a cartesian square `Y' = Y ×_T T'`, a Picard class `x` on `Y` and a point `t'` of `T'`, the
degree of `g'^* x` on the fibre over `t'` is the degree of `x` on the fibre over `g(t')`. -/
theorem relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
    (h : IsPullback g' π' π g) [IsProper π] [IsProper π']
    (hdim : ∀ t : T, topologicalKrullDim ↥(π.fiber t) ≤ 1)
    (hdim' : ∀ t' : T', topologicalKrullDim ↥(π'.fiber t') ≤ 1) (t' : T')
    (x : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHomAt π' hdim' t' (Stacks.Picard.schemePullbackClass g' x) =
      relativeInvertibleDegreeHomAt π hdim (g t') x := by
  let : Algebra (T.residueField (g t')) (T'.residueField t') :=
    (g.residueFieldMap t').hom.toAlgebra
  have hfib := isPullback_fiberToSpecResidueField_of_isPullback h t'
  have hι : π'.fiberι t' ≫ g' =
      pullback.map _ _ _ _ g' (Spec.map (g.residueFieldMap t')) g h.w.symm (by simp) ≫
        π.fiberι (g t') :=
    (pullback.lift_fst _ _ _).symm
  rw [relativeInvertibleDegreeHomAt_apply, relativeInvertibleDegreeHomAt_apply]
  refine (congrArg (invertibleCurveDegreeHom _ _ (hdim' t'))
    (((Stacks.Picard.schemePullbackClass_comp _ _ x).trans
      (congrArg (fun φ => Stacks.Picard.schemePullbackClass φ x) hι)).trans
        (Stacks.Picard.schemePullbackClass_comp _ _ x).symm)).trans ?_
  exact invertibleCurveDegreeHom_schemePullbackClass_of_isPullback
    (T.residueField (g t')) (T'.residueField t') hfib (hf := isProper_fiberToSpecResidueField π _)
    (hf' := isProper_fiberToSpecResidueField π' t') (hdim (g t')) (hdim' t') _

/-- **The degree function of a relative curve is natural in the base.** For a cartesian square
`Y' = Y ×_T T'` and a Picard class `x` on `Y`, the degree function of `g'^* x` on `T'` is the
degree function of `x` on `T` composed with `g`. -/
theorem relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback
    (h : IsPullback g' π' π g) [IsProper π] [IsProper π']
    (hdim : ∀ t : T, topologicalKrullDim ↥(π.fiber t) ≤ 1)
    (hdim' : ∀ t' : T', topologicalKrullDim ↥(π'.fiber t') ≤ 1)
    (x : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHom π' hdim' (Stacks.Picard.schemePullbackClass g' x) =
      relativeInvertibleDegreeHom π hdim x ∘ g := by
  funext t'
  exact relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback h hdim hdim' t' x

end AlgebraicGeometry

end
