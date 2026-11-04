module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Vanishing of `H¹` in large degree on a geometrically integral curve over any field

[Stacks, Tag 0B90], which is
`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree` in the
`AlgebraicGeometry` namespace, says that `H¹(X, ℒ) = 0` for an invertible `ℒ` of degree at least
`2g - 1` on a proper curve over an algebraically closed field. This file transports it to a proper
curve over an arbitrary field `K` which is geometrically integral: over an algebraic closure `K̄`
the base change is a proper curve of the same genus, the pullback of `ℒ` has the same degree, and
the dimensions of the cohomology groups do not change ([Stacks, Tag 02KH]).

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_baseChange`: the degree of an invertible module is
  invariant under extension of the ground field.
* `AlgebraicGeometry.isZero_cohomologyOverField_one_of_geometricallyIntegral`: the vanishing.

## References

* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An invertible module is invertible for the sheaf-valued structure and is quasi-coherent. -/
private theorem isInvertible_sheaf_and_isQuasicoherent {X : Scheme.{u}} (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L ∧ L.IsQuasicoherent :=
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  ⟨this, isQuasicoherent_of_isInvertible L⟩

/-- **The degree of an invertible module is invariant under extension of the ground field.** For
a base change square `X' = X ×_k k'`, the pullback of an invertible `ℒ` on `X` has the same degree
as `ℒ`: its Euler characteristic and that of the structure sheaf are unchanged
([Stacks, Tag 02KH]). -/
theorem invertibleCurveDegree_baseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    [IsProper f'] (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1)
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [hL' : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g').obj L)] :
    invertibleCurveDegree k' f' hdim' ((Scheme.Modules.pullback g').obj L) =
      invertibleCurveDegree k f hdim L := by
  obtain ⟨_, _⟩ := isInvertible_sheaf_and_isQuasicoherent L hL
  let e : (Scheme.Modules.pullback g').obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X'.ringCatSheaf := Scheme.Modules.pullbackUnitIso g'
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by
      rw [finrank_cohomologyOverField_baseChange_field k k' g' f' f h L]
  · exact finsum_congr fun n => by
      rw [← finrank_cohomologyOverField_eq_of_iso k' f' e,
        finrank_cohomologyOverField_baseChange_field k k' g' f' f h
          (SheafOfModules.unit X.ringCatSheaf)]

/-- **[Stacks, Tag 0B90] over an arbitrary field, for a geometrically integral curve.** Let `X` be
a proper curve over a field `K` which is geometrically integral over `K`, of genus `g`, and `ℒ`
an invertible module of degree at least `2g - 1`. Then `H¹(X, ℒ) = 0`. -/
theorem isZero_cohomologyOverField_one_of_geometricallyIntegral (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [GeometricallyIntegral f]
    (L : X.Modules) (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hdeg : 2 * (genus f : ℤ) - 1 ≤ @invertibleCurveDegree K _ X f _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le L hL) :
    IsZero (cohomologyOverField K f L 1) := by
  let K' := AlgebraicClosure K
  let b : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  let g : pullback f b ⟶ X := pullback.fst f b
  let f' : pullback f b ⟶ Spec (.of K') := pullback.snd f b
  have h : IsPullback g f' f b := IsPullback.of_hasPullback f b
  have : IsProper f' := MorphismProperty.of_isPullback h ‹_›
  have : GeometricallyIntegral f' := MorphismProperty.of_isPullback h ‹_›
  have : IsIntegral (pullback f b) := GeometricallyIntegral.isIntegral_of_subsingleton f'
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)
  have hdim' : topologicalKrullDim (pullback f b : Scheme.{u}) = 1 := by
    rw [topologicalKrullDim_baseChange K K' g f' f h, hdimX]
  have : IsCurve K' f' := isCurve_of_topologicalKrullDim_eq_one K' f' hdim'
  have hgen : genus f' = genus f := genus_baseChange K K' g f' f h
  have hL' : SheafOfModules.IsInvertible (pullback f b).sheaf.obj
      (pullback f b).ringCatSheaf.property ((Scheme.Modules.pullback g).obj L) :=
    Stacks.Divisors.pullback_isInvertible g L
  have hdeg' := @invertibleCurveDegree_baseChange K K' _ _ _ _ _ g f' f h _ _ hdimX.le hdim'.le
    L hL hL'
  have hvan := isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree K'
    f' ((Scheme.Modules.pullback g).obj L) hL' (by rw [hgen]; exact hdeg.trans_eq hdeg'.symm)
  obtain ⟨_, _⟩ := isInvertible_sheaf_and_isQuasicoherent L hL
  have hfin : Module.finrank K (cohomologyOverField K f L 1) = 0 := by
    rw [← finrank_cohomologyOverField_baseChange_field K K' g f' f h L 1]
    have := ModuleCat.subsingleton_of_isZero hvan
    exact Module.finrank_zero_of_subsingleton
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have := finiteDimensional_cohomologyOverField_of_isProper K f L 1
  exact ModuleCat.isZero_iff_subsingleton.mpr (Module.finrank_zero_iff.mp hfin)

end AlgebraicGeometry

end
