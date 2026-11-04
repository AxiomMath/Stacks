module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Normality and regularity agree in dimension at most one

A regular scheme is always normal. In dimension at most one the converse holds: a locally
Noetherian normal scheme of dimension `≤ 1` is regular, since each of its local rings is a
Dedekind domain. For a curve over a field normality and regularity are therefore the same
condition.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_of_isNormal` — the local rings of a locally
  Noetherian normal scheme of dimension at most one are regular local rings.
* `AlgebraicGeometry.isRegular_of_isNormal_of_topologicalKrullDim_le_one` — such a scheme is
  regular.
* `AlgebraicGeometry.isRegular_iff_isNormal_of_topologicalKrullDim_le_one` — the two conditions
  are equivalent in dimension at most one.
* `AlgebraicGeometry.isRegular_iff_isNormal_of_isCurve` — the equivalence for a curve over a
  field.

## References

* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The local ring at a point of a locally Noetherian normal scheme of dimension at most one is
a regular local ring. -/
@[ega "IV 7.9.1" "partial"]
public theorem isRegularLocalRing_stalk_of_isNormal (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsNormal X] (hX : topologicalKrullDim X ≤ 1) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans
      (by rwa [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk])
  let : IsDomain (X.presheaf.stalk x) := IsNormal.stalk_isDomain x
  let : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim)
  let : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  let : IsDedekindRing (X.presheaf.stalk x) := ⟨⟩
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- A locally Noetherian normal scheme of dimension at most one is regular. -/
@[stacks 0BX2, ega "IV 5.8.6" "(i), dim ≤ 1"]
public theorem isRegular_of_isNormal_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsNormal X] (hX : topologicalKrullDim X ≤ 1) :
    IsRegular X :=
  ((isRegular_tfae X).out 1 2 rfl rfl).mpr
    ⟨inferInstance, isRegularLocalRing_stalk_of_isNormal X hX⟩

/-- For a locally Noetherian scheme of dimension at most one, regularity and normality are the
same condition. -/
public theorem isRegular_iff_isNormal_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X ≤ 1) :
    IsRegular X ↔ IsNormal X :=
  ⟨isNormal_of_isRegular X, fun _ => isRegular_of_isNormal_of_topologicalKrullDim_le_one X hX⟩

/-- A curve over a field is regular exactly when it is normal. -/
@[ega "II 7.4.5" "special case"]
public theorem isRegular_iff_isNormal_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] : IsRegular X ↔ IsNormal X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isRegular_iff_isNormal_of_topologicalKrullDim_le_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

end AlgebraicGeometry

end
