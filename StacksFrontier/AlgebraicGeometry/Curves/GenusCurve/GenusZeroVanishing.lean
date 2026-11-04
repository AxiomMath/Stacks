module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering

/-!
# Genus zero means the first cohomology of the structure sheaf vanishes

The genus of [Stacks, Tag 0BY7] is the *dimension* `dim_k H¹(X, 𝒪_X)`, so `genus f = 0` says
only that the dimension is zero, which for an arbitrary vector space does not say that the space
is zero. For `X` proper over `k` it does: [Stacks, Tag 02O6] makes `H¹(X, 𝒪_X)` a
finite-dimensional `k`-vector space, and a finite-dimensional space of dimension zero is zero.

This file turns `genus f = 0` into the vanishing of `H¹(X, 𝒪_X)` in the `Hgroup` spelling — the
abelian-group-valued one in which the vanishing theorems of the cohomology development are
stated, and which the higher-direct-image results consume.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_unit_one_of_genus_eq_zero`: `H¹(X, 𝒪_X) = 0` in
  the `AlgebraicGeometry.cohomologyOverField` presentation.
* `AlgebraicGeometry.isZero_rightDerived_evaluation_unit_one_of_genus_eq_zero`: the same for the
  right derived functor of evaluation, with no restriction of scalars.
* `AlgebraicGeometry.isZero_Hgroup_unit_one_of_genus_eq_zero`: the same in the `Hgroup`
  spelling.

## Implementation notes

Three presentations of `H¹(X, 𝒪_X)` are crossed here, and each crossing is a named comparison
already in the library:

* `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` identifies the cohomology
  the genus is defined from with `AlgebraicGeometry.cohomologyOverField`;
* `AlgebraicGeometry.cohomologyOverField` is a restriction of scalars of the right derived
  functor of `SheafOfModules.evaluation`, by definition, and a restriction of scalars leaves the
  underlying type alone, so the two are subsingletons together;
* `Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup` identifies
  the vanishing of that right derived functor with the vanishing of `Hgroup`.

The finiteness input is `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`,
[Stacks, Tag 02O6] over a field base, which is a theorem of this repository; the coherence of the
structure sheaf it needs is
`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`. So properness is the only
hypothesis beyond `genus f = 0`, and no finiteness has to be assumed.

No `@[stacks ...]` attribute: this is the step of [Stacks, Tag 0E3H]'s proof that reads the
genus-zero clause of a rational tail as a vanishing theorem, and it is not the statement of
[Stacks, Tag 0BY7] or of [Stacks, Tag 02O6].

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **The first cohomology of the structure sheaf of a scheme of genus zero, proper over its
ground field, vanishes**, in the `AlgebraicGeometry.cohomologyOverField` presentation.

The genus is the `Module.finrank` of this very module, transported along
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`; [Stacks, Tag 02O6] over a
field base makes it finite-dimensional, and a finite-dimensional space whose `finrank` is zero
is a subsingleton. -/
public theorem isZero_cohomologyOverField_unit_one_of_genus_eq_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hgenus : genus f = 0) :
    Limits.IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
  have hcoh : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    cohomologyFiniteDimensionalOverField_of_isProper k X f inferInstance
      (SheafOfModules.unit X.ringCatSheaf) hcoh 1
  have hrank : Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) = 0 := by
    rw [← (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
    exact (genus_eq_finrank_structureSheafCohomology f).symm.trans hgenus
  have : Subsingleton (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    Module.finrank_zero_iff.1 hrank
  exact ModuleCat.isZero_of_subsingleton _

/-- **The first cohomology of the structure sheaf of a scheme of genus zero, proper over its
ground field, vanishes**, as the first right derived functor of evaluation on `X`.

`AlgebraicGeometry.cohomologyOverField` is a restriction of scalars of this module, and a
restriction of scalars does not change the underlying type. -/
public theorem isZero_rightDerived_evaluation_unit_one_of_genus_eq_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hgenus : genus f = 0) :
    Limits.IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived
      1).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  have hs : Subsingleton (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_unit_one_of_genus_eq_zero k f hgenus)
  exact @ModuleCat.isZero_of_subsingleton _ _ _ hs

/-- **`H¹(X, 𝒪_X) = 0` for a scheme of genus zero, proper over its ground field**, in the
`Hgroup` spelling of cohomology.

This is the form in which the genus-zero clause of a rational tail ([Stacks, Tag 0E3H]) is
consumed by the higher-direct-image vanishing results. -/
public theorem isZero_Hgroup_unit_one_of_genus_eq_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hgenus : genus f = 0) :
    Limits.IsZero (Hgroup X.ringCatSheaf ⊤ 1 (SheafOfModules.unit X.ringCatSheaf)) :=
  (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ 1 (SheafOfModules.unit X.ringCatSheaf)).1
    (isZero_rightDerived_evaluation_unit_one_of_genus_eq_zero k f hgenus)

end AlgebraicGeometry

end
