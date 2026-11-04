module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Vanishing of cohomology on a scheme over a field, read in either spelling

On a scheme two spellings of the cohomology of an `𝒪_X`-module over the whole space are in use.
`AlgebraicGeometry.cohomologyOverField` derives the *module*-valued sections functor and then
restricts scalars to the ground field, so that it is a module over that field;
`Hgroup` derives the abelian-group-valued sections functor and is
therefore a plain abelian group. The two are identified by [Stacks, Tag 01F1] part (1), and in
particular one vanishes exactly when the other does.

The equivalence of the two vanishing conditions is what cohomological arguments actually consume:
`AlgebraicGeometry.isZero_cohomology_of_affineCoverNum_le` and the dévissage principles are
phrased for `Hgroup`, while the Euler characteristic and the Hilbert
polynomial are phrased for `AlgebraicGeometry.cohomologyOverField`.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`: the cohomology of a module on
  a scheme over a field vanishes as a module over that field exactly when the corresponding
  cohomology group vanishes.

## Implementation notes

Neither direction uses the field structure or the structure morphism: both reduce to the
underlying abelian group being trivial. Concretely, restriction of scalars neither creates nor
destroys elements, a module is a zero object exactly when it is a subsingleton, the same holds
for abelian groups, and
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` identifies the
abelian group underlying the module-valued cohomology with the cohomology group.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **The two spellings of cohomology vanish together.** For a module `ℱ` on a scheme `X`
equipped with a structure morphism to the spectrum of a field `k`, the `k`-module
`Hⁱ(X, ℱ)` of `AlgebraicGeometry.cohomologyOverField` is a zero object exactly when the abelian
group `Hⁱ(X, ℱ)` of `Hgroup` is. This is the vanishing content of the
comparison [Stacks, Tag 01F1] part (1). -/
public theorem isZero_cohomologyOverField_iff_isZero_hgroup (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) (i : ℕ) :
    IsZero (cohomologyOverField k f F i) ↔ IsZero (Hgroup X.ringCatSheaf ⊤ i F) :=
  ⟨fun h =>
    have hs : Subsingleton
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i).obj F) :=
      @ModuleCat.subsingleton_of_isZero k _ (cohomologyOverField k f F i) h
    ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
        AddCommGrpCat.{u}).map_isZero (ModuleCat.isZero_iff_subsingleton.mpr hs)).of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ i).app F).symm,
  fun h =>
    (ModuleCat.restrictScalars _).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
        (h.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
          X.ringCatSheaf ⊤ i).app F))))⟩

end AlgebraicGeometry

end
