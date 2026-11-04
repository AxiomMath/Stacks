module

public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Vanishing of the cohomology of a proper scheme over a field in high degrees

On a scheme proper over a field the cohomology of a quasi-coherent module vanishes in every
degree at least the affine covering number of the scheme. The bound depends on the scheme
alone, so it is uniform in the module.

Consequently the Euler characteristic `AlgebraicGeometry.eulerCharacteristic` is additive along a
short exact sequence of coherent modules as soon as the cohomology of the two outer modules is
finite-dimensional below that bound.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_of_affineCoverNum_le`: the cohomology of a
  quasi-coherent module on a scheme proper over a field vanishes in degrees at least the affine
  covering number.
* `AlgebraicGeometry.finrank_cohomologyOverField_eq_zero_of_affineCoverNum_le`: the same with
  the conclusion read as a dimension.
* `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'`: additivity of
  the Euler characteristic along a short exact sequence of coherent modules on a proper scheme
  over a field, assuming only finite dimensionality of the cohomology of the two outer modules
  below the covering bound.

## Implementation notes

Properness supplies the two hypotheses of [Stacks, Tag 01XI]: a proper morphism is
quasi-compact, so the source is a compact space, and a proper morphism is separated, so the
absolute diagonal of the source is an affine morphism. Neither uses the base being a field.

[Stacks, Tag 01XI] is stated for the cohomology groups
`Hgroup`, the right derived functors of abelian-group-valued sections, whereas
`AlgebraicGeometry.cohomologyOverField` derives module-valued sections and then restricts
scalars to the ground field. The canonical comparison of the two is the content of
[Stacks, Tag 01F1] part (1), available here as
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`; vanishing transports
across it because an abelian group isomorphic to a zero object is a subsingleton, a
subsingleton module is a zero object, and restriction of scalars preserves zero objects.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Vanishing of cohomology in high degrees on a proper scheme over a field.** The cohomology
of a quasi-coherent module on a scheme proper over a field vanishes in every degree at least
the affine covering number `t(X)` of the scheme. The bound does not depend on the module. -/
public theorem isZero_cohomologyOverField_of_affineCoverNum_le [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : X.affineCoverNum ⊤ ≤ n) :
    IsZero (cohomologyOverField k f F n) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsSeparated (terminal.from X) := by
    have : IsSeparated (f ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  have hforget : IsZero
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
          AddCommGrpCat.{u}).obj F) :=
    (isZero_cohomology_of_affineCoverNum_le X F n hn).of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ n).app F)
  exact (ModuleCat.restrictScalars _).map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hforget))

/-- The dimension over the ground field of the cohomology of a quasi-coherent module on a
proper scheme is zero in every degree at least the affine covering number. -/
public theorem finrank_cohomologyOverField_eq_zero_of_affineCoverNum_le [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (hn : X.affineCoverNum ⊤ ≤ n) :
    Module.finrank k (cohomologyOverField k f F n) = 0 :=
  have := ModuleCat.subsingleton_of_isZero
    (isZero_cohomologyOverField_of_affineCoverNum_le k f F n hn)
  Module.finrank_zero_of_subsingleton

/-- **Additivity of the Euler characteristic on a proper scheme over a field.** For a short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent modules on a scheme proper over a field,
`χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)` as soon as the cohomology of `ℱ₁` and of `ℱ₃` is
finite-dimensional in the degrees below the affine covering number. -/
public theorem eulerCharacteristic_add_of_shortExact_of_finiteDimensional' [IsProper f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (hfin₁ : ∀ n < X.affineCoverNum ⊤, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₃ : ∀ n < X.affineCoverNum ⊤, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) :
    eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ :=
  have : S.X₁.IsQuasicoherent := isQuasicoherent_of_isCoherent S.X₁
  have : S.X₃.IsQuasicoherent := isQuasicoherent_of_isCoherent S.X₃
  eulerCharacteristic_add_of_shortExact_of_outer k f hS _ hfin₁ hfin₃
    (fun n hn => isZero_cohomologyOverField_of_affineCoverNum_le k f S.X₁ n hn)
    fun n hn => isZero_cohomologyOverField_of_affineCoverNum_le k f S.X₃ n hn

end AlgebraicGeometry

end
