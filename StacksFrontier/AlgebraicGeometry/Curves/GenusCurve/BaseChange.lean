module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Extension of the ground field of a proper scheme, and the genus

Let `k'/k` be an extension of fields and let `X` be a proper scheme over `k`. The base change
`X_{k'}` is again proper over `k'` (`AlgebraicGeometry.IsProper.isStableUnderBaseChange`), has
the same dimension as `X`, again has `k'` for its ring of global regular functions when `X` has
`k`, and has the same genus as `X`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_baseChange`: extending the ground field of a proper
  scheme preserves its Krull dimension.
* `AlgebraicGeometry.isIso_globalSections_baseChange`: if the canonical map `k ⟶ Γ(X, 𝒪_X)` is
  an isomorphism then so is `k' ⟶ Γ(X_{k'}, 𝒪_{X_{k'}})`.
* `AlgebraicGeometry.isIso_globalSections_pullback`: the same statement for the chosen
  categorical pullback, as an instance.
* `AlgebraicGeometry.genus_baseChange`: the genus is unchanged by extension of the ground field.

## References

* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0BY8](https://stacks.math.columbia.edu/tag/0BY8)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0BY9 "properness" AlgebraicGeometry.IsProper.isStableUnderBaseChange

add_to_stacks 0BY8 "genus as first cohomology"
  AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology

/-- For a scheme over a field, the inclusion of a fibre is an isomorphism: the base has a single
point, so the only fibre is the whole scheme. -/
private theorem isIso_fiberι_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : Spec (.of k)) : IsIso (f.fiberι x) := by
  have := isIso_fromSpecResidueField_of_field k x
  change IsIso (pullback.fst f ((Spec (.of k)).fromSpecResidueField x)); infer_instance

/-- For a scheme over a field, the local dimension of a fibre at a point agrees with the local
dimension of the scheme itself at that point. -/
private theorem topologicalKrullDimAt_fiberι_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt X x := by
  have := isIso_fiberι_over_field k f (f x)
  let he := (asIso (f.fiberι (f x))).hom.homeomorph
  rw [topologicalKrullDimAt_eq_of_homeomorph he]
  have hpoint : he (f.asFiber x) = x := by
    simp [he]
  rw [hpoint]

/-- The base change of a scheme over a field along a field extension is surjective, since the
extension of spectra is a surjection of one-point spaces. -/
private theorem surjective_baseChangeOfField
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k'))
    (f : X ⟶ Spec (.of k)) (g : Spec (.of k') ⟶ Spec (.of k))
    (h : IsPullback g' f' f g) : Surjective g' := by
  have hg : Surjective g := by
    refine ⟨?_⟩; intro x
    exact ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback h.flip hg

/-- Extending the ground field of a proper scheme preserves its Krull dimension. -/
@[stacks 0BY9 "dimension"]
theorem topologicalKrullDim_baseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [LocallyOfFiniteType f] :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have hlocal (x' : X') : topologicalKrullDimAt X' x' =
      topologicalKrullDimAt X (g' x') := by
    calc
      topologicalKrullDimAt X' x' =
          topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') :=
        (topologicalKrullDimAt_fiberι_over_field k' f' x').symm
      _ = topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) :=
        topologicalKrullDimAt_fiber_eq_of_isPullback h x'
      _ = topologicalKrullDimAt X (g' x') :=
        topologicalKrullDimAt_fiberι_over_field k f (g' x')
  have hsurj := surjective_baseChangeOfField k k' g' f' f _ h
  have hlocal' (x' : X') :
      TopologicalSpace.localKrullDim X' x' =
        TopologicalSpace.localKrullDim X (g' x') := by
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
      hlocal, TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim, iSup_congr hlocal']
  exact hsurj.surj.iSup_comp (TopologicalSpace.localKrullDim X)

/-- If all global regular functions on a proper scheme over `k` are constant, then after extending
the ground field to `k'` all global regular functions are again constant. -/
@[stacks 0BY9 "global sections"]
theorem isIso_globalSections_baseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have : IsIso f'.appTop := (isPushout_appTop_of_flat h).isIso_inr_of_isIso
  infer_instance

/-- For the chosen categorical base change, the canonical map from `k'` to global regular
functions is an isomorphism whenever the corresponding map over `k` is one. -/
instance isIso_globalSections_pullback (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫
      (pullback.snd (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) :=
  isIso_globalSections_baseChange k k' _ _ f (IsPullback.of_hasPullback _ _)

/-- The genus of a proper scheme over a field is unchanged by extension of the ground field. -/
@[stacks 0BY9 "genus"]
theorem genus_baseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f] :
    genus f' = genus f := by
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  calc
    Module.finrank k' (structureSheafCohomology f' 1)
        = Module.finrank k' (cohomologyOverField k' f'
            (SheafOfModules.unit X'.ringCatSheaf) 1) :=
      (structureSheafCohomologyIsoCohomologyOverField k' f' 1).toLinearEquiv.finrank_eq
    _ = Module.finrank k' (cohomologyOverField k' f'
          ((Scheme.Modules.pullback g').obj (SheafOfModules.unit X.ringCatSheaf)) 1) :=
      (finrank_cohomologyOverField_eq_of_iso k' f' (Scheme.Modules.pullbackUnitIso g') 1).symm
    _ = Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
      finrank_cohomologyOverField_baseChange_field k k' g' f' f h _ 1
    _ = Module.finrank k (structureSheafCohomology f 1) :=
      (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq.symm

end AlgebraicGeometry

end
