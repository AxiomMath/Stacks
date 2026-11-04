module

public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
import StacksCore.Tactic.StacksAttribute

/-!
# Separated schemes of dimension at most one over a field are H-quasi-projective

A separated scheme `X` of finite type over a field `k` whose topological Krull dimension is at
most one is H-quasi-projective over `k`: it admits a quasi-compact immersion into a projective
space `ℙⁿ_k` over `Spec k`. If `X` is moreover proper over `k`, then it is H-projective over `k`.

## Main definitions

* `Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne`: the proposition that
  every Noetherian separated scheme of topological Krull dimension at most one has an ample
  invertible module.

## Main results

* `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isAmple`: a morphism locally of
  finite type and quasi-compact whose source carries an ample invertible module is
  H-quasi-projective.
* `Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field` and
  `Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field`: a scheme of finite
  type over a field is Noetherian, and a scheme separated over a field is separated.
* `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_dimension_le_one`: a separated scheme
  of finite type over a field `k` of topological Krull dimension at most one is
  H-quasi-projective over `k`.
* `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_topologicalKrullDim_le_one`,
  `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_topologicalKrullDim_eq_zero` and
  `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`: the same conclusion for
  a reduced scheme, a scheme of dimension zero and an integral scheme of dimension one.
* `Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_ampleOfNoetherianSeparatedDimLEOne`:
  the same conclusion, assuming `AmpleOfNoetherianSeparatedDimLEOne`.
* `isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one`: a proper scheme over a field
  `k` of topological Krull dimension at most one is H-projective over `k`.

## Implementation notes

The conclusion `AlgebraicGeometry.IsHQuasiProjective f` asks for a quasi-compact immersion into
`AlgebraicGeometry.projectiveSpaceOver n S` over the base; an immersion is exactly an isomorphism
onto a locally closed subscheme. Finite type is spelled as the conjunction of
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.

Two ampleness predicates occur: `AlgebraicGeometry.Scheme.Modules.IsAmple` and
`Stacks.Ample.IsAmple`. They are identified by `Stacks.AmpleBridge.isAmple_iff_isAmple`.

## References

* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.HQuasiProjectiveDimensionOne

/-! ### Ample invertible modules and H-quasi-projectivity -/

/-- A morphism `f : X ⟶ S` that is locally of finite type and quasi-compact, and whose source
carries an ample invertible module, is H-quasi-projective. -/
theorem isHQuasiProjective_of_isAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.IsHQuasiProjective f := by
  obtain ⟨d₀, -, hd⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple f L hL
  obtain ⟨n, i, hi, hif, -⟩ := hd d₀ le_rfl
  have hif' : i ≫ (projectiveSpaceOver n S ↘ S) = f := by
    rwa [Stacks.HProjective.over_projectiveSpaceOver]
  have hic : QuasiCompact (i ≫ (projectiveSpaceOver n S ↘ S)) := by
    rw [hif']; infer_instance
  exact ⟨n, i, hi, Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated i
    (projectiveSpaceOver n S ↘ S) inferInstance hic, hif⟩

/-! ### Schemes of finite type over a field -/

/-- A scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_finiteType_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.IsNoetherian X :=
  AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType f

/-- A scheme that is separated over a field is separated. -/
theorem isSeparated_of_isSeparated_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] : X.IsSeparated :=
  AlgebraicGeometry.Scheme.IsSeparated.of_isSeparated f

/-! ### Ample invertible modules in dimension at most one -/

/-- The proposition that every Noetherian separated scheme of topological Krull dimension at most
one has an ample invertible module. -/
def AmpleOfNoetherianSeparatedDimLEOne : Prop :=
  ∀ (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated],
    topologicalKrullDim (Y : Type u) ≤ 1 →
      ∃ (L : Y.Modules)
        (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
          (structureSheafRing
            Y.toRingedSpace).property L),
        @AlgebraicGeometry.Scheme.Modules.IsAmple Y L hL

/-! ### Schemes of dimension at most one over a field -/

/-- A separated scheme of finite type over a field that has an ample invertible module, once it is
known to be Noetherian and separated, is H-quasi-projective. -/
private theorem isHQuasiProjective_of_exists_isAmple {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated],
      ∃ (L : X.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        X.ringCatSheaf.2 L), AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    AlgebraicGeometry.IsHQuasiProjective f := by
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated := isSeparated_of_isSeparated_over_field f
  obtain ⟨L, hLinv, hLamp⟩ := h
  exact isHQuasiProjective_of_isAmple f L
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hLamp)

/-- A reduced separated scheme of finite type over a field `k` whose topological Krull dimension
is at most one is H-quasi-projective over `k`. -/
theorem isHQuasiProjective_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [AlgebraicGeometry.IsReduced X] (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    AlgebraicGeometry.IsHQuasiProjective f := by
  exact isHQuasiProjective_of_exists_isAmple f
    (Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      X hdim)

/-- A separated scheme of finite type over a field `k` of topological Krull dimension zero is
H-quasi-projective over `k`. -/
@[stacks 0A25 "for a scheme of topological Krull dimension zero, where reducedness is not needed \
because such a scheme is affine and the structure sheaf of an affine scheme is ample"]
theorem isHQuasiProjective_of_topologicalKrullDim_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) = 0) :
    AlgebraicGeometry.IsHQuasiProjective f := by
  have : IsAffine X := AlgebraicGeometry.isAffine_of_finiteType_of_dimension_zero k f hdim
  exact isHQuasiProjective_of_isAmple f (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X)

/-- If every Noetherian separated scheme of topological Krull dimension at most one has an ample
invertible module, then a separated scheme of finite type over a field `k` whose topological
Krull dimension is at most one is H-quasi-projective over `k`. -/
theorem isHQuasiProjective_of_ampleOfNoetherianSeparatedDimLEOne
    (hample : AmpleOfNoetherianSeparatedDimLEOne.{u}) {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    AlgebraicGeometry.IsHQuasiProjective f := by
  exact isHQuasiProjective_of_exists_isAmple f (hample X hdim)

/-- A separated scheme of finite type over a field `k` whose topological Krull dimension is at
most one is H-quasi-projective over `k`. -/
@[stacks 0A25]
theorem isHQuasiProjective_of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    AlgebraicGeometry.IsHQuasiProjective f :=
  isHQuasiProjective_of_ampleOfNoetherianSeparatedDimLEOne (fun Y _ _ hdimY =>
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      Y hdimY) f hdim

/-- An integral separated scheme of finite type over a field `k` of topological Krull dimension
one is H-quasi-projective over `k`. -/
theorem isHQuasiProjective_of_isIntegral {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [AlgebraicGeometry.IsIntegral X] (hdim : topologicalKrullDim (X : Type u) = 1) :
    AlgebraicGeometry.IsHQuasiProjective f := by
  exact isHQuasiProjective_of_exists_isAmple f
    (AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X hdim)

/-! ### Proper schemes of dimension at most one over a field -/

/-- A proper scheme over a field `k` whose topological Krull dimension is at most one is
H-projective over `k`. -/
@[stacks 0A26]
theorem isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    IsProjectiveMorphism f :=
  (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper (f := f)).mpr
    ⟨isHQuasiProjective_of_dimension_le_one f hdim, inferInstance⟩

end Stacks.HQuasiProjectiveDimensionOne

end
