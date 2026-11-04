module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatDimensionFunctorPure
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityIffUniversalPurity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ProperSupport

/-!
# Universal flattening of a pure module

Let `f : X ⟶ S` be a morphism of schemes and `F` a quasi-coherent `𝒪_X`-module. Stacks 05UH
asserts that a universal flattening `S' ⟶ S` of `F` exists, and is a monomorphism of finite
presentation, in each of the following cases:

1. `f` and `F` are of finite presentation and `F` is pure relative to `S`;
2. `f` is of finite presentation and `X` is pure relative to `S` (the case `F = 𝒪_X`);
3. `f` is proper and of finite presentation and `F` is of finite presentation;
4. `f` is proper and of finite presentation (the case `F = 𝒪_X`).

The source deduces all four from Stacks 05UG applied to `F_0 = F_flat`, together with Stacks
05K3, which says that a module on a proper scheme is universally pure, hence pure. This file
carries out that deduction from
`FlatDimensionSituation.exists_mono_finitePresentation_representableBy_of_isPure` (Stacks 05UG);
all names here are in the namespace `AlgebraicGeometry`.

## Main results

* `exists_mono_finitePresentation_representableBy_of_isPureRelative`: part (1).
* `exists_mono_finitePresentation_representableBy_of_isSchemePureRelative`: part (2).
* `exists_mono_finitePresentation_representableBy_of_isProper`: part (3).
* `exists_mono_finitePresentation_representableBy_structureSheaf_of_isProper`:
  part (4), with the monomorphism of finite presentation that the source states only in the
  other three parts.

## Implementation notes

A universal flattening of `F` is a representing object of the flatness functor `F_flat` of
Stacks 05MW (`AlgebraicGeometry.FlatnessSituation.HasUniversalFlattening`), and a universal
flattening of `X` is one of `𝒪_X` (`AlgebraicGeometry.HasUniversalFlattening`). Each result
exhibits that representing object `Z` over `S` together with the two properties of `Z ⟶ S`.

The functor `F_0` of Stacks 05MT and `F_flat` are subterminal functors carried by the
conditions "flat in dimensions `≥ 0`" and "flat", which are the same
(`AlgebraicGeometry.isFlatOver_iff_isFlatOverInDimensionsGE_zero`); a representing object of one
is a representing object of the other through
`Stacks.Flatness.isCutOutByMonoFP_iff_exists_representableBy`.

A module of finite presentation is quasi-coherent and of finite type
(`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation`),
but typeclass search does not find either instance from `SheafOfModules.IsFinitePresentation`.
Quasi-coherence is listed among the instance arguments because the flatness situation requires
it, and part (1) also lists finiteness of type because the purity condition requires it; neither
restricts the statement.

## References

* [Stacks Project, Tag 05UH](https://stacks.math.columbia.edu/tag/05UH)
* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
* [Stacks Project, Tag 05K3](https://stacks.math.columbia.edu/tag/05K3)
* [Stacks Project, Tag 05MW](https://stacks.math.columbia.edu/tag/05MW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Flatness Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05UH, part (1).** Let `f : X ⟶ S` be of finite
presentation and let `F` be an `𝒪_X`-module of finite presentation which is pure relative to
`S`. Then the universal flattening `Z ⟶ S` of `F` exists and is a monomorphism of finite
presentation. -/
@[stacks 05UH "part (1)"]
theorem exists_mono_finitePresentation_representableBy_of_isPureRelative
    {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [F.IsFinitePresentation]
    (hpure : IsPureRelative f F) :
    ∃ Z : Over S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty (Functor.RepresentableBy
        ({ S := S, X := X, f := f, F := F, isQuasicoherent := ‹F.IsQuasicoherent› } :
          FlatnessSituation.{u}).flatFunctor Z) := by
  let E : FlatDimensionSituation.{u} := { S := S, X := X, f := f, F := F, n := 0 }
  have hE := (isCutOutByMonoFP_iff_exists_representableBy E.flatDimensionFunctor).mpr
    (E.exists_mono_finitePresentation_representableBy_of_isPure hpure)
  refine (isCutOutByMonoFP_iff_exists_representableBy _).mp (hE.of_iff fun T ↦ ?_)
  rw [E.flatDimensionFunctor_obj_nonempty_iff, FlatnessSituation.flatFunctor_obj_nonempty_iff]
  exact (isFlatOver_iff_isFlatOverInDimensionsGE_zero (E.baseChangeMap T)
    (E.baseChangeModule T)).symm

/-- **Stacks Project, Tag 05UH, part (2).** Let `f : X ⟶ S` be of finite
presentation and let `X` be pure relative to `S`. Then the universal flattening `Z ⟶ S` of `X`
exists and is a monomorphism of finite presentation. -/
@[stacks 05UH "part (2)"]
theorem exists_mono_finitePresentation_representableBy_of_isSchemePureRelative
    {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hpure : IsSchemePureRelative f) :
    ∃ Z : Over S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty ((structureSheafFlatnessSituation f).flatFunctor.RepresentableBy Z) := by
  have := structureSheaf_isFiniteType X
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  exact exists_mono_finitePresentation_representableBy_of_isPureRelative
    f (SheafOfModules.unit X.ringCatSheaf) hpure

/-- **Stacks Project, Tag 05UH, part (3).** Let `f : X ⟶ S` be proper
and of finite presentation and let `F` be an `𝒪_X`-module of finite presentation. Then the
universal flattening `Z ⟶ S` of `F` exists and is a monomorphism of finite presentation. -/
@[stacks 05UH "part (3)"]
theorem exists_mono_finitePresentation_representableBy_of_isProper
    {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ Z : Over S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty (Functor.RepresentableBy
        ({ S := S, X := X, f := f, F := F, isQuasicoherent := ‹F.IsQuasicoherent› } :
          FlatnessSituation.{u}).flatFunctor Z) :=
  have := (isQuasicoherent_isFiniteType_of_isFinitePresentation F ‹_›).2
  exists_mono_finitePresentation_representableBy_of_isPureRelative f F
    (isPureRelative_of_isUniversallyPureRelative f F (isUniversallyPureRelative_of_isProper f F))

/-- **Stacks Project, Tag 05UH, part (4).** Let `f : X ⟶ S` be proper
and of finite presentation. Then the universal flattening `Z ⟶ S` of `X` exists, and it is a
monomorphism of finite presentation. -/
@[stacks 05UH "part (4)"]
theorem exists_mono_finitePresentation_representableBy_structureSheaf_of_isProper
    {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] :
    ∃ Z : Over S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty ((structureSheafFlatnessSituation f).flatFunctor.RepresentableBy Z) :=
  exists_mono_finitePresentation_representableBy_of_isSchemePureRelative f
    (isPureRelative_of_isUniversallyPureRelative _ _
      (isSchemeUniversallyPureRelative_of_isProper f))

end AlgebraicGeometry

end
