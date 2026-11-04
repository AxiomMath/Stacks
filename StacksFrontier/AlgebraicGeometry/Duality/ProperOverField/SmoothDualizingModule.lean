module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.RelativeDualizingComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# The relative dualizing module of a smooth scheme over a field

Let `X` be smooth of relative dimension `d` over a field `k`. If the relative dualizing complex
`ω_X^•` is a module `M` placed in degree `-d`, then the relative dualizing module
`ω_X = H^{-dim(X)}(ω_X^•)` is `M`: a nonempty such `X` has dimension `d`, and on the empty scheme
every module is zero. For `X` proper and smooth of relative dimension `d` over `k` this gives
part (7) of [Stacks, Tag 0FVV]: `ω_X^• ≅ ∧^d Ω_{X/k}[d]` and `ω_X ≅ ∧^d Ω_{X/k}`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.Duality

/-- A scheme smooth of relative dimension `d` over a field has dimension `d`, read as the natural
number `ENat.toNat ((topologicalKrullDim X).getD 0)` the relative dualizing module is indexed
by, provided it is nonempty. -/
theorem toNat_topologicalKrullDim_getD_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} [Nonempty X] (d : ℕ) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension d f] :
    ENat.toNat ((topologicalKrullDim X).getD 0) = d := by
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f]
  rfl

section Module

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (d : ℕ)
  [SmoothOfRelativeDimension d f]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
  (ωY : quasiCoherentDerivedCategory (Spec (.of k)))

/-- **The relative dualizing module of a smooth scheme over a field.** If `X` is smooth of
relative dimension `d` over `k` and its relative dualizing complex is a module `M` placed in
degree `-d`, then the relative dualizing module `ω_X = H^{-dim(X)}(ω_X^•)` is `M`. -/
theorem nonempty_relativeDualizingModule_iso_of_iso_singleFunctor (M : X.Modules)
    (e : (relativeDualizingComplex f hpush ωY).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-d)).obj M) :
    Nonempty (relativeDualizingModule f hpush ωY ≅ M) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hzero : ∀ N : X.Modules, IsZero N := fun N => by
      have : IsIso (0 : N ⟶ N) :=
        (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap _).2 fun x => isEmptyElim x
      exact ((isIsoZero_iff_source_target_isZero N N).1 this).1
    exact ⟨(hzero _).iso (hzero _)⟩
  · refine ⟨?_⟩
    have h := toNat_topologicalKrullDim_getD_of_smoothOfRelativeDimension d f
    show (DerivedCategory.homologyFunctor X.Modules
      (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj
        (relativeDualizingComplex f hpush ωY).obj ≅ M
    rw [h]
    exact (DerivedCategory.homologyFunctor X.Modules (-d)).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-d)).app M

end Module

/-- **[Stacks, Tag 0FVV], part (7).** Let `X` be proper over a field `k`, with
`ω_X^• = a(𝒪_{Spec k})`. If `X ⟶ Spec k` is smooth of relative dimension `d`, then
`ω_X^• ≅ ∧^d Ω_{X/k}[d]` and `ω_X ≅ ∧^d Ω_{X/k}`. -/
@[stacks 0FVV "part (7): for X smooth of relative dimension d over k, ω_X^• ≅ ∧^d Ω_{X/k}[d] and \
ω_X ≅ ∧^d Ω_{X/k}"]
theorem nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Nonempty ((relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d)) ∧
    Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let e := (singleFunctorExteriorPowerIsoRelativeDualizingComplex f d).symm
  ⟨⟨e⟩, nonempty_relativeDualizingModule_iso_of_iso_singleFunctor f d _ _ _ e⟩

end Stacks.Duality
