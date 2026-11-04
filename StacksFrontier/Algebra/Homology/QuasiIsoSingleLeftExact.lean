module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Left exact functors and resolutions concentrated in nonnegative degrees

Three small facts about a resolution `ι : A[0] ⟶ J` in an abelian category and a functor `F`
which only preserves finite limits:

* the cohomology of `J` vanishes outside degree `0`;
* `F` preserves the left homology of a short complex whose first object is zero;
* hence, when `J` vanishes in negative degrees, `F` applied to `ι` is an isomorphism on `H⁰`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LeftExactHomology

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- The cohomology of a resolution of an object vanishes outside degree `0`. -/
lemma isZero_homology_of_quasiIso_single {ω : 𝒜} {J : CochainComplex 𝒜 ℤ}
    (ι : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]
    (n : ℤ) (hn : n ≠ 0) : IsZero (J.homology n) :=
  (HomologicalComplex.isZero_single_obj_homology _ 0 ω n hn).of_iso
    (asIso (HomologicalComplex.homologyMap ι n)).symm

/-- A functor preserving finite limits preserves the left homology of a short complex whose
first object is zero. -/
lemma preservesLeftHomologyOf_of_isZero_X₁ {ℬ : Type*} [Category* ℬ] [Abelian ℬ] (F : 𝒜 ⥤ ℬ)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] (S : ShortComplex 𝒜)
    (hS : IsZero S.X₁) : F.PreservesLeftHomologyOf S :=
  ⟨fun h => { g := inferInstance, f' := preservesCokernel_zero' F h.f' (hS.eq_of_src _ _) }⟩

/-- **A left exact functor takes a resolution `A[0] ⟶ J`, with `J` concentrated in nonnegative
degrees, to a map which is an isomorphism on `H⁰`.** -/
lemma quasiIsoAt_zero_map_of_preservesFiniteLimits {ℬ : Type*} [Category* ℬ] [Abelian ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] {ω : 𝒜} {J : CochainComplex 𝒜 ℤ}
    [J.IsStrictlyGE 0] (ι : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj ω ⟶ J)
    [QuasiIso ι] : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ι) 0 := by
  rw [quasiIsoAt_iff]
  have : F.PreservesLeftHomologyOf
      (HomologicalComplex.sc ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj ω) 0) :=
    preservesLeftHomologyOf_of_isZero_X₁ F _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 ω _ (by simp))
  have : F.PreservesLeftHomologyOf (J.sc 0) :=
    preservesLeftHomologyOf_of_isZero_X₁ F _ (J.isZero_of_isStrictlyGE 0 _ (by simp))
  have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor _ _ 0).map ι) :=
    (quasiIsoAt_iff ι 0).1 inferInstance
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map ι)

end Stacks.LeftExactHomology
