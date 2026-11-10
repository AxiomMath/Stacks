module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism

/-!
# The degree-zero scalars act on shifted global sections through the structure morphism

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded
`S`-module, `X = Proj 𝒮` and `π : X ⟶ Spec 𝒮_0` the structure morphism. For a homogeneous
element `m` of degree `n` the global section
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections` of `M(n)~` attached to it
has value `m / 1` at every point. Multiplying `m` by a **degree-zero** element `a` of `S`
therefore multiplies that global section by the function `π^♯(a)`, since `π^♯(a)` has value
`a / 1` at every point too.

That identity is the linearity the affine recovery of a morphism out of a pullback asks for.
`Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` recovers a morphism `g^*𝒫 ⟶ 𝒩` over an
affine base from a `Γ(base, 𝒪)`-**linear** map on global sections, and additivity is not enough;
for the canonical map `π^*ℳ_n ⟶ ℳ(n)~` the prescribed map on global sections is
`degreeNToGlobalSections`, whose source `𝒨 n` is an `𝒮_0`-module and whose target is a module
over `Γ(X, 𝒪_X)` with `𝒮_0` acting through `π^♯`. This file supplies exactly that equation.

## Main results

* `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_smul`: **the global
  section attached to `a · m`, for `a` of degree zero, is `π^♯(a)` times the global section
  attached to `m`.**

## Implementation notes

The product `a · m` is passed as a separate homogeneous element of degree `n` together with the
equation identifying its underlying element, rather than built with
`SetLike.GradedSMul.smul_mem`: the latter lands in the degree `0 +ᵥ n`, which is
`((0 : ℕ) : ℤ) + n` and not `n`, so stating the lemma with it would put a transport of degrees in
front of the left-hand side and obscure the content. This is the idiom the Veronese section maps
use for the same reason.

The proof is pointwise. Both sides are global sections of `M(n)~`, so it suffices to compare
their values in every module fibre; `degreeNToGlobalSections_apply` evaluates the left-hand side,
`Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val` evaluates the function
`π^♯(a)`, and the action of the structure sheaf on the fibres is the action of the full
localization through `HomogeneousLocalization.val`, which turns the scalar `a / 1` into the
action of `a` itself.

## References

* [Stacks Project, Equation 27.10.0.6, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (ModuleFiber associatedModuleSheaf associatedModuleSheafSectionsEquiv moduleSections)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

universe u v w t

namespace Stacks.AlgebraicGeometry.ProjShiftedSections

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The function on `Proj 𝒮` pulled back from a degree-zero element of `S`** along the
structure morphism `π : Proj 𝒮 ⟶ Spec 𝒮_0`, read in the spelling
`(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op ⊤)` of the global functions that the
sections of an associated module sheaf are a module over. The scheme-level spelling
`Γ(Proj 𝒮, ⊤)` of the same type is the one `Scheme.Hom.appTop` produces, and the two are equal
only up to unfolding `AlgebraicGeometry.Proj`, which instance search does not do. -/
def pullbackDegreeZero (a : 𝒮 0) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
      (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :=
  (AlgebraicGeometry.Proj.toSpecZero 𝒮).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (𝒮 0))).inv a)

omit [Decomposition 𝒨] in
/-- **A degree-zero scalar acts on shifted global sections through the structure morphism.**
For `a` of degree zero and `m` of degree `n`, the global section of `M(n)~` attached to the
product `a · m` is the function `π^♯(a)` pulled back along `π : Proj 𝒮 ⟶ Spec 𝒮_0` times the
global section attached to `m`.

This is the `𝒮_0`-linearity of the canonical map `𝒨 n ⟶ Γ(Proj 𝒮, M(n)~)`, the scalars acting on
the target through `π^♯`. -/
theorem degreeNToGlobalSections_smul (n : ℤ) (a : 𝒮 0) (m : 𝒨 n) (am : 𝒨 n)
    (ham : (am : M) = (a : S) • (m : M)) :
    degreeNToGlobalSections 𝒮 𝒨 n am =
      pullbackDegreeZero 𝒮 a • degreeNToGlobalSections 𝒮 𝒨 n m := by
  refine (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).injective ?_
  refine Subtype.ext (funext fun x => ?_)
  have happly : ∀ y : 𝒨 n, ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤)
      (degreeNToGlobalSections 𝒮 𝒨 n y)).1 x =
      LocalizedModule.mk (y : M) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    fun y => degreeNToGlobalSections_apply 𝒮 𝒨 n y x.1
  have hscalar : HomogeneousLocalization.val ((pullbackDegreeZero 𝒮 a).1 x) =
      algebraMap S (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (a : S) :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val 𝒮 a x.1
  rw [happly am, ham]
  change _ = HomogeneousLocalization.val ((pullbackDegreeZero 𝒮 a).1 x) •
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤)
      (degreeNToGlobalSections 𝒮 𝒨 n m)).1 x
  rw [happly m, hscalar, algebraMap_smul, LocalizedModule.smul'_mk]

end Stacks.AlgebraicGeometry.ProjShiftedSections

end
