module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.InvertibleFiltration
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Unconditional
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve

/-!
# The degree of a vector bundle on a proper curve is the degree of its determinant

Let `k` be a field, `X` a proper curve over `k` and `ℰ` a finite locally free `𝒪_X`-module of
constant rank `n + 1`. Then

`deg(ℰ) = deg(⋀^{n+1} ℰ)`,

the first equality of [Stacks, Tag 0DJ5] on a proper curve.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `nonempty_tensorSheaf_exteriorPower_iso` — for `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` short exact with `ℱ` of
  rank `m + 1` and `ℒ` of rank one, `⋀^{m+1} ℱ ⊗ ⋀¹ ℒ ≅ ⋀^{m+2} ℰ`, the isomorphism clause of
  [Stacks, Tag 0B38].
* `curveDegree_eq_curveDegree_exteriorPower_of_hasInvertibleFiltration` — `deg(ℰ) = deg(⋀ ℰ)`
  for a module with a filtration whose successive quotients are invertible.
* `curveDegree_eq_curveDegree_exteriorPower_of_isCurve` — **`deg(ℰ) = deg(⋀^{n+1} ℰ)` on a
  proper curve**, with no further hypothesis.

## Implementation notes

`Stacks.WeilCohomology.HasInvertibleFiltration` records the stages of the filtration as finite
locally free without their ranks. The rank of each kernel is read off: the kernel of an
epimorphism from a module of rank `m + 1` onto an invertible one has rank `m`
(`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`).

## References

* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYS](https://stacks.math.columbia.edu/tag/0AYS)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.WeilCohomology (HasInvertibleFiltration)
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

/-- **The determinant comparison of a short exact sequence on a scheme.** For
`0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` short exact with `ℱ` finite locally free of rank `m + 1` and `ℒ` of rank
one, `⋀^{m+1} ℱ ⊗ ⋀¹ ℒ ≅ ⋀^{m+2} ℰ`. This is the isomorphism clause of [Stacks, Tag 0B38] on a
scheme. -/
theorem nonempty_tensorSheaf_exteriorPower_iso {X : Scheme.{u}} {F E L : X.Modules}
    (i : F ⟶ E) (q : E ⟶ L) (w : i ≫ q = 0) (hS : (ShortComplex.mk i q w).ShortExact) (m : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1)]
    [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj
            ((Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ)))) ≅
      Scheme.Modules.exteriorPower E ((m + 2 : ℕ) : ℤ)) :=
  ⟨@asIso _ _ _ _ _ (@Stacks.SheafOfModules.TopWedge.isIso_detComparison _ X.sheaf F E L
    (_root_.SheafOfModules.algebras _ F) (_root_.SheafOfModules.algebras _ E)
    (_root_.SheafOfModules.algebras _ L) i q w hS.exact hS.mono_f hS.epi_g (m + 1) 0 hF hL)⟩


/-- **The first equality of [Stacks, Tag 0DJ5] along a filtration with invertible quotients.**
On a proper curve over a field, a finite locally free module of rank `n + 1` with a filtration
of length `n + 1` whose successive quotients are invertible has the degree of its top exterior
power. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_hasInvertibleFiltration (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (h : HasInvertibleFiltration X E (n + 1)) :
    curveDegree k f hdim E (n + 1) =
      @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)) := by
  induction n generalizing E with
  | zero => exact curveDegree_exteriorPower_one_eq k f hdim E
  | succ m ih =>
    cases h with
    | @step _ F L _ i q w hS hL _ hF =>
      have := hL
      have : Epi q := hS.epi_g
      have hker : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel q) (m + 1) :=
        Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
          q hS.epi_g hL (m + 1) inferInstance
      have hFr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) :=
        SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
          (IsLimit.conePointUniqueUpToIso hS.fIsKernel (kernelIsKernel q)).symm (h := hker)
      have hdetF := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F (m + 1)
      have hdetE := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (m + 2)
      have hdetL := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self L 1
      obtain ⟨t⟩ := nonempty_tensorSheaf_exteriorPower_iso i q w hS m
      have hTen : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj
                ((Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ))))) 1 :=
        SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X
          (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ))
          (Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ)) 1 1
      have hadd : curveDegree k f hdim E (m + 2) =
          curveDegree k f hdim F (m + 1) + curveDegree k f hdim L 1 :=
        curveDegree_add_of_shortExact_of_isProper k f hdim (ShortComplex.mk i q w) hS (m + 1)
          (m + 2) 1
      rw [hadd, ih F hF, curveDegree_exteriorPower_one_eq k f hdim L,
        ← curveDegree_eq_of_iso k f hdim 1 t,
        curveDegree_tensorSheaf_eq_add k f hdim (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ))
          (Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ)) 1 1]
      ring

/-- **The first equality of [Stacks, Tag 0DJ5] on a proper curve**: a finite locally free module
of constant rank `n + 1` on a proper curve over a field has the same degree as its top exterior
power,

`deg(ℰ) = deg(⋀^{n+1} ℰ)`,

with no further hypothesis. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_isCurve (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    curveDegree k f hdim E (n + 1) =
      @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)) := by
  obtain ⟨X', g, hg, hfilt⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration' (n + 1) X E
      inferInstance
  have : IsProper g := hg.2.1
  have : IsIntegral X' := hg.2.2
  have hc : IsCurve k (g ≫ f) := isCurve_comp_of_isModification k f g hg
  have hdimX' : topologicalKrullDim X' ≤ 1 := hc.topologicalKrullDim_eq_one.le
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)
  have hbij : Set.BijOn g (genericPointsOne X') (genericPointsOne X) := by
    rw [genericPointsOne_eq_singleton X' hc.topologicalKrullDim_eq_one,
      genericPointsOne_eq_singleton X hdimX]
    have h1 := hg.1.1
    rwa [genericPoints_eq_singleton, genericPoints_eq_singleton] at h1
  have hstalk : ∀ z ∈ genericPointsOne X', IsIso (g.stalkMap z) := by
    intro z hz
    rw [genericPointsOne_eq_singleton X' hc.topologicalKrullDim_eq_one,
      Set.mem_singleton_iff] at hz
    subst hz
    exact IsBirational.isIso_stalkMap hg.1 _ (by rw [genericPoints_eq_singleton]; rfl)
  have hE' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) (n + 1) :=
    isFiniteLocallyFreeOfRank_pullback g E (n + 1)
  have hdetE := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)
  have hdetE' := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self
    ((Scheme.Modules.pullback g).obj E) (n + 1)
  have hpdetE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))) 1 :=
    isFiniteLocallyFreeOfRank_pullback g _ 1
  rw [← curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper k (g ≫ f) f hdimX' hdim g
      rfl hbij E (n + 1) hstalk,
    ← curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper k (g ≫ f) f hdimX' hdim g
      rfl hbij (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1 hstalk,
    curveDegree_eq_curveDegree_exteriorPower_of_hasInvertibleFiltration k (g ≫ f) hdimX' n _
      hfilt]
  exact curveDegree_eq_of_iso k (g ≫ f) hdimX' 1
    (Scheme.Modules.exteriorPowerPullbackIso g E ((n + 1 : ℕ) : ℤ)).symm

end AlgebraicGeometry

end
