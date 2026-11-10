module

public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistLocalComparison

/-!
# Comparing the two trivializations of `𝒪(nd)` on the overlap of two charts of the same degree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and let `f` and `g` be homogeneous of the **same**
degree `d`. Over an open `W` inside `D₊(f) ∩ D₊(g)` the twist `𝒪(nd)` has two trivializing
sections, `f ^ n` and `g ^ n`, and they differ by the `n`-th power of the degree-zero fraction
`f / g`, which is a unit of `Γ(W, 𝒪)` there. This file proves that, and the same statement after
tensoring with an arbitrary sheaf of modules `ℱ`.

Equal degrees is what makes the statement typecheck without transport: the trivializing section
of `f` in index `n` is a section of `𝒪(n · deg f)` and the one of `g` of `𝒪(n · deg g)`, so the
two live in the same twist exactly when `deg f = deg g`. This is why the chart bijectivity of
[Stacks, Tag 03GM] is run against a cover by standard opens of elements of the degree of `f`
rather than against a cover by degree-one elements.

## Main results

* `Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection_eq_pow_smul`: **the
  trivializing section `f ^ n` of `𝒪(nd)` is `(f / g) ^ n` times the trivializing section
  `g ^ n`.**
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection_eq_pow_smul`: **the same after
  tensoring with `ℱ`** -- the section `t ⊗ f ^ n` of `ℱ(nd)` is the section
  `((f / g) ^ n · t) ⊗ g ^ n`.

## References

* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite MonoidalCategory DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingSection trivializingFun
  projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (mulTrivSection)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.Cohomology.Generators (toTensorSheafSection_smul_left toTensorSheafSection_smul_right)
open scoped TensorProduct

universe u w

namespace Stacks.AlgebraicGeometry.ProjTrivialization

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The underlying ideal of the homogeneous prime ideal of a point of `Proj 𝒮` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

variable {f : S} {d : ℕ}

/-- **The trivializing section `f ^ n` of `𝒪(nd)` is `(f / g) ^ n` times the trivializing
section `g ^ n`**, for `f` and `g` homogeneous of the same degree `d` and over an open inside
both standard opens. The fraction `f / g` is given by its values in the local rings, so the
statement applies to its restriction to a smaller open as well. -/
theorem trivializingSection_eq_pow_smul {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
    (hc : ∀ x : W, HomogeneousLocalization.val (c.1 x) =
      Localization.mk f ⟨g, hWg x.2⟩) :
    trivializingSection 𝒮 hf (n : ℤ) hWf = c ^ n • trivializingSection 𝒮 hg (n : ℤ) hWg := by
  apply Subtype.ext
  funext x
  have hn : ((n : ℤ)).toNat = n := by omega
  have hn' : (-(n : ℤ)).toNat = 0 := by omega
  change trivializingFun 𝒮 (n : ℤ) hWf x =
    HomogeneousLocalization.val ((c ^ n).1 x) * trivializingFun 𝒮 (n : ℤ) hWg x
  have hcn : HomogeneousLocalization.val ((c ^ n).1 x) =
      (Localization.mk f ⟨g, hWg x.2⟩) ^ n := by
    rw [show ((c ^ n).1 x) = (c.1 x) ^ n from rfl,
      HomogeneousLocalization.val_pow, hc x]
  rw [hcn, trivializingFun, trivializingFun, Localization.mk_pow, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [hn, hn', pow_zero, one_mul, mul_one, SubmonoidClass.coe_pow,
    Submonoid.coe_mul]
  ring

end Stacks.AlgebraicGeometry.ProjTrivialization

namespace Stacks.AlgebraicGeometry.ProjTwistRestriction

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {f : S} {d : ℕ}

/-- **Multiplication by `f ^ n` and by `g ^ n` differ by `(f / g) ^ n`**, for `f` and `g`
homogeneous of the same degree: the section `t ⊗ f ^ n` of `ℱ(nd)` over an open inside
`D₊(f) ∩ D₊(g)` is the section `((f / g) ^ n · t) ⊗ g ^ n`. -/
theorem mulTrivSection_eq_pow_smul {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) (n : ℕ)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
    (hc : ∀ x : W, HomogeneousLocalization.val (c.1 x) = Localization.mk f ⟨g, hWg x.2⟩)
    (t : F.val.obj (op W)) :
    mulTrivSection 𝒮 hf (n : ℤ) F hWf t = mulTrivSection 𝒮 hg (n : ℤ) F hWg (c ^ n • t) := by
  refine Eq.trans (congrArg (fun y => toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 ((n : ℤ) * d)) (op W)
      (t ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op W)] y))
    (Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection_eq_pow_smul
      𝒮 hf hg n hWf hWg c hc)) ?_
  refine Eq.trans (toTensorSheafSection_smul_right (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 ((n : ℤ) * d)) W (c ^ n) t
    (trivializingSection 𝒮 hg (n : ℤ) hWg)) ?_
  exact (toTensorSheafSection_smul_left (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 ((n : ℤ) * d)) W (c ^ n) t
    (trivializingSection 𝒮 hg (n : ℤ) hWg)).symm

end Stacks.AlgebraicGeometry.ProjTwistRestriction

end
