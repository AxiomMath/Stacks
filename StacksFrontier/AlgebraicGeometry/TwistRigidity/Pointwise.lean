module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# Pointwise arithmetic of the twists on an absolute `Proj`

Arithmetic in one local ring of `Proj S`, the pointwise formula for the canonical product of two
local sections of the twists, and the restrictions to an open of the global sections of the
twists attached to homogeneous elements.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn`: the restriction to an open of the
  global section of `𝒪(k)` attached to a homogeneous element of degree `k`.

## Main results

* `Stacks.AlgebraicGeometry.TwistRigidity.isUnit_mkOne`: `c / 1` is a unit of the localization
  at a submonoid containing `c`.
* `Stacks.AlgebraicGeometry.TwistRigidity.eq_of_mkOne_mul_eq`: multiplication by such a `c / 1`
  is injective.
* `Stacks.AlgebraicGeometry.TwistRigidity.mkOne_mul_mk`: `(c / 1) · (β / c) = β / 1`.
* `Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply`: the value of
  `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` at a point is the product
  of the two local values.
* `Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr`: equal sections of a twist have equal
  values at every point.
* `Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_apply`: the value of `degreeSectionOn`
  at every point is `c / 1`.
* `Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_mul_apply`: the product of
  `degreeSectionOn` with a section whose values are `β / c` has every value equal to `β / 1`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistRigidity

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### One local ring -/

/-- A fraction with denominator `1` and numerator in the submonoid is a unit. -/
public theorem isUnit_mkOne (P : Submonoid S) {c : S} (hc : c ∈ P) :
    IsUnit (LocalizedModule.mk c (1 : P)) := by
  refine IsUnit.of_mul_eq_one (b := Localization.mk 1 ⟨c, hc⟩) ?_
  show Localization.mk c (1 : P) * Localization.mk 1 ⟨c, hc⟩ = 1
  rw [Localization.mk_mul, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- Multiplication by `c / 1` is injective on the localization at a submonoid containing `c`. -/
public theorem eq_of_mkOne_mul_eq (P : Submonoid S) {c : S} (hc : c ∈ P)
    {u v : LocalizedModule P S}
    (h : LocalizedModule.mk c (1 : P) * u = LocalizedModule.mk c (1 : P) * v) : u = v :=
  (isUnit_mkOne P hc).mul_left_cancel h

/-- In the localization at a submonoid containing `c`, `(c / 1) · (β / c) = β / 1`. -/
public theorem mkOne_mul_mk (P : Submonoid S) (β : S) {c : S} (hc : c ∈ P) :
    LocalizedModule.mk c (1 : P) * LocalizedModule.mk β ⟨c, hc⟩
      = LocalizedModule.mk β (1 : P) := by
  show Localization.mk c (1 : P) * Localization.mk β ⟨c, hc⟩ = Localization.mk β (1 : P)
  rw [Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-! ### The canonical product of two local sections of the twists -/

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The value at a point of the canonical product of two local sections of the absolute twists
is the product of the two local values. -/
public theorem absoluteTwistProduct_apply (i j : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op V)) (b : (twistingSheaf 𝒜 j).val.obj (op V)) (x : V) :
    (absoluteTwistProduct 𝒜 i j V a b).1 x = a.1 x * b.1 x :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul 𝒜 i j V a b x

/-- Two equal sections of a twist have equal values at every point. -/
public theorem twist_val_congr {n : ℤ} {V : Opens (ProjectiveSpectrum.top 𝒜)}
    {s s' : (twistingSheaf 𝒜 n).val.obj (op V)} (h : s = s') (y : V) : s.1 y = s'.1 y := by
  rw [h]

/-! ### The homogeneous sections, restricted to an open -/

/-- The restriction to an open of the global section of `𝒪(k)` attached to a homogeneous
element of degree `k`. -/
public def degreeSectionOn (k : ℕ) {c : S} (hc : c ∈ 𝒜 k)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) : (twistingSheaf 𝒜 (k : ℤ)).val.obj (op V) :=
  (twistingSheaf 𝒜 (k : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
    (degreeSection 𝒜 k ⟨c, hc⟩)

/-- The value of `degreeSectionOn 𝒜 k hc V` at every point is `c / 1`. -/
public theorem degreeSectionOn_apply (k : ℕ) {c : S} (hc : c ∈ 𝒜 k)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (y : V) :
    (degreeSectionOn 𝒜 k hc V).1 y =
      LocalizedModule.mk c (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  degreeSection_apply 𝒜 k ⟨c, hc⟩ ⟨y.1, trivial⟩

/-- Multiplying a section all of whose values are the fraction `β / c` by the homogeneous section
of `c` produces a section all of whose values are `β / 1`. -/
public theorem degreeSectionOn_mul_apply (k : ℕ) {c : S} (hc : c ∈ 𝒜 k) (n : ℤ)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (t : (twistingSheaf 𝒜 n).val.obj (op V)) {β : S}
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩) (y : V) :
    (absoluteTwistProduct 𝒜 (k : ℤ) n V (degreeSectionOn 𝒜 k hc V) t).1 y =
      LocalizedModule.mk β (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  refine Eq.trans (absoluteTwistProduct_apply 𝒜 (k : ℤ) n V (degreeSectionOn 𝒜 k hc V) t y) ?_
  rw [degreeSectionOn_apply 𝒜 k hc V y, hval y]
  exact mkOne_mul_mk _ β (hnv y)

end Stacks.AlgebraicGeometry.TwistRigidity

end
