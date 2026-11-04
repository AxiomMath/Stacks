module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionCoveringTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralChartCoveringFamily

/-!
# Generation over the integral affine trivializing charts trivializes the module

Let `X` be a normal integral algebraic space over a scheme `S` and let `ℒ` be an invertible
`𝒪_X`-module. A meromorphic section of `ℒ` which generates it over **every** étale chart that is
affine, integral and carries a free generator of `ℒ` has trivial Picard class.

This is the junction of the two halves of the geometric claim of Stacks 0EPX that are already
available: the covering family of such charts
(`AlgebraicGeometry.Space.exists_coversTop_isAffine_isIntegral_generator`) and the descent from
generation over a covering family to triviality of the class
(`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_coversTop`). What it leaves is
a statement about a *single* chart, which is the shape the rest of the source's argument — the
identification of the two ratios, followed by algebraic Hartogs
(`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`) — is about.

## Main results

* `AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`:
  generation over every integral affine chart carrying a free generator kills the Picard class.

## References

* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
variable (hintegral : IsIntegralSpace B S hS X)

include hX hnormal hintegral in
/-- **The geometric claim of Stacks 0EPX, reduced to one chart.** On a normal integral algebraic
space `X`, a meromorphic section of an invertible `𝒪_X`-module `ℒ` which generates `ℒ` over every
étale chart that is affine, integral and carries a free generator of `ℒ` has trivial Picard
class.

Those charts cover the final object of the small étale site
(`AlgebraicGeometry.Space.exists_coversTop_isAffine_isIntegral_generator`), and generation over a
covering family trivializes the module
(`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_coversTop`). Neither regularity
of the section nor decency or local Noetherianness of `X` is used here; they enter through the
hypothesis. -/
theorem picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (hgen : ∀ V : SmallEtale B S hS X, IsAffine (chartScheme V) → IsIntegral (chartScheme V) →
      (∃ e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W),
        (∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
            (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
          ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
            Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) →
      GeneratesOnChart B S hS hX L t V) :
    picardClass (B := B) ⟨X, hX⟩ L hL = 0 := by
  obtain ⟨I, Y, hY, hYprop⟩ :=
    exists_coversTop_isAffine_isIntegral_generator B S hS hX hnormal hintegral L hL
  exact picardClass_eq_zero_of_generatesOnChart_coversTop B S hS hX L hL t Y hY
    fun i ↦ hgen (Y i) (hYprop i).1 (hYprop i).2.1 (hYprop i).2.2

end AlgebraicGeometry.Space

end
