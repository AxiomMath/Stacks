module

public import StacksFrontier.AlgebraicGeometry.DenominatorIdealResidue.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# The denominator ideal of a meromorphic section of an invertible sheaf

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules and `s` a meromorphic section of
`L`.  This file discharges the one remaining hypothesis of
`Stacks.DenominatorIdealResidue.mono_denominatorIdealIncl`, and so proves unconditionally that
the inclusion of the denominator ideal of `s` in the structure sheaf is a monomorphism.

## Main results

* `Stacks.DenominatorIdealInvertible.injective_tmulOne_app_of_trivialization`: on an open set
  over which `L` is trivial, `x ↦ 1 ⊗ x` is injective on sections.
* `Stacks.DenominatorIdealInvertible.injective_tmulOne_app_nhds`: local injectivity of
  `x ↦ 1 ⊗ x` for an invertible `L`, on a neighbourhood basis.
* `Stacks.DenominatorIdealInvertible.denominatorIdeal_inclusion_mono`: the inclusion of the
  denominator ideal in the structure sheaf is a monomorphism.

## Implementation notes

The hypothesis left open by `Stacks.DenominatorIdealResidue` is injectivity of the presheaf-level
map `x ↦ 1 ⊗ x` from `L` to `K_X ⊗_{𝒪_X} L` on the sections over the members of a neighbourhood
basis.  On an open set `V` over which `L` is trivial it is injective outright: a trivialization
supplies an `𝒪_X(V)`-linear isomorphism `θ : L(V) ≃ 𝒪_X(V)`, and the composite

    K_X(V) ⊗_{𝒪_X(V)} L(V) ⟶ K_X(V) ⊗_{𝒪_X(V)} 𝒪_X(V) ≅ K_X(V)

carries `1 ⊗ x` to `θ x • 1`, that is to the image of `θ x` under `𝒪_X(V) ⟶ K_X(V)`.  That ring
map is injective by `AlgebraicGeometry.toTotalQuotientSheaf_app_injective`, so `1 ⊗ x` determines
`θ x` and hence `x`.

The trivializations come from `Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible`,
which is clause 2 of Stacks Tag 0B8M in sectionwise form: it produces an open cover of `X` and
over each member a restriction-compatible family of isomorphisms `L(W) ≃ 𝒪_X(W)` for every open
`W` inside it.  This is what makes the neighbourhood basis available — for a point `p` of an open
`U` one takes `V := U ⊓ W` with `W` a trivializing member containing `p`, and the trivialization
restricts to `V` because it is indexed by maps into `W`.

The formula for `x ↦ 1 ⊗ x` on sections is `Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply`;
  the ambient adjunction's
own unit is opaque (see `Stacks.DenominatorIdealResidue`), which is why the presheaf-level
competitor is the one computed with here.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealResidue

universe w v u

namespace Stacks.DenominatorIdealInvertible

/-! ### The local statement, in the vocabulary of Tag 03CU

The sections of a presheaf of modules indexed by
  `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O` carry their module
structure at the spelling the tensor product of
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` is formed at, which is
why the elementary argument is made here rather than over the structure sheaf of a scheme. -/

section Local

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **The map `x ↦ 1 ⊗ x` is injective on the sections over an object whose module of sections
is free of rank one**, provided the ring map is injective there.  Transporting along the
isomorphism `e : G(V) ≃ 𝒪₁(V)` turns `1 ⊗ x` into `e x • 1`, that is into the image of `e x`
under the ring map, so `1 ⊗ x` determines `e x` and hence `x`. -/
lemma injective_unitApp_of_linearEquiv (θ : O₁ ⟶ O₂) (G :
  Stacks.PresheafOfModules.ChangeOfRings.PMod O₁) (V : Cᵒᵖ)
    (hθ : Function.Injective ((θ.app V).hom))
    (e : (G.obj V : Type w) ≃ₗ[(O₁.obj V : Type w)] (O₁.obj V : Type w)) :
    Function.Injective
      ((Stacks.PresheafOfModules.ChangeOfRings.unitApp θ (𝟙
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G)) V).hom) := by
  let := (θ.app V).hom.toAlgebra
  have halg : Function.Injective (algebraMap (O₁.obj V : Type w) (O₂.obj V : Type w)) := by
    rw [RingHom.algebraMap_toAlgebra]; exact hθ
  have hcollapse : ∀ x : (G.obj V : Type w),
      ((TensorProduct.congr (LinearEquiv.refl (O₁.obj V : Type w) (O₂.obj V : Type w)) e).trans
          (TensorProduct.rid (O₁.obj V : Type w) (O₂.obj V : Type w)))
        ((1 : (O₂.obj V : Type w)) ⊗ₜ[(O₁.obj V : Type w)] x) =
        algebraMap (O₁.obj V : Type w) (O₂.obj V : Type w) (e x) := fun x => by
    rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.rid_tmul,
      Algebra.algebraMap_eq_smul_one, LinearEquiv.refl_apply]
  intro a b hab
  rw [Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply,
    Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply] at hab
  -- The identity morphism's component is the identity map, so `hab` is the equality of
  -- the two pure tensors.
  have hab' : (1 : (O₂.obj V : Type w)) ⊗ₜ[(O₁.obj V : Type w)] a =
      (1 : (O₂.obj V : Type w)) ⊗ₜ[(O₁.obj V : Type w)] b := hab
  refine e.injective (halg ?_)
  rw [← hcollapse a, ← hcollapse b, hab']

end Local

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X))

/-- **On an open set over which `L` is trivial, `x ↦ 1 ⊗ x` is injective on sections.** The
trivialization identifies `L(V)` with `𝒪_X(V)`, and `1 ⊗ x` is then the image of the transported
section under the injective ring map `𝒪_X(V) ⟶ K_X(V)`, which is
`AlgebraicGeometry.toTotalQuotientSheaf_app_injective`. -/
lemma injective_tmulOne_app_of_trivialization {W : Opens X}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val W) (V : Opens X) (h : V ⟶ W) :
    Function.Injective
      (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V)) :=
  injective_unitApp_of_linearEquiv (toK₀ X) L.val (op V)
    (toTotalQuotientSheaf_app_injective X V) (t.θ V h)

/-- **For an invertible `L`, the map `x ↦ 1 ⊗ x` is locally injective.** Every point of every
open set has a trivializing neighbourhood inside it, namely its intersection with a member of a
trivializing cover. -/
lemma injective_tmulOne_app_nhds
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) :
    ∀ (U : Opens X) (p : X), p ∈ U → ∃ V : Opens X, ∃ _ : V ≤ U, p ∈ V ∧
      Function.Injective
        (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V)) := by
  have := hL
  obtain ⟨Y, hY, t⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) (O X).property L
  intro U p hp
  have hptop : p ∈ ⨆ x, Y x := hY ▸ Opens.mem_top p
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hptop
  exact ⟨U ⊓ Y x, inf_le_left, ⟨hp, hx⟩,
    injective_tmulOne_app_of_trivialization X L (t x).some _ (homOfLE inf_le_right)⟩

/-- **The denominator ideal of a meromorphic section of an invertible sheaf embeds in the
structure sheaf.** Stacks Tag 02P0, "inclusion is injective". -/
@[stacks 02P0 "inclusion is injective"]
theorem denominatorIdeal_inclusion_mono (s : MeromorphicSection.{u, u} X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) :
    Mono (denominatorIdealι X L s) :=
  mono_denominatorIdealIncl X L s (injective_tmulOne_app_nhds X L hL)

/-- The canonical morphism `L ⟶ K_X(L)` is a monomorphism for an invertible `L`. -/
theorem mono_toK (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (O X).property L) :
    Mono (toK X L) :=
  Stacks.DenominatorIdealResidue.mono_toK X L (injective_tmulOne_app_nhds X L hL)

end Stacks.DenominatorIdealInvertible

end
