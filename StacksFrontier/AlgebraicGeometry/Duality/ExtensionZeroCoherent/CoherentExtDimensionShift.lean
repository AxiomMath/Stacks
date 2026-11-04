module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtEffacement

/-!
# Dimension shifting for `Ext`-classes between coherent modules

Let `X` be a Noetherian scheme and let `𝓕`, `𝓖` be coherent `𝒪_X`-modules. Every class in
`Ext^{i + 1}_X(𝓕, 𝓖)` is the boundary class of a short exact sequence

`0 ⟶ 𝓕' ⟶ 𝓕'' ⟶ 𝓕 ⟶ 0`

of coherent modules, applied to a class in `Ext^i_X(𝓕', 𝓖)` one degree lower.

This is the dimension-shifting step of the induction on `i` in the proof of the core case of
[Stacks, Tag 0G2H]: the injectivity half of that induction takes a class `ξ` of degree `i + 1`
which vanishes on `U`, produces the surjection `α : 𝓕'' ⟶ 𝓕` effacing it, sets
`𝓕' = ker(α)`, and replaces `ξ` by the class `ξ'` of degree `i` it comes from.

## The two inputs

The surjection is `Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos`, which
effaces a positive-degree class by an epimorphism **whose source is again coherent** — the
library's older effacement comes from an injective resolution and has a source that is not even
quasi-coherent, so it is the wrong kind here. The exactness that converts the vanishing of
`ξ ∘ α` into the existence of `ξ'` is Mathlib's contravariant long exact `Ext`-sequence,
`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃`.

## Main results

* `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos`: **a positive-degree
  `Ext`-class between coherent modules is `hS.extClass ∘ ξ'` for a short exact sequence `S` of
  coherent modules with third term the source of the class.**

## Implementation notes

The sub-object `𝓕'` is modelled by `Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod`, the
subsheaf of `𝓕''` cut out by the vanishing of `α`, rather than by the categorical `kernel`: the
Artin-Rees step that consumes this sequence intersects `𝓕'` with the members `𝓘^n 𝓕''` of the
ideal-power filtration of `𝓕''`, which is a statement about submodules of `𝓕''`. Its coherence
is transported from that of the categorical kernel along
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerIso`, and is returned as part of the existential
so that consumers need not rediscover it: `AlgebraicGeometry.Scheme.Modules` is a `def`, so
instance search does not always find the `SheafOfModules` form of such a fact.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe w u

namespace Stacks.ExtEffacement

variable {X : Scheme.{u}}

/-- **A positive-degree `Ext`-class between coherent modules is a boundary class applied to a
class one degree lower.** For `ξ ∈ Ext^{i + 1}_X(𝓕, 𝓖)` with `𝓕`, `𝓖` coherent on a Noetherian
scheme there are a coherent module `𝓕''`, an epimorphism `α : 𝓕'' ⟶ 𝓕`, and a class
`ξ' ∈ Ext^i_X(ker α, 𝓖)` with `ξ = hS.extClass ∘ ξ'`, where `S` is the short exact sequence
`0 ⟶ ker α ⟶ 𝓕'' ⟶ 𝓕 ⟶ 0` and `ker α` is coherent as well.

This is the dimension-shifting step of the induction on `i` in the proof of the core case of
[Stacks, Tag 0G2H]: `α` is the coherent effacement of `ξ`, so `ξ ∘ α = 0`, and the
contravariant long exact `Ext`-sequence of `S` then exhibits `ξ` as coming from degree `i`. -/
public theorem exists_shortExact_extClass_comp_eq_of_pos [IsNoetherian X]
    [HasExt.{w} X.Modules] {F G : X.Modules} [F.IsCoherent] [G.IsCoherent] {i : ℕ}
    (ξ : Ext.{w} F G (i + 1)) :
    ∃ (E : X.Modules) (p : E ⟶ F) (_ : E.IsCoherent) (_ : Epi p) (_ : (kerMod p).IsCoherent)
      (hS : (ShortComplex.mk (kerInclusion p) p (kerInclusion_comp p)).ShortExact)
      (ξ' : Ext.{w} (kerMod p) G i),
      hS.extClass.comp ξ' (Nat.add_comm 1 i) = ξ := by
  obtain ⟨E, p, hE, hp, hzero⟩ := exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos.{w} ξ
  have := hE
  have := hp
  let := isWeakSerreClass_coherentModules X
  have : (kernel p).IsCoherent := isCoherent_kernel p
  have hker : (kerMod p).IsCoherent :=
    ObjectProperty.prop_of_iso (P := fun M : X.Modules => M.IsCoherent) (kerIso p).symm
      inferInstance
  have hS : (ShortComplex.mk (kerInclusion p) p (kerInclusion_comp p)).ShortExact :=
    ⟨ShortComplex.exact_of_f_is_kernel _ (kerIsLimit p)⟩
  obtain ⟨ξ', hξ'⟩ := Ext.contravariant_sequence_exact₃ hS G ξ hzero (Nat.add_comm 1 i)
  exact ⟨E, p, hE, hp, hker, hS, ξ', hξ'⟩

end Stacks.ExtEffacement

end
