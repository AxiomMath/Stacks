module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowersRestrict
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.NormalCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DivisorClassFaithful
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalkDepthTwo.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hartogs extension for the reflexive powers

Let `X` be an integral, locally Noetherian, normal scheme and `ℱ` a coherent reflexive
`𝒪_X`-module, with reflexive powers `ℱ^{[n]}`. Every `ℱ^{[n]}` is coherent and reflexive, and is
recovered from its restriction to any open `V ⊆ X` whose complement has codimension at least two:
the canonical map `ℱ^{[n]} ⟶ i_*(ℱ^{[n]}|_V)` is an isomorphism, and restriction
`Γ(W, ℱ^{[n]}) → Γ(V ⊓ W, ℱ^{[n]})` is bijective for every open `W`. Such an open `V` exists on
which moreover `ℱ` is finite locally free.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.isCoherent_reflexivePower'`: every reflexive power of
  a coherent module on a locally Noetherian scheme is coherent, the index `0` included.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isReflexive_reflexivePower`: every reflexive power of
  a coherent reflexive module is reflexive.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isIso_unit_reflexivePower`: **every reflexive power
  is recovered from its restriction to an open whose complement has codimension at least two.**
* `Stacks.AlgebraicGeometry.ReflexivePowers.exists_open_isIso_unit_forall_reflexivePower`: such an
  open exists on which moreover `ℱ` is finite locally free.
* `Stacks.AlgebraicGeometry.ReflexivePowers.bijective_resF_inf_reflexivePower`: the same
  statement read on sections, `Γ(W, ℱ^{[n]}) ≅ Γ(V ⊓ W, ℱ^{[n]})` for every open `W`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull isReflexive_unit)
open Stacks.AlgebraicGeometry.ReflexiveStalkDepthTwo
  (two_le_depth_stalk_of_isCoherent_of_isReflexive)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

variable {X : Scheme.{u}}

/-! ### Coherence and reflexivity of every reflexive power -/

/-- **Every reflexive power of a coherent module on a locally Noetherian scheme is coherent**,
the index `0` included. -/
theorem isCoherent_reflexivePower' [IsLocallyNoetherian X] (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∀ n : ℕ, _root_.SheafOfModules.IsCoherent (reflexivePower F n)
  | 0 => Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  | n + 1 => isCoherent_reflexivePower F hF n

/-- **Every reflexive power of a coherent reflexive module is reflexive.** -/
theorem isReflexive_reflexivePower [IsIntegral X] [IsLocallyNoetherian X] (F : X.Modules)
    (hc : _root_.SheafOfModules.IsCoherent F) (hF : IsReflexive F) :
    ∀ n : ℕ, IsReflexive (reflexivePower F n)
  | 0 => isReflexive_unit X
  | 1 => hF
  | n + 2 =>
      @AlgebraicGeometry.isReflexive_reflexiveHull X _ _ _
        (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F _ hc
          (isCoherent_reflexivePower F hc n))

/-! ### Hartogs extension across a complement of codimension at least two -/

/-- **Every reflexive power is recovered from its restriction to an open whose complement has
codimension at least two**: for a coherent reflexive `ℱ` on an integral, locally Noetherian, normal
scheme, the canonical map `ℱ^{[n]} ⟶ i_*(ℱ^{[n]}|_V)` is an isomorphism. -/
theorem isIso_unit_reflexivePower [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (F : X.Modules) (hc : _root_.SheafOfModules.IsCoherent F) (hF : IsReflexive F) (V : X.Opens)
    (hV : ∀ x : X, x ∉ V →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) (n : ℕ) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
      (reflexivePower F n)) := by
  have : _root_.SheafOfModules.IsCoherent (reflexivePower F n) := isCoherent_reflexivePower' F hc n
  refine isIso_unit_restrict_pushforward_of_depth_ge_two X (reflexivePower F n) V fun x hx => ?_
  exact two_le_depth_stalk_of_isCoherent_of_isReflexive (reflexivePower F n) ‹_›
    (isReflexive_reflexivePower F hc hF n) x
    (two_le_depth_stalk_of_notMem_of_two_le_codimension V hV x hx)

/-- For a coherent reflexive `ℱ` on an integral, locally Noetherian, normal scheme there is an
open `V` whose complement has codimension at least two, on which `ℱ` is finite locally free, and
from whose restrictions all the reflexive powers are recovered. -/
theorem exists_open_isIso_unit_forall_reflexivePower [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) :
    ∃ V : X.Opens,
      (∀ x : X, x ∉ V →
        (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (F.restrict V.ι) ∧
      ∀ n : ℕ, IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        (reflexivePower F n)) := by
  obtain ⟨V, hVcodim, hVfree, -⟩ :=
    ((isReflexive_isTorsionFree_propertyS2_extension_tfae X F).out 1 3).mp hF
  exact ⟨V, hVcodim, hVfree, isIso_unit_reflexivePower F ‹_› hF V hVcodim⟩

/-- **Hartogs extension for the reflexive powers, on sections.**  If the complement of `V` has
codimension at least two, restriction `Γ(W, ℱ^{[n]}) → Γ(V ⊓ W, ℱ^{[n]})` is bijective for every
open `W` and every `n`. -/
@[sga "6 II 2.2.7.2" "more general"]
theorem bijective_resF_inf_reflexivePower [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (F : X.Modules) (hc : _root_.SheafOfModules.IsCoherent F) (hF : IsReflexive F)
    (V : X.Opens)
    (hV : ∀ x : X, x ∉ V →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) (n : ℕ)
    (W : X.Opens) :
    Function.Bijective fun ξ : Γ(reflexivePower F n, W) =>
      Stacks.AlgebraicGeometry.PushforwardRegularity.resF (reflexivePower F n)
        (inf_le_right : V ⊓ W ≤ W) ξ :=
  Stacks.AlgebraicGeometry.PushforwardRegularity.bijective_resF_inf_of_isIso_unit V
    (reflexivePower F n) (isIso_unit_reflexivePower F hc hF V hV n) W

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
