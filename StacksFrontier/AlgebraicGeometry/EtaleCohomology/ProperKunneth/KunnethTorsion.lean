module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.CompositeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.PointProjectionFormulaFiniteCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnbounded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Künneth for a proper factor over a separably closed field, `ℤ/nℤ` coefficients

Let `k` be a separably closed field, `f : X ⟶ Spec k` proper, `g : Y ⟶ Spec k` quasi-compact and
quasi-separated with `cd(g) < ∞`, and `n ≥ 1`. For `E ∈ D(X_étale, ℤ/nℤ)` and
`K ∈ D(Y_étale, ℤ/nℤ)`, unbounded, the Künneth map
`Rf_*E ⊗^L Rg_*K ⟶ Rc_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` of
`Stacks.EtaleCohomology.etaleKunnethCompositeMap` for the fibre square of `X` and `Y` over `k` is
an isomorphism. This is the proof of [Stacks, Tag 0F14] (2), with the finiteness of the
cohomological dimension of `g` ([Stacks, Tag 0F10] for `Y` of finite type over `k`) as the one
remaining input: its three factors are invertible by [Stacks, Tag 0F0C] (proper base change),
the projection formula to the point under `cd(g) < ∞` ([Stacks, Tag 0F12] read on `Y`), and
[Stacks, Tag 0F0G] (the projection formula for the proper `pr₂`).

## Main results

* `isIso_etaleKunnethCompositeMap_zmod_of_etaleCohomologicalDimension_lt_top`: the Künneth map
  for `ℤ/nℤ` coefficients is an isomorphism when `f` is proper and `cd(g) < ∞`.

## References

* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **The Künneth map of a proper factor over a separably closed field is invertible, for `ℤ/nℤ`
coefficients, when the other factor has finite cohomological dimension.** -/
@[sga "4½ Th_finitude 1.11" "Künneth arrow RΓ(X"]
theorem isIso_etaleKunnethCompositeMap_zmod_of_etaleCohomologicalDimension_lt_top (n : ℕ)
    (hn : 0 < n) (k : Type u) [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (g : Y ⟶ Spec (.of k)) [QuasiCompact g]
    [QuasiSeparated g] (hcd : g.etaleCohomologicalDimension < ⊤)
    (E : DerivedCategory (EtaleModules.{u, 0} (ZMod n) X))
    (K : DerivedCategory (EtaleModules.{u, 0} (ZMod n) Y)) :
    IsIso (etaleKunnethCompositeMap.{u, 0} (ZMod n) f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition E K) :=
  have : NeZero n := ⟨hn.ne'⟩
  isIso_etaleKunnethCompositeMap _ _ _ _ _ _ E K
    (isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper (ZMod n)
      ⟨n, hn, ZMod.natCast_self n⟩ f (IsPullback.of_hasPullback f g) E)
    (isIso_etalePushforwardProjectionMap_zmod_of_etaleCohomologicalDimension_lt_top n hn k g hcd
      K _)
    (isIso_etalePushforwardProjectionMap_of_isProper (ZMod n) (fun x => isOfFinAddOrder_of_finite x)
      (pullback.snd f g) _ K)

end Stacks.EtaleCohomology

end
