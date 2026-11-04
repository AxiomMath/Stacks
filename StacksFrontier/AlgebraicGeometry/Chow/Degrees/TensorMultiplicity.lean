module

public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor

/-!
# Tensoring with an invertible module does not change multiplicities

Let `X` be a scheme, let `ℒ` be an invertible `𝒪_X`-module and let `𝒢` be any `𝒪_X`-module. The
stalk of `𝒢 ⊗ ℒ` at a point `x` is `𝒢_x ⊗_{𝒪_{X,x}} ℒ_x` by [Stacks, Tag 01CB], and `ℒ_x` is free
of rank one, so the two stalks have the same length. Hence the multiplicity of
[Stacks, Tag 02QX] is unchanged, and so is the cycle `[𝒢]_k` of a coherent module.

## Main results

* `Stacks.Chow.sheafMultiplicity_tensorModules_of_isInvertible` — the multiplicity of `𝒢 ⊗ ℒ` at
  a point equals the multiplicity of `𝒢` there.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_tensorModules_of_isInvertible` —
  `[𝒢 ⊗ ℒ]_k = [𝒢]_k`.

## Implementation notes

**Two module structures on one stalk.** `Stacks.Chow.sheafMultiplicity` is the length of
`F.presheaf.stalk x` for Mathlib's module structure on the stalk of a presheaf of modules, while
[Stacks, Tag 01CB] — `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` — and the local
basis of an invertible module —
`AlgebraicGeometry.exists_germ_basis_of_isInvertible` — are stated for the structure
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` builds by choosing representatives on a
neighbourhood. The two are equal, by
`Stacks.NonvanishingPullback.stalkModule_eq_scheme`, but not definitionally, and the length depends
on them. The length identity is therefore proved at the structures of Tag 01CB and transported by
the `private` lemma below, whose two module structures are *bound variables* precisely so that
`subst` applies to the equalities — the device of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`, where the same obstruction is
recorded.

**The cycle identity needs no statement about supports.** The coefficient of `[F]_k` at a point of
delta-dimension `k` is the multiplicity there with no side condition
(`Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq`), and at every other
point both coefficients vanish, so the two cycles agree coefficientwise from the multiplicity
identity alone.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- An equality of module structures transports a length identity. This is what crosses between
the module structure of [Stacks, Tag 01CB] on a stalk and Mathlib's, which
`Stacks.Chow.sheafMultiplicity` is stated for; the two are equal, by
`Stacks.NonvanishingPullback.stalkModule_eq_scheme`, but not definitionally so. -/
private theorem length_eq_of_moduleEq {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    {iM jM : Module R M} {iN jN : Module R N} (hM : iM = jM) (hN : iN = jN)
    (h : @Module.length R M _ _ iM = @Module.length R N _ _ iN) :
    @Module.length R M _ _ jM = @Module.length R N _ _ jN := by
  subst hM
  subst hN
  exact h

/-- **Tensoring with an invertible module does not change the multiplicity of a module at a
point.** The stalk of `𝒢 ⊗ ℒ` at `x` is `𝒢_x ⊗_{𝒪_{X,x}} ℒ_x` by [Stacks, Tag 01CB] and `ℒ_x` is
free of rank one, so the two stalks have equal length. -/
theorem sheafMultiplicity_tensorModules_of_isInvertible {X : Scheme.{u}} (G L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (x : X) : sheafMultiplicity (tensorModules G L) x = sheafMultiplicity G x := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  obtain ⟨W, hxW, a, hbasis⟩ := AlgebraicGeometry.exists_germ_basis_of_isInvertible L x
  let iL : Module (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace L.val x) :=
    stalkModule X.toRingedSpace L.val x
  let iG : Module (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace G.val x) :=
    stalkModule X.toRingedSpace G.val x
  let iT : Module (ringStalk X.toRingedSpace x)
      (grpStalk X.toRingedSpace (tensorModules G L).val x) :=
    stalkModule X.toRingedSpace (tensorModules G L).val x
  have hcore : Module.length (ringStalk X.toRingedSpace x)
        (grpStalk X.toRingedSpace (tensorModules G L).val x) =
      Module.length (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace G.val x) :=
    ((tensorStalkIso X.toRingedSpace x G L).trans
      ((TensorProduct.congr (LinearEquiv.refl _ _)
          (LinearEquiv.ofBijective
            (LinearMap.toSpanSingleton (ringStalk X.toRingedSpace x)
              (grpStalk X.toRingedSpace L.val x)
              (grpGerm X.toRingedSpace L.val x W hxW a)) hbasis).symm).trans
        (TensorProduct.rid (ringStalk X.toRingedSpace x)
          (grpStalk X.toRingedSpace G.val x)))).length_eq
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (length_eq_of_moduleEq
    (Stacks.NonvanishingPullback.stalkModule_eq_scheme (tensorModules G L) x)
    (Stacks.NonvanishingPullback.stalkModule_eq_scheme G x) hcore)

/-- **Tensoring with an invertible module does not change the cycle of a coherent module**:
`[𝒢 ⊗ ℒ]_k = [𝒢]_k`. At a point of delta-dimension `k` both coefficients are the multiplicity
there, and those agree by `Stacks.Chow.sheafMultiplicity_tensorModules_of_isInvertible`; at every
other point both vanish. -/
theorem cycleAssociatedToCoherentSheaf_tensorModules_of_isInvertible (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (G L : X.Modules) [G.IsCoherent]
    [(tensorModules G L).IsCoherent]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (k : ℤ)
    (hT : schemeDeltaDimension C ((reducedSupport (tensorModules G L)).subschemeι ≫ f) ≤
      (k : EInt))
    (hG : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ f) ≤ (k : EInt)) :
    cycleAssociatedToCoherentSheaf C f (tensorModules G L) k hT =
      cycleAssociatedToCoherentSheaf C f G k hG := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f _ k hT hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f G k hG hx]
    exact sheafMultiplicity_tensorModules_of_isInvertible G L hL x
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f _ k hT hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f G k hG hx]

end Stacks.Chow

end
