module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import StacksFrontier.Topology.Sheaves.Functors.Module.UnitEndomorphismSections

/-!
# Pullback along the absolute Frobenius raises an automorphism of the structure sheaf to its
# `p`-th power

Let `Z` be a scheme in characteristic `p` and let `F` be its absolute Frobenius, viewed as an
endomorphism of the underlying ringed space. Pulling an automorphism `a` of the structure sheaf
back along `F` and reading the result through the identification `F^* 𝒪_Z ≅ 𝒪_Z` gives the
`p`-fold composite of `a`:

`pullbackUnitAut F a = a ^ p`.

This is the Frobenius half of the classical computation `F^* L ≅ L^{⊗ p}` for an invertible
sheaf `L` in characteristic `p`. On a cover trivializing `L` the two trivializations of `F^* L`
and of `L^{⊗ p}` differ on an overlap by the transition automorphism of the respective sheaf,
and the statement that both transition cocycles are the `p`-th power of that of `L` is the
conjunction of this theorem — for `F^* L` — and
`Stacks.SheafOfModules.TensorPower.trivPow_trans_aut` — for `L^{⊗ p}`. Trivializing the two
sheaves on a common cover is not by itself enough to produce an isomorphism between them; the
agreement of the transition cocycles is the whole content, and this is one of its two halves.

## Main results

* `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius`: **pullback along the absolute Frobenius
  is the `p`-th composite power on automorphisms of the structure sheaf.**
* `AlgebraicGeometry.isInCharacteristic_toScheme`: an open subscheme of a scheme in
  characteristic `p` is in characteristic `p`.
* `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius_opens`: the same formula for the absolute
  Frobenius of an open subscheme — the form in which the Frobenius-side cocycle is read on an
  open of a cover trivializing an invertible sheaf.
* `AlgebraicGeometry.unitAutValue_pullbackUnitAut_absoluteFrobenius`: the formula read as an
  equation between **units of a ring of sections**, which is the spelling in which transition
  data of an invertible sheaf is recorded.

## Implementation notes

The proof is three steps and no induction beyond the one already in
`Stacks.SheafOfModules.unitAut_autPow_val_app_one`. First
`RingedSpaceModuleAdjunction.pullbackUnitAut_eq_iff` transposes the defining square across the
adjunction `F^* ⊣ F_*`, so that only `F^♯` appears; then
`Stacks.SheafOfModules.comm_unitToPushforwardObjUnit_iff` reduces that square to one equation
between values at `1` in a ring of sections; then both sides of that equation are `r ^ p`, on the
left because `Stacks.Frobenius.absoluteFrobenius_app_apply` says `F^♯` is `g ↦ g ^ p`, and on
the right by the composite-power formula. No description of `modulePullback` at a general sheaf
of modules is needed — only at the structure sheaf, where the transposition supplies one.

Both indices in that equation are the *same* open: the absolute Frobenius is the identity on the
underlying space, so `(opensMap F).op.obj U` is `U` by `rfl`
(`Stacks.Frobenius.absoluteFrobenius_preimage`), and the two values at `1` are values of the
same section of the structure sheaf. For an endomorphism moving the opens the statement would
need the restriction of that section as well, which is why the hypothesis is the absolute
Frobenius rather than an arbitrary endomorphism acting by `p`-th powers on functions.

The exponent is pinned by the mathematics, not by the route: see
`AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius_ne_autPow_succ` in
`StacksFrontier/AlgebraicGeometry/Variety/Frobenius/PullbackUnitAutWitness.lean`, which exhibits a
scheme, a prime and a non-identity automorphism for which the same statement with `p + 1` in
place of `p` is false.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **Pullback along the absolute Frobenius of a scheme in characteristic `p` sends an
automorphism of the structure sheaf to its `p`-fold composite power.**

The automorphism is read on both sides as an automorphism of `SheafOfModules.unit` of the
`RingCat`-valued structure sheaf, and the pullback is conjugated by the identification
`F^* 𝒪_Z ≅ 𝒪_Z` of `RingedSpaceModuleAdjunction.pullbackUnitAut`. -/
theorem pullbackUnitAut_absoluteFrobenius (Z : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hZ : IsInCharacteristic Z p)
    (a : SheafOfModules.unit (structureSheafRing Z.toRingedSpace) ≅
      SheafOfModules.unit (structureSheafRing Z.toRingedSpace)) :
    pullbackUnitAut ((absoluteFrobenius Z p hZ).toLRSHom.toShHom) a = a.autPow p := by
  refine (pullbackUnitAut_eq_iff_val_app_one _ a _).2 ?_
  intro U
  refine Eq.trans (absoluteFrobenius_app_apply Z p hZ U.unop _) ?_
  exact (Stacks.SheafOfModules.unitAut_autPow_val_app_one a U _ rfl p).symm

/-- **An open subscheme of a scheme in characteristic `p` is in characteristic `p`**: the
vanishing of `p` on global sections restricts to the open, and the global sections of the open
subscheme are the sections over that open. -/
theorem isInCharacteristic_toScheme {Z : Scheme.{u}} {p : ℕ} (hZ : IsInCharacteristic Z p)
    (U : Z.Opens) : IsInCharacteristic U.toScheme p := by
  simpa only [map_natCast, map_zero] using
    congrArg U.topIso.inv.hom (cast_eq_zero_of_isInCharacteristic hZ U)

/-- **`AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius` for the absolute Frobenius of an open
subscheme.** This is the form the Frobenius-side cocycle computation uses: an invertible sheaf is
trivialized on the opens of a cover, and on each of them the transition automorphism is pulled
back along the Frobenius of that open. -/
theorem pullbackUnitAut_absoluteFrobenius_opens {Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hZ : IsInCharacteristic Z p) (U : Z.Opens)
    (a : SheafOfModules.unit (structureSheafRing U.toScheme.toRingedSpace) ≅
      SheafOfModules.unit (structureSheafRing U.toScheme.toRingedSpace)) :
    pullbackUnitAut
        ((absoluteFrobenius U.toScheme p
          (isInCharacteristic_toScheme hZ U)).toLRSHom.toShHom) a = a.autPow p :=
  pullbackUnitAut_absoluteFrobenius _ p _ a

/-- **The Frobenius power formula in the unit-of-a-ring spelling.** The unit of the ring of
sections attached to `F^* a` is the `p`-th power of the unit attached to `a`. This is the form
the transition-cocycle comparison consumes, since
`Stacks.SheafOfModules.Cocycle.isoOfTransitionEq` records transition data as units of rings of
sections rather than as automorphisms of the free sheaf of rank one. -/
theorem unitAutValue_pullbackUnitAut_absoluteFrobenius (Z : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hZ : IsInCharacteristic Z p)
    (a : SheafOfModules.unit (structureSheafRing Z.toRingedSpace) ≅
      SheafOfModules.unit (structureSheafRing Z.toRingedSpace))
    (U : (Opens Z.carrier)ᵒᵖ) :
    Stacks.SheafOfModules.unitAutValue
        (pullbackUnitAut ((absoluteFrobenius Z p hZ).toLRSHom.toShHom) a) U =
      Stacks.SheafOfModules.unitAutValue a U ^ p :=
  (congrArg (fun e => Stacks.SheafOfModules.unitAutValue e U)
    (pullbackUnitAut_absoluteFrobenius Z p hZ a)).trans
    (Stacks.SheafOfModules.unitAutValue_autPow a U p)

end AlgebraicGeometry

end
