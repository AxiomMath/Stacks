module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicQuotientKer

/-!
# `hquot` for the Stacks 0DZ2 counterexample: `P'/J' = Q'/J'Q'`

Twelfth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`, and the
last of the quotient condition. Layer nine reduced `hquot` for `J' = Y·P'` to the chain
`Q'/(z) ≅ Q₁/(z) ≅ P'/(Y)`, layer ten built the surjection `Q₁ ↠ P'/(Y)` killing the
Artin–Schreier root and layer eleven computed its kernel as `(z)`. This layer does the
localization step and assembles the three into bijectivity of

`Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q') _ : P'/J' → Q'/J'Q'`,

which is `hquot` exactly as `Deformation.FlatModuleLiftBaseChangeStatement` states it.

## The localization step, and why no second quotient is formed

The chain of layer nine reads as two isomorphisms, but forming `Q'/(z)` as a ring and exhibiting
two isomorphisms out of it is more than the statement needs. What `hquot` asks for is bijectivity
of a single map, and for that it is enough to extend layer ten's surjection *past the
localization* and compute its kernel:

`qBaseToQuotOmega : Q' ↠ P'/(Y)`,  `ker = (z)·Q'`.

The extension exists because `z + 1 ↦ 0 + 1 = 1`, a unit, so `IsLocalization.lift` applies — this
is the precise content of "inverting `z + 1` does nothing modulo `z`". The kernel computation
descends from layer eleven's: writing `u ∈ Q'` as `a/s` with `s` a power of `z + 1`, the map
sends `u·s ↦ a` and `s ↦ 1`, so `a` is in layer eleven's kernel `(z)` and `u = a·s⁻¹` is in
`(z)·Q'`.

Bijectivity of `P'/J' → Q'/J'Q'` then needs no further construction. Injectivity is
`Ideal.quotientMap_injective'` applied to `J'Q' = (z)Q' = ker qBaseToQuotOmega`: an element of
`P'` whose image lies in `J'Q'` is killed by `qBaseToQuotOmega`, hence lies in `(Y)`.
Surjectivity is the surjectivity of `qBaseToQuotOmega`, used to correct an arbitrary `q ∈ Q'` by
an element of `P'` up to its kernel.

The negative result of layer ten still applies and should not be re-searched:
`AdjoinRoot.quotMapOfEquivQuotMapCMapMk` and the `quotAdjoinRootEquivQuotPolynomialQuot` family
describe `AdjoinRoot f` modulo an ideal **mapped up from the base**, which neither step of the
chain is.

## Main definitions

* `Deformation.Examples.ArtinSchreier.qBaseToQuotOmega`: the surjection `Q' ↠ P'/(Y)`, layer
  ten's map extended across the localization at `z + 1`.

## Main results

* `Deformation.Examples.ArtinSchreier.ker_qBaseToQuotOmega`: its kernel is `z·Q'`.
* `Deformation.Examples.ArtinSchreier.bijective_quotientMap_omegaP`: **`hquot` of Stacks 0DZ2**
  for `J' = Y·P'`, in the `Ideal.quotientMap` shape the statement uses.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The surjection `Q' ↠ P'/(Y)` -/

/-- `z + 1` goes to `1` under `Q₁ ↠ P'/(Y)`, because the map kills `z`. This is why inverting
`z + 1` does nothing modulo `z`, and it is the side condition of the extension below. -/
theorem qOneToQuotOmega_zRoot_add_one : qOneToQuotOmega (zRoot + 1) = 1 := by
  rw [map_add, map_one, qOneToQuotOmega_root, zero_add]

/-- **The surjection `Q' ↠ P'/(Y)`**, layer ten's `qOneToQuotOmega` extended across the
localization `Q' = (Q₁)_{z+1}`. The extension exists because `z + 1` goes to the unit `1`. -/
def qBaseToQuotOmega : QBase →+* (PBase ⧸ Ideal.span {omegaP}) :=
  IsLocalization.lift (M := Submonoid.powers (zRoot + 1)) (g := qOneToQuotOmega) (by
    intro y
    obtain ⟨k, hk⟩ := y.2
    rw [← hk, map_pow, qOneToQuotOmega_zRoot_add_one, one_pow]
    exact isUnit_one)

/-- The extension restricts to layer ten's map on `Q₁`. -/
theorem qBaseToQuotOmega_algebraMap_QOne (b : QOne) :
    qBaseToQuotOmega (algebraMap QOne QBase b) = qOneToQuotOmega b :=
  IsLocalization.lift_eq _ b

/-- The extension restricts to the quotient map on `P'`, so `P'/(Y)` is a quotient of `Q'` as a
`P'`-algebra. -/
theorem qBaseToQuotOmega_algebraMap (p : PBase) :
    qBaseToQuotOmega (algebraMap PBase QBase p) =
      Ideal.Quotient.mk (Ideal.span {omegaP}) p := by
  rw [IsScalarTower.algebraMap_apply PBase QOne QBase p, qBaseToQuotOmega_algebraMap_QOne,
    qOneToQuotOmega_algebraMap]

/-- The extension kills `z`. -/
theorem qBaseToQuotOmega_zQ : qBaseToQuotOmega zQ = 0 := by
  rw [zQ, qBaseToQuotOmega_algebraMap_QOne, qOneToQuotOmega_root]

/-- **The extension is surjective**, because it splits the structure map `P' → Q'`. -/
theorem surjective_qBaseToQuotOmega : Function.Surjective qBaseToQuotOmega := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap PBase QBase p, qBaseToQuotOmega_algebraMap p⟩

/-! ### Its kernel is `z·Q'` -/

/-- **The kernel of `Q' ↠ P'/(Y)` is `z·Q'`.** Write `u ∈ Q'` as `a/s` with `s` a power of
`z + 1`; the map sends `s` to `1`, so it sends `u·s` to the image of `a`, which is therefore
zero. Layer eleven's `ker_qOneToQuotOmega` puts `a` in `z·Q₁`, and dividing by the unit `s`
puts `u` in `z·Q'`. -/
theorem ker_qBaseToQuotOmega : RingHom.ker qBaseToQuotOmega = Ideal.span {zQ} := by
  refine le_antisymm ?_ ?_
  · intro u hu
    rw [RingHom.mem_ker] at hu
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := Submonoid.powers (zRoot + 1)) u
    have ha : qOneToQuotOmega a = 0 := by
      have hcong := congrArg qBaseToQuotOmega hs
      rw [map_mul, hu, zero_mul, qBaseToQuotOmega_algebraMap_QOne] at hcong
      exact hcong.symm
    rw [← RingHom.mem_ker, ker_qOneToQuotOmega, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨v, hv⟩ :=
      (IsLocalization.map_units (M := Submonoid.powers (zRoot + 1)) QBase s).exists_right_inv
    refine Ideal.mem_span_singleton.2 ⟨algebraMap QOne QBase c * v, ?_⟩
    have hz : algebraMap QOne QBase (zRoot * c) = zQ * algebraMap QOne QBase c := by
      rw [map_mul]
      rfl
    rw [hz] at hs
    calc u = u * (algebraMap QOne QBase (s : QOne) * v) := by rw [hv, mul_one]
      _ = (u * algebraMap QOne QBase (s : QOne)) * v := by ring
      _ = zQ * (algebraMap QOne QBase c * v) := by rw [hs]; ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact qBaseToQuotOmega_zQ

/-! ### `hquot` -/

/-- **`hquot` of Stacks 0DZ2 for the counterexample**: the canonical map `P'/J' → Q'/J'Q'` is
bijective for `J' = Y·P'`.

Injectivity is `Ideal.quotientMap_injective'`: by `map_span_omegaP` the ideal `J'Q'` is `z·Q'`,
which `ker_qBaseToQuotOmega` identifies with the kernel of `Q' ↠ P'/(Y)`, so an element of `P'`
landing in `J'Q'` is killed by that map and hence lies in `(Y)`. Surjectivity corrects an
arbitrary `q ∈ Q'` by the element of `P'` that `surjective_qBaseToQuotOmega` provides: the
difference is in the kernel, i.e. in `J'Q'`. -/
theorem bijective_quotientMap_omegaP :
    Function.Bijective (Ideal.quotientMap
      ((Ideal.span {omegaP}).map (algebraMap PBase QBase)) (algebraMap PBase QBase)
      Ideal.le_comap_map) := by
  have hker : (Ideal.span {omegaP}).map (algebraMap PBase QBase) =
      RingHom.ker qBaseToQuotOmega := by
    rw [map_span_omegaP, ker_qBaseToQuotOmega]
  constructor
  · refine Ideal.quotientMap_injective' fun p hp ↦ ?_
    rwa [Ideal.mem_comap, hker, RingHom.mem_ker, qBaseToQuotOmega_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem] at hp
  · intro y
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (qBaseToQuotOmega q)
    refine ⟨Ideal.Quotient.mk (Ideal.span {omegaP}) p, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hker, RingHom.mem_ker, map_sub,
      qBaseToQuotOmega_algebraMap, hp, sub_self]

end Deformation.Examples.ArtinSchreier

end
