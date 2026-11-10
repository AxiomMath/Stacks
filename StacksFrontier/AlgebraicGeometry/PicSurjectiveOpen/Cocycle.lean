module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.ChartGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator

/-!
# Transporting a unit cocycle from an open subscheme to the ambient scheme

Let `U` be an open of a scheme `X` and let `W : ι → X.Opens` be a family of opens meeting
pairwise inside `U`, that is, `W i ⊓ W j ≤ U` whenever `i ≠ j`. Restriction of functions
`Γ(X, V) ⟶ Γ(U, U.ι ⁻¹ᵁ V)` is an isomorphism for every `V ≤ U`, so a unit transition cocycle
on `U` for the preimages `U.ι ⁻¹ᵁ W i` can be carried back to one on `X` for the `W i`: off the
diagonal the overlap of two charts lies inside `U`, where the transported unit is defined, and
on the diagonal the unit is set to `1`.

This is the gluing half of clause (2) of
[Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA). There `U` is the retrocompact
open of the tag, the charts are `U` itself refined by a trivializing cover together with one
isolating neighbourhood per point of the complement, and the cocycle on `U` is the cocycle of
transition units of the chart generators of an invertible module on `U`. Gluing the transported
cocycle produces an invertible module on `X`, which is the one extending it.

## Main definitions

* `Stacks.PicSurjectiveOpen.invApp`: the inverse of `U.ι.app V` for `V ≤ U`.
* `Stacks.PicSurjectiveOpen.transUnit`: a transition unit of the cocycle on `U`, transported to
  an open of `X` inside `U`.
* `Stacks.PicSurjectiveOpen.transitionX` and `Stacks.PicSurjectiveOpen.cocycleX`: the transported
  cocycle on `X`.

## Main results

* `Stacks.PicSurjectiveOpen.invApp_naturality` and `invApp_naturality_apply`: the transport
  commutes with restriction.
* `Stacks.PicSurjectiveOpen.transUnit_self`, `transUnit_comp`, `transUnit_symm` and
  `transUnit_restrict`: the cocycle laws survive the transport.
* `Stacks.PicSurjectiveOpen.transitionX_of_le`: over an open inside `U` the transition unit of
  the transported cocycle is the transported transition unit, on the diagonal as well.

## Implementation notes

The diagonal is the only case needing the `if`: `W i` itself is not assumed to lie inside `U`,
so `transUnit` is not even defined over all of `W i ⊓ W i`. That `1` is the right value there is
`Stacks.SheafOfModules.UnitTransitionCocycle.transition_self`, which makes
`transitionX_of_le` unconditional on the diagonal and so removes the case split from every
subsequent proof: the three cocycle laws split only on whether the indices involved are equal,
and in each such case one factor is `1`.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.PicSurjectiveOpen

variable {X : Scheme.{u}} {U : X.Opens}

/-- The preimage along `U.ι` is monotone. -/
theorem preimage_mono {V Z : X.Opens} (h : Z ≤ V) : U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ V :=
  ((Opens.map U.ι.base).map (homOfLE h)).le

/-- The map `U.ι.app V` on sections over an open `V ≤ U` is an isomorphism. -/
theorem isIso_ι_app {V : X.Opens} (hV : V ≤ U) : IsIso (U.ι.app V) :=
  U.ι.isIso_app V (hV.trans U.opensRange_ι.ge)

/-- The inverse of the restriction isomorphism on sections over an open inside `U`. -/
noncomputable def invApp {V : X.Opens} (hV : V ≤ U) :
    Γ(U.toScheme, U.ι ⁻¹ᵁ V) ⟶ Γ(X, V) :=
  haveI := isIso_ι_app hV
  inv (U.ι.app V)

/-- `invApp hV` is a left inverse of `U.ι.app V`. -/
theorem app_invApp {V : X.Opens} (hV : V ≤ U) :
    U.ι.app V ≫ invApp hV = 𝟙 _ :=
  have := isIso_ι_app hV
  IsIso.hom_inv_id _

/-- `invApp hV` is a right inverse of `U.ι.app V`. -/
theorem invApp_app {V : X.Opens} (hV : V ≤ U) :
    invApp hV ≫ U.ι.app V = 𝟙 _ :=
  have := isIso_ι_app hV
  IsIso.inv_hom_id _

/-- `invApp` commutes with the restriction maps along `Z ≤ V`. -/
theorem invApp_naturality {V Z : X.Opens} (hV : V ≤ U) (h : Z ≤ V) :
    invApp hV ≫ X.presheaf.map (homOfLE h).op =
      U.toScheme.presheaf.map (homOfLE (preimage_mono (U := U) h)).op ≫
        invApp (h.trans hV) := by
  have := isIso_ι_app hV
  have := isIso_ι_app (h.trans hV)
  rw [← cancel_epi (U.ι.app V), ← Category.assoc, app_invApp, Category.id_comp]
  have hnat := U.ι.naturality (homOfLE h).op
  rw [show ((Opens.map U.ι.base).map (homOfLE h).op.unop).op =
      (homOfLE (preimage_mono (U := U) h)).op from Subsingleton.elim _ _] at hnat
  rw [← Category.assoc, ← hnat, Category.assoc, app_invApp, Category.comp_id]

/-- `invApp` commutes with the restriction maps along `Z ≤ V`, evaluated at a section. -/
theorem invApp_naturality_apply {V Z : X.Opens} (hV : V ≤ U) (h : Z ≤ V)
    (t : Γ(U.toScheme, U.ι ⁻¹ᵁ V)) :
    (X.presheaf.map (homOfLE h).op).hom ((invApp hV).hom t) =
      (invApp (h.trans hV)).hom
        ((U.toScheme.presheaf.map (homOfLE (preimage_mono (U := U) h)).op).hom t) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, invApp_naturality]

section TransUnit

variable {ι : Type u} {W : ι → X.Opens}
  (D : SheafOfModules.UnitTransitionCocycle U.toScheme.toRingedSpace (fun i => U.ι ⁻¹ᵁ W i))

/-- A unit cocycle on `U` for the preimages of the charts, transported to `X`: over an open
inside `U` the restriction map on sections is an isomorphism, and the transition unit is carried
back along its inverse. -/
noncomputable def transUnit (i j : ι) {V : X.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (hVU : V ≤ U) : (Γ(X, V))ˣ :=
  Units.map (invApp hVU).hom.toMonoidHom
    (D.transition i j (U.ι ⁻¹ᵁ V) (preimage_mono hi) (preimage_mono hj))

/-- The transported transition unit from a chart to itself is `1`. -/
theorem transUnit_self (i : ι) {V : X.Opens} (hi hi' : V ≤ W i) (hVU : V ≤ U) :
    transUnit D i i hi hi' hVU = 1 := by
  rw [transUnit, SheafOfModules.UnitTransitionCocycle.transition_self, map_one]

/-- The transported transition units satisfy the cocycle condition. -/
theorem transUnit_comp (i j k : ι) {V : X.Opens} (hi : V ≤ W i) (hj : V ≤ W j) (hk : V ≤ W k)
    (hVU : V ≤ U) :
    transUnit D j k hj hk hVU * transUnit D i j hi hj hVU = transUnit D i k hi hk hVU := by
  rw [transUnit, transUnit, transUnit, ← map_mul,
    D.cocycle i j k (U.ι ⁻¹ᵁ V) (preimage_mono hi) (preimage_mono hj) (preimage_mono hk)]

/-- The transported transition unit from `j` to `i` is the inverse of the one from `i` to `j`. -/
theorem transUnit_symm (i j : ι) {V : X.Opens} (hi : V ≤ W i) (hj : V ≤ W j) (hVU : V ≤ U) :
    transUnit D j i hj hi hVU = (transUnit D i j hi hj hVU)⁻¹ := by
  rw [transUnit, transUnit, D.symm i j (U.ι ⁻¹ᵁ V) (preimage_mono hi) (preimage_mono hj),
    map_inv]

/-- The transported transition units are compatible with restriction to a smaller open. -/
theorem transUnit_restrict (i j : ι) {V Z : X.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (hVU : V ≤ U) (h : Z ≤ V) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (transUnit D i j hi hj hVU) =
      transUnit D i j (h.trans hi) (h.trans hj) (h.trans hVU) := by
  refine Units.ext ?_
  have hD := D.restrict (i := i) (j := j) (preimage_mono hi) (preimage_mono hj)
    (preimage_mono (U := U) h)
  rw [transUnit, transUnit, Units.coe_map, Units.coe_map, ← hD, Units.coe_map, Units.coe_map]
  exact invApp_naturality_apply hVU h _

end TransUnit

section Cocycle

variable {ι : Type u} {W : ι → X.Opens}
  (D : SheafOfModules.UnitTransitionCocycle U.toScheme.toRingedSpace (fun i => U.ι ⁻¹ᵁ W i))
  (hWU : ∀ i j, i ≠ j → W i ⊓ W j ≤ U)

/-- The transition unit on `X`: the transported one off the diagonal, and `1` on it. The
diagonal has to be treated separately because `W i` itself need not be contained in `U`. -/
noncomputable def transitionX (i j : ι) (V : X.Opens) (hi : V ≤ W i) (hj : V ≤ W j) :
    (Γ(X, V))ˣ :=
  letI := Classical.propDecidable (i = j)
  if h : i = j then 1 else transUnit D i j hi hj ((le_inf hi hj).trans (hWU i j h))

/-- Over an open inside `U` the transition unit is the transported one, on the diagonal as
well. -/
theorem transitionX_of_le (i j : ι) (V : X.Opens) (hi : V ≤ W i) (hj : V ≤ W j) (hVU : V ≤ U) :
    transitionX D hWU i j V hi hj = transUnit D i j hi hj hVU := by
  rw [transitionX]
  split
  · subst ‹i = j›
    exact (transUnit_self D i hi hj hVU).symm
  · rfl

/-- The transition unit of `transitionX` from a chart to itself is `1`. -/
theorem transitionX_self (i : ι) (V : X.Opens) (hi hi' : V ≤ W i) :
    transitionX D hWU i i V hi hi' = 1 := by
  rw [transitionX]
  exact dite_eq_left rfl

/-- The cocycle on `X` glued from a unit cocycle on `U` whose charts are the preimages of a
family of opens of `X` meeting pairwise inside `U`. -/
noncomputable def cocycleX : SheafOfModules.UnitTransitionCocycle X.toRingedSpace W where
  transition i j V hi hj := transitionX D hWU i j V hi hj
  restrict {i j V Z} hi hj h := by
    by_cases hij : i = j
    · subst hij
      rw [transitionX_self, transitionX_self, map_one]
    · rw [transitionX_of_le D hWU i j V hi hj ((le_inf hi hj).trans (hWU i j hij)),
        transitionX_of_le D hWU i j Z (h.trans hi) (h.trans hj)
          ((le_inf (h.trans hi) (h.trans hj)).trans (hWU i j hij)),
        transUnit_restrict]
  symm i j V hi hj := by
    by_cases hij : i = j
    · subst hij
      rw [transitionX_self]
      exact inv_one.symm
    · rw [transitionX_of_le D hWU j i V hj hi ((le_inf hi hj).trans (hWU i j hij)),
        transitionX_of_le D hWU i j V hi hj ((le_inf hi hj).trans (hWU i j hij)),
        transUnit_symm]
  cocycle i j k V hi hj hk := by
    by_cases hij : i = j
    · subst hij
      rw [transitionX_self, mul_one]
    · by_cases hjk : j = k
      · subst hjk
        rw [transitionX_self, one_mul]
      · have hVU : V ≤ U := (le_inf hi hj).trans (hWU i j hij)
        rw [transitionX_of_le D hWU i j V hi hj hVU,
          transitionX_of_le D hWU j k V hj hk hVU,
          transitionX_of_le D hWU i k V hi hk hVU, transUnit_comp]

/-- The transition units of `cocycleX` are given by `transitionX`. -/
theorem cocycleX_transition (i j : ι) (V : X.Opens) (hi : V ≤ W i) (hj : V ≤ W j) :
    (cocycleX D hWU).transition i j V hi hj = transitionX D hWU i j V hi hj := rfl

end Cocycle

end Stacks.PicSurjectiveOpen

end
