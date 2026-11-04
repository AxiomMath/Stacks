module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport

/-!
# Transporting a first Chern class component rule along a closed immersion

Let `p : X ⟶ Y` be a closed immersion of schemes locally of finite type over the base scheme `S`
of chapter 42 of the Stacks Project. An integral closed subscheme `W ⊆ X` of delta-dimension
`k + 1` is isomorphic to its scheme-theoretic image `W.map p ⊆ Y`
(`Stacks.Chow.imageIsoOfIsClosedImmersion`), so a component rule on `Y` can be transported to one
on `X` by pushing its value on `W.map p` forward along the inverse of that isomorphism.

The transported rule is compatible with `p` in the strict, cycle-level sense of
`Stacks.Chow.FirstChernCapCompatibleWithPushforward`, and the verification is pure functoriality
of proper pushforward: the two composites `W ⟶ Y` agree, and a closed immersion over the base has
pushforward weight one.

## Main definitions

* `Stacks.Chow.pullbackComponentRule` — the component rule on `X` transported from one on `Y`.

## Main results

* `Stacks.Chow.firstChernComponentCycleAt_pullbackComponentRule` — the pushforward of the
  transported component cycle at a point is the component cycle at the image point.
* `Stacks.Chow.firstChernCapCompatibleWithPushforward_pullbackComponentRule` — the transported
  rule satisfies the integral-component hypothesis of Stacks 02SU.
* `Stacks.Chow.properChowPushforward_firstChernClassCap_pullbackComponentRule` — the projection
  formula of Stacks 02SU for the transported rule, with the instance of Stacks 02S2 discharged.

## Implementation notes

The identification `closure {p x} = (closure {x}).map p` of integral components is
`Stacks.Chow.integralComponentAt_comp`. Rewriting with it inside
`Stacks.Chow.firstChernComponentCycle` would meet the two proof arguments that the component rule
takes, so the rewrite is performed inside
`Stacks.Chow.IntegralComponentRule.totalize` instead, where the ideal sheaf is the only argument
and the proofs sit under a `dite`.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsClosedImmersion p] (hp : p ≫ sY = sX)
  (k : ℤ)

section Transport

include hp

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The isomorphism of a closed subscheme with its scheme-theoretic image is a morphism over the
base. -/
theorem imageIsoOfIsClosedImmersion_hom_comp_base (W : X.IdealSheafData) :
    (imageIsoOfIsClosedImmersion p W).hom ≫ ((W.map p).subschemeι ≫ sY) =
      W.subschemeι ≫ sX := by
  rw [← Category.assoc, imageIsoOfIsClosedImmersion_hom_subschemeι, Category.assoc, hp]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The inverse of that isomorphism is a morphism over the base. -/
theorem imageIsoOfIsClosedImmersion_inv_comp_base (W : X.IdealSheafData) :
    (imageIsoOfIsClosedImmersion p W).inv ≫ (W.subschemeι ≫ sX) =
      (W.map p).subschemeι ≫ sY := by
  rw [← imageIsoOfIsClosedImmersion_hom_comp_base C sX sY p hp W, Iso.inv_hom_id_assoc]

/-- The scheme-theoretic image under a closed immersion of an integral closed subscheme of
delta-dimension `k + 1` again has delta-dimension `k + 1`: the two are isomorphic over the
base. -/
theorem schemeDeltaDimension_subscheme_map (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    schemeDeltaDimension C ((W.map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) := by
  have _ := hW
  have _ := isIntegral_subscheme_map p W hW
  rwa [schemeDeltaDimension_of_iso C (W.subschemeι ≫ sX) ((W.map p).subschemeι ≫ sY)
    (imageIsoOfIsClosedImmersion p W) (imageIsoOfIsClosedImmersion_hom_comp_base C sX sY p hp W)]

variable (chernY : FirstChernComponentCycleRule C sY k)

/-- **The component rule on `X` transported from a component rule on `Y` along a closed
immersion.** Its value on an integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` is the
pushforward along the inverse of `Stacks.Chow.imageIsoOfIsClosedImmersion` of the value of the
rule on `Y` at the scheme-theoretic image `W.map p`. -/
def pullbackComponentRule : FirstChernComponentCycleRule C sX k := fun W hW hDim =>
  properPushforward C ((W.map p).subschemeι ≫ sY) (W.subschemeι ≫ sX)
    (imageIsoOfIsClosedImmersion p W).inv
    (imageIsoOfIsClosedImmersion_inv_comp_base C sX sY p hp W) k
    (chernY (W.map p) (isIntegral_subscheme_map p W hW)
      (schemeDeltaDimension_subscheme_map C sX sY p hp k W hW hDim))

/-- The component cycle on `X` of the transported rule at an integral closed subscheme is the
pushforward to `X` of the value of the rule on `Y` at the scheme-theoretic image. -/
theorem firstChernComponentCycle_pullbackComponentRule (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentCycle C sX k (pullbackComponentRule C sX sY p hp k chernY) W hW hDim =
      properPushforward C ((W.map p).subschemeι ≫ sY) sX
        ((imageIsoOfIsClosedImmersion p W).inv ≫ W.subschemeι)
        (by rw [Category.assoc, imageIsoOfIsClosedImmersion_inv_comp_base C sX sY p hp W]) k
        (chernY (W.map p) (isIntegral_subscheme_map p W hW)
          (schemeDeltaDimension_subscheme_map C sX sY p hp k W hW hDim)) :=
  congrFun (properPushforward_comp C ((W.map p).subschemeι ≫ sY) (W.subschemeι ≫ sX) sX
    (imageIsoOfIsClosedImmersion p W).inv W.subschemeι
    (imageIsoOfIsClosedImmersion_inv_comp_base C sX sY p hp W) rfl k) _

/-- The component cycle of `chernY` at the image of a point is the component cycle at the
scheme-theoretic image of the integral component of that point. The identification of ideal
sheaves is `Stacks.Chow.integralComponentAt_comp`, applied inside
`Stacks.Chow.IntegralComponentRule.totalize` so that no proof argument has to be transported. -/
theorem firstChernComponentCycleAt_base_eq (chernY' : FirstChernComponentCycleRule C sY k)
    (x : X) (hx : relativeDimension C.dimensionFunction sX x = k + 1) :
    firstChernComponentCycleAt C sY k chernY' (p.base x) =
      firstChernComponentCycle C sY k chernY' ((integralComponentAt x).map p)
        (isIntegral_subscheme_map p _ (isIntegral_integralComponentAt x))
        (schemeDeltaDimension_subscheme_map C sX sY p hp k _
          (isIntegral_integralComponentAt x)
          (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)) := by
  apply Subtype.ext
  show (firstChernCapRule C sY k chernY').totalize (integralComponentAt (p.base x)) = _
  rw [ChernCap42.integralComponentAt_comp p x]
  exact (firstChernCapRule C sY k chernY').totalize_eq _ _ _

/-- **The transported rule is strictly compatible with `p` at every integral component.** The
proper pushforward along `p` of the component cycle of the transported rule at a point of
relative dimension `k + 1` is the component cycle of the original rule at the image point.

Both sides are the pushforward to `Y` of one and the same cycle on the scheme-theoretic image,
along the two factorizations of `W ⟶ Y` through `X` and through `W.map p`. -/
theorem firstChernComponentCycleAt_pullbackComponentRule (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + 1) :
    properPushforward C sX sY p hp k
        (firstChernComponentCycleAt C sX k (pullbackComponentRule C sX sY p hp k chernY) x) =
      firstChernComponentCycleAt C sY k chernY (p.base x) := by
  set W := integralComponentAt x with hWdef
  have hW : IsIntegral W.subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt_of_eq C sX hx
  rw [firstChernComponentCycleAt_eq C sX k (pullbackComponentRule C sX sY p hp k chernY) hx,
    firstChernComponentCycleAt_base_eq C sX sY p hp k chernY x hx,
    firstChernComponentCycle_pullbackComponentRule C sX sY p hp k chernY W hW hDim]
  exact (congrFun (properPushforward_comp C ((W.map p).subschemeι ≫ sY) sX sY
    ((imageIsoOfIsClosedImmersion p W).inv ≫ W.subschemeι) p
    (by rw [Category.assoc, imageIsoOfIsClosedImmersion_inv_comp_base C sX sY p hp W]) hp k)
    _).trans <| congrFun (properPushforward_congr C ((W.map p).subschemeι ≫ sY) sY
    (((imageIsoOfIsClosedImmersion p W).inv ≫ W.subschemeι) ≫ p) (W.map p).subschemeι
    (by rw [Category.assoc, ← imageIsoOfIsClosedImmersion_hom_subschemeι p W,
      Iso.inv_hom_id_assoc]) _ _ k) _

/-- **The integral-component hypothesis of Stacks 02SU for the transported rule.** Along a closed
immersion the pushforward weight is one, so the strict compatibility of the previous result is
exactly `Stacks.Chow.FirstChernCapCompatibleWithPushforward`. -/
theorem firstChernCapCompatibleWithPushforward_pullbackComponentRule :
    FirstChernCapCompatibleWithPushforward C sX sY p hp k
      (pullbackComponentRule C sX sY p hp k chernY) chernY :=
  firstChernCapCompatibleWithPushforward_of_isClosedImmersion C sX sY p hp k
    (pullbackComponentRule C sX sY p hp k chernY) chernY
    fun x hx => firstChernComponentCycleAt_pullbackComponentRule C sX sY p hp k chernY x hx

/-- **The projection formula of Stacks 02SU for the transported rule.** Proper Chow pushforward
along a closed immersion over the base commutes with capping with the first Chern class, when the
rule on the source is the transport of the rule on the target. The instance of Stacks 02S2 that
`Stacks.Chow.properChowPushforward` requires is discharged, `p` being a closed immersion. -/
theorem properChowPushforward_firstChernClassCap_pullbackComponentRule
    (α : CycleGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion p C sX sY hp k)
        (firstChernClassCap C sX k (pullbackComponentRule C sX sY p hp k chernY) α) =
      firstChernClassCap C sY k chernY (properPushforward C sX sY p hp (k + 1) α) :=
  properChowPushforward_firstChernClassCap C sX sY p hp k
    (pullbackComponentRule C sX sY p hp k chernY) chernY _
    (firstChernCapCompatibleWithPushforward_pullbackComponentRule C sX sY p hp k chernY) α

end Transport

end Stacks.Chow

end
