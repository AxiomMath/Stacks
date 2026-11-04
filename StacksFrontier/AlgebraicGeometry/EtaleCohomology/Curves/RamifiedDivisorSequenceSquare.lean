module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RamifiedDivisorSquare

/-!
# The third square of the divisor sequences along a ramified morphism

Let `π : X ⟶ Y` be a flat morphism of integral normal schemes and `F` a family of finite sets of
closed points of `X`, the member at a closed point `y` of `Y` being the whole fibre of `π` above
`y`. The ramification-weighted third component
`Stacks.EtaleCohomology.ramifiedClosedPointDivisorDirectImageMap` reads on families of sections of
the summands as `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum`. This file shows that map
carries the family of orders of vanishing of an invertible function on the generic fibre of an
étale `Y`-scheme to the family of orders of vanishing of its restriction to the generic fibre of
the base change, globalises that to the commutation of the third square of the divisor sequences,
and assembles the morphism of divisor sequences along `π` for smooth curves.

With `F` only required to consist of points above `y`, the square is false: at a closed point `x`
of `X` outside `F (π x)` the weighted map contributes nothing while the divisor of the restricted
function at `x` need not vanish. What makes it true is that `F y` is the *whole* fibre, which is
what `Stacks.EtaleCohomology.closedPointFibreFinset` is, and that `π` carries closed points to
closed points and preserves codimension.

## Main definitions

* `Stacks.EtaleCohomology.divisorSequenceRamifiedHom`: **the morphism from the divisor sequence of
  `Y` to the direct image along `π` of the divisor sequence of `X`**, for `π` a flat quasi-compact
  morphism of smooth curves over an algebraically closed field.

## Main results

* `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum_apply`: **the weighted map on families of
  sections, read at one closed point of `X`.** The double sum over the closed points of `Y` and
  over the fibres collapses to the single term indexed by the image of that closed point.
* `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum_closedPointDivisorSections`: **the weighted
  map carries the divisor of an invertible function on the generic fibre to the divisor of its
  restriction.**
* `Stacks.EtaleCohomology.divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap`:
  **the third square of the divisor sequences along `π` commutes**, over the whole small étale
  site of `Y`.

## Implementation notes

The index type of the source of `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum` is the
closed points of `Y`, and its summand at `y` is spelt `closedPointSkyscraper Y y`, whereas
`Stacks.EtaleCohomology.closedPointDivisorSections` produces a family whose summand at `y` is
spelt `integerSkyscraper Y y.1`. The two agree by unfolding a definition but not as terms, so the
`DFinsupp` lemmas that evaluate a `DirectSum.toAddMonoid` do not apply to the composite directly.
`Stacks.EtaleCohomology.ramifiedDirectImageDirectSum_apply` is therefore stated and proved for a
family in the first spelling, by induction on the family rather than through
`DFinsupp.sumAddHom_apply`, and only then applied to a family in the second. For the same reason
the proof of `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum_closedPointDivisorSections`
chains its steps with `Eq.trans` and `congrArg`, which compare the two spellings up to unfolding,
rather than with `rw`, whose keyed matching does not see through the definition.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the divisor sequence
  whose third term the weighted map compares.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the divisor sequence of a
  smooth curve, whose morphism along `π` is assembled here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order IsLocalRing TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Sections

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]
  [AlgebraicGeometry.IsIntegral Y] [IsNormal Y] (π : X ⟶ Y) [Flat π]

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

omit [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsNormal X]
  [AlgebraicGeometry.IsIntegral Y] [AlgebraicGeometry.IsNormal Y] [Flat π] in
/-- **The weighted third component on families of sections, read at one closed point of `X`.**

The double sum defining `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum` — over the closed
points `y` of `Y` carrying a nonzero section, and over the fibre `F y` — contributes at a closed
point `x` of `X` only through the member indexed by `x` of the fibre above `τ x`: the fibres are
the whole fibres, so `x` belongs to `F (τ x)` and to no other member of the family. -/
theorem ramifiedDirectImageDirectSum_apply (U : Y.Etale)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1)
    (f : DirectSum ↥(closedPoints Y)
      fun y : closedPoints Y ↦ (closedPointSkyscraper.{u, v} Y y).obj.obj (op U))
    (x : closedPoints X) :
    ramifiedDirectImageDirectSum.{u, v} π U F hF f x =
      (π.ramificationLength x.1 : ℤ) •
        ramifiedSummandMap.{u, v} π U x (τ x) (hτ x) (f (τ x)) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let : DecidableEq ↥(closedPoints Y) := Classical.decEq _
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, smul_zero]
  | add g₁ g₂ h₁ h₂ =>
    rw [map_add, DFinsupp.add_apply, h₁, h₂, DFinsupp.add_apply, map_add, smul_add]
  | of y t =>
    have hofs : ramifiedDirectImageDirectSum.{u, v} π U F hF (DirectSum.of _ y t) =
        ∑ z ∈ (F y).attach, DirectSum.of _ z.1
          ((π.ramificationLength z.1.1 : ℤ) •
            ramifiedSummandMap.{u, v} π U z.1 y (hF y z.1 z.2) t) := by
      rw [ramifiedDirectImageDirectSum, DirectSum.toAddMonoid_of, AddMonoidHom.finsetSum_apply]
      exact Finset.sum_congr rfl fun z _ => rfl
    rw [hofs, DirectSum.sum_apply]
    by_cases hy : τ x = y
    · subst hy
      have hx : x ∈ F (τ x) := hFfull (τ x) x (hτ x)
      refine (Finset.sum_eq_single_of_mem (⟨x, hx⟩ : ↥(F (τ x))) (Finset.mem_attach _ _)
        (fun z _ hz => DirectSum.of_eq_of_ne z.1 x _ fun h =>
          hz (Subtype.ext h.symm))).trans ?_
      refine (DirectSum.of_eq_same x _).trans ?_
      rw [DirectSum.of_eq_same]
    · have hzero : (DirectSum.of (fun y : closedPoints Y ↦
          ToType ((closedPointSkyscraper.{u, v} Y y).obj.obj (op U))) y t) (τ x) = 0 :=
        DirectSum.of_eq_of_ne _ _ _ hy
      rw [Finset.sum_eq_zero fun z _ => DirectSum.of_eq_of_ne z.1 x _ fun h => hy
        (Subtype.ext ((hτ x).symm.trans ((congrArg (fun w : closedPoints X => π.base w.1)
          h).trans (hF y z.1 z.2)))), hzero, map_zero, smul_zero]

omit [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsNormal X] [Flat π] in
/-- **The weighted third component carries the divisor of an invertible function on the generic
fibre to the divisor of its restriction.** This is the third square of the morphism of divisor
sequences along `π`, read on the families of sections of the summands over an étale `Y`-scheme
with Noetherian space.

The weight at a closed point `x` of `X` is the local multiplicity of `π` at `x`, and the single
summand of `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum_apply` is matched with the
divisor upstairs by
`Stacks.EtaleCohomology.integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint_ramified`.
-/
theorem ramifiedSummandMap_integerSkyscraperDivisorOfPoint (U : Y.Etale)
    [IsLocallyNoetherian U.left] (x : closedPoints X) (y : closedPoints Y)
    (hxy : π.base x.1 = y.1)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ)) :
    ramifiedSummandMap.{u, v} π U x y hxy
        (integerSkyscraperDivisorOfPoint.{u, v} U y.1 a) =
      ((integerSkyscraperDirectImageMap.{u, v} π x.1).hom.app (op U)).hom
        (integerSkyscraperDivisorOfPoint.{u, v} U (π.base x.1) a) :=
  congrArg (fun s => ((integerSkyscraperDirectImageMap.{u, v} π x.1).hom.app (op U)).hom s)
    (eqToHom_app_integerSkyscraperDivisorOfPoint (U := U) (h := hxy.symm) (E := _) (a := a))

/-- **The weighted map carries the divisor of an invertible function on the generic fibre to the
divisor of its restriction.** For `U` an étale `Y`-scheme with Noetherian space whose base change
along `π` also has Noetherian space, and `F y` the whole fibre of `π` above each closed point `y`,
the ramification-weighted map sends the family of orders of vanishing of an invertible function
`a` on the generic fibre of `U` to the family of orders of vanishing of its restriction to the
generic fibre of the base change. -/
theorem ramifiedDirectImageDirectSum_closedPointDivisorSections
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x) (U : Y.Etale)
    [IsLocallyNoetherian U.left] [NoetherianSpace U.left]
    [IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left]
    [NoetherianSpace ((smallEtaleBaseChange π).obj U).left]
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1)
    (a : (Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ) :
    ramifiedDirectImageDirectSum.{u, v} π U F hF
        (closedPointDivisorSections.{u, v} U (Additive.ofMul a)) =
      closedPointDivisorSections.{u, v} ((smallEtaleBaseChange π).obj U)
        (Additive.ofMul (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a)) := by
  refine DFinsupp.ext fun x => ?_
  refine (ramifiedDirectImageDirectSum_apply.{u, v} π U F hF hFfull τ hτ
    (closedPointDivisorSections.{u, v} U (Additive.ofMul a)) x).trans ?_
  refine Eq.trans ?_ (closedPointDivisorSections_apply.{u, v}
    ((smallEtaleBaseChange π).obj U) (Additive.ofMul
      (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a)) x).symm
  refine Eq.trans ?_
    (integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint_ramified.{u, v} π hcoh U x.1 a)
  refine congrArg (fun s => (π.ramificationLength x.1 : ℤ) • s) ?_
  refine Eq.trans ?_ (ramifiedSummandMap_integerSkyscraperDivisorOfPoint.{u, v} π U x (τ x) (hτ x)
    (Additive.ofMul a))
  exact congrArg (fun s => ramifiedSummandMap.{u, v} π U x (τ x) (hτ x) s)
    (closedPointDivisorSections_apply.{u, v} U (Additive.ofMul a) (τ x))

end Sections

/-! ### The third square of the divisor sequences -/

section Square

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
  (π : X ⟶ Y) [Flat π] [QuasiCompact π]

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- The second map of the divisor sequence, on the class of a unit of the generic fibre, is the
section of the divisor sheaf attached to the family of orders of vanishing. -/
private theorem divisorSequenceSecondMap_app_ofUnit {Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Z] [IsNormal Z] [IsLocallyNoetherian Z] (V : Z.Etale)
    [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (a : (Γ(pullback V.hom (genericPointInclusion Z), ⊤))ˣ) :
    ((divisorSequenceSecondMap.{u, v} Z).hom.app (op V)).hom
        (Stacks.Kummer.ofUnit (U := (smallEtaleBaseChange (genericPointInclusion Z)).obj V) a) =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} Z V
        (closedPointDivisorSections.{u, v} V (Additive.ofMul a)) :=
  (divisorSequenceSecondMap_app_of_noetherianSpace.{u, v} V
    (Stacks.Kummer.ofUnit (U := (smallEtaleBaseChange (genericPointInclusion Z)).obj V) a)).trans
    (closedPointDivisorSheafSection_apply V (Additive.ofMul a))

omit [QuasiCompact π] in
/-- **The third square on sections, pointwise**: over an étale `Y`-scheme `U` with Noetherian
space, the divisor of an invertible function on the generic fibre of `U`, carried to `X` with the
ramification weights, is the divisor of its restriction to the generic fibre of `U ×_Y X`. -/
theorem ramifiedClosedPointDivisorDirectImageMap_divisorSequenceSecondMap_apply
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1)
    (U : Y.Etale) [NoetherianSpace U.left]
    [NoetherianSpace ((smallEtaleBaseChange π).obj U).left]
    (a : (Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ) :
    ((ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF).hom.app (op U)).hom
        (((divisorSequenceSecondMap.{u, v} Y).hom.app (op U)).hom (Stacks.Kummer.ofUnit a)) =
      ((divisorSequenceSecondMap.{u, v} X).hom.app
          (op ((smallEtaleBaseChange π).obj U))).hom
        (((multiplicativeDirectImageSquareMap.{u, v}
          (genericPointSquare_ramified π)).hom.app (op U)).hom (Stacks.Kummer.ofUnit a)) := by
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left Y U
  have : IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left :=
    isLocallyNoetherian_etale_left X _
  have h3 := ramifiedClosedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum.{u, v} π U F hF
    (closedPointDivisorSections.{u, v} U (Additive.ofMul a))
  have h4 := ramifiedDirectImageDirectSum_closedPointDivisorSections.{u, v} π hcoh U F hF hFfull
    τ hτ a
  have h5 : ((multiplicativeDirectImageSquareMap.{u, v}
        (genericPointSquare_ramified π)).hom.app (op U)).hom (Stacks.Kummer.ofUnit a) =
      Stacks.Kummer.ofUnit (U := (smallEtaleBaseChange (genericPointInclusion X)).obj
        ((smallEtaleBaseChange π).obj U))
        (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a) :=
    multiplicativeDirectImageSquareMap_app_ofUnit _ U a
  rw [divisorSequenceSecondMap_app_ofUnit.{u, v} U a, h3, h4, h5,
    divisorSequenceSecondMap_app_ofUnit.{u, v} ((smallEtaleBaseChange π).obj U)]

/-- **The third commuting square at an affine étale `Y`-scheme.** -/
theorem divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap_app
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1)
    (W : Y.AffineEtale) :
    (divisorSequenceSecondMap.{u, v} Y ≫
        ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF).hom.app
        (op ((Scheme.AffineEtale.Spec Y).obj W)) =
      (multiplicativeDirectImageSquareMap.{u, v} (genericPointSquare_ramified π) ≫
        (etaleAbelianDirectImage.{u, v} π).map (divisorSequenceSecondMap.{u, v} X)).hom.app
        (op ((Scheme.AffineEtale.Spec Y).obj W)) := by
  have : NoetherianSpace ((Scheme.AffineEtale.Spec Y).obj W).left :=
    noetherianSpace_affineEtale_left Y W
  have : CompactSpace ((Scheme.AffineEtale.Spec Y).obj W).left :=
    inferInstanceAs (CompactSpace (Scheme.Spec.obj W.left))
  have : NoetherianSpace ((smallEtaleBaseChange π).obj
      ((Scheme.AffineEtale.Spec Y).obj W)).left := by
    have : IsLocallyNoetherian ((smallEtaleBaseChange π).obj
      ((Scheme.AffineEtale.Spec Y).obj W)).left := isLocallyNoetherian_etale_left X _
    have : @QuasiCompact _ ((Functor.fromPUnit Y).obj ((Scheme.AffineEtale.Spec Y).obj W).right)
      π := inferInstanceAs (QuasiCompact π)
    have : @QuasiCompact ((smallEtaleBaseChange π).obj ((Scheme.AffineEtale.Spec Y).obj W)).left
        ((Scheme.AffineEtale.Spec Y).obj W).left
        (pullback.fst ((Scheme.AffineEtale.Spec Y).obj W).hom π) :=
      inferInstanceAs (QuasiCompact (pullback.fst ((Scheme.AffineEtale.Spec Y).obj W).hom π))
    have : CompactSpace ((𝟭 Scheme).obj ((Scheme.AffineEtale.Spec Y).obj W).left) :=
      inferInstanceAs (CompactSpace ((Scheme.AffineEtale.Spec Y).obj W).left)
    have : CompactSpace ((smallEtaleBaseChange π).obj
        ((Scheme.AffineEtale.Spec Y).obj W)).left :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.fst ((Scheme.AffineEtale.Spec Y).obj W).hom π)
    have : AlgebraicGeometry.IsNoetherian ((smallEtaleBaseChange π).obj
      ((Scheme.AffineEtale.Spec Y).obj W)).left := ⟨⟩
    infer_instance
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
  obtain ⟨b, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} z
  exact ramifiedClosedPointDivisorDirectImageMap_divisorSequenceSecondMap_apply.{u, v} π hcoh F hF
    hFfull τ hτ _ b

/-- **The third commuting square of the divisor-sequence comparison along a ramified morphism**:
the second map of the divisor sequence of `Y` followed by the ramification-weighted third
component equals the restriction of invertible functions to the generic fibre of the base change
followed by the direct image of the second map of the divisor sequence of `X`.

The pointwise identity holds over an étale `Y`-scheme with Noetherian space, which the affine ones
are; they are cover-dense in the small étale site, so the two morphisms of sheaves agree. -/
theorem divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1) :
    divisorSequenceSecondMap.{u, v} Y ≫ ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF =
      multiplicativeDirectImageSquareMap.{u, v} (genericPointSquare_ramified π) ≫
        (etaleAbelianDirectImage.{u, v} π).map (divisorSequenceSecondMap.{u, v} X) :=
  Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (G := Scheme.AffineEtale.Spec Y)
    (K := Y.smallEtaleTopology)).symm.injective
      (NatTrans.ext (funext fun W =>
        divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap_app.{u, v} π hcoh F
          hF hFfull τ hτ W.unop)))

end Square

/-! ### The morphism of divisor sequences -/

section Hom

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [Smooth gX] [IsCurve k gY] [Smooth gY] (π : X ⟶ Y)
  [Flat π] [QuasiCompact π]

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The morphism from the divisor sequence of `Y` to the direct image along `π` of that of
`X`**: restriction of invertible functions to `U ×_Y X` and to its generic fibre, and on divisors
the ramification-weighted map sending the summand at a closed point `y` of `Y` to the weighted sum
over the fibre above `y`.

The first square is
`multiplicativeDirectImageComparison_comp_multiplicativeDirectImageSquareMap` and the second is
`divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap`. -/
def divisorSequenceRamifiedHom (hcoh : ∀ x : X, coheight (π.base x) = coheight x)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (hFfull : ∀ (y : closedPoints Y) (x : closedPoints X), π.base x.1 = y.1 → x ∈ F y)
    (τ : closedPoints X → closedPoints Y) (hτ : ∀ x : closedPoints X, π.base x.1 = (τ x).1) :
    divisorSequence gY ⟶ (divisorSequence gX).map (etaleAbelianDirectImage.{u, u + 1} π) :=
  haveI : IsNormal X := isNormal_of_isCurve_of_smooth gX
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve gX
  haveI : IsNormal Y := isNormal_of_isCurve_of_smooth gY
  haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isCurve gY
  { τ₁ := multiplicativeDirectImageComparison.{u, u + 1} π
    τ₂ := multiplicativeDirectImageSquareMap.{u, u + 1} (genericPointSquare_ramified π)
    τ₃ := ramifiedClosedPointDivisorDirectImageMap.{u, u + 1} π F hF
    comm₁₂ := multiplicativeDirectImageComparison_comp_multiplicativeDirectImageSquareMap.{u, u + 1}
      (genericPointSquare_ramified π)
    comm₂₃ := (divisorSequenceSecondMap_comp_ramifiedClosedPointDivisorDirectImageMap.{u, u + 1}
      π hcoh F hF hFfull τ hτ).symm }

end Hom

end Stacks.EtaleCohomology

end
