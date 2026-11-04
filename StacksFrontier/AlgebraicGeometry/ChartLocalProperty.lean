module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Transferring Zariski-local properties along a chartwise description of a morphism

Let `Uo` be an open subscheme of a scheme `Z`, let `f : V ⟶ Uo` be a morphism of schemes and
let `a : A ⟶ Z` be a second morphism. Suppose `Uo` is covered by opens `Ω i` of `Z` and that
for each `i` the scheme `a ⁻¹ᵁ Ω i` is a fibre product of `f ≫ Uo.ι : V ⟶ Z` with `Ω i ⟶ Z`.
Then, chart by chart, `f` looks like a restriction of `a`, so `f` inherits every property of
`a` that is Zariski-local at the target and stable under base change.

## Main results

* `Stacks.ChartLocalProperty.of_charts`: the transfer statement for an arbitrary morphism
  property that is Zariski-local at the target and stable under base change.
* `Stacks.ChartLocalProperty.isIntegralHom_of_charts`: the special case of integral morphisms.
* `Stacks.ChartLocalProperty.surjective_of_charts`: the special case of surjective morphisms.

## Implementation notes

The hypothesis is phrased with `CategoryTheory.IsPullback (a ∣_ Ω i) (κ i) (Ω i).ι (f ≫ Uo.ι)`,
i.e. `a ⁻¹ᵁ Ω i` is presented as the fibre product of `f ≫ Uo.ι` and `(Ω i).ι` with the
restriction of `a` as the projection to `Ω i`.
-/

@[expose] public section

namespace Stacks.ChartLocalProperty

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

variable {Z : Scheme.{u}} {Uo : Z.Opens}

/-- Restricting the inclusion of an open subscheme `Uo` along an open `Ω ≤ Uo` of the ambient
scheme agrees with the canonical isomorphism `Scheme.Opens.isoOfLE`. -/
lemma morphismRestrict_ι_eq_isoOfLE {Ω : Z.Opens} (hΩ : Ω ≤ Uo) :
    Uo.ι ∣_ Ω = (Scheme.Opens.isoOfLE hΩ).hom := by
  rw [← cancel_mono Ω.ι, morphismRestrict_ι, Scheme.Opens.isoOfLE_hom_ι]

/-- Restricting the inclusion of an open subscheme `Uo` along an open `Ω ≤ Uo` of the ambient
scheme is an isomorphism. -/
lemma isIso_morphismRestrict_ι {Ω : Z.Opens} (hΩ : Ω ≤ Uo) : IsIso (Uo.ι ∣_ Ω) := by
  rw [morphismRestrict_ι_eq_isoOfLE hΩ]
  infer_instance

/-- Opens of the ambient scheme covering `Uo` pull back to a cover of the open subscheme `Uo`. -/
lemma iSup_ι_preimage_eq_top {ι : Type*} (Ω : ι → Z.Opens) (hΩ : ⨆ i, Ω i = Uo) :
    ⨆ i, Uo.ι ⁻¹ᵁ Ω i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hΩ, Scheme.Opens.ι_preimage_self]

/-- **Chartwise transfer of Zariski-local properties.** Let `f : V ⟶ Uo` be a morphism into an
open subscheme of `Z`, let `a : A ⟶ Z`, and let the opens `Ω i` of `Z` cover `Uo`. If for each
`i` the open subscheme `a ⁻¹ᵁ Ω i` of `A`, together with the restriction `a ∣_ Ω i` and a
morphism `κ i` to `V`, is a fibre product of `f ≫ Uo.ι` and `(Ω i).ι`, then `f` satisfies every
morphism property that holds for `a`, is Zariski-local at the target and is stable under base
change. -/
theorem of_charts {V A : Scheme.{u}}
    (f : V ⟶ Uo.toScheme) (a : A ⟶ Z)
    {ι : Type*} (Ω : ι → Z.Opens) (hΩ : ⨆ i, Ω i = Uo)
    (κ : ∀ i, (a ⁻¹ᵁ Ω i).toScheme ⟶ V)
    (h : ∀ i, IsPullback (a ∣_ Ω i) (κ i) (Ω i).ι (f ≫ Uo.ι))
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange] (ha : P a) :
    P f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i ↦ Uo.ι ⁻¹ᵁ Ω i)
    (iSup_ι_preimage_eq_top Ω hΩ) fun i ↦ ?_
  have hle : Ω i ≤ Uo := hΩ ▸ le_iSup Ω i
  have hiso := isIso_morphismRestrict_ι (Uo := Uo) hle
  let e := (h i).isoIsPullback _ _ (isPullback_morphismRestrict (f ≫ Uo.ι) (Ω i))
  have hcomp : e.hom ≫ (f ≫ Uo.ι) ∣_ Ω i = a ∣_ Ω i :=
    (h i).isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict (f ≫ Uo.ι) (Ω i))
  have hrestrict : P ((f ≫ Uo.ι) ∣_ Ω i) := by
    rw [← P.cancel_left_of_respectsIso e.hom, hcomp]
    exact IsZariskiLocalAtTarget.restrict ha (Ω i)
  rw [morphismRestrict_comp] at hrestrict
  exact (P.cancel_right_of_respectsIso (f ∣_ Uo.ι ⁻¹ᵁ Ω i) (Uo.ι ∣_ Ω i)).mp hrestrict

/-- A morphism into an open subscheme whose charts over a cover of that open subscheme are the
charts of an integral morphism is itself integral. -/
theorem isIntegralHom_of_charts {V A : Scheme.{u}}
    (f : V ⟶ Uo.toScheme) (a : A ⟶ Z)
    {ι : Type*} (Ω : ι → Z.Opens) (hΩ : ⨆ i, Ω i = Uo)
    (κ : ∀ i, (a ⁻¹ᵁ Ω i).toScheme ⟶ V)
    (h : ∀ i, IsPullback (a ∣_ Ω i) (κ i) (Ω i).ι (f ≫ Uo.ι))
    [IsIntegralHom a] :
    IsIntegralHom f :=
  have : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  of_charts f a Ω hΩ κ h @IsIntegralHom ‹_›

/-- A morphism into an open subscheme whose charts over a cover of that open subscheme are the
charts of a surjective morphism is itself surjective. -/
theorem surjective_of_charts {V A : Scheme.{u}}
    (f : V ⟶ Uo.toScheme) (a : A ⟶ Z)
    {ι : Type*} (Ω : ι → Z.Opens) (hΩ : ⨆ i, Ω i = Uo)
    (κ : ∀ i, (a ⁻¹ᵁ Ω i).toScheme ⟶ V)
    (h : ∀ i, IsPullback (a ∣_ Ω i) (κ i) (Ω i).ι (f ≫ Uo.ι))
    [Surjective a] :
    Surjective f :=
  of_charts f a Ω hΩ κ h @Surjective ‹_›

end

end Stacks.ChartLocalProperty
