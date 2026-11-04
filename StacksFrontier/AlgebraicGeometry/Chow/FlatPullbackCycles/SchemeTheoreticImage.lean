module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper pushforward of a principal divisor onto the scheme-theoretic image

Let `p : X ⟶ Y` be a proper morphism over the base, `V ⊆ X` an integral closed subscheme of
delta-dimension `k + 1` and `g` a nonzero rational function on `V`. The dichotomy
`Stacks.Chow.ProperPushforwardKillsPrincipalDivisor` says that the proper pushforward of `div(g)`
along `p` is either zero or the principal divisor of a rational function on the scheme-theoretic
image `V.map p`. This file proves the second alternative when `V.map p` again has
delta-dimension `k + 1`: the pushforward is then the principal divisor of the norm of `g` in the
extension `R(V.map p) ⊆ R(V)` of function fields induced by the restriction
`(V.subschemeι ≫ p).toImage : V ⟶ V.map p`. Consequently the dichotomy holds as soon as the
pushforward vanishes whenever the delta-dimension drops.

It also proves that the scheme-theoretic image of a reduced (resp. irreducible, integral) scheme
under a quasi-compact morphism is reduced (resp. irreducible, integral).

## Main results

* `Stacks.Chow.isReduced_image` — the scheme-theoretic image of a reduced scheme under a
  quasi-compact morphism is reduced.
* `Stacks.Chow.isIntegral_image` — the scheme-theoretic image of an integral scheme under a
  quasi-compact morphism is integral.
* `Stacks.Chow.isProper_toImage` — the morphism onto the scheme-theoretic image of a proper
  morphism is proper.
* `Stacks.Chow.isIntegral_subscheme_map_of_isProper` — the scheme-theoretic image of an integral
  closed subscheme under a proper morphism is integral.
* `Stacks.Chow.exists_principalDivisorPushforward_eq_of_schemeDeltaDimension_eq` — when the image
  keeps the delta-dimension, the pushforward of `div(g)` is the principal divisor of the norm of
  `g` on the image.
* `Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_vanishing_of_dimension_drop` — the
  dichotomy holds once the pushforward vanishes whenever the image drops the delta-dimension.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The scheme-theoretic image of an integral scheme -/

/-- The kernel ideal sheaf of a quasi-compact morphism out of a reduced scheme is the vanishing
ideal sheaf of its own support. -/
theorem ker_eq_vanishingIdeal_support_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal f.ker.support := by
  rw [Scheme.IdealSheafData.vanishingIdeal_support]
  refine Scheme.IdealSheafData.ext (funext fun U ↦ ?_)
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine (Ideal.radical_eq_iff.mpr ?_).symm
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)

/-- The scheme-theoretic image of a reduced scheme under a quasi-compact morphism is reduced. -/
theorem isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  rw [show f.image = (Scheme.IdealSheafData.vanishingIdeal f.ker.support).subscheme from
    congrArg Scheme.IdealSheafData.subscheme (ker_eq_vanishingIdeal_support_of_isReduced f)]
  infer_instance

/-- The scheme-theoretic image of an irreducible scheme under a quasi-compact morphism is
irreducible. -/
@[ega "I 9.5.9" "(ii), irreducible case"]
theorem irreducibleSpace_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [IrreducibleSpace X] : IrreducibleSpace f.image := by
  have hclosure := ((IrreducibleSpace.isIrreducible_univ X).image f.toImage.base
    f.toImage.continuous.continuousOn).closure
  rw [Set.image_univ, (IsDominant.denseRange (f := f.toImage)).closure_range] at hclosure
  exact (irreducibleSpace_def _).mpr hclosure

/-- The scheme-theoretic image of an integral scheme under a quasi-compact morphism is
integral. -/
@[ega "I 9.5.9" "(ii), integral case"]
theorem isIntegral_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] :
    IsIntegral f.image :=
  have := irreducibleSpace_image f
  have := isReduced_image f
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The morphism onto the scheme-theoretic image of a proper morphism is proper. -/
theorem isProper_toImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsProper f.toImage :=
  have : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  IsProper.of_comp _ f.imageι

/-- The image `V.map p` of an integral closed subscheme `V` under a proper morphism `p` is an
integral closed subscheme. -/
@[ega "I 9.5.9" "(ii), integral case"]
theorem isIntegral_subscheme_map_of_isProper {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme) : IsIntegral (V.map p).subscheme :=
  have := hV
  isIntegral_image (V.subschemeι ≫ p)

/-! ### The case where the image keeps the delta-dimension -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)

include hp

/-- Let `p : X ⟶ Y` be proper over the base, let `V ⊆ X` be an integral closed subscheme of
delta-dimension `k + 1` and let `g` be a nonzero rational function on `V`. If the
scheme-theoretic image `V.map p` again has delta-dimension `k + 1`, then the proper pushforward
of `div(g)` along `p` is the principal divisor of a rational function on `V.map p`, namely of the
norm of `g` in the extension of function fields induced by the restriction `V ⟶ V.map p` of
`p`. -/
theorem exists_principalDivisorPushforward_eq_of_schemeDeltaDimension_eq (k : ℤ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hdimT : schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    ∃ hT : IsIntegral (V.map p).subscheme,
      ∃ h : (rationalFunctions (V.map p).subscheme)ˣ,
        properPushforwardPrincipalDivisor C sX sY p V hV g =
          principalDivisorPushforward C sY (V.map p) hT h := by
  have hT : IsIntegral (V.map p).subscheme := isIntegral_subscheme_map_of_isProper p V hV
  have := hV
  have := hT
  set π : V.subscheme ⟶ (V.map p).subscheme := (V.subschemeι ≫ p).toImage with hπdef
  have hπ : π ≫ (V.map p).subschemeι = V.subschemeι ≫ p :=
    (V.subschemeι ≫ p).toImage_imageι
  have _ : IsProper π := isProper_toImage (V.subschemeι ≫ p)
  have _ : IsDominant π := inferInstanceAs (IsDominant (V.subschemeι ≫ p).toImage)
  have hπs : π ≫ ((V.map p).subschemeι ≫ sY) = V.subschemeι ≫ sX := by
    rw [← Category.assoc, hπ, Category.assoc, hp]
  have _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  have _ : IsLocallyNoetherian (V.map p).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((V.map p).subschemeι ≫ sY)
  set eV := (rationalFunctionsEquivFunctionField V.subscheme).1 with heV
  set eT := (rationalFunctionsEquivFunctionField (V.map p).subscheme).1 with heT
  set f : V.subscheme.functionField := eV (g : rationalFunctions V.subscheme) with hf
  have hfne : f ≠ 0 := (g.isUnit.map eV.toRingHom.toMonoidHom).ne_zero
  let _ : Algebra (V.map p).subscheme.functionField V.subscheme.functionField :=
    (dominantFunctionFieldMap π).toAlgebra
  set n : (V.map p).subscheme.functionField :=
    Algebra.norm (V.map p).subscheme.functionField f with hn
  have hnne : n ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hfne).map (Algebra.norm (V.map p).subscheme.functionField)).ne_zero
  obtain ⟨h, hval⟩ : ∃ h : (rationalFunctions (V.map p).subscheme)ˣ,
      eT (h : rationalFunctions (V.map p).subscheme) = n :=
    ⟨Units.mapEquiv eT.symm.toMulEquiv (isUnit_iff_ne_zero.mpr hnne).unit, by simp⟩
  refine ⟨hT, h, ?_⟩
  have h02RT : properPushforward C (V.subschemeι ≫ sX) ((V.map p).subschemeι ≫ sY) π hπs
      ((k + 1) - 1) (principalDivisorCycle C (V.subschemeι ≫ sX) hdim f) =
        principalDivisorCycle C ((V.map p).subschemeι ≫ sY) hdimT n :=
    properPushforward_principalDivisorCycle C (V.subschemeι ≫ sX)
      ((V.map p).subschemeι ≫ sY) hdim hdimT π hπs f hfne
  set dV := relativeDimension C.dimensionFunction (V.subschemeι ≫ sX)
  set dT := relativeDimension C.dimensionFunction ((V.map p).subschemeι ≫ sY)
  set dY := relativeDimension C.dimensionFunction sY
  have hcycle : AlgebraicCycle.map π dV dT (principalCycle V.subscheme f) =
      principalCycle (V.map p).subscheme n :=
    congrArg Subtype.val h02RT
  calc properPushforwardPrincipalDivisor C sX sY p V hV g
      = AlgebraicCycle.map (V.subschemeι ≫ p) dV dY (principalCycle V.subscheme f) :=
        algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX) sX sY V.subschemeι p
          rfl hp _
    _ = AlgebraicCycle.map (π ≫ (V.map p).subschemeι) dV dY (principalCycle V.subscheme f) :=
        algebraicCycle_map_congr hπ.symm _ _ _
    _ = AlgebraicCycle.map (V.map p).subschemeι dT dY
          (AlgebraicCycle.map π dV dT (principalCycle V.subscheme f)) :=
        (algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX)
          ((V.map p).subschemeι ≫ sY) sY π (V.map p).subschemeι hπs rfl _).symm
    _ = principalDivisorPushforward C sY (V.map p) hT h := by
        rw [hcycle, principalDivisorPushforward, hval]

/-! ### The dichotomy -/

/-- The dichotomy `Stacks.Chow.ProperPushforwardKillsPrincipalDivisor` holds for a proper `p` as
soon as the pushforward of `div(g)` vanishes whenever the scheme-theoretic image of the integral
closed subscheme fails to keep the delta-dimension. -/
theorem properPushforwardKillsPrincipalDivisor_of_vanishing_of_dimension_drop (k : ℤ)
    (hdrop : ∀ (V : X.IdealSheafData) (hV : IsIntegral V.subscheme),
      schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt) →
        schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) ≠ ((k + 1 : ℤ) : EInt) →
          ∀ g : (rationalFunctions V.subscheme)ˣ,
            properPushforwardPrincipalDivisor C sX sY p V hV g = 0) :
    ProperPushforwardKillsPrincipalDivisor C sX sY p k := by
  intro V hV hdim g
  by_cases hdimT : schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)
  · obtain ⟨hT, h, heq⟩ :=
      exists_principalDivisorPushforward_eq_of_schemeDeltaDimension_eq C sX sY p hp k V hV
        hdim hdimT g
    exact Or.inr ⟨hT, hdimT, h, heq⟩
  · exact Or.inl (hdrop V hV hdim hdimT g)

end Stacks.Chow

end
