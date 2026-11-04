module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs

/-!
# The `ℕ`-valued form of the Betti input of Stacks 0E6I

The input `hbetti` of
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank` asks for an
upper semicontinuous function `b` with values in `ℕ∞` whose value at the image of a field-valued
point is `AlgebraicGeometry.Space.h0FibreRank`, the `ℕ∞`-valued `Cardinal.toENat` of the rank of
`H⁰` of the fibre. Stacks 0E0R, part (2), is naturally stated for the `ℕ`-valued Betti number
`dim_{κ(y)} H^i(X_y, 𝓕_y)` given by `Module.finrank`. This file crosses the two value monoids:
an upper semicontinuous `ℕ`-valued function stays upper semicontinuous after `ℕ ↪ ℕ∞`, so a
`ℕ`-valued Betti function agreeing with `h0FibreRank` after that embedding supplies `hbetti`.

## Main results

* `AlgebraicGeometry.upperSemicontinuous_natCast_eNat`: an upper semicontinuous `ℕ`-valued
  function is upper semicontinuous as an `ℕ∞`-valued function.
* `AlgebraicGeometry.Space.exists_upperSemicontinuous_h0FibreRank_of_nat`: the conclusion of the
  `hbetti` input at one morphism, from a `ℕ`-valued upper semicontinuous Betti function.
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_natH0FibreRank`: condition
  (o) of Stacks 0E0E for `Curves^{h0,1}` over the `ℕ`-valued form of Stacks 0E0R at `i = 0`.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The composite of an upper semicontinuous `ℕ`-valued function with `ℕ ↪ ℕ∞` is upper
semicontinuous. -/
theorem upperSemicontinuous_natCast_eNat {α : Type*} [TopologicalSpace α] {β : α → ℕ}
    (h : UpperSemicontinuous β) : UpperSemicontinuous (fun x => (β x : ℕ∞)) := by
  intro x y hy
  induction y using ENat.recTopCoe with
  | top => exact Filter.Eventually.of_forall fun x' => ENat.coe_lt_top _
  | coe n =>
      have hy' : (β x : ℕ∞) < (n : ℕ∞) := hy
      have hlt : β x < n := by exact_mod_cast hy'
      refine (h x n hlt).mono fun x' hx' => ?_
      have hx'' : (β x' : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hx'
      exact hx''

namespace Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The `hbetti` conclusion at one morphism, from a `ℕ`-valued Betti function.** If `β` is an
upper semicontinuous `ℕ`-valued function on the base whose value at the image of a field-valued
point `p` is `dim H⁰` of the fibre at `p`, then `dim H⁰` is the value of one upper semicontinuous
`ℕ∞`-valued function on the base. -/
theorem exists_upperSemicontinuous_h0FibreRank_of_nat {U : BigFppfOver B integerBase hZ}
    {X : AlgebraicSpaces B integerBase hZ} (f : X ⟶ schemeSpace U)
    (β : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ) (hβ : UpperSemicontinuous β)
    (hp : ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
      Space.h0FibreRank B integerBase hZ f p = (β (Space.schemePoint B integerBase hZ U p) : ℕ∞)) :
    ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
      ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
        Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p) :=
  ⟨fun y => (β y : ℕ∞), upperSemicontinuous_natCast_eNat hβ, hp⟩

end Space

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}`, over the `ℕ`-valued form of Stacks 0E0R
at `i = 0` and Stacks 0E6B (a).** The input `hbettiNat` is parts (1) and (2) of Stacks 0E0R for
`i = 0` and `𝓕 = 𝒪_X` with the Betti number read as a natural number: for `f : X ⟶ U` proper,
flat and of finite presentation there is an upper semicontinuous `β : U → ℕ` with
`dim_k H⁰(X_k, 𝒪) = β(image of p)` at every field-valued point `p`. The conclusion is the one of
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank`. -/
theorem isOpenCurvesLocus_isH01CurveFamily_of_natH0FibreRank
    (hbettiNat : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ β : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ, UpperSemicontinuous β ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p =
            (β (Space.schemePoint B integerBase hZ U p) : ℕ∞))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) :=
  isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank
    (fun {_ _} f hproper hflat hfp =>
      let ⟨β, hβ, hp⟩ := hbettiNat f hproper hflat hfp
      Space.exists_upperSemicontinuous_h0FibreRank_of_nat f β hβ hp)
    hstruct

end CurveFamily

end AlgebraicGeometry

end
