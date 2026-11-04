module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.SectionPresentation

/-!
# The distinguished sections of a family of projective lines are Cartier divisors

For a morphism `f : X ⟶ S` the images of the zero and the infinity section of
`X ×_S 𝐏¹_S ⟶ X` are effective Cartier divisors on the whole family, with no hypothesis on
`X`, and each is the zero scheme of the canonical section of its associated invertible module.

## Main results

* `Stacks.Chow.ker_zeroSection_eq_comap` and `Stacks.Chow.ker_infinitySection_eq_comap`: the
  image of a distinguished section of `X ×_S 𝐏¹_S` is the inverse image of the corresponding
  divisor of `𝐏¹_X` under the identification `𝐏¹_X ≅ X ×_S 𝐏¹_S`.
* `Stacks.Chow.isEffectiveCartierDivisor_ker_zeroSection` and
  `Stacks.Chow.isEffectiveCartierDivisor_ker_infinitySection`: those images are effective
  Cartier divisors on `X ×_S 𝐏¹_S`.
* `Stacks.Chow.zeroScheme_divisorSheafGlobalSection_ker_zeroSection` and
  `Stacks.Chow.zeroScheme_divisorSheafGlobalSection_ker_infinitySection`: each of them is the
  zero scheme of the canonical global section of its own invertible module.
* `Stacks.Chow.isTrivial_pullback_divisorSheaf_ker_zeroSection` and
  `Stacks.Chow.isTrivial_pullback_divisorSheaf_ker_infinitySection`: the normal bundles of the
  two sections are trivial.

## References

* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 0B7A](https://stacks.math.columbia.edu/tag/0B7A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))

/-- The constant section of `𝐏¹_X ⟶ X` at an integral point of `𝐏¹_ℤ` is the constant section
of the relative projective line over the base `X`: both are the morphism into the defining
pullback with components the identity and the chosen point. -/
theorem absoluteConstantSection_eq_lineConstantSection :
    absoluteConstantSection X e = lineConstantSection X e :=
  rfl

/-- **The image of a constant section of `X ×_S 𝐏¹_S` comes from `𝐏¹_X`.** It is the inverse
image of the image of the corresponding constant section of `𝐏¹_X ⟶ X` under the identification
`Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct`. -/
theorem ker_constantSection_eq_comap :
    (constantSection f e).ker =
      (lineConstantSection X e).ker.comap
        (relativeProjectiveLineIsoProjectiveLineProduct f).inv := by
  refine AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (b := 𝟙 X) (i := lineConstantSection X e) (IsPullback.of_vert_isIso_mono ⟨?_⟩)
  rw [Category.id_comp, constantSection_eq, absoluteConstantSection_eq_lineConstantSection,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The image of the zero section of `X ×_S 𝐏¹_S` is the inverse image of `D₀ ⊆ 𝐏¹_X`. -/
theorem ker_zeroSection_eq_comap :
    (zeroSection f).ker =
      (lineZeroDivisor X).comap (relativeProjectiveLineIsoProjectiveLineProduct f).inv :=
  ker_constantSection_eq_comap f integralZeroSection

/-- The image of the infinity section of `X ×_S 𝐏¹_S` is the inverse image of `D_∞ ⊆ 𝐏¹_X`. -/
theorem ker_infinitySection_eq_comap :
    (infinitySection f).ker =
      (lineInfinityDivisor X).comap (relativeProjectiveLineIsoProjectiveLineProduct f).inv :=
  ker_constantSection_eq_comap f integralInfinitySection

/-- **The image of the zero section is an effective Cartier divisor on `X ×_S 𝐏¹_S`.** The
identification `𝐏¹_X ≅ X ×_S 𝐏¹_S` carries `D₀ ⊆ 𝐏¹_X`, which is an effective Cartier divisor
over any base, to it. -/
theorem isEffectiveCartierDivisor_ker_zeroSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroSection f).ker := by
  rw [ker_zeroSection_eq_comap f]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (lineZeroDivisor_isEffectiveCartierDivisor X)

/-- **The image of the infinity section is an effective Cartier divisor on `X ×_S 𝐏¹_S`.** -/
theorem isEffectiveCartierDivisor_ker_infinitySection :
    Stacks.Divisors.IsEffectiveCartierDivisor (infinitySection f).ker := by
  rw [ker_infinitySection_eq_comap f]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (lineInfinityDivisor_isEffectiveCartierDivisor X)

/-- **The zero section of `X ×_S 𝐏¹_S` is cut out by a global section of an invertible module.**
Its image is the zero scheme of the canonical global section of the invertible module associated
to it. -/
theorem zeroScheme_divisorSheafGlobalSection_ker_zeroSection :
    letI := isEffectiveCartierDivisor_ker_zeroSection f
    AlgebraicGeometry.zeroScheme (projectiveLineProduct f)
        (Stacks.Divisors.divisorSheaf (zeroSection f).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection f).ker) =
      (zeroSection f).ker :=
  have := isEffectiveCartierDivisor_ker_zeroSection f
  Stacks.Divisors.zeroScheme_canonicalSection _

/-- **The infinity section of `X ×_S 𝐏¹_S` is cut out by a global section of an invertible
module.** -/
theorem zeroScheme_divisorSheafGlobalSection_ker_infinitySection :
    letI := isEffectiveCartierDivisor_ker_infinitySection f
    AlgebraicGeometry.zeroScheme (projectiveLineProduct f)
        (Stacks.Divisors.divisorSheaf (infinitySection f).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection f).ker) =
      (infinitySection f).ker :=
  have := isEffectiveCartierDivisor_ker_infinitySection f
  Stacks.Divisors.zeroScheme_canonicalSection _

/-! ### The normal bundles of the two sections are trivial -/

/-- **The normal bundle of the zero section of `X ×_S 𝐏¹_S` is trivial.** The identification
`𝐏¹_X ≅ X ×_S 𝐏¹_S` carries `D₀ ⊆ 𝐏¹_X`, whose normal bundle is trivial because `D₀` lies in the
affine chart and is cut out there by the coordinate, to the image of the zero section. -/
theorem isTrivial_pullback_divisorSheaf_ker_zeroSection :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (zeroSection f).ker.subscheme.sheaf.obj (zeroSection f).ker.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroSection f).ker.subschemeι).obj
        (Stacks.Divisors.divisorSheaf (zeroSection f).ker)) := by
  rw [ker_zeroSection_eq_comap f]
  exact isTrivial_pullback_divisorSheaf_comap _ (lineZeroDivisor X)
    (lineZeroDivisor_isEffectiveCartierDivisor X)
    (Stacks.Divisors.isPullbackDefined_of_flat _ _ (lineZeroDivisor_isEffectiveCartierDivisor X))
    (isTrivial_pullback_divisorSheaf_lineZeroDivisor X)

/-- **The normal bundle of the infinity section of `X ×_S 𝐏¹_S` is trivial.** -/
theorem isTrivial_pullback_divisorSheaf_ker_infinitySection :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (infinitySection f).ker.subscheme.sheaf.obj
      (infinitySection f).ker.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (infinitySection f).ker.subschemeι).obj
        (Stacks.Divisors.divisorSheaf (infinitySection f).ker)) := by
  rw [ker_infinitySection_eq_comap f]
  exact isTrivial_pullback_divisorSheaf_comap _ (lineInfinityDivisor X)
    (lineInfinityDivisor_isEffectiveCartierDivisor X)
    (Stacks.Divisors.isPullbackDefined_of_flat _ _
      (lineInfinityDivisor_isEffectiveCartierDivisor X))
    (isTrivial_pullback_divisorSheaf_lineInfinityDivisor X)

end Stacks.Chow

end
