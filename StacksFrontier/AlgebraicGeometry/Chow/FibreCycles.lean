module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine

/-!
# The relative projective line and the fibres of a closed subscheme over its two sections

Let `f : X ⟶ S` be a morphism of schemes. The *relative projective line* `ℙ¹_S` is the base
change to `S` of the projective line over the integers, and `X ×_S ℙ¹_S` is the family of
projective lines over `X`. Every integral point `e : Spec ℤ ⟶ ℙ¹_ℤ` induces a constant section
`X ⟶ X ×_S ℙ¹_S`; taking `e` to be the origin of the first or of the second affine chart gives
the *zero section* and the *infinity section*. For a closed subscheme `Z ⊆ X ×_S ℙ¹_S` the
scheme-theoretic preimages of `Z` along these two sections are the *zero fibre* `Z₀` and the
*infinity fibre* `Z_∞`, regarded as closed subschemes of `X`.

Stacks Tag 02S5 asserts that, under bounds on the `δ`-dimensions of `Z`, `Z₀` and `Z_∞` and a
condition on the embedded points of `Z`, the cycles `[Z₀]_k` and `[Z_∞]_k` are rationally
equivalent. This file contains the geometry those statements are about: the construction of
`ℙ¹_S`, of the two sections and of the two fibres, together with their basic properties.

## Main definitions

* `Stacks.Chow.relativeProjectiveLine`: the projective line `ℙ¹_S` over a scheme `S`, with its
  `Scheme.Over S` structure.
* `Stacks.Chow.projectiveLineProduct`: the family `X ×_S ℙ¹_S` attached to `f : X ⟶ S`.
* `Stacks.Chow.integralZeroSection` and `Stacks.Chow.integralInfinitySection`: the two
  distinguished integral points of `ℙ¹_ℤ`, the origins of its two affine charts.
* `Stacks.Chow.constantSection`: the section of `X ×_S ℙ¹_S ⟶ X` determined by an integral
  point of `ℙ¹_ℤ`, with `Stacks.Chow.zeroSection` and `Stacks.Chow.infinitySection` its two
  distinguished instances.
* `Stacks.Chow.zeroFiber` and `Stacks.Chow.infinityFiber`: the scheme-theoretic preimages of a
  closed subscheme of `X ×_S ℙ¹_S` along the two sections, as closed subschemes of `X`.

## Main results

* `Stacks.Chow.constantSection_comp_fst`: a constant section really is a section of the first
  projection, so it is a split monomorphism and injective on points
  (`Stacks.Chow.constantSection_base_injective`).
* `Stacks.Chow.coe_support_zeroFiber` and `Stacks.Chow.coe_support_infinityFiber`: the support
  of a fibre is the preimage of the support of the subscheme under the section.
* `Stacks.Chow.zeroFiber_mono` and `Stacks.Chow.infinityFiber_mono`: both fibre operations are
  monotone, and they preserve the two trivial closed subschemes.

## Implementation notes

The relative projective line is the base change of
`AlgebraicGeometry.projectiveLine (ULift ℤ)`, the two-chart gluing of Tag 01JE, along the
terminal morphism; the structure morphism is the first projection of that pullback. Writing
`ℙ¹_S` this way means that a point of `ℙ¹_ℤ` gives a point of `ℙ¹_S` over every base, which is
how `constantSection` is built: the data of a map to the pullback `X ×_S ℙ¹_S` is a map to `X`,
here the identity, and a map to `ℙ¹_S`, here `f` paired with the chosen integral point.

A closed subscheme is represented by `AlgebraicGeometry.Scheme.IdealSheafData` and its
scheme-theoretic preimage by `AlgebraicGeometry.Scheme.IdealSheafData.comap`, so the two fibre
operations are literally `comap` along the two sections and inherit its lattice-theoretic API.

The two integral points are the images of the origin of `Spec ℤ[T]` under the two chart
immersions. Their ranges, and hence the ranges of the two distinguished sections, are closed;
that is proved in `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/ClosedSections.lean` and
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/SectionRange.lean`, which are not imported here
so that this file stays at
the level of the constructions.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The projective line `ℙ¹_S` over a scheme `S`, as the base change of the projective line
over the integers along the terminal morphism of `S`. -/
public abbrev relativeProjectiveLine (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ)))

/-- The structure morphism of `ℙ¹_S` is the first projection of the defining pullback. -/
public instance relativeProjectiveLineOver (S : Scheme.{u}) :
    (relativeProjectiveLine S).Over S where
  hom := pullback.fst _ _

/-- The family of projective lines `X ×_S ℙ¹_S` attached to a morphism `f : X ⟶ S`. -/
public abbrev projectiveLineProduct {X S : Scheme.{u}} (f : X ⟶ S) : Scheme.{u} :=
  pullback f (relativeProjectiveLine S ↘ S)

/-- The point `0` of `ℙ¹_ℤ`, obtained as the origin of its first affine chart. -/
public def integralZeroSection :
    (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ) :=
  (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) ≫
    projectiveLineXChart (ULift.{u} ℤ)

/-- The point `∞` of `ℙ¹_ℤ`, obtained as the origin of its second affine chart. -/
public def integralInfinitySection :
    (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ) :=
  (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) ≫
    projectiveLineYChart (ULift.{u} ℤ)

/-- The section of `X ×_S ℙ¹_S ⟶ X` determined by an integral point `e` of `ℙ¹_ℤ`: it is the
identity on the first factor and the constant `e` on the second. -/
public def constantSection {X S : Scheme.{u}} (f : X ⟶ S)
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    X ⟶ projectiveLineProduct f :=
  pullback.lift (𝟙 X)
    (pullback.lift f (terminal.from X ≫ e) (by simp)) (by
      change f = _ ≫ pullback.fst _ _
      exact (pullback.lift_fst f (terminal.from X ≫ e) (by simp)).symm)

/-- The zero section of `X ×_S ℙ¹_S ⟶ X`. -/
public def zeroSection {X S : Scheme.{u}} (f : X ⟶ S) :
    X ⟶ projectiveLineProduct f :=
  constantSection f integralZeroSection

/-- The infinity section of `X ×_S ℙ¹_S ⟶ X`. -/
public def infinitySection {X S : Scheme.{u}} (f : X ⟶ S) :
    X ⟶ projectiveLineProduct f :=
  constantSection f integralInfinitySection

/-- The zero fibre of a closed subscheme of `X ×_S ℙ¹_S`: its scheme-theoretic preimage along
the zero section, as a closed subscheme of `X`. -/
public def zeroFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : (projectiveLineProduct f).IdealSheafData) : X.IdealSheafData :=
  Z.comap (zeroSection f)

/-- The infinity fibre of a closed subscheme of `X ×_S ℙ¹_S`: its scheme-theoretic preimage
along the infinity section, as a closed subscheme of `X`. -/
public def infinityFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : (projectiveLineProduct f).IdealSheafData) : X.IdealSheafData :=
  Z.comap (infinitySection f)

section Sections

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))

/-- A constant section is a section of the first projection of `X ×_S ℙ¹_S`. -/
@[simp]
theorem constantSection_comp_fst :
    constantSection f e ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The zero section is a section of the first projection of `X ×_S ℙ¹_S`. -/
@[simp]
theorem zeroSection_comp_fst :
    zeroSection f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
  constantSection_comp_fst f integralZeroSection

/-- The infinity section is a section of the first projection of `X ×_S ℙ¹_S`. -/
@[simp]
theorem infinitySection_comp_fst :
    infinitySection f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
  constantSection_comp_fst f integralInfinitySection

/-- A constant section is a split monomorphism, the first projection being its retraction. -/
public instance isSplitMono_constantSection : IsSplitMono (constantSection f e) :=
  IsSplitMono.mk' ⟨pullback.fst f (relativeProjectiveLine S ↘ S),
    constantSection_comp_fst f e⟩

/-- The first projection undoes a constant section on points. -/
theorem fst_constantSection_apply (x : X) :
    (pullback.fst f (relativeProjectiveLine S ↘ S)) ((constantSection f e) x) = x := by
  rw [← Scheme.Hom.comp_apply, constantSection_comp_fst]
  rfl

/-- A constant section is injective on points. -/
theorem constantSection_base_injective :
    Function.Injective (constantSection f e).base := by
  intro a b hab
  rw [← fst_constantSection_apply f e a, ← fst_constantSection_apply f e b]
  exact congrArg _ hab

end Sections

section Fibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The support of the zero fibre is the preimage of the support under the zero section. -/
@[simp]
theorem coe_support_zeroFiber (Z : (projectiveLineProduct f).IdealSheafData) :
    ((zeroFiber f Z).support : Set X) = zeroSection f ⁻¹' (Z.support : Set _) := by
  simp [zeroFiber]

/-- The support of the infinity fibre is the preimage of the support under the infinity
section. -/
@[simp]
theorem coe_support_infinityFiber (Z : (projectiveLineProduct f).IdealSheafData) :
    ((infinityFiber f Z).support : Set X) = infinitySection f ⁻¹' (Z.support : Set _) := by
  simp [infinityFiber]

/-- The zero fibre of the whole family is the whole of `X`. -/
@[simp] theorem zeroFiber_bot : zeroFiber f ⊥ = ⊥ := by simp [zeroFiber]

/-- The zero fibre of the empty subscheme is empty. -/
@[simp] theorem zeroFiber_top : zeroFiber f ⊤ = ⊤ := by simp [zeroFiber]

/-- The infinity fibre of the whole family is the whole of `X`. -/
@[simp] theorem infinityFiber_bot : infinityFiber f ⊥ = ⊥ := by simp [infinityFiber]

/-- The infinity fibre of the empty subscheme is empty. -/
@[simp] theorem infinityFiber_top : infinityFiber f ⊤ = ⊤ := by simp [infinityFiber]

/-- Taking the zero fibre is monotone in the closed subscheme. -/
theorem zeroFiber_mono : Monotone (zeroFiber f) :=
  Scheme.IdealSheafData.comap_mono (f := zeroSection f)

/-- Taking the infinity fibre is monotone in the closed subscheme. -/
theorem infinityFiber_mono : Monotone (infinityFiber f) :=
  Scheme.IdealSheafData.comap_mono (f := infinitySection f)

end Fibres

end Stacks.Chow

end
