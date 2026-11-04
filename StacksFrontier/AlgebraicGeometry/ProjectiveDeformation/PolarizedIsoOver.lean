module

public import
  StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DeformationsOfProjectiveSchemesFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.GlobalSectionsDatum

/-!
# Isomorphisms of polarized families over a common base, and their section algebras

For two polarized families `(f : X ⟶ S, ℒ)` and `(g : Y ⟶ S, ℳ)` over the same scheme `S`, an
isomorphism of polarized families over `S` is an isomorphism `φ : X ≅ Y` over `S` together with an
isomorphism `φ^* ℳ ≅ ℒ`. Pulling sections back along `φ` and applying the comparison of
polarizations gives, at every cut `d₀ > 0`, a homomorphism between the global sections data of the
truncated section algebras `𝒪_S ⊕ ⨁_{d ≥ d₀} g_* ℳ^{⊗ d}` and `𝒪_S ⊕ ⨁_{d ≥ d₀} f_* ℒ^{⊗ d}` of
[Stacks, Tag 0D4F] (`Stacks.AlgebraicGeometry.SectionRingBaseChange.squarePieceMap` and
`Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapApp` for the square of `φ` over `𝟙 S`).

This file records the structure of such isomorphisms and the statement, over an affine base, that
this assignment is a bijection onto the isomorphisms of the data
(`Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`), in the form in
which it is consumed by the proof that the diagonal of the stack of polarized schemes is
representable.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver`.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver.ext`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.GradedIsomScheme

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

open SectionRingBaseChange

/-- **An isomorphism of polarized families over a common base `S`**: an isomorphism of total
spaces over `S` and an isomorphism from the pullback of the second polarization to the first. -/
structure PolarizedIsoOver {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (L : X.Modules)
    (M : Y.Modules) where
  /-- The isomorphism of total spaces. -/
  iso : X ≅ Y
  /-- The isomorphism lies over `S`. -/
  comm : iso.hom ≫ g = f
  /-- The comparison of polarizations. -/
  pol : (Scheme.Modules.pullback iso.hom).obj M ≅ L

/-- Two polarized isomorphisms over a common base agree as soon as their isomorphisms of total
spaces agree and their comparisons of polarizations agree over the latter. -/
theorem PolarizedIsoOver.ext {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules}
    {M : Y.Modules} {P Q : PolarizedIsoOver f g L M} (h : P.iso.hom = Q.iso.hom)
    (hpol : P.pol ≍ Q.pol) : P = Q := by
  obtain ⟨i, c, p⟩ := P
  obtain ⟨i', c', p'⟩ := Q
  obtain rfl : i = i' := Iso.ext h
  cases hpol
  rfl

/-- **Polarized isomorphisms over an affine base are isomorphisms of section algebras.** For
polarized families `(f, ℒ)`, `(g, ℳ)` over an affine scheme `S` (proper, flat, of finite
presentation, polarizations invertible and relatively ample) and every cut `d₀ > 0`, pulling
sections back is a bijection from the isomorphisms of polarized families over `S` onto the
isomorphisms of the global sections data of the truncated section algebras at `d₀`. -/
def PolarizedIsoSectionBijection : Prop :=
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (L : X.Modules) (M : Y.Modules)
    [IsProper f] [Flat f] [QuasiCompact f] [QuasiSeparated f]
    [IsProper g] [Flat g] [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M] [IsAffine S],
    _root_.AlgebraicGeometry.FinitePresentation f →
    _root_.AlgebraicGeometry.FinitePresentation g →
    Stacks.RelativeAmple.IsRelativelyAmple f L → Stacks.RelativeAmple.IsRelativelyAmple g M →
    ∀ (d₀ : ℕ) (hd₀ : 0 < d₀),
    ∃ e : PolarizedIsoOver f g L M ≃
        GradedMulDatum.Iso (tailAlgebra g M d₀ hd₀).globalDatum
          (tailAlgebra f L d₀ hd₀).globalDatum,
      ∀ (φ : PolarizedIsoOver f g L M) (n : ℕ)
        (s : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)),
        (e φ).hom.app n s =
          tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
            (squarePieceMap φ.iso.hom g f (𝟙 S) (by rw [φ.comm, Category.comp_id]) M L φ.pol
              ⊤ ⊤ le_top) n s

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
