module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Flat base change of a square of condition (RS*)

Let `X ⟶ X'`, `X ⟶ Y`, `Y ⟶ Y'`, `X' ⟶ Y'` be a commutative square of affine schemes whose square
of global sections is cartesian, `Γ(Y') = Γ(Y) ×_{Γ(X)} Γ(X')`, with `Γ(X') ⟶ Γ(X)` surjective —
the squares condition (RS*) of [Stacks Project, Tag 07Y8] quantifies over. Base change along a
flat morphism `V ⟶ Y'` from an affine scheme gives a square of the same kind: its square of
global sections is again cartesian, because tensoring with a flat algebra preserves the fibre
product of rings (`MilnorPatching.flat_baseChange_pullback`), and the base change of the closed
immersion `X ⟶ X'` is again a closed immersion. In particular the base-changed square is again
a pushout of schemes.

## Main results

* `Deformation.Artin.isPullback_appTop_of_flat_baseChange`: the base-changed square of global
  sections is cartesian.
* `Deformation.Artin.isPushout_of_flat_baseChange`: the base-changed square is a pushout.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

variable {X X' Y Y' V VX VX' VY : Scheme.{u}}
  [IsAffine X] [IsAffine X'] [IsAffine Y] [IsAffine Y'] [IsAffine V]
  (f : X ⟶ Y) (i : X ⟶ X') (b : Y ⟶ Y') (a : X' ⟶ Y')
  (q : V ⟶ Y') (qY : VY ⟶ V) (pY : VY ⟶ Y) (qX' : VX' ⟶ V) (pX' : VX' ⟶ X')
  (fV : VX ⟶ VY) (iV : VX ⟶ VX') (pX : VX ⟶ X)

include f i b a q qY pY qX' pX' fV iV pX in
/-- **Flat base change of a square of condition (RS*), on global sections.** -/
theorem isPullback_appTop_of_flat_baseChange
    (hΓ : IsPullback b.appTop a.appTop f.appTop i.appTop) [Flat q]
    (sY : IsPullback qY pY q b) (sX' : IsPullback qX' pX' q a)
    (sX : IsPullback fV pX pY f) (sX'' : IsPullback iV pX pX' i)
    (hcomm : fV ≫ qY = iV ≫ qX') :
    IsPullback qY.appTop qX'.appTop fV.appTop iV.appTop := by
  have : IsAffine VY := IsAffine.of_isPullback sY
  have : IsAffine VX' := IsAffine.of_isPullback sX'
  have : IsAffine VX := IsAffine.of_isPullback sX
  exact MilnorPatching.flat_baseChange_pullback hΓ (HasRingHomProperty.appTop @Flat q ‹_›)
    (isPushout_appTop_of_isPullback sY) (isPushout_appTop_of_isPullback sX')
    (isPushout_appTop_of_isPullback sX) (isPushout_appTop_of_isPullback sX'')
    (by rw [← Scheme.Hom.comp_appTop, hcomm, Scheme.Hom.comp_appTop])

include f i b a q qY pY qX' pX' fV iV pX in
/-- **Flat base change of a square of condition (RS*) is again a pushout.** -/
theorem isPushout_of_flat_baseChange
    (hΓ : IsPullback b.appTop a.appTop f.appTop i.appTop) [IsClosedImmersion i] [Flat q]
    (sY : IsPullback qY pY q b) (sX' : IsPullback qX' pX' q a)
    (sX : IsPullback fV pX pY f) (sX'' : IsPullback iV pX pX' i)
    (hcomm : fV ≫ qY = iV ≫ qX') :
    IsPushout fV iV qY qX' := by
  have : IsAffine VY := IsAffine.of_isPullback sY
  have : IsAffine VX' := IsAffine.of_isPullback sX'
  have : IsAffine VX := IsAffine.of_isPullback sX
  have : IsClosedImmersion iV := MorphismProperty.of_isPullback sX''.flip ‹_›
  exact isPushout_of_isPullback_appTop fV iV qY qX'
    (isPullback_appTop_of_flat_baseChange f i b a q qY pY qX' pX' fV iV pX hΓ sY sX' sX sX''
      hcomm)
    (Scheme.Hom.app_surjective iV ⊤ (isAffineOpen_top VX'))

end Deformation.Artin
