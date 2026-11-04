module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent

/-!
# Pseudo-coherence of a morphism, unwound into finite type and relative pseudo-coherence

Stacks 067H (1) defines a pseudo-coherent ring map as one of finite type whose target, as a module
over itself, is pseudo-coherent relative to the source, and
`Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent` identifies this with
`Algebra.PseudoCoherent`. This file applies that identification to the
maps on sections of a morphism of schemes, which is the step the source takes in the second
paragraph of the proof of Stacks 067Y when it says "this is the definition of a pseudo-coherent
ring map".

Concretely, for a morphism `f : X ⟶ S` which is locally of finite type and a compatible pair of
affine opens `U ⊆ f ⁻¹ᵁ V`, finiteness of type is automatic, so what remains
of pseudo-coherence of `Γ(S, V) ⟶ Γ(X, U)` is exactly relative pseudo-coherence of `Γ(X, U)` as
a module over itself with respect to `Γ(S, V)`. Condition (2) of Stacks 067Y, which is the
definition `AlgebraicGeometry.PseudoCoherent` of Stacks 067Z, is therefore equivalent to local
finiteness of type together with that purely module-theoretic condition at every compatible
affine pair.

## Main results

* `AlgebraicGeometry.algebraFiniteType_appLE`: for `f` locally of finite type and a compatible
  pair of affine opens, `Γ(X, U)` is a finite-type `Γ(S, V)`-algebra. This is the sections form
  of Stacks 01T2, which the source quotes immediately before Stacks 09UI to know that the closed
  immersions into affine space used there exist.
* `AlgebraicGeometry.locallyOfFiniteType_of_forall_appLE_finiteType`: the converse reading, that
  finiteness of type at every compatible affine pair gives `LocallyOfFiniteType`.
* `AlgebraicGeometry.algebraPseudoCoherent_appLE_iff`: under `LocallyOfFiniteType f`,
  pseudo-coherence of the map on sections is relative pseudo-coherence of `Γ(X, U)` over itself
  with respect to `Γ(S, V)`.
* `AlgebraicGeometry.locallyOfFiniteType_of_forall_appLE_pseudoCoherent`: the
  finite-type part of condition (2) of Stacks 067Y on its own, which is what the proof of that
  lemma uses to get the first half of condition (3).
* `AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType_and_relative`: Stacks 067Z unwound,
  that is, condition (2) of Stacks 067Y split into its finite-type part and its relative part.

## Implementation notes

`RingHom.FiniteType` is by definition `Algebra.FiniteType` for the algebra structure induced by
the homomorphism, so the sections form of Stacks 01T2 is `Scheme.Hom.finiteType_appLE` read
through that definition and needs no proof of its own. It is stated here because the two
predicates of Stacks 067H (1) that it feeds —
`PseudoCoherence.IsModuleRelativelyPseudoCoherent` and `Algebra.FiniteType` — take the algebra
and finite-type structures as instance arguments, and a caller has to produce them before either
condition can be written down at all.

`AlgebraicGeometry.algebraPseudoCoherent_appLE_iff` is
`Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent` at the finite-type
structure that `LocallyOfFiniteType f` provides. `Algebra.FiniteType` is a `Prop`, so any other
witness gives the same statement.

The statements use `letI` for the two instances rather than explicit `@`-application, matching
the way `AlgebraicGeometry.pseudoCoherent_tfae` presents condition (2) of Stacks 067Y, and the
hypotheses quantifying over affine pairs put the open of the source first, in the binder order
of that lemma's condition (2), rather than in the order of the fields of
`AlgebraicGeometry.LocallyOfFiniteType`.

## References

* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 36.60.2 (067Z)](https://stacks.math.columbia.edu/tag/067Z)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
* [The Stacks Project, Lemma 29.15.2 (01T2)](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 01T2, on sections.** If `f : X ⟶ S` is locally of finite type and `U ⊆ X`,
`V ⊆ S` are affine opens with `U ⊆ f ⁻¹ᵁ V`, then `Γ(X, U)` is a finite-type algebra over
`Γ(S, V)` for the algebra structure induced by `f.appLE V U e`.

This is `AlgebraicGeometry.Scheme.Hom.finiteType_appLE` read through the definition of
`RingHom.FiniteType`; it is recorded separately because the relative pseudo-coherence conditions
of Stacks 065I take `Algebra.FiniteType` as an instance argument. -/
public theorem algebraFiniteType_appLE [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Algebra.FiniteType Γ(S, V) Γ(X, U) :=
  f.finiteType_appLE hV hU e

/-- Conversely, a morphism of schemes whose map on sections over every compatible pair of affine
opens makes the target a finite-type algebra over the source is locally of finite type. -/
public theorem locallyOfFiniteType_of_forall_appLE_finiteType
    (h : ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V →
      ∀ (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.FiniteType Γ(S, V) Γ(X, U)) :
    LocallyOfFiniteType f :=
  ⟨fun {V} hV {U} hU e ↦ h U hU V hV e⟩

/-- Under `LocallyOfFiniteType f` the ring map `Γ(S, V) ⟶ Γ(X, U)` is of finite type, so it is
pseudo-coherent exactly when `Γ(X, U)`, as a module over itself, is pseudo-coherent relative to
`Γ(S, V)` (`Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent`). -/
public theorem algebraPseudoCoherent_appLE_iff [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
    Algebra.PseudoCoherent Γ(S, V) Γ(X, U) ↔
      PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent

/-- The finite-type part of condition (2) of Stacks 067Y: if the map on sections over every
compatible pair of affine opens is a pseudo-coherent ring map, then `f` is locally of finite
type, because a pseudo-coherent ring map is of finite presentation
(`Algebra.PseudoCoherent.finitePresentation`), hence of finite type.

From `[PseudoCoherent f]` type class search finds the conclusion through Stacks 0682,
`AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent`, followed by Mathlib's instance
from `AlgebraicGeometry.LocallyOfFinitePresentation` to `AlgebraicGeometry.LocallyOfFiniteType`;
this theorem states it against the unbundled form of condition (2) used by
`AlgebraicGeometry.pseudoCoherent_tfae`. -/
public theorem locallyOfFiniteType_of_forall_appLE_pseudoCoherent
    (h : ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V →
      ∀ (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.PseudoCoherent Γ(S, V) Γ(X, U)) :
    LocallyOfFiniteType f :=
  locallyOfFiniteType_of_forall_appLE_finiteType f fun U hU V hV e ↦
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have := h U hU V hV e
    inferInstance

/-- **Stacks 067Z unwound.** A morphism of schemes is pseudo-coherent — condition (2) of
Stacks 067Y — if and only if it is locally of finite type and, over every compatible pair of
affine opens, `Γ(X, U)` is pseudo-coherent as a module over itself relative to `Γ(S, V)`.

The right-hand side is the sections-level shape of condition (3) of Stacks 067Y: it is already
split into local finiteness of type and a purely module-theoretic relative condition, so only
the comparison of Stacks 09VF and Stacks 09UJ between that relative condition and relative
pseudo-coherence of `𝒪_X` over `S` is still needed to reach condition (3) itself. -/
public theorem pseudoCoherent_iff_locallyOfFiniteType_and_relative :
    PseudoCoherent f ↔
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
          (e : U ≤ f ⁻¹ᵁ V),
          letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
          letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
          PseudoCoherence.IsModuleRelativelyPseudoCoherent
            (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) := by
  constructor
  · intro hpc
    exact ⟨inferInstance, fun U hU V hV e ↦
      (algebraPseudoCoherent_appLE_iff f U hU V hV e).mp
        (hpc.pseudoCoherent_appLE hV hU e)⟩
  · rintro ⟨hft, h⟩
    exact ⟨fun {V} hV {U} hU e ↦
      (algebraPseudoCoherent_appLE_iff f U hU V hV e).mpr (h U hU V hV e)⟩

end AlgebraicGeometry

end
