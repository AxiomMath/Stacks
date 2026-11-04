module

public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic

/-!
# Finiteness and étaleness of the relative spectrum of a quasi-coherent algebra

Let `X` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The
structure morphism `relativeSpecToBase A` of the relative spectrum of `A` is an affine morphism,
and the preimage of an affine open `U` of `X` is `Spec A(U)`. So a property of ring maps which is
Zariski-local on the target holds for `relativeSpecToBase A` exactly when it holds for every
structure map `Γ(X, U) ⟶ A(U)` on sections over an affine open.

This file records that for finiteness and for étaleness, which together say that the relative
spectrum of `A` is a finite étale cover of `X`.

## Main results

* `Stacks.QuasicoherentAlgebraEqualizer.affineLocally_iff_app` — for an affine morphism `f` and a
  local property `Q` of ring maps, `affineLocally Q f` holds exactly when `Q (f.app U)` holds for
  every affine open `U` of the target; `Stacks.QuasicoherentAlgebraEqualizer.etale_iff_app` is the
  case of étaleness.
* `Stacks.QuasicoherentAlgebraEqualizer.isFinite_relativeSpecToBase` and
  `Stacks.QuasicoherentAlgebraEqualizer.etale_relativeSpecToBase` — the structure morphism of the
  relative spectrum of a quasi-coherent algebra is finite, respectively étale, as soon as every
  structure map on sections over an affine open is.

## Implementation notes

For finiteness no locality argument is needed: `AlgebraicGeometry.IsFinite` is by definition an
affine morphism all of whose maps on sections over an affine open are finite, so the statement is
the definition together with the identification of those maps.

For étaleness, `AlgebraicGeometry.Etale` is `affineLocally RingHom.Etale`, which quantifies over
pairs of an affine open of the target and an affine open of the source above it. For an affine
morphism those are redundant: `AlgebraicGeometry.targetAffineLocally_affineAnd_iff_affineLocally`
identifies `affineLocally Q` with `targetAffineLocally (affineAnd Q)` on affine morphisms, and
`AlgebraicGeometry.targetAffineLocally_affineAnd_iff'` evaluates the latter on the sections over
the affine opens of the target alone.

The identification of the map on sections is
`Stacks.AffineAlgebraEquivalence.structureMap_comp_sectionsIso`: the map on sections of
`relativeSpecToBase A` over an affine open `U`, followed by the isomorphism
`Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) ≅ A(U)`, is the structure map of `A` at `U`. Since
the second factor is an isomorphism, any property of ring maps stable under isomorphism does not
distinguish the two.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.QuasicoherentAlgebraEqualizer

/-! ### Affine-local criteria for an affine morphism -/

/-- For an affine morphism, a local property of ring maps holds affine-locally exactly when it
holds for the map on sections over every affine open of the target. -/
theorem affineLocally_iff_app
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.PropertyIsLocal @Q) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    affineLocally @Q f ↔ ∀ U : Y.Opens, IsAffineOpen U → Q (f.app U).hom := by
  have h := (targetAffineLocally_affineAnd_iff_affineLocally hQ f).symm.trans
    (targetAffineLocally_affineAnd_iff' hQ.respectsIso f)
  rwa [and_iff_right ‹IsAffineHom f›, and_iff_right ‹IsAffineHom f›] at h

/-- An affine morphism is étale exactly when the map on sections over every affine open of the
target is étale. -/
theorem etale_iff_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    Etale f ↔ ∀ U : Y.Opens, IsAffineOpen U → RingHom.Etale (f.app U).hom := by
  rw [HasRingHomProperty.eq_affineLocally (Q := @RingHom.Etale) @Etale]
  exact affineLocally_iff_app RingHom.Etale.propertyIsLocal f

/-! ### The relative spectrum of a quasi-coherent algebra -/

variable {X : Scheme.{u}} (A : AlgebraSheaf X) [A.IsQuasicoherent]

/-- A property of ring maps stable under isomorphism does not distinguish the map on sections of
the structure morphism of the relative spectrum over an affine open from the structure map of the
algebra over that open. -/
theorem respectsIso_app_relativeSpecToBase
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso @Q) (U : X.affineOpens) :
    Q ((relativeSpecToBase A).app (U : X.Opens)).hom ↔
      Q (A.hom.hom.app (op (U : X.Opens))).hom := by
  have h := hQ.cancel_right_isIso
    ((relativeSpecGluingData A).toBase.app (coverOpen U : X.Opens)) (sectionsIso A U).hom
  have h1 : (CommRingCat.Hom.hom (sectionsIso A U).hom).comp
        (CommRingCat.Hom.hom ((relativeSpecGluingData A).toBase.app (coverOpen U : X.Opens))) =
      CommRingCat.Hom.hom (A.hom.hom.app (op (coverOpen U : X.Opens))) :=
    congrArg CommRingCat.Hom.hom (structureMap_comp_sectionsIso A U)
  exact h.symm.trans (iff_of_eq (congrArg (fun k : _ →+* _ ↦ Q k) h1))

/-- **The relative spectrum of a quasi-coherent algebra is finite over the base** as soon as all
the structure maps of the algebra on sections over affine opens are finite. -/
theorem isFinite_relativeSpecToBase
    (h : ∀ U : X.affineOpens, RingHom.Finite (A.hom.hom.app (op (U : X.Opens))).hom) :
    IsFinite (relativeSpecToBase A) where
  finite_app U hU :=
    (respectsIso_app_relativeSpecToBase A RingHom.finite_respectsIso ⟨U, hU⟩).mpr (h ⟨U, hU⟩)

/-- **The relative spectrum of a quasi-coherent algebra is étale over the base** as soon as all
the structure maps of the algebra on sections over affine opens are étale. -/
theorem etale_relativeSpecToBase
    (h : ∀ U : X.affineOpens, RingHom.Etale (A.hom.hom.app (op (U : X.Opens))).hom) :
    Etale (relativeSpecToBase A) := by
  rw [etale_iff_app]
  exact fun U hU ↦
    (respectsIso_app_relativeSpecToBase A RingHom.Etale.propertyIsLocal.respectsIso
      ⟨U, hU⟩).mpr (h ⟨U, hU⟩)

end Stacks.QuasicoherentAlgebraEqualizer

end
