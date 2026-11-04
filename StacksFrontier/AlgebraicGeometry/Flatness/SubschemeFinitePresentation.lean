module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Closed subschemes of finite presentation

The closed subscheme of `X` cut out by quasi-coherent ideal sheaf data `I` is of finite
presentation over `X` exactly when `I` is finitely generated on every affine open, i.e. when
`I` is of finite type as a quasi-coherent sheaf of ideals. This identification turns a
statement about finite-presentation closed subschemes into a statement about the lattice
`AlgebraicGeometry.Scheme.IdealSheafData`, where `⊥` and `⊔` are available.

Only `⊥` and `⊔` are needed downstream, so those two cases are recorded separately: the zero
ideal sheaf gives a closed immersion of finite presentation (it is an isomorphism), and the
sum of two finitely generated ideal sheaves is finitely generated because the sum of two
finitely generated ideals is.

## Main results

* `Stacks.Flatness.locallyOfFinitePresentation_iff_app`: an affine morphism is locally of
  finite presentation iff its map on sections over every affine open of the target is a ring
  map of finite presentation.
* `Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff` and
  `Stacks.Flatness.finitePresentation_subschemeι_iff`: the characterization of finite
  presentation of `I.subschemeι` by finite generation of `I`.
* `Stacks.Flatness.finitePresentation_subschemeι_bot` and
  `Stacks.Flatness.finitePresentation_subschemeι_sup`: the two closure properties of the set
  of ideal sheaves whose closed subscheme is of finite presentation.

## Implementation notes

`AlgebraicGeometry.LocallyOfFinitePresentation` is `affineLocally RingHom.FinitePresentation`,
which quantifies over affine opens of the *source* as well as of the target. For an affine
morphism those inner quantifiers collapse, and Mathlib's `affineAnd` machinery
(`AlgebraicGeometry.targetAffineLocally_affineAnd_iff'` together with
`AlgebraicGeometry.targetAffineLocally_affineAnd_iff_affineLocally`) performs exactly that
collapse; `locallyOfFinitePresentation_iff_app` packages it.

Over an affine open `U` the map on sections of `I.subschemeι` is surjective with kernel
`I.ideal U` (`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective` and
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app`), so the ring-theoretic input is
just that a surjection is of finite presentation iff its kernel is finitely generated.

Quasi-compactness and quasi-separatedness of `I.subschemeι` hold unconditionally, so they
contribute nothing to the characterization of `AlgebraicGeometry.FinitePresentation`.

The finite-generation condition is spelled out ideal by ideal rather than as finite type of
the quasi-coherent module `I`, and it is stated for `I.subschemeι` rather than for an
arbitrary closed immersion, so these results are the affine-local half of Tag 01TV rather
than that tag itself.

## References

* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Flatness

/-- A surjective ring map of finite presentation has finitely generated kernel. -/
theorem fg_ker_of_finitePresentation {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
    (h : φ.FinitePresentation) (hs : Function.Surjective φ) : (RingHom.ker φ).FG := by
  algebraize [φ]
  have : Algebra.FinitePresentation R S := h
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R S) hs

/-- An affine morphism of schemes is locally of finite presentation exactly when the ring map
it induces on sections over each affine open of the target is of finite presentation. -/
theorem locallyOfFinitePresentation_iff_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    LocallyOfFinitePresentation f ↔
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.FinitePresentation := by
  refine ⟨fun hf U hU ↦ ?_, fun h ↦ ?_⟩
  · have := HasRingHomProperty.appLE @LocallyOfFinitePresentation f hf ⟨U, hU⟩
      ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
    rwa [← f.app_eq_appLE] at this
  · have hand := targetAffineLocally_affineAnd_iff_affineLocally
      (Q := fun {_ _} _ _ φ ↦ φ.FinitePresentation) RingHom.finitePresentation_isLocal f
    have hand' := targetAffineLocally_affineAnd_iff'
      (Q := fun {_ _} _ _ φ ↦ φ.FinitePresentation)
      RingHom.finitePresentation_isLocal.respectsIso f
    rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation),
      ← affineLocally_iff_affineOpens_le]
    exact (hand.mp (hand'.mpr ⟨inferInstance, h⟩)).2

/-- The closed immersion cut out by quasi-coherent ideal sheaf data `I` is locally of finite
presentation exactly when `I` is finitely generated over every affine open. -/
theorem locallyOfFinitePresentation_subschemeι_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    LocallyOfFinitePresentation I.subschemeι ↔ ∀ U : X.affineOpens, (I.ideal U).FG := by
  rw [locallyOfFinitePresentation_iff_app]
  refine ⟨fun h U ↦ ?_, fun h U hU ↦ ?_⟩
  · rw [← I.ker_subschemeι_app U]
    exact fg_ker_of_finitePresentation (h U.1 U.2) (I.subschemeι_app_surjective U)
  · exact RingHom.FinitePresentation.of_surjective _ (I.subschemeι_app_surjective ⟨U, hU⟩)
      (by simpa only [I.ker_subschemeι_app ⟨U, hU⟩] using h ⟨U, hU⟩)

/-- The closed immersion cut out by quasi-coherent ideal sheaf data `I` is of finite
presentation exactly when `I` is finitely generated over every affine open: a closed immersion
is always quasi-compact and quasi-separated, so finite presentation asks nothing beyond local
finite presentation. -/
theorem finitePresentation_subschemeι_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    FinitePresentation I.subschemeι ↔ ∀ U : X.affineOpens, (I.ideal U).FG := by
  rw [show FinitePresentation I.subschemeι ↔ LocallyOfFinitePresentation I.subschemeι from
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, inferInstance, inferInstance⟩⟩,
    locallyOfFinitePresentation_subschemeι_iff]

/-- The closed subscheme cut out by the zero ideal sheaf — all of `X` — is of finite
presentation. -/
theorem finitePresentation_subschemeι_bot {X : Scheme.{u}} :
    FinitePresentation (⊥ : X.IdealSheafData).subschemeι :=
  (finitePresentation_subschemeι_iff _).mpr fun _ ↦ Submodule.fg_bot

/-- The scheme-theoretic intersection of two finite-presentation closed subschemes, cut out by
the sum of their ideal sheaves, is again of finite presentation. -/
theorem finitePresentation_subschemeι_sup {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : FinitePresentation I.subschemeι) (hJ : FinitePresentation J.subschemeι) :
    FinitePresentation (I ⊔ J).subschemeι :=
  (finitePresentation_subschemeι_iff _).mpr fun U ↦
    Submodule.FG.sup ((finitePresentation_subschemeι_iff _).mp hI U)
      ((finitePresentation_subschemeι_iff _).mp hJ U)

end Stacks.Flatness

end
