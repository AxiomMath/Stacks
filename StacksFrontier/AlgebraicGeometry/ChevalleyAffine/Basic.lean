module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Affineness from a surjective morphism out of an affine scheme

A scheme `X` is affine exactly when the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is an
isomorphism, and that morphism is always dominant on a quasi-compact `X`. This file isolates
the two conditions that upgrade dominance to an isomorphism, and uses them to reduce
"a Noetherian scheme receiving a finite surjective morphism from an affine scheme is affine"
to two named statements about the scheme and the morphism.

## Main results

* `Stacks.AlgebraicGeometry.ChevalleyAffine.isAffine_iff_isQuasiAffine_and_surjective_toSpecΓ`:
  a scheme is affine if and only if it is quasi-affine and `X ⟶ Spec Γ(X, ⊤)` is surjective.
* `Stacks.AlgebraicGeometry.ChevalleyAffine.isDominant_SpecMap_appTop`: for a surjective
  morphism `f : Y ⟶ X` with `Y` affine and `X` quasi-compact, the induced morphism
  `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)` is dominant.
* `Stacks.AlgebraicGeometry.ChevalleyAffine.isAffine_of_universallyClosed_SpecMap_appTop`
  and `…isAffine_of_isIntegral_appTop`: a quasi-affine `X` carrying a surjective morphism from
  an affine `Y` is affine as soon as `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)` is universally closed,
  equivalently as soon as `Γ(X, ⊤) ⟶ Γ(Y, ⊤)` is an integral ring map.
* `Stacks.AlgebraicGeometry.ChevalleyAffine.isAffine_of_isQuasiAffine_of_isIntegral_appTop`:
  the previous result written in the shape of the source statement of Stacks Tag 01YQ, with the
  two extra hypotheses displayed. It is not the statement of Tag 01YQ, which does not carry them.

## Route

Write `A = Γ(X, ⊤)`, `B = Γ(Y, ⊤)` and `φ = f.appTop : A ⟶ B`. Naturality of the unit of the
`Γ`-`Spec` adjunction gives `f ≫ X.toSpecΓ = Y.toSpecΓ ≫ Spec.map φ`, and `Y.toSpecΓ` is an
isomorphism because `Y` is affine. Hence:

* `Spec.map φ` is dominant, because `f` is surjective and `X.toSpecΓ` is dominant on a
  quasi-compact `X` (`AlgebraicGeometry.Scheme.ker_toSpecΓ`);
* a dominant universally closed morphism is surjective, so `Spec.map φ` is surjective and
  therefore so is `X.toSpecΓ`;
* a surjective open immersion is an isomorphism, and `X.toSpecΓ` is an open immersion exactly
  because `X` is quasi-affine.

## What is not done

**The source statement is not proved here.** [Stacks, Tag 01YQ] -- a Noetherian scheme
receiving a finite surjective morphism from an affine scheme is affine -- is *not* proved in
this file and is not stated here. What is proved is the implication from the source's four
hypotheses **together with two further hypotheses**, namely

1. `X` is quasi-affine, i.e. `AlgebraicGeometry.IsImmersion X.toSpecΓ` (the quasi-compactness
   half of `Scheme.IsQuasiAffine` does follow from `IsNoetherian X`); and
2. `Γ(X, ⊤) ⟶ Γ(Y, ⊤)` is integral, equivalently `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)` is
   universally closed.

Neither is available at this pin, and neither is a consequence of the four hypotheses by any
argument carried out here; both are consequences of the conclusion, so this file is a
*reduction* and not a proof. The source proves the statement by a different route: vanishing
of `H¹(X, ℱ)` for every coherent `ℱ`, obtained by dévissage [Stacks, Tag 01YM] from
[Stacks, Tag 01YO], [Stacks, Tag 01YP], [Stacks, Tag 089W] and [Stacks, Tag 01XB], and then
Serre's criterion [Stacks, Tag 01XF], [Stacks, Tag 01XG]. Of those, only Tag 01YP exists in
this repository
(`Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq`);
Serre's criterion, the coherent dévissage principle, Tag 01YO, Tag 089W and Tag 01XB are all
absent from both Mathlib and this repository, so the source's route is not available.

Also not done: the finiteness of `f` and the Noetherian hypothesis on `X` are *not used* by
the proofs below -- they are retained only in the final statement, to display it in the shape
of the source. Only `Surjective f`, `IsAffine Y` and `CompactSpace X` are used.

## References

* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ChevalleyAffine

variable {X Y : Scheme.{u}}

/-- A quasi-affine scheme whose canonical morphism to the spectrum of its global sections is
surjective is affine: that morphism is an open immersion by quasi-affineness, and a surjective
open immersion is an isomorphism. -/
theorem isAffine_of_isQuasiAffine_of_surjective_toSpecΓ (X : Scheme.{u}) [X.IsQuasiAffine]
    [Surjective X.toSpecΓ] : IsAffine X :=
  ⟨(isIso_iff_isOpenImmersion_and_surjective X.toSpecΓ).mpr ⟨inferInstance, inferInstance⟩⟩

/-- A scheme is affine if and only if it is quasi-affine and the canonical morphism to the
spectrum of its global sections is surjective. -/
theorem isAffine_iff_isQuasiAffine_and_surjective_toSpecΓ (X : Scheme.{u}) :
    IsAffine X ↔ X.IsQuasiAffine ∧ Surjective X.toSpecΓ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    exact ⟨inferInstance, inferInstance⟩
  · have := h.1
    have := h.2
    exact isAffine_of_isQuasiAffine_of_surjective_toSpecΓ X

/-- If `f : Y ⟶ X` has affine source and the morphism it induces on the spectra of global
sections is surjective, then `X ⟶ Spec Γ(X, ⊤)` is surjective. -/
theorem surjective_toSpecΓ_of_surjective_SpecMap_appTop (f : Y ⟶ X) [IsAffine Y]
    [Surjective (Spec.map f.appTop)] : Surjective X.toSpecΓ := by
  have : Surjective (f ≫ X.toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    infer_instance
  exact Surjective.of_comp (f := f) (g := X.toSpecΓ)

/-- For a surjective morphism `f : Y ⟶ X` with `Y` affine and `X` quasi-compact, the induced
morphism `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)` is dominant. -/
theorem isDominant_SpecMap_appTop (f : Y ⟶ X) [IsAffine Y] [Surjective f] [CompactSpace X] :
    IsDominant (Spec.map f.appTop) := by
  have : IsDominant (Y.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  exact IsDominant.of_comp (f := Y.toSpecΓ) (g := Spec.map f.appTop)

/-- A quasi-affine scheme `X` receiving a surjective morphism `f : Y ⟶ X` from an affine
scheme is affine, provided the induced morphism `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)` is universally
closed. -/
theorem isAffine_of_universallyClosed_SpecMap_appTop (f : Y ⟶ X) [IsAffine Y] [Surjective f]
    [X.IsQuasiAffine] [UniversallyClosed (Spec.map f.appTop)] : IsAffine X := by
  have := isDominant_SpecMap_appTop f
  have : Surjective (Spec.map f.appTop) := inferInstance
  have := surjective_toSpecΓ_of_surjective_SpecMap_appTop f
  exact isAffine_of_isQuasiAffine_of_surjective_toSpecΓ X

/-- A quasi-affine scheme `X` receiving a surjective morphism `f : Y ⟶ X` from an affine
scheme is affine, provided the ring map `Γ(X, ⊤) ⟶ Γ(Y, ⊤)` is integral. -/
theorem isAffine_of_isIntegral_appTop (f : Y ⟶ X) [IsAffine Y] [Surjective f]
    [X.IsQuasiAffine] (h : (Scheme.Hom.appTop f).hom.IsIntegral) : IsAffine X := by
  have : IsIntegralHom (Spec.map f.appTop) := IsIntegralHom.SpecMap_iff.mpr h
  exact isAffine_of_universallyClosed_SpecMap_appTop f

/-- **[Stacks, Tag 01YQ] with two extra hypotheses, which are not discharged here.** A
Noetherian scheme receiving a finite surjective morphism from an affine scheme is affine,
*provided* it is quasi-affine and the induced map on global sections is integral. The source
assumes neither of these; see the "what is not done" section of this file. Of the four
hypotheses of the source, only `Surjective f` and `IsAffine Y` are used, together with the
quasi-compactness contained in `Scheme.IsQuasiAffine`. -/
theorem isAffine_of_isQuasiAffine_of_isIntegral_appTop (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsAffine Y] [IsNoetherian X] [X.IsQuasiAffine]
    (h : (Scheme.Hom.appTop f).hom.IsIntegral) : IsAffine X :=
  isAffine_of_isIntegral_appTop f h

end Stacks.AlgebraicGeometry.ChevalleyAffine
