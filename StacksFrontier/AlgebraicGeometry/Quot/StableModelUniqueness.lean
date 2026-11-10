module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Models.ModelHomUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes

/-!
# Uniqueness of stable models (towards Stacks 0E97)

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth proper curve
over `K` with `K = H⁰(C, 𝒪_C)` and genus `g`. [Stacks, Tag 0E97] says that two models `X`, `X'`
of `C` which are stable families of genus `g` curves over `R` are isomorphic by a unique
isomorphism of models.

This file states the two halves at the source's hypotheses as far as the library carries them.

* The uniqueness half holds outright: a stable family is proper, hence separated, and morphisms of
  models into a separated model are unique
  (`Stacks.Models.subsingleton_isModelHom_iso_of_isStableFamilyOfSchemesOfGenus`).
* The step of the existence half that goes through [Stacks, Tag 0E89]: two proper models
  receiving morphisms of models from a common proper model `W`, whose special fibres are
  identified compatibly and the first of which satisfies `𝒪 = c_* 𝒪` and `R¹c_* 𝒪 = 0` on special
  fibres, are isomorphic by a unique isomorphism of models. Over a complete discrete valuation
  ring this is `Stacks.Models.existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete`,
  from the complete case of 0E89
  (`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete`). It is
  UNREGISTERED: it takes [Stacks, Tag 0A42] as the explicit hypothesis `h0A42`.

The full statement, existence and uniqueness, is
`Stacks.Models.existsUnique_isModelHom_iso_of_isStableFamilyOfSchemesOfGenus`, which compares
both models through the minimal model and needs neither the complete case of 0E89 nor 0A42.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDiscreteValuationRing R] in
/-- **The uniqueness half of [Stacks, Tag 0E97].** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth proper curve over `K` with `K = H⁰(C, 𝒪_C)` and genus `g`. If
`X` and `X'` are models of `C` which are stable families of genus `g` curves over `R`, there is at
most one isomorphism of models `X ≅ X'`. -/
theorem subsingleton_isModelHom_iso_of_isStableFamilyOfSchemesOfGenus (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (C_to_K : C ⟶ Spec (.of K)) [IsCurve K C_to_K] [Smooth C_to_K] [IsProper C_to_K]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)] (g : ℕ) (_hg : genus C_to_K = g)
    {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    {e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hX : IsModel C_to_K p e) (_hX' : IsModel C_to_K p' e')
    (_hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR)
    (hst' : IsStableFamilyOfSchemesOfGenus B hZ g p' hR) :
    {f : X ≅ X' | IsModelHom p p' e e' f.hom}.Subsingleton := by
  have : IsProper p' := hst'.isProper
  exact subsingleton_isModelHom_iso hX

/-- **The step of [Stacks, Tag 0E97] that goes through [Stacks, Tag 0E89], over a complete
discrete valuation ring.** Let `R` be a complete discrete valuation ring with residue field `κ`
and closed point `s`, let `W`, `X`, `X'` be proper models of `V` and let `c : W ⟶ X`,
`c' : W ⟶ X'` be morphisms of models. If the special fibres `Xₛ`, `X'ₛ` are identified over `κ`
by an isomorphism `φ` with `cₛ ≫ φ = c'ₛ`, and `𝒪_{Xₛ} ⟶ cₛ,* 𝒪_{Wₛ}` is an isomorphism with
`R¹cₛ,* 𝒪_{Wₛ} = 0`, then there is a unique isomorphism of models `X ≅ X'`.

UNREGISTERED: [Stacks, Tag 0A42] enters as the hypothesis `h0A42`, the statement of
`AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap` without its hypotheses `halg`
and `hrig`. -/
theorem existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete
    (h0A42 : ∀ (A : Type u) [CommRing A] (I : Ideal A) {X Y : Scheme.{u}} [IsNoetherianRing A]
      (_hcomplete : IsAdicComplete I A) (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A))
      [IsProper fX] [IsSeparated fY] [LocallyOfFiniteType fY] [QuasiCompact fY]
      (g : ∀ n, adicBaseChange A I fX n ⟶ adicBaseChange A I fY n)
      (_g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι A I n) =
        pullback.snd fX (adicThickeningι A I n))
      (_g_compatible : ∀ n, adicBaseChangeSucc A I fX n ≫ g (n + 1) =
        g n ≫ adicBaseChangeSucc A I fY n),
      ∃! algebraization : {h : X ⟶ Y // h ≫ fY = fX},
        ∀ n, adicBaseChangeMap A I algebraization.1 algebraization.2 n = g n)
    (hc : IsAdicComplete (maximalIdeal R) R)
    {V W X X' : Scheme.{u}} {v : V ⟶ Spec (.of K)} {pW : W ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)}
    (hW : IsModel v pW eW) (hX : IsModel v p e) (hX' : IsModel v p' e')
    [IsProper pW] [IsProper p] [IsProper p']
    {c : W ⟶ X} {c' : W ⟶ X'} (hcX : IsModelHom pW p eW e c) (hcX' : IsModelHom pW p' eW e' c')
    (φ : pullback p (ContractionUniquenessComplete.closedPoint R) ≅
      pullback p' (ContractionUniquenessComplete.closedPoint R))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : ContractionUniquenessComplete.specialMap pW p c hcX.1 ≫ φ.hom =
      ContractionUniquenessComplete.specialMap pW p' c' hcX'.1)
    (h0 : IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint R)).Modules)
      (Scheme.Modules.unitToPushforwardUnit
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback pW (ContractionUniquenessComplete.closedPoint R)).ringCatSheaf))) :
    ∃! f : X ≅ X', IsModelHom p p' e e' f.hom := by
  have : Flat pW := hW.1
  have : Flat p := hX.1
  have : Flat p' := hX'.1
  obtain ⟨ψ, hψ, hcψ, -⟩ := exists_iso_comp_eq_of_specialFibre_of_isAdicComplete h0A42 hc pW p p'
    c hcX.1 c' hcX'.1 φ hφ hφc h0 hR
  exact existsUnique_isModelHom_iso_of_comp_eq hX hcX hcX' ψ hψ hcψ

/-- **The step of [Stacks, Tag 0E97] that goes through [Stacks, Tag 0E89], over a complete
discrete valuation ring, with no further input.** Let `R` be a complete discrete valuation ring
with residue field `κ` and closed point `s`, let `W`, `X`, `X'` be proper models of `V` and let
`c : W ⟶ X`, `c' : W ⟶ X'` be morphisms of models. If the special fibres `Xₛ`, `X'ₛ` are identified
over `κ` by an isomorphism `φ` with `cₛ ≫ φ = c'ₛ`, and `𝒪_{Xₛ} ⟶ cₛ,* 𝒪_{Wₛ}` is an isomorphism
with `R¹cₛ,* 𝒪_{Wₛ} = 0`, then there is a unique isomorphism of models `X ≅ X'`.

This is `Stacks.Models.existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete` with
[Stacks, Tag 0A42] supplied by
`AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap_holds`. -/
theorem existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete_holds
    (hc : IsAdicComplete (maximalIdeal R) R)
    {V W X X' : Scheme.{u}} {v : V ⟶ Spec (.of K)} {pW : W ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)}
    (hW : IsModel v pW eW) (hX : IsModel v p e) (hX' : IsModel v p' e')
    [IsProper pW] [IsProper p] [IsProper p']
    {c : W ⟶ X} {c' : W ⟶ X'} (hcX : IsModelHom pW p eW e c) (hcX' : IsModelHom pW p' eW e' c')
    (φ : pullback p (ContractionUniquenessComplete.closedPoint R) ≅
      pullback p' (ContractionUniquenessComplete.closedPoint R))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : ContractionUniquenessComplete.specialMap pW p c hcX.1 ≫ φ.hom =
      ContractionUniquenessComplete.specialMap pW p' c' hcX'.1)
    (h0 : IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint R)).Modules)
      (Scheme.Modules.unitToPushforwardUnit
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (ContractionUniquenessComplete.specialMap pW p c hcX.1)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback pW (ContractionUniquenessComplete.closedPoint R)).ringCatSheaf))) :
    ∃! f : X ≅ X', IsModelHom p p' e e' f.hom :=
  existsUnique_isModelHom_iso_of_specialFibre_of_isAdicComplete
    (@fun A _ I _ _ _ hcA fX fY _ _ _ _ g go gc =>
      AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap_holds A I hcA fX fY g go gc)
    hc hW hX hX' hcX hcX' φ hφ hφc h0 hR

end Stacks.Models

end
