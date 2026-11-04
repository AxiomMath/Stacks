module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStepHypotheses
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.PushforwardLadder
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.SpecialFibreTransport

/-!
# The reduction of the constructed family, as an ideal sheaf

The kernel of the comparison `𝒪_V ⟶ g_*(𝒪_U/𝔪𝒪_U)` on the sections over an affine open is `𝔪`
times the sections. This file deduces the equality of ideal sheaves

```
(i_Y).ker = 𝔪 𝒪_V
```

for the closed immersion `i_Y : Y ⟶ V`, that is, the reduction `𝒪_V/𝔪_A 𝒪_V = 𝒪_Y` read as a
closed subscheme.

## Main results

* `Stacks.BaseAdicFiltration.pushforwardAdicProj_one_comp_eq`: the comparison at `n = 1`, composed
  with an isomorphism, **is** the structure-sheaf comparison of `i_Y` composed with an
  isomorphism.
* `Stacks.BaseAdicFiltration.app_pushforwardAdicProj_one_eq_zero_iff_app_eq_zero`: the comparison
  at `n = 1` and the comorphism of `i_Y` have the same kernel on the sections over every open.
* `Stacks.BaseAdicFiltration.ker_eq_baseIdeal_of_pushforwardAdicProj`: **the reduction
  statement**, as an equality of ideal sheaves.
* `Stacks.BaseAdicFiltration.flat_and_ker_eq_baseIdeal_of_specialFibre`: flatness and the
  reduction together, assuming `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.BaseAdicFiltration

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U V X Y : Scheme.{u}}
  (p : U ⟶ Spec (CommRingCat.of A)) (pV : V ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (iX : X ⟶ U) [IsClosedImmersion iX] (iY : Y ⟶ V) [IsClosedImmersion iY]
  (fXY : X ⟶ Y) (g : U ⟶ V)

omit [IsClosedImmersion iY] in
/-- **The comparison at `n = 1` is the structure-sheaf comparison of `i_Y`, up to isomorphisms.**
Composing `𝒪_V ⟶ g_*(𝒪_U/I𝒪_U)` with the identification of the quotient as `(i_X)_*𝒪_X` and the
identification of the two composite direct images around the square gives
`𝒪_V ⟶ (i_Y)_*𝒪_Y ⟶ (i_Y)_*(f_*𝒪_X)`. -/
theorem pushforwardAdicProj_one_comp_eq (hkX : iX.ker = baseIdeal p I)
    (hsq : iX ≫ g = fXY ≫ iY) :
    pushforwardAdicProj p g I 1 ≫
        ((Scheme.Modules.pushforward g).map
            (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
          (AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf)) =
      Scheme.Modules.unitToPushforwardUnit iY ≫
        (Scheme.Modules.pushforward iY).map
          (Scheme.Modules.unitToPushforwardUnit fXY) := by
  have hinner : (Scheme.Modules.pushforward g).map
        (adicProj p I 1 (SheafOfModules.unit U.ringCatSheaf)) ≫
      ((Scheme.Modules.pushforward g).map
          (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf)) =
      (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit iX) ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf))
        ((Functor.map_comp _ _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward g).map
            (adicProj_comp_specialFibreIsoPushforwardUnit p I iX hkX))))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫ φ) hinner).trans
      (structureUnitHom_comp_pushforwardSquareIso hsq))

/-- An invertible morphism `φ` of sheaves of modules detects zero on the sections over an open:
`φ x = 0 ↔ x = 0`. -/
theorem app_eq_zero_iff_of_isIso {M N : V.Modules} (φ : M ⟶ N)
    (hφ : IsIso (C := V.Modules) φ) (O : V.Opens) (x : Γ(M, O)) :
    Scheme.Modules.Hom.app φ O x = 0 ↔ x = 0 := by
  have := hφ
  refine ⟨fun hx => (ConcreteCategory.bijective_of_isIso (φ.app O)).1 ?_, fun hx => hx ▸ map_zero _⟩
  rw [hx, map_zero]

omit [IsClosedImmersion iY] in
/-- **The comparison at `n = 1` and the comorphism of `i_Y` have the same kernel on sections**,
provided `i_X` cuts out `I 𝒪_U`, `i_X ≫ g = f ≫ i_Y`, and the structure-sheaf comparison
`𝒪_Y ⟶ f_*𝒪_X` is invertible. -/
theorem app_pushforwardAdicProj_one_eq_zero_iff_app_eq_zero (hkX : iX.ker = baseIdeal p I)
    (hsq : iX ≫ g = fXY ≫ iY)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (O : V.Opens) (s : Γ(V, O)) :
    (pushforwardAdicProj p g I 1).app O s = 0 ↔ (iY.app O).hom s = 0 := by
  have := h0
  have hi1 : IsIso (C := V.Modules) ((Scheme.Modules.pushforward g).map
      (specialFibreIsoPushforwardUnit p I iX hkX).hom) := inferInstance
  have hi2 : IsIso (C := V.Modules) ((AffinePushforward.pushforwardSquareIso hsq).hom.app
      (SheafOfModules.unit X.ringCatSheaf)) :=
    inferInstanceAs (IsIso (C := V.Modules) (((AffinePushforward.pushforwardSquareIso hsq).app
      (SheafOfModules.unit X.ringCatSheaf)).hom))
  have hi3 : IsIso (C := V.Modules) ((Scheme.Modules.pushforward iY).map
      (Scheme.Modules.unitToPushforwardUnit fXY)) := inferInstance
  have hkey : ∀ t : Γ(V, O),
      ((AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf)).app O
          (((Scheme.Modules.pushforward g).map
              (specialFibreIsoPushforwardUnit p I iX hkX).hom).app O
            ((pushforwardAdicProj p g I 1).app O t)) =
        ((Scheme.Modules.pushforward iY).map
            (Scheme.Modules.unitToPushforwardUnit fXY)).app O
          ((Scheme.Modules.unitToPushforwardUnit iY).app O t) := fun t =>
    congrArg (fun φ : Scheme.unitModule V ⟶ (Scheme.Modules.pushforward iY).obj
          ((Scheme.Modules.pushforward fXY).obj (SheafOfModules.unit X.ringCatSheaf)) =>
        Scheme.Modules.Hom.app φ O (t : Γ(Scheme.unitModule V, O)))
      (pushforwardAdicProj_one_comp_eq p I iX iY fXY g hkX hsq)
  refine Iff.trans ((app_eq_zero_iff_of_isIso _ hi1 O _).symm.trans
    (app_eq_zero_iff_of_isIso _ hi2 O _).symm) ?_
  exact (iff_of_eq (congrArg (fun z => z = 0) (hkey s))).trans
    (app_eq_zero_iff_of_isIso _ hi3 O _)

/-- **The reduction statement, as an equality of ideal sheaves.** Let `p : U ⟶ Spec A` be flat
over an Artinian local base with `𝔪^(N + 1) = 0`, and `g : U ⟶ V` a morphism over `Spec A` with
`𝒪_V = g_*𝒪_U`. Assume the direct images under `g` of the graded short exact sequences of the
`𝔪`-adic filtration of `𝒪_U` are short exact, `g_*(𝒪_U/𝔪𝒪_U)` is quasi-coherent, `i_X : X ⟶ U`
cuts out `𝔪 𝒪_U`, `i_X ≫ g = f ≫ i_Y` and `𝒪_Y ⟶ f_*𝒪_X` is invertible. Then the closed
immersion `i_Y : Y ⟶ V` is cut out by `𝔪 𝒪_V`. -/
theorem ker_eq_baseIdeal_of_pushforwardAdicProj [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] (hg : g ≫ pV = p)
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (N : ℕ) (hN : IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥)
    (hSE : ∀ n, ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (Scheme.unitModule U)).map (Scheme.Modules.pushforward g)).ShortExact)
    (hqc : ((Scheme.Modules.pushforward g).obj
      (adicQuotient p (IsLocalRing.maximalIdeal A) 1 (Scheme.unitModule U))).IsQuasicoherent)
    (hkX : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A))
    (hsq : iX ≫ g = fXY ≫ iY)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY)) :
    iY.ker = baseIdeal pV (IsLocalRing.maximalIdeal A) := by
  refine Scheme.IdealSheafData.ext (funext fun O => ?_)
  let := sectionsAlgebra pV O.1
  have hlad := (flat_sections_and_app_pushforwardAdicProj_one_eq_zero_iff p pV hg hc N hN
    hSE hqc O.1 O.2).2
  have hbridge := app_pushforwardAdicProj_one_eq_zero_iff_app_eq_zero p
    (IsLocalRing.maximalIdeal A) iX iY fXY g hkX hsq h0 O.1
  have hdef : (algebraMap A Γ(V, O.1)) =
      (pV.appLE ⊤ O.1 le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom := rfl
  refine SetLike.ext fun s => ?_
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, baseIdeal_ideal, ← hdef]
  refine Iff.trans (hbridge s).symm (Iff.trans (hlad s) ?_)
  rw [Ideal.smul_top_eq_map]
  exact Submodule.restrictScalars_mem A _ s

/-- **Flatness and the reduction together.** Let
`p : U ⟶ Spec A` be flat over an Artinian local base, `i_X : X ⟶ U` cut out its special fibre,
`g : U ⟶ V` a morphism over `Spec A` with `𝒪_V = g_*𝒪_U`, and `i_Y : Y ⟶ V` a closed immersion
with `i_X ≫ g = f ≫ i_Y`.  If `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`, then `V` is flat over `Spec A`
and `i_Y` is cut out by `𝔪 𝒪_V`. -/
theorem flat_and_ker_eq_baseIdeal_of_specialFibre [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] (hg : g ≫ pV = p)
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (hkX : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A))
    (hsq : iX ≫ g = fXY ≫ iY)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    AlgebraicGeometry.Flat pV ∧
      iY.ker = baseIdeal pV (IsLocalRing.maximalIdeal A) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥ := by
    obtain ⟨M, hM⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹IsArtinianRing A›
    exact ⟨M, by rw [pow_succ, hM, zero_mul, Submodule.zero_eq_bot]⟩
  have hSE : ∀ n, ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (Scheme.unitModule U)).map (Scheme.Modules.pushforward g)).ShortExact := fun n =>
    shortExact_map_pushforward_gradedShortComplex_unit p n g
      (isZero_rightDerived_one_specialFibre_of_isZero p (IsLocalRing.maximalIdeal A) iX g iY
        fXY hkX hsq.symm hR)
  have hqc : ((Scheme.Modules.pushforward g).obj
      (adicQuotient p (IsLocalRing.maximalIdeal A) 1
        (Scheme.unitModule U))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforward g).mapIso
        (specialFibreIsoPushforwardUnit p (IsLocalRing.maximalIdeal A) iX hkX)).symm
      (isQuasicoherent_pushforward_pushforward_unit_of_square fXY iX iY g hsq h0)
  exact ⟨flat_of_pushforwardAdicProj p pV hg hc N hN hSE hqc,
    ker_eq_baseIdeal_of_pushforwardAdicProj p pV iX iY fXY g hg hc N hN hSE hqc hkX hsq h0⟩

end Stacks.BaseAdicFiltration

end
