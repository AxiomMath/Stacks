module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured

/-!
# Multiplication by a section is a monomorphism on the closed-fibre member of a twist

The second clause of `Stacks.Algebraization.HasHilbertInductionStep` — the short exact sequences
of the induction step of [Stacks, Tag 0F27] — owes the monicity of both members of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`. The punctured-spectrum member is
`Stacks.Algebraization.CoherentTriple.mono_onPunctured_mulSectionTwistZ`. This file discharges
the closed-fibre member, which is the same corollary of
`Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` one scheme over: the
morphism is `tensorModulesMap (closedFibre A f) (𝟙 T.F₀) (mulSectionPowScheme _ L.F₀ σ₀ n)` by
the definition of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`, and the closed fibre
is `Spec(A/fA)`, locally Noetherian for `A` Noetherian.

## The closed point is not an associated point, and that is not a hypothesis

What `mono_tensorModulesMap_id_mulSectionPowScheme` asks for is nonvanishing of the section near
every point of `Ass(F₀)`. On the closed fibre `Ass(F₀)` can contain the closed point, and the
section pair cannot help there: the section `σ₀` the pair produces is the partner of `g^N x` for
a multiplier `g ∈ 𝔪` chosen by prime avoidance on the *punctured* spectrum
(`Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow`), and an element of the
maximal ideal vanishes at the closed point by definition — so no choice of multiplier makes `σ₀`
nonvanishing there, and for `N ≥ 1` and a closed fibre of positive dimension the partner of
`g^N x` must in fact vanish at the closed point, the nonvanishing locus of a section of an
invertible module on `Spec(A/fA)` being a basic open and hence either everything or disjoint
from the closed point.

The obligation at the closed point is discharged instead by the **opening reduction** of the
induction step, which is where the source puts it: the triple that gets twisted is not `T` but
the quotient `T' = (F, F₀/G₀, α)` by the sections of `F₀` supported at the closed point, and
`Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple` says the
closed point is not an associated point of `F₀/G₀`. So the hypothesis is **not** a property of
the triple to be assumed: `mono_onClosedFibre_mulSectionTwistZ_quotientTriple` below asks for
nonvanishing only away from the closed point, which is nonvanishing over the punctured closed
fibre.

## Main results

* `Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ`: **the closed-fibre
  member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a monomorphism**, given a
  section of the invertible triple's closed-fibre member that does not vanish near any associated
  point of `T.F₀`.
* `Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ_of_notMem_closedPoint`:
  the same with the nonvanishing asked for only away from the closed point, for a triple whose
  closed-fibre member has no associated point there.
* `Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ_quotientTriple`:
  **the same for the triple the opening reduction produces, with no hypothesis at the closed
  point at all.**

## What is still owed

The nonvanishing away from the closed point. `σ₀` corresponds over the punctured closed fibre to
`σ`, and `σ` avoids `Ass(T.F) ∪ Ass(T.F / f T.F)` by
`Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints_depthFree`; carrying
that to `Ass(T.F₀)` over the punctured closed fibre needs the associated points of the inverse
image of `F₀` along `Stacks.Algebraization.puncturedClosedFibre`, read across `T.alpha`, together
with the identification of `Stacks.NonvanishingOpen.nonvanishingOpen` with
`Stacks.SheafOfModules.nonvanishingLocus` that the module docstring of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured` records as not done.
That identification is owed on the punctured spectrum too, so it is one obligation for both
members and not a separate one here.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

/-- **The closed-fibre member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a
monomorphism**, given a section of the invertible triple's closed-fibre member that does not
vanish near any associated point of `T.F₀`.

This is `Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` at the closed fibre
and `σ₀`, exactly as
`Stacks.Algebraization.CoherentTriple.mono_onPunctured_mulSectionTwistZ` is that lemma at the
punctured spectrum and `σ`. -/
public theorem CoherentTriple.mono_onClosedFibre_mulSectionTwistZ (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) {N₀ : (closedFibre A f).Modules}
    (hq : ((T.twistZ L hL n).F₀).IsQuasicoherent)
    (hq' : (tensorModules (closedFibre A f) ((T.twistZ L hL n).F₀) L.F₀).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((closedFibre A f).toRingedSpace)).presheaf,
        (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints T.F₀,
      ∃ W : (closedFibre A f).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (closedFibre A f).toRingedSpace) L.F₀ (L.F₀.unitHomEquiv σ₀)) :
    Mono (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onClosedFibre :=
  let := hL.invertible_F₀
  mono_tensorModulesMap_id_mulSectionPowScheme T.F₀ L.F₀ n σ₀ hq hq' ψ hW

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
  [IsLocalRing (A ⧸ Ideal.span {f})]

/-- **The closed-fibre member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a
monomorphism when the closed point is not an associated point of `T.F₀`**, the nonvanishing of
the section being asked for only away from the closed point — that is, over the punctured closed
fibre. -/
public theorem CoherentTriple.mono_onClosedFibre_mulSectionTwistZ_of_notMem_closedPoint
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) {N₀ : (closedFibre A f).Modules}
    (hq : ((T.twistZ L hL n).F₀).IsQuasicoherent)
    (hq' : (tensorModules (closedFibre A f) ((T.twistZ L hL n).F₀) L.F₀).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((closedFibre A f).toRingedSpace)).presheaf,
        (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hcp : ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f})))
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints T.F₀,
      x ≠ IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) →
      ∃ W : (closedFibre A f).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (closedFibre A f).toRingedSpace) L.F₀ (L.F₀.unitHomEquiv σ₀)) :
    Mono (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onClosedFibre :=
  T.mono_onClosedFibre_mulSectionTwistZ L hL σ σ₀ hcompat n hq hq' ψ
    fun x hx => hW x hx fun hxc => hcp (hxc ▸ hx)

/-- **The closed-fibre member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a
monomorphism for the triple the opening reduction of [Stacks, Tag 0F27] produces**, with no
hypothesis at the closed point at all: the closed point is not an associated point of `F₀/G₀` by
`Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple`, so only
the nonvanishing of `σ₀` over the punctured closed fibre is left to produce. -/
public theorem CoherentTriple.mono_onClosedFibre_mulSectionTwistZ_quotientTriple
    (hf : f ∈ maximalIdeal A) (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) {N₀ : (closedFibre A f).Modules}
    (hq : (((T.quotientTriple hf).twistZ L hL n).F₀).IsQuasicoherent)
    (hq' : (tensorModules (closedFibre A f)
      (((T.quotientTriple hf).twistZ L hL n).F₀) L.F₀).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((closedFibre A f).toRingedSpace)).presheaf,
        (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints (T.quotientTriple hf).F₀,
      x ≠ IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) →
      ∃ W : (closedFibre A f).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (closedFibre A f).toRingedSpace) L.F₀ (L.F₀.unitHomEquiv σ₀)) :
    Mono ((T.quotientTriple hf).mulSectionTwistZ L hL σ σ₀ hcompat n).onClosedFibre :=
  (T.quotientTriple hf).mono_onClosedFibre_mulSectionTwistZ_of_notMem_closedPoint L hL σ σ₀
    hcompat n hq hq' ψ (T.not_isAssociatedPoint_closedPoint_quotientTriple hf) hW

end

end Stacks.Algebraization

end
