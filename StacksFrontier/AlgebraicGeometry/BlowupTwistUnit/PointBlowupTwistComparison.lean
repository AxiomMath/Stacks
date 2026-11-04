module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCurveDifferentialsDichotomy
public import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.RegularSurfaceCentre
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.TopFormsNormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twist comparison at a blowup in a closed point, in the spelling the 0B4T induction uses

The induction of [Stacks, Tag 0B4T] needs, at each blowup `b : X' ⟶ X` in a closed point, the
direct image of the reflexive hull of the top relative forms:

`b_*((Ω^n_{X'/S₀})^{**}) ≅ (Ω^n_{X/S₀})^{**}`.

The two halves of that computation are proved elsewhere in the tree but are spelled differently
from one another and from the induction. This file supplies the bridges and assembles the half
that is available unconditionally.

## The spellings

`Ω^n_{X/S}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`, the degree-`n` piece of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra`, while the dichotomy of
[Stacks, Tag 0B3T] is stated at `AlgebraicGeometry.Scheme.Modules.exteriorPower` of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`. Since the forms algebra of a morphism *is*
the exterior algebra of its sheaf of relative differentials, the two are the same module, and
`relativeDifferentialForms_eq_exteriorPower_relativeDifferentials` records the equality. It is an
unfolding and nothing more, but without it the dichotomy and the induction are statements about
syntactically different modules.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `relativeDifferentialForms_eq_exteriorPower_relativeDifferentials` and
  `hullForms_eq_reflexiveHull_exteriorPower_relativeDifferentials`: the two spellings of
  `Ω^n_{X/S}` and of `(Ω^n_{X/S})^{**}` agree.
* `nonempty_tensorIso_or_nonempty_iso_hullForms_residuePoint`: **the dichotomy of
  [Stacks, Tag 0B3T] for the blowup of a regular local surface in its closed point, in the
  `hullForms` spelling the 0B4T induction uses.**
* `isIso_twistUnderivedMap_top_vanishingIdeal_singleton`: **`ℰ ≅ b_*(b^*ℰ)` for the blowup of an
  integral regular Noetherian surface at a closed point** and `ℰ` finite locally free — the
  untwisted alternative of the dichotomy, with no hypothesis beyond regularity and the dimension.
* `isIso_twistUnderivedMap_exceptionalIdeal_centre`: **`ℰ ≅ b_*(b^*ℰ ⊗ 𝒪_{X'}(E))` for the blowup
  of the spectrum of a regular local ring of dimension two in its maximal ideal** and `ℰ` finite
  locally free — the twisted alternative.

## Implementation notes

Both assembled results are the *underived* direct image,
`Stacks.DeRham.TwistDerived.twistUnderivedMap`, which is where the projection formula of
[Stacks, Tag 01E8] in degree zero lands
(`Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap`); no derived category occurs in their
statements, so neither crosses between the two models of it that the tree carries.

The first is global — a closed point of an integral regular Noetherian surface — because its one
input, `𝒪_X ≅ b_*𝒪_{X'}`, is proved globally
(`AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton`, the
blowup being a modification of a normal integral scheme), together with the invertibility of the
canonical section of `𝒪_{X'}(⊤)`. The second is only over the spectrum of a local ring, because
its input `𝒪_X ≅ b_*𝒪_{X'}(E)` is
`Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_regularLocal`, whose proof reads the
closed point through the fact that it has no proper open neighbourhood.

**No `@[stacks]` attribute is attached to anything here.** [Stacks, Tag 0B4T] asserts the
existence of a map `(Ω^r_{X/Spec A₀})^{**} ⟶ ω_X` along a sequence of blowups in closed points;
what is below is one of the inputs that statement consumes, in two of its branches, and not the
statement itself. The direct-image computation of the hull that the induction actually asks for
needs, beyond this, the dichotomy carried from the presentation
`Stacks.Blowup.blowUp` to `AlgebraicGeometry.blowUp`, the identification of
`(⋀^r b^*Ω)^{**}` with `b^*((⋀^r Ω)^{**})`, and the twisted alternative over a base that is not
the spectrum of a local ring.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The two spellings of the top forms -/

/-- **`Ω^n_{X/S}` is the `n`-th exterior power of `Ω_{X/S}`.** The algebra of relative
differential forms of a morphism is by definition the exterior algebra of its sheaf of relative
differentials, so the degree-`n` piece of the one is the `n`-th exterior power of the other.

The equality is an unfolding, but the two spellings are what separate the dichotomy of
[Stacks, Tag 0B3T], stated at `AlgebraicGeometry.Scheme.Modules.exteriorPower`, from the
induction of [Stacks, Tag 0B4T], stated at
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`. -/
@[ega "IV 16.6.1"]
theorem relativeDifferentialForms_eq_exteriorPower_relativeDifferentials {X S : Scheme.{u}}
    (q : X ⟶ S) (n : ℤ) :
    Scheme.Hom.relativeDifferentialForms q n =
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q) n :=
  rfl

/-- **`(Ω^n_{W/S₀})^{**}` in the two spellings.** The reflexive hull of the top forms of
`W ⟶ S ⟶ S₀`, which is `Stacks.BlowupTwistUnit.hullForms`, is the reflexive hull of the `n`-th
exterior power of `Ω_{W/S₀}`: `relativeDifferentialForms_eq_exteriorPower_relativeDifferentials`
under `reflexiveHull`. -/
theorem hullForms_eq_reflexiveHull_exteriorPower_relativeDifferentials {S₀ S W : Scheme.{u}}
    (p : S ⟶ S₀) (n : ℤ) (h : W ⟶ S) :
    hullForms p n h =
      reflexiveHull (Scheme.Modules.exteriorPower
        (Scheme.Hom.relativeDifferentials (h ≫ p)) n) :=
  rfl

/-! ### The dichotomy in the spelling of the induction -/

/-- **The dichotomy of [Stacks, Tag 0B3T] for the blowup of a regular local surface in its closed
point, in the `hullForms` spelling.** For `(A, 𝔪)` a regular local ring of dimension two,
`b : X ⟶ S = Spec A` the blowing up of `S` in `𝔪` with exceptional divisor `E`, and `q : S ⟶ S₀`
with `b^*Ω_{S/S₀}` and `Ω_{X/S₀}` coherent and both of rank `r` on a nonempty open,

`(Ω^r_{X/S₀})^{**} ≅ ((⋀^r b^*Ω_{S/S₀})^{**})(E)` or `(Ω^r_{X/S₀})^{**} ≅ (⋀^r b^*Ω_{S/S₀})^{**}`.

This is `Stacks.Blowup.nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_residuePoint`
with its target read through
`Stacks.BlowupTwistUnit.hullForms_eq_reflexiveHull_exteriorPower_relativeDifferentials`, which is
the side the induction of [Stacks, Tag 0B4T] consumes. The source of each alternative is left at
the exterior power of the inverse image, which is not the inverse image of a hull and so has no
`hullForms` spelling. -/
theorem nonempty_tensorIso_or_nonempty_iso_hullForms_residuePoint (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    {S₀ : Scheme.{u}} (q : Spec (CommRingCat.of A) ⟶ S₀) (r : ℕ)
    [((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase
        (Stacks.Blowup.residuePoint A).ker)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker ≫ q)).IsCoherent]
    (U : (Stacks.Blowup.blowUp (Stacks.Blowup.residuePoint A).ker).Opens)
    (hU : ∃ x : Stacks.Blowup.blowUp (Stacks.Blowup.residuePoint A).ker, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase
        (Stacks.Blowup.residuePoint A).ker)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Stacks.Blowup.blowUp (Stacks.Blowup.residuePoint A).ker).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (Stacks.Blowup.blowUp (Stacks.Blowup.residuePoint A).ker).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (Stacks.Blowup.blowUp
                  (Stacks.Blowup.residuePoint A).ker).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (Stacks.Blowup.exceptionalIdeal (Stacks.Blowup.residuePoint A).ker))).obj
        (reflexiveHull (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      hullForms q (r : ℤ) (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker)) ∨
    Nonempty
      (reflexiveHull (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      hullForms q (r : ℤ) (Stacks.Blowup.blowUpToBase (Stacks.Blowup.residuePoint A).ker)) :=
  Stacks.Blowup.nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_residuePoint
    A hdim q r U hU

/-! ### The direct image of a twisted inverse image at a blowup in a closed point -/

/-- **`ℰ ≅ b_*(b^*ℰ ⊗ 𝒪_{X'}(⊤))` for the blowing up `b : X' ⟶ X` of an integral regular
Noetherian surface at a closed point**, for every finite locally free `ℰ`. This is the untwisted
alternative of the dichotomy of [Stacks, Tag 0B3T], where the exceptional exponent is `0` and
`𝒪_{X'}(0 · E)` is the structure sheaf.

Nothing is assumed beyond regularity and the dimension. By
`Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap`, the projection formula of
[Stacks, Tag 01E8] in degree zero, the only input is the invertibility of `𝒪_X ⟶ b_*𝒪_{X'}(⊤)`,
and that factors by `Stacks.DeRham.TwistDerived.twistUnitComparison_eq` into `𝒪_X ⟶ b_*𝒪_{X'}`,
invertible by
`AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton`
([Stacks, Tag 0AY8], the blowup being a modification of a normal integral scheme), followed by
`b_*` of the canonical section of `𝒪_{X'}(⊤)`, invertible by
`Stacks.DeRham.TwistDerived.isIso_canonicalSectionHom_top`. -/
theorem isIso_twistUnderivedMap_top_vanishingIdeal_singleton {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNoetherian X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X = 2) (w : X) (hw : IsClosed ({w} : Set X))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsIso (Stacks.DeRham.TwistDerived.twistUnderivedMap
      (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)))
      ⊤ E) := by
  have := Stacks.DeRham.TwistDerived.isIso_canonicalSectionHom_top
    (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)))
  refine Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap _ _ E ?_
  rw [Stacks.DeRham.TwistDerived.twistUnitComparison_eq]
  exact IsIso.comp_isIso'
    (AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton
      hreg hdim w hw)
    (Functor.map_isIso _ _)

/-- **`ℰ ≅ b_*(b^*ℰ ⊗ 𝒪_{X'}(E))` for the blowing up `b : X' ⟶ Spec A` of the spectrum of a
regular local ring of dimension two in its maximal ideal**, for every finite locally free `ℰ`.
This is the twisted alternative of the dichotomy of [Stacks, Tag 0B3T], where the exceptional
exponent is `1`.

By `Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap` the only input is the invertibility of
`𝒪_{Spec A} ⟶ b_*𝒪_{X'}(E)`, which is
`Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_regularLocal` — part (4) of
[Stacks, Tag 0AGS] in degree `-1`, read at the closed point. Unlike the untwisted alternative
this is stated over the spectrum of a local ring and not at an arbitrary closed point of a
regular surface, that being the form of the input used here; the same input at an arbitrary
closed point is
`Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_pointIdeal`. -/
theorem isIso_twistUnderivedMap_exceptionalIdeal_centre (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (E : (Spec (CommRingCat.of A)).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsIso (Stacks.DeRham.TwistDerived.twistUnderivedMap
      (AlgebraicGeometry.blowUpToBase (centre A))
      (AlgebraicGeometry.exceptionalIdeal (centre A)) E) :=
  Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap _ _ E
    (isIso_exceptionalTwistComparison_regularLocal A hdim)

end Stacks.BlowupTwistUnit

end
