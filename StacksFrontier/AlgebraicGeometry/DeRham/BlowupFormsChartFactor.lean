module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartMono
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineFormsMapFactor
public import StacksFrontier.AlgebraicGeometry.Modules.CenterFactorization

/-!
# The pole bound of Stacks 0G5G on a standard chart, at the level of sheaves

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` —
a ring `R`, `S = Spec(R)`, the coordinate closed immersion `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the
blowup `b : L ⟶ X` of `X` along `Z` — the first canonical map of [Stacks, Tag 0G5G] is
`φ : b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` (`Stacks.DeRham.blowupFormsPullbackMap`).

**This file proves that the inverse image of `φ` along a standard chart admits multiplication by
`y_i^{n-1}` as a factorisation**, which is the pole bound of the source read on that chart:

`Θ ≫ j^*φ = y_i^{n-1} · id`.

The ring-level content is `Stacks.Kaehler.exists_comp_exteriorPower_map_blowupChartMapBaseChange`,
the affine-local criterion turning it into a statement about sheaves is
`AffineDifferentialForms.exists_comp_relativeDifferentialFormsMap_specTower` (in the namespace
`Stacks.AlgebraicGeometry`), and what this file supplies is the passage from the second to the
first.

## Main results

* `Stacks.DeRham.appTop_specTowerTop_coordinateChartPoleSection`: the upper edge of the chart's
  ring tower fixes `y_i^{n-1}`.
* `Stacks.DeRham.exists_coordinateChartPresentationSquare`: the chart presentation, as the
  commutative square it is used through.
* `Stacks.DeRham.exists_comp_formsMap_coordinateAmbient`: the ring-level pole bound, promoted to
  the square of affine schemes attached to the chart's ring tower.
* `Stacks.DeRham.exists_comp_pullback_blowupFormsPullbackMap`: **the chart-level pole bound.**

## The open immersion is out of affine space, and nothing is carried back across `g`

The chart's coordinate ring is a polynomial ring only through the isomorphism `e` of
`Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation`, and the ring computation is
stated for the polynomial ring. `Stacks.DeRham.mono_chartFormsPullbackMap` reconciles the two by
proving monomorphy for the composite with `g := Spec e` and bringing it back along `g`, which
works because monomorphy is a *property* and `AlgebraicGeometry.Scheme.Modules.pullback` at an
isomorphism is faithful. A factorisation is *data*, so bringing it back the same way would need
fullness of that functor and then a compatibility of it with the scalar action.

Neither is needed. The open immersion used here is `j := g ≫ j_i` rather than `j_i`: it is still
an open immersion, since `g` is an isomorphism, and `j ≫ b` is *literally* the upper edge
`specTowerTop` of the square attached to the ring tower the chart computation is stated for. So
the affine criterion lands on `j^*φ` directly and nothing has to be carried across `g`.

What is left over is that multiplication by `y_i^{n-1}` is conjugated by the two isomorphisms of
the composition law `relativeDifferentialFormsMap_comp` — the coherence isomorphism of the two
inverse images and the comparison of the étale square of `j`. Both conjugations happen inside
one module category, and are absorbed by the naturality of
`Stacks.RegularSequence.globalSmulCenter`, which is an element of
`CategoryTheory.CatCenter` of `𝒪_{𝐀^{m+n}_S}`-modules and so commutes with *every* morphism of
them. That step and the passage from a global-sections factorisation to a factorisation of
morphisms are `Stacks.AlgebraicGeometry.Modules.comp_center_app_of_comp` and
`...Modules.center_app_eq_of_moduleSpecΓ`.

## Implementation notes

**Each declaration names what the last one would otherwise elaborate inline.** The scalar
identity, the chart presentation and the application of the affine criterion are extracted as
separate results rather than being `have`s inside the last: against the concrete modules here —
inverse images of exterior powers of sheaves of relative differentials — the whole assembly
exceeds the heartbeat budget as a single declaration, and becomes cheap once the offending
subterms are named. Three of the statements mention `specTowerTop`, so they carry
`Stacks.Kaehler.blowupChartAlgebra` through a `letI` in the statement, the way
`Stacks.Kaehler.exists_comp_exteriorPower_map_blowupChartMapBaseChange` carries its own module
instance; the last one does not, which is why its scalar clause is phrased with the chart's own
structure morphisms rather than with `specTowerTop`.

Rewriting the morphism inside
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap q p p' g hcq n` is not possible
directly, because `hcq` is an argument whose type mentions `q`. The application of the affine
criterion is therefore quantified over `q` together with its commutativity proof and `subst` is
used, exactly as in `Stacks.DeRham.mono_chartFormsPullbackMap`; the proof argument itself never
has to be matched, commutativity being a proposition.

No `@[stacks]` attribute is attached: this is the chart computation inside the proof of the pole
bound, not an assertion of the tag.

## Which blowup this is

`Stacks.DeRham.coordinateBlowup` is `AlgebraicGeometry.blowUp`, and
`Stacks.DeRham.coordinateExceptional` is the **reducible**
`AlgebraicGeometry.exceptionalIdeal`. The library has a second constant
`Stacks.Blowup.exceptionalIdeal` with the same body, and two further blowup models
`Stacks.Blowup.blowUp` and `Stacks.Blowup.blowUpSpec` with no isomorphism to
`AlgebraicGeometry.blowUp`; nothing stated for those applies here.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open Stacks.AlgebraicGeometry.AffineDifferentialForms
  (specTowerTop specTowerMid specTowerBase specTowerComm
    exists_comp_relativeDifferentialFormsMap_specTower)
open Stacks.AlgebraicGeometry.Modules (center_app_eq_of_moduleSpecΓ comp_center_app_of_comp)
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-- The global section of `𝒪_{𝐀^{m+n}_S}` given by the `(n-1)`-st power of the `i`-th of the
last `n` coordinates: the equation of `(n-1)E` on the `i`-th standard chart, read on affine
space through the chart's presentation. -/
noncomputable abbrev coordinateChartPoleSection : Γ(coordinateAmbient R m n, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom
    (X (Sum.inr i) ^ (n - 1))

/-- **The upper edge of the chart's ring tower fixes the pole section.** The chart morphism
`Stacks.Kaehler.blowupChartHom` sends `y_i` to itself
(`Stacks.Kaehler.blowupChartHom_X_inr_self`), hence `y_i^{n-1}` to itself; on global sections of
the attached morphism of spectra that is the statement below, by naturality of
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem appTop_specTowerTop_coordinateChartPoleSection :
    letI : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
      Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
    (specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
          (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))).appTop
        (coordinateChartPoleSection R m n i) =
      coordinateChartPoleSection R m n i := by
  let : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
    Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
  have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)))))
    (X (Sum.inr i) ^ (n - 1))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
  rw [coordinateChartPoleSection, ← hnat]
  congr 1
  change Stacks.Kaehler.blowupChartHom R (Fin m) (Fin n) i (X (Sum.inr i) ^ (n - 1)) = _
  rw [map_pow, Stacks.Kaehler.blowupChartHom_X_inr_self]

/-- **The chart presentation, as the commutative square it is used through.** There is an
isomorphism `g` from affine space to the `i`-th standard chart of the coordinate blowup carrying
the chart's structure morphism over the ambient affine space to `Spec` of
`Stacks.Kaehler.blowupChartHom`, that is, to the upper edge of the square attached to the ring
tower the chart computation is stated for; and its structure morphism over the base to the
structure morphism of affine space. -/
theorem exists_coordinateChartPresentationSquare :
    letI : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
      Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
    ∃ (g : coordinateAmbient R m n ⟶ coordinateBlowupChart R m n i) (_ : IsIso g),
      g ≫ coordinateBlowupChartToAmbient R m n i =
          specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
            (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) ∧
        g ≫ coordinateBlowupChartToBase R m n i =
          coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R) := by
  let : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
    Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
  obtain ⟨e, he, -⟩ := Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation R m n i
  have : IsIso (CommRingCat.ofHom
      (e : Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i →+*
        MvPolynomial (Fin m ⊕ Fin n) R)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  set g : coordinateAmbient R m n ⟶ coordinateBlowupChart R m n i :=
    Spec.map (CommRingCat.ofHom
      (e : Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i →+*
        MvPolynomial (Fin m ⊕ Fin n) R)) with hgdef
  have : IsIso g := by rw [hgdef]; infer_instance
  have hgβ : g ≫ coordinateBlowupChartToAmbient R m n i =
      specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) := by
    rw [hgdef, coordinateBlowupChartToAmbient_eq, ← Spec.map_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext he)
  refine ⟨g, inferInstance, hgβ, ?_⟩
  rw [coordinateBlowupChartToBase_eq, ← Category.assoc, hgβ]
  exact specTowerComm (CommRingCat.of R) (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
    (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))

/-- **The ring-level pole bound, promoted to the square of affine schemes attached to the
chart's ring tower.** On global sections, multiplication by `y_i^{n-1}` factors through the
canonical map on `a`-forms of that square.

This is `Stacks.Kaehler.exists_comp_exteriorPower_map_blowupChartMapBaseChange` fed to
`AffineDifferentialForms.exists_comp_relativeDifferentialFormsMap_specTower` (in the namespace
`Stacks.AlgebraicGeometry`). It is quantified over the upper edge `q` together with the hypothesis
that `q` is that edge, so that a consumer holding a different spelling of it may `subst`. -/
theorem exists_comp_formsMap_coordinateAmbient (a : ℕ) :
    letI : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
      Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
    ∀ (q : coordinateAmbient R m n ⟶ coordinateAmbient R m n)
      (_ : q = specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)))
      (hq : q ≫ coordinateAmbientToBase R m n =
        coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R)),
      ∃ Θ : Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ) ⟶
          (Scheme.Modules.pullback q).obj
            (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ)),
        ∀ s, (moduleSpecΓFunctor.map (Scheme.Hom.relativeDifferentialFormsMap q
                (coordinateAmbientToBase R m n) (coordinateAmbientToBase R m n)
                (𝟙 (coordinateBase R)) hq (a : ℤ))).hom
              ((moduleSpecΓFunctor.map Θ).hom s) =
            (X (Sum.inr i) ^ (n - 1) : MvPolynomial (Fin m ⊕ Fin n) R) • s := by
  let : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
    Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
  intro q hq0 hq
  subst hq0
  obtain ⟨ψ, hψ⟩ :=
    Stacks.Kaehler.exists_comp_exteriorPower_map_blowupChartMapBaseChange R (Fin m) (Fin n) i a
  refine exists_comp_relativeDifferentialFormsMap_specTower (CommRingCat.of R)
    (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
    (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) a _ ψ ?_
  rw [hψ, Fintype.card_fin]

/-- **The chart-level pole bound of [Stacks, Tag 0G5G], at the level of sheaves.** There is an
isomorphism `g` from affine space to the `i`-th standard chart of the coordinate blowup such
that, along the open immersion `j = g ≫ j_i`, the inverse image of the first canonical map
`φ : b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` admits multiplication by `y_i^{n-1}` as a factorisation.

The scalar `y_i^{n-1}` is recorded twice over: as the global section
`Stacks.DeRham.coordinateChartPoleSection` of affine space that the factorisation is by, and —
the second clause — as the pullback along `j` of the pullback along `b` of that same section, so
that a consumer reading the factorisation on the sections over an open of the chart's image may
exhibit the scalar there as the restriction of a global section of `𝒪_L`. -/
theorem exists_comp_pullback_blowupFormsPullbackMap (a : ℕ) :
    ∃ (g : coordinateAmbient R m n ⟶ coordinateBlowupChart R m n i) (_ : IsIso g)
      (_ : (g ≫ coordinateBlowupChartι R m n i).appTop
          ((coordinateBlowupToAmbient R m n).appTop (coordinateChartPoleSection R m n i)) =
        coordinateChartPoleSection R m n i)
      (Θ : (Scheme.Modules.pullback (g ≫ coordinateBlowupChartι R m n i)).obj
            (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ)) ⟶
          (Scheme.Modules.pullback (g ≫ coordinateBlowupChartι R m n i)).obj
            ((Scheme.Modules.pullback (coordinateBlowupToAmbient R m n)).obj
              (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ)))),
      Θ ≫ (Scheme.Modules.pullback (g ≫ coordinateBlowupChartι R m n i)).map
            (blowupFormsPullbackMap R m n a) =
        (globalSmulCenter (coordinateAmbient R m n) (coordinateChartPoleSection R m n i)).app
          ((Scheme.Modules.pullback (g ≫ coordinateBlowupChartι R m n i)).obj
            (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ))) := by
  let : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
    Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
  obtain ⟨g, hgiso, hgβ, hgB⟩ := exists_coordinateChartPresentationSquare R m n i
  have := hgiso
  have : IsOpenImmersion (g ≫ coordinateBlowupChartι R m n i) := inferInstance
  have hjB : (g ≫ coordinateBlowupChartι R m n i) ≫ coordinateBlowupToBase R m n =
      coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R) := by
    rw [Category.assoc]; exact hgB
  have hjβ : (g ≫ coordinateBlowupChartι R m n i) ≫ coordinateBlowupToAmbient R m n =
      specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) := by
    rw [Category.assoc]; exact hgβ
  have hcq : ((g ≫ coordinateBlowupChartι R m n i) ≫ coordinateBlowupToAmbient R m n) ≫
      coordinateAmbientToBase R m n = coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R) := by
    rw [hjβ]
    exact specTowerComm (CommRingCat.of R) (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
  set u := Scheme.Hom.relativeDifferentialFormsMap (g ≫ coordinateBlowupChartι R m n i)
    (coordinateBlowupToBase R m n) (coordinateAmbientToBase R m n) (𝟙 (coordinateBase R))
    hjB (a : ℤ) with hudef
  have : IsIso u := by
    rw [hudef]
    exact Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ hjB (a : ℤ)
  set K := (Scheme.Modules.pullbackComp (g ≫ coordinateBlowupChartι R m n i)
      (coordinateBlowupToAmbient R m n)).inv.app
    (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ)) with hKdef
  have hcl : Scheme.Hom.relativeDifferentialFormsMap
        ((g ≫ coordinateBlowupChartι R m n i) ≫ coordinateBlowupToAmbient R m n)
        (coordinateAmbientToBase R m n) (coordinateAmbientToBase R m n)
        (𝟙 (coordinateBase R)) hcq (a : ℤ) =
      K ≫ (Scheme.Modules.pullback (g ≫ coordinateBlowupChartι R m n i)).map
        (blowupFormsPullbackMap R m n a) ≫ u :=
    Scheme.Hom.relativeDifferentialFormsMap_comp (coordinateBlowupToAmbient R m n)
      (g ≫ coordinateBlowupChartι R m n i) (coordinateAmbientToBase R m n)
      (coordinateBlowupToBase R m n) (coordinateAmbientToBase R m n)
      (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R)) (by simp) hjB hcq
      (a : ℤ)
  have : (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n)
      (a : ℤ)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_exteriorPower
      (Scheme.Hom.relativeDifferentials (coordinateAmbientToBase R m n)) a
  obtain ⟨Θ, hΘ⟩ := exists_comp_formsMap_coordinateAmbient R m n i a _ hjβ hcq
  have hpole : (g ≫ coordinateBlowupChartι R m n i).appTop
      ((coordinateBlowupToAmbient R m n).appTop (coordinateChartPoleSection R m n i)) =
      coordinateChartPoleSection R m n i :=
    (congrArg (fun q : coordinateAmbient R m n ⟶ coordinateAmbient R m n =>
        q.appTop (coordinateChartPoleSection R m n i)) hjβ).trans
      (appTop_specTowerTop_coordinateChartPoleSection R m n i)
  refine ⟨g, hgiso, hpole, u ≫ Θ ≫ K,
    comp_center_app_of_comp (coordinateChartPoleSection R m n i) u Θ K _ ?_⟩
  rw [← hcl]
  exact center_app_eq_of_moduleSpecΓ Θ _ (X (Sum.inr i) ^ (n - 1)) hΘ

end Stacks.DeRham

end
