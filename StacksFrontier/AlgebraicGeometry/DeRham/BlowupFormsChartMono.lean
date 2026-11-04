module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineFormsMapMono
public import StacksFrontier.RingTheory.Kaehler.BlowupChartFormsPoleBound

/-!
# The first canonical map on forms of the coordinate blowup is a monomorphism

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` —
a ring `R`, `S = Spec(R)`, the coordinate closed immersion `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the
blowup `b : L ⟶ X` of `X` along `Z` — the first of the two canonical maps of [Stacks, Tag 0G5G]
is `Stacks.DeRham.blowupFormsPullbackMap`,

`φ : b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}`.

**This file proves that `φ` is a monomorphism**, which is the injectivity half of the source's
proof of that tag.

`Stacks.DeRham.mono_blowupFormsPullbackMap_of_chart` has already reduced the statement to its
`n` standard affine charts, and
`Stacks.Kaehler.injective_exteriorPower_map_blowupChartMapBaseChange` has already proved the
chart computation on the ring side — the pole bound `d t_j = (d y_j - t_j d y_i)/y_i` of the
source, in the form that `exteriorPower.map a (KaehlerDifferential.mapBaseChange R A A)` along
`Stacks.Kaehler.blowupChartHom` is injective. What this file supplies is the passage from the
second to the first: the affine criterion
`Stacks.AlgebraicGeometry.AffineDifferentialForms.mono_relativeDifferentialFormsMap_specTower`
turns that ring-theoretic injectivity into monomorphy of the canonical map on `a`-forms of a
square of affine schemes, and the chart is identified with such a square.

## Main results

* `Stacks.DeRham.coordinateBlowupChartToAmbient_eq`: the structure morphism of the `i`-th
  standard chart over the ambient affine space is `Spec` of
  `Stacks.MoreMorphisms.coordinateBlowupChartStructureMap`.
* `Stacks.DeRham.mono_chartFormsPullbackMap`: **the chart-level first canonical map is a
  monomorphism**, in every degree.
* `Stacks.DeRham.mono_blowupFormsPullbackMap`: **the first canonical map of [Stacks, Tag 0G5G]
  is a monomorphism**, in every degree.

## Implementation notes

The chart's coordinate ring is an affine blowup algebra, known to be a polynomial ring only
through the isomorphism `e` of
`Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation`, whereas the ring computation is
stated for the polynomial ring with `Stacks.Kaehler.blowupChartHom` as its structure map. The
two are reconciled **at the level of schemes**, not of rings: `g := Spec e` is an isomorphism
`𝐀^{m+n}_S ⟶ L_i` with `g ≫ (j_i ≫ b) = Spec (blowupChartHom)`, so the affine criterion applies
to the composite with the ring-theoretic injectivity as its hypothesis *verbatim*, and monomorphy
comes back along `g` by the composition law
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` together with faithfulness of
`AlgebraicGeometry.Scheme.Modules.pullback` at an isomorphism.

Doing it on the ring side instead — transporting the injectivity of
`exteriorPower.map a (KaehlerDifferential.mapBaseChange R A A)` along `e` — is not a semilinear
transport of modules but a change of the ring the exterior power is formed over, since
`exteriorPower.map` is defined only for maps linear over a fixed ring; there is no `exteriorPower`
functoriality in the ring to appeal to.

Rewriting the morphism inside
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap q p p' g hcq n` is not possible
directly, because `hcq` is an argument whose type mentions `q`. The statement is therefore
generalised over `q` together with its commutativity proof and `subst` is used; the proof
argument itself never has to be matched, commutativity being a proposition and proofs of a
proposition definitionally equal.

No `@[stacks]` attribute is attached. Tag 0G5G asserts that two canonical maps exist and that
their composite is the map induced by the inclusion `𝒪_L ⊆ 𝒪_L((n-1)E)`; monomorphy of the first
is not one of its assertions but an ingredient of the construction of the second, and the tag's
first clause is already claimed by `Stacks.DeRham.blowupFormsPullbackMap`.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.AffineDifferentialForms
  (specTowerTop specTowerMid specTowerBase specTowerComm
    mono_relativeDifferentialFormsMap_specTower)

universe u

namespace Stacks.DeRham

/-! ### Cancelling an isomorphism on each side of a monomorphism -/

/-- **A monomorphism flanked by two isomorphisms has a monomorphic middle factor.** -/
theorem mono_of_mono_isoCompIso {D : Type*} [Category D] {P M N Q : D} {u : M ⟶ N}
    (α : P ⟶ M) (δ : N ⟶ Q) (hα : IsIso α) (hδ : IsIso δ) (h : Mono (α ≫ u ≫ δ)) : Mono u := by
  have := hα
  have := hδ
  have := h
  have key : inv α ≫ (α ≫ u ≫ δ) ≫ inv δ = u := by simp
  rw [← key]
  infer_instance

/-! ### The chart as a morphism of affine schemes -/

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-- **The structure morphism of the `i`-th standard chart over the ambient affine space is
`Spec` of the chart's structure map.** This is
`Stacks.MoreMorphisms.blowupChartι_comp_blowUpToBase_coordinateIdeal` with the inclusion of the
ambient affine space as an affine open of itself read through
`AlgebraicGeometry.Scheme.isoSpec`, which is how
`Stacks.MoreMorphisms.coordinateBlowupChart_smooth` reads it. -/
theorem coordinateBlowupChartToAmbient_eq :
    coordinateBlowupChartToAmbient R m n i =
      Spec.map (CommRingCat.ofHom
        (Stacks.MoreMorphisms.coordinateBlowupChartStructureMap R m n i)) := by
  have h := Stacks.MoreMorphisms.blowupChartι_comp_blowUpToBase_coordinateIdeal R m n i
  rw [show coordinateBlowupChartToAmbient R m n i =
      blowupChartι (Stacks.MoreMorphisms.coordinateIdeal R m n)
        (Stacks.MoreMorphisms.topAffineOpen R m n)
        (Stacks.MoreMorphisms.coordinateIdealSection R m n i) ≫
      blowUpToBase (Stacks.MoreMorphisms.coordinateIdeal R m n) from rfl, h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The chart's structure morphism over the base factors through the ambient affine space. -/
theorem coordinateBlowupChartToBase_eq :
    coordinateBlowupChartToBase R m n i =
      coordinateBlowupChartToAmbient R m n i ≫ coordinateAmbientToBase R m n := by
  simp [coordinateBlowupChartToBase, coordinateBlowupChartToAmbient, coordinateBlowupToBase,
    Category.assoc]

/-! ### Monomorphy on a chart, and globally -/

/-- **The chart-level first canonical map of [Stacks, Tag 0G5G] is a monomorphism**, in every
degree.

The chart's coordinate ring is a polynomial ring in such a way that its structure map over the
ambient affine space becomes `Stacks.Kaehler.blowupChartHom`
(`Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation`). `Spec` of that isomorphism is
an isomorphism `g` of schemes whose composite with the chart's structure morphism is
`Spec (blowupChartHom)`, so the affine criterion
`Stacks.AlgebraicGeometry.AffineDifferentialForms.mono_relativeDifferentialFormsMap_specTower`
applies to the composite with the chart computation
`Stacks.Kaehler.injective_exteriorPower_map_blowupChartMapBaseChange` as its hypothesis; and the
canonical map of the composite is, by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp`, the chart-level map pulled
back along `g`, conjugated by two isomorphisms. -/
theorem mono_chartFormsPullbackMap (a : ℕ) : Mono (chartFormsPullbackMap R m n i a) := by
  obtain ⟨e, he, -⟩ := Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation R m n i
  let : Algebra ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      ↥(CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
    Stacks.Kaehler.blowupChartAlgebra R (Fin m) (Fin n) i
  have : IsIso (CommRingCat.ofHom
      (e : Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i →+*
        MvPolynomial (Fin m ⊕ Fin n) R)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  set g : coordinateAmbient R m n ⟶ coordinateBlowupChart R m n i :=
    Spec.map (CommRingCat.ofHom
      (e : Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i →+*
        MvPolynomial (Fin m ⊕ Fin n) R)) with hgdef
  have : IsIso g := by rw [hgdef]; infer_instance
  have hcomp : ((e : Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i →+*
          MvPolynomial (Fin m ⊕ Fin n) R).comp
        (Stacks.MoreMorphisms.coordinateBlowupChartStructureMap R m n i)) =
      (Stacks.Kaehler.blowupChartHom R (Fin m) (Fin n) i).toRingHom :=
    RingHom.ext he
  have hgβ : g ≫ coordinateBlowupChartToAmbient R m n i =
      specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) := by
    rw [hgdef, coordinateBlowupChartToAmbient_eq, ← Spec.map_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hcomp
  have hcomm'' : (g ≫ coordinateBlowupChartToAmbient R m n i) ≫ coordinateAmbientToBase R m n =
      coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R) := by
    rw [hgβ]
    exact specTowerComm (CommRingCat.of R) (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
      (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
  have hcomm' : g ≫ coordinateBlowupChartToBase R m n i =
      coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R) := by
    rw [coordinateBlowupChartToBase_eq, ← Category.assoc]
    exact hcomm''
  have hmono : ∀ (q : coordinateAmbient R m n ⟶ coordinateAmbient R m n)
      (_ : q = specTowerTop (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R))
        (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)))
      (hcq : q ≫ coordinateAmbientToBase R m n =
        coordinateAmbientToBase R m n ≫ 𝟙 (coordinateBase R)),
      Mono (Scheme.Hom.relativeDifferentialFormsMap q (coordinateAmbientToBase R m n)
        (coordinateAmbientToBase R m n) (𝟙 (coordinateBase R)) hcq (a : ℤ)) := by
    intro q hq hcq
    subst hq
    exact mono_relativeDifferentialFormsMap_specTower _ _ _ a
      (Stacks.Kaehler.injective_exteriorPower_map_blowupChartMapBaseChange R (Fin m) (Fin n) i a)
  have hcl := Scheme.Hom.relativeDifferentialFormsMap_comp
    (coordinateBlowupChartToAmbient R m n i) g (coordinateAmbientToBase R m n)
    (coordinateBlowupChartToBase R m n i) (coordinateAmbientToBase R m n)
    (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R))
    (coordinateBlowupChartToAmbient_comm R m n i) hcomm' hcomm'' (a : ℤ)
  have hδ : IsIso (Scheme.Hom.relativeDifferentialFormsMap g
      (coordinateBlowupChartToBase R m n i) (coordinateAmbientToBase R m n)
      (𝟙 (coordinateBase R)) hcomm' (a : ℤ)) :=
    Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g
      (coordinateBlowupChartToBase R m n i) (coordinateAmbientToBase R m n)
      (𝟙 (coordinateBase R)) (IsPullback.of_horiz_isIso ⟨hcomm'⟩) (a : ℤ)
  have hpull : Mono ((Scheme.Modules.pullback g).map (chartFormsPullbackMap R m n i a)) := by
    refine mono_of_mono_isoCompIso
      ((Scheme.Modules.pullbackComp g (coordinateBlowupChartToAmbient R m n i)).inv.app
        (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ)))
      (Scheme.Hom.relativeDifferentialFormsMap g (coordinateBlowupChartToBase R m n i)
        (coordinateAmbientToBase R m n) (𝟙 (coordinateBase R)) hcomm' (a : ℤ))
      inferInstance hδ ?_
    have hq := hmono _ hgβ hcomm''
    rw [hcl] at hq
    exact hq
  have : (Scheme.Modules.pullback g).IsEquivalence :=
    Scheme.Modules.isEquivalence_pullback_of_isIso g
  exact Functor.mono_of_mono_map (Scheme.Modules.pullback g) hpull

/-- **The first canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` of [Stacks, Tag 0G5G] is a
monomorphism**, in every degree.

This is the injectivity half of the source's proof: the `n` standard charts cover `L`,
monomorphy is local on `L`, and on each chart the map is a monomorphism by
`Stacks.DeRham.mono_chartFormsPullbackMap`. -/
theorem mono_blowupFormsPullbackMap (a : ℕ) : Mono (blowupFormsPullbackMap R m n a) :=
  mono_blowupFormsPullbackMap_of_chart R m n a fun i => mono_chartFormsPullbackMap R m n i a

end Stacks.DeRham

end
