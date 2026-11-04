module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleChartRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition

/-!
# Rig-smooth closed immersions are rig-étale, with nothing carried

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a closed immersion
of locally Noetherian formal algebraic spaces over `S`.  **Stacks 0GD4** says that the
following three conditions are equivalent:

1. `f` is rig-smooth;
2. `f` is rig-étale;
3. for every affine formal algebraic space `V` and every morphism `V ⟶ Y` representable by
   algebraic spaces and étale, the base change `X ×_Y V ⟶ V` corresponds to a surjective
   morphism `B → A` of `WAdm^{Noeth}` whose kernel `J` satisfies `I · (J / J²) = 0` for some
   ideal of definition `I` of `B`.

`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersion` states this with two inputs
carried as hypotheses.  This file proves the equivalence carrying neither.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_formalSpectrumMap_and_isTaut`,
  `AlgebraicGeometry.FormalSpace.surjective_of_isClosedImmersion_chart` and
  `AlgebraicGeometry.FormalSpace.finiteTypeAdicAlgebra_of_isClosedImmersion_chart`: the chart
  homomorphism of a fibre product chart of a closed immersion is taut, surjective, and adic of
  topologically finite type — the chart condition of Stacks 0AQI, carrying nothing.
* `AlgebraicGeometry.FormalSpace.exists_adic_presentation_of_isPullback`: the fibre product
  chart has a presentation by an adic Noetherian ring.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_hasAnnihilatedConormalOnPullbackCharts`: the
  implication (3) ⟹ (2).
* `AlgebraicGeometry.FormalSpace.isRigSmooth_tfae_of_isClosedImmersion'`: **Stacks 0GD4**.

## Implementation notes

The implications (2) ⟹ (1) (Stacks 0GD0) and (1) ⟹ (3) are as in
`AlgebraicGeometry.FormalSpace.isRigSmooth_tfae_of_isClosedImmersion`; the chart condition of
Stacks 0AQI which that statement carries is proved here.  The chart map `t` of a fibre product
chart is a closed immersion by Stacks 0GHX, conjugating it by the presenting isomorphisms of the
two charts leaves a closed immersion, its representability makes the chart homomorphism taut
(Stacks 0AN5, (1) ⟹ (3)), the quotient part of Stacks 0AQI then gives surjectivity, and Stacks
0GBW turns tautness and surjectivity into the adic-finite-type clause.

The implication (3) ⟹ (2) is where the source invokes Stacks 0GCZ, to reduce rig-étaleness of
`f`, a condition on *every* affine representable étale square `U ⟶ V` over `f`, to the fibre
product charts that condition (3) speaks about.  For a closed immersion this reduction is
direct, and needs no locality of rig-étaleness on `WAdm^{Noeth}`.  Given such a square, with
chart homomorphism `g : A → C`, let `U' = X ×_Y V`.  Then:

* `U ⟶ V` factors as `U ⟶ U' ⟶ V`, and `u : U ⟶ U'` is representable by algebraic spaces
  and étale, being a morphism between two spaces representable étale over `X`
  (`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp`, Stacks 05W3);
* `U'` is presented by an adic Noetherian ring `R`, and `U' ⟶ V` by a surjection `g' : A → R`
  (`AlgebraicGeometry.FormalSpace.exists_adic_presentation_of_isPullback`), which condition (3)
  and the computation of the completed naive cotangent complex of a surjection make rig-étale;
* `u` is presented by a homomorphism `h : R → C` (Stacks 0AN0) whose formal spectrum map is
  representable étale, so it is taut and étale on all quotient stages, hence rig-étale
  (`Rig.isRigEtale_of_etale_quotientMap`);
* `g = h ∘ g'` by faithfulness of `Spf`, and Stacks 0GCX composes the two.

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCX](https://stacks.math.columbia.edu/tag/0GCX)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GD0](https://stacks.math.columbia.edu/tag/0GD0)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
* [Stacks Project, Tag 0GHX](https://stacks.math.columbia.edu/tag/0GHX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Tautness

/-- **The chart homomorphism of a pullback chart of a closed immersion presents a closed
immersion, and is taut.**

The chart map `t : U ⟶ V` is a closed immersion because closed immersions are stable under base
change (**Stacks 0GHX**, `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_isPullback`), and
conjugating it by the presenting isomorphisms of the two charts leaves a closed immersion, an
isomorphism square being cartesian; so `Spf g` is a closed immersion.  Its representability is
the first component of the closed-immersion predicate, so the implication (1) ⟹ (3) of
**Stacks 0AN5**,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
makes `g` taut.  That implication carries the two set-theoretic conditions
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`, and both are free on a chart ring:
it is adic, hence complete for one of its ideals of definition, so
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` bounds it by the cutoff of the
site and `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` supplies the condition.

This is what makes the chart condition of Stacks 0AQI free for a closed immersion: its
surjectivity clause is read off the quotient part of Stacks 0AQI from tautness, and its
adic-finite-type clause is condition (6) of Tag 0GBW, which tautness and surjectivity give
together. -/
theorem isClosedImmersion_formalSpectrumMap_and_isTaut {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : IsClosedImmersion B S hS f) {U V : FppfSheaf B S hS} {a : U ⟶ X}
    {t : U ⟶ V} {b : V ⟶ Y} (sq : IsPullback a t f b) {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hAdicA : TopologicalRing.IsAdic A) (hAdicC : TopologicalRing.IsAdic C)
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E) (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv) :
    IsClosedImmersion B S hS (formalSpectrumMap hA g) ∧ RingHom.IsTaut g.toRingHom := by
  have ht : IsClosedImmersion B S hS t := isClosedImmersion_of_isPullback B S hS sq hf
  have hconj : IsClosedImmersion B S hS (eU.inv ≫ t ≫ eV.hom) :=
    isClosedImmersion_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := eU.inv) (snd := eU.inv ≫ t ≫ eV.hom) (f := t)
        (g := eV.inv) ⟨by simp⟩) ht
  rw [show eU.inv ≫ t ≫ eV.hom = formalSpectrumMap hA g by simp [hg]] at hconj
  refine ⟨hconj, ?_⟩
  obtain ⟨hrep, -⟩ := hconj
  refine isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS hA
    (Rig.weaklyAdmissible_of_isAdicRing hAdicC) D E
    (hasLargeSite_of_mk_lt_cutoff D ?_) (hasLargeSite_of_mk_lt_cutoff E ?_) g hrep
  · obtain ⟨I, -, hIadic, hIcomplete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
    exact mk_lt_cutoff_of_quotientSystem hIadic hIcomplete D
  · obtain ⟨J, -, hJadic, hJcomplete⟩ := exists_idealOfDefinition_isAdicComplete hAdicC
    exact mk_lt_cutoff_of_quotientSystem hJadic hJcomplete E

/-- **The chart homomorphism of a pullback chart of a closed immersion is surjective.**  This is
the surjectivity clause of **Stacks 0AQI** on the pullback charts of `f`: the chart
homomorphism is taut by
`AlgebraicGeometry.FormalSpace.isClosedImmersion_formalSpectrumMap_and_isTaut`, and the
quotient part of Stacks 0AQI,
`AlgebraicGeometry.FormalSpace.isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion`, then
identifies `A ⧸ ker g` with `C` by a ring equivalence agreeing with `g` on representatives.
Its remaining inputs are free: the source is adic, so the powers of an ideal of definition are
a countable fundamental system of neighbourhoods of zero, and the target is weakly admissible
because it is adic. -/
theorem surjective_of_isClosedImmersion_chart {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : IsClosedImmersion B S hS f) {U V : FppfSheaf B S hS} {a : U ⟶ X}
    {t : U ⟶ V} {b : V ⟶ Y} (sq : IsPullback a t f b) {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hAdicA : TopologicalRing.IsAdic A) (hAdicC : TopologicalRing.IsAdic C)
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E) (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv) :
    Function.Surjective g.toRingHom := by
  obtain ⟨hci, htaut⟩ := isClosedImmersion_formalSpectrumMap_and_isTaut B S hS hf sq hAdicA
    hAdicC hA eU eV g hg
  obtain ⟨-, e, he, -⟩ := isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA
    (Rig.weaklyAdmissible_of_isAdicRing hAdicC)
    (Rig.countablyGenerated_nhds_of_isAdicRing hAdicA) g hci htaut
  intro c
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm c)
  exact ⟨x, by rw [← he x, hx, e.apply_symm_apply]⟩

/-- **The chart homomorphism of a pullback chart of a closed immersion is adic of topologically
finite type** once it is known to be surjective — condition (6) of **Tag 0GBW**, which is the
second clause of **Stacks 0AQI** on the pullback charts of `f`.

Surjectivity gives topological finite typeness outright: already the polynomial ring in no
variables maps onto the target, so its image is dense.  Tautness is the remaining input, and it
is `AlgebraicGeometry.FormalSpace.isClosedImmersion_formalSpectrumMap_and_isTaut`; the
equivalence of the eight conditions of Tag 0GBW, `Rig.adicFiniteType_tfae`, turns the two
together into the conclusion.

Surjectivity is taken as a hypothesis rather than proved here because at the one place this is
used — the implication (3) ⟹ (2) of Stacks 0GD4 — condition (3) already asserts it. -/
theorem finiteTypeAdicAlgebra_of_isClosedImmersion_chart {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : IsClosedImmersion B S hS f) {U V : FppfSheaf B S hS} {a : U ⟶ X}
    {t : U ⟶ V} {b : V ⟶ Y} (sq : IsPullback a t f b) {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [IsNoetherianRing C]
    (hAdicA : TopologicalRing.IsAdic A) (hAdicC : TopologicalRing.IsAdic C)
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E) (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv)
    (hsurj : Function.Surjective g.toRingHom) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom := by
  obtain ⟨-, htaut⟩ := isClosedImmersion_formalSpectrumMap_and_isTaut B S hS hf sq hAdicA
    hAdicC hA eU eV g hg
  have hev : Function.Surjective
      (MvPolynomial.eval₂Hom g.toRingHom fun _ : Fin 0 ↦ (0 : C)) := by
    intro c
    obtain ⟨x, hx⟩ := hsurj c
    exact ⟨MvPolynomial.C x, by simpa using hx⟩
  have hftop : TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom :=
    ⟨0, MvPolynomial.eval₂Hom g.toRingHom fun _ ↦ 0, by ext x; simp, hev.denseRange⟩
  have hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG := by
    obtain ⟨⟨I, hI, -⟩, -, -⟩ := hAdicA
    exact ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩
  have hCfg : ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧ J.FG := by
    obtain ⟨⟨J, hJ, -⟩, -, -⟩ := hAdicC
    exact ⟨J, hJ, Ideal.fg_of_isNoetherianRing J⟩
  have hiff : (RingHom.IsTaut g.toRingHom ∧
      TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom) ↔
      Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom :=
    (Rig.adicFiniteType_tfae g.toRingHom g.continuous hAdicA hAdicC hAfg hCfg).out 2 6
  exact hiff.mp ⟨htaut, hftop⟩

end Tautness

section Presentation

/-- **The fibre product chart of a closed immersion has an adic Noetherian presentation.** Let
`f : X ⟶ Y` be a closed immersion and `V` an affine formal algebraic space presented by an adic
Noetherian ring `A`. Then the fibre product `U'` of `f` along any `b : V ⟶ Y` is presented by an
adic Noetherian ring `R`, the projection `U' ⟶ V` by a continuous homomorphism `A → R`.

`U' ⟶ V` is a closed immersion by Stacks 0GHX, so `U'` is a countably indexed affine formal
algebraic space with a countable weak presentation `R` (Stacks 0AQI, Stacks 0AN1), and the
projection is presented by a continuous homomorphism `g' : A → R` (Stacks 0AN0) whose formal
spectrum map is a closed immersion. That map is representable, so `g'` is taut (Stacks 0AN5),
hence adic (Stacks 0APU), which makes `R` adic, and surjective by the quotient part of Stacks
0AQI, which makes `R` Noetherian. -/
theorem exists_adic_presentation_of_isPullback {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsClosedImmersion B S hS f) {U' V : FppfSheaf B S hS} {a' : U' ⟶ X} {t' : U' ⟶ V}
    {b : V ⟶ Y} (sq : IsPullback a' t' f b) {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [IsNoetherianRing A]
    (hAdicA : TopologicalRing.IsAdic A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (eV : V ≅ formalSpectrum D) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : IsLinearTopology R R) (_ : IsNoetherianRing R) (_ : TopologicalRing.IsAdic R)
      (E' : QuotientSystem B S hS R) (eU' : U' ≅ formalSpectrum E') (g' : ContinuousHom D E'),
      t' = eU'.hom ≫ formalSpectrumMap hA g' ≫ eV.inv := by
  have ht' : IsClosedImmersion B S hS t' := isClosedImmersion_of_isPullback B S hS sq hf
  have hcountA := Rig.countablyGenerated_nhds_of_isAdicRing hAdicA
  have hVc : IsCountablyIndexedAffine B S hS V :=
    isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS V
      ⟨{ ring := A, system := D, iso := ⟨eV⟩ }, hA, hcountA⟩
  have hUc := isCountablyIndexedAffine_of_isClosedImmersion B S hS hVc t' ht'
  obtain ⟨Q, hQw, -⟩ := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS U' hUc
  obtain ⟨eQ⟩ := Q.iso
  obtain ⟨g', hg', -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hQw
    (eQ.inv ≫ t' ≫ eV.hom)
  have ht'g : t' = eQ.hom ≫ formalSpectrumMap hA g' ≫ eV.inv := by simp [hg']
  have hci : IsClosedImmersion B S hS (formalSpectrumMap hA g') := by
    rw [hg']
    exact isClosedImmersion_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := eQ.inv) (snd := eQ.inv ≫ t' ≫ eV.hom) (f := t')
        (g := eV.inv) ⟨by simp⟩) ht'
  obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
  have hDaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_formalSpectrum hA D
      (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_quotientSystem hI₀adic hI₀complete D))
  have htaut : RingHom.IsTaut g'.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hA hQw
      D Q.system hDaff (isAffineFormalAlgebraicSpace_of_iso B S hS eQ hUc.1) g' hci.1
  obtain ⟨-, e, he, -⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hQw hcountA g' hci htaut
  have hsurj : Function.Surjective g'.toRingHom := by
    intro c
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm c)
    exact ⟨x, by rw [← he x, hx, e.apply_symm_apply]⟩
  have hRadic : TopologicalRing.IsAdic Q.ring := by
    have hT2 : T2Space Q.ring := hQw.2.2
    have hCompl : @CompleteSpace Q.ring (IsTopologicalAddGroup.rightUniformSpace Q.ring) :=
      hQw.2.1
    obtain ⟨I, -, hImap⟩ := RingHom.isAdic_of_isTaut g'.toRingHom g'.continuous htaut
      ⟨I₀, Ideal.fg_of_isNoetherianRing I₀, hI₀adic⟩
    exact ⟨⟨I.map g'.toRingHom, TopologicalRing.isIdealOfDefinition_of_isAdic hImap, hImap⟩,
      hT2, hCompl⟩
  exact ⟨Q.ring, inferInstance, inferInstance, inferInstance, inferInstance,
    isNoetherianRing_of_surjective _ _ g'.toRingHom hsurj, hRadic, Q.system, eQ, g', ht'g⟩

end Presentation

section Rings

/-- **Stacks 0GD4, the algebraic half, for a homomorphism.** A continuous surjection `φ : A → C`
of adic Noetherian rings which is adic of topologically finite type and whose kernel `J` has
`J / J²` annihilated by an ideal of definition of `A` is rig-étale: for a surjection the
completed naive cotangent complex is the conormal module in degree `-1`. -/
theorem isRigEtale_of_surjective_of_mul_ker_le_sq {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [IsNoetherianRing C]
    (hAdicA : TopologicalRing.IsAdic A) (φ : A →+* C) (hsurj : Function.Surjective φ)
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (hJ : I * RingHom.ker φ ≤ RingHom.ker φ ^ 2) :
    RingHom.IsRigEtale φ := by
  obtain ⟨I₀, hI₀def, -, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
  obtain ⟨n, hnle, -⟩ := hI₀def.exists_pow_le_and_pow_le hI
  let _ : IsAdicComplete I₀ A := hI₀complete
  refine RingHom.isRigEtale_of_isRigEtaleOver hft I₀ hI₀def
    (Rig.isRigEtaleOver_of_isRigEtale_adicFiniteTypeAlgebra φ hft I₀ hI₀def ?_)
  exact (Rig.isRigEtale_iff_exists_pow_mul_ker_le_sq
    (Rig.adicFiniteTypeAlgebra φ hft I₀ hI₀def) hsurj).mpr
    ⟨n, fun r hr s hs ↦ hJ (Ideal.mul_mem_mul (hnle hr) hs)⟩

end Rings

section Implication

/-- **Stacks 0GD4, (3) ⟹ (2).** A closed immersion of formal algebraic spaces over `S` which
satisfies the annihilated-conormal condition on its fibre product charts is rig-étale.

For an affine representable étale square `U ⟶ V` over `f` with chart homomorphism `g`, the map
`U ⟶ V` factors through the fibre product chart `U' = X ×_Y V` by a morphism `u : U ⟶ U'`
which is representable étale (Stacks 05W3). The chart homomorphism `g'` of `U' ⟶ V` is
rig-étale by condition (3) and the computation of the completed naive cotangent complex of a
surjection; the chart homomorphism `h` of `u` has representable étale formal spectrum map, so
it is taut and étale on its quotient stages, hence rig-étale; and `g = h ∘ g'` (Stacks 0AN0)
is rig-étale by Stacks 0GCX. -/
theorem isRigEtale_of_hasAnnihilatedConormalOnPullbackCharts {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f)
    (h3 : HasAnnihilatedConormalOnPullbackCharts B S hS f) : IsRigEtale B S hS f := by
  intro U V hU hV a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g
    hg
  have sq : IsPullback (pullback.fst f b) (pullback.snd f b) f b := IsPullback.of_hasPullback f b
  obtain ⟨R, _, _, _, _, _, hRadic, E', eU', g', ht'⟩ :=
    exists_adic_presentation_of_isPullback B S hS hf sq hAdicA hA D eV
  have hbre : IsRepresentableEtale B S hS b := ⟨hb, hbe⟩
  have hRw : TopologicalRing.IsWeaklyAdmissible R := Rig.weaklyAdmissible_of_isAdicRing hRadic
  have hCw : TopologicalRing.IsWeaklyAdmissible C := Rig.weaklyAdmissible_of_isAdicRing hAdicC
  -- the chart homomorphism of the fibre product chart is rig-étale
  obtain ⟨hsurj, I, hI, hJ⟩ := h3 V hV b hbre (pullback f b) (pullback.fst f b)
    (pullback.snd f b) sq A R hAdicA hRadic hA D E' eU' eV g' ht'
  have hg' : RingHom.IsRigEtale g'.toRingHom :=
    isRigEtale_of_surjective_of_mul_ker_le_sq hAdicA g'.toRingHom hsurj
      (finiteTypeAdicAlgebra_of_isClosedImmersion_chart B S hS hf sq hAdicA hRadic hA eU' eV g'
        ht' hsurj) I hI hJ
  -- the comparison morphism to the fibre product chart is representable étale
  have hE'aff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E') := by
    obtain ⟨K, -, hKadic, hKcomplete⟩ := exists_idealOfDefinition_isAdicComplete hRadic
    exact isAffineFormalAlgebraicSpace_formalSpectrum hRw E'
      (hasLargeSite_of_mk_lt_cutoff E' (mk_lt_cutoff_of_quotientSystem hKadic hKcomplete E'))
  have hEaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) := by
    obtain ⟨K, -, hKadic, hKcomplete⟩ := exists_idealOfDefinition_isAdicComplete hAdicC
    exact isAffineFormalAlgebraicSpace_formalSpectrum hCw E
      (hasLargeSite_of_mk_lt_cutoff E (mk_lt_cutoff_of_quotientSystem hKadic hKcomplete E))
  let k : U ⟶ pullback f b := pullback.lift a t hcomm
  have hk : IsRepresentableEtale B S hS k :=
    isRepresentableEtale_of_comp B S hS k (pullback.fst f b)
      (isAffineFormalAlgebraicSpace_of_iso B S hS eU'.symm hE'aff)
      (isRepresentableEtale_of_isPullback B S hS sq.flip hbre)
      (by rw [pullback.lift_fst]; exact ⟨ha, hae⟩)
  -- its chart homomorphism is rig-étale
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hRw hCw
    (eU.inv ≫ k ≫ eU'.hom)
  have hhet : IsRepresentableEtale B S hS (formalSpectrumMap hRw h) := by
    rw [hh]
    exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS eU.inv)
      (IsRepresentableEtale.comp B S hS hk (isRepresentableEtale_of_isIso B S hS eU'.hom))
  have hhtaut : RingHom.IsTaut h.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hRw hCw
      E' E hE'aff hEaff h hhet.1
  have hh' : RingHom.IsRigEtale h.toRingHom :=
    Rig.isRigEtale_of_etale_quotientMap hRadic hAdicC h.toRingHom h.continuous hhtaut
      fun I hI ↦ etale_quotientMap_of_isRepresentableEtale_formalSpectrumMap hRw hCw E' E h
        hhtaut hhet I hI
  -- the chart homomorphism of the square is the composite
  have hgeq : g = ContinuousHom.comp hRw hA h g' := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA hCw
      (formalSpectrumMap hA g)).unique rfl ?_
    have hkt : k ≫ pullback.snd f b = t := pullback.lift_snd a t hcomm
    rw [← formalSpectrumMap_comp_eq hRw hA h g', hh,
      show formalSpectrumMap hA g = eU.inv ≫ t ≫ eV.hom by simp [hg], ← hkt, ht']
    simp
  rw [hgeq, ContinuousHom.comp_toRingHom]
  exact Rig.rigEtale_comp hAdicC hRadic hAdicA h.toRingHom g'.toRingHom h.continuous
    g'.continuous hh' hg'

end Implication

/-- **Stacks 0GD4.** For a closed immersion `f : X ⟶ Y` of locally Noetherian formal algebraic
spaces over `S`, rig-smoothness of `f` (Definition 0GCP), rig-étaleness of `f`
(Definition 0AQM), and the condition that on every affine representable étale chart `V ⟶ Y` of
the target the fibre product `X ×_Y V ⟶ V` be given by a surjection of `WAdm^{Noeth}` whose
kernel `J` has `J / J²` annihilated by an ideal of definition of the source, are all equivalent.

The implication (2) ⟹ (1) is Stacks 0GD0. The implication (1) ⟹ (3) uses the surjectivity of
the fibre product chart homomorphism, `surjective_of_isClosedImmersion_chart`, and the
computation of the completed naive cotangent complex of a surjection. The implication
(3) ⟹ (2) is `isRigEtale_of_hasAnnihilatedConormalOnPullbackCharts`. -/
@[stacks 0GD4]
theorem isRigSmooth_tfae_of_isClosedImmersion' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f) :
    List.TFAE
      [IsRigSmooth B S hS f, IsRigEtale B S hS f,
        HasAnnihilatedConormalOnPullbackCharts B S hS f] := by
  tfae_have 2 → 1 := isRigSmooth_of_isRigEtale B S hS f
  tfae_have 1 → 3 := by
    intro h V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
    have hsurj : Function.Surjective g.toRingHom :=
      surjective_of_isClosedImmersion_chart B S hS hf sq hAdicA hAdicC hA eU eV g hg
    refine ⟨hsurj, ?_⟩
    have hVc : IsCountablyIndexedAffine B S hS V :=
      isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS V
        ⟨{ ring := A, system := D, iso := ⟨eV⟩ }, hA,
          Rig.countablyGenerated_nhds_of_isAdicRing hAdicA⟩
    have hU : IsAffineFormalAlgebraicSpace B S hS U :=
      (isCountablyIndexedAffine_of_isClosedImmersion B S hS hVc t
        (isClosedImmersion_of_isPullback B S hS sq hf)).1
    obtain ⟨harep, haet⟩ := isRepresentableEtale_of_isPullback B S hS sq.flip hb
    obtain ⟨hbrep, hbet⟩ := hb
    obtain ⟨hft', I, hI, hsm⟩ :=
      h U V hU hV a b t harep hbrep haet hbet sq.w A C hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
    have hsm₀ : Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra g.toRingHom hft' I₀ hI₀def) :=
      (Rig.isRigSmooth_iff_forall_idealOfDefinition hA
        (Rig.weaklyAdmissible_of_isAdicRing hAdicC) g.toRingHom g.continuous hft').mp
        ⟨I, hI, hsm⟩ I₀ hI₀def
    let _ : IsAdicComplete I₀ A := hI₀complete
    obtain ⟨c, hc⟩ := (Rig.isRigSmooth_iff_exists_pow_mul_ker_le_sq
      (Rig.adicFiniteTypeAlgebra g.toRingHom hft' I₀ hI₀def) hsurj).mp hsm₀
    exact ⟨I₀ ^ (c + 1), isIdealOfDefinition_pow_succ hI₀adic c, Ideal.mul_le.mpr
      fun r hr s hs ↦ hc r (Ideal.pow_le_pow_right (Nat.le_succ c) hr) s hs⟩
  tfae_have 3 → 2 := isRigEtale_of_hasAnnihilatedConormalOnPullbackCharts B S hS f hf
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
