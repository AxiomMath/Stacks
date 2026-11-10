module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplications
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProductSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductCountablyIndexedBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumClassical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic

/-!
# The affine case of the clauses of Stacks 0GBB

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an affine formal algebraic
space over `S` and let `t : U ⟶ V` and `s : W ⟶ V` be morphisms from affine formal algebraic
spaces. This file proves that each of the first four types of **Stacks 0AKY** — countably
indexed, countably indexed and classical, weakly adic, adic\* — passes from `U` and `W` to
`U ×_V W`. That is the affine case of the corresponding clause of **Stacks 0GBB**, and it is
the input the globalisation engine
`AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_pullback` consumes.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_completedTensorProduct`: the engine.
  Over a *countably indexed* base the fibre product of two McQuillan affine formal algebraic
  spaces presented by `A` and `A'` is presented by `A ⊗̂_C A'`, where `C` presents the base. It
  returns with it the realisation of the first morphism as the formal spectrum map of the
  continuous homomorphism `C ⟶ A`, which is what lets a condition on that morphism be read as a
  condition on `algebraMap C A`.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_pullback_affine`,
  `AlgebraicGeometry.FormalSpace.isClassical_pullback_affine`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_pullback_affine` and
  `AlgebraicGeometry.FormalSpace.isAdicStar_pullback_affine`: the affine cases of clauses (1)
  to (4) of **Stacks 0GBB**, over an arbitrary affine formal algebraic space.

## Implementation notes

The proof is the source's. Clause (3) of **Stacks 0AN3**,
`AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct_compatible`, identifies
the fibre product with the formal spectrum of the completed tensor product of the three presenting
rings, and the type of the completed tensor product is then the corresponding clause of
**Stacks 0GB4** — for weak adicness, of **Stacks 0GXJ**. Those clauses ask nothing of the base
ring beyond a continuous map to each factor, which is why no condition on `V` survives into the
four statements below.

What does need work is that there be a base ring at all: clause (3) of Stacks 0AN3 asks all
three spaces to be McQuillan, and an affine formal algebraic space need not be. The engine
therefore assumes the base countably indexed, which by **Stacks 0AIK** makes it McQuillan, and
each of the four statements discharges that assumption by
`AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base_pullback`: the base is replaced by
a countably indexed subobject through which both morphisms factor, which changes neither the
fibre product nor the hypotheses, since all four types imply countable indexing — clause (1) by
definition and the other three through
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isWeaklyAdic`.

Clause (5) of Stacks 0GBB, the Noetherian one, is **not** here: it is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductNoetherianAffine`, which this file does
not import. Its affine case is clause (5) of Stacks 0GB4, whose hypothesis is that `C/𝔠 → A/𝔞`
be of finite type, and that is a condition on the *morphism* — so unlike the four below it needs
the realisation of the morphism by a continuous ring map, which is what
`AlgebraicGeometry.FormalSpace.exists_isPresentingRing_completedTensorProduct` returns alongside
the presentation and the four statements below discard.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0GXJ](https://stacks.math.columbia.edu/tag/0GXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre product of two McQuillan affine formal algebraic spaces over a countably
indexed one is presented by the completed tensor product of the three presenting rings.** This
is clause (3) of **Stacks 0AN3** packaged in the form the clauses of Stacks 0GBB consume: the
base ring `C` is produced from countable indexing of the base by **Stacks 0AIK**, the two
morphisms are induced by continuous ring maps `C → A` and `C → A'` by **Stacks 0AN0**, and the
conclusion is that `A ⊗̂_C A'` presents the fibre product in the sense of condition (1) of
**Stacks 0AIC**.

The base ring is returned with the data that *realises* `t` as a formal spectrum map: its weak
admissibility, its quotient system, the isomorphism of `V` with the corresponding formal
spectrum, the continuous homomorphism `C ⟶ A` whose formal spectrum map is `t` read through
those isomorphisms, and the identification of that homomorphism with the structure morphism
`algebraMap C A`. Without the realisation the ring map `algebraMap C A` is anonymous and the
chart dictionary
`AlgebraicGeometry.FormalSpace.ChartPropertyIsFiniteTypeOnReductions`, which speaks of the
continuous homomorphisms presenting a map of charts, cannot be applied to it; that is what
clause (5) of Stacks 0GBB needs in order to read the finite type condition on the chart map as
the hypothesis of clause (5) of Stacks 0GB4. The countable generation of the neighbourhood
filter of zero is returned for the same reason: it is the other half of membership in
`WAdm^{count}`, the class the dictionary quantifies over. -/
theorem exists_isPresentingRing_completedTensorProduct {U V W : FppfSheaf B S hS} (t : U ⟶ V)
    (s : W ⟶ V) (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hVc : IsCountablyIndexed B S hS V)
    (hUm : HasSomeSurjectivePresentation B S hS U)
    (hWm : HasSomeSurjectivePresentation B S hS W)
    {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A']
    (hA : IsPresentingRing B S hS A U) (hA' : IsPresentingRing B S hS A' W) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (_ : Algebra C A) (_ : Algebra C A')
      (hCwa : TopologicalRing.IsWeaklyAdmissible C) (DC : QuotientSystem B S hS C)
      (eV : V ≅ formalSpectrum DC) (cToA : ContinuousHom DC hA.2.some.quotientSystem'),
      (nhds (0 : C)).IsCountablyGenerated ∧ cToA.toRingHom = algebraMap C A ∧
        t = hA.2.some.isoFormalSpectrum.hom ≫ formalSpectrumMap hCwa cToA ≫ eV.inv ∧
      Continuous (algebraMap C A) ∧ Continuous (algebraMap C A') ∧
        IsPresentingRing B S hS
          (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := A')) (pullback t s) := by
  classical
  obtain ⟨C, iC1, iC2, iC3, iC4, hC, hCcount⟩ :=
    exists_countable_isPresentingRing_of_isCountablyIndexed B S hS V hVaff hVc
  let := iC1
  let := iC2
  let := iC3
  let := iC4
  obtain ⟨cToA, cToA', hf, hg⟩ :=
    exists_continuousHom_formalSpectrumMap_eq B S hS hA.1 hA'.1 hC.1
      hA.2.some.isoFormalSpectrum hA'.2.some.isoFormalSpectrum hC.2.some.isoFormalSpectrum t s
  obtain ⟨DT, -, -, e, hTwa, -, -, -, -⟩ :=
    exists_formalSpectrum_completedTensorProduct_compatible B S hS
      (hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS hUm)
      (hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS hWm)
      hVaff (IsAffineFormalAlgebraicSpace.isSeparated B S hS hVaff) hA.1 hA'.1 hC.1
      hA.2.some.quotientSystem' hA'.2.some.quotientSystem' hC.2.some.quotientSystem'
      hA.2.some.isoFormalSpectrum hA'.2.some.isoFormalSpectrum hC.2.some.isoFormalSpectrum
      t s cToA cToA' hf hg
  refine ⟨C, iC1, iC2, iC3, iC4, cToA.toRingHom.toAlgebra, cToA'.toRingHom.toAlgebra,
    hC.1, hC.2.some.quotientSystem', hC.2.some.isoFormalSpectrum, cToA, hCcount, rfl, ?_,
    cToA.continuous, cToA'.continuous,
    isPresentingRing_of_iso B S hS _ e.symm (isPresentingRing_formalSpectrum hTwa DT)⟩
  rw [hf]
  simp

/-- The engine over an arbitrary affine formal algebraic space base: the base is first shrunk to
a countably indexed one by
`AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base_pullback`, which changes neither
the fibre product nor the two factors. -/
theorem exists_isPresentingRing_completedTensorProduct_of_affine {U V W : FppfSheaf B S hS}
    (t : U ⟶ V) (s : W ⟶ V)
    (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (hUc : IsCountablyIndexed B S hS U) (hWc : IsCountablyIndexed B S hS W)
    {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A']
    (hA : IsPresentingRing B S hS A U) (hA' : IsPresentingRing B S hS A' W) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (_ : Algebra C A) (_ : Algebra C A'),
      Continuous (algebraMap C A) ∧ Continuous (algebraMap C A') ∧
        IsPresentingRing B S hS
          (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := A')) (pullback t s) := by
  obtain ⟨V', t', s', hV'aff, hV'c, ⟨eP⟩⟩ :=
    exists_isCountablyIndexed_base_pullback B S hS t s hUc hVaff hWc
  obtain ⟨C, i1, i2, i3, i4, alg, alg', -, -, -, -, -, -, -, hcont, hcont', hT⟩ :=
    exists_isPresentingRing_completedTensorProduct B S hS t' s' hV'aff hV'c
      (hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hUaff hUc)
      (hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hWaff hWc) hA hA'
  exact ⟨C, i1, i2, i3, i4, alg, alg', hcont, hcont',
    isPresentingRing_of_iso B S hS _ eP hT⟩

/-- **The affine case of clause (1) of Stacks 0GBB.** The fibre product of two countably indexed
affine formal algebraic spaces over an affine formal algebraic space is countably indexed.

The completed tensor product has a countable fundamental system of open ideals by clause (3) of
**Stacks 0GB4**, and by **Stacks 0AN1** that is countable indexing of the formal spectrum. -/
theorem isCountablyIndexed_pullback_affine {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (hU : IsCountablyIndexed B S hS U) (hW : IsCountablyIndexed B S hS W) :
    IsCountablyIndexed B S hS (pullback t s) := by
  obtain ⟨A, i1, i2, i3, i4, hA, hAc⟩ :=
    exists_countable_isPresentingRing_of_isCountablyIndexed B S hS U hUaff hU
  obtain ⟨A', j1, j2, j3, j4, hA', hA'c⟩ :=
    exists_countable_isPresentingRing_of_isCountablyIndexed B S hS W hWaff hW
  obtain ⟨C, k1, k2, k3, k4, alg, alg', -, -, hT⟩ :=
    exists_isPresentingRing_completedTensorProduct_of_affine B S hS t s hUaff hVaff hWaff
      hU hW hA hA'
  exact isCountablyIndexed_of_isPresentingRing B S hS _ _ hT
    (TopologicalRing.isCountablyGenerated_nhds_zero_completedTensorProduct
      (B := C) (A := A) (C := A') hAc hA'c)

/-- A presenting ring for the fibre product of two affine formal algebraic spaces over an affine
one gives the fibre product a surjective presentation. -/
private theorem hasSomeSurjectivePresentation_pullback_of_isPresentingRing
    {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [IsLinearTopology T T]
    (hT : IsPresentingRing B S hS T (pullback t s)) :
    HasSomeSurjectivePresentation B S hS (pullback t s) :=
  (hasSomeSurjectivePresentation_iff_exists_isPresentingRing B S hS
    (isAffineFormalAlgebraicSpace_pullback_of_isAffineFormalAlgebraicSpace B S hS t s hVaff
      hUaff hWaff).1).2 ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, hT⟩

/-- **The affine case of clause (2) of Stacks 0GBB**, the classical half. The fibre product of
two countably indexed classical affine formal algebraic spaces over an affine formal algebraic
space is classical: the completed tensor product is admissible by clause (2) of
**Stacks 0GB4**. -/
theorem isClassical_pullback_affine {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hUc : IsCountablyIndexed B S hS U) (hWc : IsCountablyIndexed B S hS W)
    (hU : IsClassical B S hS U) (hW : IsClassical B S hS W) :
    IsClassical B S hS (pullback t s) := by
  obtain ⟨hUm, A, i1, i2, i3, i4, hA, hAadm⟩ := id hU
  obtain ⟨hWm, A', j1, j2, j3, j4, hA', hA'adm⟩ := id hW
  obtain ⟨C, k1, k2, k3, k4, alg, alg', -, -, hT⟩ :=
    exists_isPresentingRing_completedTensorProduct_of_affine B S hS t s hUm.1 hVaff hWm.1
      hUc hWc hA hA'
  exact ⟨hasSomeSurjectivePresentation_pullback_of_isPresentingRing B S hS t s hUm.1 hVaff
      hWm.1 hT,
    _, inferInstance, inferInstance, inferInstance, inferInstance, hT,
    TopologicalRing.completedTensorProduct_isAdmissible (B := C) hAadm.1 hA'adm.1⟩

/-- **The affine case of clause (3) of Stacks 0GBB.** The fibre product of two weakly adic
affine formal algebraic spaces over an affine formal algebraic space is weakly adic: the
completed tensor product is weakly adic by **Stacks 0GXJ**. -/
theorem isWeaklyAdic_pullback_affine {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hU : IsWeaklyAdic B S hS U) (hW : IsWeaklyAdic B S hS W) :
    IsWeaklyAdic B S hS (pullback t s) := by
  obtain ⟨hUm, A, i1, i2, i3, i4, hA, hAwa⟩ := id hU
  obtain ⟨hWm, A', j1, j2, j3, j4, hA', hA'wa⟩ := id hW
  obtain ⟨C, k1, k2, k3, k4, alg, alg', -, -, hT⟩ :=
    exists_isPresentingRing_completedTensorProduct_of_affine B S hS t s hUm.1 hVaff hWm.1
      (isCountablyIndexed_of_isWeaklyAdic B S hS hU) (isCountablyIndexed_of_isWeaklyAdic B S hS hW)
      hA hA'
  exact ⟨hasSomeSurjectivePresentation_pullback_of_isPresentingRing B S hS t s hUm.1 hVaff
      hWm.1 hT,
    _, inferInstance, inferInstance, inferInstance, inferInstance, hT,
    TopologicalRing.completedTensorProduct_isWeaklyAdic (B := C) hAwa.toIsWeaklyPreAdic
      hA'wa.toIsWeaklyPreAdic⟩

/-- **The affine case of clause (4) of Stacks 0GBB.** The fibre product of two adic\* affine
formal algebraic spaces over an affine formal algebraic space is adic\*: the completed tensor
product is adic with a finitely generated ideal of definition by clause (4) of
**Stacks 0GB4**. -/
theorem isAdicStar_pullback_affine {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hU : IsAdicStar B S hS U) (hW : IsAdicStar B S hS W) :
    IsAdicStar B S hS (pullback t s) := by
  obtain ⟨hUm, A, i1, i2, i3, i4, hA, hAadic, hAfg⟩ := id hU
  obtain ⟨hWm, A', j1, j2, j3, j4, hA', hA'adic, hA'fg⟩ := id hW
  obtain ⟨C, k1, k2, k3, k4, alg, alg', hcont, hcont', hT⟩ :=
    exists_isPresentingRing_completedTensorProduct_of_affine B S hS t s hUm.1 hVaff hWm.1
      (isCountablyIndexed_of_isWeaklyAdic B S hS (isWeaklyAdic_of_isAdic B S hS
        (isAdic_of_isAdicStar B S hS hU)))
      (isCountablyIndexed_of_isWeaklyAdic B S hS (isWeaklyAdic_of_isAdic B S hS
        (isAdic_of_isAdicStar B S hS hW)))
      hA hA'
  obtain ⟨K, hKfg, hKdef⟩ := TopologicalRing.exists_fg_ideal_of_definition (B := C)
    hcont hcont' hAadic.1 hAfg hA'adic.1 hA'fg
  exact ⟨hasSomeSurjectivePresentation_pullback_of_isPresentingRing B S hS t s hUm.1 hVaff
      hWm.1 hT,
    _, inferInstance, inferInstance, inferInstance, inferInstance, hT,
    TopologicalRing.completedTensorProduct_isAdic (B := C) hcont hcont' hAadic.1 hAfg
      hA'adic.1 hA'fg, K, hKdef, hKfg⟩

end AlgebraicGeometry.FormalSpace

end
