module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianPullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRingSupplement

/-!
# The type of the source of a representable affine morphism (Stacks 0AKP, parts (3)–(6))

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves over `S` which is representable by schemes with affine represented base changes. If `Y`
is an affine formal algebraic space then so is `X`, by part (1) of **Stacks 0AKP**, and `X` is
countably indexed as soon as `Y` is, by part (2). This file carries the four remaining parts of
Stacks 0AKP, which transfer the *type* of `Y` in the sense of Stacks 0AID to `X`: classical,
weakly adic, adic\* and — for an `f` which is moreover locally of finite type — Noetherian.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_and_isClassical_of_relative_isAffineHom`:
  **Stacks 0AKP, part (3)**.
* `AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_relative_isAffineHom'`: **Stacks 0AKP,
  part (4)**.
* `AlgebraicGeometry.FormalSpace.isAdicStar_of_relative_isAffineHom'`: **Stacks 0AKP,
  part (5)**.
* `AlgebraicGeometry.FormalSpace.isNoetherian_of_relative_isAffineHom'`: **Stacks 0AKP,
  part (6)**.

## Implementation notes

All four parts run through one passage from geometry to algebra, which is isolated as
`exists_taut_isPresentingRing_of_relative_isAffineHom`: if `Y` is a countably indexed affine
formal algebraic space with presenting ring `A`, then `X` is countably indexed too, so `X` is
the formal spectrum of a weakly admissible ring `C` presenting it (**Stacks 0AN1**), the
morphism `f` becomes a morphism `Spf C ⟶ Spf A` of formal spectra and hence is `Spf` of a
unique continuous homomorphism `φ : A ⟶ C` over `S` (**Stacks 0AN0**), and `φ` is *taut* because
`f` is representable — the implication from condition (2) to condition (3) of **Stacks 0AN5**,
`AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap`. The four
parts are then the four ring-theoretic statements that the type of the source of a continuous
taut homomorphism into a complete separated ring ascends: Stacks 0GX8 for pre-admissibility,
Stacks 0GXI for weak pre-adicness and Stacks 0APU for an adic topology with a finitely
generated ideal of definition.

The countable indexing of `Y` which that passage needs is part of the hypothesis for part (3),
as it is in the source: an admissible ring need not have a countable fundamental system of
open ideals. For the other three types it is automatic — a weakly adic ring has the closed
powers of a single ideal as a fundamental system, and an adic ring the powers of an ideal of
definition — and it is then carried to `X` by part (2) of Stacks 0AKP.

Part (6) adds nothing to part (5) beyond the Noetherian stages. Through the equivalence of
conditions (1) and (3) of **Stacks 0AKM** a Noetherian affine formal algebraic space is the
same thing as an adic\* one with a presentation by Noetherian affine schemes, and that
presentation pulls back along a representable affine morphism which is locally of finite type
by `AlgebraicGeometry.FormalSpace.hasNoetherianAffinePresentation_of_relative_isAffineHom`.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0APU](https://stacks.math.columbia.edu/tag/0APU)
* [Stacks Project, Tag 0GX8](https://stacks.math.columbia.edu/tag/0GX8)
* [Stacks Project, Tag 0GXI](https://stacks.math.columbia.edu/tag/0GXI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-- The neighbourhood filter of zero in a weakly pre-adic linearly topologized ring is
countably generated: the closed powers of the distinguished ideal are a fundamental system of
open ideals indexed by the natural numbers. -/
private theorem isCountablyGenerated_nhds_zero_of_isWeaklyPreAdic {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyPreAdic A] : (nhds (0 : A)).IsCountablyGenerated := by
  obtain ⟨I, -, hbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  exact hbasis.isCountablyGenerated

/-- **The passage from geometry to algebra in parts (3)–(6) of Stacks 0AKP.** Let `f : X ⟶ Y` be
a representable affine morphism of fppf sheaves over `S` whose target is a countably indexed
affine formal algebraic space presented by the weakly admissible topological ring `A`. Then `X`
is a McQuillan affine formal algebraic space presented by a weakly admissible ring `C`, and
there is a continuous *taut* homomorphism `A ⟶ C` — the one whose formal spectrum is `f`. -/
private theorem exists_taut_isPresentingRing_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hYc : IsCountablyIndexed B S hS Y)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPresentingRing B S hS A Y) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (φ : A →+* C),
      IsPresentingRing B S hS C X ∧ HasSomeSurjectivePresentation B S hS X ∧
        Continuous φ ∧ RingHom.IsTaut φ := by
  classical
  obtain ⟨D, ⟨eY⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hA
  have hXaff := isAffineFormalAlgebraicSpace_of_relative_isAffineHom B S hS f hf hY
  have hXc := isCountablyIndexed_of_relative_isAffineHom B S hS f hf hYc
  obtain ⟨P, hPwa, -⟩ :=
    hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS X ⟨hXaff, hXc⟩
  obtain ⟨eX⟩ := P.iso
  have hDaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eY hY
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA.1 hPwa (eX.inv ≫ f ≫ eY.hom)
  have hrep : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA.1 φ) := by
    rw [hφ]
    exact MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso _ _)
      (MorphismProperty.comp_mem _ _ _ hf.rep
        (Functor.relativelyRepresentable.of_isIso _ _))
  exact ⟨P.ring, P.commRing, P.topology, P.topologicalRing, P.linearTopology, φ.toRingHom,
    isPresentingRing_of_spfPresentation B S hS P hPwa,
    hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hXaff hXc, φ.continuous,
    isTaut_of_relativelyRepresentable_formalSpectrumMap B S hS hA.1 hPwa D P.system φ hrep⟩

/-- **Stacks 0AKP, part (3).** The source of a representable affine morphism of fppf sheaves
whose target is a countably indexed classical affine formal algebraic space is itself countably
indexed and classical.

Countable indexing passes to the source by part (2) of Stacks 0AKP, and admissibility of the
presenting ring ascends along the taut homomorphism inducing the morphism, by Stacks 0GX8. -/
@[stacks 0AKP "classical_source"]
theorem isCountablyIndexed_and_isClassical_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hYc : IsCountablyIndexed B S hS Y) (hYcl : IsClassical B S hS Y) :
    IsCountablyIndexed B S hS X ∧ IsClassical B S hS X := by
  obtain ⟨hYmc, A, _, _, _, _, hA, hAadm⟩ := hYcl
  have hY : IsAffineFormalAlgebraicSpace B S hS Y := hYmc.1
  obtain ⟨C, _, _, _, _, φ, hC, hXmc, hφc, hφt⟩ :=
    exists_taut_isPresentingRing_of_relative_isAffineHom B S hS f hf hY hYc A hA
  exact ⟨isCountablyIndexed_of_relative_isAffineHom B S hS f hf hYc,
    hXmc, C, _, _, _, _, hC,
    RingHom.isPreAdmissible_of_isTaut φ hφc hφt hAadm.1, hC.1.2.2, hC.1.2.1⟩

/-- **Stacks 0AKP, part (6).** The source of a representable affine morphism of fppf sheaves
which is locally of finite type and whose target is a Noetherian affine formal algebraic space
is itself Noetherian.

By the equivalence of conditions (1) and (3) of Stacks 0AKM a Noetherian affine formal
algebraic space is an adic\* one with a presentation by Noetherian affine schemes. Part (5)
above gives the first half for the source, and the presentation pulls back to a Noetherian one
because each stage of the source is of finite type over the corresponding Noetherian stage of
the target. -/
@[stacks 0AKP "noetherian_source", ega "I 10.13.2" "special case"]
theorem isNoetherian_of_relative_isAffineHom'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hYn : IsNoetherian B S hS Y) :
    IsNoetherian B S hS X := by
  obtain ⟨hYa, hYpres⟩ :=
    isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS hYn
  exact isNoetherian_of_isAdicStar B S hS
    (isAdicStar_of_relative_isAffineHom B S hS f hf hYa)
    (hasNoetherianAffinePresentation_of_relative_isAffineHom B S hS f hf hft hYpres)

/-- **Stacks 0AKP, part (5).** The source of a representable affine morphism of fppf sheaves
whose target is an adic\* affine formal algebraic space is itself adic\*.

The powers of an ideal of definition of an adic ring are a fundamental system of open ideals,
so the target is countably indexed and part (2) of Stacks 0AKP carries that to the source. The
presenting ring of the source is complete and separated, so by Stacks 0APU the taut
homomorphism inducing the morphism makes it adic with a finitely generated ideal of
definition. -/
@[stacks 0AKP "adic_star_source"]
theorem isAdicStar_of_relative_isAffineHom'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hYa : IsAdicStar B S hS Y) :
    IsAdicStar B S hS X := by
  have hYc : IsCountablyIndexed B S hS Y := isCountablyIndexedOfIsAdicStar' B S hS Y hYa
  obtain ⟨hYmc, A, _, _, _, _, hA, hAadic, I, hIdef, hIfg⟩ := hYa
  have hY : IsAffineFormalAlgebraicSpace B S hS Y := hYmc.1
  obtain ⟨C, _, _, _, _, φ, hC, hXmc, hφc, hφt⟩ :=
    exists_taut_isPresentingRing_of_relative_isAffineHom B S hS f hf hY hYc A hA
  let : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hC.1.2.1
  let : T2Space C := hC.1.2.2
  obtain ⟨J, hJfg, hJadic⟩ := RingHom.exists_fg_ideal_isAdic_of_isTaut φ hφc hφt
    ⟨I, hIfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hAadic I hIdef⟩
  have hJdef : TopologicalRing.IsIdealOfDefinition J :=
    TopologicalRing.isIdealOfDefinition_of_isAdic hJadic
  exact ⟨hXmc, C, _, _, _, _, hC,
    ⟨⟨J, hJdef, hJadic⟩, hC.1.2.2, hC.1.2.1⟩, J, hJdef, hJfg⟩

/-- **Stacks 0AKP, part (4).** The source of a representable affine morphism of fppf sheaves
whose target is a weakly adic affine formal algebraic space is itself weakly adic.

A weakly adic ring has the closed powers of a single ideal as a fundamental system of open
ideals, so the target is countably indexed and part (2) of Stacks 0AKP carries that to the
source; weak pre-adicness of the presenting ring then ascends along the taut homomorphism
inducing the morphism, by Stacks 0GXI. -/
@[stacks 0AKP "weakly_adic_source"]
theorem isWeaklyAdic_of_relative_isAffineHom'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hYw : IsWeaklyAdic B S hS Y) :
    IsWeaklyAdic B S hS X := by
  obtain ⟨hYmc, A, _, _, _, _, hA, hAadic⟩ := hYw
  have hY : IsAffineFormalAlgebraicSpace B S hS Y := hYmc.1
  let : TopologicalRing.IsWeaklyAdic A := hAadic
  have hYc : IsCountablyIndexed B S hS Y :=
    isCountablyIndexed_of_isPresentingRing B S hS Y A hA
      isCountablyGenerated_nhds_zero_of_isWeaklyPreAdic
  obtain ⟨C, _, _, _, _, φ, hC, hXmc, hφc, hφt⟩ :=
    exists_taut_isPresentingRing_of_relative_isAffineHom B S hS f hf hY hYc A hA
  let : TopologicalRing.IsWeaklyPreAdic C :=
    TopologicalRing.isWeaklyPreAdic_of_isTaut φ hφc hφt
  let : T2Space C := hC.1.2.2
  exact ⟨hXmc, C, _, _, _, _, hC, { completeSpace := hC.1.2.1 }⟩

end AlgebraicGeometry.FormalSpace

end
