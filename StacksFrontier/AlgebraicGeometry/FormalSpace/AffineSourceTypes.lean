module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplicationsRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRingsRefined

/-!
# The type of the source of a representable affine morphism (Stacks 0AKP, parts (3) to (6))

Let `S` be a scheme in a big fppf site `B`, let `Y` be an affine formal algebraic space over
`S` and let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S` which is
representable and affine. **Stacks 0AKP** asserts that `X` is again an affine formal algebraic
space, and that each of the types of Stacks 0AID passes from `Y` to `X`:

1. `X` is an affine formal algebraic space;
2. if `Y` is countably indexed then so is `X`;
3. if `Y` is countably indexed and classical then so is `X`;
4. if `Y` is weakly adic then so is `X`;
5. if `Y` is adic\* then so is `X`;
6. if `Y` is Noetherian and `f` is locally of finite type then `X` is Noetherian.

Parts (1) and (2) are
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_relative_isAffineHom` and
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_relative_isAffineHom`; this file proves
parts (3) to (6).

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isTaut_presentingRing_of_relative_isAffineHom`: the
  passage from geometry to algebra that parts (3) to (6) run through — the source has a
  presenting ring, and the morphism is the formal spectrum of a continuous *taut* homomorphism
  from a presenting ring of the target.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_of_relative_isAffineHom`:
  **Stacks 0AKP, part (3)**.
* `AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_relative_isAffineHom`: **Stacks 0AKP,
  part (4)**.
* `AlgebraicGeometry.FormalSpace.isAdicStar_of_relative_isAffineHom`: **Stacks 0AKP,
  part (5)**.
* `AlgebraicGeometry.FormalSpace.isNoetherian_of_relative_isAffineHom`: **Stacks 0AKP,
  part (6)**.

## Implementation notes

The proofs are the ones of the source, and all four go through the same two steps.

The first step is the passage to algebra. Each of the four hypotheses on `Y` makes it countably
indexed — for (3) by assumption, and for (4), (5) and (6) by Stacks 0AIK, items (5), (3), (2)
and (1) — so part (2) of this same tag makes `X` countably indexed, and part (1) makes it an
affine formal algebraic space. Item (6) of Stacks 0AIK then gives `X` a presenting ring `C`,
that is identifies it with the formal spectrum `Spf C` of a weakly admissible topological ring,
and `Y` is `Spf A` for the presenting ring `A` the hypothesis on it supplies. Full faithfulness
of `Spf`, **Stacks 0AN0**, writes `f` as `Spf (φ)` for a unique continuous homomorphism
`φ : A → C` over `S`; and `φ` is **taut** by the implication (2) ⟹ (3) of **Stacks 0AN5**,
whose hypothesis — that `Spf (φ)` be representable by objects of the site — is what being
representable and affine contains. That is
`exists_isTaut_presentingRing_of_relative_isAffineHom`.

The second step is ring-theoretic, and is the lemma of the source cited for each clause:
pre-admissibility ascends along a continuous taut homomorphism of linearly topologized rings
by **Stacks 0GX8** (`RingHom.isPreAdmissible_of_isTaut`) for part (3); weak pre-adicness by
**Stacks 0GXI** (`TopologicalRing.isWeaklyPreAdic_of_isTaut`) for part (4); and adicness with
a finitely generated ideal of definition by **Stacks 0APU**
(`RingHom.exists_fg_ideal_isAdic_of_isTaut`) for part (5). In each case the completeness and
the Hausdorff condition that the type of `X` also asks for are part of weak admissibility of
`C`, which comes with the presenting ring.

For part (6) the source deduces adic\*ness of `X` from part (5) and then applies Stacks 0AKM.
What is done here instead is the ring-theoretic form of the same argument, which avoids
transporting a presentation: part (5)'s input gives a finitely generated ideal `J ⊆ C` defining
the topology of `C` adically, so `C` is `J`-adically complete, and Stacks 05GH
(`noetherian_of_isAdicComplete_fg`) reduces Noetherianness of `C` to that of `C ⧸ J`. Tautness
of `φ` makes the closed extended ideals `J(I) = closure (I C)` a fundamental system of
neighbourhoods of zero, so `J(I) ⊆ J` for some weak ideal of definition `I ⊆ A`; the stage half
of **Stacks 0ANT**
(`AlgebraicGeometry.FormalSpace.finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap`)
makes `A ⧸ I → C ⧸ J(I)` a ring map of finite type, so `C ⧸ J(I)` is Noetherian over the
Noetherian ring `A ⧸ I`, and `C ⧸ J` is a quotient of it.

Nothing is assumed about `X`: that it is an affine formal algebraic space, that it is countably
indexed and that it is McQuillan are all consequences of the hypotheses, by parts (1) and (2)
of this tag and item (6) of Stacks 0AIK.

## References

* [Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0APU](https://stacks.math.columbia.edu/tag/0APU)
* [Stacks Project, Tag 0GX8](https://stacks.math.columbia.edu/tag/0GX8)
* [Stacks Project, Tag 0GXI](https://stacks.math.columbia.edu/tag/0GXI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The passage from geometry to algebra for a representable affine morphism whose target is
countably indexed.** Let `f : X ⟶ Y` be representable and affine with `Y` a countably indexed
affine formal algebraic space presented by the weakly admissible topological ring `A`. Then `X`
has a presenting ring `C`, and under the resulting identifications `X = Spf C`, `Y = Spf A` the
morphism `f` is the formal spectrum of a continuous *taut* homomorphism `A → C` over `S`.

`X` is an affine formal algebraic space by part (1) of Stacks 0AKP and countably indexed by its
part (2), so item (6) of Stacks 0AIK supplies `C`. Full faithfulness of `Spf`, Stacks 0AN0,
supplies the continuous homomorphism, and tautness is the implication (2) ⟹ (3) of
Stacks 0AN5: being representable and affine contains representability by objects of the site,
and that property is carried from `f` to the formal spectrum map by the two isomorphisms. -/
theorem exists_isTaut_presentingRing_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hYc : IsCountablyIndexed B S hS Y)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsPresentingRing B S hS A Y) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C), IsPresentingRing B S hS C X ∧
      ∃ (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E)
        (eX : X ≅ formalSpectrum E) (eY : Y ≅ formalSpectrum D),
        RingHom.IsTaut g.toRingHom ∧
          formalSpectrumMap hA.1 g = eX.inv ≫ f ≫ eY.hom := by
  have hX : IsAffineFormalAlgebraicSpace B S hS X :=
    isAffineFormalAlgebraicSpace_of_relative_isAffineHom B S hS f hf hY
  have hXc : IsCountablyIndexed B S hS X :=
    isCountablyIndexed_of_relative_isAffineHom B S hS f hf hYc
  obtain ⟨C, hCR, hCT, hCTR, hCLT, hCpres, -⟩ :=
    exists_countable_isPresentingRing_of_isCountablyIndexed B S hS X hX hXc
  refine ⟨C, hCR, hCT, hCTR, hCLT, hCpres, ?_⟩
  obtain ⟨PX⟩ := hCpres.2
  obtain ⟨PY⟩ := hA.2
  set eX := PX.formalSpectrumIso with heX
  set eY := PY.formalSpectrumIso with heY
  obtain ⟨g, hg, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA.1 hCpres.1 (eX.inv ≫ f ≫ eY.hom)
  refine ⟨PY.quotientSystem, PX.quotientSystem, g, eX, eY, ?_, hg⟩
  refine isTaut_of_relativelyRepresentable_formalSpectrumMap B S hS hA.1 hCpres.1 _ _ g ?_
  rw [hg]
  exact MorphismProperty.comp_mem _ _ _
    (Functor.relativelyRepresentable.of_isIso _ eX.inv)
    (MorphismProperty.comp_mem _ _ _ hf.rep
      (Functor.relativelyRepresentable.of_isIso _ eY.hom))

/-- The source of a representable affine morphism to a countably indexed affine formal algebraic
space has some surjective presentation. -/
private theorem hasSomeSurjectivePresentation_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hYc : IsCountablyIndexed B S hS Y) :
    HasSomeSurjectivePresentation B S hS X :=
  hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS
    (isAffineFormalAlgebraicSpace_of_relative_isAffineHom B S hS f hf hY)
    (isCountablyIndexed_of_relative_isAffineHom B S hS f hf hYc)

/-- **Stacks 0AKP, part (3).** The source of a representable affine morphism of fppf sheaves
whose target is a countably indexed and classical affine formal algebraic space is itself
countably indexed and classical.

Countable indexing of the source is part (2) of the same tag. For the classical half the
morphism is the formal spectrum of a continuous taut homomorphism of presenting rings, and
pre-admissibility ascends along such a homomorphism by Stacks 0GX8; the presenting ring of the
source is complete and separated, being weakly admissible. -/
@[stacks 0AKP "classical_source"]
theorem isCountablyIndexedAndClassical_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y) :
    IsCountablyIndexed B S hS X ∧ IsClassical B S hS X := by
  obtain ⟨hYc, hSomeY, A, hAR, hAT, hATR, hALT, hApres, hAadm⟩ := hY
  obtain ⟨C, hCR, hCT, hCTR, hCLT, hCpres, D, E, g, eX, eY, htaut, -⟩ :=
    exists_isTaut_presentingRing_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc A hApres
  refine ⟨isCountablyIndexed_of_relative_isAffineHom B S hS f hf hYc,
    hasSomeSurjectivePresentation_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc,
    C, hCR, hCT, hCTR, hCLT, hCpres, ?_⟩
  exact ⟨RingHom.isPreAdmissible_of_isTaut g.toRingHom g.continuous htaut hAadm.1,
    hCpres.1.2.2, hCpres.1.2.1⟩

/-- **Stacks 0AKP, part (4).** The source of a representable affine morphism of fppf sheaves
whose target is a weakly adic affine formal algebraic space is itself weakly adic.

A weakly adic affine formal algebraic space is countably indexed by item (5) of Stacks 0AIK, so
the morphism is the formal spectrum of a continuous taut homomorphism of presenting rings; weak
pre-adicness ascends along such a homomorphism by Stacks 0GXI, and the presenting ring of the
source is complete and separated, being weakly admissible. -/
@[stacks 0AKP "weakly_adic_source"]
theorem isWeaklyAdic_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsWeaklyAdic B S hS Y) :
    IsWeaklyAdic B S hS X := by
  have hYc : IsCountablyIndexed B S hS Y := isCountablyIndexed_of_isWeaklyAdic B S hS hY
  obtain ⟨hSomeY, A, hAR, hAT, hATR, hALT, hApres, hAwadic⟩ := hY
  obtain ⟨C, hCR, hCT, hCTR, hCLT, hCpres, D, E, g, eX, eY, htaut, -⟩ :=
    exists_isTaut_presentingRing_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc A hApres
  refine ⟨hasSomeSurjectivePresentation_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc,
    C, hCR, hCT, hCTR, hCLT, hCpres, ?_⟩
  let _ : TopologicalRing.IsWeaklyAdic A := hAwadic
  let _ : TopologicalRing.IsWeaklyPreAdic C :=
    TopologicalRing.isWeaklyPreAdic_of_isTaut g.toRingHom g.continuous htaut
  let _ : T2Space C := hCpres.1.2.2
  exact { completeSpace := hCpres.1.2.1 }

/-- **Stacks 0AKP, part (5).** The source of a representable affine morphism of fppf sheaves
whose target is an adic\* affine formal algebraic space is itself adic\*.

An adic\* affine formal algebraic space is countably indexed by items (2) and (3) and (5) of
Stacks 0AIK, so the morphism is the formal spectrum of a continuous taut homomorphism of
presenting rings; Stacks 0APU makes the target of such a homomorphism adic with a finitely
generated ideal of definition as soon as its source is and the target is complete and
separated, which the presenting ring of the source is, being weakly admissible. The finitely
generated ideal of definition the hypothesis supplies defines the topology adically because the
ring is pre-adic. -/
@[stacks 0AKP "adic_star_source"]
theorem isAdicStar_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsAdicStar B S hS Y) :
    IsAdicStar B S hS X := by
  have hYc : IsCountablyIndexed B S hS Y :=
    isCountablyIndexed_of_isWeaklyAdic B S hS
      (isWeaklyAdic_of_isAdic B S hS (isAdic_of_isAdicStar B S hS hY))
  obtain ⟨hSomeY, A, hAR, hAT, hATR, hALT, hApres, hAadic, I, hIdef, hIfg⟩ := hY
  obtain ⟨C, hCR, hCT, hCTR, hCLT, hCpres, D, E, g, eX, eY, htaut, -⟩ :=
    exists_isTaut_presentingRing_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc A hApres
  refine ⟨hasSomeSurjectivePresentation_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc,
    C, hCR, hCT, hCTR, hCLT, hCpres, ?_⟩
  let _ : T2Space C := hCpres.1.2.2
  let _ : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hCpres.1.2.1
  obtain ⟨J, hJfg, hJadic⟩ :=
    RingHom.exists_fg_ideal_isAdic_of_isTaut g.toRingHom g.continuous htaut
      ⟨I, hIfg, TopologicalRing.isAdic_of_isIdealOfDefinition_of_isPreAdic hAadic.1 hIdef⟩
  exact ⟨⟨⟨J, TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJadic⟩,
    hCpres.1.2.2, hCpres.1.2.1⟩, J, TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJfg⟩

/-- **Stacks 0AKP, part (6).** The source of a representable affine morphism of fppf sheaves
which is locally of finite type and whose target is a Noetherian affine formal algebraic space
is itself Noetherian.

A Noetherian affine formal algebraic space is countably indexed by items (1), (2), (3) and (5)
of Stacks 0AIK, so the morphism is the formal spectrum of a continuous taut homomorphism
`φ : A → C` of presenting rings. An ideal of definition of the Noetherian ring `A` is finitely
generated, so Stacks 0APU produces a finitely generated ideal `J ⊆ C` defining the topology of
`C` adically; `C` is then `J`-adically complete, and Stacks 05GH reduces Noetherianness of `C`
to that of `C ⧸ J`. The closed extended ideals form a fundamental system of neighbourhoods of
zero by tautness, so `J` contains the closure `J(I)` of `I C` for a weak ideal of definition
`I ⊆ A`; the stage half of Stacks 0ANT makes `A ⧸ I → C ⧸ J(I)` of finite type, hence
`C ⧸ J(I)` Noetherian, and `C ⧸ J` is a quotient of it. -/
@[stacks 0AKP "noetherian_source"]
theorem isNoetherian_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hY : IsNoetherian B S hS Y) :
    IsNoetherian B S hS X := by
  have hYc : IsCountablyIndexed B S hS Y :=
    isCountablyIndexed_of_isWeaklyAdic B S hS
      (isWeaklyAdic_of_isAdic B S hS
        (isAdic_of_isAdicStar B S hS (isAdicStar_of_isNoetherian B S hS hY)))
  obtain ⟨hSomeY, A, hAR, hAT, hATR, hALT, hApres, hANoeth, hAadic⟩ := hY
  obtain ⟨C, hCR, hCT, hCTR, hCLT, hCpres, D, E, g, eX, eY, htaut, heq⟩ :=
    exists_isTaut_presentingRing_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc A hApres
  let _ : T2Space C := hCpres.1.2.2
  let _ : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hCpres.1.2.1
  have _ : IsNoetherianRing A := hANoeth
  obtain ⟨I₀, hI₀def, hI₀adic⟩ := hAadic.1
  obtain ⟨J, hJfg, hJadic⟩ :=
    RingHom.exists_fg_ideal_isAdic_of_isTaut g.toRingHom g.continuous htaut
      ⟨I₀, IsNoetherian.noetherian I₀, hI₀adic⟩
  have hJopen : IsOpen ((J : Ideal C) : Set C) := by
    simpa only [pow_one] using (isAdic_iff.mp hJadic).1 1
  -- a weak ideal of definition of `A` whose closed extension lies inside `J`
  obtain ⟨K, hKwid, hKJ⟩ :=
    (((RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition g.toRingHom g.continuous hApres.1
      hCpres.1).mp htaut).2.mem_iff.mp (hJopen.mem_nhds J.zero_mem))
  have hKle : Ideal.closure (K.map g.toRingHom) ≤ J := hKJ
  -- `C ⧸ J(K)` is of finite type over the Noetherian ring `A ⧸ K`, hence Noetherian
  have hlft : IsLocallyOfFiniteType B S hS (formalSpectrumMap hApres.1 g) := by
    rw [heq]
    exact IsLocallyOfFiniteType.comp B S hS eX.inv (f ≫ eY.hom)
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eX.inv
        (isRepresentableEtale_of_isIso B S hS eX.inv))
      (IsLocallyOfFiniteType.comp B S hS f eY.hom hft
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eY.hom
          (isRepresentableEtale_of_isIso B S hS eY.hom)))
  have hFT := finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap hApres.1
    hCpres.1 D E g htaut hlft K hKwid
  have _ : IsNoetherianRing (A ⧸ K) := Ideal.Quotient.isNoetherianRing K
  let _ := (Ideal.quotientMap (Ideal.closure (K.map g.toRingHom)) g.toRingHom
    (Ideal.map_le_iff_le_comap.mp subset_closure)).toAlgebra
  have _ : Algebra.FiniteType (A ⧸ K) (C ⧸ Ideal.closure (K.map g.toRingHom)) := hFT
  have hquotK : IsNoetherianRing (C ⧸ Ideal.closure (K.map g.toRingHom)) :=
    Algebra.FiniteType.isNoetherianRing (A ⧸ K) (C ⧸ Ideal.closure (K.map g.toRingHom))
  have hquotJ : IsNoetherianRing (C ⧸ J) :=
    isNoetherianRing_of_surjective (C ⧸ Ideal.closure (K.map g.toRingHom)) (C ⧸ J)
      (Ideal.Quotient.factor hKle) (Ideal.Quotient.factor_surjective hKle)
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have hcomplete : IsAdicComplete J C :=
    hJadic.isAdicComplete_iff.mpr ⟨hCpres.1.2.1, hCpres.1.2.2⟩
  exact ⟨hasSomeSurjectivePresentation_of_relative_isAffineHom B S hS f hf hSomeY.1 hYc,
    C, hCR, hCT, hCTR, hCLT, hCpres,
    noetherian_of_isAdicComplete_fg C J hJfg hcomplete hquotJ,
    ⟨⟨J, TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJadic⟩,
      hCpres.1.2.2, hCpres.1.2.1⟩⟩

end AlgebraicGeometry.FormalSpace

end
