module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Closed immersions into McQuillan affine formal algebraic spaces

Let `S` be a scheme and let `f : Y ⟶ X` be a closed immersion of formal algebraic spaces over
`S` with `X` a McQuillan affine formal algebraic space, that is, one presented by the quotients
of a weakly admissible topological ring `A` by its weak ideals of definition. Stacks 0ANQ
asserts that `Y` is then McQuillan as well, say presented by a weakly admissible topological
ring `C`, and that the continuous homomorphism `A ⟶ C` inducing `f` is taut, has closed kernel
and has dense image.

This file proves the McQuillan property of the source, and — for a closed immersion of formal
spectra, where the presenting homomorphism is given — its closed kernel and its dense image.
That the closed immersion arises from such a homomorphism at all, and that the homomorphism is
taut, are proved in
`StacksFrontier/AlgebraicGeometry/FormalSpace/ClosedImmersionMcQuillanPresentation.lean`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_of_isClosedImmersion`:
  **Stacks 0ANQ**, the source of a closed immersion into a McQuillan affine formal algebraic
  space is McQuillan.
* `AlgebraicGeometry.FormalSpace.isClosed_ker_toRingHom`: **Stacks 0ANQ**, the presenting
  homomorphism has closed kernel.
* `AlgebraicGeometry.FormalSpace.denseRange_of_isClosedImmersion_formalSpectrumMap`:
  **Stacks 0ANQ**, the presenting homomorphism has dense image.
* `AlgebraicGeometry.FormalSpace.isClosedImmersionInto_comp`,
  `AlgebraicGeometry.FormalSpace.mono_of_isClosedImmersionInto` and
  `AlgebraicGeometry.FormalSpace.isClosedImmersionInto_of_comp_mono`: the calculus of closed
  immersions of fppf sheaves used here — composites, that a closed immersion is a
  monomorphism, and that a morphism whose composite with a monomorphism is a closed immersion
  is one itself.

## Implementation notes

McQuillan is read as condition (4) of Stacks 0AIC, the form Stacks 0AID's definition is
recorded in by `AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`: an affine formal
algebraic space one of whose presentations by affine thickenings has surjective section-ring
projections. The source of a closed immersion inherits such a presentation by pulling back a
presentation of the target one stage at a time: the pulled-back stages are affine because a
closed immersion is affine, their transition morphisms are thickenings because the cartesian
squares exhibit them as base changes, and their section-ring projections are surjective
because a compatible system of sections of the stages of the target restricts to one of the
source along the stagewise closed immersions.

Dense image is the statement that `A ⟶ C ⧸ K` is surjective for every weak ideal of
definition `K` of `C`. Choosing a weak ideal of definition `J` of `A` inside the contraction of
`K` presents the stage map `Spec (C ⧸ K) ⟶ Spec (A ⧸ J)` as a factor of a composite of closed
immersions through a monomorphism, hence as a closed immersion itself, so `A ⧸ J ⟶ C ⧸ K` is
surjective. The weak ideals of definition of `C` being a fundamental system of neighbourhoods
of zero, surjectivity onto all of them is density.

The closed kernel is the general fact that a continuous homomorphism into a separated
topological ring has closed kernel; weak admissibility of the target supplies separatedness.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0ANQ](https://stacks.math.columbia.edu/tag/0ANQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Source

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of fppf sheaves is affine. -/
private theorem isAffineHom_of_isClosedImmersionInto {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersionInto B S hS f) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  exact MorphismProperty.relative_monotone
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      fun _ _ _ hg ↦ (isClosedImmersion_iff_isAffineHom.mp hg).1) f hf

/-- Surjectivity of the section-ring projections passes from a diagram of affine schemes to
one lying over it whose stagewise comparison maps have surjective section maps. -/
private theorem hasSurjectiveSectionProjections_of_surjective_stages
    {I : Type (u + 1)} [Category I] (D E : I ⥤ BigAffineFppf B S hS) (p : E ⟶ D)
    (hD : HasSurjectiveSectionProjections B S hS D)
    (hp : ∀ i : I, Function.Surjective
      (fun x : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj (Opposite.op i) ↦
        Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (p.app i)).op x)) :
    HasSurjectiveSectionProjections B S hS E := by
  classical
  intro i e
  let FD := sectionDiagram B S hS D ⋙ forget CommRingCat.{u}
  let FE := sectionDiagram B S hS E ⋙ forget CommRingCat.{u}
  let η : FD ⟶ FE :=
    Functor.whiskerRight (NatTrans.op p)
      ((BigAffineFppf.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat.{u})
  obtain ⟨d, hd⟩ := hp i e
  obtain ⟨s, hs⟩ := hD i d
  refine ⟨⟨fun j ↦ η.app j (s.1 j), ?_⟩, ?_⟩
  · intro j k g
    change FE.map g (η.app j (s.1 j)) = η.app k (s.1 k)
    rw [← NatTrans.naturality_apply η g (s.1 j), s.2 g]
  · change η.app (Opposite.op i) (s.1 (Opposite.op i)) = e
    rw [show s.1 (Opposite.op i) = d from hs]
    exact hd

/-- **Stacks 0ANQ**, the McQuillan property of the source. The source of a closed immersion of
formal algebraic spaces over `S` whose target is a McQuillan affine formal algebraic space is
again a McQuillan affine formal algebraic space. -/
@[stacks 0ANQ "the source is McQuillan"]
theorem hasSomeSurjectivePresentation_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (hX : HasSomeSurjectivePresentation B S hS X)
    (_hY : IsFormalAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    HasSomeSurjectivePresentation B S hS Y := by
  have hfInto : IsClosedImmersionInto B S hS f :=
    isClosedImmersionInto_of_isClosedImmersion B S hS f hf
  have hfAffine := isAffineHom_of_isClosedImmersionInto B S hS f hfInto
  have hYaff := AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine B S hS f hX.1 hfAffine
  obtain ⟨hXaff, I, pre, hI, hd, D, hD, ⟨hXcol⟩, hXproj⟩ := hX
  let : Preorder I := pre
  let : Nonempty I := hI
  let : IsDirected I (· ≤ ·) := hd
  obtain ⟨E, p, hYcol, hcart⟩ :=
    exists_affine_pullback_presentation B S hS f hfAffine D hXcol
  refine ⟨hYaff, I, pre, hI, hd, E,
    isThickening_of_cartesian_presentation B S hS f D E p hXcol hYcol hcart hD, ⟨hYcol⟩, ?_⟩
  apply hasSurjectiveSectionProjections_of_surjective_stages B S hS D E p hXproj
  intro i
  have hclosed : AlgebraicGeometry.IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map (p.app i)) :=
    hfInto.2 (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ hXcol.inv)
      (colimit.ι (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ hYcol.inv)
      ((BigAffineFppf.inclusion B S hS).map (p.app i)) (hcart i)
  let : AlgebraicGeometry.IsClosedImmersion
    ((BigAffineFppf.toScheme B S hS).map (p.app i)) := hclosed
  exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigAffineFppf.toScheme B S hS).map (p.app i))).2

add_to_stacks 0AJK "part (1), the conclusion that `Y` is McQuillan: the source of a closed \
immersion of formal algebraic spaces whose target is a McQuillan affine formal algebraic space \
is again a McQuillan affine formal algebraic space. Part (1)'s conclusions about the presenting \
homomorphism `φ : A → B` are tagged separately. The question part (1) raises, which conditions \
on `A` force `B = (A/K)^∧`, is a question and is asserted nowhere."
  hasSomeSurjectivePresentation_of_isClosedImmersion

end Source

section Sheaves

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A composite of closed immersions of fppf sheaves is a closed immersion. -/
private theorem isClosedImmersionInto_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsClosedImmersionInto B S hS f) (hg : IsClosedImmersionInto B S hS g) :
    IsClosedImmersionInto B S hS (f ≫ g) := by
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : (Sheaf.sheafifiedYoneda J).Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : (Sheaf.sheafifiedYoneda J).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition := by
    constructor
    intro U V W u v hu hv
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map u) at hu
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map v) at hv
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (u ≫ v))
    rw [Functor.map_comp]
    exact AlgebraicGeometry.IsClosedImmersion.comp _ _
  exact MorphismProperty.comp_mem
    (MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f g hf hg

/-- A composite of closed immersions of fppf sheaves is a closed immersion. -/
alias isClosedImmersionInto_comp' := isClosedImmersionInto_comp

/-- A closed immersion of fppf sheaves is a monomorphism. -/
private theorem mono_of_isClosedImmersionInto {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersionInto B S hS f) : Mono f := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigFppfOver.toScheme B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have hcancel : ∀ (U : BigFppfOver B S hS) (left right : F.obj U ⟶ X),
      left ≫ f = right ≫ f → left = right := by
    intro U left right heq
    let target := left ≫ f
    let projection := hf.1.snd target
    have hclosed : AlgebraicGeometry.IsClosedImmersion (T.map projection) :=
      hf.2 target (hf.1.fst target) projection (hf.1.isPullback target)
    let : AlgebraicGeometry.IsClosedImmersion (T.map projection) := hclosed
    let : Mono projection := T.mono_of_mono_map inferInstance
    let leftLift := hf.1.lift (g := target) left (𝟙 U) (by
      change left ≫ f = F.map (𝟙 U) ≫ target
      rw [F.map_id, Category.id_comp])
    let rightLift := hf.1.lift (g := target) right (𝟙 U) (by
      change right ≫ f = F.map (𝟙 U) ≫ target
      rw [F.map_id, Category.id_comp]
      exact heq.symm)
    have hlifts : leftLift = rightLift := by
      apply (cancel_mono projection).mp
      simp [leftLift, rightLift, projection]
    simpa [leftLift, rightLift] using
      congrArg (fun lift ↦ F.map lift ≫ hf.1.fst target) hlifts
  constructor
  intro Z left right heq
  apply GrothendieckTopology.hom_ext_uliftYoneda.{u + 1} J
  intro U point
  let e := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  have h := hcancel U ((e.app U).hom ≫ point ≫ left) ((e.app U).hom ≫ point ≫ right)
    (by simp only [Category.assoc, heq])
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun map ↦ (e.app U).inv ≫ map) h

/-- A closed immersion of fppf sheaves is a monomorphism. -/
alias mono_of_isClosedImmersionInto' := mono_of_isClosedImmersionInto

/-- A morphism of fppf sheaves whose composite with a monomorphism is a closed immersion is
itself a closed immersion. -/
private theorem isClosedImmersionInto_of_comp_mono {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hg : Mono g) (hfg : IsClosedImmersionInto B S hS (f ≫ g)) :
    IsClosedImmersionInto B S hS f := by
  have := hg
  have hsquare : IsPullback (𝟙 X) f (f ≫ g) g := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hsquare hfg

/-- A morphism of fppf sheaves whose composite with a monomorphism is a closed immersion is
itself a closed immersion. -/
alias isClosedImmersionInto_of_comp_mono' := isClosedImmersionInto_of_comp_mono

end Sheaves

section Rings

/-- Every weak ideal of definition of the target of a continuous homomorphism out of a weakly
admissible topological ring contains the image of one of the source. -/
private theorem exists_weakIdeal_le_comap {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (φ : A →+* C) (hφ : Continuous φ)
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ Ideal.comap φ K.1 := by
  obtain ⟨I, hI⟩ := hA.1
  refine ⟨⟨I ⊓ Ideal.comap φ K.1, ?_, fun x hx ↦ hI.2 x (Ideal.mem_inf.mp hx).1⟩, inf_le_right⟩
  change IsOpen ((I : Set A) ∩ φ ⁻¹' (K.1 : Set C))
  exact hI.1.inter (K.2.1.preimage hφ)

/-- A ring homomorphism into a weakly admissible topological ring which is surjective onto
every quotient by a weak ideal of definition has dense image. -/
private theorem denseRange_of_surjective_weakQuotients {A C : Type u} [CommRing A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hC : TopologicalRing.IsWeaklyAdmissible C) (φ : A →+* C)
    (hφ : ∀ K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I },
      Function.Surjective fun a : A ↦ Ideal.Quotient.mk K.1 (φ a)) :
    DenseRange φ := by
  change Dense (Set.range φ)
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨c, hc⟩ := hne
  have hBasis : (nhds c).HasBasis
      (fun I : Ideal C ↦ TopologicalRing.IsWeakIdealOfDefinition I)
      (fun I ↦ (fun x : C ↦ -c + x) ⁻¹' (I : Set C)) := by
    simpa [add_zero] using
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).map (fun x : C ↦ c + x)
  obtain ⟨I, hI, hIU⟩ := hBasis.mem_iff.mp (hU.mem_nhds hc)
  obtain ⟨a, ha⟩ := hφ ⟨I, hI⟩ c
  refine ⟨φ a, hIU ?_, a, rfl⟩
  change -c + φ a ∈ I
  have hdiff : φ a - c ∈ I := Ideal.Quotient.eq.mp ha
  convert hdiff using 1
  abel

/-- A ring map whose spectrum is a closed immersion of affine schemes is surjective. -/
private theorem surjective_of_isClosedImmersion_specMap {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ))) :
    Function.Surjective φ := by
  let : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := hφ
  exact (RingHom.surjective_respectsIso.arrow_mk_iso_iff
    (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom φ))).mpr
      (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
        (Spec.map (CommRingCat.ofHom φ))).2

end Rings

section Spectrum

/-- **Stacks 0ANQ**, the closed-kernel assertion. The continuous homomorphism presenting a
morphism of formal spectra of weakly admissible topological rings over `S` has closed kernel,
its target being separated. -/
@[stacks 0ANQ "closed kernel"]
theorem isClosed_ker_toRingHom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C]
    (hC : TopologicalRing.IsWeaklyAdmissible C) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (g : ContinuousHom D E) :
    IsClosed (RingHom.ker g.toRingHom : Set A) := by
  let : T2Space C := hC.2.2
  exact RingHom.isClosed_ker_of_continuous g.toRingHom g.continuous

add_to_stacks 0AJK "part (1), the conclusion that the kernel `K ⊂ A` of the homomorphism \
`φ : A → B` presenting a closed immersion is a closed ideal. It is proved here in the stronger \
form that needs only continuity of the homomorphism and separatedness of its target, so no \
closed-immersion hypothesis appears."
  isClosed_ker_toRingHom

/-- A stage inclusion of a formal spectrum is a closed immersion of fppf sheaves. -/
private theorem isClosedImmersionInto_formalSpectrumInclusion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    IsClosedImmersionInto B S hS (formalSpectrumInclusion D (OrderDual.toDual J)) := by
  have hthick := isThickening_quotient B S hS A (formalSpectrum D)
    D.weakIdealColimitPresentation hA (OrderDual.toDual J)
  have hclosed := MorphismProperty.relative_monotone
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      fun _ _ _ h ↦ h.1) _ hthick
  change IsClosedImmersionInto B S hS
    (colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) ≫ 𝟙 _) at hclosed
  simpa only [Category.comp_id] using hclosed

/-- **Stacks 0ANQ**, the dense-image assertion. The continuous homomorphism presenting a closed
immersion of formal spectra of weakly admissible topological rings over `S` has dense image. -/
@[stacks 0ANQ "dense image"]
theorem denseRange_of_isClosedImmersion_formalSpectrumMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A C : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (g : ContinuousHom D E)
    (hg : IsClosedImmersion B S hS (formalSpectrumMap hA g)) :
    DenseRange g.toRingHom := by
  apply denseRange_of_surjective_weakQuotients hC
  intro K
  obtain ⟨J, hJK⟩ := exists_weakIdeal_le_comap hA g.toRingHom g.continuous K
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let stageMap := (BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJK)
  have hcomposition := isClosedImmersionInto_comp
    (formalSpectrumInclusion E (OrderDual.toDual K)) (formalSpectrumMap hA g)
    (isClosedImmersionInto_formalSpectrumInclusion hC E K)
    (isClosedImmersionInto_of_isClosedImmersion B S hS (formalSpectrumMap hA g) hg)
  rw [formalSpectrumMap_spec hA g J K hJK] at hcomposition
  have hstage := isClosedImmersionInto_of_comp_mono (F.map stageMap)
    (formalSpectrumInclusion D (OrderDual.toDual J))
    (mono_of_isClosedImmersionInto _ (isClosedImmersionInto_formalSpectrumInclusion hA D J))
    hcomposition
  have hclosed := MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (F := F) (f := stageMap) hstage
  change AlgebraicGeometry.IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 g.toRingHom hJK))) at hclosed
  intro value
  obtain ⟨quotient, hquotient⟩ := surjective_of_isClosedImmersion_specMap _ hclosed value
  obtain ⟨element, rfl⟩ := Ideal.Quotient.mk_surjective quotient
  exact ⟨element, hquotient⟩

add_to_stacks 0AJK "part (1), the conclusion that the image `φ(A)` of the homomorphism \
`φ : A → B` presenting a closed immersion is dense in `B`. Whether `φ` is moreover surjective \
and open, equivalently whether `B` is the quotient `A/K` itself, is the question part (2) of \
the remark raises and is asserted nowhere."
  denseRange_of_isClosedImmersion_formalSpectrumMap

end Spectrum

end AlgebraicGeometry.FormalSpace

end
