module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Noetherian affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an affine formal algebraic
space over `S`. Stacks 0AKM asserts the equivalence of four conditions on `X`:

1. `X` is Noetherian;
2. `X` is adic\* and every scheme `T` admitting a closed immersion `T → X` is Noetherian;
3. `X` is adic\* and for *some* presentation `X = colim X_λ` as in Stacks 0AI7 the affine
   schemes `X_λ` are Noetherian;
4. `X` is weakly adic and for *some* such presentation the affine schemes `X_λ` are
   Noetherian.

The arguments are the ones of the source, read through the identification of a presentation of
a McQuillan affine formal algebraic space with a cofinal system of weak ideals of definition of
its associated ring (`AlgebraicGeometry.FormalSpace.presentation_quotients_cofinal`). Writing
`A` for that ring, a stage of a presentation is the spectrum of `A ⧸ K` for a weak ideal of
definition `K`, and the stage is a Noetherian scheme exactly when `A ⧸ K` is a Noetherian ring.

For (1) ⇒ (3) every quotient of the Noetherian ring `A` is Noetherian. For (3) ⇒ (1) an
adic\* space has a finitely generated ideal of definition `I`, cofinality produces a stage with
`K ⊆ I`, so `A ⧸ I` is a quotient of the Noetherian ring `A ⧸ K`; as `A` is `I`-adically
complete, Stacks 05GH upgrades this to Noetherianness of `A`. For (3) ⇒ (4) an adic ring is
weakly adic. For (4) ⇒ (3), which is the substance of the tag, a weakly adic ring is admissible
with an ideal of definition `I` whose squared closure `I₂` is open (Stacks 0GXF); a stage with
`K ⊆ I₂` makes `A ⧸ I₂` Noetherian, hence `I / I₂` a finite `A`-module, and Stacks 0GXH then
produces a finitely generated ideal defining the topology. For (2) ⇒ (3) each stage inclusion
`X_λ → X` is a thickening (Stacks 0AI9), in particular a closed immersion of formal algebraic
spaces, so the hypothesis applies to it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasNoetherianAffinePresentation`: the second half of
  conditions (3) and (4), a presentation as in Stacks 0AI7 all of whose stages are Noetherian
  affine schemes.
* `AlgebraicGeometry.FormalSpace.HasNoetherianClosedSubschemes`: the second half of condition
  (2), Noetherianness of every scheme of the site that is closed-immersed in `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.isNoetherian_tfae`: conditions (1), (3) and (4) of Stacks
  0AKM are equivalent.
* `AlgebraicGeometry.FormalSpace.isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian`,
  `AlgebraicGeometry.FormalSpace.isNoetherian_of_isAdicStar`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_isAdicStar` and
  `AlgebraicGeometry.FormalSpace.isAdicStar_of_isWeaklyAdic`: the individual implications
  (1) ⇒ (3), (3) ⇒ (1), (3) ⇒ (4) and (4) ⇒ (3).
* `AlgebraicGeometry.FormalSpace.hasNoetherianAffinePresentation_of_hasNoetherianClosedSubschemes`
  and `AlgebraicGeometry.FormalSpace.isNoetherian_of_hasNoetherianClosedSubschemes`:
  condition (2) implies conditions (3) and (1).

## Implementation notes

The predicates `AlgebraicGeometry.FormalSpace.IsNoetherian`,
`AlgebraicGeometry.FormalSpace.IsAdicStar` and `AlgebraicGeometry.FormalSpace.IsWeaklyAdic` of
Stacks 0AID already contain the condition that `X` is a McQuillan affine formal algebraic
space, so the equivalence needs no separate affineness hypothesis; condition (2) carries it
through its adic\* half, and the implication (2) ⇒ (3) is therefore stated with the
affineness of `X` supplied by that half rather than as an extra assumption.

Closed immersions into `X` are taken in the sense of Stacks 0ANP,
`AlgebraicGeometry.FormalSpace.IsClosedImmersion`: representable by algebraic spaces, with
every represented base change a closed immersion of schemes. Stacks 0AI9 delivers the stage
inclusions in the different but equivalent shape of a
`CategoryTheory.MorphismProperty.relative` along the *sheafified Yoneda* embedding; the
private helpers of this file transport such a statement to the universe-lifted Yoneda
embedding of presheaves, which is what Stacks 0ANP is phrased with. The transport is possible
because the topology is subcanonical, so sheafified Yoneda is isomorphic to the Yoneda
embedding into sheaves, and the inclusion of sheaves into presheaves is fully faithful and
preserves pullbacks.

The implication (1) ⇒ (2) uses geometry that this file does not import: a closed immersion of
a scheme into an affine formal algebraic space factors through a stage of any presentation by
affine thickenings. It is therefore proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison`, which also assembles
the four conditions into a single `List.TFAE`. What is recorded here is the equivalence of
conditions (1), (3) and (4).

## References

* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0GXF](https://stacks.math.columbia.edu/tag/0GXF)
* [Stacks Project, Tag 0GXH](https://stacks.math.columbia.edu/tag/0GXH)
* [Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### Generalities on Noetherian schemes -/

/-- Noetherianness of schemes transports along an isomorphism: an isomorphism is an open
immersion, so it carries the locally Noetherian condition, and a homeomorphism carries
quasi-compactness. -/
private theorem isNoetherian_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (hY : AlgebraicGeometry.IsNoetherian Y) : AlgebraicGeometry.IsNoetherian Z := by
  have : AlgebraicGeometry.IsNoetherian Y := hY
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isOpenImmersion e.inv
  have : CompactSpace Z := e.hom.homeomorph.compactSpace
  exact AlgebraicGeometry.IsNoetherian.mk

/-- Noetherianness of schemes transports along an isomorphism: an isomorphism is an open
immersion, so it carries the locally Noetherian condition, and a homeomorphism carries
quasi-compactness.

This is the scheme-level statement; the sheaf-level
`AlgebraicGeometry.FormalSpace.isNoetherian_of_iso` is a different assertion, about the
affine type of Stacks 0AID. -/
private alias isNoetherian_scheme_of_iso := isNoetherian_of_iso

/-- A scheme isomorphic to the spectrum of a ring is Noetherian exactly when that ring is a
Noetherian ring; this is the direction that reads Noetherianness of a presentation stage off
as Noetherianness of the corresponding quotient of the presenting ring. -/
@[ega "I 10.6.5" "necessity, discrete case"]
private theorem isNoetherianRing_of_isNoetherian_of_specIso (R : Type u) [CommRing R]
    {Y : Scheme.{u}} (e : Y ≅ Spec (.of R)) (hY : AlgebraicGeometry.IsNoetherian Y) :
    IsNoetherianRing R :=
  AlgebraicGeometry.isNoetherian_Spec.mp (isNoetherian_scheme_of_iso e hY)

/-- The spectrum of a Noetherian ring is a Noetherian scheme, in the form in which the stages
of a presentation are recognised as Noetherian. -/
@[ega "I 10.6.5" "special case"]
private theorem isNoetherian_of_isNoetherianRing_of_specIso (R : Type u) [CommRing R]
    [IsNoetherianRing R] {Y : Scheme.{u}} (e : Y ≅ Spec (.of R)) :
    AlgebraicGeometry.IsNoetherian Y :=
  isNoetherian_scheme_of_iso e.symm
    (AlgebraicGeometry.isNoetherian_Spec.mpr inferInstance)

/-- In a pre-adic linearly topologized ring *every* ideal of definition defines the topology
adically: the powers of an ideal of definition contain the powers of the ideal defining the
topology, hence are open. -/
private theorem isAdic_of_isIdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (hA : TopologicalRing.IsPreAdic A) :
    _root_.IsAdic I := by
  obtain ⟨J, hJ, hJadic⟩ := hA
  obtain ⟨m, hm⟩ := hJ.2 (I : Set A) (hI.1.mem_nhds (zero_mem I))
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, hI.2⟩
  have hm' : J ^ m ≤ I := fun x hx ↦ hm hx
  have hsub : J ^ (m * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' hm' n
  have hopen : IsOpen ((J ^ (m * n) : Ideal A) : Set A) := (isAdic_iff.mp hJadic).1 (m * n)
  exact (I ^ n).toAddSubgroup.isOpen_of_mem_nhds
    (Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) hsub)

/-- Elements of an ideal of definition are topologically nilpotent. -/
private theorem isTopologicallyNilpotent_of_mem_isIdealOfDefinition {A : Type u} [CommRing A]
    [TopologicalSpace A] {I : Ideal A} (hI : TopologicalRing.IsIdealOfDefinition I) {x : A}
    (hx : x ∈ I) : IsTopologicallyNilpotent x := by
  refine tendsto_atTop_nhds.2 fun U hU hUopen ↦ ?_
  obtain ⟨m, hm⟩ := hI.2 U (hUopen.mem_nhds hU)
  exact ⟨m, fun n hn ↦ hm (Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n))⟩

/-- A quotient of a ring by a larger ideal is Noetherian if the original quotient is. -/
private theorem isNoetherianRing_quotient_of_le {A : Type u} [CommRing A] {K J : Ideal A}
    (hK : IsNoetherianRing (A ⧸ K)) (h : K ≤ J) : IsNoetherianRing (A ⧸ J) :=
  isNoetherianRing_of_surjective (A ⧸ K) (A ⧸ J) (Ideal.Quotient.factor h)
    (Ideal.Quotient.factor_surjective h)

/-! ### Recognising a closed immersion of formal algebraic spaces -/

section Transport

/-- A relative morphism property along a functor can be read along any functor isomorphic to
it, provided the latter is fully faithful. -/
private theorem relative_of_natIso {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} [G.Full] [G.Faithful] (e : F ≅ G) (P : MorphismProperty C) [P.RespectsIso]
    {X Y : D} {f : X ⟶ Y} (hf : P.relative F f) : P.relative G f := by
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨b, q, p, hpb⟩ := hf.rep ((e.app a).hom ≫ g)
  refine ⟨b, (e.app b).inv ≫ p, q, ?_, hf.property _ _ _ hpb⟩
  apply IsPullback.of_iso hpb (e.app b) (Iso.refl _) (e.app a) (Iso.refl _)
  · simp
  · exact e.hom.naturality q
  · simp
  · simp

/-- A relative morphism property along `F` becomes a relative morphism property along
`F ⋙ L` once `L` is fully faithful and preserves pullbacks: the testing morphisms along
`F ⋙ L` all come from testing morphisms along `F`, and `L` carries the cartesian squares. -/
private theorem relative_comp_of_relative {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : C ⥤ D) [F.Full] [F.Faithful] (L : D ⥤ E) [L.Full]
    [L.Faithful] [PreservesLimitsOfShape WalkingCospan L] (P : MorphismProperty C)
    [P.RespectsIso] {X Y : D} {f : X ⟶ Y} (hf : P.relative F f) :
    P.relative (F ⋙ L) (L.map f) := by
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : F.obj a ⟶ Y, L.map g₀ = g := ⟨L.preimage g, L.map_preimage g⟩
  obtain ⟨b, q, p, hpb⟩ := hf.rep g₀
  exact ⟨b, L.map p, q, hpb.map L, hf.property _ _ _ hpb⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A relative morphism property of a morphism of fppf sheaves, taken along the sheafified
Yoneda embedding, is the same property taken along the universe-lifted Yoneda embedding of its
underlying morphism of presheaves. The topology is subcanonical, so sheafified Yoneda is
isomorphic to the Yoneda embedding into sheaves, and the inclusion of sheaves into presheaves
is fully faithful and preserves pullbacks. -/
private theorem relative_uliftYoneda_of_relative_sheafifiedYoneda
    (P : MorphismProperty (BigFppfOver B S hS)) (hP : P.RespectsIso)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : P.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) :
    P.relative (uliftYoneda.{u + 1}) f.hom := by
  have : P.RespectsIso := hP
  have h₁ : P.relative
      (GrothendieckTopology.uliftYoneda.{u + 1} (BigFppfOver.topology B S hS)) f :=
    relative_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) P hf
  have h₂ := relative_comp_of_relative
    (GrothendieckTopology.uliftYoneda.{u + 1} (BigFppfOver.topology B S hS))
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) P h₁
  exact relative_of_natIso
    (GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1}
      (BigFppfOver.topology B S hS)) P h₂

/-- **Stacks 0ANP** from the shape in which Stacks 0AI9 supplies it: a morphism of fppf
sheaves all of whose base changes along sheaves represented by objects of the site are closed
immersions of schemes is a closed immersion of formal algebraic spaces. The represented base
changes are algebraic spaces because they are represented, and the closed-immersion condition
is stable under base change. -/
theorem isClosedImmersion_of_isClosedImmersionInto {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersionInto B S hS f) : IsClosedImmersion B S hS f := by
  let : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hQ := relative_uliftYoneda_of_relative_sheafifiedYoneda'
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) hf
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
    intro U ξ
    obtain ⟨V, s, p, hpb⟩ := hQ.rep ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hpb.flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V)
  refine ⟨hrep, ?_⟩
  intro U ξ
  have hstable := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  exact hstable.of_isPullback (IsPullback.of_hasPullback ξ f.hom).flip hQ

end Transport

/-! ### The four conditions of Stacks 0AKM -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The second half of conditions (3) and (4) of Stacks 0AKM: `X` has *some* presentation as a
directed colimit of affine schemes over `S` along thickenings, as in Stacks 0AI7, whose stages
are Noetherian schemes. -/
abbrev HasNoetherianAffinePresentation (X : FppfSheaf B S hS) : Prop :=
  ∃ (I : Type (u + 1)) (pre : Preorder I),
    letI : Preorder I := pre
    Nonempty I ∧ IsDirected I (· ≤ ·) ∧
      ∃ D : I ⥤ BigAffineFppf B S hS,
        (∀ ⦃i j : I⦄ (f : i ⟶ j),
          Stacks.Thickenings.IsThickening
            ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
        Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ∧
        ∀ i : I, AlgebraicGeometry.IsNoetherian
          ((BigAffineFppf.toScheme B S hS).obj (D.obj i))

/-- The second half of condition (2) of Stacks 0AKM: every scheme of the site admitting a
closed immersion into `X`, in the sense of Stacks 0ANP, is a Noetherian scheme. -/
abbrev HasNoetherianClosedSubschemes (X : FppfSheaf B S hS) : Prop :=
  ∀ (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
    IsClosedImmersion B S hS f →
      AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj T)

/-! ### Condition (1) implies condition (3) -/

/-- **Stacks 0AKM, (1) ⇒ (3).** A Noetherian affine formal algebraic space is adic\* and every
presentation of it by affine thickenings has Noetherian stages. Indeed an ideal of definition
of a Noetherian ring is finitely generated, and every stage of a presentation is the spectrum
of a quotient of the presenting ring, hence of a Noetherian ring. -/
@[stacks 0AKM "(1) ⇒ (3)"]
theorem isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian
    {X : FppfSheaf B S hS} (hX : IsNoetherian B S hS X) :
    IsAdicStar B S hS X ∧ HasNoetherianAffinePresentation B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, hP⟩, hRing, hAdic⟩ := hX
  obtain ⟨P⟩ := hP
  obtain ⟨I, hIdef, -⟩ := hAdic.1
  refine ⟨⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, ⟨P⟩⟩, hAdic,
    I, hIdef, (isNoetherianRing_iff_ideal_fg A).mp hRing I⟩, ?_⟩
  obtain ⟨-, J, pre, hne, hdir, D, hD, ⟨eD⟩, -⟩ := hSome
  refine ⟨J, pre, hne, hdir, D, hD, ⟨eD⟩, ?_⟩
  obtain ⟨K, e, -, -, -⟩ := presentation_quotients_cofinal B S hS A hWA X P J D hD eD
  intro i
  have : IsNoetherianRing A := hRing
  have : IsNoetherianRing (A ⧸ (K i).1) := Ideal.Quotient.isNoetherianRing (K i).1
  exact isNoetherian_of_isNoetherianRing_of_specIso (A ⧸ (K i).1)
    ((BigAffineFppf.toScheme B S hS).mapIso (e i) ≪≫ P.quotientIso (K i))

/-! ### Condition (3) implies condition (1) -/

/-- **Stacks 0AKM, (3) ⇒ (1).** An adic\* affine formal algebraic space with a presentation by
Noetherian affine schemes is Noetherian. Let `I` be a finitely generated ideal of definition of
the presenting ring `A`. The weak ideals of definition cutting out the stages are cofinal, so
one of them is contained in `I`; the corresponding stage being Noetherian makes `A ⧸ I` a
quotient of a Noetherian ring, and `A` is `I`-adically complete, so Stacks 05GH makes `A`
Noetherian. -/
@[stacks 0AKM "(3) ⇒ (1)"]
theorem isNoetherian_of_isAdicStar {X : FppfSheaf B S hS} (hX : IsAdicStar B S hS X)
    (hpres : HasNoetherianAffinePresentation B S hS X) : IsNoetherian B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, hP⟩, hAdic, I, hIdef, hIFG⟩ := hX
  obtain ⟨P⟩ := hP
  obtain ⟨J, pre, hne, hdir, D, hD, ⟨eD⟩, hstage⟩ := hpres
  obtain ⟨Kstage, e, -, -, hcofinal⟩ :=
    presentation_quotients_cofinal B S hS A hWA X P J D hD eD
  have hIadic : _root_.IsAdic I := Rig.idealOfDefinition_isAdic_of_isAdicRing hAdic I hIdef
  obtain ⟨i, hKI⟩ := hcofinal
    ⟨I, ⟨hIdef.1, fun x ↦ isTopologicallyNilpotent_of_mem_isIdealOfDefinition hIdef⟩⟩
  have hquot : IsNoetherianRing (A ⧸ (Kstage i).1) :=
    isNoetherianRing_of_isNoetherian_of_specIso (A ⧸ (Kstage i).1)
      ((BigAffineFppf.toScheme B S hS).mapIso (e i) ≪≫ P.quotientIso (Kstage i)) (hstage i)
  have hmodI := isNoetherianRing_quotient_of_le hquot hKI
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have hcomplete : IsAdicComplete I A :=
    hIadic.isAdicComplete_iff.mpr ⟨hWA.2.1, hWA.2.2⟩
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, ⟨P⟩⟩,
    noetherian_of_isAdicComplete_fg A I hIFG hcomplete hmodI, hAdic⟩

/-! ### Condition (3) implies condition (4) -/

/-- **Stacks 0AKM, (3) ⇒ (4).** An adic\* affine formal algebraic space is weakly adic, because
an adic topological ring is weakly adic. -/
@[stacks 0AKM "(3) ⇒ (4)"]
theorem isWeaklyAdic_of_isAdicStar {X : FppfSheaf B S hS} (hX : IsAdicStar B S hS X) :
    IsWeaklyAdic B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hAdic, -⟩ := hX
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, TopologicalRing.isWeaklyAdic_of_isAdic A hAdic⟩

/-! ### Condition (4) implies condition (3) -/

/-- **Stacks 0AKM, (4) ⇒ (3).** A weakly adic affine formal algebraic space with a
presentation by Noetherian affine schemes is adic\*.

Let `A` be the presenting ring and `I` an ideal of definition, which exists because a weakly
adic ring is admissible. By Stacks 0GXF the closure `I₂` of `I ^ 2` is open, so it is a weak
ideal of definition; cofinality of the weak ideals cutting out the stages produces a stage
contained in `I₂`, whence `A ⧸ I₂` is Noetherian. The image of `I` in `A ⧸ I₂` is then a
finitely generated module, that is `I / I₂` is a finite `A`-module, and Stacks 0GXH produces a
finitely generated ideal defining the topology of `A`. -/
@[stacks 0AKM "(4) ⇒ (3)"]
theorem isAdicStar_of_isWeaklyAdic {X : FppfSheaf B S hS} (hX : IsWeaklyAdic B S hS X)
    (hpres : HasNoetherianAffinePresentation B S hS X) : IsAdicStar B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, hP⟩, hWAdic⟩ := hX
  obtain ⟨P⟩ := hP
  have : TopologicalRing.IsWeaklyAdic A := hWAdic
  obtain ⟨I, hIdef⟩ := (TopologicalRing.isAdmissible_of_isWeaklyAdic A).1
  have hclosures := ((TopologicalRing.weaklyPreAdic_tfae.{u, 0} A).out 1 4).mp
    (inferInstance : TopologicalRing.IsWeaklyPreAdic A)
  have hI₂open : IsOpen (((I ^ 2).topologicalClosure : Ideal A) : Set A) :=
    hclosures.2 I hIdef 2 (by norm_num)
  have hIclosed : IsClosed ((I : Ideal A) : Set A) :=
    I.toAddSubgroup.isClosed_of_isOpen hIdef.1
  have hI₂le : (I ^ 2).topologicalClosure ≤ I :=
    Submodule.topologicalClosure_minimal (I ^ 2)
      (Ideal.pow_le_self (two_ne_zero (α := ℕ))) hIclosed
  obtain ⟨J, pre, hne, hdir, D, hD, ⟨eD⟩, hstage⟩ := hpres
  obtain ⟨Kstage, e, -, -, hcofinal⟩ :=
    presentation_quotients_cofinal B S hS A hWA X P J D hD eD
  obtain ⟨i, hKI₂⟩ := hcofinal ⟨(I ^ 2).topologicalClosure,
    ⟨hI₂open, fun x hx ↦ isTopologicallyNilpotent_of_mem_isIdealOfDefinition hIdef (hI₂le hx)⟩⟩
  have hquot : IsNoetherianRing (A ⧸ (Kstage i).1) :=
    isNoetherianRing_of_isNoetherian_of_specIso (A ⧸ (Kstage i).1)
      ((BigAffineFppf.toScheme B S hS).mapIso (e i) ≪≫ P.quotientIso (Kstage i)) (hstage i)
  have hmodI₂ := isNoetherianRing_quotient_of_le hquot hKI₂
  -- `I / I₂` is a finite `A`-module: it is the image of `I` in the Noetherian ring `A ⧸ I₂`.
  have _ : Module.Finite A (↥I ⧸ Submodule.comap I.subtype (I ^ 2).topologicalClosure) :=
    Ideal.finite_quotient_comap_subtype I _ hmodI₂
  obtain ⟨L, hLfg, hLadic⟩ :=
    TopologicalRing.exists_fg_isAdic_of_quotient_closure_sq_finite I hIdef
  have hLdef : TopologicalRing.IsIdealOfDefinition L := by
    refine ⟨by simpa [pow_one] using (isAdic_iff.mp hLadic).1 1, fun U hU ↦ ?_⟩
    have hU' : U ∈ @nhds A L.adicTopology 0 := by rw [← hLadic]; exact hU
    obtain ⟨n, -, hn⟩ := L.hasBasis_nhds_zero_adic.mem_iff.mp hU'
    exact ⟨n, hn⟩
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, ⟨hWA, ⟨P⟩⟩,
    ⟨⟨L, hLdef, hLadic⟩, ⟨hWAdic.toT2Space, inferInstance⟩⟩, L, hLdef, hLfg⟩

/-! ### Condition (2) implies conditions (3) and (1) -/

/-- **Stacks 0AKM, (2) ⇒ (3).** If every scheme closed-immersed in an affine formal algebraic
space `X` is Noetherian, then every presentation of `X` by affine thickenings has Noetherian
stages: by Stacks 0AI9 each stage inclusion `X_λ → X` is a thickening, in particular a closed
immersion of formal algebraic spaces, so the hypothesis applies to its source. -/
@[stacks 0AKM "(2) ⇒ (3)"]
theorem hasNoetherianAffinePresentation_of_hasNoetherianClosedSubschemes
    {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hclosed : HasNoetherianClosedSubschemes B S hS X) :
    HasNoetherianAffinePresentation B S hS X := by
  obtain ⟨-, J, pre, hne, hdir, D, hD, ⟨eD⟩⟩ := hX
  refine ⟨J, pre, hne, hdir, D, hD, ⟨eD⟩, ?_⟩
  intro i
  refine hclosed ((BigAffineFppf.inclusion B S hS).obj (D.obj i))
    (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ eD.inv) ?_
  apply isClosedImmersion_of_isClosedImmersionInto
  refine MorphismProperty.relative_monotone
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (P := MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (fun _ _ _ h ↦ h.1) _ (isThickening_colimitι B S hS D hD X eD.symm i)

/-- **Stacks 0AKM, (2) ⇒ (1).** An adic\* affine formal algebraic space all of whose
closed subschemes that are schemes are Noetherian is itself Noetherian: the stages of any
presentation are such closed subschemes, so condition (3) holds and (3) ⇒ (1) applies. -/
@[stacks 0AKM "(2) ⇒ (1)"]
theorem isNoetherian_of_hasNoetherianClosedSubschemes {X : FppfSheaf B S hS}
    (hX : IsAdicStar B S hS X) (hclosed : HasNoetherianClosedSubschemes B S hS X) :
    IsNoetherian B S hS X :=
  isNoetherian_of_isAdicStar B S hS hX
    (hasNoetherianAffinePresentation_of_hasNoetherianClosedSubschemes B S hS hX.1.1 hclosed)

/-! ### The equivalence of conditions (1), (3) and (4) -/

/-- **Stacks 0AKM, conditions (1), (3) and (4).** For an fppf sheaf `X` on the big fppf site of
`S` the following are equivalent: `X` is a Noetherian affine formal algebraic space; `X` is
adic\* and has a presentation by Noetherian affine schemes; `X` is weakly adic and has a
presentation by Noetherian affine schemes. Each condition already contains the requirement that
`X` be a McQuillan affine formal algebraic space. -/
@[stacks 0AKM "clauses (1), (3) and (4)"]
theorem isNoetherian_tfae (X : FppfSheaf B S hS) :
    List.TFAE
      [IsNoetherian B S hS X,
        IsAdicStar B S hS X ∧ HasNoetherianAffinePresentation B S hS X,
        IsWeaklyAdic B S hS X ∧ HasNoetherianAffinePresentation B S hS X] := by
  tfae_have 1 → 2 := isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS
  tfae_have 2 → 3 := fun h ↦ ⟨isWeaklyAdic_of_isAdicStar B S hS h.1, h.2⟩
  tfae_have 3 → 1 := fun h ↦
    isNoetherian_of_isAdicStar B S hS (isAdicStar_of_isWeaklyAdic B S hS h.1 h.2) h.2
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
