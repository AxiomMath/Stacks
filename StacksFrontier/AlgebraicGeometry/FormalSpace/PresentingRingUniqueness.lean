module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition

/-!
# The presenting ring of a McQuillan affine formal algebraic space is unique (Stacks 0AIC)

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an fppf sheaf over `S`
which is an affine formal algebraic space. A weakly admissible topological ring `A` *presents*
`X` when `X` is the colimit of the spectra of the quotients of `A` by its weak ideals of
definition — `AlgebraicGeometry.FormalSpace.IsPresentingRing`, the datum of
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`. **Stacks 0AIC** calls such an `A`
*the* associated ring of `X`, and this file proves that it deserves the article: any two
presenting rings of one `X` are isomorphic as topological rings.

The route is the one the source takes. A weak-ideal colimit presentation of `X` by `A` is
turned into an `AlgebraicGeometry.FormalSpace.QuotientSystem` for `A` together with an
identification `X ≅ Spf A`; two presentations therefore give an isomorphism
`Spf C ≅ Spf A` of formal spectra, and **Stacks 0AN0** — full faithfulness of `Spf`, in the
form of `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq` —
converts it into continuous ring maps `A → C` and `C → A` over `S`. Each composite is a
continuous map over `S` whose formal spectrum is the identity, so by the uniqueness half of
Stacks 0AN0 it *is* the identity: the two ring maps are mutually inverse.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ContinuousHom.id`: the identity continuous homomorphism of
  topological rings over `S`.
* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.ofIso`: a weak-ideal colimit
  presentation transports along an isomorphism of the presented sheaf.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`: an
  isomorphism of formal spectra of weakly admissible rings over `S` comes from a ring
  equivalence continuous in both directions — the one whose two directions have the two
  directions of the given isomorphism for their formal spectra.
* `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_isPresentingRing`:
  **the uniqueness of the associated ring of Stacks 0AIC**, in the shape the rest of the library
  needs: two rings presenting the same affine formal algebraic space are isomorphic as
  topological rings. The implication (4) ⟹ (1) itself is
  `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasSomeSurjectivePresentation`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing`.
* `AlgebraicGeometry.FormalSpace.continuousHom_comp_eq_of_formalSpectrumMap_sq` and
  `AlgebraicGeometry.FormalSpace.toRingHom_comp_eq_of_formalSpectrumMap_sq`: the same
  uniqueness read on a *square* — a commuting square of formal spectra whose two columns are
  formal spectra of continuous homomorphisms is the formal spectrum of a commuting square of
  continuous homomorphisms.
* `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_comp_eq_of_formalSpectrum_iso_sq`:
  hence, when the two columns are isomorphisms, the two presenting arrows of the square agree
  up to ring equivalences continuous in both directions.

## Implementation notes

`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` and
`AlgebraicGeometry.FormalSpace.QuotientSystem` describe the same situation from opposite
directions, and the passage from the second to the first is
`AlgebraicGeometry.FormalSpace.QuotientSystem.weakIdealColimitPresentation` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpectrumPresentation.lean`. The passage back is
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.quotientSystem` together with
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.isoFormalSpectrum` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/PresentationQuotientSystem.lean`, which this file
imports; the uniqueness argument below is stated entirely in terms of those.

The uniqueness of the presenting ring is an isomorphism of topological rings, recorded as a
`RingEquiv` which is continuous in both directions rather than as an isomorphism in a category
of topological rings: that is the shape in which the transport lemmas of
`StacksFrontier/Topology/Algebra/AdicTopology/EquivTransport.lean` consume it.

The square section carries the two vertical morphisms of the square as variables `u` and `v`
together with the equations `hu` and `hv` identifying them with formal spectrum maps, rather
than writing those maps into the square. That is what lets a consumer supply a square stated
with a comparison isomorphism it has in hand — the one of
`AlgebraicGeometry.FormalSpace.completionComparison`, say — without rewriting under the
composition; consumers whose square is already in the formal spectrum spelling supply `rfl`.
The result is phrased with the *source* quotient systems of both columns, so the ring maps run
in the direction opposite to the morphisms of formal spectra, as they do throughout `Spf`.

No Stacks tag is registered on the square section. Stacks 0AN0 is the existence and uniqueness
of the continuous homomorphism realizing one morphism of formal spectra, carried by
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq` and, in the
ring-equivalence form, by
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`; applying the
uniqueness half to the two ways round a square is a step in the proofs that consume it, not a
clause of that tag.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The identity continuous homomorphism -/

section Id

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The identity ring map, as a continuous homomorphism of topological rings over `S`: on
quotients it is the transition map of the quotient system, whose compatibility with the
structure morphisms is the quotient system's own. -/
def ContinuousHom.id (D : QuotientSystem B S hS A) : ContinuousHom D D where
  toRingHom := RingHom.id A
  continuous := continuous_id
  overS J K h := by
    have h' : J.1 ≤ K.1 := fun x hx ↦ h hx
    have he : Ideal.quotientMap K.1 (RingHom.id A) h = Ideal.Quotient.factor h' := by
      refine Ideal.Quotient.ringHom_ext ?_
      ext a
      rfl
    rw [he]
    exact D.compatible J K h'

/-- The ring homomorphism underlying `ContinuousHom.id D` is the identity of `A`. -/
@[simp]
theorem ContinuousHom.id_toRingHom (D : QuotientSystem B S hS A) :
    (ContinuousHom.id D).toRingHom = RingHom.id A := rfl

end Id

/-! ### From a weak-ideal colimit presentation to a quotient system -/

section Presentation

variable {A : Type u} [CommRing A] [TopologicalSpace A] {X : FppfSheaf B S hS}

/-- A weak-ideal colimit presentation transports along an isomorphism of the presented sheaf:
only the identification of the colimit changes. -/
def WeakIdealColimitPresentation.ofIso {Y : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) (e : Y ≅ X) :
    WeakIdealColimitPresentation B S hS A Y where
  diagram := P.diagram
  quotientIso := P.quotientIso
  quotientIso_natural := P.quotientIso_natural
  colimitIso := e ≪≫ P.colimitIso

/-- The quotient system of **Stacks 0AIF** underlying a weak-ideal colimit presentation: the
quotient spectra lie in the site because they are isomorphic to the stages of the
presentation, and their structure morphisms to `S` are those of the stages read through the
identifications. -/
def WeakIdealColimitPresentation.quotientSystem
    (P : WeakIdealColimitPresentation B S hS A X) : QuotientSystem B S hS A where
  inSite J := by
    have hs := Scheme.size_congr (P.quotientIso (OrderDual.toDual J))
    have hlt : ((BigAffineFppf.toScheme B S hS).obj
        (P.diagram.obj (OrderDual.toDual J))).size < B.cutoff :=
      ((P.diagram.obj (OrderDual.toDual J)).1.1).property
    rwa [hs] at hlt
  overS J := (P.quotientIso (OrderDual.toDual J)).inv ≫
    B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
      (P.diagram.obj (OrderDual.toDual J))))
  compatible J L h := by
    let iL : WeakIdeals A := OrderDual.toDual L
    let iJ : WeakIdeals A := OrderDual.toDual J
    let f : iL ⟶ iJ := homOfLE (show iL ≤ iJ from h)
    have hn := P.quotientIso_natural f
    have hStage :
        (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫
            B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
              (P.diagram.obj iJ))) =
          B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
            (P.diagram.obj iL))) := by
      change B.inclusion.map
          (Over.Hom.left ((P.diagram.map f).1) ≫ Over.hom ((P.diagram.obj iJ).1)) =
        B.inclusion.map (Over.hom ((P.diagram.obj iL).1))
      rw [Functor.map_comp]
      exact congrArg B.inclusion.map (Over.w (P.diagram.map f).1)
    have hfactor :
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (show iJ.1 ≤ iL.1 from leOfHom f))) ≫ (P.quotientIso iJ).inv =
          (P.quotientIso iL).inv ≫
            (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) := by
      simpa [iL, iJ, f, Category.assoc] using
        (congrArg (fun g ↦ (P.quotientIso iL).inv ≫ g ≫ (P.quotientIso iJ).inv) hn).symm
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (show iJ.1 ≤ iL.1 from leOfHom f))) ≫
        ((P.quotientIso iJ).inv ≫
          B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
            (P.diagram.obj iJ)))) =
      (P.quotientIso iL).inv ≫
        B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
          (P.diagram.obj iL)))
    rw [← Category.assoc, hfactor, Category.assoc, hStage]

/-- The structure morphism to `S` of the quotient spectrum of `A` by `J`, in the quotient system
of a weak-ideal colimit presentation, is the inverse of the identification with the stage at
`J`, followed by the structure morphism of that stage. -/
theorem WeakIdealColimitPresentation.quotientSystem_overS
    (P : WeakIdealColimitPresentation B S hS A X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    P.quotientSystem.overS J = (P.quotientIso (OrderDual.toDual J)).inv ≫
      B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj
        (P.diagram.obj (OrderDual.toDual J)))) := rfl

/-- Each stage of a weak-ideal colimit presentation is isomorphic, as an affine scheme over
`S`, to the corresponding stage of the quotient system it induces: the underlying schemes are
identified by the presentation, and that identification is compatible with the structure
morphisms by the construction of the quotient system. -/
def WeakIdealColimitPresentation.stageIso (P : WeakIdealColimitPresentation B S hS A X)
    (j : WeakIdeals A) :
    P.diagram.obj j ≅ P.quotientSystem.diagram.obj j := by
  let Q := P.quotientSystem
  let hIso : B.inclusion.obj (Over.left (P.diagram.obj j).1) ≅
      B.inclusion.obj (Over.left (Q.stage (OrderDual.ofDual j)).1) := P.quotientIso j
  let eBase : (P.diagram.obj j).1.left ≅ (Q.stage (OrderDual.ofDual j)).1.left :=
    B.inclusion.preimageIso hIso
  have heBase : B.inclusion.map eBase.hom = hIso.hom :=
    B.inclusion.map_preimage hIso.hom
  have hQ : B.inclusion.map (Over.hom (Q.stage (OrderDual.ofDual j)).1) =
      hIso.inv ≫ B.inclusion.map (Over.hom (P.diagram.obj j).1) :=
    P.quotientSystem_overS (OrderDual.ofDual j)
  let eOver : (P.diagram.obj j).1 ≅ (Q.stage (OrderDual.ofDual j)).1 := Over.isoMk eBase (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, heBase, hQ]
    simp)
  exact ObjectProperty.isoMk _ eOver

/-- On underlying schemes, the isomorphism `P.stageIso j` is the identification `P.quotientIso j`
of the presentation. -/
theorem WeakIdealColimitPresentation.toScheme_map_stageIso_hom
    (P : WeakIdealColimitPresentation B S hS A X) (j : WeakIdeals A) :
    (BigAffineFppf.toScheme B S hS).map (P.stageIso j).hom = (P.quotientIso j).hom := by
  simp only [WeakIdealColimitPresentation.stageIso]
  exact B.inclusion.map_preimage _

/-- The diagram of a weak-ideal colimit presentation is the canonical diagram of quotient
spectra of the quotient system it induces. -/
def WeakIdealColimitPresentation.diagramIso (P : WeakIdealColimitPresentation B S hS A X) :
    P.diagram ≅ P.quotientSystem.diagram := by
  refine NatIso.ofComponents P.stageIso fun {j k} f ↦ ?_
  apply (BigAffineFppf.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, P.toScheme_map_stageIso_hom,
    P.toScheme_map_stageIso_hom]
  change (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫ (P.quotientIso k).hom =
    (P.quotientIso j).hom ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show k.1 ≤ j.1 from leOfHom f)))
  exact P.quotientIso_natural f

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AIC, the implication (4) ⟹ (1) for a weak-ideal colimit presentation.** A sheaf
presented as the colimit of the spectra of the quotients of `A` by its weak ideals of
definition is the formal spectrum of `A` for the induced quotient system. -/
def WeakIdealColimitPresentation.formalSpectrumIso
    (P : WeakIdealColimitPresentation B S hS A X) : X ≅ formalSpectrum P.quotientSystem :=
  P.colimitIso ≪≫ HasColimit.isoOfNatIso (Functor.isoWhiskerRight P.diagramIso
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

end Presentation

/-! ### Uniqueness of the presenting ring -/

section Uniqueness

attribute [local instance] sheaf_hasColimits

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
  {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- If continuous homomorphisms `g : D ⟶ E` and `g' : E ⟶ D` have the two directions of an
isomorphism of formal spectra for their formal spectra, then `g' ∘ g` is the identity. -/
private theorem comp_eq_id_of_formalSpectrumMap_eq_iso
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (e : formalSpectrum E ≅ formalSpectrum D) (g : ContinuousHom D E) (g' : ContinuousHom E D)
    (hg : formalSpectrumMap hA g = e.hom) (hg' : formalSpectrumMap hC g' = e.inv) :
    ContinuousHom.comp hC hA g' g = ContinuousHom.id D := by
  refine (existsUnique_continuousHom_formalSpectrumMap_eq hA hA
    (𝟙 (formalSpectrum D))).unique ?_ ?_
  · rw [← formalSpectrumMap_comp_eq hC hA g' g, hg, hg', e.inv_hom_id]
  · exact formalSpectrumMap_id hA (ContinuousHom.id D) rfl

/-- **Stacks 0AN0, applied in both directions.** An isomorphism of the formal spectra of two
weakly admissible topological rings over `S` is the formal spectrum of a ring equivalence
which is continuous in both directions. Each direction of the isomorphism is `Spf` of a unique
continuous ring map over `S`, and each composite is a continuous ring map over `S` whose formal
spectrum is the identity, hence by uniqueness is the identity ring map. The equivalence is the
one those two ring maps make: its two directions are `g` and `g'`, whose formal spectra are the
two directions of the given isomorphism. -/
@[stacks 0AN0 "the isomorphism of topological rings underlying an isomorphism of formal \
spectra, from the existence and uniqueness of the two continuous homomorphisms"]
theorem exists_continuous_ringEquiv_of_formalSpectrum_iso
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (e : formalSpectrum E ≅ formalSpectrum D) :
    ∃ (g : ContinuousHom D E) (g' : ContinuousHom E D) (φ : A ≃+* C),
      formalSpectrumMap hA g = e.hom ∧ formalSpectrumMap hC g' = e.inv ∧
        ⇑φ = ⇑g.toRingHom ∧ ⇑φ.symm = ⇑g'.toRingHom ∧
          Continuous φ ∧ Continuous φ.symm := by
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hC e.hom
  obtain ⟨g', hg', -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hC hA e.inv
  have hAA := comp_eq_id_of_formalSpectrumMap_eq_iso hA hC e g g' hg hg'
  have hCC := comp_eq_id_of_formalSpectrumMap_eq_iso hC hA e.symm g' g hg' hg
  have h1 : g'.toRingHom.comp g.toRingHom = RingHom.id A := by
    rw [← ContinuousHom.comp_toRingHom hC hA g' g, hAA, ContinuousHom.id_toRingHom]
  have h2 : g.toRingHom.comp g'.toRingHom = RingHom.id C := by
    rw [← ContinuousHom.comp_toRingHom hA hC g g', hCC, ContinuousHom.id_toRingHom]
  have hsymm : ((RingEquiv.ofRingHom g.toRingHom g'.toRingHom h2 h1).symm : C → A) =
      g'.toRingHom := by
    rw [RingEquiv.ofRingHom_symm]
    rfl
  refine ⟨g, g', RingEquiv.ofRingHom g.toRingHom g'.toRingHom h2 h1, hg, hg', rfl, hsymm,
    g.continuous, ?_⟩
  rw [hsymm]
  exact g'.continuous

/-- **Stacks 0AIC: the presenting ring of a McQuillan affine formal algebraic space is unique
up to isomorphism of topological rings.** If the weakly admissible topological rings `A` and
`C` over `S` both present the affine formal algebraic space `X` — each exhibiting `X` as the
colimit of the spectra of its quotients by weak ideals of definition — then `A` and `C` are
isomorphic as topological rings. -/
@[stacks 0AIC "the associated ring of a McQuillan affine formal algebraic space is well \
defined: two rings presenting one affine formal algebraic space are isomorphic as topological \
rings"]
theorem exists_continuous_ringEquiv_of_isPresentingRing {X : FppfSheaf B S hS}
    (hAX : IsPresentingRing B S hS A X) (hCX : IsPresentingRing B S hS C X) :
    ∃ φ : A ≃+* C, Continuous φ ∧ Continuous φ.symm := by
  obtain ⟨hA, ⟨PA⟩⟩ := hAX
  obtain ⟨hC, ⟨PC⟩⟩ := hCX
  obtain ⟨-, -, φ, -, -, -, -, hφ, hφ'⟩ := exists_continuous_ringEquiv_of_formalSpectrum_iso
    hA hC (PC.isoFormalSpectrum.symm ≪≫ PA.isoFormalSpectrum)
  exact ⟨φ, hφ, hφ'⟩

end Uniqueness

/-! ### A square of formal spectra descends to a square of presenting rings -/

section Square

attribute [local instance] sheaf_hasColimits

variable {A C A' C' : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
  [CommRing C'] [TopologicalSpace C'] [IsTopologicalRing C'] [IsLinearTopology C' C']
  (hA : TopologicalRing.IsWeaklyAdmissible A) (hA' : TopologicalRing.IsWeaklyAdmissible A')
  (hC : TopologicalRing.IsWeaklyAdmissible C) (hC' : TopologicalRing.IsWeaklyAdmissible C')
  {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
  {D' : QuotientSystem B S hS A'} {E' : QuotientSystem B S hS C'}

include hC in
/-- **Stacks 0AN0 read on a square.** A commuting square of formal spectra of weakly
admissible topological rings over `S` is the formal spectrum of a commuting square of
continuous homomorphisms: if the two vertical morphisms `u` and `v` of the square are the
formal spectra of `k` and `m`, then the two ways round the square are one and the same
continuous homomorphism.

Both composites are continuous homomorphisms `A' ⟶ C` over `S` whose formal spectrum is the
diagonal of the square, and Stacks 0AN0 says a morphism `Spf C ⟶ Spf A'` has exactly one such
preimage. -/
theorem continuousHom_comp_eq_of_formalSpectrumMap_sq
    (g : ContinuousHom D E) (g' : ContinuousHom D' E')
    (k : ContinuousHom D' D) (m : ContinuousHom E' E)
    (u : formalSpectrum D ⟶ formalSpectrum D') (v : formalSpectrum E ⟶ formalSpectrum E')
    (hu : formalSpectrumMap hA' k = u) (hv : formalSpectrumMap hC' m = v)
    (hsq : formalSpectrumMap hA g ≫ u = v ≫ formalSpectrumMap hA' g') :
    ContinuousHom.comp hA hA' g k = ContinuousHom.comp hC' hA' m g' := by
  refine (existsUnique_continuousHom_formalSpectrumMap_eq hA' hC
    (formalSpectrumMap hA g ≫ u)).unique ?_ ?_
  · rw [← formalSpectrumMap_comp_eq hA hA' g k, hu]
  · rw [← formalSpectrumMap_comp_eq hC' hA' m g', hv, hsq]

include hC in
/-- The square of ring maps underlying a commuting square of formal spectra: as maps
`A' → C`, the presenting arrow `g` of one column after the ring map `k` of the edge joining the
two bases is the ring map `m` of the edge joining the two targets after the presenting arrow
`g'` of the other column. -/
theorem toRingHom_comp_eq_of_formalSpectrumMap_sq
    (g : ContinuousHom D E) (g' : ContinuousHom D' E')
    (k : ContinuousHom D' D) (m : ContinuousHom E' E)
    (u : formalSpectrum D ⟶ formalSpectrum D') (v : formalSpectrum E ⟶ formalSpectrum E')
    (hu : formalSpectrumMap hA' k = u) (hv : formalSpectrumMap hC' m = v)
    (hsq : formalSpectrumMap hA g ≫ u = v ≫ formalSpectrumMap hA' g') :
    g.toRingHom.comp k.toRingHom = m.toRingHom.comp g'.toRingHom :=
  congrArg ContinuousHom.toRingHom
    (continuousHom_comp_eq_of_formalSpectrumMap_sq hA hA' hC hC' g g' k m u v hu hv hsq)

include hA hA' hC hC' in
/-- **Uniqueness of the presenting rings of a square.** A commuting square of formal spectra
whose two vertical morphisms are isomorphisms comes from a commuting square of rings in which
the two horizontal edges are ring equivalences continuous in both directions: the two
presenting arrows of the square agree up to those equivalences.

This is `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso` run
on each column, together with the square itself, which identifies the two composites by the
uniqueness half of Stacks 0AN0. It is what lets a chart square presented by one arrow of
weakly admissible rings be read as the chart square presented by another. -/
theorem exists_continuous_ringEquiv_comp_eq_of_formalSpectrum_iso_sq
    (g : ContinuousHom D E) (g' : ContinuousHom D' E')
    (d : formalSpectrum D ≅ formalSpectrum D') (e : formalSpectrum E ≅ formalSpectrum E')
    (hsq : formalSpectrumMap hA g ≫ d.hom = e.hom ≫ formalSpectrumMap hA' g') :
    ∃ (k : ContinuousHom D' D) (m : ContinuousHom E' E) (α : A' ≃+* A) (β : C' ≃+* C),
      formalSpectrumMap hA' k = d.hom ∧ formalSpectrumMap hC' m = e.hom ∧
        ⇑α = ⇑k.toRingHom ∧ ⇑β = ⇑m.toRingHom ∧
          Continuous α ∧ Continuous α.symm ∧ Continuous β ∧ Continuous β.symm ∧
            g.toRingHom.comp k.toRingHom = m.toRingHom.comp g'.toRingHom := by
  obtain ⟨k, -, α, hk, -, hα, -, hαc, hαc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hA' hA d
  obtain ⟨m, -, β, hm, -, hβ, -, hβc, hβc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hC' hC e
  exact ⟨k, m, α, β, hk, hm, hα, hβ, hαc, hαc', hβc, hβc',
    toRingHom_comp_eq_of_formalSpectrumMap_sq hA hA' hC hC' g g' k m d.hom e.hom hk hm hsq⟩

end Square

end AlgebraicGeometry.FormalSpace

end
