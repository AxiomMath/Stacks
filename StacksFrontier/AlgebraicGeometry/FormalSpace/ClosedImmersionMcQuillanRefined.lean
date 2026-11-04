module

import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan

/-!
# Closed immersions into McQuillan affine formal algebraic spaces: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan`. A declaration
of that module whose statement the round strengthened keeps its original statement there; its
strengthened form lives here under a primed name.

## Main results

* `isTaut_of_isClosedImmersion_formalSpectrumMap`: The continuous homomorphism presenting a
  closed immersion of formal spectra of weakly admissible topological rings is taut.
* `exists_formalSpectrumMap_of_isClosedImmersion`: A closed immersion from a formal algebraic
  space into the formal spectrum of a weakly admissible topological ring is the formal spectrum
  of a continuous homomorphism of weakly admissible topological rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Source

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

add_to_stacks 0AJK "part (1), the conclusion that `Y` is McQuillan: the source of a closed \
immersion of formal algebraic spaces whose target is a McQuillan affine formal algebraic space \
is again a McQuillan affine formal algebraic space. Part (1)'s three conclusions about the \
presenting homomorphism `φ : A → B` — that it is taut, that its kernel `K` is closed and that \
its image is dense — are tagged separately on \
`AlgebraicGeometry.FormalSpace.isTaut_of_isClosedImmersion_formalSpectrumMap`, \
`AlgebraicGeometry.FormalSpace.isClosed_ker_toRingHom` and \
`AlgebraicGeometry.FormalSpace.denseRange_of_isClosedImmersion_formalSpectrumMap`. The question \
part (1) raises, which conditions on `A` force `B = (A/K)^∧`, is a question and is asserted \
nowhere."
  hasSomeSurjectivePresentation_of_isClosedImmersion

end Source

section Sheaves

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Sheaves

section Rings

end Rings

section Spectrum

add_to_stacks 0AJK "part (1), the conclusion that the kernel `K ⊂ A` of the homomorphism \
`φ : A → B` presenting a closed immersion is a closed ideal. It is proved here in the stronger \
form that needs only continuity of the homomorphism and separatedness of its target, so no \
closed-immersion hypothesis appears."
  isClosed_ker_toRingHom

add_to_stacks 0AJK "part (1), the conclusion that the image `φ(A)` of the homomorphism \
`φ : A → B` presenting a closed immersion is dense in `B`. Whether `φ` is moreover surjective \
and open, equivalently whether `B` is the quotient `A/K` itself, is the question part (2) of \
the remark raises and is asserted nowhere."
  denseRange_of_isClosedImmersion_formalSpectrumMap

/-- **Stacks 0ANQ**, the tautness assertion. The continuous homomorphism presenting a closed
immersion of formal spectra of weakly admissible topological rings over `S` is taut. A closed
immersion is representable by objects of the site, which is condition (2) of Stacks 0AN5, and
condition (2) of that lemma gives tautness. -/
@[stacks 0ANQ "tautness"]
theorem isTaut_of_isClosedImmersion_formalSpectrumMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A C : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (g : ContinuousHom D E)
    (hg : IsClosedImmersion B S hS (formalSpectrumMap hA g)) :
    RingHom.IsTaut g.toRingHom :=
  isTaut_of_relativelyRepresentable_formalSpectrumMap B S hS hA hC D E g
    (isClosedImmersionInto_of_isClosedImmersion B S hS (formalSpectrumMap hA g) hg).rep

add_to_stacks 0AJK "part (1), the conclusion that the homomorphism `φ : A → B` presenting a \
closed immersion is taut."
  isTaut_of_isClosedImmersion_formalSpectrumMap

end Spectrum

section PresentingHomomorphism

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The lifted order on `ULift W` of a directed preorder `W` is directed. -/
private instance isDirected_ulift {W : Type u} [Preorder W] [IsDirected W (· ≤ ·)] :
    IsDirected (ULift.{u + 1} W) (· ≤ ·) :=
  ⟨fun i j ↦
    let ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.down j.down
    ⟨ULift.up k, hik, hjk⟩⟩

/-- A formal algebraic space `Y` presented as the colimit of a directed system of affine schemes
with thickening transitions and surjective section projections is isomorphic to the formal
spectrum of a weakly admissible topological ring, namely the limit of the section rings. -/
private theorem exists_formalSpectrum_iso_of_hasSurjectiveSectionProjections
    {W : Type u} [Preorder W] [Nonempty W] [IsDirected W (· ≤ ·)] {Y : FppfSheaf B S hS}
    (E : ULift.{u + 1} W ⥤ BigAffineFppf B S hS)
    (hEthick : ∀ ⦃i j : ULift.{u + 1} W⦄ (φ : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map φ)))
    (hYcol : Y ≅ colimit (E ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hEproj : HasSurjectiveSectionProjections B S hS E) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (E' : QuotientSystem B S hS C),
      TopologicalRing.IsWeaklyAdmissible C ∧ Nonempty (Y ≅ formalSpectrum E') := by
  let ι : ∀ ⦃w w' : W⦄, w ≤ w' → ((ULift.up w : ULift.{u + 1} W) ⟶ ULift.up w') :=
    fun _ _ h ↦ homOfLE h
  let R : W → Type u := fun w ↦
    Γ((BigAffineFppf.toScheme B S hS).obj (E.obj (ULift.up w)), ⊤)
  let t : ∀ ⦃w w' : W⦄, w ≤ w' → R w' →+* R w := fun {w w'} h ↦
    (((BigAffineFppf.toScheme B S hS).map (E.map (ι h))).appTop).hom
  have hnil : ∀ ⦃w w' : W⦄ (h : w ≤ w'), (RingHom.ker (t h)).LocallyNilpotent :=
    fun _ _ h _ ha ↦ (hEthick (ι h)).isNilpotent_of_mem_ker_appTop_of_compactSpace ha
  let P : DirectedQuotients B S hS Y (TopologicalRing.DirectedLimit t) (ULift.{u + 1} W) :=
    { diagram := E
      isThickening := hEthick
      colimitIso := hYcol
      proj := fun i ↦ TopologicalRing.DirectedLimit.proj t i.down
      proj_surjective := fun i x ↦
        let ⟨s, hs⟩ := hEproj i x
        ⟨⟨fun w' ↦ s.1 (Opposite.op (ULift.up w')), fun w₁ w₂ h ↦
          s.2 (ι h).op⟩, hs⟩
      proj_comp := fun {i j} h ↦ RingHom.ext fun a ↦
        TopologicalRing.DirectedLimit.t_proj t (show i.down ≤ j.down from h) a
      isWeakIdealOfDefinition_ker := fun i ↦
        TopologicalRing.DirectedLimit.isWeakIdealOfDefinition_ker t hnil i.down
      hasBasis_nhds_zero := (TopologicalRing.DirectedLimit.hasBasis_nhds_zero t).to_hasBasis
        (fun w _ ↦ ⟨ULift.up w, trivial, subset_rfl⟩) (fun i _ ↦ ⟨i.down, trivial, subset_rfl⟩) }
  obtain ⟨E', he⟩ := P.exists_quotientSystem_formalSpectrum_iso
  exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, E',
    TopologicalRing.DirectedLimit.isWeaklyAdmissible t hnil, he⟩

/-- **Stacks 0ANQ**, the presenting homomorphism. A closed immersion into the formal spectrum
of a weakly admissible topological ring `A` over `S`, from a formal algebraic space `Y`, is the
formal spectrum of a continuous homomorphism `A ⟶ C` of weakly admissible topological rings
over `S`, for a ring `C` presenting `Y`.

The source carries the pullback of the canonical presentation of the target by its quotient
spectra, whose transition morphisms are thickenings and whose section-ring projections are
surjective; `C` is the limit of those section rings, weakly admissible because the transitions
have locally nilpotent kernels. The recognition statement of
`AlgebraicGeometry.FormalSpace.DirectedQuotients` identifies `Y` with `Spf C`, and the full
faithfulness of `Spf`, Stacks 0AN0, turns the resulting morphism of formal spectra into the
homomorphism. -/
@[stacks 0ANQ "presenting homomorphism"]
theorem exists_formalSpectrumMap_of_isClosedImmersion
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {Y : FppfSheaf B S hS} (_hY : IsFormalAlgebraicSpace B S hS Y)
    (f : Y ⟶ formalSpectrum D) (hf : IsClosedImmersion B S hS f) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (E : QuotientSystem B S hS C),
      TopologicalRing.IsWeaklyAdmissible C ∧
        ∃ (e : Y ≅ formalSpectrum E) (g : ContinuousHom D E),
          f = e.hom ≫ formalSpectrumMap hA g := by
  classical
  let I₀ := { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }
  let W := OrderDual I₀
  let _ : Nonempty W := ⟨⟨hA.1.choose, hA.1.choose_spec⟩⟩
  let _ : IsDirected W (· ≤ ·) := ⟨fun w w' ↦
    ⟨(⟨w.1 ⊓ w'.1, ⟨w.2.1.inter w'.2.1, fun x hx ↦ w.2.2 x hx.1⟩⟩ : I₀),
      (inf_le_left : w.1 ⊓ w'.1 ≤ w.1), (inf_le_right : w.1 ⊓ w'.1 ≤ w'.1)⟩⟩
  let I := ULift.{u + 1} W
  let eOrder : W ≃o I :=
    { toEquiv := Equiv.ulift.symm
      map_rel_iff' := Iff.rfl }
  let eI : W ≌ I := eOrder.equivalence
  let _ : Nonempty I := ⟨ULift.up ⟨hA.1.choose, hA.1.choose_spec⟩⟩
  let Hs := BigAffineFppf.inclusion B S hS
  let Gs := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let d := eI.inverse ⋙ D.diagram
  have hdthick : ∀ ⦃i j : I⦄ (φ : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (d.map φ)) :=
    fun _ _ φ ↦ D.isThickening_map_diagram (eI.inverse.map φ)
  let dcol : formalSpectrum D ≅ colimit (d ⋙ Hs ⋙ Gs) := HasColimit.isoOfEquivalence eI
    (Functor.isoWhiskerRight eI.unitIso.symm (D.diagram ⋙ Hs ⋙ Gs) :
      eI.functor ⋙ (d ⋙ Hs ⋙ Gs) ≅ formalSpectrumDiagram D)
  have hdproj : HasSurjectiveSectionProjections B S hS d :=
    hasSurjectiveSectionProjections_of_weakIdealColimitPresentation B S hS A hA
      D.weakIdealColimitPresentation I d hdthick dcol
  have hfInto : IsClosedImmersionInto B S hS f :=
    isClosedImmersionInto_of_isClosedImmersion B S hS f hf
  obtain ⟨E, p, hYcol, hcart⟩ := exists_affine_pullback_presentation B S hS f
    (isAffineHom_of_isClosedImmersionInto B S hS f hfInto) d dcol
  have hEthick : ∀ ⦃i j : I⦄ (φ : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map φ)) :=
    isThickening_of_cartesian_presentation B S hS f d E p dcol hYcol hcart hdthick
  have hEproj : HasSurjectiveSectionProjections B S hS E := by
    apply hasSurjectiveSectionProjections_of_surjective_stages B S hS d E p hdproj
    intro i
    have : AlgebraicGeometry.IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (p.app i)) :=
      hfInto.2 (colimit.ι (d ⋙ Hs ⋙ Gs) i ≫ dcol.inv)
        (colimit.ι (E ⋙ Hs ⋙ Gs) i ≫ hYcol.inv) (Hs.map (p.app i)) (hcart i)
    exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigAffineFppf.toScheme B S hS).map (p.app i))).2
  obtain ⟨C, _, _, _, _, E', hC, ⟨e⟩⟩ :=
    exists_formalSpectrum_iso_of_hasSurjectiveSectionProjections B S hS E hEthick hYcol hEproj
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hC (e.inv ≫ f)
  exact ⟨C, _, _, _, _, E', hC, e, g, by rw [hg, Iso.hom_inv_id_assoc]⟩

add_to_stacks 0AJK "part (1), the conclusion that `f` corresponds to a continuous \
homomorphism `φ : A → B` of weakly admissible topological rings: a closed immersion `f` into \
`X = Spf(A)` whose source `Y` is a formal algebraic space is `Spf(φ)` for a weakly admissible \
`B` presenting `Y`, read through the identification of `Y` with `Spf(B)`. The three \
conclusions part (1) draws about `φ` are tagged on \
`AlgebraicGeometry.FormalSpace.isTaut_of_isClosedImmersion_formalSpectrumMap`, \
`AlgebraicGeometry.FormalSpace.isClosed_ker_toRingHom` and \
`AlgebraicGeometry.FormalSpace.denseRange_of_isClosedImmersion_formalSpectrumMap`, and that \
`Y` is McQuillan on \
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_of_isClosedImmersion`."
  exists_formalSpectrumMap_of_isClosedImmersion

end PresentingHomomorphism

end AlgebraicGeometry.FormalSpace

end
