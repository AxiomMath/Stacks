module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Stage inclusions of a formal spectrum are thickenings

For a topological ring `R`, the transition morphisms of a quotient system of `R` are thickenings,
and the transition morphisms of the canonical diagram of the formal spectrum are monomorphisms of
sheaves. Consequently every stage inclusion `Spec (R ⧸ J) ⟶ Spf R` is a representable thickening.

## Main results

* `quotientSystem_transition_isThickening'`: a transition morphism of a quotient system is a
  thickening.
* `mono_formalSpectrumDiagram_map'`: a transition morphism of the canonical diagram of a formal
  spectrum is a monomorphism.
* `formalSpectrumInclusion_isThickening'`: a stage inclusion of a formal spectrum is a
  representable thickening.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe w₂ w₁ v u

section Bridges

end Bridges

section WeakIdealIndex

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A transition morphism of a quotient system is a thickening: an element of the larger weak
ideal of definition is topologically nilpotent, hence nilpotent modulo the smaller one. -/
theorem quotientSystem_transition_isThickening' {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (D : QuotientSystem B S hS R)
    {J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ L.1) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.transition h)) := by
  change Stacks.Thickenings.IsThickening
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
  have hsur := Ideal.Quotient.factor_surjective h
  refine ⟨_root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ hsur, ?_⟩
  intro P
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h))
  rw [range_comap_of_surjective _ _ hsur]
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : r ∈ L.1 := Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨n, hn⟩ := (L.property.2 r hr).exists_pow_mem_of_mem_nhds
    (J.property.1.mem_nhds J.1.zero_mem)
  apply P.isPrime.mem_of_pow_mem (n := n)
  have hz : (Ideal.Quotient.mk J.1 r) ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  rw [hz]
  exact P.asIdeal.zero_mem

end WeakIdealIndex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section StageInclusion

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A transition morphism of the canonical diagram of a formal spectrum is a monomorphism of
sheaves: it is the spectrum of a surjection of rings, hence a closed immersion and so a
monomorphism of schemes, and the sheafified Yoneda embedding preserves that. -/
theorem mono_formalSpectrumDiagram_map' (D : QuotientSystem B S hS R)
    {I J : OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }}
    (g : I ⟶ J) : Mono ((formalSpectrumDiagram D).map g) := by
  apply Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying
    (BigFppfOver.topology B S hS) (BigFppfOver.toScheme B S hS)
  change Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g))))
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g)))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective (leOfHom g))
  infer_instance

/-- A stage inclusion `Spec (R ⧸ J) ⟶ Spf R` of a formal spectrum is a representable
thickening, by **Stacks 0AI9** applied to the presenting diagram of quotient spectra.

Nothing is assumed of `R` beyond non-emptiness of the index of weak ideals of definition; in
particular it need not be weakly admissible. -/
theorem formalSpectrumInclusion_isThickening'
    [Nonempty { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }]
    (D : QuotientSystem B S hS R)
    (J : OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (formalSpectrumInclusion D J) := by
  let _ : IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) := TopologicalRing.isDirected_weakIdealOfDefinitionIndex R
  let e₀ : ULift.{u + 1}
        (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) ≃o
      OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    { toEquiv := Equiv.ulift, map_rel_iff' := Iff.rfl }
  let H := e₀.equivalence.functor
  let E := H ⋙ D.diagram
  let F := formalSpectrumDiagram D
  have ht : ∀ ⦃i j⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.diagram.map f)) :=
    fun _ _ f => quotientSystem_transition_isThickening' D (leOfHom f)
  let _ : IsDirected (ULift.{u + 1}
      (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })) (· ≤ ·) :=
    ⟨fun I K => by
      obtain ⟨L, hI, hK⟩ :=
        (TopologicalRing.isDirected_weakIdealOfDefinitionIndex R).1 I.down K.down
      exact ⟨ULift.up L, hI, hK⟩⟩
  let hc := (colimit.isColimit F).whiskerEquivalence e₀.equivalence
  let e : colimit (H ⋙ F) ≅ formalSpectrum D :=
    (colimit.isColimit (H ⋙ F)).coconePointUniqueUpToIso hc
  have he : colimit.ι (H ⋙ F) (ULift.up J) ≫ e.hom = formalSpectrumInclusion D J :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (H ⋙ F)) hc (ULift.up J)
  have hr := isThickening_colimitι B S hS E (fun {_ _} f => ht (H.map f))
    (formalSpectrum D) e (ULift.up J)
  have he' : colimit.ι (E ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (ULift.up J) ≫ e.hom =
      formalSpectrumInclusion D J := he
  rwa [he'] at hr

end StageInclusion

section IdealComparison

variable {R : Type u} [CommRing R] [TopologicalSpace R]

end IdealComparison

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]

variable [IsTopologicalRing C] [IsLinearTopology C C]

end AlgebraicGeometry.FormalSpace

end
