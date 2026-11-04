module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf

/-!
# Global sections of a formal spectrum

The canonical map `A → Γ(Spf A, 𝒪_{Spf A})` of a topological ring into the global sections of its
formal spectrum. Since `𝒪_{Spf A} = lim 𝒪_λ`, its sections over `Spf A` are the limit of the
rings of global sections of the `𝒪_λ`, and the component of the canonical map at an ideal of
definition `I_λ` is the quotient map `A → A/I_λ` followed by the identification of `A/I_λ` with
`Γ(Spec (A/I_λ), 𝒪)`. It is continuous because each component factors through the discrete
`A/I_λ`.

## Main definitions

* `AlgebraicGeometry.spfGammaComponentOn`: the component of the canonical map at an ideal of
  definition, as a morphism of topological rings.
* `AlgebraicGeometry.spfGammaHom`: the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` of topological
  rings.

## Main results

* `TopologicalRing.continuous_quotientMk_of_isOpen`: the quotient map by an open ideal is
  continuous for the discrete topology on the quotient.
* `AlgebraicGeometry.spfGammaComponentHomOn_comp`: the components of the canonical map are
  compatible with the transition maps of the inverse system.

## Implementation notes

The source identifies `A` with `Γ(Spf A, 𝒪_{Spf A})` for an admissible `A` — the case `f = 1` of
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}`. That identification is the assertion that the map
constructed here is an isomorphism, which is where completeness of `A` enters; the map itself
needs no hypothesis beyond `A` being a topological ring.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace TopologicalRing

/-- The quotient map by an open ideal is continuous for the discrete topology on the quotient:
its fibres are the cosets of the ideal, which are open. -/
theorem continuous_quotientMk_of_isOpen (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (I : Ideal A) (hI : IsOpen (I : Set A)) :
    @Continuous A (A ⧸ I) _ ⊥ (Ideal.Quotient.mk I) := by
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x + y) '' (I : Set A), ?_, isOpenMap_add_left x _ hI,
    ⟨0, I.zero_mem, by simp⟩⟩
  rintro _ ⟨i, hi, rfl⟩
  simpa [Ideal.Quotient.eq_zero_iff_mem.2 hi] using hx

end TopologicalRing

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The component of the canonical map at a member `I` of the family: the quotient map `A → A/I`
followed by the identification of `A/I` with the global sections of `Spec (A/I)`. -/
noncomputable def spfGammaComponentHomOn (I : SpfIndex A P) :
    CommRingCat.of A ⟶ Γ(Spec (spfQuotientOn A I), ⊤) :=
  CommRingCat.ofHom (Ideal.Quotient.mk I.1) ≫ (Scheme.ΓSpecIso (spfQuotientOn A I)).inv

/-- The component of the canonical map at an ideal of definition `I`: the quotient map `A → A/I`
followed by the identification of `A/I` with the global sections of `Spec (A/I)`.

The ideals-of-definition case of `spfGammaComponentHomOn`. -/
@[reducible] noncomputable def spfGammaComponentHom (I : IdealsOfDefinition A) :
    CommRingCat.of A ⟶ Γ(Spec (spfQuotient A I), ⊤) :=
  spfGammaComponentHomOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The component of the canonical map at an ideal of definition, as a morphism of topological
rings: the global sections of `𝒪_I` carry the pseudo-discrete topology, and the component map
factors through the discrete `A/I`. -/
noncomputable def spfGammaComponentOn (I : SpfIndex A P) :
    TopCommRingCat.of A ⟶ ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor).obj I).obj (op ⊤) :=
  letI : TopologicalSpace (A ⧸ I.1) := ⊥
  letI : DiscreteTopology (A ⧸ I.1) := discreteTopology_bot _
  ⟨(spfGammaComponentHomOn A I).hom,
    continuous_pseudoDiscreteTopology_of_factorsThrough (spfComponentOn A I) ⊤
      (Ideal.Quotient.mk I.1) (continuous_quotientMk_of_isOpen A I.1 I.isWeakIdealOfDefinition.1)
      (spfGammaComponentHomOn A I).hom (Scheme.ΓSpecIso (spfQuotientOn A I)).inv.hom fun _ => rfl⟩

/-- The component of the canonical map at an ideal of definition, as a morphism of topological
rings: the global sections of `𝒪_I` carry the pseudo-discrete topology, and the component map
factors through the discrete `A/I`.

The ideals-of-definition case of `spfGammaComponentOn`. -/
@[reducible] noncomputable def spfGammaComponent (I : IdealsOfDefinition A) :
    TopCommRingCat.of A ⟶ ((spfDiagram A ⋙ pseudoDiscreteFunctor).obj I).obj (op ⊤) :=
  spfGammaComponentOn (A := A) (P := IsIdealOfDefinition) (I := I)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The components of the canonical map are compatible with the transition maps of the inverse
system: `A → A/I → A/J` is `A → A/J`, and the identifications of the quotients with rings of
global sections are natural. -/
theorem spfGammaComponentHomOn_comp {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfGammaComponentHomOn A I
        ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      = spfGammaComponentHomOn A J := by
  have key : (Scheme.ΓSpecIso (spfQuotientOn A I)).inv
        ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      = CommRingCat.ofHom (Ideal.Quotient.factor h)
        ≫ (Scheme.ΓSpecIso (spfQuotientOn A J)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hmk : CommRingCat.ofHom (Ideal.Quotient.mk I.1)
        ≫ CommRingCat.ofHom (Ideal.Quotient.factor h)
      = CommRingCat.ofHom (Ideal.Quotient.mk J.1) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (RingHom.ext fun _ => rfl)
  rw [spfGammaComponentHomOn, spfGammaComponentHomOn, Category.assoc, key, ← Category.assoc, hmk]

omit [IsTopologicalRing A] in
/-- The components of the canonical map are compatible with the transition maps of the inverse
system: `A → A/I → A/J` is `A → A/J`, and the identifications of the quotients with rings of
global sections are natural.

The ideals-of-definition case of `spfGammaComponentHomOn_comp`. -/
theorem spfGammaComponentHom_comp {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfGammaComponentHom A I
        ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      = spfGammaComponentHom A J :=
  spfGammaComponentHomOn_comp (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

variable (P) in
/-- The cone exhibiting `A` over the inverse system of the rings of global sections of the `𝒪_λ`,
whose limit is the ring of global sections of `lim 𝒪_λ`. -/
noncomputable def spfGammaConeOn : Cone ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
    (evaluation ((Opens ↥(spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op ⊤)) where
  pt := TopCommRingCat.of A
  π :=
    { app := fun I => spfGammaComponentOn A I
      naturality := fun I J h => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.comp_map]
        exact (Subtype.ext
          (congrArg CommRingCat.Hom.hom (spfGammaComponentHomOn_comp A (leOfHom h)))).symm }

/-- The cone exhibiting `A` over the inverse system of the rings of global sections of the `𝒪_λ`,
whose limit is the ring of global sections of `𝒪_{Spf A}`.

The ideals-of-definition case of `spfGammaConeOn`. -/
@[reducible] noncomputable def spfGammaCone : Cone ((spfDiagram A ⋙ pseudoDiscreteFunctor) ⋙
    (evaluation ((Opens ↥(spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op ⊤)) :=
  spfGammaConeOn (A := A) (P := IsIdealOfDefinition)

variable (P) in
/-- The canonical map `A → Γ(lim 𝒪_λ)` of topological rings, for the formal spectrum taken along
a weak ideal system: the sections of `lim 𝒪_λ` over the whole space are the limit of the rings of
global sections of the `𝒪_λ`, and `A` maps into that limit with component
`A → A/I_λ ≅ Γ(Spec (A/I_λ), 𝒪)` at `I_λ`. -/
noncomputable def spfGammaHomOn : TopCommRingCat.of A ⟶ (spfPresheafOn A P).obj (op ⊤) :=
  limit.lift _ (spfGammaConeOn A P)
    ≫ (limitObjIsoLimitCompEvaluation (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) (op ⊤)).inv

/-- The canonical map `A → Γ(Spf A, 𝒪_{Spf A})` of topological rings, for the formal spectrum
taken along the ideals of definition of `A`. -/
@[reducible] noncomputable def spfGammaHom :
    TopCommRingCat.of A ⟶ (spfPresheaf A).obj (op ⊤) :=
  spfGammaHomOn A IsIdealOfDefinition

end AlgebraicGeometry
