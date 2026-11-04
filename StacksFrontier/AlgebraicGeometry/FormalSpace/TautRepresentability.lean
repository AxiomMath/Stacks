module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine

/-!
# Representability of a taut morphism of formal spectra over a point factoring through a stage

Let `φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over a
scheme `S` and let `I` be a weak ideal of definition of `A`. A point `U ⟶ Spf A` of the formal
spectrum which factors through the stage `Spec (A ⧸ I)` has
```
U ×_{Spf A} Spf C = U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)
```
with `K` the closure of `φ(I)C`, so the base change of `Spf φ` along such a point is
represented by an object of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_factorsThroughStage`
  and `AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_factorsThroughStage'`:
  the base change of `Spf φ` along a point of `Spf A` factoring through a stage is
  represented by an object of the site, in the form of a cartesian square; in the primed form
  the projection is moreover an affine morphism of schemes.
* `AlgebraicGeometry.FormalSpace.exists_factorsThroughStage_of_isQuasiCompactObject`: a point of
  `Spf A` out of a quasi-compact object of the site does factor through a stage.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_isQuasiCompactObject`:
  the two combined: the base change along a point out of a quasi-compact object of the site is
  represented by an object of the site.
* `AlgebraicGeometry.FormalSpace.small_formalSpectrum_sections_of_isQuasiCompactObject` and
  `AlgebraicGeometry.FormalSpace.small_formalSpectrum_sections`: the sections of a formal
  spectrum over an object of the site form a `u`-small type, with no set-theoretic
  hypothesis.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheafified Yoneda embedding of the big fppf site over `S` preserves fibre products. -/
alias preservesLimitsOfShape_walkingCospan_sheafifiedYoneda :=
  preservesLimitsOfShape_sheafifiedYoneda

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- The base change of `Spf φ` along a point factoring through a stage is represented by an
object of the site, by an affine morphism to the source. -/
private theorem exists_isPullback_affine_of_factorsThroughStage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS)
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
          formalSpectrumInclusion D I) ∧
      IsAffineHom ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigAffineFppf.inclusion B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  let P := MorphismProperty.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let _ : P.IsStableUnderBaseChange := ⟨fun h hp =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{u})
      (h.map (BigFppfOver.toScheme B S hS)) hp⟩
  obtain ⟨K, -, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf I
  have hrep : P.relative F (F.map (T.map (f.stageMap I K hIK))) :=
    (MorphismProperty.relative_map_iff (P := P) (F := F)).2
      (inferInstanceAs
        (IsAffineHom ((BigAffineFppf.toScheme B S hS).map (f.stageMap I K hIK))))
  exact ⟨hrep.rep.pullback (F.map g), hrep.rep.snd (F.map g),
    F.map (hrep.rep.fst' (F.map g)) ≫ formalSpectrumInclusion E K,
    ((hrep.rep.isPullback' (F.map g)).flip.paste_vert hsq.flip).flip,
    hrep.property_snd (F.map g)⟩

/-- **The representable base change of Stacks 0AN5.** Let `φ : A ⟶ C` be a taut continuous
homomorphism of weakly admissible topological rings over `S`, let `I` be a weak ideal of
definition of `A`, and let `U ⟶ Spf A` be a point of the formal spectrum which factors through
the stage `Spec (A ⧸ I)`. Then the base change of `Spf φ` along that point is represented by an
object `V` of the site, namely `U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)` with `K` the closure of
`φ(I)C`. -/
theorem exists_isPullback_formalSpectrumMap_of_factorsThroughStage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS)
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
          formalSpectrumInclusion D I) := by
  obtain ⟨V, p, q, hpb, -⟩ :=
    exists_isPullback_affine_of_factorsThroughStage B S hS hA hC D E f hf I U g
  exact ⟨V, p, q, hpb⟩

/-- **The representable base change of Stacks 0AN5.** Let `φ : A ⟶ C` be a taut continuous
homomorphism of weakly admissible topological rings over `S`, let `I` be a weak ideal of
definition of `A`, and let `U ⟶ Spf A` be a point of the formal spectrum which factors through
the stage `Spec (A ⧸ I)`. Then the base change of `Spf φ` along that point is represented by an
object `V` of the site, namely `U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)` with `K` the closure of
`φ(I)C`, and the projection `V ⟶ U` is affine. -/
theorem exists_isPullback_formalSpectrumMap_of_factorsThroughStage'
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS)
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
          formalSpectrumInclusion D I) ∧
      IsAffineHom ((BigFppfOver.toScheme B S hS).map p) := by
  exact exists_isPullback_affine_of_factorsThroughStage B S hS hA hC D E f hf I U g

/-- **A point of a formal spectrum out of a quasi-compact object of the site factors through a
quotient stage.** -/
theorem exists_factorsThroughStage_of_isQuasiCompactObject
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (U : BigFppfOver B S hS)
    (hU : (BigFppfOver.topology B S hS).IsQuasiCompactObject U)
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        formalSpectrumInclusion D I = ξ := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : Nonempty (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    ⟨OrderDual.toDual ⟨hA.1.choose, hA.1.choose_spec⟩⟩
  let _ : IsDirected (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) :=
    ⟨fun I K => ⟨OrderDual.toDual ⟨I.1 ⊓ K.1, I.2.1.inter K.2.1, fun x hx => I.2.2 x hx.1⟩,
      show I.1 ⊓ K.1 ≤ I.1 from inf_le_left, show I.1 ⊓ K.1 ≤ K.1 from inf_le_right⟩⟩
  obtain ⟨I, g, hg⟩ := compact_map_factors_through_filtered_colimit
    (formalSpectrumDiagram D) (fun _ _ h => mono_formalSpectrumDiagram_map' B S hS D h) U hU ξ
  exact ⟨I, F.preimage g, by rwa [F.map_preimage]⟩

/-- **The representable base change of Stacks 0AN5 over a quasi-compact point.** For a taut
continuous homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S`, the base
change of `Spf φ` along any point of `Spf A` whose source is a quasi-compact object of the site
is represented by an object of the site, by an affine morphism to that source. -/
theorem exists_isPullback_formalSpectrumMap_of_isQuasiCompactObject
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (U : BigFppfOver B S hS)
    (hU : (BigFppfOver.topology B S hS).IsQuasiCompactObject U)
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f) ξ ∧
      IsAffineHom ((BigFppfOver.toScheme B S hS).map p) := by
  obtain ⟨I, g, hg⟩ := exists_factorsThroughStage_of_isQuasiCompactObject B S hS hA D U hU ξ
  obtain ⟨V, p, q, hpb, hp⟩ :=
    exists_isPullback_formalSpectrumMap_of_factorsThroughStage' B S hS hA hC D E f hf I U g
  exact ⟨V, p, q, hg ▸ hpb, hp⟩

/-- **The representable base change of Stacks 0AN5 over a point with compact source.** The
statement of `exists_isPullback_formalSpectrumMap_of_isQuasiCompactObject` at a point whose
source has compact underlying scheme. -/
theorem exists_isPullback_formalSpectrumMap_of_isAffine
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f) ξ ∧
      IsAffineHom ((BigFppfOver.toScheme B S hS).map p) :=
  exists_isPullback_formalSpectrumMap_of_isQuasiCompactObject B S hS hA hC D E f hf U
    (isQuasiCompactObject_over_of_compact_scheme B S hS U) ξ

/-! ### Smallness of the sections of a formal spectrum -/

/-- **The sections of a formal spectrum over a quasi-compact object of the site are
`u`-small.** -/
theorem small_formalSpectrum_sections_of_isQuasiCompactObject
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (U : BigFppfOver B S hS)
    (hU : (BigFppfOver.topology B S hS).IsQuasiCompactObject U) :
    Small.{u} ((formalSpectrum D).obj.obj (Opposite.op U)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigAffineFppf.inclusion B S hS
  apply small_of_surjective
    (f := fun p : Σ I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
          (U ⟶ T.obj (D.stage I)) =>
      Sheaf.sectionEquiv J (F.map p.2 ≫ formalSpectrumInclusion D p.1))
  intro x
  obtain ⟨I, g, hg⟩ := exists_factorsThroughStage_of_isQuasiCompactObject B S hS hA D U hU
    ((Sheaf.sectionEquiv J).symm x)
  exact ⟨⟨I, g⟩, (congrArg (Sheaf.sectionEquiv J) hg).trans
    ((Sheaf.sectionEquiv J).apply_symm_apply x)⟩

/-- **The sections of a formal spectrum over an arbitrary object of the site are
`u`-small.** -/
theorem small_formalSpectrum_sections
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (U : BigFppfOver B S hS) :
    Small.{u} ((formalSpectrum D).obj.obj (Opposite.op U)) := by
  classical
  let X := formalSpectrum D
  choose V a ha harange hVaff using fun O => BigFppfOver.exists_affineOpen_restrict B S hS U O
  have hcov : Sieve.ofArrows V a ∈ BigFppfOver.topology B S hS U :=
    AlgebraicGeometry.Space.generate_ofArrows_mem_topology_of_openCover B S hS V a ha (by
      intro y
      have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hy
      obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      obtain ⟨z, hz⟩ : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (a O)) := by
        rwa [harange O]
      exact ⟨O, z, hz⟩)
  have hsmall : ∀ O, Small.{u} (X.obj.obj (Opposite.op (V O))) := fun O => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (V O)) := hVaff O
    exact small_formalSpectrum_sections_of_isQuasiCompactObject B S hS hA D (V O)
      (isQuasiCompactObject_over_of_compact_scheme B S hS (V O))
  apply small_of_injective (f := fun x : X.obj.obj (Opposite.op U) =>
    fun O => (equivShrink.{u} _) (X.obj.map (a O).op x))
  intro x y h
  apply X.property.isSeparated _ _ hcov x y
  rintro Z g ⟨W, b, c, ⟨O⟩, rfl⟩
  have hO : X.obj.map (a O).op x = X.obj.map (a O).op y :=
    (equivShrink.{u} _).injective (congrFun h O)
  simp only [op_comp, X.obj.map_comp, types_comp_apply, hO]

end AlgebraicGeometry.FormalSpace

end
