module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal

/-!
# The quotient stages of `Spf A^∧ ⟶ Spf B` are étale for an étale ring map `B → A`

Let `S` be a scheme of a big fppf site, let `B` be a weakly admissible topological ring over
`S` presented by a quotient system `D`, let `f : B →+* A` be an étale ring map and let `g`
present the canonical map `B → A^∧` to the relative completion as a morphism of quotient
systems. The morphism `Spf (g) : Spf A^∧ ⟶ Spf B` of **Stacks 0AN8** has, over each quotient
stage `Spec (B ⧸ J) ⟶ Spf B`, the base change `Spec (A ⧸ JA) ⟶ Spec (B ⧸ J)`, and that
morphism of schemes is étale: the ring map `B ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)` is étale by
`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`, the first step of the proof
of **Stacks 0AN8**, which `StacksFrontier/Topology/Algebra/AdicTopology/EtaleModWeakIdeal.lean`
carries.

Consequently the base change of `Spf (g)` along *any* point of `Spf B` out of a quasi-compact
object of the site is represented by an object of the site whose projection is étale — the
source's `T ×_{Spec (B ⧸ J)} Spec (A ⧸ JA)` — because such a point factors through a stage by
**Stacks 0AIA**.

## Main results

* `etale_stageMap_canonicalMap`: the morphism of quotient stages `Spec (A^∧ ⧸ K) ⟶ Spec (B ⧸ J)`
  induced by the canonical map is étale, for `K` the kernel of the projection `A^∧ → A ⧸ JA`
  presented as the closure of the extended ideal.
* `exists_isPullback_etale_formalSpectrumMap_completionOver_of_factorsThroughStage`: for a point of
  `Spf B` factoring through a quotient stage, the base change of `Spf (g)` along it is represented
  by an object of the site whose projection is étale.
* `exists_isPullback_etale_formalSpectrumMap_completionOver_of_compactSpace`: the same at an
  arbitrary point out of a quasi-compact object of the site.

## Implementation notes

The weak ideal of definition of `A^∧` attached to `J` is the kernel of the projection
`A^∧ → A ⧸ JA` (`TopologicalRing.CompletionOver.projection_ker_isWeakIdealOfDefinition`),
which is the closure of the ideal extended along the canonical map
(`TopologicalRing.CompletionOver.ker_projection_eq_closure`, Stacks 0AN6). Presenting it in
the closure form is what lets `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage`
supply the stage square, and presenting it as a kernel is what lets
`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap` supply étaleness; the two
presentations are identified once and used in both roles.

What is *not* proved here is that `Spf (g)` is étale as a morphism of formal algebraic spaces.
That condition quantifies over every scheme-valued point of `Spf B`, while Stacks 0AIA factors
only the quasi-compact ones through a stage, so it needs a locality criterion for étaleness on
the target of the kind
`StacksFrontier/AlgebraicGeometry/FormalSpace/RepresentableFromAffinePoints.lean` provides for
being locally of finite type and for quasi-compactness. Representability by algebraic spaces
and finite type of `Spf (g)` hold without an étale hypothesis, by
`isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_completionOver` and
`isFiniteType_formalSpectrumMap_completionOver`, since an étale ring map is of finite type.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A]

omit [IsTopologicalRing B] [IsLinearTopology B B] in
/-- The quotient map of the canonical map `B → A^∧` at the kernel of a projection is étale,
for an étale `f : B →+* A`. -/
private theorem etale_quotientMap_ker_projection (f : B →+* A) (hf : f.Etale)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (K : Ideal (TopologicalRing.CompletionOver f))
    (hK : K = RingHom.ker (TopologicalRing.CompletionOver.projection f J))
    (hJK : J.1 ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) K) :
    RingHom.Etale
      (Ideal.quotientMap K (TopologicalRing.CompletionOver.canonicalMap f) hJK) := by
  subst hK
  exact TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap hf J

omit [IsTopologicalRing B] [IsLinearTopology B B] in
/-- **Stacks 0AN8**, the first step of the proof read in the site. For an étale ring map
`f : B →+* A` and a weak ideal of definition `J` of `B`, the morphism of quotient stages
`Spec (A^∧ ⧸ K) ⟶ Spec (B ⧸ J)` induced by the canonical map `B → A^∧` is étale, where `K` is
the closure of the ideal extended along the canonical map — equivalently the kernel of the
projection `A^∧ → A ⧸ JA`. These are the stages of `Spf A^∧ ⟶ Spf B`. -/
@[stacks 0AN8 "the first step of the proof read in the site: for an étale ring map `B → A` \
and a weak ideal of definition `J` of `B`, the morphism `Spec (A^∧ ⧸ K) ⟶ Spec (B ⧸ J)` of \
quotient stages of `Spf A^∧ ⟶ Spf B` induced by the canonical map `B → A^∧` is étale.  The \
assertions about the morphism of formal spectra itself — representability, étaleness, full \
faithfulness, essential surjectivity, the equivalence of categories and the McQuillan \
conclusion — are not included"]
theorem etale_stageMap_canonicalMap (f : B →+* A) (hf : f.Etale)
    (D : QuotientSystem 𝔅 S hS B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J : { J : Ideal B // TopologicalRing.IsWeakIdealOfDefinition J })
    (K : { K : Ideal (TopologicalRing.CompletionOver f) //
      TopologicalRing.IsWeakIdealOfDefinition K })
    (hK : K.1 = (J.1.map g.toRingHom).closure)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom K.1) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme 𝔅 S hS).map
      ((BigAffineFppf.inclusion 𝔅 S hS).map (g.stageMap J K hJK))) := by
  have hker : K.1 = RingHom.ker (TopologicalRing.CompletionOver.projection f J) := by
    rw [hK, hg, TopologicalRing.CompletionOver.ker_projection_eq_closure]
  have hJK' : J.1 ≤
      Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) K.1 := hg ▸ hJK
  change AlgebraicGeometry.Etale
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 g.toRingHom hJK)))
  refine (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale.{u})).mpr ?_
  change RingHom.Etale (Ideal.quotientMap K.1 g.toRingHom hJK)
  simpa only [hg] using etale_quotientMap_ker_projection f hf J K.1 hker hJK'

/-- **Stacks 0AN8**, the base change over a quotient stage. For an étale `f : B →+* A` and a
point `U ⟶ Spec (B ⧸ J) ⟶ Spf B` of the formal spectrum, the base change of
`Spf (g) : Spf A^∧ ⟶ Spf B` along it is represented by the object
`U ×_{Spec (B ⧸ J)} Spec (A ⧸ JA)` of the site, and the projection to `U` is étale. -/
theorem exists_isPullback_etale_formalSpectrumMap_completionOver_of_factorsThroughStage
    (f : B →+* A) (hf : f.Etale) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (D : QuotientSystem 𝔅 S hS B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J : { J : Ideal B // TopologicalRing.IsWeakIdealOfDefinition J })
    (U : BigFppfOver 𝔅 S hS)
    (p : U ⟶ (BigAffineFppf.inclusion 𝔅 S hS).obj (D.stage J)) :
    ∃ (V : BigFppfOver 𝔅 S hS) (q : V ⟶ U)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj V ⟶ formalSpectrum E),
      IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q)
        (formalSpectrumMap hB g)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map p ≫
          formalSpectrumInclusion D J) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme 𝔅 S hS).map q) := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)
  let _ : (BigFppfOver.topology 𝔅 S hS).Subcanonical := bigFppfOver_subcanonical 𝔅 S hS
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    change PreservesLimitsOfShape WalkingCospan
      (uliftYoneda.{u + 1} (C := BigFppfOver 𝔅 S hS) ⋙
        presheafToSheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)))
    infer_instance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme 𝔅 S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme 𝔅 S hS
  set K : { K : Ideal (TopologicalRing.CompletionOver f) //
      TopologicalRing.IsWeakIdealOfDefinition K } :=
    ⟨RingHom.ker (TopologicalRing.CompletionOver.projection f J),
      TopologicalRing.projection_ker_isWeakIdealOfDefinition f J⟩ with hKdef
  have hKeq : K.1 = (J.1.map g.toRingHom).closure := by
    rw [hKdef, hg]
    exact TopologicalRing.CompletionOver.ker_projection_eq_closure f J
  have hJK : J.1 ≤ Ideal.comap g.toRingHom K.1 := by
    rw [hKeq]
    exact Ideal.map_le_iff_le_comap.mp subset_closure
  have hsq := isPullback_formalSpectrumMap_stage 𝔅 S hS hB
    (TopologicalRing.completionOver_isWeaklyAdmissible f hB) D E g J K hKeq hJK
  set w := (BigAffineFppf.inclusion 𝔅 S hS).map (g.stageMap J K hJK) with hw
  have hinner : IsPullback (pullback.fst w p) (pullback.snd w p) w p :=
    IsPullback.of_hasPullback w p
  exact ⟨pullback w p, pullback.snd w p,
    F.map (pullback.fst w p) ≫ formalSpectrumInclusion E K,
    ((hinner.map F).flip.paste_vert hsq.flip).flip,
    MorphismProperty.of_isPullback (hinner.map (BigFppfOver.toScheme 𝔅 S hS))
      (hw ▸ etale_stageMap_canonicalMap f hf D E g hg J K hKeq hJK)⟩

/-- **Stacks 0AN8**, the base change identification of its proof. For an étale ring map
`f : B →+* A` over a weakly admissible `B` and every point `T ⟶ Spf B` whose source is a
quasi-compact object of the site, the base change `T ×_{Spf B} Spf A^∧` is represented by an
object `V` of the site, namely `T ×_{Spec (B ⧸ J)} Spec (A ⧸ JA)`, and the projection
`V ⟶ T` is étale.

The point factors through a stage `Spec (B ⧸ J) ⟶ Spf B` by **Stacks 0AIA**, in the form
`exists_factorsThroughStage_of_compactSpace`, and the base change along the factorisation is
`exists_isPullback_etale_formalSpectrumMap_completionOver_of_factorsThroughStage`. -/
@[stacks 0AN8 "the base change identification of the proof: for an étale ring map `B → A` \
and a point of `Spf B` out of a quasi-compact object `T` of the site, `T ×_{Spf B} Spf A^∧` \
is represented by the object `T ×_{Spec (B ⧸ J)} Spec (A ⧸ JA)` of the site and its \
projection to `T` is étale.  The assertions about the morphism `Spf A^∧ ⟶ Spf B` itself — \
étaleness at an arbitrary scheme-valued point, full faithfulness, essential surjectivity, \
the equivalence of categories and the McQuillan conclusion — are not included"]
theorem exists_isPullback_etale_formalSpectrumMap_completionOver_of_compactSpace
    (f : B →+* A) (hf : f.Etale) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (D : QuotientSystem 𝔅 S hS B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (U : BigFppfOver 𝔅 S hS) (hU : CompactSpace ((BigFppfOver.toScheme 𝔅 S hS).obj U))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver 𝔅 S hS) (q : V ⟶ U)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj V ⟶ formalSpectrum E),
      IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q)
        (formalSpectrumMap hB g) a ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme 𝔅 S hS).map q) := by
  obtain ⟨J, p, hp⟩ := exists_factorsThroughStage_of_compactSpace hB.1 D U hU a
  obtain ⟨V, q, r, hsq, het⟩ :=
    exists_isPullback_etale_formalSpectrumMap_completionOver_of_factorsThroughStage
      f hf hB D E g hg J U p
  exact ⟨V, q, r, hp ▸ hsq, het⟩

end AlgebraicGeometry.FormalSpace

end
