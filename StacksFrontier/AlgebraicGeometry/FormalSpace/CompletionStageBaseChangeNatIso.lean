module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageNaturality

/-!
# The stagewise base changes of `Spf A^∧ ⟶ Spf B` are the quotient stages, naturally in `J`

Let `S` be a scheme of a big fppf site, let `B` be a weakly admissible topological ring over
`S` presented by a quotient system `D`, let `f : B →+* A` be a ring map and let
`g : D ⟶ E` present the canonical map `B → A^∧` to the relative completion. **Stacks 0ANM**,
in the form `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_kerProjection`,
identifies the base change of `Spf (g) : Spf A^∧ ⟶ Spf B` along the quotient stage
`Spec (B ⧸ J) ⟶ Spf B` with `Spec (A ⧸ JA)` — but one weak ideal of definition `J` of `B` at a
time. This file assembles those identifications into an isomorphism of *diagrams* indexed by
the weak ideals of definition of `B` ordered by reverse inclusion, which is the shape the
colimit assembly
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` consumes.

## Main definitions

* `CategoryTheory.Limits.natIsoBaseChangeDiagram`: a diagram sitting in a natural family of
  pullback squares over the legs of a cocone *is* the base change of that cocone's diagram.
* `AlgebraicGeometry.FormalSpace.kerProjectionStageProjection`: the quotient-stage maps
  `Spec (A ⧸ JA) ⟶ Spec (B ⧸ J)` as a natural transformation
  `kerProjectionDiagram f ⋙ formalSpectrumDiagram E ⟶ formalSpectrumDiagram D`.
* `AlgebraicGeometry.FormalSpace.kerProjectionStageBaseChangeNatIso`: the stagewise
  identification of Stacks 0ANM, natural in `J`.
* `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageBaseChangeNatIso`: a sheaf over
  `Spf B` whose stagewise base changes are naturally those of `Spf A^∧` is `Spf A^∧`.

## Main results

* `AlgebraicGeometry.FormalSpace.ContinuousHom.transition_comp_stageMap`: the quotient-stage
  maps of a continuous homomorphism commute with the transition morphisms on both sides.

## Implementation notes

The componentwise isomorphism is `CategoryTheory.IsPullback.isoPullback` of Stacks 0ANM, so
the only content here is the pair of naturality squares, one for each projection out of the
fibre product. Over the projection to `Spf A^∧` the square is the cocone identity
`CategoryTheory.Limits.colimit.w` of the colimit presenting `Spf A^∧`; over the projection to
the stage `Spec (B ⧸ J)` it is the commuting square relating the quotient-stage maps of `g`
to the transition morphisms of the two quotient systems, which is
`AlgebraicGeometry.FormalSpace.ContinuousHom.transition_comp_stageMap` and reduces on
elements to `b ↦ g(b) mod ker (A^∧ → A ⧸ JA)` computed in two orders. That square is stated
for an arbitrary continuous homomorphism; the library previously carried only its degenerate
case `continuousHom_stageMap_comp_transition`, with the target ideal held fixed, and that one
is private to `StacksFrontier/AlgebraicGeometry/FormalSpace/FormalSpectrum.lean`.

`CategoryTheory.Limits.natIsoBaseChangeDiagram` belongs beside
`CategoryTheory.Limits.baseChangeDiagram` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/StageBaseChangeColimit.lean`; it is stated here so
that this file is a leaf.

What is *not* proved here is the stagewise identification for an arbitrary sheaf `V` over
`Spf B` with representable étale structure morphism, which is what the essential surjectivity
half of Stacks 0AN8 needs: this file supplies it only for `V = Spf A^∧` with its canonical
morphism, where it is Stacks 0ANM and carries no information about `Spf A^∧` that
Stacks 0ANM did not already carry. The residual is isolated by
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageBaseChangeNatIso`, whose hypothesis is
a natural isomorphism `stageBaseChangeDiagram D v ≅ stageBaseChangeDiagram D (Spf g)` between
the stage base changes of the two sheaves. Producing that needs the *uniqueness* clause of
Stacks 0ALI for the two étale `B ⧸ J`-algebras lifting one étale `B ⧸ J₀`-algebra, read in the
site rather than in rings; the library carries Stacks 0ALI only ring-theoretically
(`TopologicalRing.etaleBaseChange_isEquivalence_and_henselianPair_map_quotient`), and the
affine models of the stages `Spec (B ⧸ J) ×_{Spf B} V` that the ring-theoretic form would be
applied to are available functorially in `J` from
`AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation` but only up to the
unspecified isomorphism that statement's existential leaves.

## References

* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₁ v₂ w₁ w₂ u

namespace CategoryTheory.Limits

section BaseChange

variable {Q : Type w₁} [Category.{w₂} Q] [HasPullbacks Q] {I : Type v₁} [Category.{v₂} I]
  {F : I ⥤ Q} (c : Cocone F) {V : Q} (v : V ⟶ c.pt)

/-- **A diagram sitting in a natural family of pullback squares over the legs of a cocone is
the base change of that cocone's diagram.** The datum is a diagram `G`, a natural
transformation `p : G ⟶ F`, a cocone `w` on `G` with vertex `V`, and for each index a proof
that the resulting square over `c.ι.app i` and `v` is cartesian. -/
noncomputable def natIsoBaseChangeDiagram {G : I ⥤ Q} (p : G ⟶ F) (w : ∀ i, G.obj i ⟶ V)
    (hw : ∀ {i j : I} (t : i ⟶ j), G.map t ≫ w j = w i)
    (hpb : ∀ i, IsPullback (p.app i) (w i) (c.ι.app i) v) :
    G ≅ baseChangeDiagram c v :=
  NatIso.ofComponents (fun i ↦ (hpb i).isoPullback) (fun {i j} t ↦ by
    have hcond : (pullback.fst (c.ι.app i) v ≫ F.map t) ≫ c.ι.app j =
        pullback.snd (c.ι.app i) v ≫ v := by
      rw [Category.assoc, c.w t]
      exact pullback.condition
    change G.map t ≫ (hpb j).isoPullback.hom =
      (hpb i).isoPullback.hom ≫ pullback.lift _ _ hcond
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
        ← Category.assoc, IsPullback.isoPullback_hom_fst]
      exact p.naturality t
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd,
        IsPullback.isoPullback_hom_snd]
      exact hw t)

end BaseChange

end CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

section StageMapSquare

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]
  {D : QuotientSystem 𝔅 S hS A} {E : QuotientSystem 𝔅 S hS C}

/-- **The quotient-stage maps of a continuous homomorphism commute with the transition
morphisms.** For `φ : A ⟶ C` over `S`, weak ideals of definition `J ⊆ L` of `A` and `K ⊆ M` of
`C` with `φ(J) ⊆ K` and `φ(L) ⊆ M`, the square formed by the two stage maps
`Spec (C ⧸ K) ⟶ Spec (A ⧸ J)`, `Spec (C ⧸ M) ⟶ Spec (A ⧸ L)` and the two transition
morphisms commutes.

This is the naturality in *both* indices that
`AlgebraicGeometry.FormalSpace.ContinuousHom.stageMap` does not record. On elements both
composites send the class of `a ∈ A` modulo `L` to the class of `φ a` modulo `K`. -/
theorem ContinuousHom.transition_comp_stageMap (φ : ContinuousHom D E)
    {J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    {K M : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }}
    (hJL : (J : Ideal A) ≤ L.1) (hKM : (K : Ideal C) ≤ M.1)
    (hJK : (J : Ideal A) ≤ Ideal.comap φ.toRingHom K.1)
    (hLM : (L : Ideal A) ≤ Ideal.comap φ.toRingHom M.1) :
    E.transition hKM ≫ φ.stageMap J K hJK = φ.stageMap L M hLM ≫ D.transition hJL := by
  dsimp only [ContinuousHom.stageMap, QuotientSystem.transition]
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKM)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJK)) =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap M.1 φ.toRingHom hLM)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJL))
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

end StageMapSquare

section KerProjection

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] (f : B →+* A)
  {D : QuotientSystem 𝔅 S hS B}
  {E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)}

/-- **The quotient-stage maps `Spec (A ⧸ JA) ⟶ Spec (B ⧸ J)` of the canonical map
`B → A^∧`, as a natural transformation.** The source is the cofinal subdiagram of quotient
stages of `A^∧` cut out by the kernels of the projections, the target the canonical diagram of
quotient stages of `B`; naturality is
`AlgebraicGeometry.FormalSpace.ContinuousHom.transition_comp_stageMap`. -/
noncomputable def kerProjectionStageProjection (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    kerProjectionDiagram f ⋙ formalSpectrumDiagram E ⟶ formalSpectrumDiagram D where
  app J := (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
    ((BigAffineFppf.inclusion 𝔅 S hS).map
      (g.stageMap (OrderDual.ofDual J) (kerProjectionIdeal f (OrderDual.ofDual J))
        (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual J))))
  naturality J K t := by
    have hsq : E.diagram.map ((kerProjectionDiagram f).map t) ≫
          g.stageMap (OrderDual.ofDual K) (kerProjectionIdeal f (OrderDual.ofDual K))
            (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual K)) =
        g.stageMap (OrderDual.ofDual J) (kerProjectionIdeal f (OrderDual.ofDual J))
            (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual J)) ≫
          D.diagram.map t :=
      ContinuousHom.transition_comp_stageMap g (leOfHom t)
        (kerProjectionIdeal_mono f (leOfHom t))
        (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual K))
        (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual J))
    have h1 := congrArg (BigAffineFppf.inclusion 𝔅 S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map hsq
    have hL := (BigAffineFppf.inclusion 𝔅 S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map_comp
        (E.diagram.map ((kerProjectionDiagram f).map t))
        (g.stageMap (OrderDual.ofDual K) (kerProjectionIdeal f (OrderDual.ofDual K))
          (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual K)))
    have hR := (BigAffineFppf.inclusion 𝔅 S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map_comp
        (g.stageMap (OrderDual.ofDual J) (kerProjectionIdeal f (OrderDual.ofDual J))
          (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual J)))
        (D.diagram.map t)
    exact hL.symm.trans (h1.trans hR)

/-- The quotient-stage square of
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_kerProjection` read against the
natural transformation `AlgebraicGeometry.FormalSpace.kerProjectionStageProjection` and the
colimit cocone presenting `Spf B`. -/
theorem isPullback_kerProjectionStageProjection
    (hB : TopologicalRing.IsWeaklyAdmissible B) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) (J : WeakIdeals B) :
    IsPullback ((kerProjectionStageProjection f g hg).app J)
      (formalSpectrumInclusion E
        (OrderDual.toDual (kerProjectionIdeal f (OrderDual.ofDual J))))
      ((colimit.cocone (formalSpectrumDiagram D)).ι.app J) (formalSpectrumMap hB g) :=
  isPullback_formalSpectrumMap_kerProjection f hB g hg (OrderDual.ofDual J)
    (le_comap_kerProjectionIdeal f g hg (OrderDual.ofDual J))

/-- **Stacks 0ANM, natural in the weak ideal of definition of the base.** The base changes of
`Spf (g) : Spf A^∧ ⟶ Spf B` along the quotient stages of `Spf B` form the cofinal subdiagram
`J ↦ Spec (A ⧸ JA)` of quotient stages of `A^∧`.

Componentwise this is
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_kerProjection`; the content added
here is the two naturality squares. -/
noncomputable def kerProjectionStageBaseChangeNatIso
    (hB : TopologicalRing.IsWeaklyAdmissible B) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    kerProjectionDiagram f ⋙ formalSpectrumDiagram E ≅
      stageBaseChangeDiagram D (formalSpectrumMap hB g) :=
  natIsoBaseChangeDiagram _ _ (kerProjectionStageProjection f g hg)
    (fun J ↦ formalSpectrumInclusion E
      (OrderDual.toDual (kerProjectionIdeal f (OrderDual.ofDual J))))
    (fun t ↦ colimit.w (formalSpectrumDiagram E) ((kerProjectionDiagram f).map t))
    (isPullback_kerProjectionStageProjection f hB g hg)

/-- **A sheaf over `Spf B` whose stagewise base changes are naturally those of `Spf A^∧` is
`Spf A^∧`.** The given identification of diagrams of stage base changes is transported along
`AlgebraicGeometry.FormalSpace.kerProjectionStageBaseChangeNatIso` and fed to
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso`.

This is the essential surjectivity half of Stacks 0AN8 reduced to a statement about stages
alone: the colimit assembly, the cofinality transport and the identification of the stages of
`Spf A^∧` with `Spec (A ⧸ JA)` are all discharged, and what remains carried as a hypothesis is
the comparison of the stage base changes of the two sheaves. It is therefore *not* tagged. -/
noncomputable def isoFormalSpectrumOfStageBaseChangeNatIso
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (β : stageBaseChangeDiagram D v ≅
      stageBaseChangeDiagram D (formalSpectrumMap hB g)) :
    V ≅ formalSpectrum E :=
  isoFormalSpectrumOfStageNatIso f hB.1 D v E
    (β.trans (kerProjectionStageBaseChangeNatIso f hB g hg).symm)

end KerProjection

end AlgebraicGeometry.FormalSpace

end
