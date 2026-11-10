module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Recognising a directed presentation as a formal spectrum (Stacks 0AIC)

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an fppf sheaf over `S`
written as the colimit of a directed diagram of affine schemes over `S` along thickenings.
Suppose a linearly topologized ring `A` surjects compatibly onto the rings of sections of the
stages, with kernels which are weak ideals of definition forming a fundamental system of
neighbourhoods of `0`. Then `X` is the formal spectrum of `A`.

This is the implication (4) ⇒ (1) of **Stacks 0AIC** with the presenting ring named, for a
presentation indexed by an arbitrary nonempty directed preorder: the stage ideals are cofinal
among all weak ideals of definition of `A`, so the colimit over the weak ideals of definition
collapses to the colimit of the given diagram.

This is where the argument lives. The sequential case,
`StacksFrontier/AlgebraicGeometry/FormalSpace/SectionLimitPresentation.lean`, is the instance
`I = ℕ` and proves nothing again: nothing in the argument is special to a sequence once
compatibility of the surjections is required for every relation of the index rather than only
for the successor steps.

## Main definitions

* `AlgebraicGeometry.FormalSpace.DirectedQuotients`: a presentation of `X` by affine
  thickenings indexed by a preorder, together with compatible surjections of a topological ring
  onto the section rings of the stages.

## Main results

* `AlgebraicGeometry.FormalSpace.DirectedQuotients.exists_quotientSystem_formalSpectrum_iso`:
  such data produce a `AlgebraicGeometry.FormalSpace.QuotientSystem` for the ring and an
  isomorphism of `X` with the resulting formal spectrum.

## Implementation notes

A topological ring over a possibly non-affine `S` need not admit a morphism `Spec A ⟶ S`, so
the structure morphisms of its quotient spectra are the datum, as in
`AlgebraicGeometry.FormalSpace.QuotientSystem`. For a weak ideal of definition `K` that
morphism is built from any stage whose ideal it contains; the construction does not depend on
the stage, because two stages are dominated by a third — which is where directedness of the
index enters, in place of the maximum of two natural numbers.

Openness of a weak ideal of definition is what makes the stage ideals cofinal, and
`CategoryTheory.Functor.Final` turns cofinality into a comparison of colimits.

The index is not confined to `Type (u + 1)`, the universe the weak ideals of definition live
in: any index whose type is `Small.{u + 1}` will do, which is all the colimits of the sheaf
category need and which admits `ℕ` as well as the lifted indices of the canonical
presentations.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of an fppf sheaf `X` over `S` by a directed diagram of affine thickenings
whose rings of sections are the quotients of a linearly topologized ring `A` by a fundamental
system of weak ideals of definition. This is condition (4) of **Stacks 0AIC**, with the ring of
the presentation named. -/
structure DirectedQuotients (X : FppfSheaf B S hS) (A : Type u) [CommRing A]
    [TopologicalSpace A] (I : Type v) [Preorder I] [Small.{u + 1} I] where
  /-- The diagram of affine schemes over `S`. -/
  diagram : I ⥤ BigAffineFppf B S hS
  /-- Its transition morphisms are thickenings. -/
  isThickening : ∀ ⦃i j : I⦄ (f : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (diagram.map f))
  /-- Its colimit is `X`. -/
  colimitIso : X ≅ colimit (diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
  /-- The surjection of `A` onto the sections of the `i`-th stage. -/
  proj : ∀ i : I, A →+* Γ((BigAffineFppf.toScheme B S hS).obj (diagram.obj i), ⊤)
  /-- Each such map is surjective. -/
  proj_surjective : ∀ i, Function.Surjective (proj i)
  /-- The maps are compatible with every transition morphism. -/
  proj_comp : ∀ ⦃i j : I⦄ (h : i ≤ j), (((BigAffineFppf.toScheme B S hS).map
      (diagram.map (homOfLE h))).appTop).hom.comp (proj j) = proj i
  /-- Their kernels are weak ideals of definition. -/
  isWeakIdealOfDefinition_ker : ∀ i,
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (proj i))
  /-- Their kernels are a fundamental system of neighbourhoods of `0`. -/
  hasBasis_nhds_zero : (nhds (0 : A)).HasBasis (fun _ : I ↦ True)
    (fun i ↦ (RingHom.ker (proj i) : Set A))

namespace DirectedQuotients

variable {B S hS} {X : FppfSheaf B S hS} {A : Type u} [CommRing A] [TopologicalSpace A]
  {I : Type v} [Preorder I] [Small.{u + 1} I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (P : DirectedQuotients B S hS X A I)

/-- The affine scheme underlying the `i`-th stage. -/
abbrev stage (i : I) : Scheme.{u} :=
  (BigAffineFppf.toScheme B S hS).obj (P.diagram.obj i)

/-- The transition morphism of stages attached to `i ≤ j`. -/
abbrev stageMap {i j : I} (h : i ≤ j) : P.stage i ⟶ P.stage j :=
  (BigAffineFppf.toScheme B S hS).map (P.diagram.map (homOfLE h))

/-- The structure morphism of the `i`-th stage to the base. -/
abbrev stageOver (i : I) : P.stage i ⟶ S :=
  B.inclusion.map (Over.hom (P.diagram.obj i).1)

/-- The ideal cut out by the `i`-th stage. -/
abbrev ideal (i : I) : Ideal A := RingHom.ker (P.proj i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphisms of stages commute with the structure morphisms to the base. -/
theorem stageMap_comp_stageOver {i j : I} (h : i ≤ j) :
    P.stageMap h ≫ P.stageOver j = P.stageOver i := by
  change B.inclusion.map (Over.Hom.left ((P.diagram.map (homOfLE h)).1)) ≫
      B.inclusion.map (Over.hom (P.diagram.obj j).1) = _
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w ((P.diagram.map (homOfLE h)).1))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphism for `i ≤ k` is the composite of those for `i ≤ j` and `j ≤ k`. -/
theorem stageMap_trans {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    P.stageMap h ≫ P.stageMap h' = P.stageMap (h.trans h') := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphism for `i ≤ i` is the identity. -/
theorem stageMap_refl (i : I) : P.stageMap (le_refl i) = 𝟙 _ := by
  change (BigAffineFppf.toScheme B S hS).map (P.diagram.map (homOfLE (le_refl i))) = _
  rw [show homOfLE (le_refl i) = 𝟙 i from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The surjections onto the stages are compatible with every transition morphism. -/
theorem proj_comp_le {i j : I} (h : i ≤ j) :
    ((P.stageMap h).appTop).hom.comp (P.proj j) = P.proj i := P.proj_comp h

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The ideals of the stages decrease along the index. -/
theorem ideal_antitone : Antitone P.ideal := by
  intro i j hij a ha
  simpa [RingHom.mem_ker.mp ha] using (RingHom.congr_fun (P.proj_comp_le hij) a).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Every weak ideal of definition of `A` contains the ideal of some stage: it is open, hence a
neighbourhood of `0`, and the stage ideals are a fundamental system of such. -/
theorem exists_ideal_le (K : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }) :
    ∃ i : I, P.ideal i ≤ K.1 :=
  (P.hasBasis_nhds_zero.mem_iff.mp (K.2.1.mem_nhds (Ideal.zero_mem K.1))).imp fun _ h ↦ h.2

/-- The sections of the `i`-th stage are the quotient of `A` by the ideal of that stage. -/
def quotEquiv (i : I) : (A ⧸ P.ideal i) ≃+* Γ(P.stage i, ⊤) :=
  RingHom.quotientKerEquivOfSurjective (P.proj_surjective i)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The identification `quotEquiv` sends the class of `a` to the image of `a` in the sections
of the stage. -/
theorem quotEquiv_mk (i : I) (a : A) :
    P.quotEquiv i (Ideal.Quotient.mk (P.ideal i) a) = P.proj i a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (P.proj_surjective i) a

/-- The identification of the quotient of `A` by the ideal of the `i`-th stage with the ring of
sections of that stage, as an isomorphism of commutative rings. -/
def stageRingIso (i : I) : CommRingCat.of (A ⧸ P.ideal i) ≅ Γ(P.stage i, ⊤) where
  hom := CommRingCat.ofHom (P.quotEquiv i).toRingHom
  inv := CommRingCat.ofHom (P.quotEquiv i).symm.toRingHom
  hom_inv_id := by ext a; simp
  inv_hom_id := by ext a; simp

/-- The `i`-th stage is the spectrum of the quotient of `A` by its ideal. -/
def stageIso (i : I) : P.stage i ≅ Spec (.of (A ⧸ P.ideal i)) :=
  (P.stage i).isoSpec ≪≫ Scheme.Spec.mapIso (P.stageRingIso i).op

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The forward map of `stageIso` is the canonical isomorphism of the affine stage with the
spectrum of its sections, followed by the spectrum of `stageRingIso`. -/
theorem stageIso_hom (i : I) :
    (P.stageIso i).hom = (P.stage i).isoSpec.hom ≫ Spec.map (P.stageRingIso i).hom := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The identifications of the stages with the quotient spectra are natural in the stage. -/
theorem stageIso_naturality {i j : I} (h : i ≤ j) :
    P.stageMap h ≫ (P.stageIso j).hom = (P.stageIso i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) := by
  have hring : (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) ≫
      (P.stageRingIso i).hom = (P.stageRingIso j).hom ≫ (P.stageMap h).appTop := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext b
    have hb := RingHom.congr_fun (P.proj_comp_le h) b
    simp only [RingHom.coe_comp, Function.comp_apply] at hb
    simpa [stageRingIso, Ideal.Quotient.factor_mk, P.quotEquiv_mk] using hb.symm
  rw [stageIso_hom, stageIso_hom, Category.assoc, ← Spec.map_comp, hring, Spec.map_comp,
    ← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc]

/-! ### The quotient system attached to the presentation -/

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The underlying scheme of a stage is an object of the site. -/
theorem stage_contains (i : I) : B.Contains (P.stage i) := (P.diagram.obj i).1.left.2

/-- The structure morphism of the quotient spectrum of a stage, transported from the stage. -/
def stageSpecOver (i : I) : Spec (.of (A ⧸ P.ideal i)) ⟶ S :=
  (P.stageIso i).inv ≫ P.stageOver i

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The structure morphisms of the quotient spectra of the stages are compatible with the
quotient maps between stage ideals. -/
theorem stageSpecOver_compat {i j : I} (h : i ≤ j) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) ≫
      P.stageSpecOver j = P.stageSpecOver i := by
  have hfac : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) =
      (P.stageIso i).inv ≫ P.stageMap h ≫ (P.stageIso j).hom := by
    rw [P.stageIso_naturality h, Iso.inv_hom_id_assoc]
  rw [hfac, stageSpecOver, stageSpecOver, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, P.stageMap_comp_stageOver h]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The composite of two quotient maps of stage ideals is the quotient map of the smaller. -/
theorem ofHom_factor_trans {K : Ideal A} {i j : I} (hij : i ≤ j) (hi : P.ideal i ≤ K) :
    CommRingCat.ofHom (Ideal.Quotient.factor ((P.ideal_antitone hij).trans hi)) =
      CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone hij)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor hi) :=
  CommRingCat.hom_ext (Ideal.Quotient.factor_comp (P.ideal_antitone hij) hi).symm

/-- The structure morphism attached to a weak ideal of definition, built from a stage whose
ideal it contains. -/
def weakOver (K : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }) :
    Spec (.of (A ⧸ K.1)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.exists_ideal_le K).choose_spec)) ≫
    P.stageSpecOver (P.exists_ideal_le K).choose

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Passing to a later stage does not change the morphism a stage induces on the spectrum of a
quotient by a weak ideal of definition containing its ideal. -/
theorem specOver_stage_le {K : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }}
    {i j : I} (hij : i ≤ j) (hi : P.ideal i ≤ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hi)) ≫ P.stageSpecOver i =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor ((P.ideal_antitone hij).trans hi))) ≫ P.stageSpecOver j := by
  rw [P.ofHom_factor_trans hij hi, Spec.map_comp, Category.assoc, P.stageSpecOver_compat hij]

omit [Nonempty I] in
/-- The structure morphism attached to a weak ideal of definition may be computed from any
stage whose ideal it contains. -/
theorem weakOver_eq (K : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J })
    {i : I} (h : P.ideal i ≤ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ P.stageSpecOver i =
      P.weakOver K := by
  obtain ⟨k, hik, hck⟩ := exists_ge_ge i (P.exists_ideal_le K).choose
  exact (P.specOver_stage_le hik h).trans
    (P.specOver_stage_le hck (P.exists_ideal_le K).choose_spec).symm

/-- The quotient system of the presenting ring: the structure morphism of the spectrum of a
quotient by a weak ideal of definition is inherited from a stage below it. -/
def quotientSystem : QuotientSystem B S hS A where
  inSite K := by
    obtain ⟨i, hi⟩ := P.exists_ideal_le K
    have hci : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hi))) :=
      IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hi)
    refine Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hi))) ?_
    rw [← Scheme.size_congr (P.stageIso i)]
    exact P.stage_contains i
  overS K := P.weakOver K
  compatible J L h := by
    obtain ⟨i, hi⟩ := P.exists_ideal_le J
    have hfac : CommRingCat.ofHom (Ideal.Quotient.factor (hi.trans h)) =
        CommRingCat.ofHom (Ideal.Quotient.factor hi) ≫
          CommRingCat.ofHom (Ideal.Quotient.factor h) := by
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext b
      simp
    rw [← P.weakOver_eq J hi, ← P.weakOver_eq L (hi.trans h), hfac, Spec.map_comp,
      Category.assoc]

omit [Nonempty I] in
/-- The structure morphism attached to the ideal of a stage is the one transported from that
stage. -/
theorem weakOver_stage (i : I) :
    P.weakOver ⟨P.ideal i, P.isWeakIdealOfDefinition_ker i⟩ = P.stageSpecOver i := by
  rw [← P.weakOver_eq ⟨P.ideal i, P.isWeakIdealOfDefinition_ker i⟩ (le_refl (P.ideal i))]
  have hid : CommRingCat.ofHom (Ideal.Quotient.factor (le_refl (P.ideal i))) = 𝟙 _ :=
    CommRingCat.hom_ext Ideal.Quotient.factor_eq
  rw [hid, Spec.map_id, Category.id_comp]

/-! ### Comparison of the two colimits -/

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The weak ideals of definition cut out by the stages decrease along the index. -/
theorem chain_monotone :
    Monotone (fun i : I ↦ (OrderDual.toDual
      (⟨P.ideal i, P.isWeakIdealOfDefinition_ker i⟩ :
        TopologicalRing.WeakIdealOfDefinitionIndex A))) :=
  fun _ _ h ↦ P.ideal_antitone h

/-- The family of stage ideals, as a functor into the weak ideals of definition. -/
abbrev chain : I ⥤ WeakIdeals A := P.chain_monotone.functor

/-- The stage ideals are cofinal among the weak ideals of definition. -/
instance chain_final : P.chain.Final :=
  P.chain_monotone.final_functor_iff.mpr fun K ↦ P.exists_ideal_le (OrderDual.ofDual K)

/-- The underlying scheme of a stage is isomorphic to that of the corresponding stage of the
quotient system. -/
def chainStageBaseIso (i : I) :
    (P.diagram.obj i).1.left ≅ (P.quotientSystem.diagram.obj (P.chain.obj i)).1.left :=
  B.inclusion.preimageIso (show B.inclusion.obj ((P.diagram.obj i).1.left) ≅
    B.inclusion.obj ((P.quotientSystem.diagram.obj (P.chain.obj i)).1.left) from P.stageIso i)

omit [Nonempty I] in
/-- The image of `chainStageBaseIso` in schemes is `stageIso`. -/
theorem chainStageBaseIso_map (i : I) :
    B.inclusion.map (P.chainStageBaseIso i).hom = (P.stageIso i).hom :=
  B.inclusion.map_preimage _

omit [Nonempty I] in
/-- The isomorphism `chainStageBaseIso` commutes with the structure morphisms to the base. -/
theorem chainStageBaseIso_w (i : I) :
    (P.chainStageBaseIso i).hom ≫
        Over.hom ((P.quotientSystem.diagram.obj (P.chain.obj i)).1) =
      Over.hom ((P.diagram.obj i).1) := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, P.chainStageBaseIso_map]
  change (P.stageIso i).hom ≫
    P.weakOver ⟨P.ideal i, P.isWeakIdealOfDefinition_ker i⟩ = P.stageOver i
  rw [P.weakOver_stage i, stageSpecOver, Iso.hom_inv_id_assoc]

/-- Each stage of the presentation is the stage of the quotient system at the weak ideal of
definition it cuts out. -/
def chainStageIso (i : I) :
    P.diagram.obj i ≅ P.quotientSystem.diagram.obj (P.chain.obj i) :=
  ObjectProperty.isoMk _ (Over.isoMk (P.chainStageBaseIso i) (P.chainStageBaseIso_w i))

omit [Nonempty I] in
/-- The underlying morphism of schemes of `chainStageIso` is `stageIso`. -/
theorem chainStageIso_toScheme (i : I) :
    (BigAffineFppf.toScheme B S hS).map (P.chainStageIso i).hom = (P.stageIso i).hom := by
  simp only [chainStageIso, ObjectProperty.isoMk_hom]
  exact P.chainStageBaseIso_map i

/-- The presentation agrees with the restriction of the canonical diagram of the formal
spectrum along the family of stage ideals. -/
def chainDiagramIso : P.diagram ≅ P.chain ⋙ P.quotientSystem.diagram := by
  refine NatIso.ofComponents P.chainStageIso ?_
  intro i j f
  apply (BigAffineFppf.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, P.chainStageIso_toScheme, P.chainStageIso_toScheme]
  have hle : i ≤ j := leOfHom f
  have hmap : (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) = P.stageMap hle :=
    congrArg (fun g ↦ (BigAffineFppf.toScheme B S hS).map (P.diagram.map g))
      (Subsingleton.elim f (homOfLE hle))
  rw [hmap]
  exact P.stageIso_naturality hle

attribute [local instance] sheaf_hasColimits

omit [Nonempty I] in
/-- **Stacks 0AIC, (4) ⇒ (1) for a directed presentation.** A sheaf presented as the colimit of
a directed diagram of affine thickenings whose section rings are the quotients of a linearly
topologized ring `A` by a fundamental system of weak ideals of definition is the formal
spectrum of `A`: the stage ideals are cofinal among all weak ideals of definition, so the
colimit over the latter is computed along the diagram. -/
theorem exists_quotientSystem_formalSpectrum_iso (P : DirectedQuotients B S hS X A I) :
    ∃ Q : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum Q) := by
  refine ⟨P.quotientSystem, ⟨P.colimitIso ≪≫ ?_⟩⟩
  refine HasColimit.isoOfNatIso (Functor.isoWhiskerRight P.chainDiagramIso
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫ ?_
  refine HasColimit.isoOfNatIso (Functor.associator P.chain P.quotientSystem.diagram
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫ ?_
  exact Functor.Final.colimitIso P.chain (formalSpectrumDiagram P.quotientSystem)

end DirectedQuotients

end AlgebraicGeometry.FormalSpace

end
