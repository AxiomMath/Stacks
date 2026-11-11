module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Full faithfulness of the formal spectrum (Stacks 0AN0)

Let `S` be a scheme and let `A` and `C` be weakly admissible topological rings over `S`.
**Stacks 0AN0** says that every morphism `f : Spf C ⟶ Spf A` of affine formal algebraic spaces
over `S` is `Spf` of one and only one continuous ring map `A → C` over `S`. Thus `Spf` is fully
faithful on weakly admissible topological rings over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`:
  **Stacks 0AN0**, the existence and the uniqueness of `f^♯`.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`:
  **Stacks 0AN5**, the implication from its condition (2) to its condition (1).

## Implementation notes

The construction of `f^♯` is the one of Stacks 0AN0. A weak ideal of definition `K ⊆ C` gives a
morphism `Spec (C/K) → Spf C → Spf A` from a quasi-compact algebraic space, which
`AlgebraicGeometry.exists_factor_through_thickening` (Stacks 0AIA) factors through a stage of
any presentation of `Spf A` by affine thickenings; the presentation used is the canonical one by
the weak ideals of definition of `A`, so the stage is `Spec (A/J)` for some weak ideal of
definition `J ⊆ A` and the factorisation is a ring map `A/J → C/K` over `S`. Varying `K` gives a
compatible family `A → C/K`, and `C` being complete and separated these come from a unique ring
map `A → C`; its continuity is the openness of the ideals `J`, and the equality `Spf (f^♯) = f`
is read off stage by stage from the quotient-stage characterisation of `Spf` on morphisms.

What Stacks 0AIA factors through is a presentation of the target by affine thickenings, and the
formal spectrum carries one by construction: `AlgebraicGeometry.FormalSpace`
`.exists_thickeningColimit_formalSpectrum` lifts the index of the canonical diagram of quotient
spectra to the universe presentations are indexed by. So nothing has to be assumed about the
target beyond weak admissibility — in particular not that it is an affine formal algebraic
space, whose set-theoretic condition would need a site large enough to contain the coproduct of
the quotient spectra.

Both halves of the lemma therefore rest on one inverse-limit statement for a weakly admissible
ring: a compatible family of ring maps `A → C/K`, indexed by the weak ideals of definition of
`C`, comes from a unique ring map `A → C`. Separatedness alone gives the uniqueness, hence the
uniqueness of `f^♯`; completeness gives the existence.

Two auxiliary facts about monomorphisms are needed: sheafified Yoneda preserves them when the
underlying morphism of schemes is one, and a colimit injection of a filtered diagram of sheaves
with monomorphic transition morphisms is one. Both are available only privately elsewhere in the
library, so they are reproved, the first specialised to the transition morphisms of the
canonical diagram, which are spectra of surjections and hence closed immersions.

### Stacks 0AN5, and which of its implications is proved here

Stacks 0AN5 says that for a continuous homomorphism `φ : A → C` of weakly admissible
topological rings over `S` the three conditions "`Spf φ` is representable by algebraic spaces",
"`Spf φ` is representable by schemes" and "`φ` is taut" are equivalent. Only (2) implies (1) is
proved here, and it is the formal implication: a base change of `Spf φ` along a scheme-valued
point of `Spf A` is then a scheme, and a scheme is an algebraic space. The other two
implications are the content of the lemma — (1) implies (2) is Stacks 0AKN, which this library
does not have, and (3) implies (2) runs through the identification of
`C ⊗̂_A A/I` with `C/J(I)` for `J(I)` the closure of `IC`, which is Stacks 0AMZ and is
available as `TopologicalRing.closure_map_eq_ker_completedTensorProduct`. (That
identification is not Stacks 0AMS, which is instead the description of the closure of a
submodule of a linearly topologized module.)

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter

namespace AlgebraicGeometry.FormalSpace

universe w₁ w₂ v₁ v₂ u

/-! ### A weakly admissible ring is the inverse limit of its weak quotients -/

section InverseLimit

variable {A C : Type*} [CommRing A] [CommRing C] [TopologicalSpace C]
  [IsTopologicalRing C] [IsLinearTopology C C]

/-- A separated weakly admissible ring has no nonzero element lying in every weak ideal of
definition. -/
private theorem eq_zero_of_mem_weakIdealsOfDefinition
    (hC : TopologicalRing.IsWeaklyAdmissible C) {x : C}
    (hx : ∀ I : Ideal C, TopologicalRing.IsWeakIdealOfDefinition I → x ∈ I) : x = 0 := by
  by_contra hne
  let _ : T2Space C := hC.2.2
  obtain ⟨I, hI, hIx⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).mem_iff.mp
      ((isClosed_singleton (x := x)).isOpen_compl.mem_nhds (by simpa using Ne.symm hne))
  exact hIx (hx I hI) rfl

/-- A weakly pre-admissible ring has a weak ideal of definition. -/
private theorem nonempty_weakIdeals (hC : TopologicalRing.IsWeaklyAdmissible C) :
    Nonempty (WeakIdeals C) :=
  ⟨OrderDual.toDual ⟨hC.1.choose, hC.1.choose_spec⟩⟩

omit [IsTopologicalRing C] [IsLinearTopology C C] in
/-- The weak ideals of definition are directed under reverse inclusion. -/
private theorem isDirected_weakIdeals : IsDirected (WeakIdeals C) (· ≤ ·) := by
  refine ⟨fun J K ↦ ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 K.2.1⟩, ?_, ?_⟩⟩
  · change J.1 ⊓ K.1 ≤ J.1
    exact inf_le_left
  · change J.1 ⊓ K.1 ≤ K.1
    exact inf_le_right

/-- The weak ideals of definition of a weakly admissible ring, indexed by reverse inclusion,
form a neighbourhood basis of zero. -/
private theorem hasBasis_nhds_zero_weakIdeals (hC : TopologicalRing.IsWeaklyAdmissible C) :
    (nhds (0 : C)).HasBasis (fun _ : WeakIdeals C ↦ True) (fun K ↦ (K.1 : Set C)) := by
  apply (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).to_hasBasis
  · exact fun I hI ↦ ⟨OrderDual.toDual ⟨I, hI⟩, trivial, subset_rfl⟩
  · exact fun K _ ↦ ⟨K.1, K.2, subset_rfl⟩

/-- In a complete weakly admissible ring a family of elements whose differences are eventually
in every weak ideal of definition converges. -/
private theorem exists_tendsto_of_sub_mem (hC : TopologicalRing.IsWeaklyAdmissible C)
    [Nonempty (WeakIdeals C)] [IsDirected (WeakIdeals C) (· ≤ ·)] (r : WeakIdeals C → C)
    (hr : ∀ K k l : WeakIdeals C, K ≤ k → K ≤ l → r k - r l ∈ K.1) :
    ∃ b : C, Filter.Tendsto r Filter.atTop (nhds b) := by
  have hbasis := hasBasis_nhds_zero_weakIdeals hC
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  let _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  let _ : CompleteSpace C := hC.2.1
  have hcauchy : Cauchy (Filter.map r Filter.atTop) := by
    rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
    refine ⟨inferInstance, hbasis.tendsto_right_iff.mpr fun K _ ↦ ?_⟩
    rw [Filter.prod_atTop_atTop_eq, Filter.eventually_atTop_prod_self]
    exact ⟨K, fun k l hk hl ↦ hr K k l hk hl⟩
  exact cauchy_map_iff_exists_tendsto.mp hcauchy

/-- **A weakly admissible ring is the inverse limit of its quotients by weak ideals of
definition.** A compatible family of classes modulo the weak ideals of definition is the family
of classes of a unique element. -/
private theorem existsUnique_mem_weakQuotients (hC : TopologicalRing.IsWeaklyAdmissible C)
    (x : ∀ K : WeakIdeals C, C ⧸ K.1)
    (hx : ∀ (K L : WeakIdeals C) (h : K.1 ≤ L.1), Ideal.Quotient.factor h (x K) = x L) :
    ∃! c : C, ∀ K : WeakIdeals C, Ideal.Quotient.mk K.1 c = x K := by
  classical
  let _ : Nonempty (WeakIdeals C) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hC.1
  let _ : IsDirected (WeakIdeals C) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex C
  have huniq : ∀ c d : C,
      (∀ K : WeakIdeals C, Ideal.Quotient.mk K.1 c = Ideal.Quotient.mk K.1 d) → c = d := by
    intro c d h
    refine sub_eq_zero.mp (eq_zero_of_mem_weakIdealsOfDefinition hC fun I hI ↦ ?_)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem c d).mp (h (OrderDual.toDual ⟨I, hI⟩))
  have hrep : ∀ K : WeakIdeals C, ∃ a : C, Ideal.Quotient.mk K.1 a = x K := fun K ↦
    Ideal.Quotient.mk_surjective (x K)
  choose r hr using hrep
  have hstage : ∀ K L : WeakIdeals C, K ≤ L → Ideal.Quotient.mk K.1 (r L) = x K := by
    intro K L hKL
    have h : L.1 ≤ K.1 := hKL
    calc Ideal.Quotient.mk K.1 (r L)
        = Ideal.Quotient.factor h (Ideal.Quotient.mk L.1 (r L)) :=
          (Ideal.Quotient.factor_mk h (r L)).symm
      _ = Ideal.Quotient.factor h (x L) := by rw [hr]
      _ = x K := hx L K h
  obtain ⟨b, hb⟩ := exists_tendsto_of_sub_mem hC r fun K k l hk hl ↦
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ((hstage K k hk).trans (hstage K l hl).symm)
  have hb' : ∀ K : WeakIdeals C, Ideal.Quotient.mk K.1 b = x K := by
    intro K
    have hset : {c : C | Ideal.Quotient.mk K.1 c = x K} =
        (fun c : C ↦ c - r K) ⁻¹' (K.1 : Set C) := by
      ext c
      refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
      · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem c (r K)).mp (hc.trans (hr K).symm)
      · exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem c (r K)).mpr hc).trans (hr K)
    have hclosed : IsClosed {c : C | Ideal.Quotient.mk K.1 c = x K} := by
      rw [hset]
      exact (K.1.toAddSubgroup.isClosed_of_isOpen K.2.1).preimage
        (continuous_id.sub continuous_const)
    refine hclosed.mem_of_tendsto hb ?_
    filter_upwards [Filter.eventually_ge_atTop K] with l hl
    exact hstage K l hl
  exact ⟨b, hb', fun c hc ↦ huniq c b fun K ↦ (hc K).trans (hb' K).symm⟩

/-- **A compatible family of ring maps into the weak quotients of a weakly admissible ring comes
from a unique ring map.** This is the inverse-limit property of a complete separated linearly
topologized ring, read on homomorphisms out of a fixed ring. -/
@[ega "0 7.2.1" "partial"]
private theorem existsUnique_ringHom_comp_weakQuotient_mk
    (hC : TopologicalRing.IsWeaklyAdmissible C) (ψ : ∀ K : WeakIdeals C, A →+* C ⧸ K.1)
    (hψ : ∀ (K L : WeakIdeals C) (h : K.1 ≤ L.1),
      (Ideal.Quotient.factor h).comp (ψ K) = ψ L) :
    ∃! φ : A →+* C, ∀ K : WeakIdeals C, (Ideal.Quotient.mk K.1).comp φ = ψ K := by
  classical
  have key : ∀ a : A, ∃! c : C, ∀ K : WeakIdeals C, Ideal.Quotient.mk K.1 c = ψ K a := fun a ↦
    existsUnique_mem_weakQuotients hC (fun K ↦ ψ K a)
      (fun K L h ↦ congrArg (fun q : A →+* C ⧸ L.1 ↦ q a) (hψ K L h))
  choose! g hg hgu using fun a ↦ key a
  have h1 : g 1 = 1 := (hgu 1 1 fun K ↦ by rw [map_one, map_one]).symm
  have h0 : g 0 = 0 := (hgu 0 0 fun K ↦ by rw [map_zero, map_zero]).symm
  have hmul : ∀ a b : A, g (a * b) = g a * g b := fun a b ↦
    (hgu (a * b) (g a * g b) fun K ↦ by rw [map_mul, hg a K, hg b K, map_mul]).symm
  have hadd : ∀ a b : A, g (a + b) = g a + g b := fun a b ↦
    (hgu (a + b) (g a + g b) fun K ↦ by rw [map_add, hg a K, hg b K, map_add]).symm
  refine ⟨⟨⟨⟨g, h1⟩, hmul⟩, h0, hadd⟩, fun K ↦ ?_, fun φ hφ ↦ ?_⟩
  · ext a
    exact hg a K
  · ext a
    exact hgu a (φ a) fun K ↦ congrArg (fun q : A →+* C ⧸ K.1 ↦ q a) (hφ K)

/-- A ring map into a weakly admissible ring is continuous as soon as the preimage of every weak
ideal of definition contains an open ideal. -/
private theorem continuous_of_isOpen_le_comap [TopologicalSpace A] [IsTopologicalRing A]
    (hC : TopologicalRing.IsWeaklyAdmissible C) (φ : A →+* C)
    (h : ∀ K : WeakIdeals C, ∃ J : Ideal A, IsOpen (J : Set A) ∧ J ≤ Ideal.comap φ K.1) :
    Continuous φ := by
  have hbasis := hasBasis_nhds_zero_weakIdeals hC
  refine continuous_of_continuousAt_zero φ ?_
  change Filter.Tendsto (fun a : A ↦ φ a) (nhds 0) (nhds (φ 0))
  rw [map_zero]
  refine hbasis.tendsto_right_iff.mpr fun K _ ↦ ?_
  obtain ⟨J, hJ, hJK⟩ := h K
  exact Filter.mem_of_superset (hJ.mem_nhds J.zero_mem) fun a ha ↦ hJK ha

end InverseLimit

section Stages

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]
  {C : Type u} [CommRing C] [TopologicalSpace C]

attribute [local instance] sheaf_hasColimits

/-- Any two weak ideals of definition are both below a common one for reverse inclusion. -/
private theorem exists_ge_weakIdeals (J L : WeakIdeals A) : ∃ M : WeakIdeals A, J ≤ M ∧ L ≤ M :=
  isDirected_weakIdeals.directed J L

/-- The transition morphism of the canonical diagram of a formal spectrum attached to an
inclusion of weak ideals of definition is a monomorphism of sheaves. -/
private theorem mono_formalSpectrumDiagram_map (D : QuotientSystem B S hS A)
    {J K : WeakIdeals A} (f : J ⟶ K) : Mono ((formalSpectrumDiagram D).map f) := by
  have hclosed : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f))))
    exact IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (show K.1 ≤ J.1 from leOfHom f))
  have hm : Mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) := by
    let _ := hclosed
    infer_instance
  have hinj : ∀ X : (BigFppfOver B S hS)ᵒᵖ, Function.Injective
      ((uliftYoneda.{u + 1, u}.map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))).app X) := by
    intro X y z hyz
    apply ULift.ext
    apply (BigFppfOver.toScheme B S hS).map_injective
    apply (cancel_mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f)))).1
    simpa using congrArg (fun w ↦ (BigFppfOver.toScheme B S hS).map (ULift.down w)) hyz
  have hloc : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (uliftYoneda.{u + 1, u}.map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) :=
    Presheaf.isLocallyInjective_of_injective _ _ hinj
  have hloc' : Sheaf.IsLocallyInjective ((formalSpectrumDiagram D).map f) := by
    change Sheaf.IsLocallyInjective
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
        (uliftYoneda.{u + 1, u}.map
          ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))))
    exact (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hloc
  exact Sheaf.mono_of_isLocallyInjective _

/-- Every stage of the formal spectrum of a weakly admissible ring includes into it as a
monomorphism. -/
private theorem mono_formalSpectrumInclusion [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (J : WeakIdeals A) : Mono (formalSpectrumInclusion D J) := by
  let _ : Nonempty (WeakIdeals A) := nonempty_weakIdeals hA
  let _ : IsDirected (WeakIdeals A) (· ≤ ·) := isDirected_weakIdeals
  exact Sheaf.mono_colimit_ι_of_mono_transition (formalSpectrumDiagram D)
    (fun _ _ f ↦ mono_formalSpectrumDiagram_map D f) J

/-- `Spec` reverses composition of ring maps. -/
private theorem specMap_comp_ofHom {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] (a : R₂ →+* R₃) (b : R₁ →+* R₂) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- Two ring maps with the same spectrum map are equal. -/
private theorem ringHom_eq_of_specMap_eq {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    {a b : R₁ →+* R₂}
    (h : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b)) : a = b :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- Two morphisms of the site into stages of a formal spectrum which agree in the formal spectrum
already agree in any stage containing both. -/
private theorem stage_hom_eq_of_colimit_eq [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {U : BigFppfOver B S hS} {J J' M : WeakIdeals A} (u : J ⟶ M) (u' : J' ⟶ M)
    {g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J)}
    {k : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J')}
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        formalSpectrumInclusion D J =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        formalSpectrumInclusion D J') :
    g ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map u) =
      k ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map u') := by
  let _ : Mono (formalSpectrumInclusion D M) := formalSpectrumInclusion_mono B S hS hA.1 D M
  apply (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
  apply (cancel_mono (formalSpectrumInclusion D M)).1
  simp only [Functor.map_comp, Category.assoc]
  change (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
      (formalSpectrumDiagram D).map u ≫ colimit.ι (formalSpectrumDiagram D) M =
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
      (formalSpectrumDiagram D).map u' ≫ colimit.ι (formalSpectrumDiagram D) M
  rw [colimit.w, colimit.w]
  exact h

/-- Two morphisms from one object of the site into stages of a formal spectrum which agree in
the formal spectrum already agree after passing to the spectra of the quotients. -/
private theorem stage_comp_quotient_mk_eq [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {U : BigFppfOver B S hS} {J L : WeakIdeals A}
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J))
    (k : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage L))
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        formalSpectrumInclusion D J =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        formalSpectrumInclusion D L) :
    (BigFppfOver.toScheme B S hS).map g ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
      (BigFppfOver.toScheme B S hS).map k ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L.1)) := by
  obtain ⟨M, hJM, hLM⟩ := exists_ge_weakIdeals J L
  have hmk : ∀ (N : WeakIdeals A) (hn : N ≤ M),
      (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map
        (D.diagram.map (homOfLE hn))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk M.1)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk N.1)) := fun N hn ↦ by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show M.1 ≤ N.1 from hn))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk M.1)) = _
    rw [specMap_comp_ofHom, Ideal.Quotient.factor_comp_mk]
  have ht := congrArg (fun q ↦ (BigFppfOver.toScheme B S hS).map q ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk M.1)))
    (stage_hom_eq_of_colimit_eq hA (homOfLE hJM) (homOfLE hLM) h)
  simp only [Functor.map_comp] at ht
  erw [Category.assoc, Category.assoc, hmk, hmk] at ht
  exact ht

/-! ### Factoring a quotient stage of the source through a quotient stage of the target -/

/-- Every quotient stage of the source of a morphism of formal spectra maps into a quotient
stage of the target. This is Stacks 0AIA applied to the canonical presentation of the target by
the spectra of its quotients by weak ideals of definition. -/
private theorem exists_stage_factorization [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (K : WeakIdeals C)
    (f : formalSpectrum E ⟶ formalSpectrum D) :
    ∃ (J : WeakIdeals A) (m : (formalSpectrumDiagram E).obj K ⟶
      (formalSpectrumDiagram D).obj J),
      m ≫ formalSpectrumInclusion D J = formalSpectrumInclusion E K ≫ f := by
  classical
  obtain ⟨I, hpre, hne, hdir, D', hThick, ⟨e⟩⟩ :=
    exists_thickeningColimit_formalSpectrum hA D
  let _ : Preorder I := hpre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  obtain ⟨Js, es, -, hoverX, -⟩ := presentation_quotients_cofinal B S hS A hA
    (formalSpectrum D) D.weakIdealColimitPresentation I D' hThick e
  have hY : IsAlgebraicSpace B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (E.stage K))) :=
    isAlgebraicSpace_yoneda B S hS _
  have hYqc : Space.IsQuasiCompactSpace B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (E.stage K))) := by
    refine ⟨(BigAffineFppf.inclusion B S hS).obj (E.stage K), 𝟙 _, ?_, ?_, ?_⟩
    · change CompactSpace (Spec (.of (C ⧸ K.1)))
      infer_instance
    · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro X Y q p₁ p₂ hp
      have : IsIso (yoneda.map p₂) := hp.isIso_snd_of_isIso
      have : IsIso p₂ := Yoneda.fullyFaithful.isIso_of_isIso_map p₂
      have : IsIso ((BigFppfOver.toScheme B S hS).map p₂) := Functor.map_isIso _ p₂
      change Surjective ((BigFppfOver.toScheme B S hS).map p₂)
      exact ⟨(((BigFppfOver.toScheme B S hS).map p₂).homeomorph).surjective⟩
    · intro V ψ hψ
      simpa using hψ
  have hUobj : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.stage K)) =
      (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (E.stage K)) ⋙
          uliftFunctor.{u + 1, u}) := by
    rw [Sheaf.sheafifiedYoneda_obj]
    rfl
  obtain ⟨i, g, hg⟩ := exists_factor_through_thickening' B S hS I D' (fun _ _ g ↦ (hThick g).1)
    (formalSpectrum D) e
    (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (E.stage K))) hYqc
    ((eqToIso hUobj).inv ≫ formalSpectrumInclusion E K ≫ f)
  have hstage : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (es i).hom) ≫
      formalSpectrumInclusion D (Js i) =
    colimit.ι (D' ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv :=
    (congrArg (fun z ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (es i).hom) ≫ z)
      (Category.comp_id (formalSpectrumInclusion D (Js i))).symm).trans (hoverX i)
  refine ⟨Js i, (eqToIso hUobj).hom ≫ g ≫
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (es i).hom), ?_⟩
  have s1 : ((eqToIso hUobj).hom ≫ g ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (es i).hom)) ≫
        formalSpectrumInclusion D (Js i) =
      (eqToIso hUobj).hom ≫ g ≫
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (es i).hom) ≫
            formalSpectrumInclusion D (Js i)) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z ↦ (eqToIso hUobj).hom ≫ z) (Category.assoc _ _ _))
  have s2 : (eqToIso hUobj).hom ≫ g ≫
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (es i).hom) ≫
            formalSpectrumInclusion D (Js i)) =
      (eqToIso hUobj).hom ≫ g ≫ (colimit.ι (D' ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv) :=
    congrArg (fun z ↦ (eqToIso hUobj).hom ≫ g ≫ z) hstage
  have s3 : (eqToIso hUobj).hom ≫ g ≫ (colimit.ι (D' ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv) =
      (eqToIso hUobj).hom ≫ ((eqToIso hUobj).inv ≫ formalSpectrumInclusion E K ≫ f) :=
    congrArg (fun z ↦ (eqToIso hUobj).hom ≫ z) hg
  have s4 : (eqToIso hUobj).hom ≫ ((eqToIso hUobj).inv ≫
        formalSpectrumInclusion E K ≫ f) = formalSpectrumInclusion E K ≫ f :=
    (eqToIso hUobj).hom_inv_id_assoc _
  exact s1.trans (s2.trans (s3.trans s4))
/-! ### The stagewise ring maps -/

/-- The ring map between quotients underlying a morphism from a stage of one formal spectrum to
a stage of another. -/
private def stageRingHom {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (K : WeakIdeals C) (J : WeakIdeals A)
    [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full]
    (g : (formalSpectrumDiagram E).obj K ⟶ (formalSpectrumDiagram D).obj J) :
    A ⧸ J.1 →+* C ⧸ K.1 :=
  (Spec.preimage ((BigFppfOver.toScheme B S hS).map
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage g))).hom

/-- The stagewise ring map induces the morphism of affine quotient schemes it came from. -/
private theorem specMap_stageRingHom {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (K : WeakIdeals C) (J : WeakIdeals A)
    [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full]
    (g : (formalSpectrumDiagram E).obj K ⟶ (formalSpectrumDiagram D).obj J) :
    Spec.map (CommRingCat.ofHom (stageRingHom K J g)) =
      (BigFppfOver.toScheme B S hS).map
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage g) := by
  have h1 : CommRingCat.ofHom (stageRingHom K J g) =
      Spec.preimage ((BigFppfOver.toScheme B S hS).map
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage g)) :=
    CommRingCat.ofHom_hom _
  rw [h1]
  exact Spec.map_preimage _

/-- The stagewise ring map is a map over the base. -/
private theorem stageRingHom_overS {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (K : WeakIdeals C) (J : WeakIdeals A)
    [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full]
    (g : (formalSpectrumDiagram E).obj K ⟶ (formalSpectrumDiagram D).obj J) :
    Spec.map (CommRingCat.ofHom (stageRingHom K J g)) ≫ D.overS J = E.overS K := by
  rw [specMap_stageRingHom]
  exact congrArg (fun q ↦ q.hom)
    (Over.w ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage g))

/-- A ring map whose reductions modulo the weak ideals of definition of the target are maps over
the base is itself a map over the base at every stage. -/
private theorem quotientMap_overS {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (φ : A →+* C)
    (hφ : ∀ K : WeakIdeals C, ∃ (L : WeakIdeals A) (ψ : A ⧸ L.1 →+* C ⧸ K.1),
      (Ideal.Quotient.mk K.1).comp φ = ψ.comp (Ideal.Quotient.mk L.1) ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ D.overS L = E.overS K)
    (J : WeakIdeals A) (K : WeakIdeals C) (h : J.1 ≤ Ideal.comap φ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ h)) ≫ D.overS J = E.overS K := by
  obtain ⟨L, ψ, hψ, hSψ⟩ := hφ K
  obtain ⟨M, hJM, hLM⟩ := exists_ge_weakIdeals J L
  have he : (Ideal.quotientMap K.1 φ h).comp (Ideal.Quotient.factor hJM) =
      ψ.comp (Ideal.Quotient.factor hLM) := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    exact congrArg (fun q : A →+* C ⧸ K.1 ↦ q a) hψ
  rw [← D.compatible M J hJM, ← Category.assoc, specMap_comp_ofHom, he, ← specMap_comp_ofHom,
    Category.assoc, D.compatible M L hLM, hSψ]

/-- An ideal maps into an ideal as soon as the corresponding map of quotients factors. -/
private theorem le_comap_of_quotient_factor {R T : Type*} [CommRing R] [CommRing T]
    {I : Ideal R} {J : Ideal T} (φ : R →+* T) (ψ : R ⧸ I →+* T ⧸ J)
    (h : (Ideal.Quotient.mk J).comp φ = ψ.comp (Ideal.Quotient.mk I)) :
    I ≤ Ideal.comap φ J := by
  intro a ha
  have hzero : ((Ideal.Quotient.mk J).comp φ) a = 0 := by
    rw [h, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hmem : φ a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  exact hmem

/-- A continuous ring map pulls every weak ideal of definition of its target back to an ideal
containing a weak ideal of definition of its source. -/
private theorem exists_weakIdeal_le_comap [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (φ : A →+* C) (hφ : Continuous φ)
    (K : WeakIdeals C) : ∃ J : WeakIdeals A, J.1 ≤ Ideal.comap φ K.1 := by
  obtain ⟨J, hJ, hJK⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).mem_iff.mp
      (hφ.continuousAt.preimage_mem_nhds (K.2.1.mem_nhds (by simp)))
  exact ⟨OrderDual.toDual ⟨J, hJ⟩, hJK⟩

/-- A continuous ring map pulls every weak ideal of definition of its target back to an ideal
containing a weak ideal of definition of its source. -/
alias exists_weakIdeal_le_comap' := exists_weakIdeal_le_comap

/-- Two continuous ring maps over the base with the same underlying ring map are equal. -/
private theorem continuousHom_ext {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    {g g' : ContinuousHom D E} (h : g.toRingHom = g'.toRingHom) : g = g' := by
  cases g
  cases g'
  cases h
  rfl

/-- Two continuous ring maps over the base with the same underlying ring map are equal. -/
alias continuousHom_ext' := continuousHom_ext

end Stages

section Main

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AN0.** Let `A` and `C` be weakly admissible topological rings over `S`. Every
morphism `f : Spf C ⟶ Spf A` of affine formal algebraic spaces over `S` is `Spf (f^♯)` for a
unique continuous ring map `f^♯ : A → C` over `S`. -/
@[stacks 0AN0, ega "I 10.4.6" "X affine formal"]
theorem existsUnique_continuousHom_formalSpectrumMap_eq
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : formalSpectrum E ⟶ formalSpectrum D) :
    ∃! g : ContinuousHom D E, formalSpectrumMap hA g = f := by
  classical
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  choose qi qm qcomm using fun K : WeakIdeals C ↦ exists_stage_factorization hA K f
  -- the stagewise ring maps are compatible, so they come from a single ring map
  have hcompat : ∀ (K L : WeakIdeals C) (h : K.1 ≤ L.1),
      (Ideal.Quotient.factor h).comp
          ((stageRingHom K (qi K) (qm K)).comp (Ideal.Quotient.mk (qi K).1)) =
        (stageRingHom L (qi L) (qm L)).comp (Ideal.Quotient.mk (qi L).1) := by
    intro K L h
    obtain ⟨M, hKM, hLM⟩ := exists_ge_weakIdeals (qi K) (qi L)
    -- the two factorisations agree after restricting to `Spec (C/L)`
    have hcolim : ((formalSpectrumDiagram E).map (homOfLE (show L ≤ K from h)) ≫ qm K) ≫
          formalSpectrumInclusion D (qi K) = qm L ≫ formalSpectrumInclusion D (qi L) := by
      erw [Category.assoc, qcomm K, ← Category.assoc, colimit.w, qcomm L]
      rfl
    have hpre := stage_hom_eq_of_colimit_eq hA (homOfLE hKM) (homOfLE hLM)
      (g := (BigAffineFppf.inclusion B S hS).map
          (E.diagram.map (homOfLE (show L ≤ K from h))) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage (qm K))
      (k := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage (qm L))
      (by simp only [Functor.map_comp, Functor.map_preimage]; exact hcolim)
    have hscheme := congrArg (BigFppfOver.toScheme B S hS).map hpre
    simp only [Functor.map_comp] at hscheme
    -- descend the common equality to the quotient rings
    have hring : ((Ideal.Quotient.factor h).comp (stageRingHom K (qi K) (qm K))).comp
          (Ideal.Quotient.factor hKM) =
        (stageRingHom L (qi L) (qm L)).comp (Ideal.Quotient.factor hLM) := by
      refine ringHom_eq_of_specMap_eq ?_
      simp only [← specMap_comp_ofHom, specMap_stageRingHom]
      exact hscheme
    have hmk := congrArg
      (fun ρ : A ⧸ M.1 →+* C ⧸ L.1 ↦ ρ.comp (Ideal.Quotient.mk M.1)) hring
    simp only [RingHom.comp_assoc, Ideal.Quotient.factor_comp_mk] at hmk
    exact hmk
  obtain ⟨φ, hφ, hφuniq⟩ := existsUnique_ringHom_comp_weakQuotient_mk hC
    (fun K ↦ (stageRingHom K (qi K) (qm K)).comp (Ideal.Quotient.mk (qi K).1)) hcompat
  have hK : ∀ K : WeakIdeals C, (qi K).1 ≤ Ideal.comap φ K.1 := fun K ↦
    le_comap_of_quotient_factor φ (stageRingHom K (qi K) (qm K)) (hφ K)
  have hcont : Continuous φ :=
    continuous_of_isOpen_le_comap hC φ fun K ↦ ⟨(qi K).1, (qi K).2.1, hK K⟩
  have hoverS : ∀ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
      (hJK : J.1 ≤ Ideal.comap φ K.1),
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ hJK)) ≫ D.overS J = E.overS K :=
    quotientMap_overS φ fun K ↦ ⟨qi K, stageRingHom K (qi K) (qm K), hφ K,
      stageRingHom_overS K (qi K) (qm K)⟩
  let g : ContinuousHom D E := { toRingHom := φ, continuous := hcont, overS := hoverS }
  refine ⟨g, ?_, ?_⟩
  · -- `Spf φ = f`, checked on every quotient stage of the source
    refine colimit.hom_ext fun K ↦ ?_
    have hq : Ideal.quotientMap K.1 φ (hK K) = stageRingHom K (qi K) (qm K) :=
      Ideal.Quotient.ringHom_ext ((Ideal.quotientMap_comp_mk (hK K)).trans (hφ K))
    have hsite : (BigAffineFppf.inclusion B S hS).map (g.stageMap (qi K) K (hK K)) =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage (qm K) := by
      apply (BigFppfOver.toScheme B S hS).map_injective
      change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ (hK K))) = _
      rw [hq]
      exact specMap_stageRingHom K (qi K) (qm K)
    have hstage : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (g.stageMap (qi K) K (hK K))) = qm K := by
      rw [hsite]
      exact Functor.map_preimage _ _
    exact (formalSpectrumMap_spec hA g (qi K) K (hK K)).trans
      ((congrArg (fun z ↦ z ≫ formalSpectrumInclusion D (qi K)) hstage).trans (qcomm K))
  · -- uniqueness
    intro g' hg'
    refine continuousHom_ext (hφuniq g'.toRingHom fun K ↦ ?_)
    obtain ⟨J, hJ⟩ := exists_weakIdeal_le_comap hA g'.toRingHom g'.continuous K
    have hh : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (g'.stageMap J K hJ)) ≫
            formalSpectrumInclusion D J =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage (qm K)) ≫
            formalSpectrumInclusion D (qi K) :=
      (formalSpectrumMap_spec hA g' J K hJ).symm.trans
        ((congrArg (fun z ↦ formalSpectrumInclusion E K ≫ z) hg').trans
          ((qcomm K).symm.trans
            (congrArg (fun z ↦ z ≫ formalSpectrumInclusion D (qi K))
              (Functor.map_preimage
                (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (qm K)).symm)))
    have hs := stage_comp_quotient_mk_eq hA
      ((BigAffineFppf.inclusion B S hS).map (g'.stageMap J K hJ))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage (qm K)) hh
    refine ringHom_eq_of_specMap_eq ?_
    rw [← Ideal.quotientMap_comp_mk hJ]
    simp only [← specMap_comp_ofHom, specMap_stageRingHom]
    exact hs

end Main

section Representability

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of presheaves on the big fppf site of `S` with values in `Type (max w₁ u)` which
is representable by objects of the site is representable by algebraic spaces over `S`: its base
change along a scheme-valued point of the target is a universe-lifted Yoneda presheaf, and
those are algebraic spaces. -/
theorem
    _root_.AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w₁ u)} (a : F ⟶ G)
    (ha : (uliftYoneda.{w₁} (C := BigFppfOver B S hS)).relativelyRepresentable a) :
    Space.IsRepresentableByAlgebraicSpacesULift.{w₁} B S hS a := by
  intro U ξ
  obtain ⟨V, q, p, hp⟩ := ha ξ
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hp.flip.isoPullback
    (Space.isAlgebraicSpaceULift_uliftYoneda.{w₁} B S hS V)

/-- **Stacks 0AN5**, the implication from its condition (2) to its condition (1): if the formal
spectrum of a continuous homomorphism of weakly admissible topological rings over `S` is
representable by objects of the site, then it is representable by algebraic spaces over `S`. -/
theorem isRepresentableByAlgebraicSpacesULift_formalSpectrumMap
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (φ : ContinuousHom D E)
    (hφ : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (formalSpectrumMap hA φ).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA φ).hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable _ hφ

end Representability

end AlgebraicGeometry.FormalSpace

end
