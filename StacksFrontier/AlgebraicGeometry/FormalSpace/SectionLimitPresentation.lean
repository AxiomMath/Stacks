module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Recognising a sequential presentation as a formal spectrum (Stacks 0AIC)

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an fppf sheaf over `S`
written as the colimit of a sequence `X₀ → X₁ → X₂ → ⋯` of affine schemes over `S` along
thickenings. Suppose a linearly topologized ring `A` surjects compatibly onto the rings of
sections `Γ(Xₙ, 𝒪)` with kernels which are weak ideals of definition forming a fundamental
system of neighbourhoods of `0`. Then `X` is the formal spectrum of `A`.

This is the implication (4) ⇒ (1) of **Stacks 0AIC** for a sequential presentation: the
sequence of kernels is cofinal among all weak ideals of definition of `A`, so the colimit over
the weak ideals of definition collapses to the colimit of the sequence.

## Main definitions

* `AlgebraicGeometry.FormalSpace.SequentialQuotients`: a sequential presentation of `X` by
  affine thickenings together with compatible surjections of `A` onto the section rings.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso`: such data produce
  a `AlgebraicGeometry.FormalSpace.QuotientSystem` for `A` and an isomorphism of `X` with the
  resulting formal spectrum.

## Implementation notes

A topological ring over a possibly non-affine `S` need not admit a morphism `Spec A ⟶ S`, so
the structure morphisms of its quotient spectra are the datum, as in
`AlgebraicGeometry.FormalSpace.QuotientSystem`. For a weak ideal of definition `K` that
morphism is built from any stage whose kernel is contained in `K`; the construction does not
depend on the stage, because two stages are dominated by a third.

Openness of a weak ideal of definition is what makes the sequence of kernels cofinal, and
`CategoryTheory.Functor.Final` turns cofinality into a comparison of colimits.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of an fppf sheaf `X` over `S` by a sequence of affine thickenings whose
rings of sections are the quotients of a linearly topologized ring `A` by a fundamental system
of weak ideals of definition. This is condition (4) of **Stacks 0AIC** for a sequence, with the
ring of the presentation named. -/
structure SequentialQuotients (X : FppfSheaf B S hS) (A : Type u) [CommRing A]
    [TopologicalSpace A] where
  /-- The sequence of affine schemes over `S`. -/
  diagram : ℕ ⥤ BigAffineFppf B S hS
  /-- Its transition morphisms are thickenings. -/
  isThickening : ∀ ⦃m n : ℕ⦄ (f : m ⟶ n),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (diagram.map f))
  /-- Its colimit is `X`. -/
  colimitIso : X ≅ colimit (diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
  /-- The surjection of `A` onto the sections of the `n`-th stage. -/
  proj : ∀ n : ℕ, A →+* Γ((BigAffineFppf.toScheme B S hS).obj (diagram.obj n), ⊤)
  /-- Each such map is surjective. -/
  proj_surjective : ∀ n, Function.Surjective (proj n)
  /-- The maps are compatible with the transition morphisms. -/
  proj_comp : ∀ n : ℕ, (((BigAffineFppf.toScheme B S hS).map
      (diagram.map (homOfLE (Nat.le_succ n)))).appTop).hom.comp (proj (n + 1)) = proj n
  /-- Their kernels are weak ideals of definition. -/
  isWeakIdealOfDefinition_ker : ∀ n,
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (proj n))
  /-- Their kernels are a fundamental system of neighbourhoods of `0`. -/
  hasBasis_nhds_zero : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
    (fun n ↦ (RingHom.ker (proj n) : Set A))

namespace SequentialQuotients

variable {B S hS} {X : FppfSheaf B S hS} {A : Type u} [CommRing A] [TopologicalSpace A]
  (P : SequentialQuotients B S hS X A)

/-- The affine scheme underlying the `n`-th stage. -/
abbrev stage (n : ℕ) : Scheme.{u} :=
  (BigAffineFppf.toScheme B S hS).obj (P.diagram.obj n)

/-- The transition morphism of stages attached to `m ≤ n`. -/
abbrev stageMap {m n : ℕ} (h : m ≤ n) : P.stage m ⟶ P.stage n :=
  (BigAffineFppf.toScheme B S hS).map (P.diagram.map (homOfLE h))

/-- The structure morphism of the `n`-th stage to the base. -/
abbrev stageOver (n : ℕ) : P.stage n ⟶ S :=
  B.inclusion.map (Over.hom (P.diagram.obj n).1)

/-- The ideal cut out by the `n`-th stage. -/
abbrev ideal (n : ℕ) : Ideal A := RingHom.ker (P.proj n)

/-- The transition morphisms of stages commute with the structure morphisms to `S`. -/
theorem stageMap_comp_stageOver {m n : ℕ} (h : m ≤ n) :
    P.stageMap h ≫ P.stageOver n = P.stageOver m := by
  change B.inclusion.map (Over.Hom.left ((P.diagram.map (homOfLE h)).1)) ≫
      B.inclusion.map (Over.hom (P.diagram.obj n).1) = _
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w ((P.diagram.map (homOfLE h)).1))

/-- The transition morphism for `m ≤ k` is the composite of those for `m ≤ n` and `n ≤ k`. -/
theorem stageMap_trans {m n k : ℕ} (h : m ≤ n) (h' : n ≤ k) :
    P.stageMap h ≫ P.stageMap h' = P.stageMap (h.trans h') := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The transition morphism for `n ≤ n` is the identity. -/
theorem stageMap_refl (n : ℕ) : P.stageMap (le_refl n) = 𝟙 _ := by
  have h : P.diagram.map (homOfLE (le_refl n)) = 𝟙 _ := by
    rw [show homOfLE (le_refl n) = 𝟙 n from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
  change (BigAffineFppf.toScheme B S hS).map (P.diagram.map (homOfLE (le_refl n))) = _
  rw [h, CategoryTheory.Functor.map_id]

/-- The surjections onto the stages are compatible with every transition morphism. -/
theorem proj_comp_le {m n : ℕ} (h : m ≤ n) :
    ((P.stageMap h).appTop).hom.comp (P.proj n) = P.proj m := by
  induction n, h using Nat.le_induction with
  | base => rw [P.stageMap_refl]; ext a; simp
  | succ n h ih =>
    rw [← P.stageMap_trans h (Nat.le_succ n), Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_assoc]
    change ((P.stageMap h).appTop).hom.comp
      ((((BigAffineFppf.toScheme B S hS).map
        (P.diagram.map (homOfLE (Nat.le_succ n)))).appTop).hom.comp (P.proj (n + 1))) = _
    rwa [P.proj_comp n]

/-- The ideals of the stages decrease along the sequence. -/
theorem ideal_antitone : Antitone P.ideal := by
  intro m n hmn a ha
  refine RingHom.mem_ker.mpr ?_
  have h := RingHom.congr_fun (P.proj_comp_le hmn) a
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [← h, RingHom.mem_ker.mp ha, map_zero]

/-- Every weak ideal of definition of `A` contains the ideal of some stage: it is open, hence a
neighbourhood of `0`, and the stage ideals are a fundamental system of such. -/
theorem exists_ideal_le (K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ n : ℕ, P.ideal n ≤ K.1 := by
  obtain ⟨n, -, hsub⟩ :=
    P.hasBasis_nhds_zero.mem_iff.mp (K.2.1.mem_nhds (Ideal.zero_mem K.1))
  exact ⟨n, hsub⟩

/-- The sections of the `n`-th stage are the quotient of `A` by the ideal of that stage. -/
def quotEquiv (n : ℕ) : (A ⧸ P.ideal n) ≃+* Γ(P.stage n, ⊤) :=
  RingHom.quotientKerEquivOfSurjective (P.proj_surjective n)

/-- `quotEquiv` sends the class of `a` to the image of `a` under the `n`-th surjection. -/
theorem quotEquiv_mk (n : ℕ) (a : A) :
    P.quotEquiv n (Ideal.Quotient.mk (P.ideal n) a) = P.proj n a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (P.proj_surjective n) a

/-- The identification of the quotient of `A` by the ideal of the `n`-th stage with the ring of
sections of that stage, as an isomorphism of commutative rings. -/
def stageRingIso (n : ℕ) : CommRingCat.of (A ⧸ P.ideal n) ≅ Γ(P.stage n, ⊤) where
  hom := CommRingCat.ofHom (P.quotEquiv n).toRingHom
  inv := CommRingCat.ofHom (P.quotEquiv n).symm.toRingHom
  hom_inv_id := by ext a; simp
  inv_hom_id := by ext a; simp

/-- The `n`-th stage is the spectrum of the quotient of `A` by its ideal. -/
def stageIso (n : ℕ) : P.stage n ≅ Spec (.of (A ⧸ P.ideal n)) :=
  (P.stage n).isoSpec ≪≫ Scheme.Spec.mapIso (P.stageRingIso n).op

/-- The forward morphism of `stageIso` is `Scheme.isoSpec` followed by the spectrum of
`stageRingIso`. -/
theorem stageIso_hom (n : ℕ) :
    (P.stageIso n).hom = (P.stage n).isoSpec.hom ≫ Spec.map (P.stageRingIso n).hom := rfl

/-- The identifications of the stages with the quotient spectra are natural in the stage. -/
theorem stageIso_naturality {m n : ℕ} (h : m ≤ n) :
    P.stageMap h ≫ (P.stageIso n).hom = (P.stageIso m).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) := by
  have hring : (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) ≫
      (P.stageRingIso m).hom = (P.stageRingIso n).hom ≫ (P.stageMap h).appTop := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext b
    simpa [stageRingIso, Ideal.Quotient.factor_mk, P.quotEquiv_mk] using
      (RingHom.congr_fun (P.proj_comp_le h) b).symm
  rw [stageIso_hom, stageIso_hom, Category.assoc, ← Spec.map_comp, hring, Spec.map_comp,
    ← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc]

/-! ### The quotient system attached to the presentation -/

/-- The underlying scheme of a stage is an object of the site. -/
theorem stage_contains (n : ℕ) : B.Contains (P.stage n) := (P.diagram.obj n).1.left.2

/-- The structure morphism of the quotient spectrum of a stage, transported from the stage. -/
def stageSpecOver (n : ℕ) : Spec (.of (A ⧸ P.ideal n)) ⟶ S :=
  (P.stageIso n).inv ≫ P.stageOver n

/-- The structure morphisms of the quotient spectra of the stages are compatible with the
morphisms induced by the inclusions of stage ideals. -/
theorem stageSpecOver_compat {m n : ℕ} (h : m ≤ n) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) ≫
      P.stageSpecOver n = P.stageSpecOver m := by
  have hfac : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone h))) =
      (P.stageIso m).inv ≫ P.stageMap h ≫ (P.stageIso n).hom := by
    rw [P.stageIso_naturality h, Iso.inv_hom_id_assoc]
  rw [hfac, stageSpecOver, stageSpecOver, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, P.stageMap_comp_stageOver h]

/-- The composite of two quotient maps of stage ideals is the quotient map of the smaller. -/
theorem ofHom_factor_trans {K : Ideal A} {i j : ℕ} (hij : i ≤ j) (hi : P.ideal i ≤ K) :
    CommRingCat.ofHom (Ideal.Quotient.factor ((P.ideal_antitone hij).trans hi)) =
      CommRingCat.ofHom (Ideal.Quotient.factor (P.ideal_antitone hij)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor hi) :=
  CommRingCat.hom_ext (by simp)

/-- The structure morphism attached to a weak ideal of definition, built from a stage whose
ideal it contains. -/
def weakOver (K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Spec (.of (A ⧸ K.1)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (P.exists_ideal_le K).choose_spec)) ≫
    P.stageSpecOver (P.exists_ideal_le K).choose

/-- Passing to a later stage does not change the morphism a stage induces on the spectrum of a
quotient by a weak ideal of definition containing its ideal. -/
theorem specOver_stage_le {K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    {i j : ℕ} (hij : i ≤ j) (hi : P.ideal i ≤ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hi)) ≫ P.stageSpecOver i =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor ((P.ideal_antitone hij).trans hi))) ≫ P.stageSpecOver j := by
  rw [P.ofHom_factor_trans hij hi, Spec.map_comp, Category.assoc, P.stageSpecOver_compat hij]

/-- The structure morphism attached to a weak ideal of definition may be computed from any
stage whose ideal it contains. -/
theorem weakOver_eq (K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    {n : ℕ} (h : P.ideal n ≤ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ P.stageSpecOver n =
      P.weakOver K :=
  (P.specOver_stage_le (le_max_left n (P.exists_ideal_le K).choose) h).trans
    (P.specOver_stage_le (le_max_right n (P.exists_ideal_le K).choose)
      (P.exists_ideal_le K).choose_spec).symm

/-- The quotient system of the presenting ring: the structure morphism of the spectrum of a
quotient by a weak ideal of definition is inherited from a stage below it. -/
def quotientSystem : QuotientSystem B S hS A where
  inSite K := by
    obtain ⟨n, hn⟩ := P.exists_ideal_le K
    have hci : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hn))) :=
      IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hn)
    refine Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hn))) ?_
    rw [← Scheme.size_congr (P.stageIso n)]
    exact P.stage_contains n
  overS K := P.weakOver K
  compatible J L h := by
    obtain ⟨n, hn⟩ := P.exists_ideal_le J
    have hfac : CommRingCat.ofHom (Ideal.Quotient.factor (hn.trans h)) =
        CommRingCat.ofHom (Ideal.Quotient.factor hn) ≫
          CommRingCat.ofHom (Ideal.Quotient.factor h) := by
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext b
      simp
    rw [← P.weakOver_eq J hn, ← P.weakOver_eq L (hn.trans h), hfac, Spec.map_comp,
      Category.assoc]

/-- The structure morphism attached to the ideal of a stage is the one transported from that
stage. -/
theorem weakOver_stage (n : ℕ) :
    P.weakOver ⟨P.ideal n, P.isWeakIdealOfDefinition_ker n⟩ = P.stageSpecOver n := by
  rw [← P.weakOver_eq ⟨P.ideal n, P.isWeakIdealOfDefinition_ker n⟩ (le_refl (P.ideal n))]
  have hid : CommRingCat.ofHom (Ideal.Quotient.factor (le_refl (P.ideal n))) = 𝟙 _ :=
    CommRingCat.hom_ext Ideal.Quotient.factor_eq
  rw [hid, Spec.map_id, Category.id_comp]

/-! ### Comparison of the two colimits -/

/-- The weak ideals of definition cut out by the stages decrease along the sequence. -/
theorem chain_monotone :
    Monotone (fun n : ℕ ↦ (OrderDual.toDual
      (⟨P.ideal n, P.isWeakIdealOfDefinition_ker n⟩ :
        TopologicalRing.WeakIdealOfDefinitionIndex A))) :=
  fun _ _ h ↦ P.ideal_antitone h

/-- The sequence of stage ideals, as a functor into the weak ideals of definition. -/
abbrev chain : ℕ ⥤ WeakIdeals A := P.chain_monotone.functor

/-- The sequence of stage ideals is cofinal among the weak ideals of definition. -/
instance chain_final : P.chain.Final :=
  P.chain_monotone.final_functor_iff.mpr fun K ↦ P.exists_ideal_le (OrderDual.ofDual K)

/-- The underlying scheme of a stage is isomorphic to that of the corresponding stage of the
quotient system. -/
def chainStageBaseIso (n : ℕ) :
    (P.diagram.obj n).1.left ≅ (P.quotientSystem.diagram.obj (P.chain.obj n)).1.left :=
  B.inclusion.preimageIso (show B.inclusion.obj ((P.diagram.obj n).1.left) ≅
    B.inclusion.obj ((P.quotientSystem.diagram.obj (P.chain.obj n)).1.left) from P.stageIso n)

/-- The image of `chainStageBaseIso` in schemes is `stageIso`. -/
theorem chainStageBaseIso_map (n : ℕ) :
    B.inclusion.map (P.chainStageBaseIso n).hom = (P.stageIso n).hom :=
  B.inclusion.map_preimage _

/-- `chainStageBaseIso` commutes with the structure morphisms to the base. -/
theorem chainStageBaseIso_w (n : ℕ) :
    (P.chainStageBaseIso n).hom ≫
        Over.hom ((P.quotientSystem.diagram.obj (P.chain.obj n)).1) =
      Over.hom ((P.diagram.obj n).1) := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, P.chainStageBaseIso_map]
  change (P.stageIso n).hom ≫
    P.weakOver ⟨P.ideal n, P.isWeakIdealOfDefinition_ker n⟩ = P.stageOver n
  rw [P.weakOver_stage n, stageSpecOver, Iso.hom_inv_id_assoc]

/-- Each stage of the presentation is the stage of the quotient system at the weak ideal of
definition it cuts out. -/
def chainStageIso (n : ℕ) :
    P.diagram.obj n ≅ P.quotientSystem.diagram.obj (P.chain.obj n) := by
  apply ObjectProperty.isoMk
  exact Over.isoMk (P.chainStageBaseIso n) (P.chainStageBaseIso_w n)

/-- The underlying morphism of schemes of `chainStageIso` is `stageIso`. -/
theorem chainStageIso_toScheme (n : ℕ) :
    (BigAffineFppf.toScheme B S hS).map (P.chainStageIso n).hom = (P.stageIso n).hom := by
  simp only [chainStageIso, ObjectProperty.isoMk_hom]
  exact P.chainStageBaseIso_map n

/-- The presentation agrees with the restriction of the canonical diagram of the formal
spectrum along the sequence of stage ideals. -/
def chainDiagramIso : P.diagram ≅ P.chain ⋙ P.quotientSystem.diagram := by
  refine NatIso.ofComponents (fun n ↦ P.chainStageIso n) ?_
  intro m n f
  apply (BigAffineFppf.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, P.chainStageIso_toScheme, P.chainStageIso_toScheme]
  have hle : m ≤ n := leOfHom f
  have hmap : (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) = P.stageMap hle :=
    congrArg (fun g ↦ (BigAffineFppf.toScheme B S hS).map (P.diagram.map g))
      (Subsingleton.elim f (homOfLE hle))
  rw [hmap]
  exact P.stageIso_naturality hle

attribute [local instance] sheaf_hasColimits

include P in
/-- A sheaf presented as the colimit of a sequence of affine thickenings whose section rings are
the quotients of a linearly topologized ring `A` by a fundamental system of weak ideals of
definition is the formal spectrum of `A`. -/
@[stacks 0AIC "(4) implies (1), for a sequential presentation"]
theorem exists_quotientSystem_formalSpectrum_iso :
    ∃ Q : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum Q) := by
  refine ⟨P.quotientSystem, ⟨P.colimitIso ≪≫ ?_⟩⟩
  refine HasColimit.isoOfNatIso (Functor.isoWhiskerRight P.chainDiagramIso
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫ ?_
  refine HasColimit.isoOfNatIso (Functor.associator P.chain P.quotientSystem.diagram
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫ ?_
  exact Functor.Final.colimitIso P.chain (formalSpectrumDiagram P.quotientSystem)

end SequentialQuotients

end AlgebraicGeometry.FormalSpace

end
