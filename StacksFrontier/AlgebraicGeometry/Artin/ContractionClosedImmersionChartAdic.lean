module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartPoints

/-!
# The `I`-adic completion of an affine chart and its quotient stages

For a Noetherian ring `A` and an ideal `I`, the `I`-adic completion `A^∧` with its `I`-adic module
topology is an adic, weakly admissible, linearly topologized topological ring whose ideals
`I ^ (n + 1) A^∧` are weak ideals of definition, and a point of `Spec A` killing `I ^ (n + 1)`
factors through the quotient stage `Spec (A^∧ ⧸ I ^ (n + 1) A^∧)` of the quotient system
`AlgebraicGeometry.FormalSpace.adicQuotientSystem`.

## Main results

* `AlgebraicGeometry.FormalSpace.adicCompletion_isAdic_of_fg`: the `I`-adic completion is an adic,
  weakly admissible, linearly topologized topological ring.
* `AlgebraicGeometry.FormalSpace.exists_stage_factor`: a point of `Spec A` killing `I ^ (n + 1)`
  factors through the quotient stage `Spec (A^∧ ⧸ I ^ (n + 1) A^∧)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section AdicTopology

variable {A : Type u} [CommRing A]

/-- The `I`-adic module topology of an `A`-algebra `C` is the `IC`-adic topology of `C`. -/
private theorem adicModuleTopology_eq_adicTopology_map'
    {C : Type u} [CommRing C] [Algebra A C]
    (I : Ideal A) : I.adicModuleTopology C = (I.map (algebraMap A C)).adicTopology := by
  let : TopologicalSpace A := I.adicTopology
  apply IsTopologicalAddGroup.ext
  · infer_instance
  · infer_instance
  ext U
  rw [(I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis C)).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
  rw [(I.map (algebraMap A C)).hasBasis_nhds_zero_adic.mem_iff]
  constructor
  · rintro ⟨-, ⟨n, rfl⟩, hn⟩
    refine ⟨n, trivial, ?_⟩
    simpa only [id_eq, Ideal.smul_top_eq_map, Ideal.map_pow,
      Submodule.coe_restrictScalars] using hn
  · rintro ⟨n, -, hn⟩
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    simpa only [id_eq, Ideal.smul_top_eq_map, Ideal.map_pow,
      Submodule.coe_restrictScalars] using hn

/-- With its `I`-adic module topology the `I`-adic completion of `A` is an adic, weakly
admissible, linearly topologized topological ring, its topology being the `I A^∧`-adic one. -/
theorem adicCompletion_isAdic_of_fg (I : Ideal A) (hI : I.FG) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    ∃ (_ : IsTopologicalRing (AdicCompletion I A))
      (_ : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)),
      _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))) ∧
        TopologicalRing.IsAdic (AdicCompletion I A) ∧
          TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A) := by
  rw [adicModuleTopology_eq_adicTopology_map' I]
  let J := I.map (algebraMap A (AdicCompletion I A))
  let : TopologicalSpace (AdicCompletion I A) := J.adicTopology
  have hJ : _root_.IsAdic J := rfl
  let : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) := J.isLinearTopology
  let : UniformSpace (AdicCompletion I A) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (AdicCompletion I A) := isUniformAddGroup_of_addCommGroup
  have hc := hJ.isAdicComplete_iff.mp (AdicCompletion.isAdicComplete_self I hI)
  have hd := TopologicalRing.isIdealOfDefinition_of_isAdic hJ
  exact ⟨inferInstance, inferInstance, hJ, ⟨⟨J, hd, hJ⟩, hc.2, hc.1⟩,
    TopologicalRing.isWeaklyAdmissible_of_isAdic hJ (AdicCompletion.isAdicComplete_self I hI)⟩

/-- In a Noetherian ring an element whose image in `A^∧` lies in `I ^ n A^∧` lies in `I ^ n`. -/
theorem mem_pow_of_algebraMap_mem_map_pow [IsNoetherianRing A] (I : Ideal A) (n : ℕ) {a : A}
    (ha : algebraMap A (AdicCompletion I A) a ∈ (I ^ n).map (algebraMap A (AdicCompletion I A))) :
    a ∈ I ^ n := by
  have h :
      algebraMap A (AdicCompletion I A) a ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) := by
    rwa [Ideal.smul_top_eq_map]
  rwa [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
    AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top] at h

end AdicTopology

section Stage

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (hA : B.Contains (Spec (.of A)))
  (f : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG)

/-- The `I`-adic module topology on the `I`-adic completion `A^∧`. -/
noncomputable local instance instTopologicalSpaceAdicCompletionChart :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

/-- The weak ideal of definition `I ^ (n + 1) A^∧` of the `I`-adic completion. -/
noncomputable def adicCompletionPowStageIdeal (n : ℕ) :
    { J : Ideal (AdicCompletion I A) // TopologicalRing.IsWeakIdealOfDefinition J } :=
  ⟨(I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)), by
    obtain ⟨_, _, hJ, -, -⟩ := adicCompletion_isAdic_of_fg I hI
    rw [Ideal.map_pow]
    exact TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hJ n⟩

/-- **A point of `Spec A` killing `I ^ (n + 1)` factors through the quotient stage
`Spec (A^∧ ⧸ I ^ (n + 1) A^∧)`.** -/
theorem exists_stage_factor (n : ℕ) {V : BigFppfOver B S hS} (v : V ⟶ affineOver B S hS hA f)
    (hv : ∀ a ∈ I ^ (n + 1), chartRing v a = 0) :
    ∃ v' : V ⟶ (BigAffineFppf.inclusion B S hS).obj
        ((adicQuotientSystem B S hS hA f I hI).stage (adicCompletionPowStageIdeal I hI n)),
      v' ≫ quotientStageToAffine B S hS hA f I (adicQuotientSystem B S hS hA f I hI)
          (quotientSystemCompatible_adicQuotientSystem B S hS hA f I hI)
          (adicCompletionPowStageIdeal I hI n) = v ∧
        ∀ a : A, ((BigFppfOver.toScheme B S hS).map v').appTop
          ((Scheme.ΓSpecIso
              (CommRingCat.of (AdicCompletion I A ⧸ (adicCompletionPowStageIdeal I hI n).1))).inv
            (Ideal.Quotient.mk (adicCompletionPowStageIdeal I hI n).1
              (algebraMap A (AdicCompletion I A) a))) =
          chartRing v a := by
  let J := adicCompletionPowStageIdeal I hI n
  let q : A →+* AdicCompletion I A ⧸ J.1 :=
    (Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.exists_sub_algebraMap_mem_map_pow I c (n + 1)
    exact ⟨a, (Ideal.Quotient.eq.2 ha).symm⟩
  have hker : RingHom.ker q ≤ RingHom.ker (chartRing v) := fun a ha =>
    hv a (mem_pow_of_algebraMap_mem_map_pow I (n + 1) (Ideal.Quotient.eq_zero_iff_mem.1 ha))
  let ψ := q.liftOfSurjective hq ⟨chartRing v, hker⟩
  have hψ : ψ.comp q = chartRing v := q.liftOfSurjective_comp hq ⟨chartRing v, hker⟩
  let g : (BigFppfOver.toScheme B S hS).obj V ⟶ Spec (CommRingCat.of (AdicCompletion I A ⧸ J.1)) :=
    ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hg : g ≫ Spec.map (CommRingCat.ofHom q) = (BigFppfOver.toScheme B S hS).map v := by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    exact toSpecΓ_comp_spec_chartRing v
  let Q := quotientStageToAffine B S hS hA f I (adicQuotientSystem B S hS hA f I hI)
    (quotientSystemCompatible_adicQuotientSystem B S hS hA f I hI) J
  have hQ : (BigFppfOver.toScheme B S hS).map Q = Spec.map (CommRingCat.ofHom q) := rfl
  let v' : V ⟶ (BigAffineFppf.inclusion B S hS).obj
      ((adicQuotientSystem B S hS hA f I hI).stage J) :=
    Over.homMk (ObjectProperty.homMk g) (by
      rw [← Over.w Q, ← Category.assoc, ← Over.w v]
      congr 1
      apply ObjectProperty.hom_ext
      exact hg)
  refine ⟨v', ?_, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hg
  · have key : (Spec.map (CommRingCat.ofHom q)).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
        = (Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I A ⧸ J.1))).inv (q a) :=
      (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))).symm
    have e : chartRing v a = ((BigFppfOver.toScheme B S hS).map v').appTop
        ((Spec.map (CommRingCat.ofHom q)).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
      change ((Scheme.ΓSpecIso _).inv ≫ ((BigFppfOver.toScheme B S hS).map v).appTop).hom a = _
      rw [← hg]
      rfl
    rw [e, key]
    rfl

end Stage

end AlgebraicGeometry.FormalSpace
