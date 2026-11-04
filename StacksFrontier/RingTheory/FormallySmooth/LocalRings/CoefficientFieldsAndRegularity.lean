module

public import Mathlib
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.UniformSpace.Completion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import Mathlib.RingTheory.MvPowerSeries.Ideal

/-!
# Formally smooth maps of local rings: coefficient fields and regularity

This file proves the existence of coefficient fields and the power series structure of complete
(regular) local algebras with separable residue field, the relation between regularity and adic
formal smoothness of a local algebra over a field, and the comparison of smoothness at a prime
with adic formal smoothness of the induced map of local rings.

## Main definitions

* `FormallySmoothDiscreteMaximalIdeal`: formal smoothness of a map from a discrete field to a
  local ring with its maximal-ideal-adic topology.

## Main results

* `exists_residueField_algHom_section`: a complete local algebra over a field with separable
  residue field has a coefficient field.
* `exists_algEquiv_mvPowerSeries_residueField`: a complete regular local algebra over a field
  with separable residue field is a power series ring over its residue field, in as many
  variables as the dimension of its cotangent space.
* `isRegularLocalRing_of_isFormallySmooth_maximalIdeal`: a Noetherian local algebra over a field
  that is formally smooth for its maximal-ideal-adic topology is regular.
* `isFormallySmooth_maximalIdeal_of_isRegularLocalRing`: a regular local algebra over a field
  with separable residue field is formally smooth for its maximal-ideal-adic topology.
* `smoothAt_iff_formallySmoothNAdic_localization`: for a finite type algebra over a Noetherian
  ring, smoothness at a prime `q` lying over `p` is equivalent to formal smoothness of
  `A_p → B_q` for the maximal-ideal-adic topology of `B_q`.

## Implementation notes

The maximal-ideal-adic topologies are installed as local instances inside the definitions, so
`IsFormallySmooth` receives them by instance resolution; a base field carries the discrete
topology. Smoothness at a prime is `Algebra.SmoothAt`.

## References

* [Stacks Project, Tag 0C34](https://stacks.math.columbia.edu/tag/0C34)
* [Stacks Project, Tag 0C35](https://stacks.math.columbia.edu/tag/0C35)
* [Stacks Project, Tag 07EI](https://stacks.math.columbia.edu/tag/07EI)
* [Stacks Project, Tag 07EJ](https://stacks.math.columbia.edu/tag/07EJ)
* [Stacks Project, Tag 07VH](https://stacks.math.columbia.edu/tag/07VH)
-/

@[expose] public section

/-! ### Coefficient fields -/

section

section

@[expose] public section

/-- A complete local algebra over a field whose residue field is separable over the
base field has a coefficient field: the residue homomorphism has a section by an
algebra homomorphism. -/
@[stacks 0C34, ega "0 19.5.4.4" "special case"]
public theorem exists_residueField_algHom_section
    {k : Type*} {A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField A)) :
    ∃ σ : IsLocalRing.ResidueField A →ₐ[k] A,
      (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal A)).comp σ =
        AlgHom.id k (IsLocalRing.ResidueField A) := by
  let _ : Algebra.FormallySmooth k (IsLocalRing.ResidueField A) :=
    ((Algebra.isSeparableExtension_of_charZero_and_tfae k
      (IsLocalRing.ResidueField A)).2.out 1 6).mp hsep
  exact Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (AlgHom.id k (IsLocalRing.ResidueField A))

end

end

end

/-! ### Complete regular local algebras as power series rings -/

section

section

@[expose] public section

open IsLocalRing

universe u v

/-- A complete regular local algebra over a field whose residue field is separable over
the base field is isomorphic, as an algebra over that field, to a multivariable formal
power series ring over its residue field. -/
@[stacks 0C35,
  ega "0 19.6.4" "special case",
  ega "0 19.8.8" "(i), special case",
  ega "0 21.9.2" "special case", sga "1 II 5.6" "(iii)"]
public theorem exists_algEquiv_mvPowerSeries_residueField
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField A)) :
    Nonempty
      (A ≃ₐ[k] MvPowerSeries
        (Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)))
        (IsLocalRing.ResidueField A)) := by
  obtain ⟨σ, hσ⟩ := exists_residueField_algHom_section hsep
  let : Algebra (ResidueField A) A := σ.toAlgebra
  let : IsScalarTower k (ResidueField A) A :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => (σ.commutes x).symm)
  obtain ⟨e⟩ :=
    (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{v, v, v} A
      (Module.finrank (ResidueField A) (CotangentSpace A)) rfl).2
      (ResidueField A) (by
        have hr : (residue A).comp (algebraMap (ResidueField A) A) = RingHom.id _ := by
          ext x
          exact DFunLike.congr_fun hσ x
        rw [hr]
        exact Function.bijective_id)
  exact ⟨e.restrictScalars k⟩

end

end

end

/-! ### Adic formal smoothness implies regularity -/

section

section

@[expose] public section

open IsLocalRing

/-- Formal smoothness of a map from a discrete field to a local ring with its
maximal-ideal-adic topology. -/
public def FormallySmoothDiscreteMaximalIdeal.{u₁, v₁, w₁}
    {k : Type v₁} {A : Type w₁} [Field k] [CommRing A] [IsLocalRing A]
    (f : k →+* A) : Prop :=
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  let m := IsLocalRing.maximalIdeal A
  letI : TopologicalSpace A := m.adicTopology
  letI : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
  letI : IsLinearTopology A A := m.isLinearTopology
  IsFormallySmooth.{u₁} f

/-- A Noetherian local algebra over a field that is formally smooth for its
maximal-ideal adic topology is a regular local ring. -/
@[stacks 07EI, ega "0 19.6.5" "A regular (k'=k)", ega "0 22.5.8" "a) ⇒ A regular"]
public theorem isRegularLocalRing_of_isFormallySmooth_maximalIdeal.{v, w}
    {k : Type v} {A : Type w} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A]
    (h : FormallySmoothDiscreteMaximalIdeal.{max v w, v, w} (algebraMap k A)) :
    IsRegularLocalRing A := by
  obtain ⟨_, hfs⟩ := h
  exact RingHom.FormallySmoothTop.isRegularLocalRing_of_maximalIdeal.{v, w} hfs

end

end

end

/-! ### Formal smoothness of regular local algebras -/

section

section

@[expose] public section

open scoped Topology Uniformity

open Filter Set Function

private theorem formallySmoothTop_comp_ringEquiv.{u, v, w, z}
    {R : Type v} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsTopologicalRing S]
    [TopologicalSpace T] [IsTopologicalRing T]
    (f : R →+* S) (e : S ≃+* T)
    (he : Continuous e) (he' : Continuous e.symm)
    (h : RingHom.FormallySmoothTop.{u} f) :
    RingHom.FormallySmoothTop.{u} (e.toRingHom.comp f) := by
  intro D _ _ _ J hJ q hq gbar hgbar hcomm
  have hcomm' : (gbar.comp e.toRingHom).comp f = (Ideal.Quotient.mk J).comp q := by
    simpa only [RingHom.comp_assoc] using hcomm
  obtain ⟨g, hg, hgq, hgg⟩ := h D J hJ q hq (gbar.comp e.toRingHom)
    (hgbar.comp he) hcomm'
  refine ⟨g.comp e.symm.toRingHom, hg.comp he', ?_, ?_⟩
  · ext x
    have hx := congrArg (fun h : R →+* D => h x) hgq
    show g (e.symm (e (f x))) = q x
    simpa only [RingHom.comp_apply, RingEquiv.symm_apply_apply] using hx
  · ext x
    have hx := congrArg (fun h : S →+* D ⧸ J => h (e.symm x)) hgg
    show (Ideal.Quotient.mk J) (g (e.symm x)) = gbar x
    change (Ideal.Quotient.mk J) (g (e.symm x)) = gbar (e (e.symm x)) at hx
    simpa only [RingEquiv.apply_symm_apply] using hx

private theorem isFormallySmooth_comp_ringEquiv.{u, v, w, z}
    {R : Type v} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [TopologicalSpace T] [IsTopologicalRing T] [IsLinearTopology T T]
    (f : R →+* S) (e : S ≃+* T)
    (he : Continuous e) (he' : Continuous e.symm)
    (h : IsFormallySmooth.{u} f) :
    IsFormallySmooth.{u} (e.toRingHom.comp f) :=
  ⟨he.comp h.1, formallySmoothTop_comp_ringEquiv f e he he' h.2⟩

private theorem continuous_ringEquiv_adic
    {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (n : Ideal S) (n' : Ideal T)
    (he : n.map e.toRingHom = n') :
    @Continuous S T n.adicTopology n'.adicTopology e := by
  let : WithIdeal S := ⟨n⟩
  let : WithIdeal T := ⟨n'⟩
  exact (WithIdeal.uniformEquiv e he).continuous

private theorem continuous_ringEquiv_symm_adic
    {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (n : Ideal S) (n' : Ideal T)
    (he : n.map e.toRingHom = n') :
    @Continuous T S n'.adicTopology n.adicTopology e.symm := by
  let : WithIdeal S := ⟨n⟩
  let : WithIdeal T := ⟨n'⟩
  exact (WithIdeal.uniformEquiv e he).symm.continuous

private theorem isFormallySmooth_adic_congr_target.{u, v, w, z}
    {R : Type v} {S : Type w} {T : Type z}
    [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (f : R →+* S) (e : S ≃+* T) (n : Ideal S) (n' : Ideal T) (f' : R →+* T)
    (he : n.map e.toRingHom = n') (hf : e.toRingHom.comp f = f')
    (h : @IsFormallySmooth.{u} R S _ _ _ _ _ n.adicTopology
      n.ringFilterBasis.isTopologicalRing n.isLinearTopology f) :
    @IsFormallySmooth.{u} R T _ _ _ _ _ n'.adicTopology
      n'.ringFilterBasis.isTopologicalRing n'.isLinearTopology f' := by
  subst hf
  let : TopologicalSpace S := n.adicTopology
  let : IsTopologicalRing S := n.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology S S := n.isLinearTopology
  let : TopologicalSpace T := n'.adicTopology
  let : IsTopologicalRing T := n'.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology T T := n'.isLinearTopology
  exact isFormallySmooth_comp_ringEquiv f e
    (continuous_ringEquiv_adic e n n' he)
    (continuous_ringEquiv_symm_adic e n n' he) h

private theorem isFormallySmooth_mvPolynomial_idealOfVars.{u, v, w, z}
    (k : Type v) (K : Type w) (σ : Type z)
    [Field k] [Field K] [Algebra k K]
    [TopologicalSpace k] [DiscreteTopology k]
    (hsep : Algebra.IsSeparableExtension k K) :
    @IsFormallySmooth.{u} k (MvPolynomial σ K) _ _ _ _ _
      (MvPolynomial.idealOfVars σ K).adicTopology
      (MvPolynomial.idealOfVars σ K).ringFilterBasis.isTopologicalRing
      (MvPolynomial.idealOfVars σ K).isLinearTopology
      (algebraMap k (MvPolynomial σ K)) := by
  -- `obtain rfl` substitutes `⊥` for the ambient topology and discharges the binder, so the
  -- instances have to be reinstalled at `⊥` for the rest of the proof.
  obtain rfl := (DiscreteTopology.eq_bot (α := k))
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : Algebra.FormallySmooth k K :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k K).2 hsep
  let : Algebra.FormallySmooth k (MvPolynomial σ K) :=
    Algebra.FormallySmooth.comp k K (MvPolynomial σ K)
  let J := MvPolynomial.idealOfVars σ K
  let : TopologicalSpace (MvPolynomial σ K) := J.adicTopology
  let : IsTopologicalRing (MvPolynomial σ K) := J.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology (MvPolynomial σ K) (MvPolynomial σ K) := J.isLinearTopology
  have halg : (algebraMap k (MvPolynomial σ K)).toAlgebra =
      (inferInstance : Algebra k (MvPolynomial σ K)) :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  have hformal : @Algebra.FormallySmooth k (MvPolynomial σ K) _ _
      (algebraMap k (MvPolynomial σ K)).toAlgebra := by
    rw [halg]
    infer_instance
  exact (isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete
    (algebraMap k (MvPolynomial σ K))).1 ⊥ J.adicTopology
    ⟨J, rfl⟩ hformal (continuous_of_discreteTopology)

private theorem bot_adicTopology_eq_bot (R : Type*) [CommRing R] :
    (⊥ : Ideal R).adicTopology = (⊥ : TopologicalSpace R) := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  exact (is_bot_adic_iff.mpr inferInstance).symm

/-- Any ring map from a ring with the `⊥`-adic topology is continuous for an adic topology. -/
private theorem continuous_bot_adicTopology {k R : Type*} [CommRing k] [CommRing R]
    (I : Ideal R) (f : k →+* R) :
    @Continuous k R (⊥ : Ideal k).adicTopology I.adicTopology f := by
  rw [bot_adicTopology_eq_bot]
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace R := I.adicTopology
  exact continuous_of_discreteTopology

private theorem idealOfVars_isMaximal (K : Type*) (σ : Type*) [Field K] :
    (MvPolynomial.idealOfVars σ K).IsMaximal := by
  let J := MvPolynomial.idealOfVars σ K
  have hker : J = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K) := by
    ext p
    show p ∈ J ↔ MvPolynomial.constantCoeff p = 0
    rw [← pow_one J, MvPolynomial.mem_pow_idealOfVars_iff']
    constructor
    · intro hp
      simpa [MvPolynomial.constantCoeff_eq] using hp 0 (by simp)
    · intro hp x hx
      have hdegree0 : Finsupp.degree x = 0 := by lia
      have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp hdegree0
      simpa [hx0, MvPolynomial.constantCoeff_eq] using hp
  show J.IsMaximal
  rw [hker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun x =>
    ⟨MvPolynomial.C x, MvPolynomial.constantCoeff_C σ x⟩)

private noncomputable def completionCoeRingHomForIdeal (R : Type*) [CommRing R]
    (I : Ideal R) :
    R →+* @UniformSpace.Completion R (@WithIdeal.instUniformSpace R _ ⟨I⟩) := by
  letI : WithIdeal R := ⟨I⟩
  exact UniformSpace.Completion.coeRingHom

private noncomputable def adicCompletionRingEquivForIdeal (R : Type*) [CommRing R]
    (I : Ideal R) :
    @UniformSpace.Completion R (@WithIdeal.instUniformSpace R _ ⟨I⟩) ≃+*
      AdicCompletion I R := by
  letI : WithIdeal R := ⟨I⟩
  exact AdicCompletionBridge.adicCompletionRingEquiv I rfl

private theorem map_bridge_ideal (R : Type*) [CommRing R] (I : Ideal R) :
    (I.map (completionCoeRingHomForIdeal R I)).map
        (adicCompletionRingEquivForIdeal R I).toRingHom =
      I.map (algebraMap R (AdicCompletion I R)) := by
  let : WithIdeal R := ⟨I⟩
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (AdicCompletionBridge.adicCompletionRingEquiv_coe I rfl)

/-- The `idealOfVars`-adic uniformity on `MvPolynomial σ K`, so that
`UniformSpace.Completion (MvPolynomial σ K)` means the `idealOfVars`-adic completion. -/
@[instance_reducible] private noncomputable local instance withIdealMvPolynomial
    (K : Type*) (σ : Type*) [Field K] : WithIdeal (MvPolynomial σ K) :=
  ⟨MvPolynomial.idealOfVars σ K⟩

/-- The ideal `idealOfVars σ K` pushed forward to the completion of `MvPolynomial σ K`. -/
private noncomputable abbrev completionIdealOfVars (K : Type*) (σ : Type*) [Field K] :
    Ideal (UniformSpace.Completion (MvPolynomial σ K)) :=
  (MvPolynomial.idealOfVars σ K).map
    (UniformSpace.Completion.coeRingHom : MvPolynomial σ K →+*
      UniformSpace.Completion (MvPolynomial σ K))

private theorem map_completionIdeal_mvPowerSeries_maximalIdeal
    (K : Type*) (σ : Type*) [Field K] [Finite σ] :
    (completionIdealOfVars K σ).map
      (((AdicCompletionBridge.adicCompletionRingEquiv (MvPolynomial.idealOfVars σ K) rfl).trans
        (MvPowerSeries.toAdicCompletionAlgEquiv σ K).toRingEquiv.symm).toRingHom) =
      IsLocalRing.maximalIdeal (MvPowerSeries σ K) := by
  let P := MvPolynomial σ K
  let J := MvPolynomial.idealOfVars σ K
  let : WithIdeal P := ⟨J⟩
  let C := AdicCompletion J P
  let Jhat := J.map (UniformSpace.Completion.coeRingHom : P →+* UniformSpace.Completion P)
  let b := AdicCompletionBridge.adicCompletionRingEquiv J (show IsAdic J from rfl)
  let c := (MvPowerSeries.toAdicCompletionAlgEquiv σ K).toRingEquiv
  let e : UniformSpace.Completion P ≃+* MvPowerSeries σ K := b.trans c.symm
  have : J.IsMaximal := idealOfVars_isMaximal K σ
  have hfg : J.FG := MvPolynomial.idealOfVars_fg σ K
  have : (J.map (algebraMap P C)).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le J J le_rfl hfg
  have : IsAdicComplete (J.map (algebraMap P C)) C :=
    AdicCompletion.isAdicComplete_self J hfg
  have : IsLocalRing C := isLocalRing_of_isAdicComplete_maximal
    (J.map (algebraMap P C))
  have hC : J.map (algebraMap P C) = IsLocalRing.maximalIdeal C :=
    IsLocalRing.eq_maximalIdeal ‹(J.map (algebraMap P C)).IsMaximal›
  show Jhat.map e.toRingHom = IsLocalRing.maximalIdeal (MvPowerSeries σ K)
  have hecomp : e.toRingHom = c.symm.toRingHom.comp b.toRingHom := by
    ext x
    rfl
  calc
    Jhat.map e.toRingHom = (Jhat.map b.toRingHom).map c.symm.toRingHom := by
      simp only [hecomp, Ideal.map_map]
    _ = (J.map (algebraMap P C)).map c.symm.toRingHom := by
      have hbridge : Jhat.map b.toRingHom = J.map (algebraMap P C) :=
        map_bridge_ideal P J
      rw [hbridge]
    _ = IsLocalRing.maximalIdeal (MvPowerSeries σ K) := by
      rw [hC]
      exact IsLocalRing.map_maximalIdeal_of_surjective c.symm.toRingHom c.symm.surjective

/-- The completion of `MvPolynomial σ K` carries the `completionIdealOfVars`-adic topology,
not the one induced by its uniformity. -/
@[instance_reducible] private noncomputable local instance adicTopologyCompletionMvPolynomial
    (K : Type*) (σ : Type*) [Field K] :
    TopologicalSpace (UniformSpace.Completion (MvPolynomial σ K)) :=
  (completionIdealOfVars K σ).adicTopology

private theorem isFormallySmooth_completion_mvPolynomial.{u, v, w, z}
    (k : Type v) (K : Type w) (σ : Type z)
    [Field k] [Field K] [Algebra k K] [Finite σ]
    [TopologicalSpace k] [DiscreteTopology k]
    (hsep : Algebra.IsSeparableExtension k K) :
    @IsFormallySmooth.{u} k
      (UniformSpace.Completion (MvPolynomial σ K)) _ _ _ _ _
      (adicTopologyCompletionMvPolynomial K σ)
      (completionIdealOfVars K σ).nonarchimedean.toIsTopologicalRing
      (completionIdealOfVars K σ).isLinearTopology
      (UniformSpace.Completion.coeRingHom.comp (algebraMap k (MvPolynomial σ K))) := by
  obtain rfl := (DiscreteTopology.eq_bot (α := k))
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let P := MvPolynomial σ K
  let J := MvPolynomial.idealOfVars σ K
  let : WithIdeal P := ⟨J⟩
  let Jhat : Ideal (UniformSpace.Completion P) :=
    J.map UniformSpace.Completion.coeRingHom
  let : TopologicalSpace (UniformSpace.Completion P) := Jhat.adicTopology
  let : IsTopologicalRing (UniformSpace.Completion P) :=
    Jhat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (UniformSpace.Completion P) (UniformSpace.Completion P) :=
    Jhat.isLinearTopology
  have hcont := continuous_bot_adicTopology J (algebraMap k P)
  have hpol :
      let : TopologicalSpace k := (⊥ : Ideal k).adicTopology
      let : IsTopologicalRing k := (⊥ : Ideal k).ringFilterBasis.isTopologicalRing
      let : IsLinearTopology k k := (⊥ : Ideal k).isLinearTopology
      let : TopologicalSpace P := J.adicTopology
      let : IsTopologicalRing P := J.ringFilterBasis.isTopologicalRing
      let : IsLinearTopology P P := J.isLinearTopology
      IsFormallySmooth.{u} (algebraMap k P) :=
    ((isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete
      (algebraMap k P)).2 (⊥ : Ideal k) J hcont).2
      (isFormallySmooth_mvPolynomial_idealOfVars k K σ hsep)
  have hhat := (isFormallySmooth_iff_adicCompletion
    (⊥ : Ideal k) J Submodule.fg_bot (MvPolynomial.idealOfVars_fg σ K)
    (algebraMap k P) hcont).1.mp hpol
  have hcontHat : @Continuous k (UniformSpace.Completion P)
      (⊥ : Ideal k).adicTopology Jhat.adicTopology
      (UniformSpace.Completion.coeRingHom.comp (algebraMap k P)) := hhat.1
  exact ((isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete
    (UniformSpace.Completion.coeRingHom.comp (algebraMap k P))).2
      (⊥ : Ideal k) Jhat hcontHat).1 hhat

private theorem isFormallySmooth_mvPowerSeries_maximalIdeal.{u, v, w, z}
    (k : Type v) (K : Type w) (σ : Type z)
    [Field k] [Field K] [Algebra k K] [Finite σ]
    [TopologicalSpace k] [DiscreteTopology k]
    (hsep : Algebra.IsSeparableExtension k K) :
    @IsFormallySmooth.{u} k (MvPowerSeries σ K) _ _ _ _ _
      (IsLocalRing.maximalIdeal (MvPowerSeries σ K)).adicTopology
      (IsLocalRing.maximalIdeal (MvPowerSeries σ K)).ringFilterBasis.isTopologicalRing
      (IsLocalRing.maximalIdeal (MvPowerSeries σ K)).isLinearTopology
      (algebraMap k (MvPowerSeries σ K)) := by
  obtain rfl := (DiscreteTopology.eq_bot (α := k))
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let P := MvPolynomial σ K
  let J := MvPolynomial.idealOfVars σ K
  let : WithIdeal P := ⟨J⟩
  let U := UniformSpace.Completion P
  let Jhat : Ideal U := J.map UniformSpace.Completion.coeRingHom
  let B := MvPowerSeries σ K
  let m := IsLocalRing.maximalIdeal B
  let b := AdicCompletionBridge.adicCompletionRingEquiv J (show IsAdic J from rfl)
  let ca := MvPowerSeries.toAdicCompletionAlgEquiv σ K
  let e : U ≃+* B := b.trans ca.toRingEquiv.symm
  have he : Jhat.map e.toRingHom = m :=
    map_completionIdeal_mvPowerSeries_maximalIdeal K σ
  have hecoe (p : P) : e (p : U) = algebraMap P B p := by
    apply ca.injective
    show ca (ca.symm (b (p : U))) = ca (algebraMap P B p)
    rw [ca.apply_symm_apply, ca.commutes, AdicCompletionBridge.adicCompletionRingEquiv_coe]
    rfl
  have hmap : e.toRingHom.comp
      (UniformSpace.Completion.coeRingHom.comp (algebraMap k P)) = algebraMap k B := by
    apply RingHom.ext
    intro x
    show e (↑(algebraMap k P x)) = algebraMap k B x
    rw [hecoe, MvPolynomial.algebraMap_apply, MvPowerSeries.algebraMap_apply]
    exact MvPolynomial.coe_C _
  exact isFormallySmooth_adic_congr_target
    (UniformSpace.Completion.coeRingHom.comp (algebraMap k P)) e Jhat m _ he hmap
    (isFormallySmooth_completion_mvPolynomial k K σ hsep)

private theorem isSeparableExtension_residueField_adicCompletion
    {k : Type*} {A : Type*} [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A]
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField A)) :
    Algebra.IsSeparableExtension k
      (IsLocalRing.ResidueField (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let g := IsLocalRing.ResidueField.map (algebraMap A C)
  have hg : Function.Bijective g := AdicCompletion.residueField_map_bijective A
  let er : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField C :=
    RingEquiv.ofBijective g hg
  let e : IsLocalRing.ResidueField A ≃ₐ[k] IsLocalRing.ResidueField C :=
    { er with
      commutes' := by
        intro x
        simp [er, g, IsScalarTower.algebraMap_apply k A (IsLocalRing.ResidueField A),
          IsScalarTower.algebraMap_apply k C (IsLocalRing.ResidueField C),
          IsScalarTower.algebraMap_apply k A C] }
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField A) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k _).2 hsep
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField C) :=
    Algebra.FormallySmooth.of_equiv e
  exact (Algebra.FormallySmooth.iff_isSeparableExtension k _).1 inferInstance

/-- A regular local algebra over a field whose residue field is separable over
the base field is formally smooth for its maximal-ideal adic topology. -/
@[stacks 07EJ]
public theorem isFormallySmooth_maximalIdeal_of_isRegularLocalRing.{u, v, w}
    {k : Type v} {A : Type w} [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A]
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField A)) :
    FormallySmoothDiscreteMaximalIdeal.{u, v, w} (algebraMap k A) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let mC := IsLocalRing.maximalIdeal C
  let : WithIdeal A := ⟨m⟩
  let U := UniformSpace.Completion A
  let mU : Ideal U := m.map UniformSpace.Completion.coeRingHom
  have hsepC : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField C) :=
    isSeparableExtension_residueField_adicCompletion hsep
  have : IsRegularLocalRing C :=
    (isRegularLocalRing_iff_adicCompletion_maximalIdeal).mp inferInstance
  let σ := Fin (Module.finrank (IsLocalRing.ResidueField C) (IsLocalRing.CotangentSpace C))
  let B := MvPowerSeries σ (IsLocalRing.ResidueField C)
  obtain ⟨e⟩ := exists_algEquiv_mvPowerSeries_residueField hsepC
  have he : mC.map e.toRingEquiv.toRingHom = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective e.toRingEquiv.toRingHom e.surjective
  have hB :
      let n := IsLocalRing.maximalIdeal B
      let : TopologicalSpace k := ⊥
      let : DiscreteTopology k := ⟨rfl⟩
      let : TopologicalSpace B := n.adicTopology
      let : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
      let : IsLinearTopology B B := n.isLinearTopology
      IsFormallySmooth.{u} (algebraMap k B) :=
    isFormallySmooth_mvPowerSeries_maximalIdeal k (IsLocalRing.ResidueField C) σ hsepC
  have hC :
      let : TopologicalSpace C := mC.adicTopology
      let : IsTopologicalRing C := mC.ringFilterBasis.isTopologicalRing
      let : IsLinearTopology C C := mC.isLinearTopology
      IsFormallySmooth.{u} (algebraMap k C) := by
    exact isFormallySmooth_adic_congr_target
      (algebraMap k B) e.symm.toRingEquiv
      (IsLocalRing.maximalIdeal B) mC _ (by simpa using
        (IsLocalRing.map_maximalIdeal_of_surjective e.symm.toRingEquiv.toRingHom
          e.symm.surjective)) (RingHom.ext e.symm.commutes) hB
  let b := AdicCompletionBridge.adicCompletionRingEquiv m (show IsAdic m from rfl)
  have hb : mU.map b.toRingHom = mC := by
    have hbridge : mU.map b.toRingHom = m.map (algebraMap A C) :=
      map_bridge_ideal A m
    rw [hbridge]
    exact (AdicCompletion.maximalIdeal_eq_map_of_fg m.fg_of_isNoetherianRing).symm
  have hb' : mC.map b.symm.toRingHom = mU := by
    rw [← hb, Ideal.map_map]
    convert Ideal.map_id mU using 1
    congr 1
    ext x
    simp
  have hU :
      let : TopologicalSpace U := mU.adicTopology
      let : IsTopologicalRing U := mU.ringFilterBasis.isTopologicalRing
      let : IsLinearTopology U U := mU.isLinearTopology
      IsFormallySmooth.{u}
        (UniformSpace.Completion.coeRingHom.comp (algebraMap k A)) := by
    refine isFormallySmooth_adic_congr_target
      (algebraMap k C) b.symm mC mU _ hb' ?_ hC
    apply RingHom.ext
    intro x
    show b.symm ((algebraMap k C) x) =
      (↑(algebraMap k A x) : U)
    rw [← b.symm_apply_apply (↑(algebraMap k A x) : U)]
    congr 1
    rw [AdicCompletionBridge.adicCompletionRingEquiv_coe]
    rfl
  have hcont := continuous_bot_adicTopology m (algebraMap k A)
  have hcontU := continuous_bot_adicTopology mU
    (UniformSpace.Completion.coeRingHom.comp (algebraMap k A))
  have hU' := ((isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete
    (UniformSpace.Completion.coeRingHom.comp (algebraMap k A))).2
    (⊥ : Ideal k) mU hcontU).2 hU
  have hcomp := (isFormallySmooth_iff_adicCompletion
    (⊥ : Ideal k) m Submodule.fg_bot m.fg_of_isNoetherianRing
    (algebraMap k A) hcont).1.mpr hU'
  exact ((isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete
    (algebraMap k A)).2 (⊥ : Ideal k) m hcont).1 hcomp

end

end

end

/-! ### Smoothness at a prime and adic formal smoothness -/

section

section

@[expose] public section

open IsLocalRing

/-- Let `A → B` be a finite type map with `A` Noetherian, and let the prime
`q ⊆ B` lie over the prime `p ⊆ A`. Then the map is smooth at `q` if and
only if the canonical local map `A_p → B_q` is formally smooth for the
maximal-ideal-adic topology on `B_q`. -/
@[stacks 07VH,
  ega "0 22.6.4" "c) <=> d)",
  ega "IV 6.8.6" "a) ⇔ c)",
  ega "IV 17.5.3" "a) ⇔ d)",
  sga "1 III 1.9" "Noetherian A"]
public theorem smoothAt_iff_formallySmoothNAdic_localization.{u, v}
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Algebra.SmoothAt A B q ↔
      RingHom.FormallySmoothNAdic.{max u v, u, v}
        (@algebraMap (Localization.AtPrime p) (Localization.AtPrime q) _ _
          (Localization.AtPrime.algebraOfLiesOver p q))
        (maximalIdeal (Localization.AtPrime q)) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  constructor
  · intro h
    let : Algebra.FinitePresentation A B :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    obtain ⟨g, hg, hsm⟩ := h
    have hlocal : Algebra.IsSmoothAt A q :=
      Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm
        ((PrimeSpectrum.mem_basicOpen g ⟨q, inferInstance⟩).mpr hg)
    have hfsA : Algebra.FormallySmooth A (Localization.AtPrime q) := hlocal
    let := hfsA
    have hfs : Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q) :=
      Algebra.FormallySmooth.localization_base p.primeCompl
    let := hfs
    intro C _ J hJ f ψ hcomm _
    let := f.toAlgebra
    let ψa : Localization.AtPrime q →ₐ[Localization.AtPrime p] C ⧸ J :=
      { ψ with commutes' := fun x => DFunLike.congr_fun hcomm x }
    let ga := Algebra.FormallySmooth.lift J ⟨2, hJ⟩ ψa
    exact ⟨ga.toRingHom, RingHom.ext (Algebra.FormallySmooth.mk_lift J ⟨2, hJ⟩ ψa),
      by ext x; exact ga.commutes x⟩
  · intro h
    have hlocal : Algebra.IsSmoothAt A q := by
      apply ((Algebra.isSmoothAt_tfae (R := A) (S := B) q).out 4 1).mp
      intro B' C _ _ _ _ _ _ _ _ φ hφ hs g hq hg
      let : IsLocalHom (φ : B' →+* C) :=
        IsLocalHom.of_surjective (φ : B' →+* C) hφ
      have hg_units : ∀ y : q.primeCompl, IsUnit (g (y : B)) := fun y =>
        IsLocalRing.notMem_maximalIdeal.1 fun hy => y.2 (hq ▸ hy)
      let gq : Localization.AtPrime q →ₐ[A] C := IsLocalization.liftAlgHom hg_units
      have hA_units : ∀ y : p.primeCompl, IsUnit (algebraMap A B' (y : A)) := by
        intro y
        exact IsLocalHom.map_nonunit (f := (φ : B' →+* C))
          (a := algebraMap A B' (y : A)) <|
          IsLocalRing.notMem_maximalIdeal.1 <| by
            intro hy
            apply y.2
            have hmaps : φ (algebraMap A B' (y : A)) =
                g (algebraMap A B (y : A)) :=
              (φ.commutes (y : A)).trans (g.commutes (y : A)).symm
            change φ (algebraMap A B' (y : A)) ∈ maximalIdeal C at hy
            rw [hmaps] at hy
            have hyq : (algebraMap A B (y : A)) ∈ q := by
              rwa [← hq]
            exact (q.over_def p).symm ▸ hyq
      let fp : Localization.AtPrime p →ₐ[A] B' :=
        IsLocalization.liftAlgHom (M := p.primeCompl) (S := Localization.AtPrime p)
          (f := Algebra.ofId A B') hA_units
      let e : B' ⧸ RingHom.ker (φ : B' →+* C) ≃+* C :=
        RingHom.quotientKerEquivOfSurjective (f := (φ : B' →+* C)) hφ
      have hmk (y : B') : e (Ideal.Quotient.mk _ y) = φ y :=
        RingHom.quotientKerEquivOfSurjective_apply_mk hφ y
      let ψ : Localization.AtPrime q →+*
          B' ⧸ RingHom.ker (φ : B' →+* C) := e.symm.toRingHom.comp gq.toRingHom
      have hcomm : ψ.comp (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
          (Ideal.Quotient.mk (RingHom.ker (φ : B' →+* C))).comp fp.toRingHom := by
        apply IsLocalization.ringHom_ext p.primeCompl
        ext x
        apply e.injective
        simp only [RingHom.comp_apply]
        show e (e.symm (gq ((algebraMap (Localization.AtPrime p)
          (Localization.AtPrime q)) (algebraMap A (Localization.AtPrime p) x)))) =
          e (Ideal.Quotient.mk _ (fp (algebraMap A (Localization.AtPrime p) x)))
        rw [e.apply_symm_apply, hmk, ← IsScalarTower.algebraMap_apply A (Localization.AtPrime p)
          (Localization.AtPrime q), gq.commutes, fp.commutes, φ.commutes]
      have hpow : ∃ k : ℕ, 1 ≤ k ∧
          maximalIdeal (Localization.AtPrime q) ^ k ≤ RingHom.ker ψ := by
        obtain ⟨k, hk⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp
          (inferInstance : IsArtinianRing C)
        have hk0 : k ≠ 0 := by
          intro hkzero
          subst k
          have hone : (1 : C) ∈ (⊥ : Ideal C) := by
            have hmem : (1 : C) ∈ maximalIdeal C ^ 0 := by simp
            rwa [hk] at hmem
          simp at hone
        have hmap : Ideal.map gq.toRingHom
            (maximalIdeal (Localization.AtPrime q)) ≤ maximalIdeal C := by
          rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q,
            Ideal.map_map, Ideal.map_le_iff_le_comap]
          intro x hx
          show gq (algebraMap B (Localization.AtPrime q) x) ∈ maximalIdeal C
          rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
          show x ∈ Ideal.comap (g : B →+* C) (maximalIdeal C)
          rw [hq]
          exact hx
        refine ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, ?_⟩
        intro x hx
        rw [RingHom.mem_ker]
        apply e.injective
        show e (e.symm (gq x)) = e 0
        rw [e.apply_symm_apply, map_zero]
        have hx' : gq x ∈ maximalIdeal C ^ k := (pow_le_pow_left' hmap k) (by
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ hx)
        rwa [hk] at hx'
      obtain ⟨lift, hlift, hbase⟩ :=
        h B' (RingHom.ker (φ : B' →+* C))
          (Ideal.sq_eq_bot_of_isSimpleModule (RingHom.ker_ne_top _) hs)
          fp.toRingHom ψ hcomm hpow
      let liftA : B →ₐ[A] B' :=
        { lift.comp (algebraMap B (Localization.AtPrime q)) with
          commutes' := fun x => by
            calc
              lift (algebraMap B (Localization.AtPrime q) (algebraMap A B x)) =
                  lift (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
                    (algebraMap A (Localization.AtPrime p) x)) := by
                    congr 1
                    exact (IsScalarTower.algebraMap_apply A B
                      (Localization.AtPrime q) x).symm.trans
                        (IsScalarTower.algebraMap_apply A (Localization.AtPrime p)
                          (Localization.AtPrime q) x)
              _ = fp (algebraMap A (Localization.AtPrime p) x) :=
                DFunLike.congr_fun hbase _
              _ = algebraMap A B' x := fp.commutes x }
      refine ⟨liftA, ?_⟩
      apply AlgHom.ext
      intro x
      show φ (lift (algebraMap B (Localization.AtPrime q) x)) = g x
      have hx := congrArg e (DFunLike.congr_fun hlift
        (algebraMap B (Localization.AtPrime q) x))
      change e (Ideal.Quotient.mk _ (lift (algebraMap B
        (Localization.AtPrime q) x))) = e (e.symm (gq
          (algebraMap B (Localization.AtPrime q) x))) at hx
      rw [hmk, e.apply_symm_apply] at hx
      exact hx.trans (IsLocalization.lift_eq hg_units x)
    let : Algebra.FinitePresentation A B :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact Algebra.IsSmoothAt.exists_notMem_smooth A q

end

end

end

end
