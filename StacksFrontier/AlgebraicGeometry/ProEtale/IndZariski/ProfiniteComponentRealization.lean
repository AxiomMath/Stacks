module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Profinite
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Connected.ComponentSpace
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ComponentRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# Ind-Zariski realization of a profinite space over the components of a spectrum

For a ring `A` and a profinite space `T` with a continuous map to the space of connected
components of `Spec A`, there is an ind-Zariski `A`-algebra `B` whose spectrum is the fibre
product `Spec A \times_{\pi_0(Spec A)} T`. Its space of connected components is `T`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_indZariski_of_profinite_component_map`: the algebra, the
  map from its spectrum to `T`, the identification of the component space with `T`, and the
  cartesian square realizing the spectrum as the fibre product.

## Implementation notes

The construction is a cofiltered limit over the discrete quotients of `T`. For a discrete
quotient `q` the finite product `q \to A` has spectrum the disjoint union of `q` copies of
`Spec A`, and the closed union of connected components of that spectrum cut out by the image
of `T` is the spectrum of a surjective ind-Zariski algebra over `q \to A`. These stages form a
filtered diagram of algebras over `A`, whose colimit is the asserted algebra; its spectrum is
the limit of the stage spectra because the transition morphisms are affine.

Choices of stage and of transition morphism are packaged in two auxiliary structures so that
the diagram can be assembled: the transition morphisms are uniquely determined by their effect
on spectra, which is what makes the functor laws hold.

The ring `A` and the profinite space `T` have independent universes. The constructed algebra
lies in their maximum universe, as does the index category for its ind-Zariski presentation.
The cartesian diagram is stated with its canonical projections in `TopCat` at that maximum
universe, using `ULift` for the spaces attached to `A` and for `T`.

## References

* [Stacks Project, Tag 097D](https://stacks.math.columbia.edu/tag/097D)
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace AlgebraicGeometry.ProEtale

open Topology

private lemma isCoinducing_prodMap_id_mk
    (S : Type u) (X : Type v) [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace X] :
    IsCoinducing (fun p : S × X => (p.1, (ConnectedComponents.mk p.2 :
      ConnectedComponents X))) := by
  let h : S × X → S × ConnectedComponents X := fun p => (p.1, p.2)
  have hc : Continuous h :=
    continuous_fst.prodMk (ConnectedComponents.continuous_coe.comp continuous_snd)
  show IsCoinducing h
  rw [isCoinducing_iff]
  intro U
  constructor
  · intro hpre
    have hsec (s : S) :
        IsOpen {c : ConnectedComponents X | (s, c) ∈ U} := by
      apply (ConnectedComponents.isQuotientMap_coe.isCoinducing.isOpen_preimage).mp
      let k : X → S × X := fun x => (s, x)
      have hk : Continuous k := by
        show Continuous (fun x : X => (s, x))
        exact (continuous_const : Continuous (fun _ : X => s)).prodMk continuous_id
      have heq : k ⁻¹' (h ⁻¹' U) =
          (fun x : X => (s, ConnectedComponents.mk x)) ⁻¹' U := by
        ext x
        simp [h, k]
      show IsOpen ((fun x : X => (s, ConnectedComponents.mk x)) ⁻¹' U)
      rw [← heq]
      exact hpre.preimage hk
    have hU : U = ⋃ s : S,
        ({s} : Set S) ×ˢ {c : ConnectedComponents X | (s, c) ∈ U} := by
      ext ⟨s, c⟩
      simp
    rw [hU]
    exact isOpen_iUnion fun s => (isOpen_discrete _).prod (hsec s)
  · exact fun hU => hU.preimage hc

private noncomputable def connectedComponentsProdDiscreteHomeo
    (S : Type u) (X : Type v) [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace X] :
    ConnectedComponents (S × X) ≃ₜ S × ConnectedComponents X := by
  let h : S × X → S × ConnectedComponents X := fun p => (p.1, p.2)
  let hc : C(S × X, S × ConnectedComponents X) :=
    ⟨h, continuous_fst.prodMk
      (ConnectedComponents.continuous_coe.comp continuous_snd)⟩
  let g : ConnectedComponents (S × X) → S × ConnectedComponents X :=
    hc.continuous.connectedComponentsLift
  have hgcont : Continuous g := hc.continuous.connectedComponentsLift_continuous
  have hg_bij : Function.Bijective g := by
    constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
      have hab' : h x = h y := by simpa [g, hc] using hab
      change (x.1, ConnectedComponents.mk x.2) =
        (y.1, ConnectedComponents.mk y.2) at hab'
      obtain ⟨h1, h2⟩ := Prod.mk.inj hab'
      apply ConnectedComponents.coe_eq_coe.mpr
      rw [connectedComponent_prod, connectedComponent_prod, h1,
        (ConnectedComponents.coe_eq_coe.mp h2)]
    · rintro ⟨s, c⟩
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨ConnectedComponents.mk (s, x), rfl⟩
  have hco : IsCoinducing h := isCoinducing_prodMap_id_mk S X
  have hgco : IsCoinducing g := by
    apply IsCoinducing.of_comp ConnectedComponents.continuous_coe hgcont
    simpa [g, hc, h] using hco
  exact IsHomeomorph.homeomorph g
    ⟨hgcont, hgco.isOpenMap_of_injective hg_bij.1, hg_bij⟩

private noncomputable def connectedComponentsDiscreteHomeo
    (S : Type u) [TopologicalSpace S] [DiscreteTopology S] :
    S ≃ₜ ConnectedComponents S where
  toFun := ConnectedComponents.mk
  invFun := continuous_id.connectedComponentsLift
  left_inv := fun _ => rfl
  right_inv := ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  continuous_toFun := ConnectedComponents.continuous_coe
  continuous_invFun := continuous_id.connectedComponentsLift_continuous

private lemma continuous_prodToSigma
    (S : Type u) (X : Type v) [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace X] :
    Continuous (fun p : S × X => (⟨p.1, p.2⟩ : Σ _ : S, X)) := by
  refine ⟨fun U hU => ?_⟩
  rw [isOpen_prod_iff]
  rw [isOpen_sigma_iff] at hU
  intro a b hab
  refine ⟨{a}, (fun x : X => (⟨a, x⟩ : Σ _ : S, X)) ⁻¹' U,
    isOpen_discrete _, hU a, by simp, hab, ?_⟩
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  obtain rfl : s = a := by simpa using hs
  simpa using hx

private noncomputable def stageComponentsMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    C(T, ConnectedComponents (PrimeSpectrum (q → A))) := by
  let p : C(T, q × ConnectedComponents (PrimeSpectrum A)) :=
    ⟨fun t => (q.proj t, f t), q.proj_continuous.prodMk f.continuous⟩
  let h₁ := (connectedComponentsProdDiscreteHomeo q (PrimeSpectrum A)).symm
  let h₂ := (continuous_prodToSigma q (PrimeSpectrum A)).connectedComponentsMap
  let h₃ := Continuous.connectedComponentsMap
    (PrimeSpectrum.isOpenEmbedding_sigmaToPi (fun _ : q => A)).continuous
  have h₂cont : Continuous h₂ :=
    (continuous_prodToSigma q (PrimeSpectrum A)).connectedComponentsMap_continuous
  have h₃cont : Continuous h₃ := Continuous.connectedComponentsMap_continuous
    (PrimeSpectrum.isOpenEmbedding_sigmaToPi (fun _ : q => A)).continuous
  exact ⟨fun t => h₃ (h₂ (h₁ (p t))),
    h₃cont.comp (h₂cont.comp (h₁.continuous.comp p.continuous))⟩

private def stageRestrictRingHom
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    (q q' : DiscreteQuotient T) (h : q ≤ q') : (q' → A) →+* (q → A) where
  toFun b s := b (DiscreteQuotient.ofLE h s)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

private lemma connectedComponentsProdDiscreteHomeo_symm_mk
    (S : Type u) (X : Type v) [TopologicalSpace S] [DiscreteTopology S]
    [TopologicalSpace X] (s : S) (x : X) :
    (connectedComponentsProdDiscreteHomeo S X).symm (s, ConnectedComponents.mk x) =
      ConnectedComponents.mk (s, x) := by
  apply (connectedComponentsProdDiscreteHomeo S X).injective
  exact (connectedComponentsProdDiscreteHomeo S X).apply_symm_apply _

attribute [local simp] connectedComponentsProdDiscreteHomeo_symm_mk

private lemma stageComponentsMap_mk
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) (t : T) (p : PrimeSpectrum A)
    (hp : f t = ConnectedComponents.mk p) :
    stageComponentsMap A T q f t =
      ConnectedComponents.mk (PrimeSpectrum.sigmaToPi (fun _ : q => A)
        ⟨q.proj t, p⟩) := by
  dsimp [stageComponentsMap]
  rw [hp]
  simp only [connectedComponentsProdDiscreteHomeo_symm_mk,
    Continuous.connectedComponentsMap_mk, PrimeSpectrum.sigmaToPi_apply]

private noncomputable def stageSpectrumIndexMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) :
    C(PrimeSpectrum (q → A), q) := by
  letI : Finite q := inferInstance
  letI : DiscreteTopology q := inferInstance
  let e := PrimeSpectrum.sigmaToPiHomeo (fun _ : q => A)
  have hfst : Continuous (fun z : Σ _ : q, PrimeSpectrum A => z.1) :=
    continuous_sigma (fun _ => continuous_const)
  exact ⟨fun p => (e.symm p).1, hfst.comp e.symm.continuous⟩

private noncomputable def stageSpectrumBaseMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) :
    C(PrimeSpectrum (q → A), PrimeSpectrum A) := by
  letI : Finite q := inferInstance
  let e := PrimeSpectrum.sigmaToPiHomeo (fun _ : q => A)
  have hsnd : Continuous (fun z : Σ _ : q, PrimeSpectrum A => z.2) :=
    continuous_sigma (fun _ => continuous_id)
  exact ⟨fun p => (e.symm p).2, hsnd.comp e.symm.continuous⟩

private noncomputable def stageComponentIndexMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) :
    C(ConnectedComponents (PrimeSpectrum (q → A)), q) :=
  let e := connectedComponentsDiscreteHomeo q
  ⟨fun c => e.symm ((stageSpectrumIndexMap A T q).continuous.connectedComponentsMap c),
    e.symm.continuous.comp
      (stageSpectrumIndexMap A T q).continuous.connectedComponentsMap_continuous⟩

private noncomputable def stageComponentBaseMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) :
    C(ConnectedComponents (PrimeSpectrum (q → A)),
      ConnectedComponents (PrimeSpectrum A)) :=
  ⟨(stageSpectrumBaseMap A T q).continuous.connectedComponentsMap,
    (stageSpectrumBaseMap A T q).continuous.connectedComponentsMap_continuous⟩

private lemma sigmaToPiHomeo_symm_sigmaToPi
    (A : Type u) (ι : Type*) [CommRing A] [Finite ι] (i : ι) (p : PrimeSpectrum A) :
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : ι => A)).symm
      (PrimeSpectrum.sigmaToPi (fun _ : ι => A) ⟨i, p⟩) = ⟨i, p⟩ :=
  (Homeomorph.symm_apply_eq _).2 (PrimeSpectrum.sigmaToPiHomeo_apply _).symm

private lemma stageSpectrumIndexMap_sigmaToPi
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (i : q) (p : PrimeSpectrum A) :
    stageSpectrumIndexMap A T q (PrimeSpectrum.sigmaToPi (fun _ : q => A) ⟨i, p⟩) = i :=
  congrArg Sigma.fst (sigmaToPiHomeo_symm_sigmaToPi A q i p)

private lemma stageSpectrumBaseMap_sigmaToPi
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (i : q) (p : PrimeSpectrum A) :
    stageSpectrumBaseMap A T q (PrimeSpectrum.sigmaToPi (fun _ : q => A) ⟨i, p⟩) = p :=
  congrArg Sigma.snd (sigmaToPiHomeo_symm_sigmaToPi A q i p)

private lemma stageComponentIndexMap_mk
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (p : PrimeSpectrum (q → A)) :
    stageComponentIndexMap A T q (ConnectedComponents.mk p) =
      stageSpectrumIndexMap A T q p := by
  dsimp [stageComponentIndexMap]
  show (connectedComponentsDiscreteHomeo q).symm
    (ConnectedComponents.mk (stageSpectrumIndexMap A T q p)) = _
  exact (connectedComponentsDiscreteHomeo q).symm_apply_apply _

private lemma stageComponentBaseMap_mk
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (p : PrimeSpectrum (q → A)) :
    stageComponentBaseMap A T q (ConnectedComponents.mk p) =
      ConnectedComponents.mk (stageSpectrumBaseMap A T q p) := by
  simp [stageComponentBaseMap, Continuous.connectedComponentsMap_mk]

private lemma stageComponentIndexMap_map
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) (t : T) :
    stageComponentIndexMap A T q (stageComponentsMap A T q f t) = q.proj t := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (f t)
  rw [stageComponentsMap_mk A T q f t p hp.symm, stageComponentIndexMap_mk]
  exact stageSpectrumIndexMap_sigmaToPi A T q _ _

private lemma stageComponentBaseMap_map
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) (t : T) :
    stageComponentBaseMap A T q (stageComponentsMap A T q f t) = f t := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (f t)
  rw [stageComponentsMap_mk A T q f t p hp.symm, stageComponentBaseMap_mk,
    stageSpectrumBaseMap_sigmaToPi, hp]

private lemma stageComponentsMap_natural
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) (t : T) :
    (PrimeSpectrum.continuous_comap (stageRestrictRingHom A T q q' h)).connectedComponentsMap
      (stageComponentsMap A T q f t) = stageComponentsMap A T q' f t := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (f t)
  rw [stageComponentsMap_mk A T q f t p hp.symm,
    stageComponentsMap_mk A T q' f t p hp.symm]
  apply congrArg ConnectedComponents.mk
  apply PrimeSpectrum.ext
  ext a
  simp [PrimeSpectrum.sigmaToPi_apply, stageRestrictRingHom,
    DiscreteQuotient.ofLE_proj]

private lemma isClosed_range_stageComponentsMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsClosed (Set.range (stageComponentsMap A T q f)) := by
  let : SpectralSpace (PrimeSpectrum (q → A)) := inferInstance
  let : T2Space (ConnectedComponents (PrimeSpectrum (q → A))) :=
    (connectedComponents_isProfinite (PrimeSpectrum (q → A))).1
  exact (isCompact_range (stageComponentsMap A T q f).continuous).isClosed

private structure ProfiniteStage
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) where
  B : Type (max u v)
  [commRingB : CommRing B]
  [algebraB : Algebra (q → A) B]
  isIndZariski : IsIndZariski.{max u v, max u v, max u v} (q → A) B
  surjective : Function.Surjective (algebraMap (q → A) B)
  isEmbedding : IsEmbedding (PrimeSpectrum.comap (algebraMap (q → A) B))
  range : Set.range (PrimeSpectrum.comap (algebraMap (q → A) B)) =
    ConnectedComponents.mk ⁻¹' Set.range (stageComponentsMap A T q f)

private lemma exists_profiniteStage
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Nonempty (ProfiniteStage A T q f) := by
  obtain ⟨B, hB, hAlg, hInd, hsurj, hemb, hrange⟩ :=
    exists_surjective_indZariski_range_comap_eq_preimage_components
      (q → A) (Set.range (stageComponentsMap A T q f))
      (isClosed_range_stageComponentsMap A T q f)
  let : CommRing B := hB
  let : Algebra (q → A) B := hAlg
  exact ⟨⟨B, hInd, hsurj, hemb, hrange⟩⟩

private noncomputable def chosenProfiniteStage
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) : ProfiniteStage A T q f :=
  Classical.choice (exists_profiniteStage A T q f)

@[instance_reducible] private noncomputable def chosenStageCommRing
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    CommRing (chosenProfiniteStage A T q f).B :=
  (chosenProfiniteStage A T q f).commRingB

attribute [local instance] chosenStageCommRing

@[instance_reducible] private noncomputable def chosenStageAlgebra
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Algebra (q → A) (chosenProfiniteStage A T q f).B :=
  (chosenProfiniteStage A T q f).algebraB

attribute [local instance] chosenStageAlgebra

@[instance_reducible] private noncomputable def chosenStageAlgebraOverA
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Algebra A (chosenProfiniteStage A T q f).B :=
  Algebra.compHom (chosenProfiniteStage A T q f).B (algebraMap A (q → A))

attribute [local instance] chosenStageAlgebraOverA

@[instance_reducible] private noncomputable def chosenStageAlgebraOverLiftA
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Algebra (ULift.{max u v} A) (chosenProfiniteStage A T q f).B :=
  Algebra.compHom (chosenProfiniteStage A T q f).B
    (ULift.ringEquiv (R := A)).toRingHom

attribute [local instance] chosenStageAlgebraOverLiftA

@[instance_reducible] private noncomputable def baseAlgebraOfLift
    (A : Type u) [CommRing A] : Algebra (ULift.{max u v} A) A :=
  (ULift.ringEquiv (R := A)).toRingHom.toAlgebra

attribute [local instance] baseAlgebraOfLift

private theorem chosenStageScalarTower
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsScalarTower A (q → A) (chosenProfiniteStage A T q f).B :=
  .of_algebraMap_eq' (by ext x; rfl)

attribute [local instance] chosenStageScalarTower

private lemma chosenStage_isIndZariski_over_A
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsIndZariski.{u, max u v, max u v} A
      (chosenProfiniteStage A T q f).B := by
  have : Algebra.IsLocalIso A (q → A) := Algebra.IsLocalIso.pi_of_finite A (fun _ : q => A)
  have hBaseInd : IsIndZariski.{u, max u v, max u v} A (q → A) :=
    isIndZariski_of_isLocalIso A _
  exact Algebra.IsIndZariski.comp A (q → A) _ hBaseInd (chosenProfiniteStage A T q f).isIndZariski

@[instance_reducible] private noncomputable def chosenStageRestrictAlgebra
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Algebra (q' → A) (chosenProfiniteStage A T q f).B :=
  Algebra.compHom (chosenProfiniteStage A T q f).B
    (stageRestrictRingHom A T q q' h)

private def stageAlgHomRingHom
    (R B C : Type w) [CommSemiring R] [Semiring B] [Semiring C]
    (hB : Algebra R B) (hC : Algebra R C)
    (φ : @AlgHom R B C inferInstance inferInstance inferInstance hB hC) : B →+* C :=
  @AlgHom.toRingHom R B C inferInstance inferInstance inferInstance hB hC φ

private structure StageTransitionPackage
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) where
  homOverStage : @AlgHom (q' → A)
    (chosenProfiniteStage A T q' f).B (chosenProfiniteStage A T q f).B
    inferInstance inferInstance inferInstance
    (chosenStageAlgebra A T q' f) (chosenStageRestrictAlgebra A T q q' h f)
  hom : (chosenProfiniteStage A T q' f).B →ₐ[A]
    (chosenProfiniteStage A T q f).B
  specMap : C(PrimeSpectrum (chosenProfiniteStage A T q f).B,
    PrimeSpectrum (chosenProfiniteStage A T q' f).B)
  specMap_eq : AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
      (stageAlgHomRingHom (q' → A) (chosenProfiniteStage A T q' f).B
        (chosenProfiniteStage A T q f).B (chosenStageAlgebra A T q' f)
        (chosenStageRestrictAlgebra A T q q' h f) homOverStage)) = TopCat.ofHom specMap
  specMap_eq_overA : AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom hom.toRingHom) = TopCat.ofHom specMap
  spec_compat (p : PrimeSpectrum (chosenProfiniteStage A T q f).B) :
    PrimeSpectrum.comap
        (algebraMap (q' → A) (chosenProfiniteStage A T q' f).B) (specMap p) =
      PrimeSpectrum.comap (stageRestrictRingHom A T q q' h)
        (PrimeSpectrum.comap
          (algebraMap (q → A) (chosenProfiniteStage A T q f).B) p)

private noncomputable def chosenStageTransitionPackage
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    StageTransitionPackage A T q q' h f := by
  classical
  let S := chosenProfiniteStage A T q f
  let S' := chosenProfiniteStage A T q' f
  let r := stageRestrictRingHom A T q q' h
  let e : PrimeSpectrum S.B → PrimeSpectrum (q → A) :=
    PrimeSpectrum.comap (algebraMap (q → A) S.B)
  let e' : PrimeSpectrum S'.B → PrimeSpectrum (q' → A) :=
    PrimeSpectrum.comap (algebraMap (q' → A) S'.B)
  letI : Algebra (q' → A) S.B := Algebra.compHom S.B r
  letI : IsScalarTower A (q' → A) S.B := .of_algebraMap_eq' (by ext x; rfl)
  have he : IsEmbedding e := S.isEmbedding
  have he' : IsEmbedding e' := S'.isEmbedding
  have hrange : Set.range (fun p : PrimeSpectrum S.B => PrimeSpectrum.comap r (e p)) ⊆
      Set.range e' := by
    rintro z ⟨p, rfl⟩
    rw [S'.range]
    apply Set.mem_preimage.mpr
    obtain ⟨t, ht⟩ : ∃ t, ConnectedComponents.mk (e p) =
        stageComponentsMap A T q f t := by
      have hp : e p ∈ Set.range e := Set.mem_range_self _
      rw [S.range] at hp
      obtain ⟨t, ht⟩ := (by simpa only [Set.mem_preimage, Set.mem_range] using hp)
      exact ⟨t, ht.symm⟩
    refine ⟨t, ?_⟩
    have hn := stageComponentsMap_natural A T q q' h f t
    rw [← ht] at hn
    exact hn.symm
  let z : C(PrimeSpectrum S.B, PrimeSpectrum (q' → A)) :=
    ⟨fun p => PrimeSpectrum.comap r (e p),
      (PrimeSpectrum.continuous_comap r).comp (PrimeSpectrum.continuous_comap _)⟩
  let hi := he'.homeomorphOfSubsetRange hrange
  let gfun : PrimeSpectrum S.B → PrimeSpectrum S'.B :=
    fun p => (hi.symm ⟨z p, ⟨p, rfl⟩⟩).val
  have hgcomp : e' ∘ gfun = z := by
    funext p
    exact congrArg Subtype.val (hi.apply_symm_apply ⟨z p, ⟨p, rfl⟩⟩)
  have hcompat (p : PrimeSpectrum S.B) :
      e' (gfun p) = PrimeSpectrum.comap r (e p) :=
    congrArg Subtype.val (hi.apply_symm_apply ⟨z p, ⟨p, rfl⟩⟩)
  have hgcont : Continuous gfun := by
    apply he'.toIsInducing.continuous_iff.mpr
    simpa [hgcomp] using z.continuous
  let g : AlgebraicGeometry.Spec.topObj (CommRingCat.of S.B) ⟶
      AlgebraicGeometry.Spec.topObj (CommRingCat.of S'.B) :=
    TopCat.ofHom ⟨gfun, hgcont⟩
  have hcomm : g ≫ AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom (algebraMap (q' → A) S'.B)) =
      AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom (algebraMap (q' → A) S.B)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply PrimeSpectrum.ext
    change (e' (gfun p)).asIdeal =
      (PrimeSpectrum.comap (algebraMap (q' → A) S.B) p).asIdeal
    rw [hcompat p]
    apply Ideal.ext
    intro a
    change algebraMap (q → A) S.B (r a) ∈ p.asIdeal ↔
      algebraMap (q' → A) S.B a ∈ p.asIdeal
    rfl
  have hLoc : Algebra.IdentifiesLocalRings (q' → A) S'.B :=
    identifiesLocalRings_of_isIndZariski (q' → A) S'.B S'.isIndZariski
  let hUnique := existsUnique_algHom_of_specTopMap_over
    (q' → A) S'.B S.B hLoc g hcomm
  let φ := Classical.choose hUnique
  have hφ : AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom φ.toRingHom) = g :=
    (Classical.choose_spec hUnique).1
  have hφA : AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom (φ.restrictScalars A).toRingHom) = g := by
    simpa using hφ
  exact ⟨φ, φ.restrictScalars A, ⟨gfun, hgcont⟩, hφ, hφA, hcompat⟩

private noncomputable def chosenStageTransition
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    (chosenProfiniteStage A T q' f).B →ₐ[A] (chosenProfiniteStage A T q f).B :=
  (chosenStageTransitionPackage A T q q' h f).hom

private noncomputable def stageProductSpectrumPoint
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (i : q)
    (p : PrimeSpectrum A) : PrimeSpectrum (q → A) := by
  letI : Finite q := inferInstance
  exact PrimeSpectrum.sigmaToPi (fun _ : q => A) ⟨i, p⟩

private lemma stageProductSpectrumPoint_index
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (i : q)
    (p : PrimeSpectrum A) :
    stageSpectrumIndexMap A T q (stageProductSpectrumPoint A T q i p) = i :=
  stageSpectrumIndexMap_sigmaToPi A T q i p

private lemma stageProductSpectrumPoint_basePrime
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (i : q)
    (p : PrimeSpectrum A) :
    stageSpectrumBaseMap A T q (stageProductSpectrumPoint A T q i p) = p :=
  stageSpectrumBaseMap_sigmaToPi A T q i p

private lemma stageSpectrum_eq_productPoint
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T) (z : PrimeSpectrum (q → A)) :
    z = stageProductSpectrumPoint A T q (stageSpectrumIndexMap A T q z)
      (stageSpectrumBaseMap A T q z) := by
  let : Finite q := inferInstance
  let e := PrimeSpectrum.sigmaToPiHomeo (fun _ : q => A)
  calc
    z = e (e.symm z) := (e.apply_symm_apply z).symm
    _ = e ⟨(e.symm z).1, (e.symm z).2⟩ := rfl
    _ = stageProductSpectrumPoint A T q (stageSpectrumIndexMap A T q z)
        (stageSpectrumBaseMap A T q z) := by
          rw [PrimeSpectrum.sigmaToPiHomeo_apply]
          rfl

private lemma comap_stageRestrictRingHom_productPoint
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q') (i : q) (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (stageRestrictRingHom A T q q' h) (stageProductSpectrumPoint A T q i p) =
      stageProductSpectrumPoint A T q' (DiscreteQuotient.ofLE h i) p := by
  apply PrimeSpectrum.ext
  ext a
  simp [stageProductSpectrumPoint, stageRestrictRingHom, PrimeSpectrum.sigmaToPi_apply]

private lemma stageSpectrumIndexMap_restrict
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (z : PrimeSpectrum (q → A)) :
    stageSpectrumIndexMap A T q'
      (PrimeSpectrum.comap (stageRestrictRingHom A T q q' h) z) =
        DiscreteQuotient.ofLE h (stageSpectrumIndexMap A T q z) := by
  rw [stageSpectrum_eq_productPoint A T q z, comap_stageRestrictRingHom_productPoint,
    stageProductSpectrumPoint_index, stageProductSpectrumPoint_index]

private lemma stageSpectrumBaseMap_restrict
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (z : PrimeSpectrum (q → A)) :
    stageSpectrumBaseMap A T q'
      (PrimeSpectrum.comap (stageRestrictRingHom A T q q' h) z) =
        stageSpectrumBaseMap A T q z := by
  rw [stageSpectrum_eq_productPoint A T q z, comap_stageRestrictRingHom_productPoint,
    stageProductSpectrumPoint_basePrime, stageProductSpectrumPoint_basePrime]

private abbrev ComponentPullback
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :=
  {z : PrimeSpectrum A × T // ConnectedComponents.mk z.1 = f z.2}

private noncomputable def componentPullbackStageAmbient
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    C(ComponentPullback A T f, PrimeSpectrum (q → A)) := by
  letI : Finite q := inferInstance
  let pairMap : C(ComponentPullback A T f, q × PrimeSpectrum A) :=
    ⟨fun z => (q.proj z.val.2, z.val.1),
      (q.proj_continuous.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        (continuous_fst.comp continuous_subtype_val)⟩
  let sigmaMap : C(q × PrimeSpectrum A, Σ _ : q, PrimeSpectrum A) :=
    ⟨fun z => ⟨z.1, z.2⟩, continuous_prodToSigma q (PrimeSpectrum A)⟩
  let e := PrimeSpectrum.sigmaToPiHomeo (fun _ : q => A)
  exact ⟨fun z => e (sigmaMap (pairMap z)),
    e.continuous_toFun.comp (sigmaMap.continuous.comp pairMap.continuous)⟩

private lemma componentPullbackStageAmbient_eq
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    componentPullbackStageAmbient A T q f z =
      stageProductSpectrumPoint A T q (q.proj z.val.2) z.val.1 := by
  let : Finite q := inferInstance
  show (PrimeSpectrum.sigmaToPiHomeo (fun _ : q => A))
    ⟨q.proj z.val.2, z.val.1⟩ = PrimeSpectrum.sigmaToPi (fun _ : q => A)
      ⟨q.proj z.val.2, z.val.1⟩
  exact PrimeSpectrum.sigmaToPiHomeo_apply _

private lemma componentPullbackStageAmbient_mem_range
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    componentPullbackStageAmbient A T q f z ∈
      Set.range (PrimeSpectrum.comap
        (algebraMap (q → A) (chosenProfiniteStage A T q f).B)) := by
  rw [(chosenProfiniteStage A T q f).range]
  refine ⟨z.val.2, ?_⟩
  rw [stageComponentsMap_mk A T q f z.val.2 z.val.1 z.property.symm]
  rw [componentPullbackStageAmbient_eq, stageProductSpectrumPoint]

/-- The stage spectrum as a homeomorphic copy of its image in the spectrum of `q → A`. -/
private noncomputable def chosenStageRangeHomeo
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    PrimeSpectrum (chosenProfiniteStage A T q f).B ≃ₜ
      Set.range (PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B)) :=
  (chosenProfiniteStage A T q f).isEmbedding.toHomeomorph

private noncomputable def componentPullbackStageMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    C(ComponentPullback A T f,
      PrimeSpectrum (chosenProfiniteStage A T q f).B) := by
  let e := chosenStageRangeHomeo A T q f
  exact ⟨fun z => e.symm ⟨componentPullbackStageAmbient A T q f z,
      componentPullbackStageAmbient_mem_range A T q f z⟩,
    e.symm.continuous.comp (Continuous.subtype_mk
      (componentPullbackStageAmbient A T q f).continuous
      (componentPullbackStageAmbient_mem_range A T q f))⟩

private lemma componentPullbackStageMap_comap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B)
      (componentPullbackStageMap A T q f z) =
        componentPullbackStageAmbient A T q f z := by
  let e := chosenStageRangeHomeo A T q f
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨componentPullbackStageAmbient A T q f z,
      componentPullbackStageAmbient_mem_range A T q f z⟩)

private noncomputable def chosenStagePointIndex
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    C(PrimeSpectrum (chosenProfiniteStage A T q f).B, q) := by
  letI : Finite q := inferInstance
  exact (stageSpectrumIndexMap A T q).comp
    ⟨PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B),
      PrimeSpectrum.continuous_comap _⟩

private noncomputable def chosenStagePointBase
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    C(PrimeSpectrum (chosenProfiniteStage A T q f).B, PrimeSpectrum A) :=
  (stageSpectrumBaseMap A T q).comp
    ⟨PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B),
      PrimeSpectrum.continuous_comap _⟩

private lemma chosenStagePointIndex_pullback
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    chosenStagePointIndex A T q f (componentPullbackStageMap A T q f z) = q.proj z.val.2 := by
  show stageSpectrumIndexMap A T q
    (PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B)
      (componentPullbackStageMap A T q f z)) = _
  rw [componentPullbackStageMap_comap, componentPullbackStageAmbient_eq]
  exact stageProductSpectrumPoint_index A T q _ _

private lemma chosenStagePointBase_pullback
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    chosenStagePointBase A T q f (componentPullbackStageMap A T q f z) = z.val.1 := by
  show stageSpectrumBaseMap A T q
    (PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B)
      (componentPullbackStageMap A T q f z)) = z.val.1
  rw [componentPullbackStageMap_comap, componentPullbackStageAmbient_eq]
  exact stageProductSpectrumPoint_basePrime A T q _ _

private lemma componentPullbackStageMap_natural
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    (chosenStageTransitionPackage A T q q' h f).specMap
      (componentPullbackStageMap A T q f z) = componentPullbackStageMap A T q' f z := by
  let P := chosenStageTransitionPackage A T q q' h f
  have hres : PrimeSpectrum.comap (stageRestrictRingHom A T q q' h)
      (componentPullbackStageAmbient A T q f z) =
        componentPullbackStageAmbient A T q' f z := by
    rw [componentPullbackStageAmbient_eq, componentPullbackStageAmbient_eq,
      comap_stageRestrictRingHom_productPoint, DiscreteQuotient.ofLE_proj]
  apply (chosenProfiniteStage A T q' f).isEmbedding.injective
  calc
    PrimeSpectrum.comap (algebraMap (q' → A) (chosenProfiniteStage A T q' f).B)
        (P.specMap (componentPullbackStageMap A T q f z)) =
        PrimeSpectrum.comap (stageRestrictRingHom A T q q' h)
          (PrimeSpectrum.comap
            (algebraMap (q → A) (chosenProfiniteStage A T q f).B)
            (componentPullbackStageMap A T q f z)) := P.spec_compat _
    _ = componentPullbackStageAmbient A T q' f z := by
      rw [componentPullbackStageMap_comap, hres]
    _ = PrimeSpectrum.comap (algebraMap (q' → A) (chosenProfiniteStage A T q' f).B)
        (componentPullbackStageMap A T q' f z) :=
        (componentPullbackStageMap_comap A T q' f z).symm

private lemma chosenStagePointIndex_natural
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (p : PrimeSpectrum (chosenProfiniteStage A T q f).B) :
    DiscreteQuotient.ofLE h (chosenStagePointIndex A T q f p) =
      chosenStagePointIndex A T q' f
        ((chosenStageTransitionPackage A T q q' h f).specMap p) := by
  show DiscreteQuotient.ofLE h
      (stageSpectrumIndexMap A T q
        (PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B) p)) =
    stageSpectrumIndexMap A T q'
      (PrimeSpectrum.comap (algebraMap (q' → A) (chosenProfiniteStage A T q' f).B)
        ((chosenStageTransitionPackage A T q q' h f).specMap p))
  rw [(chosenStageTransitionPackage A T q q' h f).spec_compat p]
  exact (stageSpectrumIndexMap_restrict A T q q' h _).symm

private lemma chosenStagePointBase_natural
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (p : PrimeSpectrum (chosenProfiniteStage A T q f).B) :
    chosenStagePointBase A T q' f
        ((chosenStageTransitionPackage A T q q' h f).specMap p) =
      chosenStagePointBase A T q f p := by
  show stageSpectrumBaseMap A T q'
      (PrimeSpectrum.comap (algebraMap (q' → A) (chosenProfiniteStage A T q' f).B)
        ((chosenStageTransitionPackage A T q q' h f).specMap p)) =
    stageSpectrumBaseMap A T q
      (PrimeSpectrum.comap (algebraMap (q → A) (chosenProfiniteStage A T q f).B) p)
  rw [(chosenStageTransitionPackage A T q q' h f).spec_compat p]
  exact stageSpectrumBaseMap_restrict A T q q' h _

private lemma stageAlgHom_unique_of_specTopMap_eq
    (R B C : Type w) [CommRing R] [CommRing B] [CommRing C]
    (algB : Algebra R B) (algC : Algebra R C)
    (hB : @Algebra.IdentifiesLocalRings R B _ _ algB)
    (φ ψ : @AlgHom R B C _ _ _ algB algC)
    (h : AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
        (stageAlgHomRingHom R B C algB algC φ)) =
      AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
        (stageAlgHomRingHom R B C algB algC ψ))) : φ = ψ := by
  let : Algebra R B := algB
  let : Algebra R C := algC
  let g := AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
    (stageAlgHomRingHom R B C algB algC ψ))
  have hcompat : g ≫ AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom (algebraMap R B)) =
      AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom (algebraMap R C)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    show PrimeSpectrum.comap (algebraMap R B)
        (PrimeSpectrum.comap (stageAlgHomRingHom R B C algB algC ψ) p) =
      PrimeSpectrum.comap (algebraMap R C) p
    have hcomp : RingHom.comp (stageAlgHomRingHom R B C algB algC ψ)
        (algebraMap R B) = algebraMap R C := by
      ext r
      exact ψ.commutes r
    have hcomap := congrFun
      (PrimeSpectrum.comap_comp (algebraMap R B)
        (stageAlgHomRingHom R B C algB algC ψ)) p
    calc
      PrimeSpectrum.comap (algebraMap R B)
          (PrimeSpectrum.comap (stageAlgHomRingHom R B C algB algC ψ) p) =
          PrimeSpectrum.comap (RingHom.comp
            (stageAlgHomRingHom R B C algB algC ψ) (algebraMap R B)) p := hcomap.symm
      _ = PrimeSpectrum.comap (algebraMap R C) p := by rw [hcomp]
  have hex := existsUnique_algHom_of_specTopMap_over R B C hB g hcompat
  exact ExistsUnique.unique hex h rfl

private noncomputable def chosenStageIdentityHom
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    @AlgHom (q → A) (chosenProfiniteStage A T q f).B
      (chosenProfiniteStage A T q f).B inferInstance inferInstance inferInstance
      (chosenStageAlgebra A T q f) (chosenStageRestrictAlgebra A T q q (le_rfl) f) := by
  classical
  let S := chosenProfiniteStage A T q f
  let r := stageRestrictRingHom A T q q le_rfl
  have hr : r = RingHom.id (q → A) := by
    ext x t
    simp [r, stageRestrictRingHom]
  refine @AlgHom.mk (q → A) S.B S.B inferInstance inferInstance inferInstance
    (chosenStageAlgebra A T q f) (chosenStageRestrictAlgebra A T q q le_rfl f)
    (RingHom.id S.B) ?_
  intro a
  change (RingHom.id S.B) (algebraMap (q → A) S.B a) =
    algebraMap (q → A) S.B (r a)
  rw [hr]
  rfl

private lemma chosenStageTransitionPackage_id
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    (chosenStageTransitionPackage A T q q (le_rfl) f).homOverStage =
      chosenStageIdentityHom A T q f := by
  classical
  let P := chosenStageTransitionPackage A T q q (le_rfl) f
  let S := chosenProfiniteStage A T q f
  let I := chosenStageIdentityHom A T q f
  have hr : stageRestrictRingHom A T q q (le_rfl) = RingHom.id (q → A) := by
    ext x t
    simp [stageRestrictRingHom]
  have hs (p : PrimeSpectrum S.B) : P.specMap p = p := by
    apply S.isEmbedding.injective
    calc
      PrimeSpectrum.comap (algebraMap (q → A) S.B) (P.specMap p) =
          PrimeSpectrum.comap (stageRestrictRingHom A T q q le_rfl)
            (PrimeSpectrum.comap (algebraMap (q → A) S.B) p) := by
              simpa [chosenStageRestrictAlgebra] using P.spec_compat p
      _ = PrimeSpectrum.comap (algebraMap (q → A) S.B) p := by rw [hr]; simp
  have hspecP : AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom (stageAlgHomRingHom (q → A) S.B S.B
        (chosenStageAlgebra A T q f) (chosenStageRestrictAlgebra A T q q le_rfl f)
        P.homOverStage)) = TopCat.ofHom P.specMap :=
    P.specMap_eq
  have hspecI : AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
      (stageAlgHomRingHom (q → A) S.B S.B (chosenStageAlgebra A T q f)
        (chosenStageRestrictAlgebra A T q q le_rfl f) I)) =
      TopCat.ofHom (ContinuousMap.id (PrimeSpectrum S.B)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rfl
  have hspec : AlgebraicGeometry.Spec.topMap
      (CommRingCat.ofHom (stageAlgHomRingHom (q → A) S.B S.B
        (chosenStageAlgebra A T q f) (chosenStageRestrictAlgebra A T q q le_rfl f)
        P.homOverStage)) =
      AlgebraicGeometry.Spec.topMap (CommRingCat.ofHom
        (stageAlgHomRingHom (q → A) S.B S.B (chosenStageAlgebra A T q f)
          (chosenStageRestrictAlgebra A T q q le_rfl f) I)) := by
    have hmap : P.specMap = ContinuousMap.id (PrimeSpectrum S.B) :=
      ContinuousMap.ext hs
    exact hspecP.trans ((congrArg TopCat.ofHom hmap).trans hspecI.symm)
  have hLoc : Algebra.IdentifiesLocalRings (q → A) S.B :=
    identifiesLocalRings_of_isIndZariski (q → A) S.B S.isIndZariski
  exact stageAlgHom_unique_of_specTopMap_eq (q → A) S.B S.B
    (chosenStageAlgebra A T q f)
    (chosenStageRestrictAlgebra A T q q le_rfl f) hLoc
    P.homOverStage I hspec

private lemma chosenStageTransition_id
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    chosenStageTransition A T q q le_rfl f =
      AlgHom.id A (chosenProfiniteStage A T q f).B := by
  apply AlgHom.ext
  intro x
  show (chosenStageTransitionPackage A T q q le_rfl f).hom x = x
  have h := congrArg (fun φ : @AlgHom (q → A)
      (chosenProfiniteStage A T q f).B (chosenProfiniteStage A T q f).B
      inferInstance inferInstance inferInstance (chosenStageAlgebra A T q f)
      (chosenStageRestrictAlgebra A T q q le_rfl f) => φ x)
      (chosenStageTransitionPackage_id A T q f)
  unfold chosenStageTransitionPackage at h ⊢
  exact h

private lemma chosenStageTransition_comp
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q₀ q₁ q₂ : DiscreteQuotient T)
    (h₀₁ : q₀ ≤ q₁) (h₁₂ : q₁ ≤ q₂)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    (chosenStageTransition A T q₀ q₁ h₀₁ f).comp
        (chosenStageTransition A T q₁ q₂ h₁₂ f) =
      chosenStageTransition A T q₀ q₂ (le_trans h₀₁ h₁₂) f := by
  classical
  let B₀ := (chosenProfiniteStage A T q₀ f).B
  let B₁ := (chosenProfiniteStage A T q₁ f).B
  let B₂ := (chosenProfiniteStage A T q₂ f).B
  let : Algebra (q₁ → A) B₀ := chosenStageRestrictAlgebra A T q₀ q₁ h₀₁ f
  let : Algebra (q₂ → A) B₁ := chosenStageRestrictAlgebra A T q₁ q₂ h₁₂ f
  let : Algebra (q₂ → A) B₀ := chosenStageRestrictAlgebra A T q₀ q₂ (le_trans h₀₁ h₁₂) f
  let r₁₂ := stageRestrictRingHom A T q₁ q₂ h₁₂
  let r₀₁ := stageRestrictRingHom A T q₀ q₁ h₀₁
  let r₀₂ := stageRestrictRingHom A T q₀ q₂ (le_trans h₀₁ h₁₂)
  let : Algebra (q₂ → A) (q₁ → A) := RingHom.toAlgebra r₁₂
  have hr : RingHom.comp r₀₁ r₁₂ = r₀₂ := by
    ext x t
    simp [r₀₁, r₁₂, r₀₂, stageRestrictRingHom]
  have hbase₁ : algebraMap (q₂ → A) B₁ =
      (algebraMap (q₁ → A) B₁).comp (algebraMap (q₂ → A) (q₁ → A)) := by
    show (algebraMap (q₁ → A) B₁).comp r₁₂ =
      (algebraMap (q₁ → A) B₁).comp r₁₂
    rfl
  have hbase₀ : algebraMap (q₂ → A) B₀ =
      (algebraMap (q₁ → A) B₀).comp (algebraMap (q₂ → A) (q₁ → A)) := by
    show (algebraMap (q₀ → A) B₀).comp r₀₂ =
      ((algebraMap (q₀ → A) B₀).comp r₀₁).comp r₁₂
    rw [RingHom.comp_assoc, hr]
  let : IsScalarTower (q₂ → A) (q₁ → A) B₁ := .of_algebraMap_eq' hbase₁
  let : IsScalarTower (q₂ → A) (q₁ → A) B₀ := .of_algebraMap_eq' hbase₀
  let P₀₁ := chosenStageTransitionPackage A T q₀ q₁ h₀₁ f
  let P₁₂ := chosenStageTransitionPackage A T q₁ q₂ h₁₂ f
  let P₀₂ := chosenStageTransitionPackage A T q₀ q₂ (le_trans h₀₁ h₁₂) f
  let φ₀₁ := P₀₁.homOverStage.restrictScalars (q₂ → A)
  let φ₁₂ := P₁₂.homOverStage
  let φ₀₂ := P₀₂.homOverStage
  have hLoc : Algebra.IdentifiesLocalRings (q₂ → A) B₂ :=
    identifiesLocalRings_of_isIndZariski (q₂ → A) B₂
      (chosenProfiniteStage A T q₂ f).isIndZariski
  have hcomp : φ₀₁.comp φ₁₂ = φ₀₂ := by
    apply stageAlgHom_unique_of_specTopMap_eq (q₂ → A) B₂ B₀
      inferInstance inferInstance hLoc (φ₀₁.comp φ₁₂) φ₀₂
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    let p' : PrimeSpectrum B₀ := p
    apply (chosenProfiniteStage A T q₂ f).isEmbedding.injective
    apply PrimeSpectrum.ext
    ext a
    show a ∈ (PrimeSpectrum.comap (algebraMap (q₂ → A) B₂)
        (PrimeSpectrum.comap (stageAlgHomRingHom (q₂ → A) B₂ B₀
          inferInstance inferInstance (φ₀₁.comp φ₁₂)) p')).asIdeal ↔
      a ∈ (PrimeSpectrum.comap (algebraMap (q₂ → A) B₂)
        (PrimeSpectrum.comap (stageAlgHomRingHom (q₂ → A) B₂ B₀
          inferInstance inferInstance φ₀₂) p')).asIdeal
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    show (φ₀₁.comp φ₁₂) (algebraMap (q₂ → A) B₂ a) ∈ p'.asIdeal ↔
      φ₀₂ (algebraMap (q₂ → A) B₂ a) ∈ p'.asIdeal
    rw [(φ₀₁.comp φ₁₂).commutes a, φ₀₂.commutes a]
  apply AlgHom.ext
  intro x
  have h := congrArg (fun ψ => ψ x) hcomp
  show P₀₁.homOverStage (P₁₂.homOverStage x) = P₀₂.homOverStage x
  exact h

private noncomputable def chosenStageSchemeDiagram
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    DiscreteQuotient T ⥤ Scheme.{max u v} where
  obj q := Spec
    (CommRingCat.of (chosenProfiniteStage A T q f).B)
  map {q q'} h := Spec.map
    (CommRingCat.ofHom (chosenStageTransition A T q q' h.le f).toRingHom)
  map_id q := by
    simp [chosenStageTransition_id]
  map_comp {q₀ q₁ q₂} h₀₁ h₁₂ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map <| congrArg CommRingCat.ofHom <|
      congrArg AlgHom.toRingHom
        (chosenStageTransition_comp A T q₀ q₁ q₂ h₀₁.le h₁₂.le f).symm

private theorem chosenStageSchemeDiagram_isAffine
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (q : DiscreteQuotient T) :
    IsAffine ((chosenStageSchemeDiagram A T f).obj q) := by
  show IsAffine (Spec (CommRingCat.of (chosenProfiniteStage A T q f).B))
  infer_instance

attribute [local instance] chosenStageSchemeDiagram_isAffine

private theorem algebraIsLocalIso_finitePresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsLocalIso R S) : Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_span_eq_top_target
    {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S)
  intro g hg
  have hstd : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
  obtain ⟨r, hr⟩ := hstd.exists_away
  let : IsLocalization.Away r (Localization.Away g) := hr
  let : Algebra.FinitePresentation R (Localization.Away r) :=
    IsLocalization.Away.finitePresentation r
  exact Algebra.FinitePresentation.equiv
    (IsLocalization.algEquiv (Submonoid.powers r)
      (Localization.Away r) (Localization.Away g))

private noncomputable def chosenStageAlgDiagram
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    (DiscreteQuotient T)ᵒᵖ ⥤ CommAlgCat.{max u v} (ULift.{max u v} A) where
  obj q :=
    CommAlgCat.of (ULift.{max u v} A)
      (chosenProfiniteStage A T q.unop f).B
  map {q q'} h := by
    let hle : q'.unop ≤ q.unop := h.unop.le
    let B := (chosenProfiniteStage A T q.unop f).B
    let C := (chosenProfiniteStage A T q'.unop f).B
    letI : CommRing B := (chosenProfiniteStage A T q.unop f).commRingB
    letI : CommRing C := (chosenProfiniteStage A T q'.unop f).commRingB
    letI : Algebra A B := chosenStageAlgebraOverA A T q.unop f
    letI : Algebra A C := chosenStageAlgebraOverA A T q'.unop f
    let φ := chosenStageTransition A T q'.unop q.unop hle f
    exact CommAlgCat.ofHom {
      toRingHom := φ.toRingHom
      commutes' := fun x => by
        change φ (algebraMap A B x.down) = algebraMap A C x.down
        exact φ.commutes x.down }
  map_id q := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change chosenStageTransition A T q.unop q.unop le_rfl f x = x
    exact congrArg (fun φ => φ x) (chosenStageTransition_id A T q.unop f)
  map_comp {q q' q''} h₁ h₂ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change chosenStageTransition A T q''.unop q.unop
        (le_trans h₂.unop.le h₁.unop.le) f x =
      chosenStageTransition A T q''.unop q'.unop h₂.unop.le f
        (chosenStageTransition A T q'.unop q.unop h₁.unop.le f x)
    exact congrArg (fun φ => φ x)
      (chosenStageTransition_comp A T q''.unop q'.unop q.unop
        h₂.unop.le h₁.unop.le f).symm

@[instance_reducible] private def liftedStageIndexCategory
    (T : Type v) [TopologicalSpace T] [CompactSpace T] :
    Category.{v, max u v} (ULift.{max u v} ((DiscreteQuotient T)ᵒᵖ)) :=
  CategoryTheory.uliftCategory ((DiscreteQuotient T)ᵒᵖ)

attribute [local instance] liftedStageIndexCategory

private noncomputable def chosenStageAlgDiagramLift
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    CategoryTheory.ULiftHom.{max u v}
        (ULift.{max u v} ((DiscreteQuotient T)ᵒᵖ)) ⥤
      CommAlgCat.{max u v} (ULift.{max u v} A) := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  letI : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  exact CategoryTheory.ULiftHom.down ⋙ CategoryTheory.ULift.downFunctor ⋙
    chosenStageAlgDiagram A T f

private noncomputable def chosenStageIndexEquiv
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] :
    DiscreteQuotient T ≌
      (CategoryTheory.ULiftHom.{max u v}
        (ULift.{max u v} ((DiscreteQuotient T)ᵒᵖ)))ᵒᵖ := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  letI : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  let e : J ≌ J' :=
    CategoryTheory.ULiftHomULiftCategory.equiv.{max u v, max u v, v, v} J
  exact (CategoryTheory.opOpEquivalence (DiscreteQuotient T)).symm.trans e.op

private noncomputable def chosenStageSchemeDiagramLift
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    (CategoryTheory.ULiftHom.{max u v}
        (ULift.{max u v} ((DiscreteQuotient T)ᵒᵖ)))ᵒᵖ ⥤ Scheme.{max u v} :=
  (chosenStageAlgDiagramLift A T f ⋙
    (forget₂ (CommAlgCat.{max u v} (ULift.{max u v} A)) CommRingCat)).op ⋙
      Scheme.Spec

private lemma chosenStageSchemeDiagram_eq_lift
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    chosenStageSchemeDiagram A T f =
      (chosenStageIndexEquiv A T).functor ⋙ chosenStageSchemeDiagramLift A T f :=
  CategoryTheory.Functor.ext (fun q => rfl) (fun q q' h => rfl)

attribute [local instance] Cardinal.fact_isRegular_aleph0


private noncomputable def chosenStageAlgColimit
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    CommAlgCat.{max u v} (ULift.{max u v} A) := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let D := chosenStageAlgDiagramLift A T f
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  letI : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  letI : SmallCategory J' := inferInstance
  exact colimit D

@[instance_reducible] private noncomputable def chosenStageAlgColimitAlgebraOverA
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Algebra A (chosenStageAlgColimit A T f) :=
  Algebra.compHom (chosenStageAlgColimit A T f)
    (ULift.ringEquiv (R := A)).symm.toRingHom

attribute [local instance] chosenStageAlgColimitAlgebraOverA

private theorem chosenStageAlgColimitScalarTower
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsScalarTower A (ULift.{max u v} A) (chosenStageAlgColimit A T f) :=
  .of_algebraMap_eq' (by ext x; rfl)

attribute [local instance] chosenStageAlgColimitScalarTower

private theorem chosenStageAlgColimit_isIndZariski
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsIndZariski.{max u v, max u v, max u v} (ULift.{max u v} A)
      (chosenStageAlgColimit A T f) := by
  classical
  let P : ObjectProperty (CommAlgCat.{max u v} (ULift.{max u v} A)) :=
    fun S => Algebra.IsLocalIso (ULift.{max u v} A) S
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{max u v}
      (CommAlgCat.{max u v} (ULift.{max u v} A)) :=
    fun S hS => localIso_isFinitelyPresentable _ S hS
  let D := chosenStageAlgDiagramLift A T f
  let J := (DiscreteQuotient T)ᵒᵖ
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  let : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  let : SmallCategory J' := inferInstance
  have hcolim : ObjectProperty.ind.{max u v} (ObjectProperty.ind.{max u v} P)
      (chosenStageAlgColimit A T f) := by
    refine ⟨J', inferInstance, inferInstance,
      ColimitPresentation.colimit D, ?_⟩
    intro j
    let q := (CategoryTheory.ULiftHom.objDown j).down.unop
    let Bq := (chosenProfiniteStage A T q f).B
    let : Algebra A Bq := chosenStageAlgebraOverA A T q f
    let : Algebra (ULift.{max u v} A) Bq := chosenStageAlgebraOverLiftA A T q f
    have hmap : algebraMap (ULift.{max u v} A) Bq =
        (algebraMap A Bq).comp (algebraMap (ULift.{max u v} A) A) := by
      ext x
      rfl
    have hTower : IsScalarTower (ULift.{max u v} A) A Bq :=
      IsScalarTower.of_algebraMap_eq' hmap
    have hqA : IsIndZariski.{u, max u v, max u v} A Bq :=
      chosenStage_isIndZariski_over_A A T q f
    have hAInd : IsIndZariski.{max u v, u, max u v}
        (ULift.{max u v} A) A := by
      show ObjectProperty.ind.{max u v} P
        (CommAlgCat.of (ULift.{max u v} A) (ULift.{max u v} A))
      exact ObjectProperty.le_ind P
        (CommAlgCat.of (ULift.{max u v} A) (ULift.{max u v} A)) inferInstance
    have hqLift : ObjectProperty.ind.{max u v} P
        (CommAlgCat.of (ULift.{max u v} A) (ULift.{max u v} Bq)) :=
      @Algebra.IsIndZariski.comp (ULift.{max u v} A) A Bq
        inferInstance inferInstance inferInstance
        (baseAlgebraOfLift A) (chosenStageAlgebraOverA A T q f)
        (chosenStageAlgebraOverLiftA A T q f) hTower hAInd hqA
    exact (ObjectProperty.ind P).prop_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv (R := ULift.{max u v} A))) hqLift
  rw [ObjectProperty.ind_ind hfp] at hcolim
  exact (ObjectProperty.ind P).prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv (R := ULift.{max u v} A)).symm) hcolim

private theorem chosenStageAlgColimit_isIndZariski_overA
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsIndZariski.{u, max u v, max u v} A
      (chosenStageAlgColimit A T f) := by
  classical
    let C := chosenStageAlgColimit A T f
    let R := ULift.{max u v} A
  let : CommRing C := C.commRing
  let : Algebra R C := C.algebra
  let : Algebra A R := (ULift.ringEquiv (R := A)).symm.toRingHom.toAlgebra
  let : IsScalarTower A R C := chosenStageAlgColimitScalarTower A T f
  have hAA : IsIndZariski.{u, max u v, max u v} A R := by
    have : Algebra.IsLocalIso A R := by
      have : Algebra.IsStandardOpenImmersion A R :=
        Algebra.IsStandardOpenImmersion.of_bijective
          (by simpa [RingHom.algebraMap_toAlgebra] using
            (ULift.ringEquiv (R := A)).symm.bijective)
      infer_instance
    exact isIndZariski_of_isLocalIso A R
  have hRC : IsIndZariski.{max u v, max u v, max u v} R C :=
    chosenStageAlgColimit_isIndZariski A T f
  exact @Algebra.IsIndZariski.comp A R C
    inferInstance inferInstance inferInstance
    (inferInstance : Algebra A R) (inferInstance : Algebra R C)
    (inferInstance : Algebra A C) (chosenStageAlgColimitScalarTower A T f) hAA hRC

private lemma chosenStageAlgDiagramLift_preservesColimit
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    PreservesColimit (chosenStageAlgDiagramLift A T f)
      (forget₂ (CommAlgCat.{max u v} (ULift.{max u v} A)) CommRingCat) := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  let : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  let : SmallCategory J' := inferInstance
  let : IsFiltered J' := inferInstance
  change PreservesColimit (chosenStageAlgDiagramLift A T f)
    ((commAlgCatEquivUnder (CommRingCat.of (ULift.{max u v} A))).functor ⋙
      Under.forget (CommRingCat.of (ULift.{max u v} A)))
  infer_instance

private noncomputable def chosenStageSpecCone
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Cone (chosenStageSchemeDiagram A T f) := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let D := chosenStageAlgDiagramLift A T f
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  letI : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  letI : SmallCategory J' := inferInstance
  let F := forget₂ (CommAlgCat.{max u v} (ULift.{max u v} A)) CommRingCat
  let cLift := (Scheme.Spec.mapCone (F.mapCocone (colimit.cocone D)).op).whisker
    (chosenStageIndexEquiv A T).functor
  cases chosenStageSchemeDiagram_eq_lift A T f
  exact cLift

private noncomputable def chosenStageSpecCone_isLimit
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    IsLimit (chosenStageSpecCone A T f) := by
  let J := (DiscreteQuotient T)ᵒᵖ
  let D := chosenStageAlgDiagramLift A T f
  let J' := CategoryTheory.ULiftHom.{max u v} (ULift.{max u v} J)
  letI : Category.{max u v} J' := CategoryTheory.ULiftHom.category
  letI : SmallCategory J' := inferInstance
  let F := forget₂ (CommAlgCat.{max u v} (ULift.{max u v} A)) CommRingCat
  haveI := chosenStageAlgDiagramLift_preservesColimit A T f
  let ccRing := F.mapCocone (colimit.cocone D)
  have hLift := (Functor.Initial.isLimitWhiskerEquiv
      (chosenStageIndexEquiv A T).functor (Scheme.Spec.mapCone ccRing.op)).symm
    (isLimitOfPreserves Scheme.Spec (isColimitOfPreserves F (colimit.isColimit D)).op)
  cases chosenStageSchemeDiagram_eq_lift A T f
  exact hLift

private noncomputable def chosenStageSpectrumProjection
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (q : DiscreteQuotient T) :
    C(PrimeSpectrum (chosenStageAlgColimit A T f),
      PrimeSpectrum (chosenProfiniteStage A T q f).B) := by
  let h := (chosenStageSpecCone A T f).π.app q
  exact ⟨h.base.hom, h.base.hom.continuous⟩

private lemma chosenStageSchemeMap_eq_package
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ⟶ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ((chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop).map h).hom =
      (chosenStageTransitionPackage A T q q' h.le f).specMap := by
  let P := chosenStageTransitionPackage A T q q' h.le f
  have hs : (chosenStageSchemeDiagram A T f).map h =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (chosenStageTransition A T q q' h.le f).toRingHom) := by
    show AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (chosenStageTransition A T q q' h.le f).toRingHom) = _
    rfl
  rw [Functor.comp_map, hs]
  have ht : chosenStageTransition A T q q' h.le f = P.hom := rfl
  rw [ht]
  show (AlgebraicGeometry.Spec.topMap
    (CommRingCat.ofHom P.hom.toRingHom)).hom = P.specMap
  exact congrArg (fun g => g.hom) P.specMap_eq_overA

private lemma chosenStageSchemeMap_apply
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ⟶ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) :
    ((chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop).map h).hom
      (componentPullbackStageMap A T q f z) =
        componentPullbackStageMap A T q' f z := by
  rw [chosenStageSchemeMap_eq_package A T q q' h f]
  exact componentPullbackStageMap_natural A T q q' h.le f z

private noncomputable def componentPullbackStageCone
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    Cone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop) where
  pt := TopCat.of (ComponentPullback A T f)
  π := {
    app := fun q => TopCat.ofHom (componentPullbackStageMap A T q f)
    naturality := by
      intro q q' h
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      exact (chosenStageSchemeMap_apply A T q q' h f z).symm }

private lemma chosenStageTransitionPackage_specMap_limit_val
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q q' : DiscreteQuotient T) (h : q ≤ q')
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (y : (TopCat.limitCone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop)).pt) :
    (chosenStageTransitionPackage A T q q' h f).specMap (y.val q) = y.val q' := by
  have heq := congrArg (fun g : C(PrimeSpectrum (chosenProfiniteStage A T q f).B,
      PrimeSpectrum (chosenProfiniteStage A T q' f).B) => g (y.val q))
    (chosenStageSchemeMap_eq_package A T q q' (CategoryTheory.homOfLE h) f)
  exact heq.symm.trans (y.property (CategoryTheory.homOfLE h))

private lemma componentPullback_ext_of_stageMap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) {z z' : ComponentPullback A T f}
    (h : ∀ q, componentPullbackStageMap A T q f z = componentPullbackStageMap A T q f z') :
    z = z' := by
  apply Subtype.ext
  apply Prod.ext
  · exact (chosenStagePointBase_pullback A T ⊤ f z).symm.trans
      ((congrArg (chosenStagePointBase A T ⊤ f) (h ⊤)).trans
        (chosenStagePointBase_pullback A T ⊤ f z'))
  · apply DiscreteQuotient.eq_of_forall_proj_eq
    intro q
    exact (chosenStagePointIndex_pullback A T q f z).symm.trans
      ((congrArg (chosenStagePointIndex A T q f) (h q)).trans
        (chosenStagePointIndex_pullback A T q f z'))

private lemma connectedComponents_mk_eq_of_limit_compat
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (y : (TopCat.limitCone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop)).pt)
    (t : T) (p : PrimeSpectrum A)
    (ht : ∀ q : DiscreteQuotient T, q.proj t = chosenStagePointIndex A T q f (y.val q))
    (hbase : ∀ q : DiscreteQuotient T, chosenStagePointBase A T q f (y.val q) = p) :
    ConnectedComponents.mk p = f t := by
  let : T2Space (ConnectedComponents (PrimeSpectrum A)) :=
    (connectedComponents_isProfinite (PrimeSpectrum A)).1
  by_contra hne
  have hneq : f t ≠ ConnectedComponents.mk p := fun h => hne h.symm
  have hclosedPoint : IsClosed ({ConnectedComponents.mk p} :
      Set (ConnectedComponents (PrimeSpectrum A))) := isClosed_singleton
  have hmem : t ∈ f ⁻¹' ({ConnectedComponents.mk p}ᶜ) := hneq
  obtain ⟨V, hV, htV, hVU⟩ := compact_exists_isClopen_in_isOpen
    (hclosedPoint.isOpen_compl.preimage f.continuous) hmem
  let qV := DiscreteQuotient.ofIsClopen hV
  let xV := PrimeSpectrum.comap
    (algebraMap (qV → A) (chosenProfiniteStage A T qV f).B) (y.val qV)
  have hxV : ConnectedComponents.mk xV ∈ Set.range (stageComponentsMap A T qV f) := by
    have hx : xV ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (qV → A) (chosenProfiniteStage A T qV f).B)) :=
      ⟨y.val qV, rfl⟩
    rw [(chosenProfiniteStage A T qV f).range] at hx
    exact hx
  obtain ⟨t', ht'⟩ := hxV
  have hi' : qV.proj t' = qV.proj t := by
    have h := congrArg (stageComponentIndexMap A T qV) ht'
    rw [stageComponentIndexMap_map, stageComponentIndexMap_mk] at h
    have hidx' : stageSpectrumIndexMap A T qV xV = qV.proj t := (ht qV).symm
    have hidxT : stageSpectrumIndexMap A T qV xV = qV.proj t' := by
      simpa only [stageComponentIndexMap_mk, stageComponentIndexMap_map] using h.symm
    exact hidxT.symm.trans hidx'
  have hb' : f t' = ConnectedComponents.mk p := by
    have h := congrArg (stageComponentBaseMap A T qV) ht'
    rw [stageComponentBaseMap_map, stageComponentBaseMap_mk] at h
    have hbase' : stageSpectrumBaseMap A T qV xV = p := hbase qV
    exact h.trans (congrArg ConnectedComponents.mk hbase')
  have hrel' : t' ∈ V ↔ t ∈ V := Quotient.exact' hi'
  exact hVU (hrel'.mpr htV) hb'

private lemma exists_componentPullbackStageMap_eq
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (y : (TopCat.limitCone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop)).pt) :
    ∃ z : ComponentPullback A T f, ∀ q, componentPullbackStageMap A T q f z = y.val q := by
  let idx : (q : DiscreteQuotient T) → q := fun q =>
    chosenStagePointIndex A T q f (y.val q)
  have hidx (q q' : DiscreteQuotient T) (h : q ≤ q') :
      DiscreteQuotient.ofLE h (idx q) = idx q' := by
    calc
      DiscreteQuotient.ofLE h (idx q) = chosenStagePointIndex A T q' f
          ((chosenStageTransitionPackage A T q q' h f).specMap (y.val q)) :=
        chosenStagePointIndex_natural A T q q' h f (y.val q)
      _ = idx q' := by rw [chosenStageTransitionPackage_specMap_limit_val A T q q' h f y]
  obtain ⟨t, ht⟩ := DiscreteQuotient.exists_of_compat idx hidx
  let p := chosenStagePointBase A T ⊤ f (y.val ⊤)
  have hbase (q : DiscreteQuotient T) :
      chosenStagePointBase A T q f (y.val q) = p := by
    calc
      chosenStagePointBase A T q f (y.val q) = chosenStagePointBase A T ⊤ f
          ((chosenStageTransitionPackage A T q ⊤ le_top f).specMap (y.val q)) :=
        (chosenStagePointBase_natural A T q ⊤ le_top f (y.val q)).symm
      _ = p := by rw [chosenStageTransitionPackage_specMap_limit_val A T q ⊤ le_top f y]
  refine ⟨⟨(p, t), connectedComponents_mk_eq_of_limit_compat A T f y t p ht hbase⟩,
    fun q => ?_⟩
  apply (chosenProfiniteStage A T q f).isEmbedding.injective
  have hidx' : stageSpectrumIndexMap A T q
      (PrimeSpectrum.comap (algebraMap (q → A)
        (chosenProfiniteStage A T q f).B) (y.val q)) = q.proj t := (ht q).symm
  have hbase' : stageSpectrumBaseMap A T q
      (PrimeSpectrum.comap (algebraMap (q → A)
        (chosenProfiniteStage A T q f).B) (y.val q)) = p := hbase q
  rw [componentPullbackStageMap_comap, componentPullbackStageAmbient_eq,
    stageSpectrum_eq_productPoint A T q
      (PrimeSpectrum.comap (algebraMap (q → A)
        (chosenProfiniteStage A T q f).B) (y.val q)), hidx', hbase']

private lemma continuous_of_forall_discreteQuotient_proj
    {Y : Type w} [TopologicalSpace Y] {T : Type v} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] (g : Y → T)
    (hg : ∀ q : DiscreteQuotient T, Continuous fun y => q.proj (g y)) : Continuous g := by
  refine continuous_def.2 fun U hU => ?_
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_isClopen.open_eq_sUnion hU
  rw [Set.sUnion_eq_biUnion, Set.preimage_iUnion₂]
  refine isOpen_biUnion fun V hV => ?_
  let qV := DiscreteQuotient.ofIsClopen (hS hV)
  have hpre : g ⁻¹' V = (fun y => qV.proj (g y)) ⁻¹' (qV.proj '' V) := by
    ext y
    constructor
    · exact fun hy => ⟨g y, hy, rfl⟩
    · rintro ⟨t₀, ht₀, hq⟩
      exact (Quotient.exact' hq.symm : g y ∈ V ↔ t₀ ∈ V).mpr ht₀
  rw [hpre]
  exact (hg qV).isOpen_preimage _ (isOpen_discrete _)

private lemma continuous_of_componentPullbackStageMap_eq
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (θ : (TopCat.limitCone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop)).pt →
      ComponentPullback A T f)
    (hθ : ∀ y q, componentPullbackStageMap A T q f (θ y) = y.val q) : Continuous θ := by
  have hpcont : Continuous (fun y => (θ y).val.1) := by
    have hfun : (fun y => (θ y).val.1) = fun y =>
        chosenStagePointBase A T ⊤ f (y.val ⊤) := by
      funext y
      calc
        (θ y).val.1 = chosenStagePointBase A T ⊤ f
            (componentPullbackStageMap A T ⊤ f (θ y)) :=
              (chosenStagePointBase_pullback A T ⊤ f (θ y)).symm
        _ = chosenStagePointBase A T ⊤ f (y.val ⊤) :=
              congrArg (chosenStagePointBase A T ⊤ f) (hθ y ⊤)
    rw [hfun]
    exact (chosenStagePointBase A T ⊤ f).continuous.comp
      (continuous_apply ⊤ |>.comp continuous_subtype_val)
  have htcont : Continuous (fun y => (θ y).val.2) := by
    refine continuous_of_forall_discreteQuotient_proj _ fun q => ?_
    refine ((chosenStagePointIndex A T q f).continuous.comp
      (continuous_apply q |>.comp continuous_subtype_val)).congr fun y => ?_
    calc
      chosenStagePointIndex A T q f (y.val q) = chosenStagePointIndex A T q f
          (componentPullbackStageMap A T q f (θ y)) := by rw [hθ y q]
      _ = q.proj (θ y).val.2 := chosenStagePointIndex_pullback A T q f (θ y)
  exact Continuous.subtype_mk (hpcont.prodMk htcont) (fun y => (θ y).property)

private noncomputable def componentPullbackStageCone_homeomorph_limit
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ComponentPullback A T f ≃ₜ
      (TopCat.limitCone (chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop)).pt := by
  classical
  letI : T2Space T := ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT).2.1
  letI : TotallyDisconnectedSpace T :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT).2.2
  letI : T2Space (ConnectedComponents (PrimeSpectrum A)) :=
    (connectedComponents_isProfinite (PrimeSpectrum A)).1
  have hclosed : IsClosed
      ({z : PrimeSpectrum A × T | ConnectedComponents.mk z.1 = f z.2} :
        Set (PrimeSpectrum A × T)) :=
    isClosed_eq (ConnectedComponents.continuous_coe.comp continuous_fst)
      (f.continuous.comp continuous_snd)
  letI : CompactSpace (ComponentPullback A T f) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  let D := chosenStageSchemeDiagram A T f ⋙ Scheme.forgetToTop
  let η := (TopCat.limitConeIsLimit D).lift (componentPullbackStageCone A T f)
  have hcoord (z : ComponentPullback A T f) (q : DiscreteQuotient T) :
      (η.hom z).val q = componentPullbackStageMap A T q f z := rfl
  let θ : (TopCat.limitCone D).pt → ComponentPullback A T f :=
    fun y => Classical.choose (exists_componentPullbackStageMap_eq A T f y)
  have hθcoord (y : (TopCat.limitCone D).pt) (q : DiscreteQuotient T) :
      componentPullbackStageMap A T q f (θ y) = y.val q :=
    Classical.choose_spec (exists_componentPullbackStageMap_eq A T f y) q
  have hθright (y : (TopCat.limitCone D).pt) : η.hom (θ y) = y := by
    apply Subtype.ext
    funext q
    exact (hcoord (θ y) q).trans (hθcoord y q)
  exact {
    toEquiv := {
      toFun := η.hom
      invFun := θ
      left_inv := fun z => componentPullback_ext_of_stageMap A T f fun q =>
        (hθcoord (η.hom z) q).trans (hcoord z q)
      right_inv := hθright }
    continuous_toFun := η.hom.continuous
    continuous_invFun := continuous_of_componentPullbackStageMap_eq A T f θ hθcoord }

private lemma componentPullbackStageCone_homeomorph_limit_apply
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (z : ComponentPullback A T f) (q : DiscreteQuotient T) :
    (componentPullbackStageCone_homeomorph_limit A T hT f z).val q =
      componentPullbackStageMap A T q f z := rfl

private lemma chosenStageSchemeDiagram_preservesLimit
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    PreservesLimit (chosenStageSchemeDiagram A T f) Scheme.forgetToTop := by
  let D := chosenStageSchemeDiagramLift A T f
  let : ∀ j, IsAffine (D.obj j) := fun j => by
    show IsAffine (Spec _)
    infer_instance
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => by
    infer_instance
  have : PreservesLimit D Scheme.forgetToTop :=
    AlgebraicGeometry.preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom D
  rw [chosenStageSchemeDiagram_eq_lift]
  exact Functor.Initial.comp_preservesLimit (chosenStageIndexEquiv A T).functor

private noncomputable def chosenStageSpectrumHomeo
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    PrimeSpectrum (chosenStageAlgColimit A T f) ≃ₜ ComponentPullback A T f := by
  haveI := chosenStageSchemeDiagram_preservesLimit A T f
  let h := isLimitOfPreserves Scheme.forgetToTop (chosenStageSpecCone_isLimit A T f)
  exact (TopCat.homeoOfIso (h.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit _))).trans
      (componentPullbackStageCone_homeomorph_limit A T hT f).symm

private lemma chosenStageSpectrumHomeo_coord
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (p : PrimeSpectrum (chosenStageAlgColimit A T f)) (q : DiscreteQuotient T) :
    componentPullbackStageMap A T q f (chosenStageSpectrumHomeo A T hT f p) =
      chosenStageSpectrumProjection A T f q p := by
  have := chosenStageSchemeDiagram_preservesLimit A T f
  let h := isLimitOfPreserves Scheme.forgetToTop (chosenStageSpecCone_isLimit A T f)
  let e := TopCat.homeoOfIso (h.conePointUniqueUpToIso (TopCat.limitConeIsLimit _))
  let k := componentPullbackStageCone_homeomorph_limit A T hT f
  have hc : (e p).val q = chosenStageSpectrumProjection A T f q p :=
    ConcreteCategory.congr_hom
      (h.conePointUniqueUpToIso_hom_comp (TopCat.limitConeIsLimit _) q) p
  have hk : componentPullbackStageMap A T q f (k.symm (e p)) = (e p).val q :=
    (componentPullbackStageCone_homeomorph_limit_apply A T hT f _ q).symm.trans
      (congrArg (fun z => z.val q) (k.apply_symm_apply (e p)))
  exact hk.trans hc

private lemma chosenStagePointBase_eq_comap
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (q : DiscreteQuotient T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (p : PrimeSpectrum (chosenProfiniteStage A T q f).B) :
    chosenStagePointBase A T q f p = PrimeSpectrum.comap (algebraMap A _) p := by
  let z := PrimeSpectrum.comap (algebraMap (q → A) _) p
  have hz := stageSpectrum_eq_productPoint A T q z
  have hb := congrArg (PrimeSpectrum.comap (algebraMap A (q → A))) hz
  have hpoint (i : q) (r : PrimeSpectrum A) :
      PrimeSpectrum.comap (algebraMap A (q → A))
        (stageProductSpectrumPoint A T q i r) = r := by
    apply PrimeSpectrum.ext
    ext a
    rfl
  rw [hpoint] at hb
  exact hb.symm

private lemma chosenStageSpectrumProjection_base
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (q : DiscreteQuotient T) (p : PrimeSpectrum (chosenStageAlgColimit A T f)) :
    PrimeSpectrum.comap (algebraMap A _)
      (chosenStageSpectrumProjection A T f q p) =
        PrimeSpectrum.comap (algebraMap A _) p := by
  let j := ((chosenStageIndexEquiv A T).functor.obj q).unop
  let φ := (colimit.ι (chosenStageAlgDiagramLift A T f) j).hom
  show PrimeSpectrum.comap (algebraMap A (chosenProfiniteStage A T q f).B)
    (PrimeSpectrum.comap φ.toRingHom p) = _
  apply PrimeSpectrum.ext
  ext a
  show φ (algebraMap A (chosenProfiniteStage A T q f).B a) ∈ p.asIdeal ↔
    algebraMap A (chosenStageAlgColimit A T f) a ∈ p.asIdeal
  have h := φ.commutes (ULift.up a)
  change φ (algebraMap A (chosenProfiniteStage A T q f).B a) =
    algebraMap A (chosenStageAlgColimit A T f) a at h
  rw [h]
  rfl

private lemma chosenStageSpectrumHomeo_base
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    [CompactSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A)))
    (p : PrimeSpectrum (chosenStageAlgColimit A T f)) :
    (chosenStageSpectrumHomeo A T hT f p).val.1 =
      PrimeSpectrum.comap (algebraMap A _) p := by
  rw [← chosenStagePointBase_pullback A T ⊤ f,
    chosenStageSpectrumHomeo_coord, chosenStagePointBase_eq_comap,
    chosenStageSpectrumProjection_base]

private lemma connectedComponents_snd_injective
    {X : Type u} {T : Type v} [TopologicalSpace X] [TopologicalSpace T]
    [TotallyDisconnectedSpace T] (f : C(T, ConnectedComponents X))
    {Y : Type w} [TopologicalSpace Y]
    (e : Y ≃ₜ {z : X × T // ConnectedComponents.mk z.1 = f z.2}) :
    Function.Injective
      ((continuous_snd.comp continuous_subtype_val).comp e.continuous).connectedComponentsLift := by
  intro a b hab
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  change (e x).val.2 = (e y).val.2 at hab
  have hcc : ConnectedComponents.mk (e x).val.1 = ConnectedComponents.mk (e y).val.1 :=
    (e x).property.trans ((congrArg f hab).trans (e y).property.symm)
  let C := connectedComponent (e y).val.1
  let k : C → Y := fun z => e.symm ⟨(z.val, (e y).val.2),
    (ConnectedComponents.coe_eq_coe'.mpr z.property).trans (e y).property⟩
  have hk : Continuous k := e.symm.continuous.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
  have hC : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_connectedComponent
  have hi : IsPreconnected (Set.range k) := isPreconnected_range hk
  have hx : x ∈ Set.range k := by
    refine ⟨⟨(e x).val.1, ConnectedComponents.coe_eq_coe'.mp hcc⟩, ?_⟩
    apply e.injective
    show e (e.symm _) = e x
    rw [e.apply_symm_apply]
    exact Subtype.ext (Prod.ext rfl hab.symm)
  have hy : y ∈ Set.range k := by
    refine ⟨⟨(e y).val.1, mem_connectedComponent⟩, ?_⟩
    exact e.symm_apply_apply y
  exact ConnectedComponents.coe_eq_coe'.mpr (hi.subset_connectedComponent hy hx)

private noncomputable def connectedComponentsHomeoOfComponentPullback
    {X : Type u} {T : Type v} [TopologicalSpace X] [TopologicalSpace T]
    [TotallyDisconnectedSpace T] [T2Space T] (f : C(T, ConnectedComponents X))
    {Y : Type w} [TopologicalSpace Y] [CompactSpace Y]
    (e : Y ≃ₜ {z : X × T // ConnectedComponents.mk z.1 = f z.2}) :
    ConnectedComponents Y ≃ₜ T := by
  let h := ((continuous_snd.comp continuous_subtype_val).comp e.continuous)
  apply IsHomeomorph.homeomorph h.connectedComponentsLift
  apply isHomeomorph_iff_continuous_bijective.mpr
  refine ⟨h.connectedComponentsLift_continuous,
    connectedComponents_snd_injective f e, ?_⟩
  intro t
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (f t)
  refine ⟨ConnectedComponents.mk (e.symm ⟨(p,t), hp⟩), ?_⟩
  change (e (e.symm ⟨(p, t), hp⟩)).val.2 = t
  rw [e.apply_symm_apply]

private lemma isPullback_of_componentPullback_homeomorph
    {X : Type u} {T : Type v} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Y]
    (f : C(T, ConnectedComponents X)) (a : C(Y, X))
    (e : Y ≃ₜ {z : X × T // ConnectedComponents.mk z.1 = f z.2})
    (ha : ∀ y, (e y).val.1 = a y) :
    IsPullback
      (TopCat.ofHom (⟨fun y => ULift.up (a y), continuous_uliftUp.comp a.continuous⟩ :
        C(Y, ULift.{v} X)))
      (TopCat.ofHom (⟨fun y => ULift.up (e y).val.2,
        continuous_uliftUp.comp ((continuous_snd.comp continuous_subtype_val).comp
          e.continuous)⟩ : C(Y, ULift.{u} T)))
      (TopCat.ofHom (⟨fun x => ULift.up (ConnectedComponents.mk x.down),
        continuous_uliftUp.comp
          (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩ :
        C(ULift.{v} X, ULift.{v} (ConnectedComponents X))))
      (TopCat.ofHom (⟨fun t => ULift.up (f t.down),
        continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} T, ULift.{v} (ConnectedComponents X)))) := by
  let l := TopCat.ofHom (⟨fun y => ULift.up (a y),
    continuous_uliftUp.comp a.continuous⟩ : C(Y, ULift.{v} X))
  let r := TopCat.ofHom (⟨fun y => ULift.up (e y).val.2,
    continuous_uliftUp.comp ((continuous_snd.comp continuous_subtype_val).comp
      e.continuous)⟩ : C(Y, ULift.{u} T))
  let b := TopCat.ofHom (⟨fun x => ULift.up (ConnectedComponents.mk x.down),
    continuous_uliftUp.comp
      (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩ :
    C(ULift.{v} X, ULift.{v} (ConnectedComponents X)))
  let c := TopCat.ofHom (⟨fun t => ULift.up (f t.down),
    continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩ :
    C(ULift.{u} T, ULift.{v} (ConnectedComponents X)))
  have hw : l ≫ b = r ≫ c := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    show ULift.up (ConnectedComponents.mk (a y)) = ULift.up (f (e y).val.2)
    rw [← ha y, (e y).property]
  refine IsPullback.of_isLimit (c := PullbackCone.mk l r hw) ?_
  refine PullbackCone.isLimitAux' _ fun s => ?_
  have hk (z : s.pt) : ConnectedComponents.mk (s.fst z).down = f (s.snd z).down :=
    congrArg ULift.down (ConcreteCategory.congr_hom s.condition z)
  let k : C(s.pt, {z : X × T // ConnectedComponents.mk z.1 = f z.2}) :=
    ⟨fun z => ⟨((s.fst z).down, (s.snd z).down), hk z⟩,
      ((continuous_uliftDown.comp s.fst.hom.continuous).prodMk
        (continuous_uliftDown.comp s.snd.hom.continuous)).subtype_mk hk⟩
  refine ⟨TopCat.ofHom ((e.symm : C(_, _)).comp k), ?_, ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    show ULift.up (a (e.symm (k z))) = s.fst z
    rw [← ha, e.apply_symm_apply]
    rfl
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    show ULift.up (e (e.symm (k z))).val.2 = s.snd z
    rw [e.apply_symm_apply]
    rfl
  · intro m hl hr
    ext z
    apply e.injective
    show e (m z) = e (e.symm (k z))
    rw [e.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact (ha (m.hom z)).trans
        (congrArg ULift.down (ConcreteCategory.congr_hom hl z))
    · exact congrArg ULift.down (ConcreteCategory.congr_hom hr z)

/-- **Stacks Project, Tag 097D.** A profinite space over the connected components of an affine
spectrum is realized by the spectrum of an ind-Zariski algebra, with its canonical component
space and cartesian square. -/
@[stacks 097D]
theorem exists_indZariski_of_profinite_component_map
    (A : Type u) [CommRing A] (T : Type v) [TopologicalSpace T]
    (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra A B),
      IsIndZariski.{u, max u v, max u v} A B ∧
      ∃ g : C(PrimeSpectrum B, T),
      ∃ e : ConnectedComponents (PrimeSpectrum B) ≃ₜ T,
        (∀ p : PrimeSpectrum B, e (ConnectedComponents.mk p) = g p) ∧
        IsPullback
          (TopCat.ofHom (⟨fun p => ULift.up (PrimeSpectrum.comap (algebraMap A B) p),
            continuous_uliftUp.comp (PrimeSpectrum.continuous_comap (algebraMap A B))⟩ :
              C(PrimeSpectrum B, ULift.{v} (PrimeSpectrum A))))
          (TopCat.ofHom (⟨fun p => ULift.up (g p), continuous_uliftUp.comp g.continuous⟩ :
            C(PrimeSpectrum B, ULift.{u} T)))
          (TopCat.ofHom (⟨fun p => ULift.up (ConnectedComponents.mk p.down),
            continuous_uliftUp.comp
              (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩ :
                C(ULift.{v} (PrimeSpectrum A),
                  ULift.{v} (ConnectedComponents (PrimeSpectrum A)))))
          (TopCat.ofHom (⟨fun t => ULift.up (f t.down),
            continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩ :
              C(ULift.{u} T, ULift.{v} (ConnectedComponents (PrimeSpectrum A))))) := by
  classical
  let : CompactSpace T :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT).1
  let : T2Space T :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT).2.1
  let : TotallyDisconnectedSpace T :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).mp hT).2.2
  let B := chosenStageAlgColimit A T f
  let h := chosenStageSpectrumHomeo A T hT f
  let g : C(PrimeSpectrum B, T) :=
    ⟨fun p => (h p).val.2,
      (continuous_snd.comp continuous_subtype_val).comp h.continuous⟩
  refine ⟨B, inferInstance, inferInstance,
    chosenStageAlgColimit_isIndZariski_overA A T f, g,
    connectedComponentsHomeoOfComponentPullback f h, fun _ => rfl,
    isPullback_of_componentPullback_homeomorph f
      ⟨PrimeSpectrum.comap (algebraMap A B), PrimeSpectrum.continuous_comap _⟩ h
      (chosenStageSpectrumHomeo_base A T hT f)⟩

end AlgebraicGeometry.ProEtale

end
