module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeAllPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverCofinality
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.StageEtaleSystem
import all StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
import all StacksFrontier.Topology.Algebra.AdicTopology.FiniteType

/-!
# Factoring a taut topologically finite type map through affine space

Let `g : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S`. When `g` is taut and `C` is topologically of finite type over `A`, the morphism
`Spf (g) : Spf C ⟶ Spf A` factors as

`Spf C ⟶ 𝔸ʳ_{Spf A} ⟶ Spf A`

with the first arrow a closed immersion. This is the reformulation of the conclusion of Stacks
0ANT stated in part (4) of Stacks 0AJK. Here `𝔸ʳ_{Spf A} = Spf A{x₁, …, xᵣ}` is the formal
spectrum of the completion `A{x₁, …, xᵣ} = lim_I (A/I)[x₁, …, xᵣ]` of the polynomial ring over
the weak ideals of definition `I` of `A` (`TopologicalRing.CompletionOver MvPolynomial.C`).

## Main results

* `TopologicalRing.exists_ringHom_forall_weakIdeal_comp_eq`: a weakly admissible ring is the
  inverse limit of its quotients by weak ideals of definition, read on ring maps into it.
* `RingHom.isTaut_of_isTaut_comp`: if `c` is taut, `ψ` continuous and `ψ ∘ c` taut, then `ψ`
  is taut.
* `TopologicalRing.exists_continuous_lift_completionOver`: a ring map `p : P ⟶ C` with `p ∘ c`
  continuous extends continuously to the completion of `P` over `A`.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_formalSpectrumMap_of_isTaut_of_denseRange`:
  the formal spectrum of a taut homomorphism with dense image is a closed immersion.
* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_completionOver_of_finiteType` and
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum_completionOver`:
  the relative completion of a finite type algebra over a ring whose formal spectrum is an
  affine formal algebraic space has a formal spectrum in the same site, again an affine formal
  algebraic space, with no condition on the size of the site.
* `AlgebraicGeometry.FormalSpace.exists_isClosedImmersion_affineSpace_factorization`: the
  factorization through affine space.

## Implementation notes

A dense polynomial presentation `p : A[x₁, …, xᵣ] ⟶ C` of `g` extends to the completion
`A{x₁, …, xᵣ}` because `C` is complete and separated: modulo a weak ideal of definition `K` of
`C` it factors through `(A/I)[x₁, …, xᵣ]` for a weak ideal of definition `I` of `A` mapping into
`K`, and the resulting compatible family of maps into the quotients `C/K` comes from one map
into `C`. The extension is taut because its composite with the taut canonical map
`A ⟶ A{x₁, …, xᵣ}` is `g`, and it has dense image because `p` has.

That the formal spectrum of a taut homomorphism `ψ : A' ⟶ C` with dense image is a closed
immersion is read off on the stages of `Spf A'`: over `Spec (A'/I)` the base change of
`Spf (ψ)` is `Spec (C/J(I))` with `J(I)` the closure of `ψ(I)C`, by tautness, and
`A'/I ⟶ C/J(I)` is surjective because `ψ(A')` is dense and `J(I)` is open. The stages cover
`Spf A'`, and closed immersions descend along such coverings.

## References

* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0ANQ](https://stacks.math.columbia.edu/tag/0ANQ)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u v w

section InverseLimit

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Two elements of a weakly admissible ring with the same class modulo every weak ideal of
definition are equal, the ring being separated. -/
theorem eq_of_forall_weakIdeal_mk_eq (hC : IsWeaklyAdmissible C) {c d : C}
    (h : ∀ K : WeakIdealOfDefinitionIndex C,
      Ideal.Quotient.mk K.1 c = Ideal.Quotient.mk K.1 d) : c = d := by
  let _ : T2Space C := hC.2.2
  refine sub_eq_zero.mp (by_contra fun hne ↦ ?_)
  obtain ⟨I, hI, hIx⟩ := (hasBasis_nhds_zero_isWeakIdealOfDefinition hC).mem_iff.mp
    ((isClosed_singleton (x := c - d)).isOpen_compl.mem_nhds (by simpa using Ne.symm hne))
  exact hIx ((Ideal.Quotient.mk_eq_mk_iff_sub_mem c d).mp (h ⟨I, hI⟩)) rfl

/-- **A compatible family of classes modulo the weak ideals of definition of a weakly
admissible ring is the family of classes of one element.** This is completeness of the ring,
read through the neighbourhood basis of zero formed by the weak ideals of definition. -/
theorem exists_forall_weakIdeal_mk_eq (hC : IsWeaklyAdmissible C)
    (x : ∀ K : WeakIdealOfDefinitionIndex C, C ⧸ K.1)
    (hx : ∀ (K L : WeakIdealOfDefinitionIndex C) (h : K.1 ≤ L.1),
      Ideal.Quotient.factor h (x K) = x L) :
    ∃ c : C, ∀ K : WeakIdealOfDefinitionIndex C, Ideal.Quotient.mk K.1 c = x K := by
  classical
  let W := OrderDual (WeakIdealOfDefinitionIndex C)
  let _ : Nonempty W := ⟨OrderDual.toDual ⟨hC.1.choose, hC.1.choose_spec⟩⟩
  let _ : IsDirected W (· ≤ ·) := ⟨fun J K ↦ ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    isWeakIdealOfDefinition_inf_of_isOpen_right J.2 K.2.1⟩,
      show J.1 ⊓ K.1 ≤ J.1 from inf_le_left, show J.1 ⊓ K.1 ≤ K.1 from inf_le_right⟩⟩
  have hbasis : (nhds (0 : C)).HasBasis (fun _ : W ↦ True) (fun K ↦ (K.1 : Set C)) :=
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hC).to_hasBasis
      (fun I hI ↦ ⟨OrderDual.toDual ⟨I, hI⟩, trivial, subset_rfl⟩)
      (fun K _ ↦ ⟨K.1, K.2, subset_rfl⟩)
  choose r hr using fun K : W ↦ Ideal.Quotient.mk_surjective (x K)
  have hstage : ∀ K L : W, K ≤ L → Ideal.Quotient.mk K.1 (r L) = x K := by
    intro K L hKL
    have h : L.1 ≤ K.1 := hKL
    rw [← Ideal.Quotient.factor_mk h (r L), hr L]
    exact hx L K h
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  let _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  let _ : CompleteSpace C := hC.2.1
  have hcauchy : Cauchy (Filter.map r Filter.atTop) := by
    rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
    refine ⟨inferInstance, hbasis.tendsto_right_iff.mpr fun K _ ↦ ?_⟩
    rw [Filter.prod_atTop_atTop_eq, Filter.eventually_atTop_prod_self]
    exact ⟨K, fun k l hk hl ↦ (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      ((hstage K k hk).trans (hstage K l hl).symm)⟩
  obtain ⟨b, hb⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  refine ⟨b, fun K ↦ ?_⟩
  let K' : W := OrderDual.toDual K
  have hset : {c : C | Ideal.Quotient.mk K.1 c = x K} =
      (fun c : C ↦ c - r K') ⁻¹' (K.1 : Set C) := by
    ext c
    refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
    · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem c (r K')).mp (hc.trans (hr K').symm)
    · exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem c (r K')).mpr hc).trans (hr K')
  have hclosed : IsClosed {c : C | Ideal.Quotient.mk K.1 c = x K} := by
    rw [hset]
    exact (K.1.toAddSubgroup.isClosed_of_isOpen K.2.1).preimage
      (continuous_id.sub continuous_const)
  refine hclosed.mem_of_tendsto hb ?_
  filter_upwards [Filter.eventually_ge_atTop K'] with l hl
  exact hstage K' l hl

/-- **A compatible family of ring maps into the quotients of a weakly admissible ring by its
weak ideals of definition comes from a ring map into the ring itself.** -/
theorem exists_ringHom_forall_weakIdeal_comp_eq {R : Type w} [CommRing R]
    (hC : IsWeaklyAdmissible C) (ψ : ∀ K : WeakIdealOfDefinitionIndex C, R →+* C ⧸ K.1)
    (hψ : ∀ (K L : WeakIdealOfDefinitionIndex C) (h : K.1 ≤ L.1),
      (Ideal.Quotient.factor h).comp (ψ K) = ψ L) :
    ∃ χ : R →+* C, ∀ K : WeakIdealOfDefinitionIndex C,
      (Ideal.Quotient.mk K.1).comp χ = ψ K := by
  classical
  choose g hg using fun a : R ↦ exists_forall_weakIdeal_mk_eq hC (fun K ↦ ψ K a)
    (fun K L h ↦ congrArg (fun q : R →+* C ⧸ L.1 ↦ q a) (hψ K L h))
  have hext : ∀ a c, (∀ K : WeakIdealOfDefinitionIndex C, Ideal.Quotient.mk K.1 c = ψ K a) →
      g a = c := fun a c hc ↦ eq_of_forall_weakIdeal_mk_eq hC fun K ↦ (hg a K).trans (hc K).symm
  refine ⟨⟨⟨⟨g, hext 1 1 fun K ↦ by rw [map_one, map_one]⟩, fun a b ↦ hext _ _ fun K ↦ by
      rw [map_mul, hg a K, hg b K, map_mul]⟩, hext 0 0 fun K ↦ by rw [map_zero, map_zero],
      fun a b ↦ hext _ _ fun K ↦ by rw [map_add, hg a K, hg b K, map_add]⟩, fun K ↦ ?_⟩
  ext a
  exact hg a K

end InverseLimit

section Taut

/-- **Tautness of the second factor.** If `c : A → R` is taut and `ψ : R → C` is continuous
with `ψ ∘ c` taut, then `ψ` is taut: every open ideal of `R` contains the closure of the
extension of an open ideal of `A`, and closing before extending along `ψ` changes nothing. -/
theorem _root_.RingHom.isTaut_of_isTaut_comp {A R C : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] (c : A →+* R) (ψ : R →+* C) (hc : RingHom.IsTaut c)
    (hψ : Continuous ψ) (h : RingHom.IsTaut (ψ.comp c)) : RingHom.IsTaut ψ := by
  have hopen : ∀ L : Ideal R, IsOpen (L : Set R) →
      IsOpen ((Ideal.closure (L.map ψ) : Ideal C) : Set C) := by
    intro L hL
    obtain ⟨I, hI, hIL⟩ := hc.2.mem_iff.mp (hL.mem_nhds L.zero_mem)
    refine Ideal.isOpen_of_isOpen_subideal ?_ (h.1 I hI)
    rw [← Ideal.map_map]
    exact closure_mono (Ideal.map_mono fun _ hx ↦ hIL (subset_closure hx))
  refine ⟨hopen, Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩⟩
  · obtain ⟨I, hI, hIU⟩ := h.2.mem_iff.mp hU
    refine ⟨Ideal.closure (I.map c), hc.1 I hI, ?_⟩
    rwa [RingHom.closure_map_closure ψ hψ, Ideal.map_map]
  · rintro ⟨L, hL, hLU⟩
    exact Filter.mem_of_superset ((hopen L hL).mem_nhds (Ideal.closure _).zero_mem) hLU

end Taut

section Lift

/-- Passing from a quotient of `S` by `K` to one by a larger ideal `L` commutes with the maps
induced by `f`. -/
private theorem factor_comp_quotientMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {K L : Ideal S} (hKL : K ≤ L) {I : Ideal R} (h : I ≤ K.comap f) (h' : I ≤ L.comap f) :
    (Ideal.Quotient.factor hKL).comp (Ideal.quotientMap K f h) = Ideal.quotientMap L f h' := by
  ext x
  rfl

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] {P : Type v} [CommRing P] {C : Type w} [CommRing C]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- The class modulo `K` of an element of the completion of `P` over `A`, computed through any
weak ideal of definition `J` of `A` whose extension maps into `K`. -/
private def liftStage (c : A →+* P) (p : P →+* C) (K : Ideal C)
    (J : WeakIdealOfDefinitionIndex A) (hJ : extendedIdeal c J ≤ K.comap p) :
    CompletionOver c →+* C ⧸ K :=
  (Ideal.quotientMap K p hJ).comp (CompletionOver.projection c J)

omit [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C] in
private theorem liftStage_eq_of_le (c : A →+* P) (p : P →+* C) (K : Ideal C)
    (J J' : WeakIdealOfDefinitionIndex A) (hJJ' : J.1 ≤ J'.1)
    (hJ : extendedIdeal c J ≤ K.comap p) (hJ' : extendedIdeal c J' ≤ K.comap p) :
    liftStage c p K J hJ = liftStage c p K J' hJ' := by
  ext x
  have hx : transitionMap c hJJ' (x.1 J) = x.1 J' := x.2 J J' hJJ'
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.1 J)
  change Ideal.quotientMap K p hJ (x.1 J) = Ideal.quotientMap K p hJ' (x.1 J')
  rw [← hx, ← ha]
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C] in
private theorem liftStage_eq (c : A →+* P) (p : P →+* C) (K : Ideal C)
    (J J' : WeakIdealOfDefinitionIndex A)
    (hJ : extendedIdeal c J ≤ K.comap p) (hJ' : extendedIdeal c J' ≤ K.comap p) :
    liftStage c p K J hJ = liftStage c p K J' hJ' := by
  let M : WeakIdealOfDefinitionIndex A :=
    ⟨J.1 ⊓ J'.1, isWeakIdealOfDefinition_inf_of_isOpen_right J.2 J'.2.1⟩
  have hM : extendedIdeal c M ≤ K.comap p := (Ideal.map_mono inf_le_left).trans hJ
  rw [← liftStage_eq_of_le c p K M J inf_le_left hM hJ,
    liftStage_eq_of_le c p K M J' inf_le_right hM hJ']

omit [IsTopologicalRing C] [IsLinearTopology C C] in
/-- Every open ideal of `C` receives the extension of some weak ideal of definition of `A`,
when `p ∘ c` is continuous. -/
private theorem exists_extendedIdeal_le (hA : IsWeaklyAdmissible A) (c : A →+* P)
    (p : P →+* C) (hpc : Continuous (p.comp c)) (K : Ideal C) (hK : IsOpen (K : Set C)) :
    ∃ J : WeakIdealOfDefinitionIndex A, extendedIdeal c J ≤ K.comap p := by
  refine ⟨⟨hA.1.choose ⊓ K.comap (p.comp c), isWeakIdealOfDefinition_inf_of_isOpen_right
    hA.1.choose_spec (hK.preimage hpc)⟩, ?_⟩
  rw [extendedIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  exact inf_le_right

/-- **The extension of a ring map to a relative completion.** Let `c : A → P` be a ring map
out of a weakly admissible ring and `p : P → C` a ring map into a weakly admissible ring with
`p ∘ c` continuous. Then `p` extends to a continuous ring map `P^∧ → C` on the completion of
`P` over `A`. -/
theorem exists_continuous_lift_completionOver (hA : IsWeaklyAdmissible A)
    (hC : IsWeaklyAdmissible C) (c : A →+* P) (p : P →+* C) (hpc : Continuous (p.comp c)) :
    ∃ χ : CompletionOver c →+* C, Continuous χ ∧ χ.comp (CompletionOver.ofTarget c) = p := by
  classical
  choose J hJ using fun K : WeakIdealOfDefinitionIndex C ↦
    exists_extendedIdeal_le hA c p hpc K.1 K.2.1
  obtain ⟨χ, hχ⟩ := exists_ringHom_forall_weakIdeal_comp_eq hC
    (fun K ↦ liftStage c p K.1 (J K) (hJ K)) (fun K L hKL ↦ by
      have hKL' : extendedIdeal c (J K) ≤ L.1.comap p := (hJ K).trans (Ideal.comap_mono hKL)
      rw [liftStage_eq c p L.1 (J L) (J K) (hJ L) hKL', liftStage, liftStage,
        ← RingHom.comp_assoc, factor_comp_quotientMap p hKL])
  have hstage : ∀ K x, Ideal.Quotient.mk K.1 (χ x) = liftStage c p K.1 (J K) (hJ K) x :=
    fun K x ↦ congrArg (fun q ↦ q x) (hχ K)
  refine ⟨χ, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero χ ?_
    change Filter.Tendsto χ (nhds 0) (nhds (χ 0))
    rw [map_zero]
    refine (hasBasis_nhds_zero_isWeakIdealOfDefinition hC).tendsto_right_iff.mpr
      fun K hK ↦ ?_
    refine Filter.mem_of_superset ((CompletionOver.isOpen_ker_projection c
      (J ⟨K, hK⟩)).mem_nhds (Ideal.zero_mem _)) fun x hx ↦ ?_
    change CompletionOver.projection c (J ⟨K, hK⟩) x = 0 at hx
    change χ x ∈ K
    rw [← Ideal.Quotient.eq_zero_iff_mem, hstage ⟨K, hK⟩ x]
    change Ideal.quotientMap K p (hJ ⟨K, hK⟩) (CompletionOver.projection c (J ⟨K, hK⟩) x) = 0
    rw [hx, map_zero]
  · ext a
    refine eq_of_forall_weakIdeal_mk_eq hC fun K ↦ ?_
    rw [RingHom.comp_apply, hstage K]
    rfl

end Lift

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

section ClosedImmersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsLinearTopology C C] in
/-- A ring map with dense image onto a ring with an open ideal `K` is surjective modulo `K`. -/
private theorem surjective_quotientMap_of_denseRange (g : A →+* C) (hg : DenseRange g)
    (I : Ideal A) (K : Ideal C) (hK : IsOpen (K : Set C)) (hIK : I ≤ K.comap g) :
    Function.Surjective (Ideal.quotientMap K g hIK) := by
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := hg.exists_mem_open
    (hK.preimage (continuous_id.sub (continuous_const (y := c))))
    ⟨c, by simp⟩
  refine ⟨Ideal.Quotient.mk I a, ?_⟩
  change Ideal.Quotient.mk K (g a) = Ideal.Quotient.mk K c
  exact Ideal.Quotient.eq.mpr ha

/-- **The formal spectrum of a taut homomorphism with dense image is a closed immersion.** Let
`g : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over `S` which
is taut and has dense image. Then `Spf (g) : Spf C ⟶ Spf A` is a closed immersion.

Over the stage `Spec (A/I)` of `Spf A` the base change of `Spf (g)` is `Spec (C/J(I))`, with
`J(I)` the closure of `g(I)C`, because `g` is taut; the stage map is `Spec` of
`A/I ⟶ C/J(I)`, which is surjective because `g` has dense image and `J(I)` is open. The stages
cover `Spf A`, and being a closed immersion descends along such a covering. This is the
converse of the tautness and dense-image assertions of Stacks 0ANQ. -/
theorem isClosedImmersion_formalSpectrumMap_of_isTaut_of_denseRange
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E)
    (htaut : RingHom.IsTaut g.toRingHom) (hdense : DenseRange g.toRingHom) :
    IsClosedImmersion B S hS (formalSpectrumMap hA g) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  set Idx := ULift.{u + 1, u} (TopologicalRing.WeakIdealOfDefinitionIndex A) with hIdx
  set Yi : Idx → FppfSheaf B S hS :=
    fun i => (formalSpectrumDiagram D).obj (OrderDual.toDual i.down) with hYi
  set cc : ∀ i, Yi i ⟶ formalSpectrum D :=
    fun i => formalSpectrumInclusion D (OrderDual.toDual i.down) with hcc
  have hls : Sheaf.IsLocallySurjective (Limits.Sigma.desc cc) := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨fun {Q} f₁ f₂ h => Limits.colimit.hom_ext fun Kk => ?_⟩
    have hK : cc (ULift.up (OrderDual.ofDual Kk)) ≫ f₁ =
        cc (ULift.up (OrderDual.ofDual Kk)) ≫ f₂ := by
      rw [← Limits.Sigma.ι_comp_desc cc (ULift.up (OrderDual.ofDual Kk)),
        Category.assoc, Category.assoc, h]
    exact hK
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS Idx Yi cc hls ?_
  intro i
  obtain ⟨K, hK, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E g htaut i.down
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map (g.stageMap i.down K hIK)) := by
    change _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 g.toRingHom hIK)))
    exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      (surjective_quotientMap_of_denseRange g.toRingHom hdense i.down.1 K.1 K.2.1 hIK)
  have hrel : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (g.stageMap i.down K hIK))) := by
    have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
    have _ := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
    exact MorphismProperty.relative_map hclosed
  have hm := isClosedImmersion_of_isClosedImmersionInto B S hS _ hrel
  have hpb2 := IsPullback.of_hasPullback (formalSpectrumMap hA g) (cc i)
  have hw : (hsq.isoIsPullback _ _ hpb2).inv ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (g.stageMap i.down K hIK)) =
      pullback.snd (formalSpectrumMap hA g) (cc i) ≫ 𝟙 (Yi i) := by
    rw [Category.comp_id]
    exact hsq.isoIsPullback_inv_snd _ _ hpb2
  exact isClosedImmersion_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := (hsq.isoIsPullback _ _ hpb2).inv) (g := 𝟙 (Yi i))
      (CommSq.mk hw)) hm

end ClosedImmersion

section RelativeCompletion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A P : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing P]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The structure morphism over `S` attached to a quotient of a ring receiving a ring map from
`A` does not depend on the weak ideal of definition of `A` used to factor it. -/
private theorem overS_quotientMap_eq' {C : Type u} [CommRing C] (D : QuotientSystem B S hS A)
    (φ : A →+* C) (J L : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (K : Ideal C) (hJ : J.1 ≤ K.comap φ) (hL : L.1 ≤ K.comap φ) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ hJ)) ≫ D.overS J =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ hL)) ≫ D.overS L := by
  let M : TopologicalRing.WeakIdealOfDefinitionIndex A :=
    ⟨J.1 ⊓ L.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 L.2.1⟩
  rw [← D.compatible M J inf_le_left, ← D.compatible M L inf_le_right,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The quotient of the relative completion by an ideal containing the kernel of its projection
at `J` is a quotient of `P/JP`. -/
private theorem surjective_quotientMap_ofTarget (f : A →+* P)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (K : Ideal (TopologicalRing.CompletionOver f))
    (hK : RingHom.ker (TopologicalRing.CompletionOver.projection f J) ≤ K)
    (hJK : TopologicalRing.extendedIdeal f J ≤
      K.comap (TopologicalRing.CompletionOver.ofTarget f)) :
    Function.Surjective (Ideal.quotientMap K (TopologicalRing.CompletionOver.ofTarget f) hJK) := by
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (TopologicalRing.CompletionOver.projection f J c)
  have hdiff : TopologicalRing.CompletionOver.ofTarget f a - c ∈
      RingHom.ker (TopologicalRing.CompletionOver.projection f J) := by
    rw [RingHom.mem_ker, map_sub, TopologicalRing.CompletionOver.projection_ofTarget, ha,
      sub_self]
  exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.eq.mpr (hK hdiff)⟩

/-- **The relative completion of a finite type algebra over `S`.** If `f : A → P` is of finite
type, the completion `P^∧` of `P` over the weak ideals of definition of `A` carries a quotient
system over `S` together with a continuous map from `A` over `S` whose underlying ring map is
the canonical one. Each quotient of `P^∧` by a weak ideal of definition is a quotient of some
`P/JP`, which is of finite type over `A/J`, so its spectrum lies in the site because that of
`A/J` does; no condition on the size of the site is needed. -/
theorem exists_quotientSystem_completionOver_of_finiteType
    (hA : TopologicalRing.IsWeaklyAdmissible A) (f : A →+* P) (hf : f.FiniteType)
    (D : QuotientSystem B S hS A) :
    ∃ (E : QuotientSystem B S hS (TopologicalRing.CompletionOver f)) (g : ContinuousHom D E),
      g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f := by
  classical
  set c := TopologicalRing.CompletionOver.canonicalMap f with hc
  have hcont : Continuous c := TopologicalRing.continuous_canonicalMap f
  choose J hJ using fun K : TopologicalRing.WeakIdealOfDefinitionIndex
      (TopologicalRing.CompletionOver f) ↦ exists_weakIdeal_below_comap hA c hcont K
  refine ⟨{ inSite := ?_, overS := ?_, compatible := ?_ }, ⟨c, hcont, ?_⟩, rfl⟩
  · intro K
    obtain ⟨J₀, hJ₀⟩ := TopologicalRing.CompletionOver.exists_ker_projection_le_of_isOpen f hA.1
      K.2.1
    have hJK : TopologicalRing.extendedIdeal f J₀ ≤
        K.1.comap (TopologicalRing.CompletionOver.ofTarget f) := by
      rw [TopologicalRing.extendedIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro a ha
      refine hJ₀ ?_
      change TopologicalRing.CompletionOver.projection f J₀
        (TopologicalRing.CompletionOver.ofTarget f (f a)) = 0
      rw [TopologicalRing.CompletionOver.projection_ofTarget]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f ha)
    let q := Ideal.quotientMap K.1 (TopologicalRing.CompletionOver.ofTarget f) hJK
    let : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
        (surjective_quotientMap_ofTarget f J₀ K.1 hJ₀ hJK)
    refine Scheme.size_lt_of_isClosedImmersion (Spec.map (CommRingCat.ofHom q)) ?_
    let b : A ⧸ J₀.1 →+* P ⧸ TopologicalRing.extendedIdeal f J₀ :=
      Ideal.quotientMap (TopologicalRing.extendedIdeal f J₀) f Ideal.le_comap_map
    let : Algebra (A ⧸ J₀.1) (P ⧸ TopologicalRing.extendedIdeal f J₀) := b.toAlgebra
    have hbft : b.FiniteType := by
      refine RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk J₀.1) (g := b) ?_
      have : b.comp (Ideal.Quotient.mk J₀.1) =
          (Ideal.Quotient.mk (TopologicalRing.extendedIdeal f J₀)).comp f := RingHom.ext fun _ ↦ rfl
      rw [this]
      exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hf
    have : Algebra.FiniteType (A ⧸ J₀.1) (P ⧸ TopologicalRing.extendedIdeal f J₀) :=
      RingHom.finiteType_algebraMap.mp hbft
    exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (A ⧸ J₀.1) (P ⧸ TopologicalRing.extendedIdeal f J₀) (D.inSite J₀)
  · exact fun K ↦ Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 c (hJ K))) ≫ D.overS (J K)
  · intro K L hKL
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [TopologicalRing.factor_comp_quotientMap c hKL _ ((hJ K).trans (Ideal.comap_mono hKL))]
    exact overS_quotientMap_eq' B S hS D c (J K) (J L) L.1 _ _
  · exact fun L K h ↦ overS_quotientMap_eq' B S hS D c L (J K) K.1 h (hJ K)

attribute [local instance] sheaf_hasColimits in
/-- **The formal spectrum of a relative completion of finite type is an affine formal algebraic
space.** Let `f : A → P` be of finite type with `Spf A` an affine formal algebraic space. Then
`Spf P^∧` is an affine formal algebraic space as well, and so McQuillan.

`Spf P^∧ ⟶ Spf A` is taut and of finite type modulo every weak ideal of definition, so its base
change along a point of `Spf A` out of an affine object of the site is an affine object of the
site of finite type over it. This bounds the sections of `Spf P^∧` over affine objects, hence
over all objects; the affine charts then glue to show that `Spf P^∧ ⟶ Spf A` is representable,
and the set-theoretic condition of Stacks 0AIS passes from `Spf A` to `Spf P^∧` along a
representable morphism. -/
theorem isAffineFormalAlgebraicSpace_formalSpectrum_completionOver
    (hA : TopologicalRing.IsWeaklyAdmissible A) (f : A →+* P) (hf : f.FiniteType)
    (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (E : QuotientSystem B S hS (TopologicalRing.CompletionOver f)) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) := by
  classical
  have hA' : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletionOver f) :=
    TopologicalRing.completionOver_isWeaklyAdmissible f hA
  have htaut : RingHom.IsTaut g.toRingHom := by
    rw [hg]
    exact TopologicalRing.isTaut_canonicalMap f hA.1
  have hmod : TopologicalRing.FiniteTypeModuloEveryWeakIdeal g.toRingHom :=
    TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType' g.toRingHom
      htaut (by
        rw [hg]
        exact TopologicalRing.isTopologicallyOfFiniteType_canonicalMap f hA.1 hf)
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigFppfOver.topology B S hS
  let _ := CartesianColimit.small_of_setTheoreticCondition B S hS _ hX.1
  let _ := CartesianColimit.essentiallySmall_bigFppfOver B S hS
  have hsmall : FunctorToTypes.Small.{u} (formalSpectrum E).obj := by
    apply CartesianColimit.small_sections_of_affine B S hS
    intro U hU
    have : Small.{u} (G.obj U ⟶ formalSpectrum D) :=
      small_of_injective (Sheaf.sectionEquiv T (X := U) (F := formalSpectrum D)).injective
    have : Small.{u} (G.obj U ⟶ formalSpectrum E) :=
      CartesianColimit.small_hom_of_represented_fibers.{u} G (formalSpectrumMap hA g) U
        (fun ξ ↦ by
          obtain ⟨V, p, q, hp, -⟩ :=
            exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine B S hS hA hA' D E g
              hmod U hU ξ
          exact ⟨V, p, q, hp⟩)
    exact small_of_surjective (Sheaf.sectionEquiv T (X := U)).surjective
  have _ : MorphismProperty.RespectsIso
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have hzlA : IsZariskiLocalAtTarget (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have hzlT : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hrel : (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)).relative G (formalSpectrumMap hA g) := by
    refine CartesianColimit.relative_of_affineBaseChanges B S hS _
      (MorphismProperty.IsLocalAtTarget.inf _ _) _ (κ := 0)
      (lt_of_lt_of_le Cardinal.aleph0_pos B.aleph0_lt_cutoff.le) fun U hU ξ ↦ ?_
    obtain ⟨V, p, q, hq, hqa, hqt⟩ :=
      exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine B S hS hA hA' D E g
        hmod U hU ξ
    refine ⟨V, p, q, hq, ⟨hqa, hqt⟩, ?_⟩
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := hqa
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q)
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := hqt
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map q)).trans (le_max_right _ _)
  exact ⟨satisfiesSetTheoreticCondition_of_relativelyRepresentable B S hS
    (formalSpectrumMap hA g) hrel.rep hX.1, exists_thickeningColimit_formalSpectrum hA' E⟩

end RelativeCompletion

section Factorization

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The constant-coefficient inclusion into a polynomial ring in finitely many variables is of
finite type. -/
private theorem finiteType_mvPolynomial_C (r : ℕ) :
    letI : Algebra A (MvPolynomial (Fin r) A) :=
      (MvPolynomial.C : A →+* MvPolynomial (Fin r) A).toAlgebra
    Algebra.FiniteType A (MvPolynomial (Fin r) A) := by
  have h : (algebraMap A (MvPolynomial (Fin r) A)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  rwa [MvPolynomial.algebraMap_eq] at h

/-- **Factorization through affine space over a formal spectrum.** Let `g : A ⟶ C` be a
continuous homomorphism of weakly admissible topological rings over `S` which is taut and
topologically of finite type, with `Spf A` an affine formal algebraic space. Then there are an
integer `r` and a factorization

`Spf C ⟶ 𝔸ʳ_{Spf A} = Spf A{x₁, …, xᵣ} ⟶ Spf A`

of `Spf (g)`, where `A{x₁, …, xᵣ} = lim_I (A/I)[x₁, …, xᵣ]` is the completion of the polynomial
ring over the weak ideals of definition `I` of `A`, the second arrow is `Spf` of the canonical
map, and the first arrow is a closed immersion, `Spf` of a taut homomorphism with dense
image. The affine space `Spf A{x₁, …, xᵣ}` is a McQuillan affine formal algebraic space. -/
theorem exists_isClosedImmersion_affineSpace_factorization
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (E : QuotientSystem B S hS C)
    (g : ContinuousHom D E) (htaut : RingHom.IsTaut g.toRingHom)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom) :
    ∃ (r : ℕ) (E' : QuotientSystem B S hS
        (TopologicalRing.CompletionOver (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)))
      (π : ContinuousHom D E') (ι : ContinuousHom E' E),
      π.toRingHom = TopologicalRing.CompletionOver.canonicalMap MvPolynomial.C ∧
        _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E') ∧
        HasSomeSurjectivePresentation B S hS (formalSpectrum E') ∧
        RingHom.IsTaut ι.toRingHom ∧ DenseRange ι.toRingHom ∧
        IsClosedImmersion B S hS (formalSpectrumMap
          (TopologicalRing.completionOver_isWeaklyAdmissible MvPolynomial.C hA) ι) ∧
        formalSpectrumMap
            (TopologicalRing.completionOver_isWeaklyAdmissible MvPolynomial.C hA) ι ≫
          formalSpectrumMap hA π = formalSpectrumMap hA g := by
  obtain ⟨r, p, hpC, hpd⟩ := hft
  let c : A →+* MvPolynomial (Fin r) A := MvPolynomial.C
  have hA' : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletionOver c) :=
    TopologicalRing.completionOver_isWeaklyAdmissible c hA
  obtain ⟨E', π, hπ⟩ :=
    exists_quotientSystem_completionOver_of_finiteType B S hS hA c
      (finiteType_mvPolynomial_C r) D
  have hE'aff := isAffineFormalAlgebraicSpace_formalSpectrum_completionOver B S hS hA c
    (finiteType_mvPolynomial_C r) D hX E' π hπ
  have hpc : Continuous (p.comp c) := by
    change Continuous (p.comp MvPolynomial.C)
    rw [hpC]
    exact g.continuous
  obtain ⟨χ, hχc, hχp⟩ := TopologicalRing.exists_continuous_lift_completionOver hA hC c p hpc
  have hχcan : χ.comp (TopologicalRing.CompletionOver.canonicalMap c) = g.toRingHom := by
    rwa [← TopologicalRing.CompletionOver.ofTarget_comp, ← RingHom.comp_assoc, hχp]
  obtain ⟨ι, hι⟩ := exists_continuousHom_of_comp hA π g χ hχc (by rwa [hπ])
  have htautι : RingHom.IsTaut ι.toRingHom := by
    rw [hι]
    refine RingHom.isTaut_of_isTaut_comp _ χ
      (TopologicalRing.isTaut_canonicalMap c hA.1) hχc ?_
    rwa [hχcan]
  have hdense : DenseRange ι.toRingHom := by
    rw [hι]
    refine hpd.mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨TopologicalRing.CompletionOver.ofTarget c a, by
      rw [← RingHom.comp_apply, hχp]⟩
  refine ⟨r, E', π, ι, hπ, hE'aff,
    (hasAllSurjectivePresentations_formalSpectrum hA' E' hE'aff.1).hasSomeSurjectivePresentation,
    htautι, hdense,
    isClosedImmersion_formalSpectrumMap_of_isTaut_of_denseRange B S hS hA' hC E' E ι htautι
      hdense, ?_⟩
  refine formalSpectrumMap_comp hA hA' π ι g ?_
  rw [hι, hπ]
  exact hχcan.symm

end Factorization

end AlgebraicGeometry.FormalSpace

end
