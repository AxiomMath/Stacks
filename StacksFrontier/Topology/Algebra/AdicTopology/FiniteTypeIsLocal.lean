module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.RingTheory.RingHom.QuotientBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal

/-!
# Topological finite type is a local property

Tautness together with topological finite type satisfies the three locality axioms of
Situation 0CBA: the pair ascends along a completed étale localization diagram, descends along
such a diagram whose upper horizontal ring map is faithfully flat, and is preserved by finite
products of targets.

## Main results

* `TopologicalRing.topologicallyFiniteType_localizationPreserves`: tautness together with
  topological finite type ascends along a completed étale localization diagram.
* `TopologicalRing.topologicallyFiniteType_faithfullyFlatDescent`: it descends along such a
  diagram whose upper horizontal ring map is faithfully flat.
* `TopologicalRing.topologicallyFiniteType_finiteProductPreserves`: it is preserved by finite
  products of targets.
* `TopologicalRing.topologicallyFiniteType_propertyIsLocal`: it is a local property.
* `TopologicalRing.isTopologicallyOfFiniteType_of_commSq`: topological finite type propagates
  across a commuting square.
* `TopologicalRing.CompletionOver.denseRange_ofTarget`: the image of the canonical map
  `A → (A')^∧` from the ring being completed is dense.
* `TopologicalRing.isTopologicallyOfFiniteType_canonicalMap`: the completion of a ring of finite
  type is topologically of finite type.
* `TopologicalRing.isTopologicallyOfFiniteType_pi`: topological finite type for a finite
  product of targets.

## References

* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped TensorProduct

/-! ### Topological finite type across a commuting square -/

section CommSq

/-- A ring homomorphism out of a polynomial ring maps into a subring if it does so on the
constants and the variables. -/
private theorem mem_of_ringHom_mvPolynomial {R σ T : Type*} [CommRing R] [CommRing T]
    (F : MvPolynomial σ R →+* T) (S : Subring T) (hC : ∀ a, F (MvPolynomial.C a) ∈ S)
    (hX : ∀ i, F (MvPolynomial.X i) ∈ S) (p : MvPolynomial σ R) : F p ∈ S := by
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (hX i)

/-- Let `χ ∘ ρ = ψ ∘ φ` be a commuting square of ring homomorphisms, with `ψ` continuous into a
topological ring. If `φ` and `ψ` are topologically of finite type then so is `χ`. -/
public theorem isTopologicallyOfFiniteType_of_commSq
    {B A C B' : Type*} [CommRing B] [CommRing A] [TopologicalSpace A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [CommRing B']
    (φ : B →+* A) (ψ : A →+* C) (ρ : B →+* B') (χ : B' →+* C)
    (hψ : Continuous ψ) (hcomm : χ.comp ρ = ψ.comp φ)
    (hφ : IsTopologicallyOfFiniteType φ) (hψft : IsTopologicallyOfFiniteType ψ) :
    IsTopologicallyOfFiniteType χ := by
  obtain ⟨n, g, hgC, hgd⟩ := hφ
  obtain ⟨m, h, hhC, hhd⟩ := hψft
  set v : Fin n ⊕ Fin m → C :=
    Sum.elim (fun i : Fin n ↦ ψ (g (MvPolynomial.X i)))
      (fun j : Fin m ↦ h (MvPolynomial.X j)) with hv
  set G : MvPolynomial (Fin (n + m)) B' →+* C :=
    MvPolynomial.eval₂Hom χ (fun k ↦ v (finSumFinEquiv.symm k)) with hG
  have hGC : ∀ b, G (MvPolynomial.C b) = χ b := fun b ↦ MvPolynomial.eval₂Hom_C _ _ b
  have hGXl : ∀ i : Fin n,
      G (MvPolynomial.X (finSumFinEquiv (Sum.inl i))) = ψ (g (MvPolynomial.X i)) := by
    intro i
    rw [hG, MvPolynomial.eval₂Hom_X', Equiv.symm_apply_apply, hv, Sum.elim_inl]
  have hGXr : ∀ j : Fin m,
      G (MvPolynomial.X (finSumFinEquiv (Sum.inr j))) = h (MvPolynomial.X j) := by
    intro j
    rw [hG, MvPolynomial.eval₂Hom_X', Equiv.symm_apply_apply, hv, Sum.elim_inr]
  refine ⟨n + m, G, RingHom.ext hGC, ?_⟩
  have hsub : ∀ p : MvPolynomial (Fin n) B, ψ (g p) ∈ G.range :=
    mem_of_ringHom_mvPolynomial (ψ.comp g) G.range
      (fun a ↦ by
        have h2 : χ (ρ a) = ψ (φ a) := RingHom.congr_fun hcomm a
        exact ⟨MvPolynomial.C (ρ a), (hGC _).trans (h2.trans (congrArg ψ
          (RingHom.congr_fun hgC a)).symm)⟩)
      fun i ↦ RingHom.mem_range.mpr ⟨MvPolynomial.X (finSumFinEquiv (Sum.inl i)), hGXl i⟩
  have hψA : ∀ a : A, ψ a ∈ G.range.topologicalClosure := by
    intro a
    refine closure_minimal (fun c hc ↦ ?_) (Subring.isClosed_topologicalClosure _)
      (image_closure_subset_closure_image hψ ⟨a, hgd a, rfl⟩)
    obtain ⟨_, ⟨p, rfl⟩, rfl⟩ := hc
    exact Subring.le_topologicalClosure _ (hsub p)
  have hhS : ∀ p : MvPolynomial (Fin m) A, h p ∈ G.range.topologicalClosure :=
    mem_of_ringHom_mvPolynomial h _
      (fun a ↦ by
        rw [show h (MvPolynomial.C a) = ψ a from RingHom.congr_fun hhC a]; exact hψA a)
      fun j ↦ Subring.le_topologicalClosure _
        (RingHom.mem_range.mpr ⟨MvPolynomial.X (finSumFinEquiv (Sum.inr j)), hGXr j⟩)
  intro x
  exact closure_minimal (fun c hc ↦ by obtain ⟨p, rfl⟩ := hc; exact hhS p)
    (Subring.isClosed_topologicalClosure _) (hhd x)

end CommSq

/-! ### The ring being completed sits densely in its completion -/

namespace CompletionOver

section OfTarget

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace B]

end OfTarget

section Dense

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B]
  [CommRing A]

/-- The image of `A` is dense in the completion of `A` over `B`. -/
public lemma denseRange_ofTarget (f : B →+* A) (hB : IsWeaklyPreAdmissible B) :
    DenseRange (ofTarget f) := by
  intro x
  refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  have hpre : (fun y : CompletionOver f ↦ x + y) ⁻¹' t ∈ nhds (0 : CompletionOver f) := by
    refine ContinuousAt.preimage_mem_nhds ?_ (by simpa using ht)
    exact (continuous_const.add continuous_id).continuousAt
  obtain ⟨L, hL, hLt⟩ := (isTaut_canonicalMap f hB).2.mem_iff.mp hpre
  obtain ⟨I₀, hI₀⟩ := hB
  set J : WeakIdealOfDefinitionIndex B :=
    ⟨I₀ ⊓ L, isWeakIdealOfDefinition_inf_of_isOpen_right hI₀ hL⟩ with hJ
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (projection f J x)
  have hker : ofTarget f a - x ∈ RingHom.ker (projection f J) := by
    rw [RingHom.mem_ker, map_sub, projection_ofTarget, ha, sub_self]
  have hsub : (RingHom.ker (projection f J) : Set (CompletionOver f)) ⊆
      (fun y : CompletionOver f ↦ x + y) ⁻¹' t := by
    refine Set.Subset.trans ?_ hLt
    rw [ker_projection_eq_closure]
    exact closure_mono (Ideal.map_mono (le_trans inf_le_right le_rfl))
  exact ⟨ofTarget f a, by simpa using hsub hker, a, rfl⟩

end Dense

end CompletionOver

section FiniteTypeCompletion

universe u v

/-- The completion of `A` over `B` is topologically of finite type over `B` whenever `A` is of
finite type over `B`. -/
public theorem isTopologicallyOfFiniteType_canonicalMap
    {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B]
    [CommRing A] (f : B →+* A) (hB : IsWeaklyPreAdmissible B) (hf : f.FiniteType) :
    IsTopologicallyOfFiniteType (CompletionOver.canonicalMap f) := by
  let _ : Algebra B A := f.toAlgebra
  have hft : Algebra.FiniteType B A := hf
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  refine ⟨n, (CompletionOver.ofTarget f).comp p.toRingHom, RingHom.ext fun b ↦ ?_, ?_⟩
  · have hb : p.toRingHom (MvPolynomial.C b) = f b := p.commutes b
    rw [RingHom.comp_apply, RingHom.comp_apply, hb]
    rfl
  · refine Dense.mono (fun z hz ↦ ?_) (CompletionOver.denseRange_ofTarget f hB)
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨q, rfl⟩ := hp a
    exact ⟨q, rfl⟩

end FiniteTypeCompletion

/-! ### Finite type from étale -/

section Etale

/-- A homomorphism of finite presentation is of finite type. -/
public theorem finiteType_of_finitePresentation {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.FinitePresentation) : f.FiniteType := by
  let _ : Algebra R S := f.toAlgebra
  have _ : Algebra.FinitePresentation R S := hf
  exact Algebra.FiniteType.of_finitePresentation

/-- An étale homomorphism is of finite type. -/
public theorem finiteType_of_etale {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Etale) : f.FiniteType :=
  finiteType_of_finitePresentation (RingHom.Etale.finitePresentation hf)

end Etale

/-! ### Topological finite type for a finite product of targets -/

section Pi

/-- Topological finite type is preserved by a finite product of targets. -/
public theorem isTopologicallyOfFiniteType_pi {ι : Type*} [Finite ι] {B : Type*} [CommRing B]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    (f : ∀ i, B →+* A i) (h : ∀ i, IsTopologicallyOfFiniteType (f i)) :
    IsTopologicallyOfFiniteType (RingHom.pi f) := by
  classical
  cases nonempty_fintype ι
  choose n g hgC hgd using h
  set ι' := (Σ i : ι, Fin (n i)) ⊕ ι with hι'
  set e : ι' ≃ Fin (Fintype.card ι') := Fintype.equivFin ι' with he
  set v : Fin (Fintype.card ι') → ∀ i, A i := fun k ↦
    Sum.elim (fun q : Σ i : ι, Fin (n i) ↦ Pi.single q.1 (g q.1 (MvPolynomial.X q.2)))
      (fun i : ι ↦ Pi.single i 1) (e.symm k) with hvdef
  set G : MvPolynomial (Fin (Fintype.card ι')) B →+* ∀ i, A i :=
    MvPolynomial.eval₂Hom (RingHom.pi f) v with hG
  have hGC : ∀ b, G (MvPolynomial.C b) = RingHom.pi f b := fun b ↦
    MvPolynomial.eval₂Hom_C _ _ b
  have hGXl : ∀ (i : ι) (j : Fin (n i)), G (MvPolynomial.X (e (Sum.inl ⟨i, j⟩))) =
      Pi.single i (g i (MvPolynomial.X j)) := by
    intro i j
    simp only [hG, MvPolynomial.eval₂Hom_X', hvdef, Equiv.symm_apply_apply, Sum.elim_inl]
  have hGXr : ∀ i : ι, G (MvPolynomial.X (e (Sum.inr i))) = Pi.single i 1 := by
    intro i
    simp only [hG, MvPolynomial.eval₂Hom_X', hvdef, Equiv.symm_apply_apply, Sum.elim_inr]
  refine ⟨Fintype.card ι', G, RingHom.ext hGC, ?_⟩
  have hblock : ∀ (i : ι) (q : MvPolynomial (Fin (n i)) B),
      G (MvPolynomial.rename (fun j : Fin (n i) ↦ e (Sum.inl ⟨i, j⟩)) q) i = g i q := by
    intro i q
    induction q using MvPolynomial.induction_on with
    | C a =>
      have h1 : g i (MvPolynomial.C a) = f i a := RingHom.congr_fun (hgC i) a
      rw [MvPolynomial.rename_C, hGC, h1]
      rfl
    | add q r hq hr => rw [map_add, map_add, Pi.add_apply, hq, hr, map_add]
    | mul_X q j hq =>
      have h2 : G (MvPolynomial.rename (fun j : Fin (n i) ↦ e (Sum.inl ⟨i, j⟩))
            (q * MvPolynomial.X j)) =
          G (MvPolynomial.rename (fun j : Fin (n i) ↦ e (Sum.inl ⟨i, j⟩)) q) *
            Pi.single i (g i (MvPolynomial.X j)) := by
        rw [map_mul, map_mul, MvPolynomial.rename_X, hGXl i j]
      rw [h2, Pi.mul_apply, hq, Pi.single_eq_same, map_mul]
  intro x
  refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  rw [nhds_pi] at ht
  obtain ⟨s, -, V, hV, hVt⟩ := Filter.mem_pi.mp ht
  have hVmem : ∀ i, (V i ∩ Set.range (g i)).Nonempty := fun i ↦
    mem_closure_iff_nhds.mp (hgd i (x i)) (V i) (hV i)
  choose y hyV hyr using hVmem
  choose p hp using hyr
  have hcoord : ∀ i : ι, G (∑ i : ι, MvPolynomial.X (e (Sum.inr i)) *
      MvPolynomial.rename (fun j : Fin (n i) ↦ e (Sum.inl ⟨i, j⟩)) (p i)) i = g i (p i) := by
    intro i
    have hzero : ∀ b ∈ (Finset.univ : Finset ι), b ≠ i →
        G (MvPolynomial.X (e (Sum.inr b)) *
          MvPolynomial.rename (fun j : Fin (n b) ↦ e (Sum.inl ⟨b, j⟩)) (p b)) i = 0 := by
      intro b _ hb
      rw [map_mul, Pi.mul_apply, hGXr b, Pi.single_eq_of_ne (Ne.symm hb), zero_mul]
    rw [map_sum, Finset.sum_apply,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero, map_mul, Pi.mul_apply,
      hGXr i, Pi.single_eq_same, one_mul, hblock i (p i)]
  refine ⟨G (∑ i : ι, MvPolynomial.X (e (Sum.inr i)) *
    MvPolynomial.rename (fun j : Fin (n i) ↦ e (Sum.inl ⟨i, j⟩)) (p i)), hVt ?_, _, rfl⟩
  intro i _
  rw [hcoord i, hp i]
  exact hyV i

end Pi

/-! ### Properties of a quotient of a faithfully flat or finitely presented map -/

section BaseChange

universe u

/-- A property of ring homomorphisms stable under base change and respecting isomorphisms holds
for the induced map `A ⧸ I → A' ⧸ IA'`. -/
public theorem quotientMap_of_isStableUnderBaseChange
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hbc : RingHom.IsStableUnderBaseChange @P) (hiso : RingHom.RespectsIso @P)
    {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A') (hf : P f) (I : Ideal A) :
    P (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  let _ : Algebra A A' := f.toAlgebra
  have h1 : P (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A')) := hbc.tensorProduct (A ⧸ I) hf
  have h2 := hiso.1 (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A'))
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm.toRingEquiv h1
  have heq : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A'
        I).symm.toRingEquiv.toRingHom.comp (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A')) =
      Ideal.quotientMap (I.map f) f Ideal.le_comap_map :=
    RingHom.ext fun z ↦
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm.commutes z
  exact heq ▸ h2

/-- `A ⧸ I → A' ⧸ IA'` is faithfully flat whenever `A → A'` is. -/
public theorem faithfullyFlat_quotientMap {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (hf : f.FaithfullyFlat) (I : Ideal A) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FaithfullyFlat :=
  quotientMap_of_isStableUnderBaseChange RingHom.FaithfullyFlat.isStableUnderBaseChange
    RingHom.FaithfullyFlat.respectsIso f hf I

/-- `A ⧸ I → A' ⧸ IA'` is of finite presentation whenever `A → A'` is. -/
public theorem finitePresentation_quotientMap {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (hf : f.FinitePresentation) (I : Ideal A) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FinitePresentation :=
  quotientMap_of_isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange
    RingHom.finitePresentation_respectsIso f hf I

end BaseChange

/-! ### The three locality axioms -/

section Local

universe u

/-- Tautness together with topological finite type ascends along a completed étale localization
diagram of countably indexed weakly admissible rings. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_localizationPreserves :
    LocalizationPreserves.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP
  refine ⟨isTaut_localizationPreserves D hA hB hA' hB' hP.1, ?_⟩
  exact isTopologicallyOfFiniteType_of_commSq D.map (CompletionOver.canonicalMap D.toA')
    (CompletionOver.canonicalMap D.toB') D.completedMap (continuous_canonicalMap D.toA')
    D.commutes.symm hP.2
    (isTopologicallyOfFiniteType_canonicalMap D.toA' D.weaklyAdmissibleA.1
      (finiteType_of_etale D.etaleA))

/-- Tautness together with topological finite type descends along a completed étale localization
diagram whose upper horizontal ring map is faithfully flat. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_faithfullyFlatDescent :
    FaithfullyFlatDescent.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hff hP
  have htaut : RingHom.IsTaut D.map := isTaut_faithfullyFlatDescent D hA hB hA' hB' hff hP.1
  have hκAc : Continuous (CompletionOver.canonicalMap D.toA') := continuous_canonicalMap _
  have hcompTaut : RingHom.IsTaut ((CompletionOver.canonicalMap D.toA').comp D.map) := by
    rw [D.commutes]
    exact RingHom.isTaut_comp (CompletionOver.canonicalMap D.toB') D.completedMap
      (continuous_canonicalMap D.toB') D.continuousCompletedMap
      (isTaut_canonicalMap D.toB' D.weaklyAdmissibleB.1) hP.1
  have hcompFT :
      IsTopologicallyOfFiniteType ((CompletionOver.canonicalMap D.toA').comp D.map) := by
    rw [D.commutes]
    exact isTopologicallyOfFiniteType_of_commSq (CompletionOver.canonicalMap D.toB')
      D.completedMap (RingHom.id B)
      (D.completedMap.comp (CompletionOver.canonicalMap D.toB')) D.continuousCompletedMap
      (RingHom.comp_id _)
      (isTopologicallyOfFiniteType_canonicalMap D.toB' D.weaklyAdmissibleB.1
        (finiteType_of_etale D.etaleB)) hP.2
  have hcompA : FiniteTypeModuloEveryWeakIdeal ((CompletionOver.canonicalMap D.toA').comp D.map) :=
    ((finiteType_tfae' ((CompletionOver.canonicalMap D.toA').comp D.map)
      (hκAc.comp D.continuousMap) D.weaklyAdmissibleB hA'.1 D.countableB).out 3 1).mp
      (And.intro hcompTaut hcompFT)
  have hmapA : FiniteTypeModuloEveryWeakIdeal D.map := by
    refine ⟨htaut, fun J hJ ↦ ?_⟩
    set I : Ideal A := Ideal.closure (J.map D.map) with hI
    have hIwid : IsWeakIdealOfDefinition I :=
      ⟨htaut.1 J hJ.1, fun _ hy ↦ closure_map_le_topologicalNilradical D.map
        D.continuousMap J (fun z hz ↦ hJ.2 z hz) hy⟩
    set Ĩ : WeakIdealOfDefinitionIndex A := ⟨I, hIwid⟩
    set Î : Ideal (CompletionOver D.toA') :=
      Ideal.closure (J.map ((CompletionOver.canonicalMap D.toA').comp D.map))
    have hÎle : Î ≤ RingHom.ker (CompletionOver.projection D.toA' Ĩ) := by
      intro z hz
      refine closure_minimal ?_ ((RingHom.ker (CompletionOver.projection D.toA' Ĩ)).toAddSubgroup
        |>.isClosed_of_isOpen (CompletionOver.isOpen_ker_projection D.toA' Ĩ)) hz
      refine SetLike.coe_subset_coe.mpr (Ideal.map_le_iff_le_comap.mpr fun b hb ↦ ?_)
      have hzero : Ideal.Quotient.mk (I.map D.toA') (D.toA' (D.map b)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _
          (subset_closure (Ideal.mem_map_of_mem _ hb)))
      exact RingHom.mem_ker.mpr hzero
    set π : (CompletionOver D.toA' ⧸ Î) →+* A' ⧸ I.map D.toA' :=
      Ideal.Quotient.lift Î (CompletionOver.projection D.toA' Ĩ)
        (fun z hz ↦ RingHom.mem_ker.mp (hÎle hz)) with hπ
    have hπsurj : Function.Surjective π := by
      intro w
      obtain ⟨z, hz⟩ := CompletionOver.projection_surjective D.toA' Ĩ w
      exact ⟨Ideal.Quotient.mk Î z, by rw [hπ, Ideal.Quotient.lift_mk]; exact hz⟩
    have heq : (Ideal.quotientMap (I.map D.toA') D.toA' Ideal.le_comap_map).comp
          (Ideal.quotientMap I D.map (Ideal.map_le_iff_le_comap.mp subset_closure)) =
        π.comp (Ideal.quotientMap Î ((CompletionOver.canonicalMap D.toA').comp D.map)
          (Ideal.map_le_iff_le_comap.mp subset_closure)) := by
      refine RingHom.ext fun z ↦ ?_
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hl : (Ideal.quotientMap (I.map D.toA') D.toA' Ideal.le_comap_map).comp
            (Ideal.quotientMap I D.map (Ideal.map_le_iff_le_comap.mp subset_closure))
            (Ideal.Quotient.mk J b) =
          Ideal.Quotient.mk (I.map D.toA') (D.toA' (D.map b)) := by
        simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
      have hr : π.comp (Ideal.quotientMap Î ((CompletionOver.canonicalMap D.toA').comp D.map)
            (Ideal.map_le_iff_le_comap.mp subset_closure)) (Ideal.Quotient.mk J b) =
          Ideal.Quotient.mk (I.map D.toA') (D.toA' (D.map b)) := by
        rw [RingHom.comp_apply, Ideal.quotientMap_mk, hπ]
        exact Ideal.Quotient.lift_mk Î (CompletionOver.projection D.toA' Ĩ) _
      exact hl.trans hr.symm
    have hcomp : ((Ideal.quotientMap (I.map D.toA') D.toA' Ideal.le_comap_map).comp
        (Ideal.quotientMap I D.map (Ideal.map_le_iff_le_comap.mp subset_closure))).FiniteType := by
      rw [heq]
      exact (RingHom.FiniteType.of_surjective π hπsurj).comp (hcompA.2 J hJ)
    exact RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation hcomp
      (faithfullyFlat_quotientMap D.toA' hff I)
      (finitePresentation_quotientMap D.toA' (RingHom.Etale.finitePresentation D.etaleA) I)
  exact ((finiteType_tfae' D.map D.continuousMap D.weaklyAdmissibleB D.weaklyAdmissibleA
    D.countableB).out 1 3).mp hmapA

/-- Tautness together with topological finite type is preserved by finite products of
targets. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_finiteProductPreserves :
    FiniteProductPreserves.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f) := by
  intro B _ _ _ _ hBwa hBcount ι _ A _ _ _ _ hAwa hAcount f hfc hCB hCA hP
  exact ⟨isTaut_finiteProductPreserves hBwa hBcount A hAwa hAcount f hfc hCB hCA
      (fun i ↦ (hP i).1),
    isTopologicallyOfFiniteType_pi f (fun i ↦ (hP i).2)⟩

/-- Tautness together with topological finite type is a local property of morphisms of
countably indexed weakly admissible topological rings. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_propertyIsLocal :
    PropertyIsLocal.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f) :=
  ⟨topologicallyFiniteType_localizationPreserves, topologicallyFiniteType_faithfullyFlatDescent,
    topologicallyFiniteType_finiteProductPreserves⟩

end Local

end TopologicalRing

end
