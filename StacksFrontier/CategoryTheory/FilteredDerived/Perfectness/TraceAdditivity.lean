module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
import all StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cyclicity and additivity of the trace on perfect complexes

Properties of `CategoryTheory.FilteredDerived.perfectDerivedTrace`, the trace of an endomorphism
of a perfect complex computed on a bounded complex of finite projective modules. They are
proved on such a representative from the degreewise traces, whose lemmas are private to
`StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace` and are read here through
`import all`.

## Main results

* `CategoryTheory.FilteredDerived.perfectDerivedTrace_comp_comm`: the trace is cyclic,
  `Tr(a ≫ b) = Tr(b ≫ a)` for morphisms between two perfect complexes.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_add`: the trace is additive in the
  endomorphism.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_sum_of_sum_comp_eq_id`: the trace
  through a finite decomposition of the identity is the sum of the traces of the diagonal
  blocks.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-- A morphism `Q P ⟶ Q L` out of a bounded complex of finite projective modules is the image of a
morphism of complexes. -/
@[sga "5 IIIB 5.7" "partial"]
private lemma exists_Q_map_eq_of_finiteProjectiveComplex (R : Type u) [Ring R]
    {P : CochainComplex (ModuleCat.{v} R) ℤ} (hP : finiteProjectiveComplex R P)
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    (φ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :
    ∃ g : P ⟶ L, DerivedCategory.Q.map g = φ := by
  let : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    let : P.IsStrictlyLE d := hd
    let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
    let (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  obtain ⟨gh, hgh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj L)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P ≫ φ ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective gh
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P),
    ← DerivedCategory.quotientCompQhIso_hom_naturality, hgh]
  simp

/-- **The trace on perfect complexes is cyclic**: for `a : K ⟶ L` and `b : L ⟶ K` between perfect
complexes, `Tr(a ≫ b | K) = Tr(b ≫ a | L)`. -/
@[sga "5 IIIB 1.1" "more general",
  sga "5 IIIB 5.7" "more general",
  sga "5 IIIB 5.8" "special case",
  sga "6 I 8.3" "special case",
  sga "6 I 8.5" "special case"]
public theorem perfectDerivedTrace_comp_comm (R : Type u) [Ring R]
    (K L : PerfectDerivedCategory.{u, v} R) (a : K.obj ⟶ L.obj) (b : L.obj ⟶ K.obj) :
    perfectDerivedTrace R K (a ≫ b) = perfectDerivedTrace R L (b ≫ a) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isPerfect_iff R K.obj).mp K.property
  obtain ⟨P', hP', ⟨eP'⟩⟩ := (isPerfect_iff R L.obj).mp L.property
  obtain ⟨a', ha'⟩ := exists_Q_map_eq_of_finiteProjectiveComplex R hP P' (eP.hom ≫ a ≫ eP'.inv)
  obtain ⟨b', hb'⟩ := exists_Q_map_eq_of_finiteProjectiveComplex R hP' P (eP'.hom ≫ b ≫ eP.inv)
  rw [perfectDerivedTrace_eq_alternatingTrace R K (a ≫ b) P hP eP (a' ≫ b')
      (by simp [Functor.map_comp, ha', hb']),
    perfectDerivedTrace_eq_alternatingTrace R L (b ≫ a) P' hP' eP' (b' ≫ a')
      (by simp [Functor.map_comp, ha', hb'])]
  exact alternatingTrace_cyclic R P P' hP hP' a' b'

/-- **The trace on a perfect complex is additive**: `Tr(f + g) = Tr(f) + Tr(g)`. -/
public theorem perfectDerivedTrace_add (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) (f g : K.obj ⟶ K.obj) :
    perfectDerivedTrace R K (f + g) = perfectDerivedTrace R K f + perfectDerivedTrace R K g := by
  classical
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isPerfect_iff R K.obj).mp K.property
  obtain ⟨f', hf'⟩ := exists_Q_map_eq_of_finiteProjectiveComplex R hP P (eP.hom ≫ f ≫ eP.inv)
  obtain ⟨g', hg'⟩ := exists_Q_map_eq_of_finiteProjectiveComplex R hP P (eP.hom ≫ g ≫ eP.inv)
  rw [perfectDerivedTrace_eq_alternatingTrace R K (f + g) P hP eP (f' + g')
      (by simp [Functor.map_add, hf', hg', Preadditive.comp_add, Preadditive.add_comp]),
    perfectDerivedTrace_eq_alternatingTrace R K f P hP eP f' hf',
    perfectDerivedTrace_eq_alternatingTrace R K g P hP eP g' hg']
  show (∑ᶠ i : ℤ, signedTraceAt R P hP i ((f' + g').f i)) =
    (∑ᶠ i : ℤ, signedTraceAt R P hP i (f'.f i)) + ∑ᶠ i : ℤ, signedTraceAt R P hP i (g'.f i)
  have hfin := finite_nonzero_degrees R P hP
  rw [← finsum_add_distrib (hfin.subset (signedTraceAt_support_subset R P hP (fun i => f'.f i)))
    (hfin.subset (signedTraceAt_support_subset R P hP (fun i => g'.f i)))]
  refine finsum_congr fun i => ?_
  simp only [signedTraceAt, HomologicalComplex.add_f_apply, traceAt_add]
  split_ifs <;> abel

/-- The trace of the zero endomorphism vanishes. -/
public theorem perfectDerivedTrace_zero (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) :
    perfectDerivedTrace R K 0 = 0 := by
  have h := perfectDerivedTrace_add R K 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **The trace on a perfect complex is additive over finite sums of endomorphisms.** -/
public theorem perfectDerivedTrace_sum (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) {ι : Type*} (s : Finset ι) (f : ι → (K.obj ⟶ K.obj)) :
    perfectDerivedTrace R K (∑ i ∈ s, f i) = ∑ i ∈ s, perfectDerivedTrace R K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using perfectDerivedTrace_zero R K
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, perfectDerivedTrace_add, ih]

/-- **The trace through a finite decomposition of the identity.**  If `K` is perfect and
`∑ᵢ pᵢ ≫ ιᵢ = 𝟙` for morphisms `pᵢ : K ⟶ Pᵢ`, `ιᵢ : Pᵢ ⟶ K` with each `Pᵢ` perfect (for
instance the projections and inclusions of a finite direct sum), then
`Tr(f | K) = ∑ᵢ Tr(ιᵢ ≫ f ≫ pᵢ | Pᵢ)`: the trace is the sum of the traces of the diagonal
blocks.  No orthogonality `ιᵢ ≫ pⱼ = 0` is needed. -/
public theorem perfectDerivedTrace_eq_sum_of_sum_comp_eq_id (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) {ι : Type*} (s : Finset ι)
    (P : ι → PerfectDerivedCategory.{u, v} R) (p : ∀ i, K.obj ⟶ (P i).obj)
    (inc : ∀ i, (P i).obj ⟶ K.obj) (h : ∑ i ∈ s, p i ≫ inc i = 𝟙 K.obj)
    (f : K.obj ⟶ K.obj) :
    perfectDerivedTrace R K f = ∑ i ∈ s, perfectDerivedTrace R (P i) (inc i ≫ f ≫ p i) := by
  have hf : f = ∑ i ∈ s, p i ≫ (inc i ≫ f) := by
    simp_rw [← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]
  conv_lhs => rw [hf]
  rw [perfectDerivedTrace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [perfectDerivedTrace_comp_comm R K (P i) (p i) (inc i ≫ f), Category.assoc]

end CategoryTheory.FilteredDerived

end
