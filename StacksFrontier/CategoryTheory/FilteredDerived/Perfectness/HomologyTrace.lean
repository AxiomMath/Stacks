module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a perfect complex with projective cohomology

Let `R` be a ring and `K` a perfect complex of `R`-modules whose cohomology modules `H^i(K)` are
all finite projective. For an endomorphism `f` of `K` in the derived category,

`Tr(f | K) = ∑_i (-1)^i Tr(H^i(f) | H^i(K))`

in `R^natural`.

## Main definitions

* `CategoryTheory.FilteredDerived.signedByDegree`: the sign `(-1)^i` applied to an element of
  `R^natural`.
* `CategoryTheory.FilteredDerived.homologyTrace`: the trace of the map induced on the `i`-th
  cohomology of a complex.
* `CategoryTheory.FilteredDerived.derivedHomologyTrace`: the trace of the map induced on the
  `i`-th cohomology of an object of the derived category.

## Main results

* `CategoryTheory.FilteredDerived.projectiveModuleTrace_shortExact`: additivity of the trace of
  finite projective modules along a short exact sequence whose quotient is projective.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_fourTerm`: for an exact sequence
  `0 → A → B → C → D → 0` with `B, C, D` finite projective, `A` is finite projective and
  `Tr(B) + Tr(D) = Tr(A) + Tr(C)`.
* `CategoryTheory.FilteredDerived.alternatingTrace_eq_homologyTrace`: for a bounded complex of
  finite projective modules with finite projective cohomology, the alternating sum of the traces
  on the terms equals the alternating sum of the traces on cohomology.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_homologyTrace`: for a perfect complex `K`
  with finite projective cohomology, `Tr(f | K) = ∑_i (-1)^i Tr(H^i(f) | H^i(K))`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9
* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

section Modules

variable (R : Type u) [Ring R]

/-- For a short exact sequence `0 → A → B → C → 0` of finite projective modules with compatible
endomorphisms `α`, `β`, `γ`, `Tr(β) = Tr(α) + Tr(γ)`. -/
public lemma projectiveModuleTrace_shortExact
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g)
    (α : Module.End R A) (β : Module.End R B) (γ : Module.End R C)
    (hα : β.comp f = f.comp α) (hγ : g.comp β = γ.comp g) :
    Stacks.Trace.projectiveModuleTrace R B β =
      Stacks.Trace.projectiveModuleTrace R A α +
        Stacks.Trace.projectiveModuleTrace R C γ := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  let E := Function.Exact.splitSurjectiveEquiv h hf ⟨l, hl⟩
  set e : B ≃ₗ[R] A × C := E.1
  have he₁ : f = e.symm.toLinearMap.comp (LinearMap.inl R A C) := E.2.1
  have he₂ (x : B) : g x = (e x).2 := LinearMap.congr_fun E.2.2 x
  refine projectiveModuleTrace_splitExact R e.symm f g α β γ he₁.symm ?_ hα hγ
  ext x <;> simp [he₂]

/-- A submodule `I ⊆ C` which is the kernel of a surjection `C → D` onto a finite projective
module, with `C` finite projective, is finite projective. -/
@[sga "6 I 1.3" "more general"]
lemma finite_projective_ker_of_surjective
    {C D : Type v} [AddCommGroup C] [AddCommGroup D] [Module R C] [Module R D]
    [Module.Finite R C] [Module.Projective R C] [Module.Projective R D]
    {c : C →ₗ[R] D} (hc : Function.Surjective c) :
    Module.Finite R (LinearMap.ker c) ∧ Module.Projective R (LinearMap.ker c) := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property c LinearMap.id hc
  have hl' (x : D) : c (l x) = x := LinearMap.congr_fun hl x
  let s : C →ₗ[R] LinearMap.ker c :=
    LinearMap.codRestrict _ (LinearMap.id - l.comp c) (fun x => by simp [hl'])
  have hs : s.comp (LinearMap.ker c).subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [s, LinearMap.mem_ker.1 hx]
  have hsurj : Function.Surjective s := fun y =>
    ⟨(LinearMap.ker c).subtype y, by simpa using LinearMap.congr_fun hs y⟩
  exact ⟨Module.Finite.of_surjective s hsurj,
    Module.Projective.of_split (LinearMap.ker c).subtype s hs⟩

/-- For an exact sequence `0 → A → B → C → D → 0` with `B` finite projective and `C → D` having a
finite projective kernel, `A` is finite projective. -/
lemma finite_projective_of_shortExact
    {A B I : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup I]
    [Module R A] [Module R B] [Module R I]
    [Module.Finite R B] [Module.Projective R B] [Module.Projective R I]
    {a : A →ₗ[R] B} {b : B →ₗ[R] I} (ha : Function.Injective a) (hb : Function.Surjective b)
    (hab : Function.Exact a b) :
    Module.Finite R A ∧ Module.Projective R A := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property b LinearMap.id hb
  let E := Function.Exact.splitSurjectiveEquiv hab ha ⟨l, hl⟩
  have he₁ : a = E.1.symm.toLinearMap.comp (LinearMap.inl R A I) := E.2.1
  let s : B →ₗ[R] A := (LinearMap.fst R A I).comp E.1.toLinearMap
  have hs : s.comp a = LinearMap.id := by
    rw [he₁]
    ext x
    simp [s]
  have hsurj : Function.Surjective s := fun y => ⟨a y, by simpa using LinearMap.congr_fun hs y⟩
  exact ⟨Module.Finite.of_surjective s hsurj, Module.Projective.of_split a s hs⟩

/-- For an exact sequence `A → B → C → D`, the map `B → C` corestricts to a surjection onto the
kernel of `C → D`, and `A → B → ker c` is still exact. -/
private theorem exists_surjective_exact_ker
    {A B C D : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    {a : A →ₗ[R] B} {b : B →ₗ[R] C} {c : C →ₗ[R] D}
    (hab : Function.Exact a b) (hbc : Function.Exact b c) :
    ∃ b' : B →ₗ[R] LinearMap.ker c, (∀ x, (b' x : C) = b x) ∧ Function.Surjective b' ∧
      Function.Exact a b' := by
  refine ⟨LinearMap.codRestrict _ b (fun x => (hbc (b x)).2 ⟨x, rfl⟩), fun x => rfl, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (hbc y).1 hy
    exact ⟨x, rfl⟩
  · intro x
    rw [← hab x]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **The four-term exact sequence and projectivity.** For an exact sequence
`0 → A → B → C → D → 0` with `B`, `C`, `D` finite projective, `A` is finite projective. -/
public lemma finite_projective_of_fourTerm
    {A B C D : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Projective R D]
    {a : A →ₗ[R] B} {b : B →ₗ[R] C} {c : C →ₗ[R] D}
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hc : Function.Surjective c) :
    Module.Finite R A ∧ Module.Projective R A := by
  obtain ⟨_, hI⟩ := finite_projective_ker_of_surjective R hc
  obtain ⟨b', hb'x, hb', hab'⟩ := exists_surjective_exact_ker R hab hbc
  exact finite_projective_of_shortExact R ha hb' hab'

/-- **Additivity of the trace along a four-term exact sequence.** For an exact sequence
`0 → A → B → C → D → 0` of finite projective modules with a compatible endomorphism,
`Tr(B) + Tr(D) = Tr(A) + Tr(C)`. -/
public lemma projectiveModuleTrace_fourTerm
    {A B C D : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite R D] [Module.Projective R D]
    {a : A →ₗ[R] B} {b : B →ₗ[R] C} {c : C →ₗ[R] D}
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hc : Function.Surjective c)
    (α : Module.End R A) (β : Module.End R B) (γ : Module.End R C) (δ : Module.End R D)
    (hα : β.comp a = a.comp α) (hβ : γ.comp b = b.comp β) (hγ : c.comp γ = δ.comp c) :
    Stacks.Trace.projectiveModuleTrace R B β + Stacks.Trace.projectiveModuleTrace R D δ =
      Stacks.Trace.projectiveModuleTrace R A α + Stacks.Trace.projectiveModuleTrace R C γ := by
  obtain ⟨_, _⟩ := finite_projective_ker_of_surjective R hc
  have hγI (x : C) (hx : x ∈ LinearMap.ker c) : γ x ∈ LinearMap.ker c := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hγ, LinearMap.comp_apply, hx, map_zero]
  let γI : Module.End R (LinearMap.ker c) := γ.restrict hγI
  obtain ⟨b', hb'x, hb', hab'⟩ := exists_surjective_exact_ker R hab hbc
  have h₁ := projectiveModuleTrace_shortExact R ha hb' hab' α β γI hα (by
    ext x
    simpa [γI, hb'x] using (LinearMap.congr_fun hβ x).symm)
  have hI : Function.Exact (LinearMap.ker c).subtype c := by
    intro x
    simp
  have h₂ := projectiveModuleTrace_shortExact R (LinearMap.ker c).injective_subtype hc hI γI γ δ
    (by ext x; simp [γI]) hγ
  rw [h₁, h₂]
  abel

end Modules

section Complexes

variable (R : Type u) [Ring R]

/-- The sign `(-1)^i` applied to an element of `R^natural`. -/
public def signedByDegree (i : ℤ) (x : AdditiveCommutatorQuotient R) :
    AdditiveCommutatorQuotient R :=
  if Even i then x else -x

/-- `signedByDegree R i` is additive. -/
lemma signedByDegree_add (i : ℤ) (x y : AdditiveCommutatorQuotient R) :
    signedByDegree R i (x + y) = signedByDegree R i x + signedByDegree R i y := by
  unfold signedByDegree
  split_ifs <;> abel

/-- `signedByDegree R i` commutes with negation. -/
lemma signedByDegree_neg (i : ℤ) (x : AdditiveCommutatorQuotient R) :
    signedByDegree R i (-x) = -signedByDegree R i x := by
  unfold signedByDegree
  split_ifs <;> abel

/-- The sign in degree `i + 1` is the opposite of the sign in degree `i`. -/
lemma signedByDegree_succ (i : ℤ) (x : AdditiveCommutatorQuotient R) :
    signedByDegree R (i + 1) x = -signedByDegree R i x := by
  unfold signedByDegree
  by_cases hi : Even i <;> simp [hi]

/-- `signedByDegree R i` sends `0` to `0`. -/
lemma signedByDegree_zero (i : ℤ) : signedByDegree R i 0 = 0 := by
  unfold signedByDegree
  split_ifs <;> simp

variable {R} (P : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The inclusion of the cycles into the `i`-th term is injective. -/
lemma injective_iCycles (i : ℤ) : Function.Injective (P.iCycles i).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The projection from the cycles onto the `i`-th cohomology is surjective. -/
lemma surjective_homologyπ (i : ℤ) : Function.Surjective (P.homologyπ i).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The sequence `Z^i → P^i → Z^{i+1}` is exact. -/
lemma exact_iCycles_toCycles (i : ℤ) :
    Function.Exact (P.iCycles i).hom (P.toCycles i (i + 1)).hom := by
  have hS : (ShortComplex.mk (P.iCycles i) (P.d i (i + 1)) (P.iCycles_d i (i + 1))).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (P.cyclesIsKernel i (i + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hS
  have hd (x : P.X i) : (P.iCycles (i + 1)).hom ((P.toCycles i (i + 1)).hom x) =
      (P.d i (i + 1)).hom x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, P.toCycles_i]
  refine fun x => ⟨fun hx => hS x (by rw [← hd, hx, map_zero]), ?_⟩
  rintro ⟨z, rfl⟩
  apply injective_iCycles P (i + 1)
  rw [hd, map_zero, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, P.iCycles_d]
  rfl

/-- The sequence `P^i → Z^{i+1} → H^{i+1}` is exact. -/
lemma exact_toCycles_homologyπ (i : ℤ) :
    Function.Exact (P.toCycles i (i + 1)).hom (P.homologyπ (i + 1)).hom := by
  have hS : (ShortComplex.mk (P.toCycles i (i + 1)) (P.homologyπ (i + 1))
      (P.toCycles_comp_homologyπ i (i + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (P.homologyIsCokernel i (i + 1) (by simp))
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS

/-- The cycles in a degree where the complex is zero are trivial. -/
lemma subsingleton_cycles_of_isZero (i : ℤ) (h : IsZero (P.X i)) : Subsingleton (P.cycles i) := by
  have := ModuleCat.subsingleton_of_isZero h
  exact (injective_iCycles P i).subsingleton

/-- The cohomology in a degree where the complex is zero is trivial. -/
lemma subsingleton_homology_of_isZero (i : ℤ) (h : IsZero (P.X i)) :
    Subsingleton (P.homology i) := by
  have := subsingleton_cycles_of_isZero P i h
  exact (surjective_homologyπ P i).subsingleton

/-- A trivial module is finite projective. -/
lemma finite_projective_of_subsingleton (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.Finite R M ∧ Module.Projective R M :=
  ⟨inferInstance, Module.Projective.of_free⟩

variable {P}

/-- In a bounded complex of finite projective modules whose cohomology is finite projective,
every module of cycles is finite projective. -/
lemma finite_projective_cycles (hP : finiteProjectiveComplex R P)
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i)) (i : ℤ) :
    Module.Finite R (P.cycles i) ∧ Module.Projective R (P.cycles i) := by
  obtain ⟨hi, hhi⟩ := hP.1.2
  have : P.IsStrictlyLE hi := hhi
  suffices h : ∀ m : ℕ, ∀ i : ℤ, hi < i + m →
      Module.Finite R (P.cycles i) ∧ Module.Projective R (P.cycles i) by
    exact h (hi - i + 1).toNat i (by omega)
  intro m
  induction m with
  | zero =>
    intro i hi'
    have := subsingleton_cycles_of_isZero P i
      (CochainComplex.isZero_of_isStrictlyLE P hi i (by omega))
    exact finite_projective_of_subsingleton _
  | succ m ih =>
    intro i hi'
    obtain ⟨h₁, h₂⟩ := ih (i + 1) (by omega)
    have := (hP.2 i).1
    have := (hP.2 i).2
    have := (hH (i + 1)).1
    exact finite_projective_of_fourTerm R (injective_iCycles P i) (exact_iCycles_toCycles P i)
      (exact_toCycles_homologyπ P i) (surjective_homologyπ P (i + 1))

/-- The trace of the map induced on cycles, in each degree. -/
def cyclesTrace (hP : finiteProjectiveComplex R P)
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) (i : ℤ) : AdditiveCommutatorQuotient R := by
  letI := (finite_projective_cycles hP hH i).1
  letI := (finite_projective_cycles hP hH i).2
  exact Stacks.Trace.projectiveModuleTrace R (P.cycles i) (HomologicalComplex.cyclesMap g i).hom

/-- The trace of the map induced on cohomology, in each degree. -/
public def homologyTrace
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) (i : ℤ) : AdditiveCommutatorQuotient R := by
  letI := (hH i).1
  letI := (hH i).2
  exact Stacks.Trace.projectiveModuleTrace R (P.homology i)
    (HomologicalComplex.homologyMap g i).hom

/-- The trace of a component of an endomorphism of a complex of finite projective modules. -/
def termTrace (hP : finiteProjectiveComplex R P) (g : P ⟶ P) (i : ℤ) :
    AdditiveCommutatorQuotient R := by
  letI := (hP.2 i).1
  letI := (hP.2 i).2
  exact Stacks.Trace.projectiveModuleTrace R (P.X i) (g.f i).hom

/-- The trace identity `Tr(g | P^i) + Tr(g | H^{i+1}) = Tr(g | Z^i) + Tr(g | Z^{i+1})` coming
from the exact sequence `0 → Z^i → P^i → Z^{i+1} → H^{i+1} → 0`. -/
lemma termTrace_add_homologyTrace (hP : finiteProjectiveComplex R P)
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) (i : ℤ) :
    termTrace hP g i + homologyTrace hH g (i + 1) =
      cyclesTrace hP hH g i + cyclesTrace hP hH g (i + 1) := by
  let := (finite_projective_cycles hP hH i).1
  let := (finite_projective_cycles hP hH i).2
  let := (finite_projective_cycles hP hH (i + 1)).1
  let := (finite_projective_cycles hP hH (i + 1)).2
  let := (hP.2 i).1
  let := (hP.2 i).2
  let := (hH (i + 1)).1
  let := (hH (i + 1)).2
  refine projectiveModuleTrace_fourTerm R (injective_iCycles P i) (exact_iCycles_toCycles P i)
    (exact_toCycles_homologyπ P i) (surjective_homologyπ P (i + 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, HomologicalComplex.cyclesMap_i]
  · rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp]
    congr 1
    rw [← cancel_mono (P.iCycles (i + 1)), Category.assoc, Category.assoc,
      HomologicalComplex.cyclesMap_i, HomologicalComplex.toCycles_i_assoc,
      HomologicalComplex.toCycles_i]
    exact (g.comm i (i + 1)).symm
  · rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality]

/-- A function on degrees vanishing wherever the term of `P` is zero has finite support. -/
lemma support_subset_of_isZero (hP : finiteProjectiveComplex R P)
    (t : ℤ → AdditiveCommutatorQuotient R) (ht : ∀ i, IsZero (P.X i) → t i = 0) :
    (Function.support t).Finite :=
  (finite_nonzero_degrees R P hP).subset (fun i hi h => hi (ht i h))

/-- The trace on cycles vanishes in a degree where the complex is zero. -/
lemma cyclesTrace_eq_zero (hP : finiteProjectiveComplex R P)
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) (i : ℤ) (h : IsZero (P.X i)) : cyclesTrace hP hH g i = 0 := by
  have := subsingleton_cycles_of_isZero P i h
  exact projectiveModuleTrace_eq_zero_of_subsingleton R _ _

/-- The trace on cohomology vanishes in a degree where the complex is zero. -/
lemma homologyTrace_eq_zero
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) (i : ℤ) (h : IsZero (P.X i)) : homologyTrace hH g i = 0 := by
  have := subsingleton_homology_of_isZero P i h
  exact projectiveModuleTrace_eq_zero_of_subsingleton R _ _

/-- Shifting the index of a signed sum by one changes its sign. -/
lemma finsum_signedByDegree_succ (t : ℤ → AdditiveCommutatorQuotient R) :
    ∑ᶠ i : ℤ, signedByDegree R i (t (i + 1)) = -∑ᶠ i : ℤ, signedByDegree R i (t i) := by
  have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    (f := fun j : ℤ => signedByDegree R (j - 1) (t j))
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  rw [h, ← finsum_neg_distrib]
  apply finsum_congr
  intro j
  have := signedByDegree_succ R (j - 1) (t j)
  rw [sub_add_cancel] at this
  rw [this, neg_neg]

/-- **The trace of an endomorphism of a complex with projective cohomology, chain level.** For a
bounded complex `P` of finite projective modules whose cohomology modules are finite projective,
the alternating sum of the traces of an endomorphism `g` on the terms of `P` equals the
alternating sum of the traces of `H^i(g)`. -/
public theorem alternatingTrace_eq_homologyTrace (hP : finiteProjectiveComplex R P)
    (hH : ∀ i, Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i))
    (g : P ⟶ P) :
    alternatingTrace R P hP g = ∑ᶠ i : ℤ, signedByDegree R i (homologyTrace hH g i) := by
  have hX : alternatingTrace R P hP g = ∑ᶠ i : ℤ, signedByDegree R i (termTrace hP g i) := rfl
  have hZf := support_subset_of_isZero hP (cyclesTrace hP hH g) (cyclesTrace_eq_zero hP hH g)
  have hHf := support_subset_of_isZero hP (homologyTrace hH g) (homologyTrace_eq_zero hH g)
  have hfin (t : ℤ → AdditiveCommutatorQuotient R) (ht : (Function.support t).Finite) (a : ℤ) :
      (Function.support fun i => signedByDegree R i (t (i + a))).Finite := by
    refine (ht.preimage (Equiv.addRight a).injective.injOn).subset ?_
    intro i hi h
    exact hi (by simp only [Equiv.coe_addRight] at h; simp [h, signedByDegree_zero])
  have h0 (t : ℤ → AdditiveCommutatorQuotient R) :
      (fun i => signedByDegree R i (t (i + 0))) = fun i => signedByDegree R i (t i) := by
    simp
  have hterm (i : ℤ) : signedByDegree R i (termTrace hP g i) =
      signedByDegree R i (cyclesTrace hP hH g (i + 0)) +
        signedByDegree R i (cyclesTrace hP hH g (i + 1)) -
          signedByDegree R i (homologyTrace hH g (i + 1)) := by
    rw [add_zero, ← signedByDegree_add, sub_eq_add_neg, ← signedByDegree_neg, ← signedByDegree_add,
      ← termTrace_add_homologyTrace hP hH g i]
    congr 1
    abel
  have hZ0 := hfin _ hZf 0
  have hZ1 := hfin _ hZf 1
  have hH1 := hfin _ hHf 1
  rw [hX, finsum_congr hterm, finsum_sub_distrib ((hZ0.union hZ1).subset (Function.support_add _ _))
    hH1, finsum_add_distrib hZ0 hZ1, h0, finsum_signedByDegree_succ, finsum_signedByDegree_succ]
  abel

end Complexes

section Derived

variable (R : Type u) [Ring R]

/-- Every cohomology module of an object of the derived category is finite projective. -/
public abbrev HasFiniteProjectiveHomology (X : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∀ i, Module.Projective R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj X) ∧
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj X)

/-- The trace of the map induced on the `i`-th cohomology of an object of the derived category,
when that cohomology module is finite projective. -/
public def derivedHomologyTrace (X : DerivedCategory (ModuleCat.{v} R))
    (hH : HasFiniteProjectiveHomology R X) (f : X ⟶ X) (i : ℤ) : AdditiveCommutatorQuotient R := by
  letI := (hH i).1
  letI := (hH i).2
  exact Stacks.Trace.projectiveModuleTrace R _
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map f).hom

/-- **The trace of a perfect complex with projective cohomology.** If every cohomology module
`H^i(K)` of a perfect complex `K` is finite projective, then for every endomorphism `f` of `K`,
`Tr(f | K) = ∑_i (-1)^i Tr(H^i(f) | H^i(K))`. -/
public theorem perfectDerivedTrace_eq_homologyTrace (K : PerfectDerivedCategory.{u, v} R)
    (f : K.obj ⟶ K.obj) (hH : HasFiniteProjectiveHomology R K.obj) :
    perfectDerivedTrace R K f =
      ∑ᶠ i : ℤ, signedByDegree R i (derivedHomologyTrace R K.obj hH f i) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R K.obj).1 K.property
  have := isKProjective_of_finiteProjectiveComplex R hP
  obtain ⟨g, hg⟩ := exists_map_eq_of_isKProjective P P (e.hom ≫ f ≫ e.inv)
  let E (i : ℤ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K.obj ≅ P.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app P
  have hHP (i : ℤ) : Module.Projective R (P.homology i) ∧ Module.Finite R (P.homology i) := by
    let := (hH i).1
    let := (hH i).2
    exact ⟨Module.Projective.of_equiv (E i).toLinearEquiv,
      Module.Finite.equiv (E i).toLinearEquiv⟩
  rw [perfectDerivedTrace_eq_alternatingTrace R K f P hP e g hg,
    alternatingTrace_eq_homologyTrace hP hHP g]
  apply finsum_congr
  intro i
  congr 1
  let := (hH i).1
  let := (hH i).2
  let := (hHP i).1
  let := (hHP i).2
  have hmap : HomologicalComplex.homologyMap g i =
      (E i).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map f ≫ (E i).hom := by
    have hn := DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat.{v} R) g i
    rw [hg] at hn
    have hE : (E i).hom = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map e.inv ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).hom.app P := rfl
    have hn' := congrArg
      (fun t => (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map e.inv ≫ t) hn
    rw [Iso.eq_inv_comp, hE]
    refine (Category.assoc _ _ _).trans (hn'.symm.trans ?_)
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc, Functor.map_comp_assoc]
    rfl
  change Stacks.Trace.projectiveModuleTrace R (P.homology i)
      (HomologicalComplex.homologyMap g i).hom = _
  rw [hmap]
  exact projectiveModuleTrace_conj R (E i).toLinearEquiv _

end Derived

end CategoryTheory.FilteredDerived
