module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.GroupTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Trace of an endomorphism of a finite projective module

Let `R` be a possibly noncommutative ring. The trace of an endomorphism of a finite projective
left `R`-module takes values in the additive commutator quotient `Rⁿᵃᵗ`; it is computed by
embedding the module as a direct summand of a finite free module and taking the trace of the
induced endomorphism there. This file proves the formal properties of that trace: it may be
computed from *any* splitting, it is cyclic, additive, vanishes on a zero module, is invariant
under conjugation by an isomorphism, and is additive along a split short exact sequence.

## Main definitions

* `CategoryTheory.FilteredDerived.blockTriangular`: the block upper triangular endomorphism of
  `M × N` assembled from endomorphisms of `M` and `N` and an off-diagonal map `N →ₗ[R] M`.

## Main results

* `CategoryTheory.FilteredDerived.freeModuleTrace_cyclic`: the trace on finite free modules is
  unchanged by cyclically permuting a composite.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_of_split`: the trace of a finite
  projective module is computed by any splitting of it off a finite free module, not only by
  the chosen one.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_cyclic`,
  `CategoryTheory.FilteredDerived.projectiveModuleTrace_add` and
  `CategoryTheory.FilteredDerived.projectiveModuleTrace_zero`: cyclicity and additivity.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_conj`: invariance under conjugation.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_blockTriangular` and
  `CategoryTheory.FilteredDerived.projectiveModuleTrace_splitExact`: the trace of a block upper
  triangular endomorphism, and of an endomorphism of a split short exact sequence, is the sum of
  the traces of its diagonal parts.

## References

* [Stacks Project, Tag 03TI](https://stacks.math.columbia.edu/tag/03TI)
* [Stacks Project, Tag 03TL](https://stacks.math.columbia.edu/tag/03TL)
-/

@[expose] public noncomputable section

open scoped BigOperators

universe u v w

namespace CategoryTheory.FilteredDerived

/-- Multiplication in a ring is commutative after passing to the additive commutator
quotient. -/
public lemma additiveCommutatorQuotientMk_mul_comm (R : Type u) [Ring R] (a b : R) :
    additiveCommutatorQuotientMk R (a * b) =
      additiveCommutatorQuotientMk R (b * a) := by
  apply (QuotientAddGroup.eq).2
  have h : b * a - a * b ∈ additiveCommutatorSubgroup R :=
    AddSubgroup.subset_closure ⟨b, a, rfl⟩
  simpa [sub_eq_add_neg, add_comm] using h

/-- Every vector of a finite free module is the sum of its coordinates times the standard basis
vectors. -/
public lemma standardBasisVector_decomp (R : Type u) [Ring R]
    (ι : Type v) [Fintype ι] (x : ι → R) :
    x = ∑ i, x i • standardBasisVector R ι i := by
  classical
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply]
  show x i = ∑ j, x j * standardBasisVector R ι j i
  rw [Finset.sum_eq_single i]
  · simp [standardBasisVector]
  · intro j hj hji
    simp [standardBasisVector, hji.symm]
  · simp

/-- The trace on finite free modules is cyclic: the two composites of a pair of maps between
finite free modules have the same trace. -/
@[sga "5 IIIB 1.1" "special case", sga "5 IIIB 5.8" "(5.8.5) for E", sga "6 I 8.3" "special case"]
public lemma freeModuleTrace_cyclic (R : Type u) [Ring R]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : (κ → R) →ₗ[R] (ι → R)) (g : (ι → R) →ₗ[R] (κ → R)) :
    freeModuleTrace R ι (f.comp g) = freeModuleTrace R κ (g.comp f) := by
  classical
  have eval_f (x : κ → R) (i : ι) :
      f x i = ∑ j, x j * f (standardBasisVector R κ j) i := by
    nth_rw 1 [standardBasisVector_decomp R κ x]
    simp [Finset.sum_apply]
  have eval_g (x : ι → R) (j : κ) :
      g x j = ∑ i, x i * g (standardBasisVector R ι i) j := by
    nth_rw 1 [standardBasisVector_decomp R ι x]
    simp [Finset.sum_apply]
  rw [freeModuleTrace_apply, freeModuleTrace_apply]
  show additiveCommutatorQuotientMk R
      (∑ i, f (g (standardBasisVector R ι i)) i) =
    additiveCommutatorQuotientMk R
      (∑ j, g (f (standardBasisVector R κ j)) j)
  rw [map_sum, map_sum]
  have left (i : ι) :
      additiveCommutatorQuotientMk R (f (g (standardBasisVector R ι i)) i) =
        ∑ j, additiveCommutatorQuotientMk R
          (g (standardBasisVector R ι i) j * f (standardBasisVector R κ j) i) := by
    rw [eval_f]
    exact map_sum (additiveCommutatorQuotientMk R) _ _
  have right (j : κ) :
      additiveCommutatorQuotientMk R (g (f (standardBasisVector R κ j)) j) =
        ∑ i, additiveCommutatorQuotientMk R
          (f (standardBasisVector R κ j) i * g (standardBasisVector R ι i) j) := by
    rw [eval_g]
    exact map_sum (additiveCommutatorQuotientMk R) _ _
  calc
    _ = ∑ i, ∑ j, additiveCommutatorQuotientMk R
          (g (standardBasisVector R ι i) j * f (standardBasisVector R κ j) i) :=
      Finset.sum_congr rfl fun i _ => left i
    _ = ∑ j, ∑ i, additiveCommutatorQuotientMk R
          (g (standardBasisVector R ι i) j * f (standardBasisVector R κ j) i) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, additiveCommutatorQuotientMk R
          (f (standardBasisVector R κ j) i * g (standardBasisVector R ι i) j) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
        additiveCommutatorQuotientMk_mul_comm R _ _
    _ = ∑ j, additiveCommutatorQuotientMk R
          (g (f (standardBasisVector R κ j)) j) :=
      Finset.sum_congr rfl fun j _ => (right j).symm

/-- The trace of an endomorphism of a finite projective module can be computed from any
presentation of it as a direct summand of a finite free module. -/
@[sga "4½ Rapport 4.2"]
public lemma projectiveModuleTrace_eq_of_split (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] (f : Module.End R P) {ι : Type w} [Fintype ι]
    (p : (ι → R) →ₗ[R] P) (i : P →ₗ[R] (ι → R))
    (hpi : p.comp i = LinearMap.id) :
    Stacks.Trace.projectiveModuleTrace R P f =
      freeModuleTrace R ι (i.comp (f.comp p)) := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n₀ := h.choose
  let p₀ := h.choose_spec.choose
  let i₀ := h.choose_spec.choose_spec.choose
  have hp₀i₀ : p₀.comp i₀ = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  have hp₀i₀_apply (x : P) : p₀ (i₀ x) = x := LinearMap.congr_fun hp₀i₀ x
  show freeModuleTrace R (Fin n₀) (i₀.comp (f.comp p₀)) = _
  let a : (ι → R) →ₗ[R] (Fin n₀ → R) := i₀.comp (f.comp p)
  let b : (Fin n₀ → R) →ₗ[R] (ι → R) := i.comp p₀
  have hpi_apply (x : P) : p (i x) = x := LinearMap.congr_fun hpi x
  simpa [Stacks.Trace.projectiveModuleTrace, a, b, LinearMap.comp_assoc,
    hpi_apply, hp₀i₀_apply] using (freeModuleTrace_cyclic R a b)

/-- Composing two split composites collapses the middle projection-inclusion pair. -/
private theorem comp_comp_comp_comp_eq_of_comp_eq_id {R : Type u} [Ring R]
    {X Y Z P Q : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup P] [AddCommGroup Q] [Module R X] [Module R Y] [Module R Z] [Module R P]
    [Module R Q] (i₁ : P →ₗ[R] Z) (g : Q →ₗ[R] P) (f : P →ₗ[R] Q) (p₁ : X →ₗ[R] P)
    {i₂ : Q →ₗ[R] Y} {p₂ : Y →ₗ[R] Q} (h : p₂.comp i₂ = LinearMap.id) :
    (i₁.comp (g.comp p₂)).comp (i₂.comp (f.comp p₁)) = i₁.comp ((g.comp f).comp p₁) := by
  ext x
  have hx : p₂ (i₂ (f (p₁ x))) = f (p₁ x) := LinearMap.congr_fun h _
  simp [hx]

/-- The trace of a finite projective module is cyclic: the two composites of a pair of maps
between finite projective modules have the same trace. -/
@[sga "5 IIIB 1.1" "special case", sga "5 IIIB 5.8" "(5.8.5) for E", sga "6 I 8.3" "special case"]
public lemma projectiveModuleTrace_cyclic (R : Type u) [Ring R]
    (P Q : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) :
    Stacks.Trace.projectiveModuleTrace R P (g.comp f) =
      Stacks.Trace.projectiveModuleTrace R Q (f.comp g) := by
  classical
  let hP := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := hP.choose
  let pP : (Fin n → R) →ₗ[R] P := hP.choose_spec.choose
  let iP : P →ₗ[R] (Fin n → R) := hP.choose_spec.choose_spec.choose
  have hP' : pP.comp iP = LinearMap.id := hP.choose_spec.choose_spec.choose_spec.2.2
  let hQ := Module.Finite.exists_comp_eq_id_of_projective R Q
  let m := hQ.choose
  let pQ : (Fin m → R) →ₗ[R] Q := hQ.choose_spec.choose
  let iQ : Q →ₗ[R] (Fin m → R) := hQ.choose_spec.choose_spec.choose
  have hQ' : pQ.comp iQ = LinearMap.id := hQ.choose_spec.choose_spec.choose_spec.2.2
  rw [projectiveModuleTrace_eq_of_split R P (g.comp f) pP iP hP',
    projectiveModuleTrace_eq_of_split R Q (f.comp g) pQ iQ hQ']
  let a : (Fin n → R) →ₗ[R] (Fin m → R) := iQ.comp (f.comp pP)
  let b : (Fin m → R) →ₗ[R] (Fin n → R) := iP.comp (g.comp pQ)
  have hab : b.comp a = iP.comp ((g.comp f).comp pP) :=
    comp_comp_comp_comp_eq_of_comp_eq_id iP g f pP hQ'
  have hba : a.comp b = iQ.comp ((f.comp g).comp pQ) :=
    comp_comp_comp_comp_eq_of_comp_eq_id iQ f g pQ hP'
  rw [← hab, ← hba]
  exact freeModuleTrace_cyclic R b a

/-- The trace of a finite projective module is additive in the endomorphism. -/
public lemma projectiveModuleTrace_add (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f g : Module.End R P) :
    Stacks.Trace.projectiveModuleTrace R P (f + g) =
      Stacks.Trace.projectiveModuleTrace R P f +
        Stacks.Trace.projectiveModuleTrace R P g := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := h.choose
  let p : (Fin n → R) →ₗ[R] P := h.choose_spec.choose
  let i : P →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  have hi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  rw [projectiveModuleTrace_eq_of_split R P (f + g) p i hi,
    projectiveModuleTrace_eq_of_split R P f p i hi,
    projectiveModuleTrace_eq_of_split R P g p i hi]
  have hsum : i.comp ((f + g).comp p) = i.comp (f.comp p) + i.comp (g.comp p) := by
    apply LinearMap.ext
    intro x
    simp [LinearMap.comp_apply]
  rw [hsum, (freeModuleTrace R (Fin n)).map_add]

/-- The trace of the zero endomorphism of a finite projective module vanishes. -/
public lemma projectiveModuleTrace_zero (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] :
    Stacks.Trace.projectiveModuleTrace R P (0 : Module.End R P) = 0 := by
  classical simp [Stacks.Trace.projectiveModuleTrace]

/-- Every endomorphism of a zero finite projective module has vanishing trace. -/
public lemma projectiveModuleTrace_eq_zero_of_subsingleton (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [Subsingleton P] (f : Module.End R P) :
    Stacks.Trace.projectiveModuleTrace R P f = 0 := by
  have hf : f = 0 := by
    ext x
    exact Subsingleton.elim _ _
  rw [hf, projectiveModuleTrace_zero]

/-- The trace of a finite projective module is invariant under conjugating an endomorphism by an
isomorphism of modules. -/
@[sga "6 I 8.4" "special case"]
public lemma projectiveModuleTrace_conj (R : Type u) [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (f : Module.End R M) :
    Stacks.Trace.projectiveModuleTrace R N
        (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      Stacks.Trace.projectiveModuleTrace R M f := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  let ι := h.choose
  let p := h.choose_spec.choose
  let i := h.choose_spec.choose_spec.choose
  have hp : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  have hp_apply (x : M) : p (i x) = x := LinearMap.congr_fun hp x
  let p' : (Fin ι → R) →ₗ[R] N := e.toLinearMap.comp p
  let i' : N →ₗ[R] (Fin ι → R) := i.comp e.symm.toLinearMap
  have hp' : p'.comp i' = LinearMap.id := by
    ext x
    simp [p', i', LinearMap.comp_apply, hp_apply]
  rw [projectiveModuleTrace_eq_of_split R N
    (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) p' i' hp',
    projectiveModuleTrace_eq_of_split R M f p i hp]
  simp [p', i', LinearMap.comp_assoc, ι]

/-- The block upper triangular endomorphism of `M × N` with diagonal blocks `a` and `b` and
off-diagonal block `c`. -/
public def blockTriangular {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (a : Module.End R M) (b : Module.End R N) (c : N →ₗ[R] M) :
    Module.End R (M × N) where
  toFun x := (a x.1 + c x.2, b x.2)
  map_add' x y := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
    · simp
  map_smul' r x := by ext <;> simp [smul_add]

/-- The trace of a block upper triangular endomorphism of a product of finite projective modules
is the sum of the traces of its diagonal blocks. -/
@[sga "6 I 8.1.1" "special case"]
public lemma projectiveModuleTrace_blockTriangular (R : Type u) [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (a : Module.End R M) (b : Module.End R N) (c : N →ₗ[R] M) :
    Stacks.Trace.projectiveModuleTrace R (M × N) (blockTriangular a b c) =
      Stacks.Trace.projectiveModuleTrace R M a +
        Stacks.Trace.projectiveModuleTrace R N b := by
  classical
  obtain ⟨nM, pM, iM, _, _, hpM⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨nN, pN, iN, _, _, hpN⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R N
  let p : ((Sum (Fin nM) (Fin nN)) → R) →ₗ[R] M × N := {
    toFun x := (pM (fun i => x (Sum.inl i)), pN (fun j => x (Sum.inr j)))
    map_add' x y := by
      ext
      · exact map_add pM _ _
      · exact map_add pN _ _
    map_smul' r x := by
      ext
      · exact map_smul pM r _
      · exact map_smul pN r _
  }
  let i : M × N →ₗ[R] (Sum (Fin nM) (Fin nN)) → R := {
    toFun x := Sum.elim (iM x.1) (iN x.2)
    map_add' x y := by
      ext z
      cases z <;> simp
    map_smul' r x := by
      ext z
      cases z <;> simp
  }
  have hpM_apply (x : M) : pM (iM x) = x := LinearMap.congr_fun hpM x
  have hpN_apply (x : N) : pN (iN x) = x := LinearMap.congr_fun hpN x
  have hpi : p.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨x, y⟩
    ext <;> simp [p, i, LinearMap.comp_apply, hpM_apply, hpN_apply]
  rw [projectiveModuleTrace_eq_of_split R (M × N) (blockTriangular a b c) p i hpi,
    projectiveModuleTrace_eq_of_split R M a pM iM hpM,
    projectiveModuleTrace_eq_of_split R N b pN iN hpN]
  rw [freeModuleTrace_apply, freeModuleTrace_apply, freeModuleTrace_apply]
  show additiveCommutatorQuotientMk R
      (∑ x : Sum (Fin nM) (Fin nN), (i.comp ((blockTriangular a b c).comp p))
        (standardBasisVector R (Sum (Fin nM) (Fin nN)) x) x) =
    additiveCommutatorQuotientMk R
      (∑ x : Fin nM, (iM.comp (a.comp pM)) (standardBasisVector R (Fin nM) x) x) +
    additiveCommutatorQuotientMk R
      (∑ x : Fin nN, (iN.comp (b.comp pN)) (standardBasisVector R (Fin nN) x) x)
  have hpNfun : pN (fun _ : Fin nN => 0) = 0 := by
    show pN (0 : Fin nN → R) = 0
    exact map_zero pN
  have hInl (x : Fin nM) :
      (fun i : Fin nM =>
          standardBasisVector R (Sum (Fin nM) (Fin nN)) (Sum.inl x) (Sum.inl i)) =
        standardBasisVector R (Fin nM) x := by
    funext i
    simp [standardBasisVector, Pi.single_apply]
  have hInr (x : Fin nN) :
      (fun j : Fin nN =>
          standardBasisVector R (Sum (Fin nM) (Fin nN)) (Sum.inr x) (Sum.inr j)) =
        standardBasisVector R (Fin nN) x := by
    funext j
    simp [standardBasisVector, Pi.single_apply]
  simp [Fintype.sum_sum_type, p, i, blockTriangular, LinearMap.comp_apply,
    standardBasisVector, hpNfun, hInl, hInr]

/-- An endomorphism of a split short exact sequence of finite projective modules has the trace
of its middle term equal to the sum of the traces of its two outer terms. -/
public lemma projectiveModuleTrace_splitExact (R : Type u) [Ring R]
    {A C B : Type v} [AddCommGroup A] [AddCommGroup C] [AddCommGroup B]
    [Module R A] [Module R C] [Module R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite R B] [Module.Projective R B]
    (e : (A × C) ≃ₗ[R] B) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (α : Module.End R A) (β : Module.End R B) (γ : Module.End R C)
    (he : e.toLinearMap.comp (LinearMap.inl R A C) = f)
    (hg : g.comp e.toLinearMap = LinearMap.snd R A C)
    (hα : β.comp f = f.comp α) (hγ : g.comp β = γ.comp g) :
    Stacks.Trace.projectiveModuleTrace R B β =
      Stacks.Trace.projectiveModuleTrace R A α +
        Stacks.Trace.projectiveModuleTrace R C γ := by
  classical
  let T : Module.End R (A × C) :=
    e.symm.toLinearMap.comp (β.comp e.toLinearMap)
  let c : C →ₗ[R] A := (LinearMap.fst R A C).comp
    (T.comp (LinearMap.inr R A C))
  have he_apply (x : A) : e (LinearMap.inl R A C x) = f x :=
    congrArg (fun k : A →ₗ[R] B => k x) he
  have hsymm (x : A) : e.symm (f x) = LinearMap.inl R A C x := by
    rw [← he_apply x, e.symm_apply_apply]
  have hTinl (x : A) : T (LinearMap.inl R A C x) = LinearMap.inl R A C (α x) := by
    show e.symm (β (e (LinearMap.inl R A C x))) = _
    rw [he_apply x]
    have hx := congrArg (fun k : A →ₗ[R] B => k x) hα
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
    rw [hx, hsymm]
  have hsnd_apply (x : B) : (e.symm x).2 = g x := by
    have hx := congrArg (fun k : A × C →ₗ[R] C => k (e.symm x)) hg
    simpa [LinearMap.comp_apply, e.apply_symm_apply] using hx.symm
  have hTsnd (x : A × C) : (T x).2 = γ x.2 := by
    dsimp [T]
    rw [hsnd_apply]
    have hx := congrArg (fun k : B →ₗ[R] C => k (e x)) hγ
    have hgx := congrArg (fun k : A × C →ₗ[R] C => k x) hg
    simpa [LinearMap.comp_apply] using hx.trans (congrArg γ hgx)
  have hT : T = blockTriangular α γ c := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    have hx : (x, y) = LinearMap.inl R A C x + LinearMap.inr R A C y := by
      ext <;> simp
    rw [hx, map_add]
    apply Prod.ext
    · show (T (LinearMap.inl R A C x)).1 + (T (LinearMap.inr R A C y)).1 = _
      rw [hTinl]
      simp [blockTriangular, c, LinearMap.comp_apply]
    · show (T (LinearMap.inl R A C x)).2 + (T (LinearMap.inr R A C y)).2 = _
      simp [blockTriangular, hTsnd]
  calc
    Stacks.Trace.projectiveModuleTrace R B β =
        Stacks.Trace.projectiveModuleTrace R (A × C) T := by
      simpa [T, LinearMap.comp_assoc] using (projectiveModuleTrace_conj R e T)
    _ = Stacks.Trace.projectiveModuleTrace R (A × C) (blockTriangular α γ c) := by rw [hT]
    _ = Stacks.Trace.projectiveModuleTrace R A α +
        Stacks.Trace.projectiveModuleTrace R C γ :=
      projectiveModuleTrace_blockTriangular R α γ c

end CategoryTheory.FilteredDerived
