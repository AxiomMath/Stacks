module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Symmetric and exterior powers of a free module are free

If `M` is a free `R`-module, then for every `n` the exterior power `⋀^n M` and the symmetric
power `Sym^n M` are free `R`-modules. For a basis of `M` indexed by a linearly ordered type `κ`,
a basis of `Sym^n M` is given by the monomials indexed by the multisets `s : Sym κ n`.

## Main definitions

* `SymmetricPower.lift`: The linear map on the symmetric power induced by a permutation-invariant
  multilinear map.
* `symMonomial`: The monomial family in the symmetric power attached to a basis.

## Main results

* `exteriorPower_free`: The exterior powers of a free module are free.
* `symMonomial_linearIndependent`: The monomial family is linearly independent.
* `symMonomial_span_eq_top`: The monomial family spans the symmetric power.
* `symmetricPower_free`: The symmetric powers of a free module are free.
-/

@[expose] public section

open SymmetricPower
open scoped TensorProduct

/-- If `M` is a free `R`-module, then for every `n ≥ 0` the `n`-th exterior power `⋀^n(M)` is a
free `R`-module. -/
@[stacks 00DN, ega "0 5.5.4" "free case", sga "6 X 6.1" "special case"]
theorem exteriorPower_free
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] (n : ℕ) :
    Module.Free R (ExteriorAlgebra.exteriorPower R n M) :=
  exteriorPower.instFree R n

universe u

namespace SymmetricPower

variable {R ι : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The additive map underlying `SymmetricPower.lift`. -/
def liftAddHom (f : MultilinearMap R (fun _ : ι => M) N)
    (hf : ∀ (e : Equiv.Perm ι) (v : ι → M), f (fun i => v (e i)) = f v) : Sym[R] ι M →+ N :=
  AddCon.lift _ (PiTensorProduct.lift f).toAddMonoidHom <| AddCon.addConGen_le.mpr <| by
    rintro _ _ ⟨e, v⟩
    simp [AddCon.ker_rel, hf]

/-- `liftAddHom f hf` sends the class of a tensor `x` to `PiTensorProduct.lift f x`. -/
theorem liftAddHom_mk (f : MultilinearMap R (fun _ : ι => M) N)
    (hf : ∀ (e : Equiv.Perm ι) (v : ι → M), f (fun i => v (e i)) = f v)
    (x : ⨂[R] _ : ι, M) : liftAddHom f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  rfl

/-- A permutation-invariant multilinear map induces a linear map on the symmetric power. -/
noncomputable def lift (f : MultilinearMap R (fun _ : ι => M) N)
    (hf : ∀ (e : Equiv.Perm ι) (v : ι → M), f (fun i => v (e i)) = f v) : Sym[R] ι M →ₗ[R] N where
  toFun := liftAddHom f hf
  map_add' := map_add (liftAddHom f hf)
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.mp (range_mk R ι M) x
    rw [← map_smul (mk R ι M) r x, liftAddHom_mk, liftAddHom_mk, map_smul, RingHom.id_apply]

/-- `lift f hf` sends the class of a tensor `x` to `PiTensorProduct.lift f x`. -/
@[simp]
theorem lift_mk (f : MultilinearMap R (fun _ : ι => M) N)
    (hf : ∀ (e : Equiv.Perm ι) (v : ι → M), f (fun i => v (e i)) = f v) (x : ⨂[R] _ : ι, M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  rfl

/-- `lift f hf` sends the symmetric pure tensor of `v` to `f v`. -/
@[simp]
theorem lift_tprod (f : MultilinearMap R (fun _ : ι => M) N)
    (hf : ∀ (e : Equiv.Perm ι) (v : ι → M), f (fun i => v (e i)) = f v) (v : ι → M) :
    lift f hf (tprod R v) = f v := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

end SymmetricPower

/-- The content (value multiset) of a word `w : Fin n → κ`. -/
def contentOf {n : ℕ} {κ : Type*} (w : Fin n → κ) : Sym κ n :=
  Sym.mk (Multiset.map w Finset.univ.val) (by simp)

/-- The underlying multiset of `contentOf w` is the image of `w` over all slots. -/
@[simp] theorem coe_contentOf {n : ℕ} {κ : Type*} (w : Fin n → κ) :
    (contentOf w : Multiset κ) = Multiset.map w Finset.univ.val :=
  rfl

/-- The content of a word is invariant under permuting its slots. -/
theorem contentOf_comp {n : ℕ} {κ : Type*} (w : Fin n → κ) (e : Equiv.Perm (Fin n)) :
    contentOf (fun i => w (e i)) = contentOf w := by
  apply Sym.coe_injective
  rw [coe_contentOf, coe_contentOf, ← Function.comp_def, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Reading off the entries of a list of length `n` over all of `Fin n` recovers the list as a
multiset. -/
theorem map_get_univ {n : ℕ} {κ : Type*} (l : List κ) (h : l.length = n) :
    Multiset.map (fun i : Fin n => l.get (Fin.cast h.symm i)) Finset.univ.val =
      (l : Multiset κ) := by
  rw [Fin.univ_val_map, ← List.ofFn_congr h l.get, List.ofFn_get]

/-- The sorted word of a multiset `s : Sym κ n`. -/
noncomputable def Sym.sortedFn {n : ℕ} {κ : Type*} [LinearOrder κ] (s : Sym κ n) : Fin n → κ :=
  fun i => ((s : Multiset κ).sort (· ≤ ·)).get (Fin.cast (by simp [Multiset.length_sort]) i)

/-- The sorted word of a multiset `s` has content `s`. -/
theorem Sym.ofFn_sortedFn {n : ℕ} {κ : Type*} [LinearOrder κ] (s : Sym κ n) :
    contentOf (Sym.sortedFn s) = s := by
  apply Sym.coe_injective
  rw [coe_contentOf]
  have hlen : ((s : Multiset κ).sort (· ≤ ·)).length = n := by simp [Multiset.length_sort]
  unfold Sym.sortedFn
  rw [map_get_univ _ hlen]
  exact Multiset.sort_eq _ _

/-- The sorted word of `s` is monotone. -/
theorem Sym.monotone_sortedFn {n : ℕ} {κ : Type*} [LinearOrder κ] (s : Sym κ n) :
    Monotone (Sym.sortedFn s) := by
  intro i j hij
  unfold Sym.sortedFn
  have hp : List.Pairwise (· ≤ ·) ((s : Multiset κ).sort (· ≤ ·)) := Multiset.pairwise_sort _ _
  rw [List.pairwise_iff_get] at hp
  rcases lt_or_eq_of_le hij with h | rfl
  · exact hp _ _ (by simpa using h)
  · rfl

/-- Two monotone (sorted) words with the same content multiset are equal. -/
theorem monotone_eq_of_content {n : ℕ} {κ : Type*} [LinearOrder κ] (g h : Fin n → κ)
    (hg : Monotone g) (hh : Monotone h) (H : contentOf g = contentOf h) : g = h := by
  rw [← List.ofFn_inj]
  refine List.Perm.eq_of_pairwise (fun _ _ _ _ => le_antisymm)
    (List.sortedLE_ofFn_iff.mpr hg).pairwise (List.sortedLE_ofFn_iff.mpr hh).pairwise ?_
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
  simpa using congrArg (fun s : Sym κ n => (s : Multiset κ)) H

/-- The sorted word of `contentOf w` is `w` reordered by its sorting permutation. -/
theorem Sym.sortedFn_ofFn {n : ℕ} {κ : Type*} [LinearOrder κ] (w : Fin n → κ) :
    Sym.sortedFn (contentOf w) = fun i => w (Tuple.sort w i) :=
  monotone_eq_of_content _ _ (Sym.monotone_sortedFn _) (Tuple.monotone_sort w) <| by
    rw [Sym.ofFn_sortedFn, contentOf_comp]

/-- The (finite) set of distinct words with content `t`, realised as the orbit of
the sorted word `Sym.sortedFn t` under permutations of the positions. -/
noncomputable def wordsOfContent {n : ℕ} {κ : Type*} [LinearOrder κ] (t : Sym κ n) :
    Finset (Fin n → κ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).image
    (fun σ : Equiv.Perm (Fin n) => fun i => Sym.sortedFn t (σ i))

/-- The set of words with content `t` is closed under permuting slots. -/
theorem mem_wordsOfContent_comp {n : ℕ} {κ : Type*} [LinearOrder κ] (t : Sym κ n) {w : Fin n → κ}
    (e : Equiv.Perm (Fin n)) (hw : w ∈ wordsOfContent t) :
    (fun i => w (e i)) ∈ wordsOfContent t := by
  simp only [wordsOfContent, Finset.mem_image, Finset.mem_univ, true_and] at hw ⊢
  obtain ⟨σ, rfl⟩ := hw
  exact ⟨σ * e, rfl⟩

/-- The sorted word of `s` has content `t` exactly when `s = t`. -/
theorem sortedFn_mem_wordsOfContent_iff {n : ℕ} {κ : Type*} [LinearOrder κ] (s t : Sym κ n) :
    Sym.sortedFn s ∈ wordsOfContent t ↔ s = t := by
  simp only [wordsOfContent, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨fun ⟨σ, hσ⟩ => ?_, fun h => ⟨1, h ▸ rfl⟩⟩
  simpa [contentOf_comp, Sym.ofFn_sortedFn] using (congrArg contentOf hσ).symm

/-- The "permanent" symmetric multilinear map for target multiset `t`: the sum,
over all distinct words `w` with content `t`, of the product of the coordinate
functionals `b.coord (w j)`. -/
noncomputable def permanentMultilinearMap (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) {n : ℕ} (t : Sym κ n) :
    MultilinearMap R (fun _ : Fin n => M) R :=
  ∑ w ∈ wordsOfContent t,
    (MultilinearMap.mkPiAlgebra R (Fin n) R).compLinearMap (fun j => b.coord (w j))

/-- The permanent-style multilinear map at `t` evaluates as the sum over words of content `t`
of the products of the corresponding coordinates. -/
theorem permanentMultilinearMap_apply (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) {n : ℕ} (t : Sym κ n)
    (v : Fin n → M) :
    permanentMultilinearMap R b t v = ∑ w ∈ wordsOfContent t, ∏ j, (b.coord (w j)) (v j) := by
  simp [permanentMultilinearMap]

/-- The permanent-style multilinear map at `t` is invariant under permuting its arguments. -/
theorem permanentMultilinearMap_apply_perm (R : Type*) [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {κ : Type*} [LinearOrder κ]
    (b : Module.Basis κ R M) {n : ℕ} (t : Sym κ n)
    (e : Equiv.Perm (Fin n)) (v : Fin n → M) :
    permanentMultilinearMap R b t (fun i => v (e i)) = permanentMultilinearMap R b t v := by
  rw [permanentMultilinearMap_apply, permanentMultilinearMap_apply]
  refine Finset.sum_nbij' (fun w i => w (e.symm i)) (fun w i => w (e i))
    (fun _ hw => mem_wordsOfContent_comp t e.symm hw) (fun _ hw => mem_wordsOfContent_comp t e hw)
    (fun _ _ => by ext; simp) (fun _ _ => by ext; simp) fun w _ => ?_
  rw [← Equiv.prod_comp e (fun j => (b.coord (w (e.symm j))) (v j))]
  simp

/-- The product of coordinates `∏ j, b.coord (w j) (b (w' j))` is `1` if `w' = w` and `0`
otherwise. -/
theorem prod_coord_basis {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {κ : Type*} [DecidableEq κ] (b : Module.Basis κ R M) {n : ℕ} (w w' : Fin n → κ) :
    (∏ j, (b.coord (w j)) (b (w' j))) = if w' = w then 1 else 0 := by
  have coord_basis : ∀ i k : κ, (b.coord i) (b k) = if k = i then 1 else 0 := by
    intro i k
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp_rw [coord_basis]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, forall_const, eq_iff_iff]
  exact funext_iff.symm

/-- Evaluating the permanent-style multilinear map at `t` on the basis word of `s` gives `1` if
`s = t` and `0` otherwise. -/
theorem permanentMultilinearMap_eval (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) {n : ℕ} (s t : Sym κ n) :
    permanentMultilinearMap R b t (fun i => b (Sym.sortedFn s i)) = if s = t then 1 else 0 := by
  rw [permanentMultilinearMap_apply]
  simp_rw [prod_coord_basis b]
  rw [Finset.sum_ite_eq (wordsOfContent t) (Sym.sortedFn s) (fun _ => (1:R))]
  simp [sortedFn_mem_wordsOfContent_iff]

/-- The degree-`n` monomial family in a basis `b = {x_i}_{i ∈ κ}` of `M`, indexed
by size-`n` multisets `s : Sym κ n`. It sends `s` to the symmetric pure tensor of
the (sorted) basis vectors of `s`; by symmetry of `tprod` (`tprod_equiv`) the
choice of ordering is irrelevant, so this is the monomial `∏_{i ∈ s} x_i`. -/
noncomputable def symMonomial (R : Type) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) (n : ℕ)
    (s : Sym κ n) : SymmetricPower R (Fin n) M :=
  SymmetricPower.tprod R fun i => b (Sym.sortedFn s i)

/-- A pure word-tensor `tprod (b ∘ w)` equals the monomial indexed by its content
multiset. -/
theorem tprod_eq_symMonomial (R : Type) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) {n : ℕ}
    (w : Fin n → κ) :
    SymmetricPower.tprod R (fun i => b (w i)) = symMonomial R b n (contentOf w) := by
  rw [symMonomial, Sym.sortedFn_ofFn w]
  exact (SymmetricPower.tprod_equiv (Tuple.sort w) fun j => b (w j)).symm

/-- The coordinate functional dual to the monomial indexed by `t`. -/
noncomputable def dualFunctional (R : Type) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) {n : ℕ} (t : Sym κ n) :
    SymmetricPower R (Fin n) M →ₗ[R] R :=
  SymmetricPower.lift (permanentMultilinearMap R b t)
    (permanentMultilinearMap_apply_perm R b t)

/-- Duality: `dualFunctional t` evaluated on the monomial `symMonomial s` is the
Kronecker delta `δ_{s,t}`. -/
theorem dualFunctional_symMonomial (R : Type) [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {κ : Type*} [LinearOrder κ]
    (b : Module.Basis κ R M) {n : ℕ} (s t : Sym κ n) :
    dualFunctional R b t (symMonomial R b n s) = if s = t then 1 else 0 := by
  rw [dualFunctional, symMonomial, SymmetricPower.lift_tprod]
  exact permanentMultilinearMap_eval R b s t

/-- The monomial family is linearly independent. -/
theorem symMonomial_linearIndependent (R : Type) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) (n : ℕ) :
    LinearIndependent R (symMonomial R b n) := by
  refine LinearIndependent.of_comp (LinearMap.pi fun t => dualFunctional R b t) ?_
  have h : ⇑(LinearMap.pi fun t => dualFunctional R b t) ∘ symMonomial R b n =
      fun s => Pi.single s (1 : R) := by
    ext s t
    rw [Function.comp_apply, LinearMap.pi_apply, dualFunctional_symMonomial, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  rw [h]
  exact Pi.linearIndependent_single_one (Sym κ n) R

/-- The monomial family spans the symmetric power. -/
theorem symMonomial_span_eq_top (R : Type) [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {κ : Type*} [LinearOrder κ] (b : Module.Basis κ R M) (n : ℕ) :
    ⊤ ≤ Submodule.span R (Set.range (symMonomial R b n)) := by
  rw [← SymmetricPower.span_tprod_eq_top R (Fin n) M, Submodule.span_le, Set.range_subset_iff]
  intro m
  have hm : m = fun i => ∑ k ∈ (b.repr (m i)).support, (b.repr (m i)) k • b k := by
    funext i
    conv_lhs => rw [← b.linearCombination_repr (m i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [SetLike.mem_coe, hm, MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [MultilinearMap.map_smul_univ (m := fun j => b (r j)), tprod_eq_symMonomial R b r]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (Set.mem_range_self _))

/-- If `M` has a basis indexed by a linearly ordered type, then `Sym^n M` is free. -/
theorem symmetricPower_free_of_basis (R : Type) [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] (n : ℕ) {κ : Type*} [LinearOrder κ]
    (b : Module.Basis κ R M) :
    Module.Free R (SymmetricPower R (Fin n) M) :=
  .of_basis (.mk (symMonomial_linearIndependent R b n) (symMonomial_span_eq_top R b n))

/-- If `M` is a free `R`-module, then for every `n ≥ 0` the `n`-th symmetric power `Sym^n(M)` is
a free `R`-module. -/
@[stacks 00DN]
theorem symmetricPower_free
    (R : Type) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
    [Module.Free R M] (n : ℕ) :
    Module.Free R (SymmetricPower R (Fin n) M) := by
  obtain ⟨κ, b⟩ := (inferInstance : Module.Free R M).exists_basis
  let := (exists_wellFoundedLT κ).choose
  exact symmetricPower_free_of_basis R n b

end
