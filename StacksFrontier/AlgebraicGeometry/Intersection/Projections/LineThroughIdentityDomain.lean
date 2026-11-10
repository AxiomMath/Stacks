module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints

/-!
# A line of endomorphisms through the identity on whose every point a subvariety is defined

Let `X ⊊ 𝐏(V)` be a closed subset. The first clause of Tag 0B1S asks for `X ⊆ U(g)` at every
point `[g]` of a general line through `[id_V]` in the parameter space `𝐏 = 𝐏((End V)ᵛ)`. The
points of the line through `[id_V]` and `[h]` are the classes of `a • id_V + b • h`, and a
closed point of `𝐏(V)`, cut out by a nonzero functional `f`, fails to lie in
`U(a • id_V + b • h)` exactly when `f ∘ (a • id_V + b • h) = 0`. For `(a, b) ≠ (0, 0)` that
forces `b ≠ 0` and makes `f` an eigenvector of the transpose of `h`. So the whole line through
`[id_V]` and `[h]` is good for clause (1) precisely when no eigenvector of the transpose of `h`
cuts out a point of `X`.

That reformulation makes the *existence* of a good line elementary: pick a basis `f₀, …, fₙ` of
the dual `Vᵛ` none of whose members cuts out a point of `X` — possible because `𝐏(V)` is
irreducible, so `X` together with a proper linear subspace is still a proper closed subset — and
let `h` be the automorphism whose transpose has the `fᵢ` as eigenvectors with pairwise distinct
eigenvalues. Every eigenvector of the transpose is then a multiple of some `fᵢ`, hence cuts out
a point off `X`.

## Main results

All names below are in the namespace `AlgebraicGeometry.ProjectiveSpaceOfModule`.

* `notMem_endDomain_linearFunctionalPoint_iff`: a closed point of `𝐏(V)` cut out by `f` lies
  outside `U(g)` exactly when `f ∘ g = 0`.
* `subset_endDomain_of_forall_linearFunctionalPoint`: a closed subset lies in `U(g)` as soon as
  each of its closed points does.
* `exists_linearFunctionalPoint_mem_of_isClosed`: a nonempty closed subset of `𝐏(V)` contains a
  point cut out by a functional.
* `exists_basis_dual_forall_linearFunctionalPoint_notMem`: a proper closed subset of `𝐏(V)`
  misses the points cut out by the members of some basis of `Vᵛ`.
* `exists_forall_subset_endDomain_line`: **there is a line through `[id_V]` along which clause (1)
  of Tag 0B1S holds.**

## Implementation notes

This is the *existence* half of clause (1) of Tag 0B1S, not the clause itself: the source asks
for the clause along a *general* line, that is along the lines through `[id_V]` meeting a
nonempty Zariski open subset of `𝐏`, and getting from one line to an open set of them is exactly
the step that needs the bad locus of clause (1) to be contained in a closed subset of
codimension at least two. That step is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension`, which needs
neither elimination theory nor the family of projective transformations over `𝐏`: the adjugate
writes the omitted point of a corank-one class in closed form, as a tuple of forms of degree
`dim V - 1`, so substituting it into a form cutting out `X` already cuts out a proper closed
subset of the determinant hypersurface. Nothing here is registered against Tag 0B1S because that
tag also asserts clause (2), whose bad locus is not bounded in the library.

The line is given by the endomorphism `h` spanning it with `id_V`, and the points of the line by
their representatives `a • id_V + b • h`, rather than through
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` of a corank-two submodule of
`(End V)ᵛ` as in Tag 0B2T; the two descriptions agree by double annihilation, which is not
carried out. That `h` is not a scalar multiple of `id_V`, so that the two do span a line, is
part of the conclusion whenever `V` has dimension at least two.

The passage from the closed points of `X` to all of `X` is Jacobsonness of `𝐏(V)`: the locus
where the clause fails is closed, so if it is nonempty it contains a point closed in `𝐏(V)`,
which over an algebraically closed field is cut out by a functional.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The point cut out by `f` lies in the linear subspace of `W` exactly when `f` vanishes on `W`. -/
private theorem linearFunctionalPoint_mem_linearSubspace_iff (W : Submodule k V)
    (f : Module.Dual k V) (hf : f ≠ 0) :
    linearFunctionalPoint k V f hf ∈ linearSubspace k V W ↔ ∀ w ∈ W, f w = 0 := by
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint]
  rfl

/-- **The domain of `r_g` at a closed point.** The point of `𝐏(V)` cut out by a nonzero
functional `f` lies outside `U(g)` exactly when `f ∘ g = 0`: the complement of `U(g)` is the
linear subspace cut out by the image of `g`, and the degree-one forms vanishing at the point are
the vectors killed by `f`. -/
public theorem notMem_endDomain_linearFunctionalPoint_iff (f : Module.Dual k V) (hf : f ≠ 0)
    (g : V →ₗ[k] V) :
    linearFunctionalPoint k V f hf ∉ endDomain k V g ↔ f ∘ₗ g = 0 := by
  rw [notMem_endDomain_iff, linearFunctionalPoint_mem_linearSubspace_iff]
  simp [LinearMap.ext_iff]

variable [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]

/-- **A nonempty closed subset of `𝐏(V)` contains a point cut out by a functional.** Being of
finite type over a field, `𝐏(V)` is locally Noetherian, so a nonempty closed subset has a point
that is closed in `𝐏(V)`; over an algebraically closed field such a point is cut out by a
nonzero linear functional. -/
public theorem exists_linearFunctionalPoint_mem_of_isClosed
    {Z : Set (projectiveSpaceOfModule k V)} (hZ : Z.Nonempty) (hZc : IsClosed Z) :
    ∃ (f : Module.Dual k V) (hf : f ≠ 0), linearFunctionalPoint k V f hf ∈ Z := by
  obtain ⟨p, hpZ, hpc⟩ :=
    nonempty_inter_closedPoints_of_isClosed (projectiveSpaceOfModule k V) hZ hZc
  obtain ⟨q, hq⟩ := closedPointOfDual_surjective k V ⟨p, mem_closedPoints_iff.mp hpc⟩
  refine ⟨q.rep, q.rep_nonzero, ?_⟩
  have hp : linearFunctionalPoint k V q.rep q.rep_nonzero = p := by
    rw [← closedPointOfDual_mk k V q.rep q.rep_nonzero, Projectivization.mk_rep, hq]
  rw [hp]
  exact hpZ

/-- **Clause (1) of Tag 0B1S is tested on closed points.** A closed subset of `𝐏(V)` lies in the
domain of definition `U(g)` of the projective transformation attached to `g` as soon as every
one of its points cut out by a functional does, because the locus where it fails is closed. -/
public theorem subset_endDomain_of_forall_linearFunctionalPoint
    {X : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (g : V →ₗ[k] V)
    (hX : ∀ (f : Module.Dual k V) (hf : f ≠ 0),
      linearFunctionalPoint k V f hf ∈ X → f ∘ₗ g ≠ 0) :
    X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)) := by
  by_contra hsub
  obtain ⟨q, hqX, hqg⟩ := Set.not_subset.mp hsub
  obtain ⟨f, hf, hfmem⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V
    (Z := X ∩ linearSubspace k V (LinearMap.range g))
    ⟨q, hqX, (notMem_endDomain_iff k V g q).mp hqg⟩
    (hXc.inter (isClosed_linearSubspace k V _))
  exact hX f hf hfmem.1 ((notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mp
    ((notMem_endDomain_iff k V g _).mpr hfmem.2))

omit [IsAlgClosed k] in
/-- `𝐏(V)` is irreducible, so two closed subsets neither of which is everything do not cover
it. -/
private theorem union_ne_univ {A B : Set (projectiveSpaceOfModule k V)} (hA : IsClosed A)
    (hB : IsClosed B) (hAne : A ≠ Set.univ) (hBne : B ≠ Set.univ) : A ∪ B ≠ Set.univ := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hirr : IrreducibleSpace (projectiveSpaceOfModule k V) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k V hn
  intro hcover
  obtain ⟨x, -, hxA, hxB⟩ :=
    (IrreducibleSpace.isIrreducible_univ (projectiveSpaceOfModule k V)).2 Aᶜ Bᶜ
      hA.isOpen_compl hB.isOpen_compl
      (by simpa using Set.nonempty_compl.mpr hAne) (by simpa using Set.nonempty_compl.mpr hBne)
  have hx : x ∈ A ∪ B := hcover ▸ Set.mem_univ x
  rcases hx with h | h
  · exact hxA h
  · exact hxB h

omit [IsAlgClosed k] in
/-- A nonzero vector is not killed by every linear functional. -/
private theorem exists_dual_apply_ne_zero {w : V} (hw : w ≠ 0) :
    ∃ f : Module.Dual k V, f w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw (by simpa using (Module.forall_dual_apply_eq_zero_iff k w).mp hc)

/-- **Independent functionals whose points avoid a proper closed subset.** For every `m` at most
the dimension of `V` there are `m` linearly independent functionals none of which cuts out a
point of a given proper closed subset `X` of `𝐏(V)`. The inductive step intersects `X` with the
linear subspace cut out by the common kernel of the functionals already chosen: that kernel is
nonzero as long as `m` is below the dimension, so the subspace is proper, and `𝐏(V)` is
irreducible, so the union is still proper and misses a closed point. -/
private theorem exists_linearIndependent_forall_notMem
    {X : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hXne : X ≠ Set.univ) :
    ∀ m : ℕ, m ≤ Module.finrank k V →
      ∃ (s : Fin m → Module.Dual k V) (hs : ∀ i, s i ≠ 0), LinearIndependent k s ∧
        ∀ i, linearFunctionalPoint k V (s i) (hs i) ∉ X := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i =>
      i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨s, hs, hind, hnot⟩ := ih (by omega)
    have hWdim : Module.finrank k V ≤
        m + Module.finrank k ↥(LinearMap.ker (LinearMap.pi s)) := by
      have hrk := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi s)
      have hle : Module.finrank k ↥(LinearMap.range (LinearMap.pi s)) ≤ m := by
        refine le_trans (Submodule.finrank_le _) ?_
        simp
      omega
    set W : Submodule k V := LinearMap.ker (LinearMap.pi s) with hW
    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot] at hWdim
      simp only [finrank_bot, add_zero] at hWdim
      omega
    have hLSne : linearSubspace k V W ≠ Set.univ := by
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
      obtain ⟨f, hf⟩ := exists_dual_apply_ne_zero k V hw0
      have hf0 : f ≠ 0 := fun h => hf (by rw [h]; rfl)
      intro huniv
      have hmem : linearFunctionalPoint k V f hf0 ∈ linearSubspace k V W := huniv ▸ Set.mem_univ _
      exact hf ((linearFunctionalPoint_mem_linearSubspace_iff k V W f hf0).mp hmem w hwW)
    obtain ⟨f, hf0, hfnot⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k V
      (hXc.union (isClosed_linearSubspace k V W))
      (union_ne_univ k V hXc (isClosed_linearSubspace k V W) hXne hLSne)
    have hfX : linearFunctionalPoint k V f hf0 ∉ X := fun h => hfnot (Or.inl h)
    have hfspan : f ∉ Submodule.span k (Set.range s) := by
      intro hmem
      refine hfnot (Or.inr ?_)
      rw [linearFunctionalPoint_mem_linearSubspace_iff]
      intro w hw
      refine Submodule.span_induction (p := fun g _ => g w = 0) ?_ rfl
        (fun a b _ _ ha hb => by simp [ha, hb]) (fun c a _ ha => by simp [ha]) hmem
      rintro _ ⟨i, rfl⟩
      have hzero : LinearMap.pi s w = 0 := by rw [hW] at hw; exact hw
      simpa using congrFun hzero i
    refine ⟨Fin.cons f s, ?_, ?_, ?_⟩
    · exact Fin.cases hf0 hs
    · exact (linearIndependent_finCons).mpr ⟨hind, hfspan⟩
    · refine Fin.cases ?_ ?_
      · exact hfX
      · exact hnot

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The point cut out by a functional is unchanged by a nonzero scalar multiple. -/
private theorem linearFunctionalPoint_smul {α : k} (hα : α ≠ 0) (f : Module.Dual k V)
    (hf : f ≠ 0) (hαf : α • f ≠ 0) :
    linearFunctionalPoint k V (α • f) hαf = linearFunctionalPoint k V f hf := by
  have h := linearFunctionalPoint_units_smul k V (Units.mk0 α hα) f hf (by simpa using hαf)
  simpa using h

/-- **A basis of the dual avoiding a proper closed subset.** A proper closed subset of `𝐏(V)`
contains none of the points cut out by the members of some basis of `Vᵛ`. -/
public theorem exists_basis_dual_forall_linearFunctionalPoint_notMem
    {X : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hXne : X ≠ Set.univ) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k (Module.Dual k V),
      ∀ (i : Fin (Module.finrank k V)) (hb : b i ≠ 0),
        linearFunctionalPoint k V (b i) hb ∉ X := by
  obtain ⟨s, hs, hind, hnot⟩ :=
    exists_linearIndependent_forall_notMem k V hXc hXne (Module.finrank k V) le_rfl
  have hcard : Fintype.card (Fin (Module.finrank k V)) =
      Module.finrank k (Module.Dual k V) := by
    simp [Subspace.dual_finrank_eq]
  have : Nonempty (Fin (Module.finrank k V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hind hcard, fun i hb => ?_⟩
  have hcoe : (basisOfLinearIndependentOfCardEqFinrank hind hcard) i = s i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hind hcard) i
  rw [linearFunctionalPoint_eq_of_eq k V hb (hs i) hcoe]
  exact hnot i

/-- An injective family of scalars of any finite length: an algebraically closed field is
infinite, so an embedding of `ℕ` serves. -/
private theorem exists_injective_fin (m : ℕ) :
    ∃ l : Fin m → k, Function.Injective l :=
  ⟨Infinite.natEmbedding k ∘ Fin.val, (Infinite.natEmbedding k).injective.comp Fin.val_injective⟩

/-- **Clause (1) of Tag 0B1S holds along some line through `[id_V]`.** For a closed subset
`X ⊊ 𝐏(V)` there is an endomorphism `h` of `V`, not a scalar multiple of the identity once `V`
has dimension at least two, such that `X` lies in the domain of definition `U(a·id + b·h)` of
the projective transformation attached to every nonzero point `(a, b)` of the line spanned by
`id_V` and `h`.

Take a basis `f₀, …, fₙ` of `Vᵛ` none of whose members cuts out a point of `X`, let `e₀, …, eₙ`
be the biorthogonal basis of `V` and let `h` act on it diagonally with pairwise distinct
eigenvalues. A closed point of `X` cut out by `f` would otherwise satisfy
`f ∘ (a·id + b·h) = 0`, which forces `b ≠ 0` and makes `f` an eigenvector of the transpose of
`h`; the distinct eigenvalues make every such `f` a multiple of some `fᵢ`, whose point is off
`X`. -/
public theorem exists_forall_subset_endDomain_line
    {X : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hXne : X ≠ Set.univ) :
    ∃ h : V →ₗ[k] V, (2 ≤ Module.finrank k V → ∀ c : k, h ≠ c • LinearMap.id) ∧
      ∀ a b : k, (a ≠ 0 ∨ b ≠ 0) →
        X ⊆ (endDomain k V (a • LinearMap.id + b • h) :
          Set (projectiveSpaceOfModule k V)) := by
  classical
  obtain ⟨bd, hbd⟩ := exists_basis_dual_forall_linearFunctionalPoint_notMem k V hXc hXne
  set e : Module.Basis (Fin (Module.finrank k V)) k V :=
    bd.dualBasis.map (Module.evalEquiv k V).symm with he
  have hbe : ∀ i j, bd i (e j) = if j = i then (1 : k) else 0 := by
    intro i j
    have hej : e j = (Module.evalEquiv k V).symm (bd.dualBasis j) := by rw [he]; rfl
    rw [hej, Module.apply_evalEquiv_symm_apply, Module.Basis.dualBasis_apply_self]
    simp [eq_comm]
  obtain ⟨l, hlinj⟩ := exists_injective_fin k (Module.finrank k V)
  have hh : ∀ i, (e.constr k fun i => l i • e i) (e i) = l i • e i := e.constr_basis k _
  refine ⟨e.constr k fun i => l i • e i, ?_, ?_⟩
  · intro h2 c hc
    have hval : ∀ i, l i = c := by
      intro i
      have h1 := hh i
      rw [hc] at h1
      have h2' : (l i - c) • e i = 0 := by
        rw [sub_smul]
        simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at h1
        rw [← h1]
        simp
      rcases smul_eq_zero.mp h2' with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h (e.ne_zero i)
    exact absurd (hlinj ((hval ⟨0, by omega⟩).trans (hval ⟨1, by omega⟩).symm))
      (by simp [Fin.ext_iff])
  · intro a b hab
    refine subset_endDomain_of_forall_linearFunctionalPoint k V hXc _ ?_
    intro f hf hfX hzero
    have hcoord : ∀ i, (a + b * l i) * f (e i) = 0 := by
      intro i
      have h1 := LinearMap.congr_fun hzero (e i)
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, LinearMap.zero_apply, hh, map_add, map_smul,
        smul_eq_mul] at h1
      linear_combination h1
    obtain ⟨j, hj⟩ : ∃ j, f (e j) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf (e.ext fun i => by simp [hc i])
    have hbj : b ≠ 0 := by
      rintro rfl
      have := hcoord j
      simp only [zero_mul, add_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact (hab.resolve_right (by simp)) h
      · exact hj h
    have hlj : a + b * l j = 0 := by
      rcases mul_eq_zero.mp (hcoord j) with h | h
      · exact h
      · exact absurd h hj
    have hother : ∀ i, i ≠ j → f (e i) = 0 := by
      intro i hij
      rcases mul_eq_zero.mp (hcoord i) with h | h
      · refine absurd (hlinj (mul_left_cancel₀ hbj ?_)) hij
        linear_combination h - hlj
      · exact h
    obtain ⟨α, hα, hfeq⟩ : ∃ α : k, α ≠ 0 ∧ f = α • bd j := by
      refine ⟨f (e j), hj, e.ext fun i => ?_⟩
      rw [LinearMap.smul_apply, hbe j i, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, hother i hij]
    subst hfeq
    exact hbd j (bd.ne_zero j)
      (linearFunctionalPoint_smul k V hα (bd j) (bd.ne_zero j) hf ▸ hfX)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
