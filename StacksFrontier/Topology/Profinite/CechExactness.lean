module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Category.Profinite.Nobeling.Induction
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Separation.Profinite
public import StacksFrontier.Algebra.Module.Projective.DedekindSubmodule

/-!
# Exactness of Čech complexes of continuous functions on profinite spaces

Let `π : T' → T` be a continuous surjection between profinite spaces. For `p ≥ 0` let
`T'ₚ ⊆ (T')^{p+1}` be the space of `(p+1)`-tuples of points of `T'` with a common image in `T`;
these form the Čech nerve of `π`, with face maps forgetting one coordinate. For an abelian group
`A` the alternating sums of the face maps make the functions on the `T'ₚ` into a complex.

The main result is that for a complete nonarchimedean topological abelian group `Y` (one whose
open subgroups form a basis of neighbourhoods of zero and which is the limit of its discrete
quotients by them) the complex `C(T'₀, Y) → C(T'₁, Y) → ⋯` of continuous functions is exact in
every positive degree.

The proof has three steps.

* For discrete coefficients a cocycle is, on the fibre over a point `t` of `T`, the coboundary of
  the cochain obtained by inserting a fixed point `y` of the fibre as first coordinate. That
  cochain extends to a locally constant cochain on all of `T'ₚ`, and by the tube lemma it still
  bounds the cocycle over a clopen neighbourhood of `t`. Finitely many such neighbourhoods
  partition `T`, and the cochains glue along the partition.
* For coefficients `ℤ`, the groups of locally constant functions are free by Nöbeling's theorem,
  and subgroups of free abelian groups are projective, so the augmented complex, being exact,
  is split: it carries a contracting homotopy.
* Extending scalars along the homotopy gives contracting homotopies for every group of discrete
  coefficients, compatible with all homomorphisms of coefficients. Applied to the discrete
  quotients of `Y` they produce compatible primitives of a cocycle, which assemble into a
  continuous primitive because `Y` is complete.

## Main definitions

* `Stacks.ProfiniteCech.FibrePower`: the space `T'ₚ` of `(p+1)`-tuples with a common image.
* `Stacks.ProfiniteCech.cechD`: the alternating sum of the face maps on functions.
* `Stacks.ProfiniteCech.IsProDiscrete`: completeness of a topological abelian group with respect
  to its open subgroups.

## Main results

* `Stacks.ProfiniteCech.exists_isLocallyConstant_cechD_eq`: exactness in positive degrees for
  locally constant functions with values in an abelian group.
* `Stacks.ProfiniteCech.exists_continuous_cechD_eq`: exactness in positive degrees for continuous
  functions with values in a complete nonarchimedean abelian group.

## Implementation notes

Degrees are those of the Čech complex: `T'ₚ` consists of `(p+1)`-tuples, so the complex starts
with `C(T'₀, Y) = C(T', Y)`. The augmented complex, which also has `C(T, Y)` in degree `-1`, is
only used for coefficients `ℤ`, where its exactness in degrees `-1` and `0` is the injectivity of
pulling back along `π` and descent of locally constant functions along the quotient map `π`.
-/

@[expose] public section

open CategoryTheory Topology Set Function

namespace Stacks.ProfiniteCech

section FibrePower

variable {T' T : Type*} [TopologicalSpace T'] [TopologicalSpace T] (π : C(T', T))

/-- The `p`-th term of the Čech nerve of `π`: the `(p+1)`-tuples of points of `T'` with a common
image in `T`. -/
abbrev FibrePower (p : ℕ) : Type _ := {x : Fin (p + 1) → T' // ∀ a b, π (x a) = π (x b)}

/-- The `j`-th face map, forgetting the `j`-th coordinate. -/
def face {p : ℕ} (j : Fin (p + 2)) (x : FibrePower π (p + 1)) : FibrePower π p :=
  ⟨x.1 ∘ j.succAbove, fun _ _ ↦ x.2 _ _⟩

/-- The coordinates of the `j`-th face of `x` are those of `x` with the `j`-th one removed. -/
@[simp]
lemma face_coe {p : ℕ} (j : Fin (p + 2)) (x : FibrePower π (p + 1)) :
    (face π j x).1 = x.1 ∘ j.succAbove := rfl

/-- The face maps are continuous. -/
lemma continuous_face {p : ℕ} (j : Fin (p + 2)) : Continuous (face π (p := p) j) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun a ↦ (continuous_apply (j.succAbove a)).comp continuous_subtype_val

/-- The common image in `T` of the coordinates of a tuple. -/
def basePt {p : ℕ} (x : FibrePower π p) : T := π (x.1 0)

/-- Every coordinate of a tuple lies over its base point. -/
lemma basePt_eq {p : ℕ} (x : FibrePower π p) (a : Fin (p + 1)) : basePt π x = π (x.1 a) :=
  x.2 0 a

/-- A face of a tuple has the same base point as the tuple. -/
@[simp]
lemma basePt_face {p : ℕ} (j : Fin (p + 2)) (x : FibrePower π (p + 1)) :
    basePt π (face π j x) = basePt π x :=
  x.2 _ _

/-- The base point of a tuple depends continuously on the tuple. -/
lemma continuous_basePt {p : ℕ} : Continuous (basePt π (p := p)) :=
  π.continuous.comp ((continuous_apply _).comp continuous_subtype_val)

/-- The tuple `(y, x₀, …, xₚ)`, for `y` in the fibre containing the `xᵢ`. -/
def consPt {p : ℕ} (y : T') (x : FibrePower π p) (h : basePt π x = π y) :
    FibrePower π (p + 1) :=
  ⟨Fin.cons y x.1, by
    have key : ∀ a : Fin (p + 2), π (Fin.cons (α := fun _ ↦ T') y x.1 a) = π y := by
      intro a
      refine Fin.cases ?_ (fun a ↦ ?_) a
      · simp
      · simpa using ((basePt_eq π x a).symm.trans h)
    intro a b
    rw [key a, key b]⟩

/-- Forgetting the first coordinate of `(y, x₀, …, xₚ₊₁)` gives back `x`. -/
lemma face_zero_consPt {p : ℕ} (y : T') (x : FibrePower π (p + 1)) (h : basePt π x = π y) :
    face π 0 (consPt π y x h) = x := by
  apply Subtype.ext
  funext a
  simp [consPt]

/-- The `(k+1)`-th face of `(y, x₀, …, xₚ₊₁)` is `y` followed by the `k`-th face of `x`. -/
lemma face_succ_consPt {p : ℕ} (y : T') (x : FibrePower π (p + 1)) (h : basePt π x = π y)
    (k : Fin (p + 2)) :
    face π k.succ (consPt π y x h) =
      consPt π y (face π k x) ((basePt_face π k x).trans h) := by
  apply Subtype.ext
  simp only [face_coe, consPt]
  rw [Fin.cons_comp_succ_succAbove]
  rfl

/-- The fibre power is closed in the space of all tuples. -/
lemma isClosed_fibrePower [T2Space T] (p : ℕ) :
    IsClosed {x : Fin (p + 1) → T' | ∀ a b, π (x a) = π (x b)} := by
  simp only [setOf_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
    isClosed_eq (π.continuous.comp (continuous_apply a)) (π.continuous.comp (continuous_apply b))

/-- The fibre powers of a map from a compact space to a Hausdorff space are compact. -/
instance [CompactSpace T'] [T2Space T] (p : ℕ) : CompactSpace (FibrePower π p) :=
  isCompact_iff_compactSpace.mp (isClosed_fibrePower π p).isCompact

/-- The fibre powers of a Hausdorff space are Hausdorff. -/
instance [T2Space T'] (p : ℕ) : T2Space (FibrePower π p) := inferInstance

/-- The fibre powers of a totally disconnected space are totally disconnected. -/
instance [TotallyDisconnectedSpace T'] (p : ℕ) : TotallyDisconnectedSpace (FibrePower π p) :=
  inferInstance

end FibrePower

section Differential

variable {T' T : Type*} [TopologicalSpace T'] [TopologicalSpace T] (π : C(T', T))
  {A : Type*} [AddCommGroup A]

/-- The structure map of the Čech nerve along a morphism of the simplex category. -/
def nerveMap {m n : SimplexCategory} (θ : m ⟶ n) (x : FibrePower π n.len) :
    FibrePower π m.len :=
  ⟨x.1 ∘ θ.toOrderHom, fun _ _ ↦ x.2 _ _⟩

/-- The structure map of the Čech nerve along the coface map `δ j` is the face map `face π j`. -/
lemma nerveMap_δ {p : ℕ} (j : Fin (p + 2)) (x : FibrePower π (p + 1)) :
    nerveMap π (SimplexCategory.δ j) x = face π j x := rfl

variable (A) in
/-- The cosimplicial abelian group of all `A`-valued functions on the Čech nerve. -/
def functionsCosimplicial : CosimplicialObject AddCommGrpCat where
  obj n := AddCommGrpCat.of (FibrePower π n.len → A)
  map θ := AddCommGrpCat.ofHom
    { toFun c := c ∘ nerveMap π θ
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Čech differential: the alternating sum of the pullbacks along the face maps, that is,
the differential of the alternating coface complex of `functionsCosimplicial`. -/
def cechD (p : ℕ) (c : FibrePower π p → A) : FibrePower π (p + 1) → A :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (functionsCosimplicial π A) p).hom c

/-- The Čech differential is the alternating sum `(d c)(x) = ∑ⱼ (-1)ʲ c(∂ⱼ x)`. -/
lemma cechD_apply (p : ℕ) (c : FibrePower π p → A) (x : FibrePower π (p + 1)) :
    cechD π p c x = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • c (face π j x) := by
  have e : ∀ s : Finset (Fin (p + 2)),
      (∑ i ∈ s, (-1 : ℤ) ^ (i : ℕ) • (functionsCosimplicial π A).δ i).hom c x =
        ∑ i ∈ s, (-1 : ℤ) ^ (i : ℕ) • c (face π i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, AddCommGrpCat.hom_add]
      exact congrArg₂ (· + ·) rfl ih
  exact e Finset.univ

/-- The Čech differential composed with itself vanishes. -/
lemma cechD_cechD (p : ℕ) (c : FibrePower π p → A) :
    cechD π (p + 1) (cechD π p c) = 0 := by
  show (AlgebraicTopology.AlternatingCofaceMapComplex.objD (functionsCosimplicial π A) p ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD (functionsCosimplicial π A) (p + 1)).hom c
      = 0
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.d_squared]
  rfl

/-- The Čech differential is additive. -/
lemma cechD_add (p : ℕ) (c c' : FibrePower π p → A) :
    cechD π p (c + c') = cechD π p c + cechD π p c' := by
  funext x
  simp only [cechD_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- The Čech differential commutes with subtraction. -/
lemma cechD_sub (p : ℕ) (c c' : FibrePower π p → A) :
    cechD π p (c - c') = cechD π p c - cechD π p c' := by
  funext x
  simp only [cechD_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- The Čech differential of the zero cochain is zero. -/
lemma cechD_zero (p : ℕ) : cechD π p (0 : FibrePower π p → A) = 0 := by
  funext x
  simp [cechD_apply]

/-- The Čech differential commutes with postcomposition by a homomorphism. -/
lemma cechD_comp {B : Type*} [AddCommGroup B] (ψ : A →+ B) (p : ℕ) (c : FibrePower π p → A) :
    cechD π p (ψ ∘ c) = ψ ∘ cechD π p c := by
  funext x
  simp [cechD_apply, map_sum, map_zsmul]

/-- The Čech differential of a locally constant cochain is locally constant. -/
lemma isLocallyConstant_cechD (p : ℕ) {c : FibrePower π p → A} (hc : IsLocallyConstant c) :
    IsLocallyConstant (cechD π p c) := by
  rw [show cechD π p c = fun x ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • c (face π j x) from
    funext (cechD_apply π p c)]
  have : ∀ s : Finset (Fin (p + 2)), IsLocallyConstant
      (fun x : FibrePower π (p + 1) ↦ ∑ j ∈ s, (-1 : ℤ) ^ (j : ℕ) • c (face π j x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact IsLocallyConstant.const (0 : A)
    | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact IsLocallyConstant.add
        (((hc.comp_continuous (continuous_face π j))).comp _) ih
  exact this Finset.univ

/-- The Čech differential of a continuous cochain with values in a topological group is
continuous. -/
lemma continuous_cechD [TopologicalSpace A] [IsTopologicalAddGroup A] (p : ℕ)
    {c : FibrePower π p → A} (hc : Continuous c) : Continuous (cechD π p c) := by
  rw [show cechD π p c = fun x ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • c (face π j x) from
    funext (cechD_apply π p c)]
  refine continuous_finset_sum _ fun j _ ↦ ?_
  exact (hc.comp (continuous_face π j)).zsmul _

/-- **The homotopy identity on a fibre.** Inserting a point `y` of the fibre as the first
coordinate is a contracting homotopy over that fibre:
`(d c)(y, x) = c(x) - ∑ₖ (-1)ᵏ c(y, ∂ₖ x)`. -/
lemma cechD_consPt (p : ℕ) (c : FibrePower π (p + 1) → A) (y : T')
    (x : FibrePower π (p + 1)) (h : basePt π x = π y) :
    cechD π (p + 1) c (consPt π y x h) =
      c x - ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        c (consPt π y (face π k x) ((basePt_face π k x).trans h)) := by
  rw [cechD_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_zero_consPt, Fin.val_succ, pow_succ,
    face_succ_consPt, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_neg_one, neg_smul]

end Differential

section Extension

/-- **Locally constant functions extend from closed subsets of profinite spaces.** -/
theorem exists_isLocallyConstant_extend {Z B : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [T2Space Z] [TotallyDisconnectedSpace Z] [Nonempty B] {S : Set Z} (hS : IsClosed S)
    (f : S → B) (hf : IsLocallyConstant f) :
    ∃ F : Z → B, IsLocallyConstant F ∧ ∀ s : S, F s = f s := by
  classical
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  let I := Set.range f
  have : Finite I := hf.range_finite.to_subtype
  let Zs : I → Set Z := fun i ↦ Subtype.val '' (f ⁻¹' {i.1})
  have hZ : ∀ i, IsClosed (Zs i) := fun i ↦
    hS.isClosedMap_subtype_val _ (hf.isClopen_fiber _).isClosed
  have hdisj : Set.univ.PairwiseDisjoint Zs := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    obtain rfl : s' = s := Subtype.ext hss'
    exact hij (Subtype.ext ((Set.mem_singleton_iff.1 hs).symm.trans
      (Set.mem_singleton_iff.1 hs')))
  rcases isEmpty_or_nonempty I with hI | hI
  · refine ⟨fun _ ↦ Classical.arbitrary B, IsLocallyConstant.const _, fun s ↦ ?_⟩
    exact (hI.false ⟨f s, s, rfl⟩).elim
  obtain ⟨C, hCcl, hZC, -, hcov, hCdisj⟩ := exists_clopen_partition_of_clopen_cover hZ
    (fun _ ↦ isClopen_univ) (fun _ ↦ Set.subset_univ _) hdisj
  have hmem : ∀ z : Z, ∃ i, z ∈ C i := fun z ↦ by
    obtain ⟨i⟩ := hI
    exact Set.mem_iUnion.1 (hcov (Set.mem_iUnion.2 ⟨i, Set.mem_univ z⟩))
  choose idx hidx using hmem
  have hidx_eq : ∀ z i, z ∈ C i → idx z = i := fun z i hz ↦ by
    by_contra h
    exact Set.disjoint_left.1 (hCdisj (Set.mem_univ _) (Set.mem_univ _) h) (hidx z) hz
  refine ⟨fun z ↦ (idx z).1, ?_, fun s ↦ ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro z
    refine ⟨C (idx z), (hCcl _).isOpen, hidx z, fun z' hz' ↦ ?_⟩
    rw [hidx_eq z' _ hz']
  · have : (s : Z) ∈ C ⟨f s, s, rfl⟩ := hZC _ ⟨s, rfl, rfl⟩
    show (idx s).1 = f s
    rw [hidx_eq _ _ this]

end Extension

section DiscreteExactness

variable {T' T : Type*} [TopologicalSpace T'] [TopologicalSpace T]
  [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T']
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
  (π : C(T', T)) (hπ : Function.Surjective π) {A : Type*} [AddCommGroup A]

include hπ in
/-- Near the fibre over a point, a locally constant cocycle bounds a locally constant
cochain. -/
lemma exists_local_primitive {q : ℕ} (c : FibrePower π (q + 1) → A)
    (hc : IsLocallyConstant c) (hdc : cechD π (q + 1) c = 0) (t : T) :
    ∃ U : Set T, IsClopen U ∧ t ∈ U ∧ ∃ b : FibrePower π q → A, IsLocallyConstant b ∧
      ∀ x, basePt π x ∈ U → cechD π q b x = c x := by
  classical
  obtain ⟨y, rfl⟩ := hπ t
  obtain ⟨cbar, hcbar, hcbar_eq⟩ :=
    exists_isLocallyConstant_extend (isClosed_fibrePower π (q + 1)) c hc
  let btil : FibrePower π q → A := fun w ↦ cbar (Fin.cons y w.1)
  have hcons : Continuous fun w : FibrePower π q ↦ (Fin.cons y w.1 : Fin (q + 2) → T') := by
    refine continuous_pi fun a ↦ ?_
    refine Fin.cases ?_ (fun a ↦ ?_) a
    · simp only [Fin.cons_zero]
      exact continuous_const
    · simp only [Fin.cons_succ]
      exact (continuous_apply a).comp continuous_subtype_val
  have hbtil : IsLocallyConstant btil := hcbar.comp_continuous hcons
  have key : ∀ x : FibrePower π (q + 1), basePt π x = π y → cechD π q btil x = c x := by
    intro x hx
    have h1 := congrFun hdc (consPt π y x hx)
    rw [cechD_consPt, Pi.zero_apply, sub_eq_zero] at h1
    rw [cechD_apply, h1]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    exact hcbar_eq ⟨_, (consPt π y (face π k x) ((basePt_face π k x).trans hx)).2⟩
  let e : FibrePower π (q + 1) → A := c - cechD π q btil
  have he : IsLocallyConstant e := hc.sub (isLocallyConstant_cechD π q hbtil)
  let bad : Set (FibrePower π (q + 1)) := (e ⁻¹' {0})ᶜ
  have hbad : IsClosed bad := (he.isClopen_fiber 0).isOpen.isClosed_compl
  have himg : IsClosed (basePt π '' bad) :=
    (hbad.isCompact.image (continuous_basePt π)).isClosed
  have ht : π y ∉ basePt π '' bad := by
    rintro ⟨x, hx, hxt⟩
    exact hx (show e x = 0 from sub_eq_zero.2 (key x hxt).symm)
  obtain ⟨U, hU, htU, hUsub⟩ := compact_exists_isClopen_in_isOpen himg.isOpen_compl ht
  refine ⟨U, hU, htU, btil, hbtil, fun x hx ↦ ?_⟩
  by_contra hne
  exact hUsub hx ⟨x, fun h ↦ hne (sub_eq_zero.1 (show e x = 0 from h)).symm, rfl⟩

include hπ in
/-- **Exactness in positive degrees for locally constant functions.** A locally constant
`(q+1)`-cocycle on the Čech nerve of a surjection of profinite spaces is the coboundary of a
locally constant `q`-cochain. -/
theorem exists_isLocallyConstant_cechD_eq {q : ℕ} (c : FibrePower π (q + 1) → A)
    (hc : IsLocallyConstant c) (hdc : cechD π (q + 1) c = 0) :
    ∃ b : FibrePower π q → A, IsLocallyConstant b ∧ cechD π q b = c := by
  classical
  choose U hU htU b hb hbc using exists_local_primitive π hπ c hc hdc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U (fun t ↦ (hU t).isOpen)
    (fun t _ ↦ Set.mem_iUnion.2 ⟨t, htU t⟩)
  obtain ⟨C, hCcl, -, hCU, hcov, hCdisj⟩ := exists_clopen_partition_of_clopen_cover
    (I := s) (Z := fun _ ↦ ∅) (D := fun i ↦ U i.1) (fun _ ↦ isClosed_empty)
    (fun i ↦ hU i.1) (fun _ ↦ Set.empty_subset _) (fun _ _ _ _ _ ↦ disjoint_bot_left)
  have hmem : ∀ t : T, ∃ i : s, t ∈ C i := fun t ↦ by
    obtain ⟨t', ht', htt'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
    exact Set.mem_iUnion.1 (hcov (Set.mem_iUnion.2 ⟨⟨t', ht'⟩, htt'⟩))
  choose idx hidx using hmem
  have hidx_eq : ∀ t i, t ∈ C i → idx t = i := fun t i ht ↦ by
    by_contra h
    exact Set.disjoint_left.1 (hCdisj (Set.mem_univ _) (Set.mem_univ _) h) (hidx t) ht
  refine ⟨fun w ↦ b (idx (basePt π w)).1 w, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro w
    obtain ⟨V, hV, hwV, hVc⟩ := (IsLocallyConstant.iff_exists_open _).1 (hb (idx (basePt π w)).1) w
    refine ⟨basePt π ⁻¹' C (idx (basePt π w)) ∩ V,
      ((hCcl _).isOpen.preimage (continuous_basePt π)).inter hV, ⟨hidx _, hwV⟩, ?_⟩
    rintro w' ⟨hw'C, hw'V⟩
    rw [hidx_eq _ _ hw'C]
    exact hVc w' hw'V
  · funext x
    rw [cechD_apply]
    simp only [basePt_face]
    rw [← cechD_apply]
    exact hbc _ x (hCU _ (hidx _))

omit [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [TotallyDisconnectedSpace T] in
include hπ in
/-- Exactness in degree zero: a locally constant function on `T'` whose two pullbacks to
`T' ×_T T'` agree descends to a locally constant function on `T`. -/
theorem exists_isLocallyConstant_eq_comp_basePt (c : FibrePower π 0 → A)
    (hc : IsLocallyConstant c) (hdc : cechD π 0 c = 0) :
    ∃ b : T → A, IsLocallyConstant b ∧ c = b ∘ basePt π := by
  classical
  choose sec hsec using hπ
  let single : T' → FibrePower π 0 := fun y ↦ ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩
  have hsingle : Continuous single := Continuous.subtype_mk (continuous_pi fun _ ↦ continuous_id) _
  have hrel : ∀ (y : T') (x : FibrePower π 0) (h : basePt π x = π y), c x = c (single y) := by
    intro y x h
    have h1 := congrFun hdc (consPt π y x h)
    rw [cechD_apply, Fin.sum_univ_two, Pi.zero_apply] at h1
    have e0 : face π 0 (consPt π y x h) = x := by
      apply Subtype.ext; funext a; simp [consPt]
    have e1 : face π 1 (consPt π y x h) = single y := by
      apply Subtype.ext; funext a
      rw [Fin.fin_one_eq_zero a]
      simp [consPt, single]
    rw [e0, e1] at h1
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h1
    exact add_neg_eq_zero.1 h1
  let b : T → A := fun t ↦ c (single (sec t))
  have hb : c = b ∘ basePt π := funext fun x ↦ hrel _ x (hsec _).symm
  refine ⟨b, ?_, hb⟩
  have hq : IsQuotientMap π := π.continuous.isClosedMap.isQuotientMap π.continuous
    (fun t ↦ ⟨sec t, hsec t⟩)
  have hbπ : b ∘ π = c ∘ single := funext fun y ↦
    (hrel _ (single y) ((hsec (π y)).symm)).symm
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro a
  rw [← hq.isOpen_preimage, ← Set.preimage_comp, hbπ]
  exact ((hc.comp_continuous hsingle).isClopen_fiber a).isOpen

omit [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T] in
include hπ in
/-- Pulling back along the augmentation `T'₀ → T` is injective. -/
theorem eq_zero_of_comp_basePt_eq_zero (b : T → A) (hb : b ∘ basePt π (p := 0) = 0) :
    b = 0 := by
  funext t
  obtain ⟨y, rfl⟩ := hπ t
  exact congrFun hb ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩

end DiscreteExactness

section ScalarExtension

/-! ### Extending a homomorphism of groups of `ℤ`-valued locally constant functions to
arbitrary coefficients -/

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {A B : Type*}
  [AddCommGroup A] [AddCommGroup B]

/-- Evaluation of a finite sum of locally constant functions is the sum of the evaluations. -/
lemma LC_sum_apply {ι : Type*} (s : Finset ι) (f : ι → LocallyConstant Z A) (z : Z) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z :=
  map_sum (LocallyConstant.evalAddMonoidHom z) f s

/-- The locally constant function `z ↦ φ(z) • a`. -/
def smulConst (φ : LocallyConstant Z ℤ) (a : A) : LocallyConstant Z A := φ.map fun n ↦ n • a

/-- The value of `smulConst φ a` at `z` is `φ z • a`. -/
@[simp]
lemma smulConst_apply (φ : LocallyConstant Z ℤ) (a : A) (z : Z) :
    smulConst φ a z = φ z • a := rfl

/-- `smulConst` is additive in the `ℤ`-valued function. -/
lemma smulConst_add_left (φ ψ : LocallyConstant Z ℤ) (a : A) :
    smulConst (φ + ψ) a = smulConst φ a + smulConst ψ a :=
  LocallyConstant.ext fun _ ↦ add_smul _ _ _

/-- `smulConst` is additive in the coefficient. -/
lemma smulConst_add_right (φ : LocallyConstant Z ℤ) (a b : A) :
    smulConst φ (a + b) = smulConst φ a + smulConst φ b :=
  LocallyConstant.ext fun _ ↦ smul_add _ _ _

/-- `smulConst` of the zero function is zero. -/
lemma smulConst_zero_left (a : A) : smulConst (0 : LocallyConstant Z ℤ) a = 0 :=
  LocallyConstant.ext fun _ ↦ zero_smul _ _

/-- `smulConst` commutes with finite sums in the `ℤ`-valued function. -/
lemma smulConst_sum_left {ι : Type*} (s : Finset ι) (φ : ι → LocallyConstant Z ℤ) (a : A) :
    smulConst (∑ i ∈ s, φ i) a = ∑ i ∈ s, smulConst (φ i) a :=
  LocallyConstant.ext fun z ↦ by simp [LC_sum_apply, Finset.sum_smul]

/-- An integer multiple of the `ℤ`-valued function may be moved onto the coefficient. -/
lemma smulConst_zsmul_left (n : ℤ) (φ : LocallyConstant Z ℤ) (a : A) :
    smulConst (n • φ) a = smulConst φ (n • a) :=
  LocallyConstant.ext fun z ↦ by
    show (n • φ z) • a = φ z • (n • a)
    rw [smul_eq_mul, smul_smul, mul_comm]

/-- Postcomposing `smulConst φ a` with a homomorphism `ψ` gives `smulConst φ (ψ a)`. -/
lemma map_smulConst (ψ : A →+ B) (φ : LocallyConstant Z ℤ) (a : A) :
    (smulConst φ a).map ψ = smulConst φ (ψ a) :=
  LocallyConstant.ext fun z ↦ by simp [LocallyConstant.map_apply]

/-- The indicator function of the fibre `q⁻¹(i)` of a locally constant map. -/
noncomputable def fibreInd {ι : Type*} (q : LocallyConstant X ι) (i : ι) :
    LocallyConstant X ℤ :=
  open scoped Classical in q.map fun j ↦ if j = i then 1 else 0

/-- The indicator `fibreInd q i` takes the value `1` at `x` if `q x = i`, and `0` otherwise. -/
lemma fibreInd_apply {ι : Type*} (q : LocallyConstant X ι) (i : ι) (x : X) :
    fibreInd q i x = open scoped Classical in if q x = i then 1 else 0 := rfl

/-- The indicator of a fibre `q⁻¹(i)` vanishes when `q` never takes the value `i`. -/
private lemma fibreInd_eq_zero {ι : Type*} (q : LocallyConstant X ι) (i : ι) (h : ∀ x, q x ≠ i) :
    fibreInd q i = 0 := by
  ext x
  simp [fibreInd_apply, h x]

/-- A locally constant function factoring through `q` is a finite combination of the
indicators of the fibres of `q`. -/
lemma eq_sum_smulConst_fibreInd {ι : Type*} (q : LocallyConstant X ι) (R : Finset ι)
    (hR : ∀ x, q x ∈ R) (h : ι → A) :
    q.map h = ∑ i ∈ R, smulConst (fibreInd q i) (h i) := by
  classical
  ext x
  rw [LC_sum_apply]
  simp only [smulConst_apply, fibreInd_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, if_pos (hR x), LocallyConstant.map_apply, Function.comp_apply]

variable (s : LocallyConstant X ℤ →+ LocallyConstant Z ℤ)

/-- Extension of `s` along a factorization through a locally constant `q`. -/
noncomputable def extendAlong {ι : Type*} (q : LocallyConstant X ι) (R : Finset ι)
    (h : ι → A) : LocallyConstant Z A :=
  ∑ i ∈ R, smulConst (s (fibreInd q i)) (h i)

/-- `extendAlong` is additive in the coefficient function `h`. -/
lemma extendAlong_add {ι : Type*} (q : LocallyConstant X ι) (R : Finset ι) (h h' : ι → A) :
    extendAlong s q R (h + h') = extendAlong s q R h + extendAlong s q R h' := by
  simp [extendAlong, smulConst_add_right, Finset.sum_add_distrib]

/-- Postcomposing the extension along `q` of `h` with `ψ` gives the extension of `ψ ∘ h`. -/
lemma map_extendAlong {ι : Type*} (q : LocallyConstant X ι) (R : Finset ι) (h : ι → A)
    (ψ : A →+ B) : (extendAlong s q R h).map ψ = extendAlong s q R (ψ ∘ h) := by
  rw [extendAlong, extendAlong, ← LocallyConstant.mapAddMonoidHom_apply, map_sum]
  simp [map_smulConst]

/-- Refining the factorization does not change the extension. -/
lemma extendAlong_refine {ι ι' : Type*} (q : LocallyConstant X ι) (R : Finset ι)
    (q' : LocallyConstant X ι') (R' : Finset ι') (hR' : ∀ x, q' x ∈ R')
    (r : ι' → ι) (hr : ∀ x, r (q' x) ∈ R) (hq : ∀ x, q x = r (q' x)) (h : ι → A) :
    extendAlong s q R h = extendAlong s q' R' (h ∘ r) := by
  classical
  let S := R'.filter fun i' ↦ r i' ∈ R
  have hind : ∀ i ∈ R, fibreInd q i = ∑ i' ∈ S with r i' = i, fibreInd q' i' := by
    intro i _
    ext x
    rw [LC_sum_apply]
    simp only [fibreInd_apply, hq, S]
    by_cases hx : r (q' x) = i
    · subst hx
      simp [hR' x, hr x]
    · simp [hx]
  have step : ∀ i ∈ R, smulConst (s (fibreInd q i)) (h i) =
      ∑ i' ∈ S with r i' = i, smulConst (s (fibreInd q' i')) (h (r i')) := by
    intro i hi
    rw [hind i hi, map_sum, smulConst_sum_left]
    exact Finset.sum_congr rfl fun i' hi' ↦ by rw [(Finset.mem_filter.1 hi').2]
  unfold extendAlong
  rw [Finset.sum_congr rfl step,
    Finset.sum_fiberwise_of_maps_to (g := r) (fun i' hi' ↦ (Finset.mem_filter.1 hi').2)]
  refine Finset.sum_filter_of_ne fun i' _ hne ↦ ?_
  by_contra hi'
  apply hne
  rw [fibreInd_eq_zero q' i' fun x hx ↦ hi' (hx ▸ hr x), map_zero, smulConst_zero_left]

/-- The extension along `q` depends only on the values of `h` on the range of `q`. -/
lemma extendAlong_congr {ι : Type*} (q : LocallyConstant X ι) (R : Finset ι)
    {h h' : ι → A} (hh : ∀ x, h (q x) = h' (q x)) :
    extendAlong s q R h = extendAlong s q R h' := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : ∃ x, q x = i
  · obtain ⟨x, rfl⟩ := hi
    rw [hh x]
  · rw [fibreInd_eq_zero q i fun x h ↦ hi ⟨x, h⟩, map_zero, smulConst_zero_left,
      smulConst_zero_left]

variable [CompactSpace X]

/-- Every value of a locally constant function lies in the finset of its values. -/
private lemma apply_mem_range_toFinset {α : Type*} (f : LocallyConstant X α) (x : X) :
    f x ∈ f.range_finite.toFinset :=
  (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩

variable (A) in
/-- **The extension of `s` to coefficients `A`**, characterized by
`extendScalars s (φ · a) = (s φ) · a`. -/
noncomputable def extendScalarsFun (f : LocallyConstant X A) : LocallyConstant Z A :=
  extendAlong s f f.range_finite.toFinset id

/-- `extendScalarsFun A s f` is the extension along any factorization `f = h ∘ q` of `f` through
a locally constant `q` with values in `R`. -/
lemma extendScalarsFun_eq {ι : Type*} (f : LocallyConstant X A) (q : LocallyConstant X ι)
    (R : Finset ι) (hR : ∀ x, q x ∈ R) (h : ι → A) (hf : ∀ x, f x = h (q x)) :
    extendScalarsFun A s f = extendAlong s q R h := by
  unfold extendScalarsFun
  rw [extendAlong_refine s f f.range_finite.toFinset q R hR h
    (fun x ↦ by rw [Set.Finite.mem_toFinset, ← hf]; exact ⟨x, rfl⟩) hf id]
  rfl

/-- `extendScalarsFun` is additive. -/
lemma extendScalarsFun_add (f g : LocallyConstant X A) :
    extendScalarsFun A s (f + g) = extendScalarsFun A s f + extendScalarsFun A s g := by
  classical
  let q : LocallyConstant X (A × A) :=
    ⟨fun x ↦ (f x, g x), (f.isLocallyConstant.prodMk g.isLocallyConstant)⟩
  let R : Finset (A × A) := f.range_finite.toFinset ×ˢ g.range_finite.toFinset
  have hR : ∀ x, q x ∈ R := fun x ↦
    Finset.mem_product.2 ⟨apply_mem_range_toFinset f x, apply_mem_range_toFinset g x⟩
  rw [extendScalarsFun_eq s (f + g) q R hR (fun p ↦ p.1 + p.2) (fun _ ↦ rfl),
    extendScalarsFun_eq s f q R hR Prod.fst (fun _ ↦ rfl),
    extendScalarsFun_eq s g q R hR Prod.snd (fun _ ↦ rfl), ← extendAlong_add]
  rfl

variable (A) in
/-- The extension of `s` to coefficients `A`, as a homomorphism. -/
noncomputable def extendScalars : LocallyConstant X A →+ LocallyConstant Z A where
  toFun := extendScalarsFun A s
  map_zero' := by
    rw [extendScalarsFun_eq s 0 (0 : LocallyConstant X Unit) {()} (fun _ ↦ by simp)
      (fun _ ↦ 0) (fun _ ↦ rfl)]
    simp [extendAlong, smulConst]
    rfl
  map_add' := extendScalarsFun_add s

/-- `extendScalars A s f` is the extension along any factorization `f = h ∘ q` of `f` through a
locally constant `q` with values in `R`. -/
lemma extendScalars_eq {ι : Type*} (f : LocallyConstant X A) (q : LocallyConstant X ι)
    (R : Finset ι) (hR : ∀ x, q x ∈ R) (h : ι → A) (hf : ∀ x, f x = h (q x)) :
    extendScalars A s f = extendAlong s q R h :=
  extendScalarsFun_eq s f q R hR h hf

/-- The extension sends `φ · a` to `(s φ) · a`. -/
lemma extendScalars_smulConst (φ : LocallyConstant X ℤ) (a : A) :
    extendScalars A s (smulConst φ a) = smulConst (s φ) a := by
  classical
  let R := φ.range_finite.toFinset
  have hR : ∀ x, φ x ∈ R := apply_mem_range_toFinset φ
  rw [extendScalars_eq s _ φ R hR (fun n ↦ n • a) (fun _ ↦ rfl), extendAlong]
  simp_rw [← smulConst_zsmul_left, ← smulConst_sum_left, ← map_zsmul, ← map_sum]
  congr 2
  ext x
  rw [LC_sum_apply]
  simp only [LocallyConstant.coe_smul, Pi.smul_apply, fibreInd_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, if_pos (hR x)]

/-- The extension is natural in the coefficients. -/
lemma map_extendScalars (ψ : A →+ B) (f : LocallyConstant X A) :
    (extendScalars A s f).map ψ = extendScalars B s (f.map ψ) := by
  classical
  let R := f.range_finite.toFinset
  have hR : ∀ x, f x ∈ R := apply_mem_range_toFinset f
  rw [extendScalars_eq s f f R hR id (fun _ ↦ rfl),
    extendScalars_eq s (f.map ψ) f R hR ψ (fun _ ↦ rfl), map_extendAlong]
  rfl

omit [CompactSpace X] in
/-- **Transport of a homotopy identity to coefficients `A`.** If `d₀ s₀ + s₁ d₁ = id` for
homomorphisms of groups of `ℤ`-valued locally constant functions, and `d₀`, `d₁` have
counterparts with coefficients `A` compatible with `φ ↦ φ · a`, then the extended homotopies
satisfy the same identity. -/
lemma homotopy_extendScalars {X₀ X₂ : Type*} [TopologicalSpace X₀] [TopologicalSpace X₂]
    [CompactSpace X₂] (d₀ : LocallyConstant X₀ ℤ →+ LocallyConstant X ℤ)
    (d₁ : LocallyConstant X ℤ →+ LocallyConstant X₂ ℤ)
    (dA₀ : LocallyConstant X₀ A →+ LocallyConstant X A)
    (dA₁ : LocallyConstant X A →+ LocallyConstant X₂ A)
    (hd₀ : ∀ φ a, dA₀ (smulConst φ a) = smulConst (d₀ φ) a)
    (hd₁ : ∀ φ a, dA₁ (smulConst φ a) = smulConst (d₁ φ) a)
    (s₀ : LocallyConstant X ℤ →+ LocallyConstant X₀ ℤ)
    (s₁ : LocallyConstant X₂ ℤ →+ LocallyConstant X ℤ) [CompactSpace X]
    (hs : ∀ φ, d₀ (s₀ φ) + s₁ (d₁ φ) = φ) (f : LocallyConstant X A) :
    dA₀ (extendScalars A s₀ f) + extendScalars A s₁ (dA₁ f) = f := by
  classical
  let R := f.range_finite.toFinset
  have hR : ∀ x, f x ∈ R := apply_mem_range_toFinset f
  have hf : f = ∑ a ∈ R, smulConst (fibreInd f a) a := eq_sum_smulConst_fibreInd f R hR id
  have h1 : extendScalars A s₀ f = ∑ a ∈ R, smulConst (s₀ (fibreInd f a)) a :=
    extendScalars_eq s₀ f f R hR id fun _ ↦ rfl
  have h2 : dA₁ f = ∑ a ∈ R, smulConst (d₁ (fibreInd f a)) a := by
    conv_lhs => rw [hf]
    simp only [map_sum, hd₁]
  rw [h1, h2]
  simp only [map_sum, hd₀, extendScalars_smulConst, ← Finset.sum_add_distrib,
    ← smulConst_add_left, hs]
  exact hf.symm

end ScalarExtension

section Contraction

universe u

variable {T' T : Type u} [TopologicalSpace T'] [TopologicalSpace T]
  [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T']
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
  (π : C(T', T)) (A : Type*) [AddCommGroup A]

/-- The Čech differential on locally constant functions, as a homomorphism. -/
def cechDLC (p : ℕ) :
    LocallyConstant (FibrePower π p) A →+ LocallyConstant (FibrePower π (p + 1)) A where
  toFun c := ⟨cechD π p c, isLocallyConstant_cechD π p c.isLocallyConstant⟩
  map_zero' := LocallyConstant.ext fun x ↦ congrFun (cechD_zero π p) x
  map_add' c c' := LocallyConstant.ext fun x ↦ congrFun (cechD_add π p c c') x

omit [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T] in
/-- `cechDLC π A p` is the Čech differential on underlying functions. -/
@[simp]
lemma cechDLC_apply (p : ℕ) (c : LocallyConstant (FibrePower π p) A) (x : FibrePower π (p + 1)) :
    cechDLC π A p c x = cechD π p c x := rfl

omit [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T] in
/-- The Čech differential sends `φ · a` to `(d φ) · a`. -/
lemma cechDLC_smulConst (p : ℕ) (φ : LocallyConstant (FibrePower π p) ℤ) (a : A) :
    cechDLC π A p (smulConst φ a) = smulConst (cechDLC π ℤ p φ) a :=
  LocallyConstant.ext fun x ↦ by
    simp only [cechDLC_apply, smulConst_apply, cechD_apply, Finset.sum_smul, smul_assoc]

/-- The terms of the augmented complex of `ℤ`-valued locally constant functions:
`C(T, ℤ)` in degree `0` and `C(T'ₚ, ℤ)` in degree `p + 1`. -/
abbrev augTerm : ℕ → Type u
  | 0 => LocallyConstant T ℤ
  | n + 1 => LocallyConstant (FibrePower π n) ℤ

/-- The terms of the augmented complex are abelian groups. -/
instance augTerm.instAddCommGroup : (n : ℕ) → AddCommGroup (augTerm π n)
  | 0 => inferInstanceAs (AddCommGroup (LocallyConstant T ℤ))
  | n + 1 => inferInstanceAs (AddCommGroup (LocallyConstant (FibrePower π n) ℤ))

/-- The terms of the augmented complex are `ℤ`-modules. -/
instance augTerm.instModule : (n : ℕ) → Module ℤ (augTerm π n)
  | 0 => inferInstanceAs (Module ℤ (LocallyConstant T ℤ))
  | n + 1 => inferInstanceAs (Module ℤ (LocallyConstant (FibrePower π n) ℤ))

/-- The terms of the augmented complex are projective `ℤ`-modules: by Nöbeling's theorem they
are free. -/
instance augTerm.instProjective : (n : ℕ) → Module.Projective ℤ (augTerm π n)
  | 0 => by
    have : Module.Free ℤ (LocallyConstant (Profinite.of T) ℤ) :=
      LocallyConstant.freeOfProfinite _
    exact Module.Projective.of_free (P := LocallyConstant T ℤ)
  | n + 1 => by
    have : Module.Free ℤ (LocallyConstant (Profinite.of (FibrePower π n)) ℤ) :=
      LocallyConstant.freeOfProfinite _
    exact Module.Projective.of_free (P := LocallyConstant (FibrePower π n) ℤ)

/-- The differentials of the augmented complex. -/
def augD : (n : ℕ) → augTerm π n →ₗ[ℤ] augTerm π (n + 1)
  | 0 => (LocallyConstant.comapAddMonoidHom
      (⟨basePt π, continuous_basePt π⟩ : C(FibrePower π 0, T))).toIntLinearMap
  | n + 1 => (cechDLC π ℤ n).toIntLinearMap

omit [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T] in
/-- The augmentation `augD π 0` pulls a function on `T` back along the base point map. -/
lemma augD_zero_apply (x : LocallyConstant T ℤ) (w : FibrePower π 0) :
    (augD π 0 x : LocallyConstant (FibrePower π 0) ℤ) w = x (basePt π w) := rfl

omit [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T'] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T] in
/-- In positive degrees the differential of the augmented complex is the Čech differential. -/
lemma augD_succ_apply (n : ℕ) (x : LocallyConstant (FibrePower π n) ℤ)
    (w : FibrePower π (n + 1)) :
    (augD π (n + 1) x : LocallyConstant (FibrePower π (n + 1)) ℤ) w = cechD π n x w := rfl

variable {π} in
/-- **The augmented complex of `ℤ`-valued locally constant functions is contractible.** -/
theorem exists_augContraction (hπ : Function.Surjective π) :
    ∃ s : ∀ n, augTerm π (n + 1) →ₗ[ℤ] augTerm π n,
      (∀ x, s 0 (augD π 0 x) = x) ∧
        ∀ n x, augD π n (s n x) + s (n + 1) (augD π (n + 1) x) = x := by
  refine Module.exists_contraction_of_isDedekindDomain (augD π) ?_ ?_ ?_
  · intro n x
    cases n with
    | zero =>
      change LocallyConstant T ℤ at x
      ext y
      show cechD π 0 (fun w ↦ x (basePt π w)) y = 0
      rw [cechD_apply, Fin.sum_univ_two]
      simp [basePt_face]
    | succ n =>
      change LocallyConstant (FibrePower π n) ℤ at x
      ext y
      rw [augD_succ_apply]
      exact congrFun (cechD_cechD π n x) y
  · intro x x' h
    change LocallyConstant T ℤ at x x'
    have h' : ((x - x' : LocallyConstant T ℤ) : T → ℤ) ∘ basePt π (p := 0) = 0 := by
      funext w
      have : x (basePt π w) = x' (basePt π w) :=
        congrArg (fun f : LocallyConstant (FibrePower π 0) ℤ ↦ f w) h
      simp only [Function.comp_apply, Pi.zero_apply, LocallyConstant.coe_sub, Pi.sub_apply,
        this, sub_self]
    exact sub_eq_zero.1 (LocallyConstant.coe_injective
      (eq_zero_of_comp_basePt_eq_zero π hπ _ h'))
  · intro n x hx
    cases n with
    | zero =>
      change LocallyConstant (FibrePower π 0) ℤ at x
      have hx' : cechD π 0 (x : FibrePower π 0 → ℤ) = 0 := funext fun w ↦
        congrArg (fun f : LocallyConstant (FibrePower π 1) ℤ ↦ f w) hx
      obtain ⟨b, hb, hbc⟩ := exists_isLocallyConstant_eq_comp_basePt π hπ
        (x : FibrePower π 0 → ℤ) x.isLocallyConstant hx'
      exact ⟨(⟨b, hb⟩ : LocallyConstant T ℤ),
        LocallyConstant.ext fun w ↦ (congrFun hbc w).symm⟩
    | succ n =>
      change LocallyConstant (FibrePower π (n + 1)) ℤ at x
      have hx' : cechD π (n + 1) (x : FibrePower π (n + 1) → ℤ) = 0 := funext fun w ↦
        congrArg (fun f : LocallyConstant (FibrePower π (n + 2)) ℤ ↦ f w) hx
      obtain ⟨b, hb, hbc⟩ := exists_isLocallyConstant_cechD_eq π hπ
        (x : FibrePower π (n + 1) → ℤ) x.isLocallyConstant hx'
      exact ⟨(⟨b, hb⟩ : LocallyConstant (FibrePower π n) ℤ),
        LocallyConstant.ext fun w ↦ congrFun hbc w⟩

end Contraction

section ContinuousExactness

/-! ### Complete nonarchimedean coefficients -/

/-- A topological abelian group is *complete with respect to its open subgroups* if every
compatible system of residues modulo its open subgroups is the system of residues of a single
element. Together with `NonarchimedeanAddGroup` and `T2Space` this says that the group is the
inverse limit of its discrete quotients by open subgroups. -/
def IsProDiscrete (Y : Type*) [AddCommGroup Y] [TopologicalSpace Y] : Prop :=
  ∀ f : OpenAddSubgroup Y → Y, (∀ N N' : OpenAddSubgroup Y, N ≤ N' → f N - f N' ∈ N') →
    ∃ y, ∀ N, y - f N ∈ N

variable {X Y : Type*} [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y]

/-- Reduction modulo an open subgroup turns a continuous function into a locally constant
one. -/
def reduceLC (N : OpenAddSubgroup Y) (c : C(X, Y)) :
    LocallyConstant X (Y ⧸ (N : AddSubgroup Y)) :=
  ⟨QuotientAddGroup.mk ∘ c, by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    have : (QuotientAddGroup.mk ∘ c : X → Y ⧸ (N : AddSubgroup Y)) ⁻¹' {(y : Y ⧸ _)} =
        (fun x ↦ -y + c x) ⁻¹' (N : Set Y) := by
      ext x
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
      rfl
    rw [this]
    exact N.isOpen.preimage (continuous_const.add c.continuous)⟩

/-- The value of `reduceLC N c` at `x` is the class of `c x` modulo `N`. -/
@[simp]
lemma reduceLC_apply (N : OpenAddSubgroup Y) (c : C(X, Y)) (x : X) :
    reduceLC N c x = (c x : Y ⧸ (N : AddSubgroup Y)) := rfl

end ContinuousExactness

section MainExactness

universe u

variable {T' T : Type u} [TopologicalSpace T'] [TopologicalSpace T]
  [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T']
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
  {π : C(T', T)} (hπ : Function.Surjective π)
  {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [NonarchimedeanAddGroup Y] [T2Space Y]

omit [IsTopologicalAddGroup Y] in
include hπ in
/-- **Exactness in positive degrees with complete nonarchimedean coefficients.** Let
`π : T' → T` be a continuous surjection of profinite spaces and let `Y` be a Hausdorff
nonarchimedean topological abelian group which is complete with respect to its open subgroups.
Then every continuous `(q+1)`-cocycle on the Čech nerve of `π` with values in `Y` is the
coboundary of a continuous `q`-cochain. -/
theorem exists_continuous_cechD_eq (hY : IsProDiscrete Y) {q : ℕ}
    (c : FibrePower π (q + 1) → Y) (hc : Continuous c) (hdc : cechD π (q + 1) c = 0) :
    ∃ b : FibrePower π q → Y, Continuous b ∧ cechD π q b = c := by
  classical
  obtain ⟨s, -, hs⟩ := exists_augContraction hπ
  let s₀ : LocallyConstant (FibrePower π (q + 1)) ℤ →+ LocallyConstant (FibrePower π q) ℤ :=
    (s (q + 1)).toAddMonoidHom
  let s₁ : LocallyConstant (FibrePower π (q + 2)) ℤ →+
      LocallyConstant (FibrePower π (q + 1)) ℤ :=
    (s (q + 2)).toAddMonoidHom
  have hs' : ∀ φ, cechDLC π ℤ q (s₀ φ) + s₁ (cechDLC π ℤ (q + 1) φ) = φ := hs (q + 1)
  let cc : C(FibrePower π (q + 1), Y) := ⟨c, hc⟩
  let bN : ∀ N : OpenAddSubgroup Y,
      LocallyConstant (FibrePower π q) (Y ⧸ (N : AddSubgroup Y)) := fun N ↦
    extendScalars _ s₀ (reduceLC N cc)
  have hbN : ∀ N : OpenAddSubgroup Y, cechDLC π _ q (bN N) = reduceLC N cc := by
    intro N
    have h := homotopy_extendScalars (d₀ := cechDLC π ℤ q) (d₁ := cechDLC π ℤ (q + 1))
      (dA₀ := cechDLC π _ q) (dA₁ := cechDLC π _ (q + 1)) (cechDLC_smulConst π _ q)
      (cechDLC_smulConst π _ (q + 1)) s₀ s₁ hs' (reduceLC N cc)
    have h0 : cechDLC π _ (q + 1) (reduceLC N cc) = 0 := by
      ext x
      have := congrFun (cechD_comp π (QuotientAddGroup.mk' (N : AddSubgroup Y)) (q + 1) c) x
      rw [cechDLC_apply]
      refine this.trans ?_
      simp [hdc]
    rwa [h0, map_zero, add_zero] at h
  have hcompat : ∀ N N' : OpenAddSubgroup Y, (hle : N ≤ N') →
      (bN N).map (QuotientAddGroup.map (N : AddSubgroup Y) (N' : AddSubgroup Y)
        (AddMonoidHom.id Y) hle) = bN N' := by
    intro N N' hle
    show (extendScalars _ s₀ (reduceLC N cc)).map
      (QuotientAddGroup.map (N : AddSubgroup Y) (N' : AddSubgroup Y) (AddMonoidHom.id Y) hle) = _
    rw [map_extendScalars]
    rfl
  have hfam : ∀ w, ∃ y : Y, ∀ N : OpenAddSubgroup Y, (y : Y ⧸ (N : AddSubgroup Y)) = bN N w := by
    intro w
    let f : OpenAddSubgroup Y → Y := fun N ↦ Quotient.out (bN N w)
    have hf : ∀ N : OpenAddSubgroup Y, (f N : Y ⧸ (N : AddSubgroup Y)) = bN N w :=
      fun N ↦ Quotient.out_eq _
    have hfc : ∀ N N' : OpenAddSubgroup Y, N ≤ N' → f N - f N' ∈ N' := by
      intro N N' hle
      refine QuotientAddGroup.eq_iff_sub_mem.1 ?_
      rw [hf N', ← hcompat N N' hle]
      show _ = QuotientAddGroup.map _ _ (AddMonoidHom.id Y) hle (bN N w)
      rw [← hf N]
      rfl
    obtain ⟨y, hy⟩ := hY f hfc
    exact ⟨y, fun N ↦ (hf N).symm ▸ QuotientAddGroup.eq_iff_sub_mem.2 (hy N)⟩
  choose b hb using hfam
  have hbsub : ∀ w w' (N : OpenAddSubgroup Y), bN N w' = bN N w → b w' - b w ∈ N := by
    intro w w' N h
    exact QuotientAddGroup.eq_iff_sub_mem.1 ((hb w' N).trans (h.trans (hb w N).symm))
  refine ⟨b, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w U hU
    have h0 : (fun y ↦ y + b w) ⁻¹' U ∈ 𝓝 (0 : Y) :=
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨N, hN⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    have hV : {w' | bN N w' = bN N w} ∈ 𝓝 w :=
      ((bN N).isLocallyConstant.isOpen_fiber (bN N w)).mem_nhds rfl
    refine Filter.mem_map.2 (Filter.mem_of_superset hV fun w' hw' ↦ ?_)
    simpa using hN (hbsub w w' N hw')
  · funext x
    have hall : ∀ N : OpenAddSubgroup Y, cechD π q b x - c x ∈ N := by
      intro N
      have h2 : ⇑(QuotientAddGroup.mk' (N : AddSubgroup Y)) ∘ b = ⇑(bN N) :=
        funext fun w ↦ hb w N
      have h3 := congrFun (cechD_comp π (QuotientAddGroup.mk' (N : AddSubgroup Y)) q b) x
      have h4 : cechD π q (bN N) x = (c x : Y ⧸ (N : AddSubgroup Y)) :=
        congrArg (fun f : LocallyConstant (FibrePower π (q + 1)) _ ↦ f x) (hbN N)
      rw [h2, h4] at h3
      exact QuotientAddGroup.eq_iff_sub_mem.1 h3.symm
    by_contra hne
    have hne' : cechD π q b x - c x ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨N, hN⟩ := NonarchimedeanAddGroup.is_nonarchimedean
      ({cechD π q b x - c x}ᶜ : Set Y)
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa [eq_comm] using hne'))
    exact hN (hall N) rfl

end MainExactness

section ContinuousCosimplicial

/-! ### The cosimplicial group of continuous functions on the Čech nerve -/

universe u v w

variable {T' T : Type u} [TopologicalSpace T'] [TopologicalSpace T] (π : C(T', T))
  (Y : Type v) [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- The structure maps of the Čech nerve are continuous. -/
lemma continuous_nerveMap {m n : SimplexCategory} (θ : m ⟶ n) :
    Continuous (nerveMap π θ) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun a ↦ (continuous_apply _).comp continuous_subtype_val

/-- The cosimplicial abelian group of continuous `Y`-valued functions on the Čech nerve of `π`,
lifted to the universe `max u v w`. -/
def contCosimplicial : CosimplicialObject AddCommGrpCat.{max u v w} where
  obj n := AddCommGrpCat.of (ULift.{w} C(FibrePower π n.len, Y))
  map θ := AddCommGrpCat.ofHom
    { toFun c := ⟨c.down.comp ⟨nerveMap π θ, continuous_nerveMap π θ⟩⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The differential of the alternating coface complex of `contCosimplicial π Y` is the Čech
differential on underlying functions. -/
lemma objD_contCosimplicial_apply (p : ℕ)
    (c : (contCosimplicial.{u, v, w} π Y).obj (SimplexCategory.mk p))
    (x : FibrePower π (p + 1)) :
    ((AlgebraicTopology.AlternatingCofaceMapComplex.objD (contCosimplicial.{u, v, w} π Y) p).hom
      c).down x = cechD π p c.down x := by
  have e : ∀ s : Finset (Fin (p + 2)),
      ((∑ i ∈ s, (-1 : ℤ) ^ (i : ℕ) • (contCosimplicial.{u, v, w} π Y).δ i).hom c).down x =
        ∑ i ∈ s, (-1 : ℤ) ^ (i : ℕ) • c.down (face π i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, AddCommGrpCat.hom_add]
      exact congrArg₂ (· + ·) rfl ih
  rw [cechD_apply]
  exact e Finset.univ

variable [CompactSpace T'] [T2Space T'] [TotallyDisconnectedSpace T']
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
  [NonarchimedeanAddGroup Y] [T2Space Y]

/-- **The Čech complex of continuous functions is exact in positive degrees.** -/
theorem isZero_homology_contCosimplicial (hπ : Function.Surjective π) (hY : IsProDiscrete Y)
    (p : ℕ) (hp : 0 < p) :
    Limits.IsZero (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
      (contCosimplicial.{u, v, w} π Y)).homology p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  have hd : ∀ n, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
      (contCosimplicial.{u, v, w} π Y)).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (contCosimplicial.{u, v, w} π Y) n :=
    fun n ↦ CochainComplex.of_d
      (fun m ↦ (contCosimplicial.{u, v, w} π Y).obj (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (contCosimplicial.{u, v, w} π Y)) n
  intro c hc
  change ((((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
      (contCosimplicial.{u, v, w} π Y)).d (q + 1) (q + 1 + 1)).hom c) = 0 at hc
  rw [hd] at hc
  have hc' : cechD π (q + 1) c.down = 0 := by
    funext x
    exact (objD_contCosimplicial_apply.{u, v, w} π Y (q + 1) c x).symm.trans
      (congrArg (fun z : (contCosimplicial.{u, v, w} π Y).obj (SimplexCategory.mk (q + 1 + 1)) ↦
        z.down x) hc)
  obtain ⟨b, hb, hbc⟩ := exists_continuous_cechD_eq hπ hY c.down c.down.continuous hc'
  refine ⟨⟨⟨b, hb⟩⟩, ?_⟩
  show (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
      (contCosimplicial.{u, v, w} π Y)).d q (q + 1)).hom ⟨⟨b, hb⟩⟩ = c
  rw [hd]
  apply ULift.ext
  ext x
  exact (objD_contCosimplicial_apply.{u, v, w} π Y q ⟨⟨b, hb⟩⟩ x).trans (congrFun hbc x)

end ContinuousCosimplicial

end Stacks.ProfiniteCech
