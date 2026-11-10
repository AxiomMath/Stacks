module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationWedge

/-!
# Changing the equations by a matrix multiplies the equation wedge by its determinant

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c` be functions on an open `V` of `X`
and let `g_j = ∑_l a_{jl} f_l` be a second family, given by a matrix `a` of functions on `V`.
This file proves

`ω ∧ d g₁ ∧ ⋯ ∧ d g_c = det(a) (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) + ∑_l f_l η_l`

for an arbitrary local relative `p`-form `ω`, with the `η_l` relative `(p + c)`-forms. This is
the congruence of the two equation wedges *modulo the equations* that the proof of
[Stacks, Tag 0G86] uses to compare the Gysin maps of two families of equations over an open on
which both cut out the closed subscheme; it is
`Stacks.Gysin.ChartComparison.wedge_det` in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Globalisation.lean`, and
`AlgebraicGeometry.Scheme.Hom.wedge_det_self` below is the statement in the shape that field
asks for.

The determinant appears for the usual reason: by the Leibniz rule `d g_j = ∑_l a_{jl} d f_l`
modulo the `f_l`, and a wedge of `c` linear combinations of `c` degree-one forms is the
determinant of the coefficient matrix times the wedge of those forms, because the wedge is
alternating in its degree-one arguments.

## Main definitions

* `Stacks.Wedge.smulSpan`: the submodule of the elements `∑ l, f l • η l` for a finite family
  `f` of scalars — the elements that vanish modulo the ideal the family generates.
* `AlgebraicGeometry.Scheme.Hom.wedgeGen`, `AlgebraicGeometry.Scheme.Hom.wedgeGenMulti` and
  `AlgebraicGeometry.Scheme.Hom.wedgeGenAlternating`: the ordered wedge
  `ι(m₁) ∧ ⋯ ∧ ι(m_c)` of the images of `c` local sections of the sheaf of relative
  differentials under the degree-one generator, as a function, as a multilinear map, and as an
  alternating map.

## Main results

* `Stacks.Wedge.map_matrix_row_smul`: **the alternating expansion of a change of coefficients.**
  For an alternating map `Λ` and a square matrix `A`, `Λ (fun i => ∑ j, A i j • v j)` is
  `det A • Λ v`.
* `SheafOfModules.GradedAlgebra.prodDegOne_mul_generator_eq_zero` and
  `SheafOfModules.GradedAlgebra.prodDegOne_generator_eq_zero_of_eq`: **a wedge of degree-one
  generators with a repeated factor vanishes**, in the two shapes the alternating map needs.
* `AlgebraicGeometry.Scheme.Hom.wedgeGen_matrix`: the determinant expansion for the wedge of
  relative differentials.
* `AlgebraicGeometry.Scheme.Hom.wedge_det` and
  `AlgebraicGeometry.Scheme.Hom.wedge_det_self`: **the determinant relation for the Gysin wedge
  factor**, the second in the shape `Stacks.Gysin.ChartComparison.wedge_det` asks for.

## Implementation notes

**No graded commutativity is used.** The only input from the exterior algebra is that the
degree-one generator has square zero
(`SheafOfModules.GradedAlgebra.SquareZero`): two generators then anticommute, because the
generator of a sum squares to zero as well, and that is all the alternating property needs. In
particular nothing here imports
`StacksFrontier/AlgebraicGeometry/DeRham/CupProduct/GradedCommutativity.lean`, and the statements
are about `SheafOfModules.GradedAlgebra.prodDegOne` with integer degrees rather than about
`AlgebraicGeometry.SheafOfModules.formProduct` with its degree-normalized natural-number
degrees, so no `reindexForm` transport appears.

**The multilinear map is built by currying, not by hand.** `prodDegOne` recurses on the right,
so `MultilinearMap.uncurryRight` assembles the multilinear map in `c + 1` arguments out of the
one in `c` arguments composed with the bilinear "wedge one more generator" map; the alternative
is a `Function.update` computation in each of the two multilinearity laws.

**Two spellings of the sections.** `SheafOfModules.GradedAlgebra.prodDegOne` produces a term of
type `(A.piece n).val.obj (op V)`, whereas the `Γ(ℱ, V)` notation of
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` — the spelling the module structure over
`Γ(X, V)` is registered at, and the spelling the consumers in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Globalisation.lean` use — unfolds to
`(Scheme.Modules.presheaf ℱ).obj (op V)`. The two are definitionally equal but instance search
sees only the second, so every statement below is phrased in the `Γ(ℱ, V)` spelling and the
wrappers `AlgebraicGeometry.Scheme.Hom.exteriorGenLin`,
`AlgebraicGeometry.Scheme.Hom.relDiffHom`, `AlgebraicGeometry.Scheme.Hom.wedgeGen` and
`AlgebraicGeometry.Scheme.Hom.formMulLeft` exist to put it there; a statement mixing the two is
type-correct only at default transparency, which is enough for `exact` but not for `rw`. Each
wrapper is the underlying term, so the final statement is definitionally the field's.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing

namespace Stacks.Wedge

/-! ### Vanishing modulo a finite family of scalars -/

section SmulSpan

variable {R : Type*} [CommRing R] {c : ℕ}

/-- The submodule of the elements of the shape `∑ l, f l • η l` for a finite family `f` of
scalars: the elements that vanish modulo the ideal the family generates. -/
def smulSpan (R : Type*) [CommRing R] (W : Type*) [AddCommGroup W] [Module R W] {c : ℕ}
    (f : Fin c → R) : Submodule R W :=
  LinearMap.range (∑ l, (LinearMap.lsmul R W (f l)).comp (LinearMap.proj l))

variable (R) in
/-- An element lies in `Stacks.Wedge.smulSpan R W f` if and only if it is of the form
`∑ l, f l • η l` for some family `η`. -/
theorem mem_smulSpan_iff (W : Type*) [AddCommGroup W] [Module R W] (f : Fin c → R) (x : W) :
    x ∈ smulSpan R W f ↔ ∃ η : Fin c → W, x = ∑ l, f l • η l := by
  simp only [smulSpan, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.lsmul_apply, eq_comm]

variable {W P : Type*} [AddCommGroup W] [Module R W] [AddCommGroup P] [Module R P]

/-- Every element `∑ l, f l • η l` lies in `Stacks.Wedge.smulSpan R W f`. -/
theorem sum_smul_mem_smulSpan (f : Fin c → R) (η : Fin c → W) :
    ∑ l, f l • η l ∈ smulSpan R W f :=
  (mem_smulSpan_iff R W f _).mpr ⟨η, rfl⟩

/-- A linear map carries the elements vanishing modulo a family of scalars to elements
vanishing modulo that family. -/
theorem map_mem_smulSpan (φ : W →ₗ[R] P) (f : Fin c → R) {x : W} (hx : x ∈ smulSpan R W f) :
    φ x ∈ smulSpan R P f := by
  obtain ⟨η, hη⟩ := (mem_smulSpan_iff R W f x).mp hx
  refine (mem_smulSpan_iff R P f _).mpr ⟨fun l => φ (η l), ?_⟩
  rw [hη, map_sum]
  exact Finset.sum_congr rfl fun l _ => map_smul φ (f l) (η l)

variable {ι : Type*}

/-- A multilinear map vanishes modulo a family of scalars as soon as one of its arguments
does. -/
theorem map_mem_smulSpan_of_coord (Λ : MultilinearMap R (fun _ : ι => W) P) (f : Fin c → R)
    (m : ι → W) (j : ι) (hj : m j ∈ smulSpan R W f) : Λ m ∈ smulSpan R P f := by
  classical
  obtain ⟨η, hη⟩ := (mem_smulSpan_iff R W f (m j)).mp hj
  have hm : Function.update m j (∑ l, f l • η l) = m := by
    rw [← hη, Function.update_eq_self]
  rw [← hm, Λ.map_update_sum Finset.univ j (fun l => f l • η l) m]
  refine (mem_smulSpan_iff R P f _).mpr ⟨fun l => Λ (Function.update m j (η l)), ?_⟩
  exact Finset.sum_congr rfl fun l _ => Λ.map_update_smul m j (f l) (η l)

/-- **Perturbing every argument of a multilinear map by something vanishing modulo a family of
scalars perturbs the value by something vanishing modulo that family.** -/
theorem map_add_sub_mem_smulSpan [Finite ι] (Λ : MultilinearMap R (fun _ : ι => W) P)
    (f : Fin c → R) (u v : ι → W) (hv : ∀ j, v j ∈ smulSpan R W f) :
    Λ (u + v) - Λ u ∈ smulSpan R P f := by
  classical
  have := Fintype.ofFinite ι
  have hsplit : Λ (u + v)
      = (∑ s ∈ (Finset.univ : Finset (Finset ι)).erase Finset.univ, Λ (s.piecewise u v))
        + Λ u := by
    rw [Λ.map_add_univ u v,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ (Finset.univ : Finset ι)),
      Finset.piecewise_univ]
  rw [hsplit, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun s hs => ?_
  obtain ⟨j, hj⟩ : ∃ j, j ∉ s := by
    by_contra hcon
    exact (Finset.mem_erase.mp hs).1 (Finset.eq_univ_iff_forall.mpr (by simpa using hcon))
  refine map_mem_smulSpan_of_coord Λ f _ j ?_
  rw [Finset.piecewise_eq_of_notMem _ _ _ hj]
  exact hv j

end SmulSpan

/-! ### The alternating expansion of a change of coefficients -/

section Alternating

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- An alternating map vanishes on a family reindexed by a map that is not a bijection: such a
reindexing repeats an argument. -/
private theorem map_comp_eq_zero_of_not_bijective [Finite ι] (Λ : M [⋀^ι]→ₗ[R] N) (v : ι → M)
    {r : ι → ι} (hr : ¬Function.Bijective r) : Λ (v ∘ r) = 0 := by
  refine Λ.map_eq_zero_of_not_injective _ fun hinj => hr ?_
  exact Finite.injective_iff_bijective.mp fun a b hab =>
    hinj (show (v ∘ r) a = (v ∘ r) b from congrArg v hab)

/-- The determinant as a signed sum over the permutations, with the row index moving. -/
private theorem det_eq_sum_perm_row (A : Matrix ι ι R) :
    ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) • ∏ i, A i (σ i) = A.det := by
  rw [← Matrix.det_transpose A, Matrix.det_apply]
  exact Finset.sum_congr rfl fun σ _ => by rw [Units.smul_def]; rfl

/-- **The alternating expansion of a change of coefficients.** For an alternating map `Λ` in
`ι` arguments and a square matrix `A` indexed by `ι`, replacing each argument `v i` by the
linear combination `∑ j, A i j • v j` multiplies the value by `det A`. -/
theorem map_matrix_row_smul (Λ : M [⋀^ι]→ₗ[R] N) (A : Matrix ι ι R) (v : ι → M) :
    Λ (fun i => ∑ j, A i j • v j) = A.det • Λ v := by
  classical
  have hexp : Λ (fun i => ∑ j, A i j • v j)
      = ∑ r : ι → ι, (∏ i, A i (r i)) • Λ (v ∘ r) := by
    rw [show (Λ (fun i => ∑ j, A i j • v j)) =
      Λ.toMultilinearMap (fun i => ∑ j, A i j • v j) from rfl, MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun r _ =>
      Λ.toMultilinearMap.map_smul_univ (fun i => A i (r i)) (fun i => v (r i))
  have hshrink : ∑ r ∈ (Finset.univ.image fun σ : Equiv.Perm ι => (σ : ι → ι)),
        (∏ i, A i (r i)) • Λ (v ∘ r)
      = ∑ r : ι → ι, (∏ i, A i (r i)) • Λ (v ∘ r) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun r _ hr => ?_
    have hb : ¬Function.Bijective r := fun hb =>
      hr (Finset.mem_image.mpr ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩)
    rw [map_comp_eq_zero_of_not_bijective Λ v hb, smul_zero]
  have hsign : ∀ σ : Equiv.Perm ι, (∏ i, A i (σ i)) • Λ (v ∘ (σ : ι → ι))
      = ((Equiv.Perm.sign σ : ℤ) • ∏ i, A i (σ i)) • Λ v := by
    intro σ
    rw [Λ.map_perm, Units.smul_def, smul_assoc]
    exact smul_comm _ _ _
  rw [hexp, ← hshrink, Finset.sum_image fun a _ b _ h => Equiv.coe_fn_injective h,
    Finset.sum_congr rfl fun σ _ => hsign σ, ← Finset.sum_smul, det_eq_sum_perm_row]

end Alternating

/-! ### Products with a repeated square-zero factor -/

/-- A product of pairwise anticommuting square-zero elements of a ring, multiplied on the right
by one of its own factors, vanishes. -/
theorem listProd_mul_eq_zero {S : Type*} [Ring S] (n : ℕ) (x : Fin n → S)
    (hsq : ∀ i, x i * x i = 0) (hanti : ∀ i i', x i * x i' = -(x i' * x i)) (j : Fin n) :
    (List.ofFn x).prod * x j = 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
      rw [List.ofFn_succ', List.prod_concat]
      refine Fin.lastCases ?_ ?_ j
      · rw [mul_assoc, hsq, mul_zero]
      · intro j'
        rw [mul_assoc, hanti (Fin.last n) j'.castSucc, mul_neg, ← mul_assoc,
          ih (fun i => x i.castSucc) (fun i => hsq i.castSucc)
            (fun i i' => hanti i.castSucc i'.castSucc) j',
          zero_mul, neg_zero]

end Stacks.Wedge

namespace SheafOfModules.GradedAlgebra

/-! ### A wedge of degree-one generators with a repeated factor -/

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
  {M : SheafOfModules R}

/-- The ordered product of `n` degree-one local sections, read in the ring of all local
sections, is the product of the corresponding degree-one summands. -/
private theorem of_prodDegOne' (A : GradedAlgebra R) (U : Cᵒᵖ) (n : ℕ)
    (z : Fin n → (A.piece 1).val.obj U) :
    DirectSum.of (A.sectionsPiece U) (n : ℤ) (A.prodDegOne U n z) =
      (List.ofFn fun j => DirectSum.of (A.sectionsPiece U) 1 (z j)).prod := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.prod_nil]; rfl
  | succ n ih =>
      rw [List.ofFn_succ', List.prod_concat, ← ih (fun i => z i.castSucc)]
      exact (A.of_mul_of_eq U (n : ℤ) 1 _ (z (Fin.last n))).symm

/-- The degree-one summand of the image of a local section under a square-zero degree-one
generator squares to zero in the ring of all local sections. -/
private theorem of_generator_sq_eq_zero {A : GradedAlgebra R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) (x : M.val.obj U) :
    DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x) *
        DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x) = 0 := by
  rw [of_mul_of_eq]
  exact (congrArg (DirectSum.of (A.sectionsPiece U) (1 + 1)) (hι U x)).trans (map_zero _)

/-- The degree-one summands of the images of two local sections under a square-zero degree-one
generator anticommute in the ring of all local sections: the generator of their sum squares to
zero as well. -/
private theorem of_generator_anticomm {A : GradedAlgebra R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) (x y : M.val.obj U) :
    DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x) *
        DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U y) =
      -(DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U y) *
        DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x)) := by
  have hadd : DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U (x + y)) =
      DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x) +
        DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U y) := by
    rw [show ι.val.app U (x + y) = ι.val.app U x + ι.val.app U y from map_add _ _ _, map_add]
  have h := of_generator_sq_eq_zero hι U (x + y)
  rw [hadd, add_mul, mul_add, mul_add, of_generator_sq_eq_zero hι U x,
    of_generator_sq_eq_zero hι U y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **A wedge of degree-one generators, multiplied on the right by one of its own factors,
vanishes.** -/
theorem prodDegOne_mul_generator_eq_zero {A : GradedAlgebra R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) {n : ℕ} (g : Fin n → M.val.obj U) (j : Fin n) :
    (A.mul (n : ℤ) 1).app U (A.prodDegOne U n fun k => ι.val.app U (g k))
      (ι.val.app U (g j)) = 0 := by
  refine DirectSum.of_injective (β := A.sectionsPiece U) ((n : ℤ) + 1) ?_
  rw [map_zero, ← A.of_mul_of_eq U (n : ℤ) 1, of_prodDegOne' A U n]
  exact Stacks.Wedge.listProd_mul_eq_zero n _ (fun i => of_generator_sq_eq_zero hι U (g i))
    (fun i i' => of_generator_anticomm hι U (g i) (g i')) j

/-- **A wedge of degree-one generators with a repeated factor vanishes.** -/
theorem prodDegOne_generator_eq_zero_of_eq {A : GradedAlgebra R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) :
    ∀ (n : ℕ) (g : Fin n → M.val.obj U) (a b : Fin n), g a = g b → a ≠ b →
      A.prodDegOne U n (fun k => ι.val.app U (g k)) = 0 := by
  intro n
  induction n with
  | zero => exact fun _ a => a.elim0
  | succ n ih =>
      have key : ∀ (g : Fin (n + 1) → M.val.obj U) (k : Fin n),
          g (Fin.last n) = g k.castSucc →
            A.prodDegOne U (n + 1) (fun k => ι.val.app U (g k)) = 0 := by
        intro g k h
        rw [prodDegOne_succ]
        refine Eq.trans (congrArg (fun z => (A.mul (n : ℤ) 1).app U
          (A.prodDegOne U n fun k => ι.val.app U (g k.castSucc)) (ι.val.app U z)) h) ?_
        exact prodDegOne_mul_generator_eq_zero hι U (fun i => g i.castSucc) k
      intro g a b
      refine Fin.lastCases ?_ ?_ b
      · refine Fin.lastCases ?_ ?_ a
        · exact fun _ h => absurd rfl h
        · exact fun a' h _ => key g a' h.symm
      · intro b'
        refine Fin.lastCases ?_ ?_ a
        · exact fun h _ => key g b' h
        · intro a' h hne
          have hz : ((A.mul (n : ℤ) 1).app U) 0 = (0 : _ →+ _) := map_zero _
          rw [prodDegOne_succ, ih (fun i => g i.castSucc) a' b' h
            (fun hcc => hne (congrArg Fin.castSucc hcc)), hz]
          exact AddMonoidHom.zero_apply _

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-! ### The wedge of relative differentials as an alternating map -/

/-- The degree-one generator of the algebra of relative differential forms, on the sections over
an open, as a linear map over the sections of the structure sheaf. -/
def exteriorGenLin (π : X ⟶ S) (V : X.Opens) :
    Γ(relativeDifferentials π, V) →ₗ[Γ(X, V)] Γ(relativeDifferentialForms π 1, V) :=
  ConcreteCategory.hom
    ((Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.app (op V))

/-- `AlgebraicGeometry.Scheme.Hom.exteriorGenLin` is the degree-one exterior generator on
sections over `V`. -/
theorem exteriorGenLin_apply (π : X ⟶ S) (V : X.Opens) (m : Γ(relativeDifferentials π, V)) :
    exteriorGenLin π V m =
      (Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.app (op V) m :=
  rfl

/-- The universal relative derivation on the sections over an open, as an additive map to the
sections of the sheaf of relative differentials. -/
def relDiffHom (π : X ⟶ S) (V : X.Opens) : Γ(X, V) →+ Γ(relativeDifferentials π, V) :=
  (universalRelativeDerivation π).d

/-- The Leibniz rule for the universal relative derivation, on the sections over an open. -/
theorem relDiffHom_mul (π : X ⟶ S) (V : X.Opens) (a b : Γ(X, V)) :
    relDiffHom π V (a * b) = a • relDiffHom π V b + b • relDiffHom π V a :=
  (universalRelativeDerivation π).d_mul a b

/-- The exact one-form of a local function is the generator applied to its universal relative
differential. -/
theorem exactOneForm_eq_exteriorGenLin (π : X ⟶ S) (V : X.Opens) (b : Γ(X, V)) :
    exactOneForm π (op V) b = exteriorGenLin π V (relDiffHom π V b) :=
  rfl

/-- The ordered wedge of the images of `c` local sections of the sheaf of relative differentials
under the degree-one generator. -/
def wedgeGen (π : X ⟶ S) (V : X.Opens) (c : ℕ) (m : Fin c → Γ(relativeDifferentials π, V)) :
    Γ(relativeDifferentialForms π (c : ℤ), V) :=
  (relativeDifferentialFormsAlgebra π).prodDegOne (op V) c fun j => exteriorGenLin π V (m j)

/-- Wedging a relative `c`-form with the image of a local section of the sheaf of relative
differentials under the degree-one generator, as a bilinear map. -/
def wedgeGenStep (π : X ⟶ S) (V : X.Opens) (c : ℕ) :
    Γ(relativeDifferentialForms π (c : ℤ), V) →ₗ[Γ(X, V)]
      Γ(relativeDifferentials π, V) →ₗ[Γ(X, V)]
        Γ(relativeDifferentialForms π ((c : ℤ) + 1), V) :=
  LinearMap.mk₂ Γ(X, V)
    (fun x z => ((relativeDifferentialFormsAlgebra π).mul (c : ℤ) 1).app (op V) x
      (exteriorGenLin π V z))
    (fun x x' z =>
      ((relativeDifferentialFormsAlgebra π).mul (c : ℤ) 1).map_add_left (op V) x x' _)
    (fun r x z =>
      ((relativeDifferentialFormsAlgebra π).mul (c : ℤ) 1).map_smul_left (op V) r x _)
    (fun x z z' => by
      rw [map_add]
      exact map_add _ _ _)
    (fun r x z => by
      rw [map_smul]
      exact ((relativeDifferentialFormsAlgebra π).mul (c : ℤ) 1).map_smul_right (op V) r x _)

/-- The ordered wedge `AlgebraicGeometry.Scheme.Hom.wedgeGen`, as a multilinear map. -/
def wedgeGenMulti (π : X ⟶ S) (V : X.Opens) :
    (c : ℕ) → MultilinearMap Γ(X, V) (fun _ : Fin c => Γ(relativeDifferentials π, V))
      Γ(relativeDifferentialForms π (c : ℤ), V)
  | 0 => MultilinearMap.constOfIsEmpty Γ(X, V) _
      ((relativeDifferentialFormsAlgebra π).one.eval (op V))
  | c + 1 => ((wedgeGenStep π V c).compMultilinearMap (wedgeGenMulti π V c)).uncurryRight

/-- The multilinear map `AlgebraicGeometry.Scheme.Hom.wedgeGenMulti` evaluates to the ordered
wedge `AlgebraicGeometry.Scheme.Hom.wedgeGen`. -/
theorem wedgeGenMulti_apply (π : X ⟶ S) (V : X.Opens) :
    ∀ (c : ℕ) (m : Fin c → Γ(relativeDifferentials π, V)),
      wedgeGenMulti π V c m = wedgeGen π V c m
  | 0, _ => rfl
  | c + 1, m => by
      change ((wedgeGenStep π V c) (wedgeGenMulti π V c (Fin.init m))) (m (Fin.last c)) = _
      rw [wedgeGenMulti_apply π V c (Fin.init m)]
      rfl

/-- The ordered wedge `AlgebraicGeometry.Scheme.Hom.wedgeGen`, as an alternating map: a repeated
factor makes it vanish. -/
def wedgeGenAlternating (π : X ⟶ S) (V : X.Opens) (c : ℕ) :
    Γ(relativeDifferentials π, V) [⋀^Fin c]→ₗ[Γ(X, V)]
      Γ(relativeDifferentialForms π (c : ℤ), V) :=
  { wedgeGenMulti π V c with
    map_eq_zero_of_eq' := fun m a b h hab =>
      (wedgeGenMulti_apply π V c m).trans
        (SheafOfModules.GradedAlgebra.prodDegOne_generator_eq_zero_of_eq
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials π)).1
          (op V) c m a b h hab) }

/-- The alternating map `AlgebraicGeometry.Scheme.Hom.wedgeGenAlternating` evaluates to the
ordered wedge `AlgebraicGeometry.Scheme.Hom.wedgeGen`. -/
theorem wedgeGenAlternating_apply (π : X ⟶ S) (V : X.Opens) (c : ℕ)
    (m : Fin c → Γ(relativeDifferentials π, V)) :
    wedgeGenAlternating π V c m = wedgeGen π V c m :=
  wedgeGenMulti_apply π V c m

/-- **The alternating expansion of a wedge of degree-one forms.** -/
theorem wedgeGen_matrix (π : X ⟶ S) (V : X.Opens) {c : ℕ}
    (N : Matrix (Fin c) (Fin c) Γ(X, V)) (m : Fin c → Γ(relativeDifferentials π, V)) :
    wedgeGen π V c (fun j => ∑ l, N j l • m l) = N.det • wedgeGen π V c m := by
  have h := Stacks.Wedge.map_matrix_row_smul (wedgeGenAlternating π V c) N m
  rwa [wedgeGenAlternating_apply, wedgeGenAlternating_apply] at h

/-! ### The determinant relation for a change of equations -/

/-- Wedging a fixed relative `p`-form with a relative `q`-form, as a linear map. -/
def formMulLeft (π : X ⟶ S) (V : X.Opens) (p q : ℤ)
    (ω : Γ(relativeDifferentialForms π p, V)) :
    Γ(relativeDifferentialForms π q, V) →ₗ[Γ(X, V)]
      Γ(relativeDifferentialForms π (p + q), V) where
  toFun η := ((relativeDifferentialFormsAlgebra π).mul p q).app (op V) ω η
  map_add' := map_add (((relativeDifferentialFormsAlgebra π).mul p q).app (op V) ω)
  map_smul' r η :=
    ((relativeDifferentialFormsAlgebra π).mul p q).map_smul_right (op V) r ω η

/-- `AlgebraicGeometry.Scheme.Hom.formMulLeft π V p q ω` is the product with `ω` in the algebra
of relative differential forms. -/
theorem formMulLeft_apply (π : X ⟶ S) (V : X.Opens) (p q : ℤ)
    (ω : Γ(relativeDifferentialForms π p, V)) (η : Γ(relativeDifferentialForms π q, V)) :
    formMulLeft π V p q ω η = ((relativeDifferentialFormsAlgebra π).mul p q).app (op V) ω η :=
  rfl

/-- The Leibniz rule for a change of equations: the universal relative differential of
`∑ l, a_l f_l` is the corresponding combination of the `d f_l` plus a differential vanishing
modulo the `f_l`. -/
theorem relDiffHom_sum_mul (π : X ⟶ S) (V : X.Opens) {c : ℕ} (a f : Fin c → Γ(X, V)) :
    relDiffHom π V (∑ l, a l * f l)
      = (∑ l, a l • relDiffHom π V (f l)) + ∑ l, f l • relDiffHom π V (a l) := by
  rw [map_sum, show (fun l => relDiffHom π V (a l * f l))
      = fun l => a l • relDiffHom π V (f l) + f l • relDiffHom π V (a l) from
      funext fun l => relDiffHom_mul π V (a l) (f l)]
  exact Finset.sum_add_distrib

/-- **The determinant relation for the wedge of the differentials of a changed family of
equations**, modulo the equations themselves. -/
theorem wedgeGen_relDiff_sub_det_smul_mem (π : X ⟶ S) (V : X.Opens) {c : ℕ}
    (N : Matrix (Fin c) (Fin c) Γ(X, V)) (f g : Fin c → Γ(X, V))
    (hg : ∀ j, g j = ∑ l, N j l * f l) :
    wedgeGen π V c (fun j => relDiffHom π V (g j))
        - N.det • wedgeGen π V c (fun j => relDiffHom π V (f j))
      ∈ Stacks.Wedge.smulSpan Γ(X, V) Γ(relativeDifferentialForms π (c : ℤ), V) f := by
  have hvmem : ∀ j, (∑ l, f l • relDiffHom π V (N j l)) ∈
      Stacks.Wedge.smulSpan Γ(X, V) Γ(relativeDifferentials π, V) f := fun j =>
    Stacks.Wedge.sum_smul_mem_smulSpan f _
  have hstep := Stacks.Wedge.map_add_sub_mem_smulSpan (wedgeGenMulti π V c) f
    (fun j => ∑ l, N j l • relDiffHom π V (f l))
    (fun j => ∑ l, f l • relDiffHom π V (N j l)) hvmem
  rw [wedgeGenMulti_apply, wedgeGenMulti_apply] at hstep
  have hsum : wedgeGen π V c ((fun j => ∑ l, N j l • relDiffHom π V (f l))
        + fun j => ∑ l, f l • relDiffHom π V (N j l))
      = wedgeGen π V c fun j => relDiffHom π V (g j) :=
    congrArg (wedgeGen π V c) (funext fun j =>
      ((congrArg (relDiffHom π V) (hg j)).trans (relDiffHom_sum_mul π V (N j) f)).symm)
  rwa [hsum, wedgeGen_matrix π V N fun l => relDiffHom π V (f l)] at hstep

/-- **The determinant relation for the Gysin wedge factor.** For a change of equations
`g_j = ∑_l a_{jl} f_l` given by a matrix `N = (a_{jl})` of functions on `V`, wedging a relative
`p`-form `ω` with `d g₁ ∧ ⋯ ∧ d g_c` is `det N` times wedging it with `d f₁ ∧ ⋯ ∧ d f_c`, up to
a combination of the equations:

`ω ∧ d g₁ ∧ ⋯ ∧ d g_c = det N (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) + ∑_l f_l η_l`. -/
theorem wedge_det (π : X ⟶ S) (V : X.Opens) (p : ℤ) {c : ℕ}
    (N : Matrix (Fin c) (Fin c) Γ(X, V)) (f g : Fin c → Γ(X, V))
    (hg : ∀ j, g j = ∑ l, N j l * f l) (ω : Γ(relativeDifferentialForms π p, V)) :
    ∃ η : Fin c → Γ(relativeDifferentialForms π (p + (c : ℤ)), V),
      formMulLeft π V p (c : ℤ) ω (wedgeGen π V c fun j => relDiffHom π V (g j)) =
        N.det • formMulLeft π V p (c : ℤ) ω (wedgeGen π V c fun j => relDiffHom π V (f j))
          + ∑ l, f l • η l := by
  have hmem := Stacks.Wedge.map_mem_smulSpan (formMulLeft π V p (c : ℤ) ω) f
    (wedgeGen_relDiff_sub_det_smul_mem π V N f g hg)
  rw [map_sub, map_smul] at hmem
  obtain ⟨η, hη⟩ := (Stacks.Wedge.mem_smulSpan_iff Γ(X, V) _ f _).mp hmem
  exact ⟨η, by rw [← hη]; abel⟩

/-- Restriction along the trivial inclusion `V ≤ V` is the identity on sections. -/
theorem presheaf_map_le_refl (V : X.Opens) (b : Γ(X, V)) :
    X.presheaf.map (homOfLE (le_refl V)).op b = b := by
  rw [show (homOfLE (le_refl V) : V ⟶ V) = 𝟙 V from Subsingleton.elim _ _]
  simp

/-- **The determinant relation for the Gysin wedge factor, in the shape the chart comparison of
[Stacks, Tag 0G86] asks for.** This is literally the field
`Stacks.Gysin.ChartComparison.wedge_det` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Globalisation.lean` after unfolding
`Stacks.Gysin.gysinWedgeOn` and `Stacks.Gysin.equationsWedgeOn`, so it discharges that field by
`exact`. -/
theorem wedge_det_self (π : X ⟶ S) (V : X.Opens) (p : ℤ) {c : ℕ}
    (N : Matrix (Fin c) (Fin c) Γ(X, V)) (f g : Fin c → Γ(X, V))
    (hg : ∀ j, g j = ∑ l, N j l * f l) (ω : Γ(relativeDifferentialForms π p, V)) :
    ∃ η : Fin c → Γ(relativeDifferentialForms π (p + (c : ℤ)), V),
      formMulLeft π V p (c : ℤ) ω (wedgeGen π V c fun j =>
          relDiffHom π V (X.presheaf.map (homOfLE (le_refl V)).op (g j))) =
        N.det • formMulLeft π V p (c : ℤ) ω (wedgeGen π V c fun j =>
          relDiffHom π V (X.presheaf.map (homOfLE (le_refl V)).op (f j)))
          + ∑ l, f l • η l := by
  simpa only [presheaf_map_le_refl] using wedge_det π V p N f g hg ω

end AlgebraicGeometry.Scheme.Hom

end
