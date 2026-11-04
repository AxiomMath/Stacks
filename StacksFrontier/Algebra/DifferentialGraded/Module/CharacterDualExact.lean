module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.Module.CharacterModule.Duality
public import StacksCore.Tactic.StacksAttribute

/-! # Exactness of the graded `ℚ/ℤ`-dual

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. The graded dual
`M ↦ M^∨` of `StacksFrontier/Algebra/DifferentialGraded/Module/CharacterDual.lean` sends a left
differential graded `A`-module to a right one, contravariantly. This file proves that it is
*exact*: a short exact sequence `0 → K → L → M → 0` of left differential graded modules dualizes
to a short exact sequence `0 → M^∨ → L^∨ → K^∨ → 0` of right differential graded modules.

The two outer ends of the dual sequence are already settled in `CharacterDual.lean`:
`DifferentialGraded.LeftModule.dualMap_injective` makes `M^∨ → L^∨` injective, and
`DifferentialGraded.LeftModule.dualMap_surjective` makes `L^∨ → K^∨` surjective. What is proved
here is exactness in the middle, `range (dualMap p) = ker (dualMap i)`.

## Main results

* `DifferentialGraded.LeftModule.range_gradedMap_eq_ker`: an exact pair of left differential
  graded modules is exact in each degree separately.
* `DifferentialGraded.LeftModule.exists_dualPiece_preimage`: a homogeneous character of `L`
  killing the image of `i` is the pullback along `p` of a homogeneous character of `M`.
* `DifferentialGraded.LeftModule.dualMap_exact`: the graded dual of an exact sequence is exact.

## Implementation notes

The engine is the ungraded statement `CharacterModule.dual_exact`, which is applied once in each
degree `-n` to the restricted maps `DifferentialGraded.LeftModule.Hom.gradedMap`. Three
reductions carry it to the graded dual: exactness holds degreewise because the decomposition of a
preimage can be truncated to a single degree (`range_gradedMap_eq_ker`); a homogeneous character
is recovered from its restriction to the single graded piece it is supported on, by
`dualPieceRestrict` and `extendChar`; and a general element of `ker (dualMap i)` is the finite sum
of its homogeneous components, each of which is again killed by `dualMap i` because `dualMap i`
preserves degrees.

Both of the degreewise arguments are run through `DirectSum.gradedProjection`, whose naturality
in a degree-preserving linear map is `gradedProjection_comm` below; that lemma mentions no
differential graded structure and belongs with `DirectSum.gradedProjection` itself.

Following `CharacterDual.lean`, every statement here binds its character variables at the honest
type `CharacterModule L.M` rather than at `(dual L).M`, and passes between the two only through
the readers `dualChar` and `dualOf`. The carrier of `dual L` is equal to its underlying subtype
only under default-transparency unfolding, so a membership proof for `⨆ n, dualPiece M n` does
not typecheck against `dualCarrier M` without the explicit bridge `mem_dualCarrier`, and
submodule-level rewriting at the bundled type does not fire at all.

## References

* [Stacks Project, Tag 0FQD](https://stacks.math.columbia.edu/tag/0FQD)
* [Stacks Project, Tag 09K3](https://stacks.math.columbia.edu/tag/09K3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

attribute [local instance] charModule charIsScalarTower

/-- A degree-preserving linear map commutes with the projections onto the graded pieces: both
sides agree on a homogeneous element, where each is either the map itself or zero. -/
theorem gradedProjection_comm {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (𝒩 : ℤ → Submodule R N) [DirectSum.Decomposition 𝒩] (f : M →ₗ[R] N)
    (hf : ∀ (n : ℤ) (x : M), x ∈ ℳ n → f x ∈ 𝒩 n) (d : ℤ) (x : M) :
    f (DirectSum.gradedProjection ℳ d x) = DirectSum.gradedProjection 𝒩 d (f x) := by
  refine LinearMap.congr_fun (DirectSum.linearMap_ext_of_mem ℳ
    (f := f ∘ₗ DirectSum.gradedProjection ℳ d)
    (g := DirectSum.gradedProjection 𝒩 d ∘ₗ f) ?_) x
  intro n y hy
  simp only [LinearMap.comp_apply]
  by_cases hn : n = d
  · subst hn
    rw [DirectSum.gradedProjection_of_mem_same ℳ hy,
      DirectSum.gradedProjection_of_mem_same 𝒩 (hf n y hy)]
  · rw [DirectSum.gradedProjection_of_mem_ne ℳ hy hn, map_zero,
      DirectSum.gradedProjection_of_mem_ne 𝒩 (hf n y hy) hn]

/-- The composite of an exact pair of homomorphisms vanishes. -/
theorem comp_eq_zero_of_range_eq_ker {K L M : LeftModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hexact : LinearMap.range i.toFun = LinearMap.ker p.toFun) (z : K.M) :
    p.toFun (i.toFun z) = 0 :=
  LinearMap.mem_ker.mp (hexact ▸ LinearMap.mem_range_self i.toFun z)

/-- An exact pair of left differential graded modules is exact in each degree separately.

The inclusion `range ⊆ ker` is immediate. For the converse, a homogeneous `x ∈ L^d` killed by `p`
is `i z` for some `z : K`, and `z` may be replaced by its degree-`d` component: projecting the
equation `i z = x` onto degree `d` fixes the right-hand side and passes through `i`. -/
theorem range_gradedMap_eq_ker {K L M : LeftModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hexact : LinearMap.range i.toFun = LinearMap.ker p.toFun) (d : ℤ) :
    LinearMap.range (Hom.gradedMap i d) = LinearMap.ker (Hom.gradedMap p d) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (comp_eq_zero_of_range_eq_ker i p hexact (x : K.M))
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hmem : (x : L.M) ∈ LinearMap.range i.toFun := by
      rw [hexact, LinearMap.mem_ker]
      exact congrArg Subtype.val hx
    obtain ⟨z, hz⟩ := hmem
    refine ⟨⟨DirectSum.gradedProjection K.grading d z,
      DirectSum.gradedProjection_mem K.grading d z⟩, Subtype.ext ?_⟩
    show i.toFun (DirectSum.gradedProjection K.grading d z) = (x : L.M)
    rw [gradedProjection_comm K.grading L.grading i.toFun i.map_grading d z, hz,
      DirectSum.gradedProjection_of_mem_same L.grading x.2]

/-- A homogeneous character of `L` of degree `n` that kills the image of `i` is the pullback
along `p` of a homogeneous character of `M` of degree `n`.

This is the ungraded `CharacterModule.dual_exact`, applied to the degree-`(-n)` part of the
sequence: the character restricts to one of `L^{-n}` killing the image of `K^{-n}`, hence is
pulled back from a character of `M^{-n}`, whose extension by zero is the character sought. -/
theorem exists_dualPiece_preimage {K L M : LeftModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hexact : LinearMap.range i.toFun = LinearMap.ker p.toFun) {n : ℤ}
    {l : CharacterModule L.M} (hl : l ∈ dualPiece L n)
    (hker : ∀ z : K.M, l (i.toFun z) = 0) :
    ∃ l' ∈ dualPiece M n, ∀ y : L.M, l' (p.toFun y) = l y := by
  have hex : Function.Exact (Hom.gradedMap i (-n)) (Hom.gradedMap p (-n)) :=
    LinearMap.exact_iff.mpr (range_gradedMap_eq_ker i p hexact (-n)).symm
  have hzero : CharacterModule.dual (Hom.gradedMap i (-n))
      (dualPieceRestrict L n ⟨l, hl⟩) = 0 := by
    apply CharacterModule.ext
    intro w
    show (dualPieceRestrict L n ⟨l, hl⟩) (Hom.gradedMap i (-n) w) = 0
    rw [dualPieceRestrict_apply]
    exact hker (w : K.M)
  obtain ⟨ν, hν⟩ := (CharacterModule.dual_exact _ _ hex _).mp hzero
  refine ⟨extendChar M n ν, extendChar_mem M n ν, fun y => ?_⟩
  refine induction_homogeneous (M := L) (p := fun w => extendChar M n ν (p.toFun w) = l w) y
    (fun m w hw => ?_) (by simp) (fun w w' hw hw' => by simp only [map_add, hw, hw'])
  by_cases hm : m = -n
  · have hpw : p.toFun w ∈ M.grading (-n) := hm ▸ p.map_grading m w hw
    have hw' : w ∈ L.grading (-n) := hm ▸ hw
    rw [extendChar_apply, show ((DirectSum.decompose M.grading (p.toFun w)) (-n))
        = ⟨p.toFun w, hpw⟩ from Subtype.ext (DirectSum.decompose_of_mem_same M.grading hpw)]
    calc ν ⟨p.toFun w, hpw⟩
        = ν ((Hom.gradedMap p (-n)) ⟨w, hw'⟩) := by rw [show
            (Hom.gradedMap p (-n)) ⟨w, hw'⟩ = (⟨p.toFun w, hpw⟩ : M.grading (-n)) from
            Subtype.ext rfl]
      _ = (CharacterModule.dual (Hom.gradedMap p (-n)) ν) ⟨w, hw'⟩ := rfl
      _ = (dualPieceRestrict L n ⟨l, hl⟩) ⟨w, hw'⟩ := by rw [hν]
      _ = l w := dualPieceRestrict_apply L n ⟨l, hl⟩ ⟨w, hw'⟩
  · rw [extendChar_apply, show ((DirectSum.decompose M.grading (p.toFun w)) (-n)) = 0 from
      Subtype.ext (DirectSum.decompose_of_mem_ne M.grading (p.map_grading m w hw) hm),
      map_zero, hl m hm w hw]

/-- A homogeneous element of `L^∨` killed by `dualMap i` lies in the image of `dualMap p`: read
it as a homogeneous character of `L` and apply `exists_dualPiece_preimage`. -/
theorem mem_range_dualMap_of_mem_grading {K L M : LeftModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hexact : LinearMap.range i.toFun = LinearMap.ker p.toFun) {n : ℤ} {y : (dual L).M}
    (hy : y ∈ (dual L).grading n) (h : (dualMap i).toFun y = 0) :
    y ∈ LinearMap.range (dualMap p).toFun := by
  have hker : ∀ z : K.M, dualChar y (i.toFun z) = 0 := by
    intro z
    rw [← dualChar_dualMap i y z, h]
    rfl
  obtain ⟨l', hl', hl'p⟩ :=
    exists_dualPiece_preimage i p hexact (mem_dual_grading.mp hy) hker
  refine ⟨dualOf l' (mem_dualCarrier.mpr (Submodule.mem_iSup_of_mem n hl')),
    dualChar_injective ?_⟩
  apply CharacterModule.ext
  intro w
  rw [dualChar_dualMap, dualChar_dualOf]
  exact hl'p w

/-- **The graded dual of an exact sequence is exact.** If `i : K ⟶ L` and `p : L ⟶ M` are
homomorphisms of left differential graded `A`-modules with `range i = ker p`, then the dualized
pair `dualMap p : M^∨ ⟶ L^∨` and `dualMap i : L^∨ ⟶ K^∨` of right differential graded
`A`-modules again satisfies `range (dualMap p) = ker (dualMap i)`.

Together with `dualMap_injective` and `dualMap_surjective` this says that `M ↦ M^∨` carries a
short exact sequence of left differential graded modules to a short exact sequence of right
ones.

The inclusion `range ⊆ ker` is formal: a character pulled back twice is evaluated at
`p (i z) = 0`. For the converse, an element of `ker (dualMap i)` is the sum of its homogeneous
components, which `dualMap i` kills separately because it preserves degrees, and each of which
is handled by `mem_range_dualMap_of_mem_grading`.

Surjectivity of `p` is not needed for this inclusion — it is what makes `dualMap p` *injective*
(`dualMap_injective`) — and is carried here only so that the lemma is stated at the shape of a
short exact sequence. -/
theorem dualMap_exact {K L M : LeftModule A} (i : K ⟶ L) (p : L ⟶ M)
    (_hp : Function.Surjective p.toFun)
    (hexact : LinearMap.range i.toFun = LinearMap.ker p.toFun) :
    LinearMap.range (dualMap p).toFun = LinearMap.ker (dualMap i).toFun := by
  classical
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    refine dualChar_injective ?_
    apply CharacterModule.ext
    intro z
    rw [dualChar_dualMap, dualChar_dualMap,
      comp_eq_zero_of_range_eq_ker i p hexact z, map_zero]
    rfl
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [← DirectSum.sum_support_decompose (dual L).grading y]
    refine Submodule.sum_mem _ (fun n _ => ?_)
    refine mem_range_dualMap_of_mem_grading i p hexact
      (DirectSum.decompose (dual L).grading y n).2 ?_
    show (dualMap i).toFun (DirectSum.gradedProjection (dual L).grading n y) = 0
    rw [gradedProjection_comm (dual L).grading (dual K).grading (dualMap i).toFun
      (dualMap i).map_grading n y, hy, map_zero]

end DifferentialGraded.LeftModule

end
