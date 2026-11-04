module

public import StacksFrontier.Homology.Perfect.Basic

@[expose] public section

/-!
# Perfectness along a finite filtration

Let `R` be a ring and let `D(R)` be the derived category of `R`-modules. [Stacks, Tag 066R],
`StacksDraft.Perfect.isPerfect_of_distinguished`, says that perfectness is a two-out-of-three
property along a distinguished triangle. Iterating it gives the statement that the stupid
filtration argument of the Stacks project uses over and over: **an object carrying a finite
filtration whose graded pieces are perfect is itself perfect.**

Two indexings of "finite filtration" are recorded, because both occur. The increasing one starts
at a zero object and builds up, `0 = L_0 → L_1 → ⋯ → L_n = K`, which is the shape a filtration
by subobjects of an abelian category leaves behind in the derived category. The decreasing one
starts at `K` and exhausts it, `K = L_0 ← L_1 ← ⋯ ← L_n = 0`, which is the shape of the stupid
filtration `σ^{≥ q}` of a bounded complex. In both cases the graded pieces `G_i` are the third
objects of the distinguished triangles, and the inductive step is the same component of
[Stacks, Tag 066R].

The filtration is not asked for as a predicate on the object, and deliberately so: a one-step
filtration `0 → K` has `K` itself as its only graded piece, so "admits a finite filtration with
perfect graded pieces" is *equivalent* to perfectness and would be no reduction at all. The
content is in the implication, applied to a filtration whose graded pieces are given by something
other than `K` — for the stupid filtration of a complex, by the shifted terms.

A zero object is perfect, which is the base case of both inductions; it is recorded separately as
`StacksDraft.Perfect.isPerfect_of_isZero`, the zero complex being a bounded complex of finite
projective modules.

## Main results

* `StacksDraft.Perfect.isPerfect_of_isZero`: a zero object of `D(R)` is perfect.
* `StacksDraft.Perfect.isPerfect_of_filtration`: the top of an increasing finite filtration whose
  bottom is zero and whose graded pieces are perfect is perfect.
* `StacksDraft.Perfect.isPerfect_of_filtration_desc`: the bottom of a decreasing finite filtration
  whose top is zero and whose graded pieces are perfect is perfect.

## References

* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- A zero object of `D(R)` is perfect: the zero complex is a bounded complex of finite projective
modules, and it represents every zero object. -/
theorem isPerfect_of_isZero {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsZero K) : IsPerfect K := by
  let P : CochainComplex (ModuleCat.{v} R) ℤ := HomologicalComplex.zero
  have hP : IsZero P := HomologicalComplex.isZero_zero
  have hPX (i : ℤ) : IsZero (P.X i) := (HomologicalComplex.eval _ _ i).map_isZero hP
  have (i : ℤ) : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp (hPX i)
  exact ⟨P, 0, 0, (CochainComplex.isStrictlyGE_iff _ _).2 fun i _ => hPX i,
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i _ => hPX i, fun _ => inferInstance,
    fun _ => inferInstance, ⟨hK.iso (DerivedCategory.Q.map_isZero hP)⟩⟩

/-- **A finite filtration with perfect graded pieces is perfect**, for a filtration indexed
increasingly from a zero object: if `L 0` is zero, if for every `i < n` there is a distinguished
triangle `L i ⟶ L (i + 1) ⟶ G i ⟶ (L i)⟦1⟧`, and if every `G i` with `i < n` is perfect, then
`L n` is perfect.

This is [Stacks, Tag 066R] iterated: at each step the first and third objects of the triangle are
perfect — the first by induction, the third by hypothesis — so the second is, which is the
`isPerfect_of_distinguished` component `IsPerfect T.obj₁ → IsPerfect T.obj₃ → IsPerfect T.obj₂`.
Only the triangles below `n` are used, so a filtration given on all of `ℕ` may be truncated
anywhere. -/
theorem isPerfect_of_filtration {R : Type u} [CommRing R]
    (L G : ℕ → DerivedCategory (ModuleCat.{v} R)) (n : ℕ)
    (hzero : IsZero (L 0)) (hG : ∀ i < n, IsPerfect (G i))
    (hT : ∀ i < n, ∃ (a : L i ⟶ L (i + 1)) (b : L (i + 1) ⟶ G i)
      (c : G i ⟶ (L i)⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distinguishedTriangles) :
    IsPerfect (L n) := by
  induction n with
  | zero => exact isPerfect_of_isZero _ hzero
  | succ n ih =>
      obtain ⟨a, b, c, hd⟩ := hT n (by lia)
      exact (isPerfect_of_distinguished (Triangle.mk a b c) hd).2.1
        (ih (fun i hi => hG i (by lia)) (fun i hi => hT i (by lia))) (hG n (by lia))

/-- **A finite filtration with perfect graded pieces is perfect**, for a filtration indexed
decreasingly and exhausting the object: if `L n` is zero, if for every `i < n` there is a
distinguished triangle `L (i + 1) ⟶ L i ⟶ G i ⟶ (L (i + 1))⟦1⟧`, and if every `G i` with `i < n`
is perfect, then `L 0` is perfect.

This is the shape of the stupid filtration `σ^{≥ q}` of a bounded complex, whose graded pieces are
the shifted terms, and it is proved by the same component of [Stacks, Tag 066R] as
`isPerfect_of_filtration`, run downwards from the zero end. -/
theorem isPerfect_of_filtration_desc {R : Type u} [CommRing R]
    (L G : ℕ → DerivedCategory (ModuleCat.{v} R)) (n : ℕ)
    (hzero : IsZero (L n)) (hG : ∀ i < n, IsPerfect (G i))
    (hT : ∀ i < n, ∃ (a : L (i + 1) ⟶ L i) (b : L i ⟶ G i)
      (c : G i ⟶ (L (i + 1))⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distinguishedTriangles) :
    IsPerfect (L 0) := by
  induction n generalizing L G with
  | zero => exact isPerfect_of_isZero _ hzero
  | succ n ih =>
      obtain ⟨a, b, c, hd⟩ := hT 0 (by lia)
      exact (isPerfect_of_distinguished (Triangle.mk a b c) hd).2.1
        (ih (fun i => L (i + 1)) (fun i => G (i + 1)) hzero (fun i hi => hG (i + 1) (by lia))
          fun i hi => hT (i + 1) (by lia)) (hG 0 (by lia))

end StacksDraft.Perfect

end
