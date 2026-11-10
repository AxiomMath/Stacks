module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Cohomology
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyClassOfClosedMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory

/-! # The canonical map from the cohomology of a differential graded algebra to its derived
graded endomorphisms of a bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. A homogeneous element `a` of `A` of degree `k` acts on
`N` by left multiplication, which is a degree-`k` right `B`-linear map
`DifferentialGraded.Bimodule.leftMultiplication`. That map is closed for the Hom differential
exactly when `a` is a cocycle, in which case it is a homomorphism `N → N[k]` of differential
graded `B`-modules (`DifferentialGraded.Bimodule.cocycleAction`), and cohomologous cocycles act by
homotopic homomorphisms. Passing to the quotient therefore produces the canonical map
$$H^k(A) \longrightarrow \Hom_{D(B, d)}(N, N[k])$$
whose bijectivity is hypothesis (2) of [Stacks, Tag 09R9].

## Main definitions

* `DifferentialGraded.Bimodule.leftMultiplication`: left multiplication by a homogeneous element,
  as a homogeneous right `B`-linear endomorphism of the bimodule.
* `DifferentialGraded.Bimodule.cocycleAction`: the homomorphism `N → N[k]` of differential graded
  `B`-modules given by the action of a degree-`k` cocycle.
* `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison`: the canonical map
  `H^k(A) → Hom_{D(B, d)}(N, N[k])`.

## Main results

* `DifferentialGraded.Bimodule.homogeneousMapDifferential_leftMultiplication`: left multiplication
  intertwines the differential of `A` with the Hom differential.
* `DifferentialGraded.Bimodule.toHomotopyCategory_map_cocycleAction_eq`: cohomologous cocycles act
  by the same morphism of the homotopy category.

## Implementation notes

The base ring, the two algebras and the modules all live in a single universe `u`, as in the
`DifferentialGradedAlgebra` encoding of Stacks Tag 09JJ, whereas the Stacks Project allows them to
be independent.

The left action of a bimodule is a family of cochains on the underlying complex, each induced by a
homogeneous right `B`-linear map (`DifferentialGradedModule.IsRightLinearCochain`);
`leftMultiplication` is that induced map, and `leftMultiplication_apply` computes it on
homogeneous elements.

## References

* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9); the action of a cocycle
  on a homomorphism into a shift is [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC).
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe u

/- The underlying cochain complex is made locally reducible: the components of the left action
cochain are elements of `N.rightModule.toCochainComplex.X i`, which is the homogeneous piece
`N.rightModule.grading i` by definition but not reducibly so, and instance search and the
tactic-level type checks run below default transparency. -/
attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex

namespace DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} (N : Bimodule A B)

/-- Left multiplication by a homogeneous element of degree `k`, as a degree-`k` homogeneous right
`B`-linear endomorphism of the bimodule. -/
def leftMultiplication (k : ℤ) (a : A.grading k) :
    HomogeneousMap B N.rightModule N.rightModule k :=
  (N.leftAction.2 k a).choose

/-- On a homogeneous element, left multiplication is the corresponding component of the left
action cochain of the bimodule. -/
theorem leftMultiplication_apply (k p : ℤ) (a : A.grading k) (x : N.rightModule.grading p) :
    (N.leftMultiplication k a).1 x =
      ((show N.rightModule.grading (p + k) from
        (N.leftAction.1.action k a).v p (p + k) rfl x) : N.rightModule.M) :=
  ((N.leftAction.2 k a).choose_spec p x).symm

/-- Homogeneous endomorphisms of the bimodule are equal if they agree on homogeneous elements. -/
private theorem homogeneousMap_ext_of_apply {k : ℤ}
    (f g : HomogeneousMap B N.rightModule N.rightModule k)
    (h : ∀ (p : ℤ) (x : N.rightModule.grading p), f.1 x = g.1 x) : f = g := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | homogeneous x => exact h _ x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Left multiplication by zero is zero. -/
theorem leftMultiplication_zero (k : ℤ) : N.leftMultiplication k 0 = 0 := by
  refine N.homogeneousMap_ext_of_apply _ _ fun p x => ?_
  simp only [leftMultiplication_apply, map_zero, Cochain.zero_v]
  rfl

/-- Left multiplication is additive in the acting element. -/
theorem leftMultiplication_sub (k : ℤ) (a b : A.grading k) :
    N.leftMultiplication k (a - b) =
      N.leftMultiplication k a - N.leftMultiplication k b := by
  refine N.homogeneousMap_ext_of_apply _ _ fun p x => ?_
  change (N.leftMultiplication k (a - b)).1 x =
    (N.leftMultiplication k a).1 x - (N.leftMultiplication k b).1 x
  simp only [leftMultiplication_apply, map_sub, Cochain.sub_v]
  rfl

/-- Left multiplication intertwines the differential of the algebra with the Hom differential: the
Hom differential of left multiplication by `a` is left multiplication by `d a`. -/
theorem homogeneousMapDifferential_leftMultiplication (k : ℤ) (a : A.grading k) :
    homogeneousMapDifferential B (N.leftMultiplication k a) =
      N.leftMultiplication (k + 1) ⟨A.d a, A.d_mem k a a.property⟩ := by
  refine N.homogeneousMap_ext_of_apply _ _ fun p x => ?_
  change N.rightModule.d ((N.leftMultiplication k a).1 x) -
    gradedSign R k • (N.leftMultiplication k a).1 (N.rightModule.d x) = _
  rw [leftMultiplication_apply, leftMultiplication_apply, N.leftAction.1.map_d,
    δ_v k (k + 1) rfl _ p (p + (k + 1)) rfl (p + k) (p + 1) (by lia) rfl]
  have hcomponent (i j : ℤ) (hij : i + k = j) (y : N.rightModule.grading i) :
      ((show N.rightModule.grading j from
        (N.leftAction.1.action k a).v i j hij y) : N.rightModule.M) =
        (N.leftMultiplication k a).1 y := by
    subst j
    exact (leftMultiplication_apply N k i a y).symm
  have hd (i j : ℤ) (hij : i + 1 = j) (y : N.rightModule.grading i) :
      ((show N.rightModule.grading j from
        N.rightModule.toCochainComplex.d i j y) : N.rightModule.M) = N.rightModule.d y := by
    subst j
    rw [DifferentialGradedModule.toCochainComplex_d]
    rfl
  change _ =
    ((show N.rightModule.grading (p + (k + 1)) from
      N.rightModule.toCochainComplex.d (p + k) (p + (k + 1))
        ((N.leftAction.1.action k a).v p (p + k) rfl x)) : N.rightModule.M) +
    ((k + 1).negOnePow : ℤ) •
      ((show N.rightModule.grading (p + (k + 1)) from
        (N.leftAction.1.action k a).v (p + 1) (p + (k + 1)) (by lia)
          (N.rightModule.toCochainComplex.d p (p + 1) x)) : N.rightModule.M)
  rw [hd (p + k) (p + (k + 1)) (by lia), hcomponent, DifferentialGradedModule.toCochainComplex_d,
    Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.val_neg, neg_smul, sub_eq_add_neg,
    ← Int.cast_smul_eq_zsmul R, intCast_negOnePow, hcomponent]
  rfl

/-- The action of a cocycle is closed for the Hom differential. -/
theorem homogeneousMapDifferential_leftMultiplication_eq_zero (k : ℤ) (a : A.Cocycle k) :
    homogeneousMapDifferential B (N.leftMultiplication k a.1) = 0 := by
  rw [homogeneousMapDifferential_leftMultiplication,
    show (⟨A.d a.1, A.d_mem k a.1 a.1.property⟩ : A.grading (k + 1)) = 0 from Subtype.ext a.2,
    leftMultiplication_zero]

/-- A degree-`k` cocycle of `A` acts on the bimodule by a homomorphism `N ⟶ N[k]` of differential
graded `B`-modules. -/
def cocycleAction (k : ℤ) (a : A.Cocycle k) :
    N.rightModule ⟶ N.rightModule.shift k :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift B _ _ k
    (N.leftMultiplication k a.1)).mp
      (N.homogeneousMapDifferential_leftMultiplication_eq_zero k a)).choose

/-- The homomorphism attached to a cocycle has left multiplication as its underlying linear
map. -/
theorem cocycleAction_toFun (k : ℤ) (a : A.Cocycle k) :
    (N.cocycleAction k a).toFun = (N.leftMultiplication k a.1).1 :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift B _ _ k
    (N.leftMultiplication k a.1)).mp
      (N.homogeneousMapDifferential_leftMultiplication_eq_zero k a)).choose_spec

/-- Cohomologous cocycles act by the same morphism of the homotopy category. -/
theorem toHomotopyCategory_map_cocycleAction_eq (k : ℤ) (a b : A.Cocycle k)
    (h : ∃ c : A.grading (k - 1), (a.1 : A.A) - b.1 = A.d c) :
    (toHomotopyCategory B).map (N.cocycleAction k a) =
      (toHomotopyCategory B).map (N.cocycleAction k b) := by
  obtain ⟨c, hc⟩ := h
  have hd : (homogeneousMapDifferential B (N.leftMultiplication (k - 1) c)).1 =
      (N.leftMultiplication k a.1 - N.leftMultiplication k b.1).1 := by
    rw [homogeneousMapDifferential_leftMultiplication, ← leftMultiplication_sub]
    generalize hl : k - 1 = l at c hc ⊢
    obtain rfl : k = l + 1 := by lia
    congr 2
    exact Subtype.ext hc.symm
  exact (toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential B
    (N.cocycleAction_toFun k a) (N.cocycleAction_toFun k b)).mpr
      ⟨N.leftMultiplication (k - 1) c, by rw [hd, Submodule.coe_sub]⟩

/-- The canonical map `H^k(A) → Hom_{D(B, d)}(N, N[k])` induced by the left action of `A` on the
bimodule. The target is formed with the image of the shifted differential graded module, the
canonical model of `N[k]`. -/
def cohomologyEndomorphismComparison (k : ℤ) :
    A.Cohomology k →
      (((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        ((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).obj (N.rightModule.shift k)) :=
  Quotient.lift
    (fun a => ((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).map (N.cocycleAction k a))
    (fun _ _ h => congrArg ((quasiIsomorphisms' B).Q.map)
      (N.toHomotopyCategory_map_cocycleAction_eq k _ _ h))

/-- On the class of a cocycle, the canonical comparison is the image in the derived category of
the action of that cocycle. -/
theorem cohomologyEndomorphismComparison_mk (k : ℤ) (a : A.Cocycle k) :
    N.cohomologyEndomorphismComparison k (Quotient.mk _ a) =
      ((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).map (N.cocycleAction k a) :=
  rfl

end DifferentialGraded.Bimodule

end
