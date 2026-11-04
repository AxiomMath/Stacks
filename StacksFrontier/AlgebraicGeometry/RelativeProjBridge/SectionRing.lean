module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Algebra

/-!
# The graded ring of sections of a sheaf-level graded algebra

For a sheaf-level graded `𝒪_S`-algebra `A` and an open `U` of `S`, this file builds the graded
ring of sections of `A` over `U`: the external direct sum `⨁ n : ℕ, Γ(A.piece n, U)` of the
nonnegative homogeneous pieces, its commutative ring structure, its internal grading by
additive subgroups, and the structure map from `𝒪_S(U)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces`: the
  homogeneous sections of degree `n` over an open.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRing`: their direct
  sum, `⨁ n : ℕ, Γ(A.piece n, U)`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`: the internal
  grading, by the ranges of the inclusions of the homogeneous summands.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom`: the structure map
  `𝒪_S(U) →+* ⨁ n, Γ(A.piece n, U)`, a function to its multiple of the unit.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.instGCommRing` and
  `instCommRing`: the homogeneous sections form a graded commutative ring, hence their direct
  sum is a commutative ring.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.instGradedRing`: that ring is
  internally graded by `grading`, so it is the carrier Situation 01NN wants.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom_mul_of` and
  `strHom_mul_apply`: multiplication by a degree-`0` section is the module action of the
  corresponding function, on a homogeneous summand and on all components.

## Implementation notes

**The carrier comparison.** Two descriptions of the graded ring of sections are in play: the
*external* direct sum `⨁ n : ℕ, Γ(A.piece n, U)`, which is what the sheaf-level data produces,
and the *internal* grading `ℕ → AddSubgroup (ring U)` by which
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` records its graded rings. The external
sum is the carrier, and the internal grading is the family of ranges of the summand inclusions
`DirectSum.of`; `DirectSum.Decomposition.ofAddHom` turns the evident inverse into the
decomposition, and the graded-monoid axioms transfer from `DirectSum.of_mul_of`. No comparison
map and no quotient is involved: the internal grading is read off the external sum.

**Degree bookkeeping, and why there is almost none.** The pieces are indexed by `ℤ`, matching
the source, while the grading of the section ring is by `ℕ`. The two spellings `(n : ℤ) + (m : ℤ)`
and `((n + m : ℕ) : ℤ)` are *definitionally* equal, since `Nat.cast` into `ℤ` is `Int.ofNat` and
`Int.add` reduces on constructors; so the multiplication of homogeneous sections needs no
transport at all, and the only transports left are the `ℕ`-index ones that Mathlib's
`GradedMonoid` interface forces for the unit, associativity and commutativity laws. Those are
`gradedMonoid_ext`, which is `Sigma.ext`, and `heq_smul` for the degree-`0` action.

**Transparency.** `sectionPieces` and `grading` are `abbrev`s on purpose. `sectionPieces` must
be reducible for the `AddCommGroup` and `Module` instances on `Γ(A.piece n, U)` to be found at
the graded-ring fields; `grading` must be reducible for `simp` to see the summand inclusions
inside `Decomposition.ofAddHom`, which a semireducible `def` hides, leaving the first
obligation of the decomposition unsolved. Rewriting is syntactic in the degree spelling:
`A.mul ↑0 ↑n` with `ℕ`-casts and `A.mul 0 ↑n` with an `ℤ` literal are definitionally equal but
do not match, so every degree-`0` computation is isolated in a lemma written in one spelling
(`app_zero_zero_smul`, `heq_app_zero_smul`) and applied with `exact`.

**Universes.** Monomorphic in the scheme universe `u`, as the sheaf-level data is: the
homogeneous pieces are `S.Modules`, whose sections live in `Type u`, so the section ring does
too.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)

## Not done here

Restriction of the graded rings of sections and the localization property are in the sibling
file `StacksFrontier/AlgebraicGeometry/RelativeProjBridge/Basic.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open DirectSum

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The degree-`n` homogeneous sections over an open. -/
public abbrev sectionPieces (n : ℕ) : Type u := Γ(A.piece (n : ℤ), U)

/-- The unit of the graded sections is the unit section of `A`, in degree `0`. -/
public noncomputable instance instGOne : GradedMonoid.GOne (A.sectionPieces U) := ⟨A.one U⟩

/-- The product of homogeneous sections is the algebra's multiplication `A.mul n m` over `U`. -/
public noncomputable instance instGMul : GradedMonoid.GMul (A.sectionPieces U) :=
  ⟨fun {n m} a b => (A.mul (n : ℤ) (m : ℤ)).app U a b⟩

/-- The graded unit is the unit section of `A`. -/
public theorem gOne_def :
    (GradedMonoid.GOne.one : A.sectionPieces U 0) = A.one U := rfl

/-- The graded product of two homogeneous sections is `A.mul n m` applied to them. -/
public theorem gMul_def {n m : ℕ} (a : A.sectionPieces U n) (b : A.sectionPieces U m) :
    (GradedMonoid.GMul.mul a b : A.sectionPieces U (n + m)) =
      (A.mul (n : ℤ) (m : ℤ)).app U a b := rfl

/-- The homogeneous sections form a graded monoid: the unit and associativity laws are those of
`A`. -/
public noncomputable instance instGMonoid : GradedMonoid.GMonoid (A.sectionPieces U) where
  one_mul a := Sigma.ext (Nat.zero_add a.1) (A.one_mul _ U a.2)
  mul_one a := Sigma.ext (Nat.add_zero a.1) (A.mul_one _ U a.2)
  mul_assoc a b c := Sigma.ext (Nat.add_assoc a.1 b.1 c.1) (A.mul_assoc _ _ _ U a.2 b.2 c.2)

/-- The homogeneous sections form a graded ring, with the integers acting through multiples of
the unit. -/
public noncomputable instance instGRing : DirectSum.GRing (A.sectionPieces U) where
  mul_zero a := map_zero _
  zero_mul b := by rw [gMul_def, map_zero]; rfl
  mul_add a b c := map_add _ _ _
  add_mul a b c := by rw [gMul_def, map_add]; rfl
  natCast n := n • A.one U
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast n := n • A.one U
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

/-- **Stacks 01NN, the graded rings of local sections.** The homogeneous sections of a
quasi-coherent graded algebra over an open form a graded commutative ring, whose multiplication
and unit are the algebra's own: see the characterizing equations below. -/
@[stacks 01NN "graded rings of local sections"]
public noncomputable instance instGCommRing : DirectSum.GCommRing (A.sectionPieces U) where
  mul_comm a b := Sigma.ext (Nat.add_comm a.1 b.1) (A.mul_comm _ _ U a.2 b.2)

/-- The graded ring of sections of `A` over an open: the direct sum of the homogeneous
pieces. -/
public abbrev sectionRing : Type u := ⨁ n : ℕ, A.sectionPieces U n

/-- The section ring is a commutative ring, from the graded commutative ring structure. -/
public noncomputable instance instCommRing : CommRing (A.sectionRing U) := inferInstance

/-! ### Degree bookkeeping -/

/-- Equality in the graded monoid of homogeneous sections, from an equality of degrees and a
heterogeneous equality of sections. This is the only transport the construction needs. -/
public theorem gradedMonoid_ext {i j : ℕ} (hij : i = j) {a : A.sectionPieces U i}
    {b : A.sectionPieces U j} (h : HEq a b) :
    (GradedMonoid.mk i a : GradedMonoid (A.sectionPieces U)) = GradedMonoid.mk j b :=
  Sigma.ext hij h

/-- Transport of a scalar multiple along an equality of degrees. -/
public theorem heq_smul {i j : ℕ} (hij : i = j) (r : Γ(S, U)) {z : A.sectionPieces U i}
    {y : A.sectionPieces U j} (h : HEq z y) : HEq (r • z) (r • y) := by
  subst hij
  rw [eq_of_heq h]

/-- The product of the unit with itself is the unit. Both sides lie in degree `0 + 0`, which is
`0` definitionally, so this is an equality rather than a heterogeneous one. -/
public theorem mul_one_one : (A.mul 0 0).app U (A.one U) (A.one U) = A.one U :=
  eq_of_heq (A.one_mul 0 U (A.one U))

/-- The product of two multiples of the unit. -/
public theorem app_zero_zero_smul (r s : Γ(S, U)) :
    (A.mul 0 0).app U (r • A.one U) (s • A.one U) = (r * s) • A.one U := by
  rw [(A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right, A.mul_one_one U, smul_smul]

/-- A multiple of the unit multiplies a homogeneous section by acting on it. -/
public theorem heq_app_zero_smul (r : Γ(S, U)) {n : ℕ} (y : A.sectionPieces U n) :
    HEq ((A.mul 0 (n : ℤ)).app U (r • A.one U) y) (r • y) := by
  rw [(A.mul 0 (n : ℤ)).map_smul_left]
  exact A.heq_smul U (Nat.zero_add n) r (A.one_mul (n : ℤ) U y)

/-! ### The internal grading -/

/-- The degree-`n` part of the section ring, as an additive subgroup: the range of the
inclusion of the degree-`n` summand. -/
public noncomputable abbrev grading (n : ℕ) : AddSubgroup (A.sectionRing U) :=
  (DirectSum.of (A.sectionPieces U) n).range

/-- The additive subgroups of the section ring form an `AddSubgroupClass`.

Named, rather than left to `inferInstance` at each use site, because this instance is
an argument of `AlgebraicGeometry.Proj (A.grading U)` and appears at some forty
positions inside the body of a single morphism there. Anonymous, Lean's nested-proof
abstraction lifts it into a *per-declaration* auxiliary, so two spellings of one term
differ at every one of those positions and the kernel must discharge forty
proof-irrelevance checks, each needing the type of the abstracted proof — the
`GradedRing`/`DirectSum` tower over `A.sectionRing U`. Observed cost of the resulting
`rfl`: 171–211 s of *kernel* time against a limit between 78 s and 171 s, i.e. a
`(kernel) deterministic timeout` that no elaborator option can reach, since the
kernel ignores both transparency attributes and heartbeat budgets. With the instance
named, every elaboration spells it as the same small constant application and the
comparison is free.

Consistent with this file's own transparency note, which records that `sectionPieces`
and `grading` are `abbrev`s deliberately, for instance-finding reasons. -/
public noncomputable instance instAddSubgroupClass :
    AddSubgroupClass (AddSubgroup (A.sectionRing U)) (A.sectionRing U) := inferInstance

/-- A homogeneous section of degree `n` lies in the degree-`n` part of the section ring. -/
public theorem of_mem_grading {n : ℕ} (y : A.sectionPieces U n) :
    DirectSum.of (A.sectionPieces U) n y ∈ A.grading U n := ⟨y, rfl⟩

/-- An element lies in the degree-`n` part exactly when it is the inclusion of a homogeneous
section of degree `n`. -/
public theorem mem_grading_iff {n : ℕ} (x : A.sectionRing U) :
    x ∈ A.grading U n ↔ ∃ y, DirectSum.of (A.sectionPieces U) n y = x := Iff.rfl

/-- The section ring is the direct sum of its homogeneous parts. -/
@[instance_reducible]
public noncomputable def decomposition : DirectSum.Decomposition (A.grading U) := by
  let d : A.sectionRing U →+ ⨁ n : ℕ, A.grading U n :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => A.grading U n) n).comp
        (DirectSum.of (A.sectionPieces U) n).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp [d]
  · apply DirectSum.addHom_ext
    intro n y
    obtain ⟨x, hx⟩ := y
    obtain ⟨a, rfl⟩ := hx
    simp [d]
    rfl

/-- **The section ring is an `ℕ`-graded ring.** -/
public noncomputable instance instGradedRing : GradedRing (A.grading U) where
  toDecomposition := A.decomposition U
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro n m a b ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (DirectSum.of_mul_of (A := A.sectionPieces U) a b).symm⟩

/-! ### The structure map -/

/-- The structure map from the sections of `𝒪_S` over an open to the graded ring of sections
of `A`: a function is sent to its multiple of the unit. -/
@[stacks 01NN "graded rings of local sections"]
public noncomputable def strHom : Γ(S, U) →+* A.sectionRing U where
  toFun r := DirectSum.of (A.sectionPieces U) 0 (r • A.one U)
  map_one' := by rw [one_smul]; exact (DirectSum.one_def _).symm
  map_mul' r s := by
    rw [DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (A.gradedMonoid_ext U rfl (heq_of_eq (A.app_zero_zero_smul U r s).symm))
  map_zero' := by rw [zero_smul, map_zero]
  map_add' r s := by rw [add_smul, map_add]

/-- The structure map sends a function to its multiple of the unit, in degree `0`. -/
@[stacks 01NN "graded rings of local sections"]
public theorem strHom_apply (r : Γ(S, U)) :
    A.strHom U r = DirectSum.of (A.sectionPieces U) 0 (r • A.one U) := rfl

/-- The structure map lands in the degree-`0` part of the section ring. -/
public theorem strHom_mem (r : Γ(S, U)) : A.strHom U r ∈ A.grading U 0 :=
  A.of_mem_grading U _

/-- **Multiplication by a degree-`0` section is the module action.** -/
public theorem strHom_mul_of (r : Γ(S, U)) {n : ℕ} (y : A.sectionPieces U n) :
    A.strHom U r * DirectSum.of (A.sectionPieces U) n y =
      DirectSum.of (A.sectionPieces U) n (r • y) := by
  rw [A.strHom_apply U r, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (A.gradedMonoid_ext U (Nat.zero_add n) (A.heq_app_zero_smul U r y))

/-- Multiplication by a degree-`0` section, read on the homogeneous components. -/
public theorem strHom_mul_apply (r : Γ(S, U)) (w : A.sectionRing U) (n : ℕ) :
    (A.strHom U r * w) n = r • w n := by
  induction w using DirectSum.induction_on with
  | zero => rw [mul_zero]; simp
  | of m y =>
    rw [A.strHom_mul_of U r y, DirectSum.of_apply, DirectSum.of_apply]
    rcases eq_or_ne m n with rfl | hmn
    · simp
    · simp [hmn]
  | add x y hx hy => rw [mul_add]; simp [hx, hy]

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
