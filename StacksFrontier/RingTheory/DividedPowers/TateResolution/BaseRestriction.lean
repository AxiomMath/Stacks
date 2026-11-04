module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ScalarRestriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-! # Reading a graded divided power algebra over a smaller base ring

A graded divided power algebra over `R` is one over any ring `R'` mapping to `R`: the grading,
strict graded commutativity and the divided powers depend on the coefficient ring only through
the underlying submodules, which is the content of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/ScalarRestriction.lean`. This file bundles
that restriction as a `DividedPowers.TateResolution.GradedDPAlgebra` over the smaller base, so
that an algebra over `R` can be the *target* of a morphism out of a construction over `R'`.

This is the situation of the square-zero lift of Tag 09PS. The lift `π : B → A` goes from an
algebra over the square-zero extension `R'` to an algebra over the quotient `R`, and it is a
`RingHom`, not an `R`-algebra map; reading `A` over `R'` through `q` makes it an `R'`-algebra
map, which is the form the universal property of the construction of `B` produces.

## Main definitions

* `DividedPowers.TateResolution.restrictBaseDPAlgebra` — an `R`-algebra with divided powers,
  bundled as a graded divided power algebra over `R'` along a ring map `q : R' → R`.

## Main results

* `DividedPowers.TateResolution.mem_restrictBaseDPAlgebra_grade` — the grading is unchanged as a
  family of subsets, and `DividedPowers.TateResolution.restrictBaseDPAlgebra_dpow` — so are the
  divided powers.
* `DividedPowers.TateResolution.algebraMap_restrictBaseDPAlgebra` — the structure map of the
  restricted algebra is the structure map of the original composed with `q`. This is the clause
  `map_algebraMap` of `DividedPowers.TateResolution.IsSquareZeroLift`.

## Implementation notes

The `R'`-algebra structure on the carrier is `Algebra.compHom`, and the `R'`-algebra structure on
`R` itself is `RingHom.toAlgebra`; `IsScalarTower R' R A` then holds because both reduce to
multiplying by the image of `q`. None of the three is declared as an instance — `q` is not
canonical — so each is introduced with a local `let` where it is needed, and every lemma below is
stated for the bundled algebra, whose fields carry the instances.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

section BaseRestriction

variable {R' : Type u} {R : Type v} {A : Type w}
  [CommRing R'] [CommRing R] [Ring A] [Algebra R A]

/-- Along a ring map `q : R' → R`, scalar multiplication through `R` and scalar multiplication
through `q` agree: both are multiplication by the image of `q`. -/
public theorem isScalarTower_of_ringHom (q : R' →+* R) :
    letI : Algebra R' R := q.toAlgebra
    letI : Algebra R' A := Algebra.compHom A q
    IsScalarTower R' R A := by
  let _ : Algebra R' R := q.toAlgebra
  let _ : Algebra R' A := Algebra.compHom A q
  refine ⟨fun r' r a => ?_⟩
  have hsmul : ∀ (s : R') (x : A), s • x = algebraMap R A (q s) * x := fun s x => by
    rw [Algebra.smul_def]
    rfl
  have hbase : r' • r = q r' * r := rfl
  rw [hsmul, hbase, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-- An `R`-algebra with a grading, strict graded commutativity and divided powers, read as a
graded divided power algebra over a ring `R'` mapping to `R`. -/
public noncomputable def restrictBaseDPAlgebra (q : R' →+* R) (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) :
    GradedDPAlgebra.{u, w} R' :=
  let : Algebra R' R := q.toAlgebra
  let : Algebra R' A := Algebra.compHom A q
  let : IsScalarTower R' R A := isScalarTower_of_ringHom q
  { carrier := A
    ring := inferInstance
    algebra := inferInstance
    grade := restrictGrade R' 𝒜
    graded := inferInstance
    strict := inferInstance
    gamma := γ.restrictScalars R' }

variable (q : R' →+* R) (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜)

/-- The carrier of the restricted algebra is the original algebra. -/
@[simp]
public theorem restrictBaseDPAlgebra_carrier :
    (restrictBaseDPAlgebra q 𝒜 γ).carrier = A := rfl

/-- The grading of the restricted algebra has the same members as the original. -/
@[simp]
public theorem mem_restrictBaseDPAlgebra_grade (n : ℕ) (x : A) :
    x ∈ (restrictBaseDPAlgebra q 𝒜 γ).grade n ↔ x ∈ 𝒜 n := Iff.rfl

/-- The divided powers of the restricted algebra are those of the original. -/
@[simp]
public theorem restrictBaseDPAlgebra_dpow :
    (restrictBaseDPAlgebra q 𝒜 γ).gamma.dpow = γ.dpow := rfl

/-- The positive even part of the restricted algebra has the same members as the original. -/
public theorem mem_restrictBaseDPAlgebra_positiveEvenPart (x : A) :
    x ∈ positiveEvenPart (restrictBaseDPAlgebra q 𝒜 γ).grade ↔ x ∈ positiveEvenPart 𝒜 := by
  let _ : Algebra R' R := q.toAlgebra
  let _ : Algebra R' A := Algebra.compHom A q
  let _ : IsScalarTower R' R A := isScalarTower_of_ringHom q
  exact mem_positiveEvenPart_restrictGrade R' 𝒜 x

/-- The structure map of the restricted algebra is the structure map of the original composed
with `q`. -/
@[simp]
public theorem algebraMap_restrictBaseDPAlgebra (r : R') :
    algebraMap R' (restrictBaseDPAlgebra q 𝒜 γ).carrier r = algebraMap R A (q r) := rfl

end BaseRestriction

end DividedPowers.TateResolution

end
