module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication

/-!
# Tag 01O4 in one statement

Let `S` be a scheme and `𝒜` a quasi-coherent sheaf of graded `𝒪_S`-modules generated as an
`𝒜_0`-algebra by `𝒜_1`. [Stacks, Tag 01O4] makes three assertions about
`X = Proj_S(𝒜)`:

1. `X` represents the functor `F_1` which sends `f : T ⟶ S` to the set of pairs `(L, ψ)` with `L`
   an invertible `𝒪_T`-module and `ψ : f^*𝒜 ⟶ ⨁_{n ≥ 0} L^{⊗ n}` a graded `𝒪_T`-algebra
   homomorphism whose degree-one component `f^*𝒜_1 ⟶ L` is surjective, taken up to strict
   equivalence;
2. all the quasi-coherent sheaves `𝒪_{Proj(𝒜)}(n)` are invertible `𝒪_{Proj(𝒜)}`-modules;
3. the multiplication maps induce isomorphisms
   `𝒪_{Proj(𝒜)}(n) ⊗ 𝒪_{Proj(𝒜)}(m) ⟶ 𝒪_{Proj(𝒜)}(n + m)`.

Each of the three is established separately —
`Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible` and
`Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra` — and the
first lives in a module that does not see the other two. This file imports both sides and states
all three together, under the source's degree-one generation hypothesis and nothing else.

The twists of the second and third assertions are **the** twists: the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which is constructed from
the graded algebra alone, so `𝒪_{Proj(𝒜)}(n)` is a term and not an input. The degree-one
generation hypothesis serves all three conjuncts: `...ProjRepresentsF1.IsGeneratedInDegreeOne` is
by definition the condition `Algebra.adjoin (𝒜_0(U)) (𝒜_1(U)) = ⊤` over every affine open `U`
that the two twist lemmas take.

One binder beyond the source's hypothesis remains, the choice of tensor algebras
`TA : TensorAlgebras`. It is data rather than a hypothesis, and it is what the library needs in
order to speak of `⨁_{n ≥ 0} L^{⊗ n}` at all, hence to state the first assertion; the comparison
of its pullbacks is then pinned to the canonical one,
`...ProjRepresentsF1.tensorAlgebraPullbackIsos`.

## Main results

* `Stacks.AlgebraicGeometry.TwistMapsInvertible.f1Bundle_and_twists`: **the three assertions of
  [Stacks, Tag 01O4] in one statement.**

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

/-- **[Stacks, Tag 01O4].** Let `S` be a scheme and `𝒜` a quasi-coherent sheaf of graded
`𝒪_S`-modules generated as an `𝒜_0`-algebra by `𝒜_1`. Then, for `X = Proj_S(𝒜)`:

1. `X` represents the functor `F_1` of pairs `(L, ψ)` with `L` invertible and `f^*𝒜_1 ⟶ L`
   surjective, up to strict equivalence — the bijections between the morphisms `T ⟶ X` over `S`
   and the strict isomorphism classes of such pairs, normalised at the identity of `X` and
   natural in the test scheme;
2. every homogeneous piece `𝒪_X(n)` of the canonical twist datum on `X` is an invertible
   `𝒪_X`-module; and
3. the multiplication maps `𝒪_X(n) ⊗ 𝒪_X(m) ⟶ 𝒪_X(n + m)` are isomorphisms in all integer
   degrees.

The first assertion is a family of bijections, hence data rather than a proposition, so it is
joined to the other two by `PProd` rather than `And`.

The hypothesis `hgen` is the source's own degree-one generation. The binder `TA` is the choice of
tensor algebras, which is data the library needs in order to state the first assertion at all,
and the comparison of its pullbacks is the canonical `tensorAlgebraPullbackIsos`. The twists are
the canonical twist datum `twistDataOfGradedAlgebra`, constructed from `𝒜` alone.

The three assertions are `...ProjRepresentsF1.f1Bundle`,
`twistDataOfGradedAlgebra_isInvertible` and `isIso_mulSheaf_twistDataOfGradedAlgebra`. -/
@[stacks 01O4 "for a scheme S and a quasi-coherent sheaf of graded O_S-modules A generated as an \
A_0-algebra by A_1, three things hold of X = Proj_S(A): X represents the functor F_1 sending \
f : T -> S to the strict isomorphism classes of pairs (L, psi) with L an invertible O_T-module \
and psi : f^*A -> ⨁_{n >= 0} L^{⊗ n} a graded algebra homomorphism whose degree-one component \
f^*A_1 -> L is surjective, by bijections normalised at the identity of X and natural in the test \
scheme; every homogeneous piece O_X(n) of the canonical twist datum on X is an invertible \
O_X-module; and the multiplication maps O_X(n) (x) O_X(m) -> O_X(n+m) are isomorphisms in all \
integer degrees"]
def f1Bundle_and_twists {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
    (hgen : IsGeneratedInDegreeOne A) :
    PProd (F1Bundle A TA (tensorAlgebraPullbackIsos TA))
      ((∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
            (relativeProj A).scheme.ringCatSheaf.2
            ((twistDataOfGradedAlgebra A).algebra.piece n)) ∧
        ∀ n m : ℤ, IsIso (_root_.SheafOfModules.GradedAlgebra.mulSheaf
          (twistDataOfGradedAlgebra A).algebra n m)) :=
  ⟨f1Bundle A TA hgen, fun n => twistDataOfGradedAlgebra_isInvertible hgen n,
    fun n m => isIso_mulSheaf_twistDataOfGradedAlgebra hgen n m⟩

end Stacks.AlgebraicGeometry.TwistMapsInvertible

end
