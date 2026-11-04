module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The canonical descent datum of a quasi-coherent module, and effective descent data

Let `X` be an algebraic space over `S`, let `(f i : Y i ⟶ X)` be a family of algebraic spaces
over it and let `M` be a quasi-coherent `𝒪_X`-module.  The inverse images `(f i)^*M` carry a
descent datum relative to the family whose pairwise isomorphism is the canonical comparison of
the two inverse images of `M` to `Y i ×_X Y j`; this is the canonical descent datum
`(M|_{Y i}, can)` of Stacks 04W5.  For the one-member family `{𝟙 X}` it is the trivial descent
datum.  A descent datum is *effective* when it is isomorphic to a canonical one.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` is the canonical descent
  datum of a quasi-coherent module, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.trivialDescentDatum` its special case for the
  one-member family `{𝟙 X}`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.IsEffective` says that a descent datum is
  isomorphic to the canonical descent datum of a quasi-coherent module on the target.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_canonicalDescentDatum`: a canonical
  descent datum is effective.

## Implementation notes

Everything here is unconditional.  Two inputs are used, and they are why these definitions live
in their own module rather than beside the coherence lemmas they rest on.  The cocycle condition
comes from `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_canonicalComparison` in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/Canonical.lean`, which needs only the
associativity coherence of the comparison of inverse images of Stacks 03LU.  Quasi-coherence of
the inverse images is Stacks 03GA for an *arbitrary* morphism of algebraic spaces,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, whose
module carries the affine chart diagram machinery; keeping that out of the closure of the
coherence lemmas is what this split is for.

Isomorphism of descent data is isomorphism in the category
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.category` of Stacks 04W3, part (2),
rather than a separate notion.

The source defines the canonical descent datum as the pullback of the trivial descent datum
along the family; it is constructed here directly from the inverse images `(f i)^*M` and the
canonical comparison, which is the datum `(M|_{Y i}, can)` the source's notation names.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **Stacks 04W5.**  The canonical descent datum `(M|_{Y i}, can)` of a quasi-coherent
`𝒪_X`-module `M` relative to a family `(f i : Y i ⟶ X)`: the inverse images `(f i)^*M`, with
the canonical comparison of the two inverse images of `M` on each pairwise fibre product. -/
@[stacks 04W5 "the canonical descent datum"]
def canonicalDescentDatum
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    DescentDatum B S hS Y f where
  F i := (modulePullback B S hS (f i)).obj M
  quasicoherent i :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) M hM
  transition i j := canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j)
    (f i) (f j) (pair_condition B S hS Y f i j) M
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    rw [transitionOn_canonicalComparison B S hS Y f M i j vij vi vj hij₀ hij₁,
      transitionOn_canonicalComparison B S hS Y f M j k vjk vj vk hjk₀ hjk₁,
      transitionOn_canonicalComparison B S hS Y f M i k vik vi vk hik₀ hik₁]
    exact canonicalComparison_trans B S hS vi vj vk (f i) (f j) (f k) _ _ M

/-- The `i`-th component module of the canonical descent datum is the inverse image of `M`
along `f i`. -/
@[simp]
theorem canonicalDescentDatum_F
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (i : I) :
    (canonicalDescentDatum B S hS Y f M hM).F i =
      (modulePullback B S hS (f i)).obj M :=
  rfl

/-- The pairwise isomorphism of the canonical descent datum is the canonical comparison of the
two inverse images of `M` to the pairwise fibre product. -/
@[simp]
theorem canonicalDescentDatum_transition
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (i j : I) :
    (canonicalDescentDatum B S hS Y f M hM).transition i j =
      canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j) (f i) (f j)
        (pair_condition B S hS Y f i j) M :=
  rfl

/-- **Stacks 04W5.**  The trivial descent datum of a quasi-coherent `𝒪_X`-module: its canonical
descent datum relative to the one-member family `{𝟙 X}`. -/
@[stacks 04W5 "the trivial descent datum"]
def trivialDescentDatum
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    DescentDatum B S hS (fun _ : PUnit.{v + 1} => X) (fun _ => 𝟙 X) :=
  canonicalDescentDatum B S hS _ _ M hM

/-- **Stacks 04W5.**  A descent datum for quasi-coherent modules is effective when it is
isomorphic to the canonical descent datum of a quasi-coherent module on the target. -/
@[stacks 04W5 "effective descent datum"]
def IsEffective
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (D : DescentDatum B S hS Y f) : Prop :=
  ∃ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite),
    Nonempty (D ≅ canonicalDescentDatum B S hS Y f M hM)

/-- A canonical descent datum is effective. -/
theorem isEffective_canonicalDescentDatum
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    IsEffective B S hS Y f (canonicalDescentDatum B S hS Y f M hM) :=
  ⟨M, hM, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
