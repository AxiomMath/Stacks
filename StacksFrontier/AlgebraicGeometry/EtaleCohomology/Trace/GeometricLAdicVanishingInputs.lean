module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction

/-!
# The vanishing input of Tag 03V2: Tag 095U, as statements

The degree bound of [Stacks, Tag 03V2], that `Hⁱ_c(X_k̄, F)` vanishes above `2 dim X`, rests on
[Stacks, Tag 095U]: for a proper morphism `f` all of whose fibres have dimension at most `n`,
`R^q f_* F = 0` for every torsion abelian sheaf `F` and every `q > 2n`.  That lemma is not proved
in this library (its induction needs the curve case [Stacks, Tag 03SC], ported separately).  This
file records it, and the absolute form in which the proof of Tag 03V2 consumes it, as
propositions, so that the conditional steps of 03V2 can name exactly what they use.  Nothing here
is registered against a tag: these are statements, not proofs.

* `Stacks.EtaleCohomology.ProperDirectImageVanishingStatement`: Tag 095U, in the shape of the
  source: abelian torsion sheaves, `AlgebraicGeometry.Scheme.Hom.IsEtaleHigherDirectImageBound`.
* `Stacks.EtaleCohomology.ProperSeparablyClosedVanishingStatement`: its absolute case over a
  separably closed field, for sheaves of `ℤ/m`-modules: if `Y` is proper over a separably closed
  field `K` with `dim Y ≤ n`, then `Hᵠ(Y, G) = 0` for `q > 2n`, cohomology being
  `Hᵠ(RΓ(Spec K, Rg_* G))`.  This is the step to which the proof of 095U itself reduces (via
  Tag 0DDF), and it follows from 095U because `Γ(Spec K, -)` is exact for `K` separably closed
  and the higher direct images of a sheaf of `ℤ/m`-modules agree with those of the underlying
  abelian sheaf, which is torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 095U], as a statement.**  For every proper morphism of schemes `f : X ⟶ Y` all
of whose fibres have dimension at most `n`, and every torsion abelian sheaf `F` on `X_étale`,
`R^q f_* F = 0` for `q > 2n`. -/
def ProperDirectImageVanishingStatement : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (n : ℕ),
    (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n) →
      f.IsEtaleHigherDirectImageBound ((2 * n : ℕ) : ℕ∞)

/-- **The absolute case of [Stacks, Tag 095U] over a separably closed field, for sheaves of
`ℤ/m`-modules, as a statement.**  For every scheme `Y` proper over a separably closed field `K`
with `dim Y ≤ n`, every `m ≠ 0` and every sheaf `G` of `ℤ/m`-modules on `Y_étale`,
`Hᵠ(Y, G) = Hᵠ(RΓ(Spec K, Rg_* G)) = 0` for `q > 2n`. -/
def ProperSeparablyClosedVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsSepClosed K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g]
    (n : ℕ), topologicalKrullDim Y ≤ n → ∀ (m : ℕ) [NeZero m] (G : EtaleModules.{u, 0} (ZMod m) Y)
      (q : ℤ), 2 * (n : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod m)) q).obj
          (derivedDirectImageSections g (ZMod m) G))

end Stacks.EtaleCohomology
