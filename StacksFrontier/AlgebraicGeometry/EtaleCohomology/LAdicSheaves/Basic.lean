module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves

/-!
# ℓ-adic sheaves on the small étale site

An ℓ-adic sheaf is a compatible inverse system of constructible sheaves of modules over
`ℤ/ℓⁿℤ`. It is lisse when every finite-level sheaf is locally constant, and torsion when
one power of ℓ annihilates the whole system.

## Main definitions

* `Stacks.EtaleCohomology.FiniteLevelSheaf` is the category of small étale sheaves of
  modules at a single finite level of coefficients, with the restriction, reduction and
  comparison maps relating consecutive levels.
* `Stacks.EtaleCohomology.LAdicSheaf` is the type of ℓ-adic sheaves on a Noetherian
  scheme, and `Stacks.EtaleCohomology.LAdicSheaf.Hom` is a morphism of such.
* `Stacks.EtaleCohomology.LAdicSheaf.IsLisse` expresses local constancy at every level.
* `Stacks.EtaleCohomology.LAdicSheaf.IsTorsion` expresses annihilation by a single power
  of ℓ.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.category` makes ℓ-adic sheaves a category.

## Implementation notes

Levels are indexed by `n : ℕ`, with level `n` carrying coefficients in `ℤ/ℓⁿ⁺¹ℤ`. Each
transition is a map to the restriction of scalars of the next level. Scalar reduction is
sheafified extension of scalars along `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ`. The sheaf-level
extension/restriction adjunction canonically induces the reduction map; compatibility
says it is an isomorphism. Morphisms are compatible families of module-sheaf morphisms.

Multiplication by `ℓ ^ k` on an ℓ-adic sheaf is zero precisely when its component at
every finite level is zero. The existential exponent lies outside the universal
quantifier on levels, so it is a uniform bound. This form lets subsequent statements use
torsion as a predicate on objects of the category of ℓ-adic sheaves without requiring an
additive structure on that category.

## References

* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
* [Stacks Project, Tag 03UR](https://stacks.math.columbia.edu/tag/03UR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- A torsion ℓ-adic sheaf is annihilated by a single power of ℓ, uniformly
at all finite levels. -/
@[stacks 03UR "torsion_sheaf"]
public abbrev LAdicSheaf.IsTorsion [IsNoetherian X.1] [Fact ℓ.Prime]
    (F : LAdicSheaf B X ℓ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, (ℓ ^ k) • (𝟙 (F.level n)) = 0

end Stacks.EtaleCohomology
