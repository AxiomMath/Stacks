module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing

/-!
# Smooth base change along a limit of smooth schemes: the statement

Let `S` be a scheme and let `S' = lim S_i` be a directed inverse limit of schemes `S_i` smooth
over `S` with affine transition morphisms. Let `f : X ⟶ S` be quasi-compact and quasi-separated
and let `X' = X ×_S S'`, with projections `f' : X' ⟶ S'` and `g' : X' ⟶ X`. The smooth base
change theorem, in the form of [Stacks, Tag 0F09], asserts that the base change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism for every `E ∈ D⁺(X_étale)` whose cohomology
sheaves have stalks which are torsion of orders invertible on `S`.

This file states that assertion as a proposition, `SmoothLimitBaseChange`.

## Main definitions

* `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn` — an abelian sheaf on `X_étale` has
  stalks which are torsion of orders invertible on `S`: every local section is, locally,
  annihilated by a positive integer which is a unit in `Γ(S, 𝒪_S)`.
* `Stacks.EtaleCohomology.SmoothLimitBaseChange` — the assertion of [Stacks, Tag 0F09].

## References

* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- The derived categories are those of the standard model, in which
-- `smallEtaleDerivedBaseChangeAb` is defined.
attribute [local instance] HasDerivedCategory.standard

/-- An abelian sheaf `F` on the small étale site of `X` **has stalks which are torsion of orders
invertible on `S`**: every local section of `F` is, after restriction along the members of some
étale covering, annihilated by a positive integer which is a unit in `Γ(S, 𝒪_S)`. -/
def HasTorsionOrdersInvertibleOn (S : Scheme.{u}) {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) : Prop :=
  LocallyAnnihilated (smallEtaleTopology X) (fun n : ℕ ↦ 0 < n ∧ IsUnit (n : Γ(S, ⊤))) F

/-- **The assertion of [Stacks, Tag 0F09]**, smooth base change along a limit of smooth schemes.

Let `S' = lim S_i` be a directed inverse limit of schemes `S_i` smooth over `S` with affine
transition morphisms, presented by an inverse system `D` over a directed nonempty preorder `I`,
structure morphisms `p_i : S_i ⟶ S`, a limit cone `c` with point `S'`, and `g : S' ⟶ S` the
composite of each leg of `c` with `p_i`. Let `f : X ⟶ S` be quasi-compact and quasi-separated and
let `X' = X ×_S S'` be a fibre product, with projections `f' : X' ⟶ S'` and `g' : X' ⟶ X`. Then
for every `E ∈ D⁺(X_étale)` whose cohomology sheaves `H^q(E)` have stalks which are torsion of
orders invertible on `S`, the base change map `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism.
-/
def SmoothLimitBaseChange : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S),
    (∀ i, Smooth (p.app i)) → (∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), IsAffineHom (D.map a)) →
    ∀ (c : Cone D), IsLimit c → ∀ (g : c.pt ⟶ S), (∀ i, c.π.app i ≫ p.app i = g) →
    ∀ (X X' : Scheme.{u}) (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (f' : X' ⟶ c.pt) (g' : X' ⟶ X) (sq : IsPullback f' g' g f)
      (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})),
    (∀ q : ℤ, HasTorsionOrdersInvertibleOn S
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E)) →
    IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' sq.w).app E)

end Stacks.EtaleCohomology

end
