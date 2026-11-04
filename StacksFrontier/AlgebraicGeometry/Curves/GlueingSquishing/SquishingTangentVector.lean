module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DualNumber
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.Skyscraper.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Squishing a tangent vector

Let `X'` and `X` be algebraic schemes over an algebraically closed field. This file says what
it means for a finite morphism `X' ⟶ X` to contract a closed embedded copy of the dual
numbers to one rational point, with the prescribed additive conductor quotient.

## Main definitions

* `AlgebraicGeometry.skyscraperAddSheaf` is the additive skyscraper sheaf at a point with
  fibre the base field.
* `AlgebraicGeometry.epsilonCoefficientAt` extracts the coefficient of `ε` from a section
  pulled back along a dual-number-valued point.
* `AlgebraicGeometry.IsSquishingTangentVector` says that `X` is obtained from `X'` by
  squishing the given tangent vector.

## Implementation notes

The short exact sequence is stated in the category of additive sheaves. Its first arrow is the
canonical structure-sheaf map to the pushforward. The second arrow is specified on each
neighbourhood of the contracted point by the coefficient of `ε` after pullback to the dual
numbers. Thus the existential sheaf map is constrained, rather than chosen arbitrarily.

An algebraic `k`-scheme is represented by an `Over (Spec k)` structure whose structure
morphism is quasi-compact and locally of finite type. The equations involving the structure
morphisms say that the tangent vector and its contracted point are defined over `k`.

## References

* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- The additive skyscraper sheaf at the contracted point, with fibre `k`. -/
noncomputable abbrev skyscraperAddSheaf {k : Type u} [Field k] (X : Scheme.{u})
    (x : X) : TopCat.Sheaf AddCommGrpCat.{u} X := by classical exact skyscraperSheaf x (.of k)

/-- The coefficient of `ε` after restricting a section along a dual-number-valued point. -/
noncomputable def epsilonCoefficientAt {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (s : Γ(X, U)) : k :=
  ((X.presheaf.germ U _ hθ ≫ Scheme.stalkClosedPointTo θ).hom s).snd

/-- A morphism of algebraic `k`-schemes squishes a tangent vector if that vector is a closed
immersion which is contracted to a rational point, the morphism is finite and an isomorphism
off that point, and taking the coefficient of `ε` gives the skyscraper quotient of the
pushforward structure sheaf. -/
@[stacks 0C1K "squishing_tangent_vector"]
def IsSquishingTangentVector {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X') : Prop :=
  let p : Spec (.of (DualNumber k)) := IsLocalRing.closedPoint (DualNumber k)
  f.IsOver (Spec (.of k)) ∧
    LocallyOfFiniteType (X' ↘ Spec (.of k)) ∧
    QuasiCompact (X' ↘ Spec (.of k)) ∧
    LocallyOfFiniteType (X ↘ Spec (.of k)) ∧
    QuasiCompact (X ↘ Spec (.of k)) ∧
    IsClosedImmersion θ ∧
    θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k ∧
    ∃ x : Spec (.of k) ⟶ X,
    x.IsOver (Spec (.of k)) ∧
    ∃ hcontract : θ ≫ f = dualNumberToBase k ≫ x,
    IsFinite f ∧
    (∃ U : X.Opens, (U : Set X) = {(θ ≫ f).base p}ᶜ ∧
      IsIso (f ∣_ U)) ∧
    letI : Preadditive (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      inferInstanceAs (Preadditive
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    letI : Limits.HasZeroMorphisms (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      Preadditive.preadditiveHasZeroMorphisms
    letI : ∀ (A B : TopCat.Sheaf AddCommGrpCat.{u} X), Zero (A ⟶ B) :=
      Limits.HasZeroMorphisms.zero
    let φ :=
      (sheafCompose (Opens.grothendieckTopology X)
        (forget₂ RingCat AddCommGrpCat)).map (Scheme.Hom.toRingCatSheafHom f)
    ∃ (ψ : (sheafCompose (Opens.grothendieckTopology X)
        (forget₂ RingCat AddCommGrpCat)).obj
          (((Opens.map f.base).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology X')).obj X'.ringCatSheaf) ⟶
          skyscraperAddSheaf (k := k) X ((θ ≫ f).base p))
      (hzero : φ ≫ ψ = (Limits.HasZeroMorphisms.zero _ _).zero),
      (ShortComplex.mk φ ψ hzero).ShortExact ∧
        ∀ (U : X.Opens) (hx : (θ ≫ f).base p ∈ U)
          (s : Γ(X', f ⁻¹ᵁ U)),
          ψ.hom.app (op U) s =
            (show ((skyscraperAddSheaf (k := k) X
              ((θ ≫ f).base p)).obj.obj (op U)) from
              (by
                simpa only [skyscraperAddSheaf, skyscraperSheaf,
                  skyscraperPresheaf, ite_eq_left hx] using
                  (epsilonCoefficientAt θ (f ⁻¹ᵁ U) (by exact hx) s)))

end AlgebraicGeometry
