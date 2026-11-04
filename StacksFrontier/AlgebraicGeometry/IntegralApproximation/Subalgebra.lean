module

public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Subalgebras of an integral algebra sheaf are finite

Let `X` be a scheme and let `A` be a sheaf of algebras over its structure sheaf which is
integral, in the sense that its structural ring map is integral over every affine open.  This
file proves that every subalgebra of `A` which is of finite type is already finite:

* `Stacks.AlgebraicGeometry.IntegralSubalgebras.isFinite_of_mono`.

In particular every object of the category
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.FiniteTypeSubalgebra A` of finite type
quasi-coherent subalgebras of `A` is finite, so the diagram indexed by that category which
[Stacks, Tag 05JT] presents `A` as the colimit of consists of *finite* quasi-coherent
algebras as soon as `A` is integral.  That is the step by which [Stacks, Tag 0817] is deduced
from tags 05JT and 086N.

## The route

A subalgebra of `A` is a monomorphism `i : B ⟶ A` in the category of algebra sheaves, and the
content of the file is that integrality descends along such an `i`.  Integrality is a condition
on the sections over an affine open `U`, so what has to be supplied is that the component
`B(U) ⟶ A(U)` of a monomorphism of algebra sheaves is *injective*.  That is
`Stacks.AlgebraicGeometry.IntegralSubalgebras.injective_app_of_mono`, and it is proved by
composing three functors which each preserve monomorphisms because each preserves pullbacks:

* `CategoryTheory.Under.forget` on the structure sheaf, which has the left adjoint
  `CategoryTheory.Under.costar` as soon as the ambient category has binary coproducts;
* `TopCat.Sheaf.forget`, which is `CategoryTheory.sheafToPresheaf` and is a right adjoint
  because sheafification of `CommRingCat`-valued presheaves exists;
* evaluation at `U`, where a monomorphism of commutative rings is an injective ring map.

With injectivity in hand, `RingHom.IsIntegral.tower_bot` shows that `Γ(X, U) ⟶ B(U)` is
integral, and `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFinite_of_isFiniteType` upgrades
finite type to finite.

The binary coproducts needed by the first step are supplied as
`Stacks.AlgebraicGeometry.IntegralSubalgebras.hasBinaryCoproducts`, the coproduct of two
sheaves of commutative rings on a topological space.  This is an instance that Mathlib already
implies, but whose search does not terminate within the default instance budget: the
`CategoryTheory.Sheaf` colimit construction has to be found through the `def`-wrapped
`TopCat.Sheaf`, and declaring the instance at that spelling is what makes it available.

## Main results

* `Stacks.AlgebraicGeometry.IntegralSubalgebras.injective_app_of_mono`: the sections of a
  monomorphism of algebra sheaves over any open are injective.
* `Stacks.AlgebraicGeometry.IntegralSubalgebras.isIntegral_of_mono`: integrality of an algebra
  sheaf descends to any subalgebra.
* `Stacks.AlgebraicGeometry.IntegralSubalgebras.isFinite_of_mono`: a finite type subalgebra of
  an integral algebra sheaf is finite.
* `Stacks.AlgebraicGeometry.IntegralSubalgebras.isFinite_subobject` and
  `Stacks.AlgebraicGeometry.IntegralSubalgebras.isFinite_finiteTypeSubalgebraDiagram_obj`: the
  same statement for the subobjects of `A` and for the objects of the diagram of tag 05JT.

## Implementation notes

`AlgebraicGeometry.Scheme.sheaf` lands in `TopCat.Sheaf`, which is a `def` and not an
abbreviation for `CategoryTheory.Sheaf`.  Instance search therefore does not see through it, and
the two places where that matters are handled by naming the term rather than searching for it:
the coproducts instance is stated at the `TopCat.Sheaf` spelling, and the limit-preservation of
`TopCat.Sheaf.forget` is obtained from that of `CategoryTheory.sheafToPresheaf` with
`inferInstanceAs`, which checks the identification at default transparency.

Nothing in this file uses quasi-compactness, quasi-separatedness, quasi-coherence, or any
hypothesis on `X` beyond its being a scheme; integrality of `A` and a monomorphism into it are
the whole input.

## What is not done

This does not prove any part of [Stacks, Tag 0817].  What is missing for that is, in order:

* the directedness assertion of [Stacks, Tag 05JT], that the finite type quasi-coherent
  subalgebras of a quasi-coherent algebra are directed and cover it.  Its blocker is recorded
  in `StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebra/Coproducts.lean`: the join in the
  subobject lattice needs `CategoryTheory.Limits.HasImages` on the category of algebra sheaves,
  and no construction of those exists here or in Mathlib at this pin;
* the colimit assertion of tag 05JT, that the resulting cocone is colimiting;
* [Stacks, Tag 086N], that a finite quasi-coherent algebra is a directed colimit of finite and
  finitely presented ones;
* the combination of the two directed systems into the single one that tag 0817 asserts.

This file also does not transport `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` along an
isomorphism of algebra sheaves, which every route to tag 05JT needs and which remains absent.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.IntegralSubalgebras

variable {X : Scheme.{u}}

/-- **Binary coproducts of sheaves of commutative rings on a topological space.**  The
coproduct is the sheafification of the pointwise coproduct, which is Mathlib's construction of
colimits in a category of sheaves; the instance is declared here at the `TopCat.Sheaf` spelling
because `TopCat.Sheaf` is a `def` and instance search does not unfold it.

This is what gives `CategoryTheory.Under.forget` on the structure sheaf of a scheme a left
adjoint, and hence makes it preserve monomorphisms. -/
instance hasBinaryCoproducts (T : TopCat.{u}) :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} T) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- Forgetting the structure morphism of an algebra sheaf preserves monomorphisms: it is a right
adjoint, its left adjoint being `CategoryTheory.Under.costar`, which exists because sheaves of
commutative rings on a space have binary coproducts. -/
theorem underForget_preservesMonomorphisms (X : Scheme.{u}) :
    (Under.forget X.sheaf).PreservesMonomorphisms :=
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- Passing from a sheaf of commutative rings to its underlying presheaf preserves
monomorphisms: it is `CategoryTheory.sheafToPresheaf`, which is a right adjoint because
sheafification of `CommRingCat`-valued presheaves exists. -/
theorem sheafForget_preservesMonomorphisms (T : TopCat.{u}) :
    (TopCat.Sheaf.forget CommRingCat.{u} T).PreservesMonomorphisms :=
  let : PreservesLimitsOfShape WalkingCospan (TopCat.Sheaf.forget CommRingCat.{u} T) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (sheafToPresheaf _ _))
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **A monomorphism of algebra sheaves is injective on sections.**  Over any open `U` of `X`
the component `B(U) ⟶ A(U)` of a monomorphism `B ⟶ A` of sheaves of algebras is an injective
ring map. -/
theorem injective_app_of_mono {A B : AlgebraSheaf X} (i : B ⟶ A) [Mono i] (U : X.Opens) :
    Function.Injective (i.right.hom.app (op U)).hom := by
  have := underForget_preservesMonomorphisms X
  have : Mono i.right := (Under.forget X.sheaf).map_mono i
  have := sheafForget_preservesMonomorphisms (T := (X : TopCat))
  have : Mono i.right.hom :=
    (TopCat.Sheaf.forget CommRingCat.{u} (X : TopCat)).map_mono i.right
  have : Mono (i.right.hom.app (op U)) := inferInstance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The structural ring map of `A` over an open `U` factors through that of a subalgebra. -/
theorem app_eq_comp_of_hom {A B : AlgebraSheaf X} (i : B ⟶ A) (U : X.Opens) :
    (A.hom.hom.app (op U)).hom =
      (i.right.hom.app (op U)).hom.comp (B.hom.hom.app (op U)).hom := by
  rw [← Under.w i]; rfl

/-- **Integrality descends to a subalgebra.**  If `A` is an integral algebra sheaf and
`i : B ⟶ A` is a monomorphism of algebra sheaves, then `B` is integral.

Over an affine open `U` the map `Γ(X, U) ⟶ A(U)` is integral and factors as
`Γ(X, U) ⟶ B(U) ⟶ A(U)` with the second map injective, so the first is integral. -/
theorem isIntegral_of_mono {A B : AlgebraSheaf X} (hA : A.IsIntegral) (i : B ⟶ A) [Mono i] :
    B.IsIntegral := by
  intro U hU
  refine RingHom.IsIntegral.tower_bot (B.hom.hom.app (op U)).hom (i.right.hom.app (op U)).hom
    (injective_app_of_mono i U) ?_
  rw [← app_eq_comp_of_hom i U]
  exact hA U hU

/-- **A finite type subalgebra of an integral algebra sheaf is finite.**  This is the sheaf-level
form of [Stacks, Tag 02JJ] for subalgebras, and the step by which the finite type approximations
of [Stacks, Tag 05JT] become the finite ones that [Stacks, Tag 0817] asks for. -/
theorem isFinite_of_mono {A B : AlgebraSheaf X} (hA : A.IsIntegral) (i : B ⟶ A) [Mono i]
    (hB : B.IsFiniteType) : B.IsFinite :=
  (isIntegral_of_mono hA i).isFinite_of_isFiniteType hB

/-- For an integral algebra sheaf, a subalgebra is finite exactly when it is of finite type. -/
theorem isFiniteType_iff_isFinite_of_mono {A B : AlgebraSheaf X} (hA : A.IsIntegral)
    (i : B ⟶ A) [Mono i] : B.IsFiniteType ↔ B.IsFinite :=
  ⟨isFinite_of_mono hA i, Stacks.RelativeSpec.AlgebraSheaf.IsFinite.isFiniteType⟩

/-- A subobject of an integral algebra sheaf whose underlying algebra sheaf is of finite type
has finite underlying algebra sheaf. -/
theorem isFinite_subobject {A : AlgebraSheaf X} (hA : A.IsIntegral) (B : Subobject A)
    (hB : (B : AlgebraSheaf X).IsFiniteType) : (B : AlgebraSheaf X).IsFinite :=
  isFinite_of_mono hA B.arrow hB

/-- **Every object of the diagram of [Stacks, Tag 05JT] is finite when the algebra is
integral.**  Tag 05JT presents a quasi-coherent algebra `A` as the colimit of the diagram of its
finite type quasi-coherent subalgebras; when `A` is integral every algebra sheaf occurring in
that diagram is finite, which is the finiteness in the conclusion of [Stacks, Tag 0817]. -/
theorem isFinite_finiteTypeSubalgebraDiagram_obj {A : AlgebraSheaf X} (hA : A.IsIntegral)
    (B : FiniteTypeSubalgebras.FiniteTypeSubalgebra A) :
    ((FiniteTypeSubalgebras.finiteTypeSubalgebraDiagram A).obj B).IsFinite :=
  isFinite_subobject hA B.obj B.property.2

/-- The objects of the diagram of [Stacks, Tag 05JT] are quasi-coherent, finite, and of finite
type when the algebra is integral.  Compared with the conclusion of [Stacks, Tag 0817] the
missing condition is finite presentation, which is what [Stacks, Tag 086N] supplies and which no
subalgebra of `A` need satisfy. -/
theorem isQuasicoherent_and_isFinite_finiteTypeSubalgebraDiagram_obj {A : AlgebraSheaf X}
    (hA : A.IsIntegral) (B : FiniteTypeSubalgebras.FiniteTypeSubalgebra A) :
    ((FiniteTypeSubalgebras.finiteTypeSubalgebraDiagram A).obj B).IsQuasicoherent ∧
      ((FiniteTypeSubalgebras.finiteTypeSubalgebraDiagram A).obj B).IsFinite ∧
      ((FiniteTypeSubalgebras.finiteTypeSubalgebraDiagram A).obj B).IsFiniteType :=
  ⟨B.property.1, isFinite_finiteTypeSubalgebraDiagram_obj hA B, B.property.2⟩

end Stacks.AlgebraicGeometry.IntegralSubalgebras
