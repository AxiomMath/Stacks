module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-!
# The kernel of the counit at a point of a topos

Let `p` be a point of a topos `Sh(C, J)` and let `A` be an abelian group. The counit of the
adjunction `p⁻¹ ⊣ p_*` gives a morphism of abelian groups `p⁻¹p_*A ⟶ A`, and this file names
its kernel. It is the group written `Iₚ(A)` in the discussion preceding Stacks 05V7, which is
the complement to `A` in `p⁻¹p_*A`: the counit is a split surjection
(`PointOfTopos.isSplitEpi_counit_app`), so `p⁻¹p_*A ≅ A ⊕ Iₚ(A)`.

## Main definitions

* `PointOfTopos.kernelComplementOfCounit`: the kernel `Iₚ(A)` of the counit `p⁻¹p_*A ⟶ A`.

## Main results

No results are proved here; this file only names the object.

## Implementation notes

Abelian groups and abelian sheaves are represented by commutative group objects, so that the
inverse-image and direct-image functors of the point act on them through their
finite-product-preserving structure; the counit used in the definition is therefore the
canonical counit induced by the given adjunction, rather than a separately chosen morphism.
The kernel itself is taken in `AddCommGrpCat`, where Mathlib has the limit, and transported
back to commutative group objects of `Type w` along `commGrpTypeEquivalenceCommGrp`.

The two monoidal instances on `Sheaf J (Type w)` are local: they come from finite products,
which is what makes a commutative group object the same thing as a sheaf of abelian groups,
and declaring them globally would fix a monoidal structure on every sheaf topos.

## References

* Stacks Project, Section 18, the definition preceding
  [Tag 05V7](https://stacks.math.columbia.edu/tag/05V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace PointOfTopos

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The cartesian monoidal structure on sheaves of types given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The symmetric braiding on sheaves of types induced by the cartesian monoidal structure. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

/-- For a point `p` of a topos and an abelian group `A`, the group `Iₚ(A)` is the kernel of
the counit `p⁻¹p_*A ⟶ A` on abelian group objects. -/
noncomputable def kernelComplementOfCounit (p : PointOfTopos.{w, v, u} J)
    (A : CommGrp (Type w)) : CommGrp (Type w) := by
  let : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
  let : p.inverseImage.Braided := .ofChosenFiniteProducts _
  let : PreservesFiniteLimits p.pushforward := p.preservesFiniteLimits_pushforward
  let : p.pushforward.Braided := .ofChosenFiniteProducts _
  let adj := p.adj.mapCommGrp
  exact commGrpTypeEquivalenceCommGrp.inverse.obj <|
    AddCommGrpCat.toCommGrp.obj <|
      kernel <| CommGrpCat.toAddCommGrp.map <|
        commGrpTypeEquivalenceCommGrp.functor.map (adj.counit.app A)

end PointOfTopos
