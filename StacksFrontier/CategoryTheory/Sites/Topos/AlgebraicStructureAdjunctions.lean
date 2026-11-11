module

public import StacksFrontier.CategoryTheory.Sites.Topos.StructureAdjunctionInstances
public import StacksFrontier.CategoryTheory.Sites.Topos.PointedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MonoidAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.LieAlgebraAdjunction
public import StacksFrontier.CategoryTheory.Sites.Presheaf.AlgebraicStructure.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of topoi preserve algebraic structure

Let `C`, `D` be sites and let `f = (f⁻¹, f_*)` be a morphism of topoi `Sh(C) → Sh(D)`. Stacks
00YV asserts that `f` gives an adjoint pair of functors `(f⁻¹, f_*)` on sheaves of algebraic
structures, compatible with taking the underlying sheaves of sets, for the following types of
algebraic structures: pointed sets, abelian groups, groups, monoids, rings, modules over a fixed
ring, and Lie algebras over a fixed field.

This file assembles the seven cases. For each type, with values in the corresponding category
`A` and forgetful functor `forget A`, `Stacks.Topos.StructureAdjunction f (forget A)` consists of
the two functors on `A`-valued sheaves, the adjunction between them, the identifications of their
underlying sheaves of sets with `f⁻¹`, resp. `f_*`, of the underlying sheaf of sets, and the
identification of the unit of the adjunction with the unit of `f⁻¹ ⊣ f_*` on sheaves of sets.

## Main definitions

* `Stacks.Topos.AlgebraicStructureAdjunctions`: the seven adjoint pairs.
* `Stacks.Topos.toposAlgebraicStructureAdjunctions`: **Stacks 00YV**, constructing them for any
  morphism of topoi between the topoi of sheaves of sets on two sites.
* `Stacks.Topos.AlgebraicStructureSheafification` and
  `Stacks.Topos.algebraicStructureSheafification`: the final assertion of Stacks 00YV, that the
  properties (α)–(ζ) of sheafification (`Stacks.Sites.SheafificationProperties`) hold on any site
  for each of the seven types.

## Implementation notes

* Rings in the Stacks project are commutative, so the case of rings is `CommRingCat`. The ring
  over which the modules are taken is an arbitrary (not necessarily commutative) ring `R`; nothing
  in the construction uses commutativity. Lie algebras over a field `k` are the tree's
  `LieAlgCat k` (Stacks 007N).
* The sites are small, with sheaves of sets in the universe of the site, as in the source: this
  is what makes the forgetful functors of the seven categories compatible with sheaves
  (`CategoryTheory.GrothendieckTopology.HasSheafCompose`) by instance search.
* The cases are constructed in the sibling files `StructureAdjunctionInstances.lean` (groups,
  abelian groups, rings, modules), `PointedAdjunction.lean`, `MonoidAdjunction.lean` and
  `LieAlgebraAdjunction.lean`, each from the set-level adjunction `f⁻¹ ⊣ f_*` and the fact that
  `f⁻¹` and `f_*` preserve finite products, which is the method of the source.

## References

* [Stacks 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Topos

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}

/-- The adjoint pairs `(f⁻¹, f_*)` attached to a morphism of topoi `f : Sh(C) → Sh(D)` on sheaves
of pointed sets, abelian groups, groups, monoids, (commutative) rings, `R`-modules and Lie
algebras over `k`, each compatible with taking the underlying sheaves of sets. -/
structure AlgebraicStructureAdjunctions
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) (R : Type u) [Ring R]
    (k : Type u) [Field k] where
  /-- The adjoint pair on sheaves of pointed sets. -/
  pointed : StructureAdjunction f (forget Pointed.{u})
  /-- The adjoint pair on sheaves of abelian groups. -/
  addCommGrp : StructureAdjunction f (forget AddCommGrpCat.{u})
  /-- The adjoint pair on sheaves of groups. -/
  grp : StructureAdjunction f (forget GrpCat.{u})
  /-- The adjoint pair on sheaves of monoids. -/
  mon : StructureAdjunction f (forget MonCat.{u})
  /-- The adjoint pair on sheaves of (commutative) rings. -/
  commRing : StructureAdjunction f (forget CommRingCat.{u})
  /-- The adjoint pair on sheaves of `R`-modules. -/
  module : StructureAdjunction f (forget (ModuleCat.{u} R))
  /-- The adjoint pair on sheaves of Lie algebras over `k`. -/
  lieAlgebra : StructureAdjunction f (forget (LieAlgCat.{u} k))

/-- **Stacks 00YV.** Let `C`, `D` be sites and let `f = (f⁻¹, f_*)` be a morphism of topoi
`Sh(C) → Sh(D)`. Then `f` gives an adjoint pair of functors `(f⁻¹, f_*)` on sheaves of algebraic
structures compatible with taking the underlying sheaves of sets, for pointed sets, abelian
groups, groups, monoids, rings, modules over a fixed ring `R` and Lie algebras over a fixed field
`k`. -/
@[stacks 00YV "The adjoint pairs for the seven listed types, each compatible with the underlying
  sheaves of sets: the underlying sheaf of sets of `f⁻¹ F`, resp. `f_* G`, is `f⁻¹`, resp. `f_*`,
  of the underlying sheaf of sets, and the unit is the unit of `f⁻¹ ⊣ f_*` on sheaves of sets.
  Rings are commutative rings; the module case is stated for an arbitrary ring `R`. The final
  assertion, (α)–(ζ) for each type, is `Stacks.Topos.algebraicStructureSheafification`."]
noncomputable def toposAlgebraicStructureAdjunctions
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) (R : Type u) [Ring R]
    (k : Type u) [Field k] : AlgebraicStructureAdjunctions f R k where
  pointed := pointedStructureAdjunction f
  addCommGrp := addCommGrpStructureAdjunction f
  grp := grpStructureAdjunction f
  mon := monStructureAdjunction f
  commRing := commRingStructureAdjunction f
  module := moduleStructureAdjunction f R
  lieAlgebra := lieAlgebraStructureAdjunction k f

/-- The properties (α)–(ζ) of sheafification of presheaves on the site `(C, J)`
(`Stacks.Sites.SheafificationProperties`) for presheaves of pointed sets, abelian groups, groups,
monoids, (commutative) rings, `R`-modules and Lie algebras over `k`. -/
structure AlgebraicStructureSheafification (J : GrothendieckTopology C) (R : Type u) [Ring R]
    (k : Type u) [Field k] where
  /-- (α)–(ζ) for presheaves of pointed sets. -/
  pointed : Sites.SheafificationProperties J Pointed.{u}
  /-- (α)–(ζ) for presheaves of abelian groups. -/
  addCommGrp : Sites.SheafificationProperties J AddCommGrpCat.{u}
  /-- (α)–(ζ) for presheaves of groups. -/
  grp : Sites.SheafificationProperties J GrpCat.{u}
  /-- (α)–(ζ) for presheaves of monoids. -/
  mon : Sites.SheafificationProperties J MonCat.{u}
  /-- (α)–(ζ) for presheaves of (commutative) rings. -/
  commRing : Sites.SheafificationProperties J CommRingCat.{u}
  /-- (α)–(ζ) for presheaves of `R`-modules. -/
  module : Sites.SheafificationProperties J (ModuleCat.{u} R)
  /-- (α)–(ζ) for presheaves of Lie algebras over `k`. -/
  lieAlgebra : Sites.SheafificationProperties J (LieAlgCat.{u} k)

/-- **Stacks 00YV, final assertion.** On any site, for each of the seven types of algebraic
structures of Stacks 00YV, the properties (α)–(ζ) of sheafification hold: a presheaf is a sheaf
if and only if its underlying presheaf of sets is; `P# = (P⁺)⁺` is a sheaf; sheafification
commutes with taking underlying presheaves of sets; `P ⟶ P#` is an isomorphism exactly when `P`
is a sheaf; sheafification is left adjoint to the inclusion; and sheafification is left exact. -/
@[stacks 00YV "The final assertion: (α)–(ζ) hold for each of the seven listed types, on any
  site (`Stacks.Sites.SheafificationProperties`). The adjoint pairs themselves are
  `Stacks.Topos.toposAlgebraicStructureAdjunctions`."]
noncomputable def algebraicStructureSheafification (J : GrothendieckTopology C) (R : Type u)
    [Ring R] (k : Type u) [Field k] : AlgebraicStructureSheafification J R k where
  pointed := Sites.SheafificationProperties.pointed J
  addCommGrp := Sites.SheafificationProperties.addCommGrpCat J
  grp := Sites.SheafificationProperties.grpCat J
  mon := Sites.SheafificationProperties.monCat J
  commRing := Sites.SheafificationProperties.commRingCat J
  module := Sites.SheafificationProperties.moduleCat J R
  lieAlgebra := Sites.SheafificationProperties.lieAlgCat J k

end Stacks.Topos
