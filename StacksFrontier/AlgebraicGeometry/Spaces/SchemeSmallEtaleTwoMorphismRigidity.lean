module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoMorphismRigidity

/-!
# Rigidity of 2-morphisms of the small étale ringed topos of a scheme

Let `g : U ⟶ V` be a morphism of schemes of the big fppf site of a scheme `S`.  Stacks 04IJ
says that the morphism of small étale ringed topoi `(g_{small}, g^♯)` that `g` induces has no
non-trivial 2-endomorphisms: a 2-morphism from it to itself, in the sense of Stacks 04IC, is
the identity.

This is the scheme case of Stacks 04KK, which is the same statement for a morphism of algebraic
spaces.  A scheme of the big fppf site of `S` is an algebraic space over `S` — its presheaf of
points, `AlgebraicGeometry.schemeSpace` — and the small étale site of that algebraic
space is, by definition, the site of étale morphisms of schemes into the scheme, carrying its
sheaf of global functions; `AlgebraicGeometry.Space.schemeChartToOver` is that presentation of
the site.  So `AlgebraicGeometry.Space.smallEtaleRingedToposHom` applied to
`AlgebraicGeometry.schemeSpaceMap g` *is* the morphism of ringed topoi of Stacks 04IJ,
and the lemma is Stacks 04KK read at that morphism.

## Main results

* `AlgebraicGeometry.Space.schemeSmallEtaleRingedToposHom_twoMorphism_eq_id`: **Stacks 04IJ** —
  every 2-endomorphism of the morphism of small étale ringed topoi induced by a morphism of
  schemes is the identity.
* `AlgebraicGeometry.Space.schemeSmallEtaleRingedToposHom_twoMorphismOfRingedTopoi_eq_id`: the
  same statement for a 2-morphism over the four-field
  `Stacks.Sheaves.RingedToposModules.RingedToposHom`.

## Implementation notes

Both of the `@[stacks 04IC]` structures of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposTwoMorphism.lean` are a notion of
2-morphism of the pair `(g_{small}, g^♯)`:
`AlgebraicGeometry.RingedToposHom.TwoMorphism` for the two-field
`AlgebraicGeometry.RingedToposHom`, which is the structure
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` is, and
`Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi` for the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom` it becomes under
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.  Stacks 04KK is stated over each of
them, so Stacks 04IJ is too, and the tag covers the pair.

## References

* [Stacks Project, Lemma 59.40.2 (Tag 04IJ)](https://stacks.math.columbia.edu/tag/04IJ)
* [Stacks Project, Tag 04KK](https://stacks.math.columbia.edu/tag/04KK)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : BigFppfOver B S hS} (g : U ⟶ V)

/-- **Stacks 04IJ.** A 2-morphism from the morphism of small étale ringed topoi induced by a
morphism of schemes to itself is the identity. -/
@[stacks 04IJ]
theorem schemeSmallEtaleRingedToposHom_twoMorphism_eq_id
    (t : AlgebraicGeometry.RingedToposHom.TwoMorphism.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g))
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g))) :
    t = AlgebraicGeometry.RingedToposHom.TwoMorphism.id
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g)) :=
  smallEtaleRingedToposHom_twoMorphism_eq_id B S hS (schemeSpaceMap g) t

/-- **Stacks 04IJ** for a 2-morphism over the four-field morphism of ringed topoi: a 2-morphism
from the morphism of small étale ringed topoi induced by a morphism of schemes to itself is the
identity. -/
@[stacks 04IJ]
theorem schemeSmallEtaleRingedToposHom_twoMorphismOfRingedTopoi_eq_id
    (t : Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g)).toRingedToposModulesHom
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g)).toRingedToposModulesHom) :
    t = Stacks.Sheaves.RingedToposModules.TwoMorphismOfRingedTopoi.id.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (schemeSpaceMap g)).toRingedToposModulesHom :=
  smallEtaleRingedToposHom_twoMorphismOfRingedTopoi_eq_id B S hS
    (schemeSpaceMap g) t

end AlgebraicGeometry.Space

end
