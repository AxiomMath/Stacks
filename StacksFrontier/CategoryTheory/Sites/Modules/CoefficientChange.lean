module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Change of coefficient rings on a fixed site as a morphism of ringed topoi

A map `α : O ⟶ O'` of sheaves of commutative rings on a site `(C, J)` is a morphism of ringed
topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose underlying morphism of sites is the identity functor of
`C`. This file builds it as an `AlgebraicGeometry.RingedToposSiteHom`, the presentation of a
morphism of ringed topoi by a continuous functor of the underlying sites, and identifies the
pullback of sheaves of modules along it with extension of scalars along `α`.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.coefficientChange`: the morphism of ringed topoi
  attached to a map of coefficient sheaves on a fixed site.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.coefficientChange_fSharpRing`: its structure map, read
  as a map of sheaves of not necessarily commutative rings, is `α` with commutativity
  forgotten.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange`: the pullback of
  sheaves of modules along it is extension of scalars along `α`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.RingedToposSiteHom

/-- **Change of coefficient rings on a fixed site.** A map `α : O ⟶ O'` of sheaves of
commutative rings on `(C, J)` is a morphism of ringed topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose
underlying morphism of sites is the identity functor of `C` and whose structure map is `α`. -/
def coefficientChange {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O') :
    RingedToposSiteHom ({ C := C, J := J, O := O' } : RingedTopos.{v, u, w})
      ({ C := C, J := J, O := O } : RingedTopos.{v, u, w}) where
  u := 𝟭 C
  fSharp := α

/-- The underlying morphism of sites of a change of coefficient rings is the identity. -/
@[simp]
theorem coefficientChange_u {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O') :
    (coefficientChange.{w, v, u} J α).u = 𝟭 C :=
  rfl

/-- The structure map of a change of coefficient rings is the given map of coefficient
sheaves. -/
@[simp]
theorem coefficientChange_fSharp {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O') :
    (coefficientChange.{w, v, u} J α).fSharp = α :=
  rfl

section Rings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}}

/-- The structure map of a change of coefficient rings, read as a map of sheaves of not
necessarily commutative rings, is `α` with commutativity forgotten. -/
theorem coefficientChange_fSharpRing (α : O ⟶ O') :
    (coefficientChange.{w, v, u} J α).fSharpRing =
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α :=
  rfl

end Rings

section Pullback

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O O' : Sheaf J CommRingCat.{w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The pullback of sheaves of modules along a change of coefficient rings is extension of
scalars along its structure map. -/
theorem pullbackTopos_coefficientChange (α : O ⟶ O') :
    (coefficientChange.{w, w, w} J α).pullbackTopos =
      Stacks.Sheaves.ModuleAdjunction.extendScalars.{w}
        ((coefficientChange.{w, w, w} J α).fSharpRing) :=
  rfl

end Pullback

end AlgebraicGeometry.RingedToposSiteHom

end
