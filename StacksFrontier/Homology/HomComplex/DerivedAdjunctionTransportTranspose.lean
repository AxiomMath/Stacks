module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTransport

/-!
# The transported transpose at arbitrary objects

`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj` evaluates
the inverse of a conjugated tensor--Hom transpose, but only when all three of its objects are
literally `e.functor.obj` of objects of the source category.  That hypothesis is not met where the
identity is wanted: the objects there are values of a derived functor, and no presentation of them
as images under `e.functor` is available.

This module removes the hypothesis.  At arbitrary objects the conjugated transpose cannot be a
morphism of the source category, so the statement is instead about its image under `e.inverse`,
followed by the inverse unit of the equivalence: that composite -- the counit of the *other*
adjunction of `e` applied to the conjugated transpose -- is the original transpose of the image of
the morphism under `e.inverse`, prefixed by the unit at the tensor product.  The content is one
naturality square of the inverse unit and one triangle identity, and the whole statement is
exactly the first half of the definition of
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv` read backwards.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_apply` -- **the
  generalization.**  The conjugated transpose of `g`, restricted along `e.inverse` and followed by
  the inverse unit, is the unconjugated transpose of `e.inverse.map g` prefixed by the unit.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_apply_of_counit_values` --
  the same with the two components of the unit isomorphism taken as data, so that an instantiation
  may supply them in whatever spelling the goal has them.  This is the form a consumer uses: the
  equivalence the tensor--Hom bundle is conjugated along and the one the change-of-rings
  isomorphism is stated with are opposite to each other, so the two units appear there as counits.
* `CategoryTheory.Functor.comp_map_comp_eq_of_eq` -- substitution of one factor occurring under a
  functor in the middle of a composite, as an equation of the whole composite.  It exists so that
  the identity above can be applied by `refine` inside a goal no rewrite reaches.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory

namespace StacksDraft.DerivedHom

universe u₁ u₂ v₁ v₂ w₁ w₂

namespace DerivedHomAdjunction

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
  (d : DerivedHomAdjunction R)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- **The transported transpose at arbitrary objects.**

`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj` needs all
three objects to be images under `e.functor`.  Here they are arbitrary, and what is evaluated is
the image under `e.inverse` of the conjugated transpose followed by the inverse unit of `e` --
equivalently, the transpose of the conjugated transpose under the adjunction `e.inverse ⊣
e.functor`.  It is the original transpose of `e.inverse.map g`, prefixed by the unit of `e` at the
tensor product.

Only the definition of `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv`, one
naturality square of the inverse unit and the triangle identity
`CategoryTheory.Equivalence.unit_inverse_comp` enter; nothing is assumed of `d`. -/
theorem transportHomEquiv_symm_apply (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (g : (d.transportTensor e).obj (K, L) ⟶ M) :
    e.inverse.map ((d.transportHomEquiv e K L M).symm g) ≫
        e.unitIso.inv.app
          (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)) =
      (d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).symm
        (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)) ≫
          e.inverse.map g) := by
  set b := (d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).symm
    (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)) ≫
      e.inverse.map g) with hb
  have hval : (d.transportHomEquiv e K L M).symm g =
      e.counitIso.inv.app K ≫ e.functor.map b := by
    simp only [transportHomEquiv, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
      Adjunction.homAddEquiv_apply, Adjunction.homEquiv_unit, hb,
      Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_unit]
    rfl
  have hnat : e.inverse.map (e.functor.map b) ≫
      e.unitIso.inv.app
        (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)) =
      e.unitIso.inv.app (e.inverse.obj K) ≫ b := e.unitIso.inv.naturality b
  rw [hval, e.inverse.map_comp, Category.assoc, hnat]
  simp

/-- **The transported transpose at arbitrary objects, with the two units as data.**

`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_apply` with the two components
of the unit isomorphism of `e` given as arguments together with their values, so that an
instantiation computes its statement from the data rather than requiring the goal to spell them as
components of `e.unitIso`.

That is what a consumer needs.  The tensor--Hom bundle of [stacks 0A63] is conjugated along
`StacksDraft.DerivedHom.derivedScalarEquivalence`, while [stacks 0E1W] is stated with the opposite
equivalence `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`; the unit of the one
is the inverse counit of the other, so in a goal written in the vocabulary of [stacks 0E1W] the two
morphisms below occur as counit components and no rewrite reaches them. -/
theorem transportHomEquiv_symm_apply_of_counit_values
    (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (g : (d.transportTensor e).obj (K, L) ⟶ M)
    (c₁ : e.inverse.obj (e.functor.obj
        (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))) ⟶
      d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))
    (c₂ : d.tensor.obj (e.inverse.obj K, e.inverse.obj L) ⟶
      e.inverse.obj (e.functor.obj (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))))
    (hc₁ : e.unitIso.inv.app
      (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)) = c₁)
    (hc₂ : e.unitIso.hom.app
      (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)) = c₂) :
    e.inverse.map ((d.transportHomEquiv e K L M).symm g) ≫ c₁ =
      (d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).symm
        (c₂ ≫ e.inverse.map g) := by
  subst hc₁
  subst hc₂
  exact transportHomEquiv_symm_apply d e K L M g

end DerivedHomAdjunction

end StacksDraft.DerivedHom

namespace CategoryTheory.Functor

/-- **A factor under a functor in the middle of a composite, substituted.**

If `m` and `m'` agree then a composite `(a ≫ b ≫ V.map m) ≫ p` may be read with `m'` in place of
`m`.  Stated over variable categories with the surrounding factors as arguments, so that an
instantiation computes its statement from the data: it is used where the goal is not type-correct
at `implicit` transparency, and there a rewrite of `m` reports that it cannot find a pattern that
is visibly present, while `refine` unifies at default transparency and succeeds.

The bracketing is the one
`Stacks.DerivedHom.BaseChange.functor_map_comp_scalarRestrictionIso_hom_app_comp` leaves behind:
a morphism out of the source category, the transported restriction comparison, the restriction of
the factor to be substituted, and then the tail. -/
public theorem comp_map_comp_eq_of_eq {C D : Type*} [Category* C] [Category* D] (V : D ⥤ C)
    {X₀ X₁ Y : C} {Z W : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ V.obj Z) {m m' : Z ⟶ W}
    (p : V.obj W ⟶ Y) (h : m = m') :
    (a ≫ b ≫ V.map m) ≫ p = (a ≫ b ≫ V.map m') ≫ p :=
  congrArg (fun z => (a ≫ b ≫ V.map z) ≫ p) h

end CategoryTheory.Functor

end
