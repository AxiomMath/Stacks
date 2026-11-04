module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedMixedTensor

/-!
# The auxiliary topos of a change of coefficient rings

A map `γ : O ⟶ O'` of sheaves of commutative rings on a fixed site `(C, J)` presents a morphism
of ringed topoi `f : (Sh(J), O') ⟶ (Sh(J), O)` whose underlying continuous functor is the
identity of `C`. The factorization of Stacks 0G6R through an auxiliary topos inserts
`f⁻¹O = ((𝟭 C).sheafPullback CommRingCat J J).obj O` between the two; for a coefficient change
that sheaf is `O` itself, and this file supplies that identification.

## Main definitions

* `Stacks.Cohomology.CoefficientChange.invRingIso`: `f⁻¹O ≅ O` for a change of coefficient
  rings.
* `Stacks.Cohomology.CoefficientChange.invRingIsoRing`: the same after forgetting
  commutativity, which is the form restriction of scalars consumes.

## Main results

* `Stacks.Cohomology.CoefficientChange.auxHomG_fSharp`: the structure map of the geometric half
  of the factorization is the inverse of `invRingIso`.
* `Stacks.Cohomology.CoefficientChange.invRingIso_inv_comp_auxHomH_fSharp` and
  `Stacks.Cohomology.CoefficientChange.invRingIsoRing_inv_comp_structureMapOfInvRing`: the
  structure map of the ring-theoretic half is, through that identification, the coefficient
  change itself.

## Implementation notes

The inverse image along the identity functor of a site is the identity functor of the category
of sheaves, `CategoryTheory.Functor.sheafPullbackIdIso`, and the identification is that
isomorphism at `O`.

The two structure maps of the factorization are the unit of the inverse-image/direct-image
adjunction at `O` and the adjoint of `γ`. The uniqueness of left adjoints is set up so that
the unit of the chosen inverse image, followed by the comparison with the identity functor, is
the unit of the identity adjunction; that identity is the first result above, and the second is
the defining property of the adjoint read through it.

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.CoefficientChange

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {O O' : Sheaf J CommRingCat.{u}}

/-- **The inverse image of the structure sheaf along a change of coefficient rings is that
sheaf itself.** The underlying continuous functor of a coefficient change is the identity of
the site, and the inverse image along the identity functor is the identity functor. -/
def invRingIso (γ : O ⟶ O') :
    StacksPullbackFactorization.invRing
        (RingedToposSiteHom.coefficientChange.{u, u, u} J γ) ≅ O :=
  (Functor.sheafPullbackIdIso CommRingCat.{u} J).app O

/-- **The structure map of the geometric half of the factorization of a coefficient change is
the inverse of `invRingIso`.** That map is the unit of the inverse-image/direct-image adjunction
at `O`, and the unit of the identity adjunction is the identity, so the two are matched by the
uniqueness of left adjoints. -/
theorem auxHomG_fSharp (γ : O ⟶ O') :
    (StacksPullbackFactorization.auxHomG
        (RingedToposSiteHom.coefficientChange.{u, u, u} J γ)).fSharp = (invRingIso γ).inv :=
  (Iso.comp_hom_eq_id (invRingIso γ)).1
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((𝟭 C).sheafAdjunctionContinuous CommRingCat.{u} J J) Adjunction.id O)

/-- **The structure map of the ring-theoretic half of the factorization of a coefficient change
is the coefficient change itself**, read through `invRingIso`: it is the adjoint of `γ`, and the
unit of the adjunction at `O` is `(invRingIso γ).inv`. -/
theorem invRingIso_inv_comp_auxHomH_fSharp (γ : O ⟶ O') :
    (invRingIso γ).inv ≫ (StacksPullbackFactorization.auxHomH
        (RingedToposSiteHom.coefficientChange.{u, u, u} J γ)).fSharp = γ := by
  rw [← auxHomG_fSharp γ]
  exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

section Rings

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- `invRingIso` after forgetting commutativity, which is the form restriction of scalars
consumes: the structure sheaf of the auxiliary topos of a coefficient change is `O`. -/
def invRingIsoRing (γ : O ⟶ O') :
    (Stacks.SheafOfModules.Tensor.ringSheaf (StacksPullbackFactorization.auxTopos
        (RingedToposSiteHom.coefficientChange.{u, u, u} J γ)).O) ≅
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.Cohomology.ringedTopos J O).O) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso (invRingIso γ)

/-- **The ring-theoretic half of the factorization of a coefficient change is the coefficient
change itself**, read through `invRingIsoRing`. This is
`invRingIso_inv_comp_auxHomH_fSharp` after forgetting commutativity, which it survives
objectwise because forgetting commutativity commutes with the direct image on the nose. -/
theorem invRingIsoRing_inv_comp_structureMapOfInvRing (γ : O ⟶ O') :
    (invRingIsoRing γ).inv ≫ Stacks.Cohomology.MixedDerivedTensor.structureMapOfInvRing
        (RingedToposSiteHom.coefficientChange.{u, u, u} J γ) =
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map γ :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun U => congrArg (fun (t : O ⟶ _) =>
    (forget₂ CommRingCat.{u} RingCat.{u}).map (t.hom.app U)) (invRingIso_inv_comp_auxHomH_fSharp γ)

end Rings

end Stacks.Cohomology.CoefficientChange

end
