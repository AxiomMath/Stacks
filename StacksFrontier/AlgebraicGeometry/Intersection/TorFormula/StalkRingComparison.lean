module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafStalk
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The two stalk rings of a scheme, and transport of length between them

The local ring of a scheme at a point is computed as a filtered colimit, and that colimit can be
taken in commutative rings or in rings. The two answers are the `CommRingCat`-valued stalk
`X.presheaf.stalk x`, which is the ring the Chow-homology multiplicities and the Tor-formula
intersection multiplicity are phrased over, and the `RingCat`-valued stalk of the underlying
sheaf of rings, which is the ring `AlgebraicGeometry.Scheme.Modules.stalkFunctor` takes its
modules over. They are isomorphic but not definitionally equal: they are colimits in two
different categories, identified only because the forgetful functor preserves filtered colimits.

This file names that isomorphism for a scheme and records what crosses it. What has to cross,
for the intersection-theoretic applications, is not a functor but a *length*: both
`Stacks.Chow.sheafMultiplicity` and `Ideal.localIntersectionMultiplicity` are built from
`Module.length`, and the length of a module is unchanged by a semilinear isomorphism, because
such an isomorphism induces an isomorphism of submodule lattices.

## Main definitions

* `AlgebraicGeometry.TorFormula.stalkRingEquiv` — the ring isomorphism between the two stalks.

## Main results

* `AlgebraicGeometry.TorFormula.ringSheaf_obj_eq` — the sheaf of rings whose stalk the module
  stalk functor uses is the structure sheaf composed with the forgetful functor. This is the
  identification that makes `stalkRingEquiv` land on the two spellings at issue, and it holds by
  `rfl`; it is stated once here so that later proofs do not rediscover it.
* `AlgebraicGeometry.TorFormula.stalkRingEquiv_germ` — the isomorphism matches the germ maps.
* `Module.length_eq_of_semilinearEquiv` — length is invariant under a semilinear isomorphism.
* `AlgebraicGeometry.TorFormula.length_eq_of_stalkSemilinearEquiv` — the specialisation along
  `stalkRingEquiv`: a module over one stalk ring and a module over the other that correspond
  under a semilinear isomorphism have the same length.

## Implementation notes

`Module.length_eq_of_semilinearEquiv` is the semilinear analogue of Mathlib's
`LinearEquiv.length_eq` and is proved the same way, from
`AlgebraicGeometry.Submodule.orderIsoMapComap` and the invariance of Krull dimension under an
order isomorphism. The `RingHomSurjective` and `RingHomInvPair` instances it needs are the ones
a `RingEquiv` supplies.

No transport of the `Tor` functor along the isomorphism is provided, and none is needed: the
consumers take lengths of `Tor` modules, so the length lemma above suffices. Transporting the
functor would mean building an equivalence `ModuleCat R ≌ ModuleCat S` and showing it commutes
with the derived tensor product, which is a large construction with no use here.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB), the stalk of a sheaf of
  modules and its module structure over the stalk of the structure sheaf.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- **Length is invariant under a semilinear isomorphism.** A semilinear isomorphism induces an
isomorphism of the two submodule lattices, and the length of a module is the Krull dimension of
its submodule lattice. This is the semilinear analogue of `LinearEquiv.length_eq`. -/
theorem Module.length_eq_of_semilinearEquiv {R S : Type*} [Ring R] [Ring S]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    {σ : R →+* S} [RingHomSurjective σ] {τ : S →+* R}
    [RingHomInvPair σ τ] [RingHomInvPair τ σ] (e : M ≃ₛₗ[σ] N) :
    Module.length R M = Module.length S N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

namespace AlgebraicGeometry.TorFormula

/-- The sheaf of rings over which the module stalk functor of a scheme works is the structure
sheaf read in rings. This holds by definition, and is what makes `stalkRingEquiv` below a
statement about the two stalk rings actually in use. -/
theorem ringSheaf_obj_eq (X : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj
      = X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u} :=
  rfl

/-- **The two stalk rings of a scheme at a point are isomorphic.** On the left is the
`RingCat`-valued stalk of the structure sheaf read in rings, the ring over which the module
stalk functor takes its values; on the right the `CommRingCat`-valued stalk `𝒪_{X, x}`. The
isomorphism comes from the forgetful functor preserving the filtered colimit computing the
stalk. -/
def stalkRingEquiv (X : Scheme.{u}) (x : X) :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x) ≃+*
      ToType (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- The two stalk rings are inverse to each other, in the form semilinear maps ask for. -/
instance ringHomInvPair_stalkRingEquiv (X : Scheme.{u}) (x : X) :
    RingHomInvPair (stalkRingEquiv X x).toRingHom (stalkRingEquiv X x).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (stalkRingEquiv X x)

/-- The companion of `ringHomInvPair_stalkRingEquiv` in the other order. -/
instance ringHomInvPair_stalkRingEquiv_symm (X : Scheme.{u}) (x : X) :
    RingHomInvPair (stalkRingEquiv X x).symm.toRingHom (stalkRingEquiv X x).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (stalkRingEquiv X x)

/-- The isomorphism of stalk rings matches the germ maps: the germ of a section computed in
rings goes to the germ computed in commutative rings. -/
theorem stalkRingEquiv_germ (X : Scheme.{u}) (x : X) (U : Opens X) (hx : x ∈ U)
    (r : X.presheaf.obj (op U)) :
    stalkRingEquiv X x (TopCat.Presheaf.germ (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj U x hx r)
      = X.presheaf.germ U x hx r :=
  SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hx r

/-- **Transport of length across the two stalk rings.** A module over the `RingCat`-valued stalk
and a module over `𝒪_{X, x}` that correspond under a semilinear isomorphism along
`stalkRingEquiv` have the same length. This is what the intersection-theoretic multiplicities
need from the comparison of the two rings. -/
theorem length_eq_of_stalkSemilinearEquiv (X : Scheme.{u}) (x : X)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) M]
    [Module (ToType (X.presheaf.stalk x)) N]
    (e : M ≃ₛₗ[(stalkRingEquiv X x).toRingHom] N) :
    Module.length (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) M =
      Module.length (ToType (X.presheaf.stalk x)) N :=
  Module.length_eq_of_semilinearEquiv (τ := (stalkRingEquiv X x).symm.toRingHom) e

end AlgebraicGeometry.TorFormula

end
