module

public import StacksFrontier.Homology.HomComplex.DerivedInternalHom

/-!
# The transpose of a transported tensor--Hom adjunction, in units and counits

`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv` is the Hom equivalence of a
tensor--Hom adjunction conjugated by an additive equivalence `e`: a composite of three additive
equivalences, two of them the Hom equivalences of the two adjunctions of `e`. This file computes
it in units and counits, and shows that the transpose of a composite ending in `e.functor`
applied to a morphism of the untransported world *cancels* the conjugation: the counit of one of
the two adjunctions of `e` absorbs it.

The bundle of [stacks 0A63] on `D(R)` at a module universe independent of the ring's,
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, is such a conjugation, of the
fixed-universe construction along `StacksDraft.DerivedHom.derivedScalarEquivalence`; by
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq` the bifunctor of the change-of-rings
isomorphism of [stacks 0E1W] is the same conjugation read in the other direction.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_apply` — the transpose of the
  conjugated adjunction in units and counits: `e.functor` applied to the untransported transpose
  of `e.inverse` of the argument, followed by the counit of `e.functor ⊣ e.inverse`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_comp_functor_map` — **the
  cancellation**: when the argument is `w` followed by `e.functor` applied to a morphism `x` of
  the untransported world, `e.inverse` of it cancels against the counit of
  `e.inverse ⊣ e.functor` and the transpose is the untransported transpose of `x` alone,
  precomposed with the tensor of the remaining `w`.
* `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_comp_functor_map` — the
  cancellation at `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`.

## Implementation notes

The first two are stated for an arbitrary `StacksDraft.DerivedHom.DerivedHomAdjunction` and an
arbitrary additive equivalence, so that an instantiation computes its own type: the objects of
the fixed-universe world never have to be written out.

No `@[stacks]` attribute is placed here: this is API for an existing construction and covers no
tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ v₁ v₂ w₁ w₂

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
  (d : DerivedHomAdjunction R)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- **The transpose of a conjugated tensor--Hom adjunction.**  For a morphism
`u : K ⟶ e.functor (RHom(e.inverse L, e.inverse M))` the transpose of `u` under the conjugated
adjunction is `e.functor` applied to the untransported transpose of

`e.inverse u` followed by the counit of `e.inverse ⊣ e.functor`,

postcomposed with the counit of `e.functor ⊣ e.inverse`. -/
theorem transportHomEquiv_apply (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (u : K ⟶ (d.transportHom e).obj (Opposite.op L, M)) :
    d.transportHomEquiv e K L M u =
      e.functor.map (d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)
          (e.inverse.map u ≫ e.symm.toAdjunction.counit.app
            (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)))) ≫
        e.toAdjunction.counit.app M := by
  simp only [transportHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_symm_apply,
    Adjunction.homEquiv_counit, Equivalence.symm_functor]

/-- **The conjugation cancels against the transpose.**  Let `x` be a morphism of the
untransported world into an internal Hom, and let `w` be any morphism into `e.functor` of its
source.  Then the transpose, under the conjugated adjunction, of `w` followed by `e.functor x` is
`e.functor` applied to the tensor of the transpose of `w` with the identity, followed by the
untransported transpose of `x` -- and no occurrence of `e.inverse ∘ e.functor` is left. -/
theorem transportHomEquiv_comp_functor_map (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (Z : DerivedCategory (ModuleCat.{v₁} R)) (w : K ⟶ e.functor.obj Z)
    (x : Z ⟶ d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)) :
    d.transportHomEquiv e K L M (w ≫ e.functor.map x) =
      e.functor.map
          (d.tensor.map (show (e.inverse.obj K, e.inverse.obj L) ⟶ (Z, e.inverse.obj L) from
              (e.inverse.map w ≫ e.symm.toAdjunction.counit.app Z, 𝟙 (e.inverse.obj L))) ≫
            d.homEquiv Z (e.inverse.obj L) (e.inverse.obj M) x) ≫
        e.toAdjunction.counit.app M := by
  rw [transportHomEquiv_apply]
  refine congrArg (· ≫ e.toAdjunction.counit.app M) (congrArg e.functor.map ?_)
  refine Eq.trans (congrArg (d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)) ?_)
    (d.homEquiv_naturality_left _ x)
  refine Eq.trans ?_ (Category.assoc _ _ x).symm
  rw [e.inverse.map_comp, Category.assoc]
  exact congrArg (e.inverse.map w ≫ ·) (e.symm.toAdjunction.counit_naturality x)

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace StacksDraft.DerivedHom

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- **The cancellation at the bundle of [stacks 0A63].**
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is the conjugation of the fixed-universe
construction along `StacksDraft.DerivedHom.derivedScalarEquivalence`, so
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_comp_functor_map` applies to it:
the [stacks 0A63] transpose of a morphism of the form `w` followed by the scalar equivalence
applied to a morphism `x` of the `ULift` world is the fixed-universe transpose of `x` alone,
precomposed with the fixed-universe tensor of the transpose of `w`. -/
public theorem derivedHomAdjunctionOverRing_homEquiv_comp_functor_map
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L M : DerivedCategory (ModuleCat.{max u v} R))
    (Z : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (w : K ⟶ (derivedScalarEquivalence.{u, v, w} R).functor.obj Z)
    (x : Z ⟶ (DerivedInternalHom.Model.hom (ULift.{v} R)).obj
      (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).inverse.obj L),
        (derivedScalarEquivalence.{u, v, w} R).inverse.obj M)) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv K L M
        (w ≫ (derivedScalarEquivalence.{u, v, w} R).functor.map x) =
      (derivedScalarEquivalence.{u, v, w} R).functor.map
          ((DerivedInternalHom.Model.tensor (ULift.{v} R)).map
              (show ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K,
                    (derivedScalarEquivalence.{u, v, w} R).inverse.obj L) ⟶
                  (Z, (derivedScalarEquivalence.{u, v, w} R).inverse.obj L) from
                ((derivedScalarEquivalence.{u, v, w} R).inverse.map w ≫
                    (derivedScalarEquivalence.{u, v, w} R).symm.toAdjunction.counit.app Z,
                  𝟙 ((derivedScalarEquivalence.{u, v, w} R).inverse.obj L))) ≫
            DerivedInternalHom.Model.homEquiv Z
              ((derivedScalarEquivalence.{u, v, w} R).inverse.obj L)
              ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M) x) ≫
        (derivedScalarEquivalence.{u, v, w} R).toAdjunction.counit.app M :=
  DerivedHomAdjunction.transportHomEquiv_comp_functor_map _ _ K L M Z w x

end StacksDraft.DerivedHom

end
