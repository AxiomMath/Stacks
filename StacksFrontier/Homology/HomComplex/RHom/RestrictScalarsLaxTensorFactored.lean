module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorTranspose

/-!
# Every chain map into a restricted internal Hom complex factors through the unit

`Stacks.DerivedHom.BaseChangeIso.uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap`
evaluates the [stacks 0A63] uncurrying of the chain-level map of [stacks 0E1W], but only at a
morphism of the special shape

`K ⟶ (A ⊗_R K)|_R ⟶ Hom_A(A ⊗_R P, J)|_R`,

the degreewise unit of extension of scalars followed by the restriction of a transpose over `A`.
The keystone of Chapter 47 meets that uncurrying at a morphism `w : K ⟶ Hom_A(A ⊗_R P, J)|_R`
about which nothing at all is known: `Dualizing.exists_prefix_chain_map` produces `w` from
K-injectivity of the target, so it is an arbitrary chain map.

This file observes that the restriction is no restriction.  The target is the restriction along `f`
of a complex of `A`-modules, so `w` *is* a transpose: `t` is `w` read across the degreewise
extension--restriction adjunction, and `w = η_K ≫ t|_R` is the triangle identity.  Feeding `t` to
the lemma above therefore evaluates the uncurrying at an arbitrary `w`, and what comes out carries
the monoidality comparison `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of
[stacks 068I] at the pair `(K, P)` of *ordinary* complexes -- the only pair at which that
comparison is available -- together with the degreewise unit at `K ⊗_R P`, which is the keystone's
other side.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
chain-level mate square is available at the keystone's own chain map and not only at a transpose.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.exists_uncurry_unit_value` -- for every chain map `w` into the
  restriction of an internal Hom complex over `A` there is a transpose `t` presenting `w` as the
  degreewise unit followed by the restriction of `t`, and the uncurrying of `w` composed with the
  chain-level map of [stacks 0E1W] is the degreewise unit at the tensor product, the restriction of
  the inverse monoidality comparison composed with the uncurrying of `t`, and the chosen morphism
  out of the restricted K-injective target.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditiveLaxTensorFactored :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **Every morphism into the image of a right adjoint is the unit followed by a transpose.**  The
triangle identity read as a factorization: the transpose of `w` across the adjunction is a morphism
`t` out of the left adjoint, and `w` is the unit followed by the right adjoint of `t`. -/
private theorem exists_eq_unit_comp_map {C D : Type*} [Category C] [Category D]
    {Lf : C ⥤ D} {Gf : D ⥤ C} (adj : Lf ⊣ Gf) {X : C} {Y : D} (w : X ⟶ Gf.obj Y) :
    ∃ t, w = adj.unit.app X ≫ Gf.map t :=
  ⟨(adj.homEquiv X Y).symm w,
    (Equiv.apply_symm_apply (adj.homEquiv X Y) w).symm.trans
      (Adjunction.homEquiv_unit _ _ _ _)⟩

/-- **The chain-level mate square at an arbitrary chain map.**

For every chain map `w : K ⟶ Hom_A(A ⊗_R P, J)|_R` there is a transpose
`t : A ⊗_R K ⟶ Hom_A(A ⊗_R P, J)` with `w = η_K ≫ t|_R`, and then
`Stacks.DerivedHom.BaseChangeIso.uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap`
evaluates the [stacks 0A63] uncurrying of `w` followed by the chain-level map of [stacks 0E1W]:
it is the degreewise unit of extension of scalars at `K ⊗_R P`, then the restriction of the
inverse monoidality comparison of [stacks 068I] at `(K, P)` composed with the uncurrying of `t`,
then `q`.

The transpose is where all the freedom in `w` has gone, and the shape of the right-hand side is
what the keystone of Chapter 47 needs: its [stacks 0GMT] side carries the degreewise unit at the
total tensor complex, and its [stacks 068I] side carries the monoidality comparison.

Nothing is assumed of `K`, `P`, `J`, `I`, `q` or `w`; in particular no K-flatness and no
K-injectivity. -/
public theorem exists_uncurry_unit_value
    (K P : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (w : K ⟶ (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
      (CochainComplex.HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J)) :
    ∃ t : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj K ⟶
        CochainComplex.HomComplexR A
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J,
      w = ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ∧
        DerivedInternalHom.Model.uncurry
            (w ≫ Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) =
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
            (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
              ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv ≫
                DerivedInternalHom.Model.uncurry t) ≫ q := by
  obtain ⟨t, rfl⟩ := exists_eq_unit_comp_map
    (CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj f) w
  exact ⟨t, rfl, uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap f K P J I q t⟩

end Stacks.DerivedHom.BaseChangeIso

end
