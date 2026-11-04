module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorTranspose

/-!
# The keystone's residual equation, read at the chain level in one step

`Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_unit_comp_changeOfRingsMap` evaluates the
[stacks 0A63] transpose over `R` of a localized chain map through the K-injective representation
`StacksDraft.DerivedHom.DerivedHomData.homIso` of derived internal Hom.  The equation the keystone
of Chapter 47 reduces to is not displayed as a transpose, though: by
`Dualizing.tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation` it is an equation of morphisms
out of `Hom`-free derived tensor product, whose left-hand side is the derived tensor bifunctor
applied to a pair, followed by the pairing morphism `c` of that reduction and a tail `rho`.

Three pieces of data are asked for: a chain map `w` presenting the first entry of the pair, the
presentation of `c` as a transpose which
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation` supplies, and
the right-hand side given as the uncurrying of `w` followed by the chain-level map of
[stacks 0E1W].  What comes out is the equation itself.

So the content of the keystone's residual equation at a K-flat pair is exactly two statements: that
the [stacks 068I] side's prefix is a localized chain map, and that the [stacks 0GMT] side is the
uncurrying of that chain map composed with the chain-level map of [stacks 0E1W].  Neither mentions
a transpose, a unit or a counit of either scalar equivalence.

The three naturality properties used are naturality of the transpose of [stacks 0A63] in its source
variable, functoriality of the derived tensor bifunctor, and
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`, whose hypotheses are a
K-flat Hom-source and a K-injective target.  Nothing is assumed of `w`, of the second entry `lam`
of the pair, of the tail `rho` or of the objects they connect.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
remaining content of the other hypothesis is two chain-level statements in a single chain map.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.tensor_map_comp_homEquiv_comp_eq_of_uncurry` -- the keystone's
  residual equation holds as soon as its first factor is a localized chain map, its pairing
  morphism is the transpose of the chain-level map of [stacks 0E1W], and its right-hand side is the
  uncurrying of the two.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A)

local instance extendScalarsAdditiveLaxTensorResidue :
    (ModuleCat.extendScalars.{u, u, u} g).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).left_adjoint_additive

/-- **The keystone's residual equation, from a chain-level first factor and a chain-level
right-hand side.**

Let `g : R →+* A`, let `P` be a K-flat complex of `R`-modules, `J` a complex of `A`-modules, `I` a
K-injective complex of `R`-modules and `q : J|_R ⟶ I` any morphism, and let `w` be any morphism
from a complex `K` of `R`-modules to `Hom_A(A ⊗_R P, J)|_R`.

Suppose the first entry `a` of the pair the derived tensor bifunctor is applied to is `w`
localized, up to an isomorphism `eK` presenting its source as a class; suppose the pairing morphism
`c` presents the localization of the chain-level map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W] as a transpose through
`StacksDraft.DerivedHom.DerivedHomData.homIso`, which is what
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation` says of the
keystone's own `c`; and suppose the right-hand side is the derived tensor bifunctor at the pair
`(eK.hom, lam)`, then the K-flat representation `tensorIso` of the derived tensor product, then the
localized uncurrying of `w` followed by that chain-level map, then the tail.

Then the equation holds.  No K-flatness of `K`, no property of `q` and no property of `w` is
used. -/
public theorem tensor_map_comp_homEquiv_comp_eq_of_uncurry
    (XK XL MM : DerivedCategory (ModuleCat.{u} R))
    (K P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} g).obj J ⟶ I)
    (w : K ⟶ (CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
      (CochainComplex.HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J))
    (eK : XK ≅ DerivedCategory.Q.obj K) (lam : XL ⟶ DerivedCategory.Q.obj P)
    (a : XK ⟶ DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
      (CochainComplex.HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)))
    (c : (DerivedInternalHom.Model.tensor R).obj
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)),
          DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj I)
    (rho : DerivedCategory.Q.obj I ⟶ MM)
    (rhs : (DerivedInternalHom.Model.tensor R).obj (XK, XL) ⟶ MM)
    (ha : a = eK.hom ≫ DerivedCategory.Q.map w)
    (hc : DerivedCategory.Q.map
          (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q) =
        (DerivedInternalHom.Model.homEquiv
            (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
              (CochainComplex.HomComplexR A
                ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)))
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm c ≫
          ((DerivedInternalHom.Model.adjunction R).homIso P I).hom)
    (hrhs : rhs = (DerivedInternalHom.Model.adjunction R).tensor.map
          (((eK.hom, lam) : ((XK, XL) : DerivedCategory (ModuleCat.{u} R) ×
              DerivedCategory (ModuleCat.{u} R)) ⟶
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))) ≫
        ((DerivedInternalHom.Model.adjunction R).tensorIso K P hP).hom ≫
          DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry
            (w ≫ Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q)) ≫ rho) :
    (DerivedInternalHom.Model.adjunction R).tensor.map
        (((a, lam) : ((XK, XL) : DerivedCategory (ModuleCat.{u} R) ×
            DerivedCategory (ModuleCat.{u} R)) ⟶
          (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)),
            DerivedCategory.Q.obj P))) ≫ c ≫ rho = rhs := by
  subst ha hrhs
  have hb : DerivedCategory.Q.map
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q) ≫
      ((DerivedInternalHom.Model.adjunction R).homIso P I).inv =
      (DerivedInternalHom.Model.homEquiv
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)))
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm c := by
    rw [hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcv := (congrArg (fun z => (DerivedInternalHom.Model.homEquiv
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
        (CochainComplex.HomComplexR A
          ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)))
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) z) hb).trans
    (AddEquiv.apply_symm_apply _ c)
  have harg := (Category.assoc (DerivedCategory.Q.map w)
      (DerivedCategory.Q.map
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q))
      ((DerivedInternalHom.Model.adjunction R).homIso P I).inv).symm.trans
    (congrArg (fun z => z ≫ ((DerivedInternalHom.Model.adjunction R).homIso P I).inv)
      (DerivedCategory.Q.map_comp w
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q)).symm)
  have hmid := (congrArg (fun z => (DerivedInternalHom.Model.adjunction R).tensor.map
          ((DerivedCategory.Q.map w, 𝟙 (DerivedCategory.Q.obj P)) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) :
              DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R)) ⟶
              (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
                (CochainComplex.HomComplexR A
                  ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)),
                DerivedCategory.Q.obj P)) ≫ z) hcv.symm).trans
    (((DerivedInternalHom.Model.adjunction R).homEquiv_naturality_left
        (DerivedCategory.Q.map w)
        (DerivedCategory.Q.map
            (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q) ≫
          ((DerivedInternalHom.Model.adjunction R).homIso P I).inv)).symm.trans
      ((congrArg (fun z => (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) z) harg).trans
        (DerivedInternalHom.Model.homEquiv_map_uncurry K P I hP
          (w ≫ Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap g P J I q))))
  have hsplit : (DerivedInternalHom.Model.adjunction R).tensor.map
        (((eK.hom ≫ DerivedCategory.Q.map w, lam) :
          ((XK, XL) : DerivedCategory (ModuleCat.{u} R) ×
              DerivedCategory (ModuleCat.{u} R)) ⟶
            (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
              (CochainComplex.HomComplexR A
                ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)),
              DerivedCategory.Q.obj P))) =
      (DerivedInternalHom.Model.adjunction R).tensor.map
          (((eK.hom, lam) : ((XK, XL) : DerivedCategory (ModuleCat.{u} R) ×
              DerivedCategory (ModuleCat.{u} R)) ⟶
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))) ≫
        (DerivedInternalHom.Model.adjunction R).tensor.map
          ((DerivedCategory.Q.map w, 𝟙 (DerivedCategory.Q.obj P)) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) :
              DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R)) ⟶
              (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{u, u, u} g).obj
                (CochainComplex.HomComplexR A
                  ((CochainComplex.extendScalarsLarge.{u, u, u} g).obj P) J)),
                DerivedCategory.Q.obj P)) := by
    rw [← Functor.map_comp, prod_comp, Category.comp_id]
  rw [hsplit, Category.assoc, ← Category.assoc _ _ rho, hmid, Category.assoc]

end Stacks.DerivedHom.BaseChangeIso

end
