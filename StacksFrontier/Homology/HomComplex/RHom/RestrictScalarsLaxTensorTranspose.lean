module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorHom

/-!
# The change-of-rings Hom map absorbs a transpose

`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` reads the
restricted evaluation of an internal Hom complex over the larger ring as the evaluation over the
smaller one, precomposed with the chain-level change-of-rings map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W].  That identity is about
the *identity* of the Hom complex.  The keystone's [stacks 068I] side instead meets the
change-of-rings map preceded by the restriction of a [stacks 0A63] transpose over the larger ring:
the transpose of the [stacks 068I] candidate.

This module evaluates that composite.  The transpose is absorbed, by naturality of the lax monoidal
structure map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` in its first variable and the
chain-level triangle identity
`StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry_eq_tensorHom_evaluationMor`, leaving the
lax structure map at the pair whose first entry is the *source* of the transpose rather than an
internal Hom complex.  That is exactly the move the keystone needs: at a pair of extensions of
ordinary complexes the lax structure map is governed by the mate square
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor`, which at a pair whose
first entry is an internal Hom complex it is not.

The last result makes that move.  With the unit of degreewise extension--restriction in front, the
whole composite becomes the unit at the tensor product followed by the restriction of the inverse
monoidality comparison `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` and the uncurried
transpose.  No K-flatness, no K-injectivity and no property of the resolution `q` is used anywhere.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.uncurry_restrictScalars_map_comp_changeOfRingsMap` -- the
  restriction of a transpose followed by the change-of-rings map, uncurried: the unit in the second
  variable, the lax structure map at the transpose's source, the restriction of the uncurried
  transpose, and `q`.
* `Stacks.DerivedHom.BaseChangeIso.uncurry_comp_restrictScalars_map_comp_changeOfRingsMap` -- the
  same with an arbitrary morphism composed in front, with the two whiskerings of the unit merged
  into one.
* `Stacks.DerivedHom.BaseChangeIso.uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap` --
  **the mate square fired.**  With the unit of degreewise extension--restriction as that morphism,
  the composite is the unit at the tensor product, the restriction of the inverse monoidality
  comparison and the uncurried transpose, and `q`.
* `Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_unit_comp_changeOfRingsMap` -- the same read in
  the derived category, as a [stacks 0A63] transpose over `R`, at a K-flat
  Hom-source and a K-injective target.

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

local instance extendScalarsAdditiveLaxTensorTranspose :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The change-of-rings Hom map absorbs the restriction of a transpose.**

Let `f : R →+* A`, let `X` be a complex of `A`-modules, `P` a complex of `R`-modules, `J` a
complex of `A`-modules and `q : J|_R ⟶ I` a map of complexes of `R`-modules, and let
`t : X ⟶ Hom_A(A ⊗_R P, J)` be any morphism.  Then the [stacks 0A63] uncurrying over `R` of

`X|_R ⟶ Hom_A(A ⊗_R P, J)|_R ⟶ Hom_R(P, I)`

-- the restriction of `t` followed by the chain-level change-of-rings map of [stacks 0E1W] -- is
the unit of degreewise extension--restriction in the second variable, the lax monoidal structure
map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` **at `(X, A ⊗_R P)`**, the restriction
of the uncurrying of `t` over `A`, and then `q`.

`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_uncurry_changeOfRingsMap` is the case
`t = 𝟙`, where the lax structure map stands at the pair `(Hom_A(A ⊗_R P, J), A ⊗_R P)`.

Nothing is assumed of `X`, `P`, `J`, `I`, `q` or `t`. -/
public theorem uncurry_restrictScalars_map_comp_changeOfRingsMap
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (t : X ⟶ CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) :
    DerivedInternalHom.Model.uncurry
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ≫
          Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) =
      (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X) ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f X
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (DerivedInternalHom.Model.uncurry t) ≫ q := by
  have hnat := CochainComplex.ExtendScalars.restrictScalarsLaxTensor_naturality f t
    (𝟙 ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P))
  rw [CategoryTheory.Functor.map_id] at hnat
  have hev : (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        (t ⊗ₘ 𝟙 ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P)) ≫
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        (DerivedInternalHom.Model.evaluationMor
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) =
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        (DerivedInternalHom.Model.uncurry t) := by
    rw [← CategoryTheory.Functor.map_comp,
      ← DerivedInternalHom.Model.uncurry_eq_tensorHom_evaluationMor t]
  have hA : ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ⊗ₘ 𝟙 P) ≫
        (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J)) ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) =
      (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X) ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) ≫
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ⊗ₘ
          𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P))) := by
    refine (tensorHom_comp_tensorHom _ _ _ _).trans (Eq.trans ?_
      (tensorHom_comp_tensorHom _ _ _ _).symm)
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg _ (Category.comp_id _).symm
  have hD : ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ⊗ₘ
          𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P))) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J)
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
              (DerivedInternalHom.Model.evaluationMor
                ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) ≫ q =
      CochainComplex.ExtendScalars.restrictScalarsLaxTensor f X
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (DerivedInternalHom.Model.uncurry t) ≫ q := by
    rw [reassoc_of% hnat, reassoc_of% hev]
  refine (DerivedInternalHom.Model.uncurry_comp_left _ _).trans ?_
  rw [← restrictedEvaluation_eq_uncurry_changeOfRingsMap f P J I q]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hA]
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X) ⊗ₘ
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P) ≫ z) hD

/-- **The same with a prefix, and the unit whiskered once.**

`Stacks.DerivedHom.BaseChangeIso.uncurry_restrictScalars_map_comp_changeOfRingsMap` with a further
morphism `u` out of a complex of `R`-modules composed in front, and with the two whiskerings
`u ⊗ₘ 𝟙` and `𝟙 ⊗ₘ η` merged into the single `u ⊗ₘ η` by
`CategoryTheory.MonoidalCategory.tensorHom_id_comp_id_tensorHom`.

That merged shape is the hypothesis the mate square
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor` is stated against. -/
public theorem uncurry_comp_restrictScalars_map_comp_changeOfRingsMap
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (Y : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : Y ⟶ (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X)
    (t : X ⟶ CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) :
    DerivedInternalHom.Model.uncurry
        (u ≫ (CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ≫
          Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) =
      (u ⊗ₘ ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app P) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f X
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (DerivedInternalHom.Model.uncurry t) ≫ q := by
  refine (DerivedInternalHom.Model.uncurry_comp_left _ _).trans ?_
  rw [uncurry_restrictScalars_map_comp_changeOfRingsMap f X P J I q t]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [CategoryTheory.MonoidalCategory.tensorHom_id_comp_id_tensorHom]

/-- **The mate square fired: the whole composite is the unit at the tensor product.**

`Stacks.DerivedHom.BaseChangeIso.uncurry_comp_restrictScalars_map_comp_changeOfRingsMap` with the
prefix taken to be the unit of degreewise extension--restriction at `K`, so that the lax monoidal
structure map stands at the pair `(A ⊗_R K, A ⊗_R P)` of extensions of ordinary complexes.  There
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor_eq` applies: the unit in
both variables followed by the lax structure map is the unit at `K ⊗_R P` followed by the
restriction of the inverse monoidality comparison
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.

So the uncurrying of

`K ⟶ (A ⊗_R K)|_R ⟶ Hom_A(A ⊗_R P, J)|_R ⟶ Hom_R(P, I)`

-- the unit of [stacks 0GMT] at the chain level, the restriction of a [stacks 0A63] transpose over
`A`, and the chain-level [stacks 0E1W] map -- is the unit at `K ⊗_R P`, then the restriction of the
inverse monoidality comparison at the pair `(K, P)` composed with the uncurried transpose, and then
`q`.

This is the chain-level content of the keystone's residual equation: its left-hand side is the
[stacks 068I] side's prefix and its right-hand side carries the unit of [stacks 0GMT] at the tensor
product -- the keystone's other side -- with the [stacks 068I] monoidality comparison at the pair
of *ordinary* complexes, which is the only pair at which that comparison is available.

Nothing is assumed of `K`, `P`, `J`, `I`, `q` or `t`; in particular no K-flatness and no
K-injectivity. -/
public theorem uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap
    (K P : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (t : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj K ⟶
      CochainComplex.HomComplexR A
        ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) :
    DerivedInternalHom.Model.uncurry
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ≫
            Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv ≫
            DerivedInternalHom.Model.uncurry t) ≫ q := by
  have hmate : ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K)
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P)) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv :=
    CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor_eq f K P
  refine (uncurry_comp_restrictScalars_map_comp_changeOfRingsMap f
    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) P J I q K
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app K) t).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
    (DerivedInternalHom.Model.uncurry t) ≫ q) hmate).trans ?_
  rw [CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫ z) (Category.assoc _ _ _).symm)

/-- **The chain-level residue localized.**

`Stacks.DerivedHom.BaseChangeIso.uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap`
carried into the derived category by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`, whose two hypotheses are a
K-flat Hom-source and a K-injective target: the [stacks 0A63] transpose over `R` of the
localization of

`K ⟶ (A ⊗_R K)|_R ⟶ Hom_A(A ⊗_R P, J)|_R ⟶ Hom_R(P, I)`,

read through the K-injective representation `homIso` of derived internal Hom, is the K-flat
representation `tensorIso` of the derived tensor product followed by the localization of the unit
of [stacks 0GMT] at `K ⊗_R P`, the restriction of the inverse monoidality comparison at `(K, P)`
and the uncurried transpose.

This is the shape in which the chain-level residue meets the keystone: there the transpose over `R`
is what the uncurried inverse component of [stacks 0E1W] is evaluated by, and the right-hand side
is the keystone's own other side. -/
public theorem homEquiv_Q_map_unit_comp_changeOfRingsMap
    (K P : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (t : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj K ⟶
      CochainComplex.HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj P) J) :
    DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K ≫
            (CochainComplex.restrictScalarsLarge.{u, u, u} f).map t ≫
              Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) ≫
          ((DerivedInternalHom.Model.adjunction R).homIso P I).inv) =
      ((DerivedInternalHom.Model.adjunction R).tensorIso K P hP).hom ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
            (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
              ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv ≫
                DerivedInternalHom.Model.uncurry t) ≫ q) := by
  refine (DerivedInternalHom.Model.homEquiv_map_uncurry K P I hP _).trans ?_
  rw [uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap f K P J I q t]

end Stacks.DerivedHom.BaseChangeIso

end
