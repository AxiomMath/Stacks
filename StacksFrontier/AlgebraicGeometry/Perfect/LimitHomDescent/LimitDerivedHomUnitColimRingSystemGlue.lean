module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.LimitHomDescentRingSystemDerived

/-!
# The identification `A ⊗_R R[0] ≅ A[0]` is compatible with the two-step comparison

`Stacks.LimitHomDescent.Affine.extSingleSelfIso` identifies `A ⊗_R R[0]` with the one-term
complex `A[0]`, and `Stacks.LimitHomDescent.Affine.extCompIsoOf` identifies `A' ⊗_A (A ⊗_R C)`
with `A' ⊗_R C` along a factorisation `f ≫ β = f'`.  This file proves that the two agree: the
triangle

`A' ⊗_A (A ⊗_R R[0]) ⟶ A' ⊗_A A[0] ⟶ A'[0]` and `A' ⊗_A (A ⊗_R R[0]) ⟶ A' ⊗_R R[0] ⟶ A'[0]`

are the same morphism.

That square is what the module documentation of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/LimitHomDescentRingSystemDerived.lean`
records as missing, and it is what lets a consumer of
`Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq` restate the surjectivity
clause with the structure sheaf `A_j[0]` as the source rather than `A_j ⊗_R R[0]`: that
restatement is `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq_source`
below.  The injectivity clause needs no such square — conjugating it is a `cancel_epi` — which
is why only this half was outstanding.

## Main results

* `ModuleCat.ExtendScalars.objSelfIso_inv_comp_map_objSelfIso_inv`: the module-level content,
  that `A' ⟶ A' ⊗_A (A ⊗_R R)` is the same whether one goes through `A' ⊗_A A` or through
  `A' ⊗_R R`.  Both send `x` to `x ⊗ (1 ⊗ 1)`.
* `Stacks.LimitHomDescent.Affine.extSingleSelfIso_hom_comp`: the square itself.
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq_source`: every morphism
  `A[0] ⟶ A ⊗_R C'` of `D(A)` comes from a morphism `A_j[0] ⟶ A_j ⊗_R C'` of complexes at a
  stage.

## References

* [Stacks Project, Tag 09RE](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace ModuleCat.ExtendScalars

variable {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A']

/-- **The two routes from `A'` to `A' ⊗_A (A ⊗_R R)` agree.**  Going through `A' ⊗_A A` — the
inverse of `ModuleCat.ExtendScalars.objSelfIso` for `β`, followed by extension of scalars along
`β` of the inverse for `f` — is going through `A' ⊗_R R`: the inverse of `objSelfIso` for
`β ∘ f`, followed by the comparison `ModuleCat.extendScalarsComp`.

Both are `A'`-linear maps out of `A'`, so it is enough to compare them at `1`, where both give
`1 ⊗ (1 ⊗ 1)`. -/
theorem objSelfIso_inv_comp_map_objSelfIso_inv (f : R →+* A) (β : A →+* A') :
    (objSelfIso β).inv ≫ (ModuleCat.extendScalars β).map (objSelfIso f).inv =
      (objSelfIso (β.comp f)).inv ≫
        (ModuleCat.extendScalarsComp f β).hom.app (ModuleCat.of R R) := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  exact (ModuleCat.extendScalarsComp_hom_app_one_tmul f β (ModuleCat.of R R) (1 : R)).symm

/-- **The two routes from `A' ⊗_A (A ⊗_R R)` to `A'` agree.**  This is
`ModuleCat.ExtendScalars.objSelfIso_inv_comp_map_objSelfIso_inv` read on the inverse
isomorphisms; it is the module-level content of
`Stacks.LimitHomDescent.Affine.extSingleSelfIso_hom_comp`. -/
theorem map_objSelfIso_hom_comp (f : R →+* A) (β : A →+* A') :
    (ModuleCat.extendScalars β).map (objSelfIso f).hom ≫ (objSelfIso β).hom =
      (ModuleCat.extendScalarsComp f β).inv.app (ModuleCat.of R R) ≫
        (objSelfIso (β.comp f)).hom :=
  (Iso.inv_eq_inv ((ModuleCat.extendScalars β).mapIso (objSelfIso f) ≪≫ objSelfIso β)
      (((ModuleCat.extendScalarsComp f β).app (ModuleCat.of R R)).symm ≪≫
        objSelfIso (β.comp f))).mp
    (objSelfIso_inv_comp_map_objSelfIso_inv f β)

/-- **`ModuleCat.ExtendScalars.map_objSelfIso_hom_comp` with a map into `R` in front and a map
out of `A'` behind.**  This is the shape in which the degree-zero component of
`Stacks.LimitHomDescent.Affine.extSingleSelfIso_hom_comp` consumes it: there `ι` is the
identification of the degree-zero term of `R[0]` with `R` and `ρ` the inverse of the
identification of the degree-zero term of `A'[0]` with `A'`. -/
theorem map_map_comp_objSelfIso_hom (f : R →+* A) (β : A →+* A') {M : ModuleCat.{u} R}
    {N : ModuleCat.{u} A'} (ι : M ⟶ ModuleCat.of R R) (ρ : ModuleCat.of A' A' ⟶ N) :
    (ModuleCat.extendScalars β).map ((ModuleCat.extendScalars f).map ι) ≫
        (ModuleCat.extendScalars β).map (objSelfIso f).hom ≫ (objSelfIso β).hom ≫ ρ =
      (ModuleCat.extendScalarsComp f β).inv.app M ≫
        (ModuleCat.extendScalars (β.comp f)).map ι ≫ (objSelfIso (β.comp f)).hom ≫ ρ := by
  rw [reassoc_of% (map_objSelfIso_hom_comp f β), ← Functor.comp_map, NatTrans.naturality_assoc]

end ModuleCat.ExtendScalars

namespace Stacks.LimitHomDescent.Affine

variable {R A A' : CommRingCat.{u}}

/-- **`extSingleSelfIso` is compatible with `extCompIsoOf`.**  For a factorisation
`f ≫ β = f'`, identifying `A ⊗_R R[0]` with `A[0]` and then `A' ⊗_A A[0]` with `A'[0]` is
identifying `A' ⊗_A (A ⊗_R R[0])` with `A' ⊗_R R[0]` and then with `A'[0]`.

Degreewise away from `0` both sides land in a zero object.  In degree `0` the two
`HomologicalComplex.singleObjXSelf` identifications cancel and the naturality of
`ModuleCat.extendScalarsComp` reduces the claim to
`ModuleCat.ExtendScalars.objSelfIso_inv_comp_map_objSelfIso_inv`. -/
theorem extSingleSelfIso_hom_comp (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f') :
    (ext β).map (extSingleSelfIso f).hom ≫ (extSingleSelfIso β).hom =
      (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R))).hom ≫
        (extSingleSelfIso f').hom := by
  subst h
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp only [HomologicalComplex.comp_f, extSingleSelfIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapHomologicalComplex_map_f, Functor.mapIso_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, extCompIsoOf, extComp,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      eqToIso_refl, Iso.refl_hom, Category.comp_id, CommRingCat.hom_comp,
      Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.symm_hom,
      Iso.map_inv_hom_id_assoc, NatTrans.mapHomologicalComplex]
    rw [ModuleCat.ExtendScalars.map_map_comp_objSelfIso_hom]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of (A' : Type u) (A' : Type u)) n hn).eq_of_tgt _ _

/-- **The inverse form of `Stacks.LimitHomDescent.Affine.extSingleSelfIso_hom_comp`.** -/
theorem extSingleSelfIso_inv_comp (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f') :
    (extSingleSelfIso β).inv ≫ (ext β).map (extSingleSelfIso f).inv =
      (extSingleSelfIso f').inv ≫
        (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R))).inv :=
  (Iso.inv_eq_inv ((ext β).mapIso (extSingleSelfIso f) ≪≫ extSingleSelfIso β)
      (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)) ≪≫ extSingleSelfIso f')).mpr
    (extSingleSelfIso_hom_comp f β f' h)

/-- **Conjugating a chain map out of `A ⊗_R R[0]` by `extSingleSelfIso` commutes with the
two-step comparison.**  For a factorisation `f ≫ β = f'` and a chain map
`t : A ⊗_R R[0] ⟶ A ⊗_R C'`, extending `t` precomposed with `A[0] ≅ A ⊗_R R[0]` along `β` and
reading the source through `A'[0] ≅ A' ⊗_A A[0]` is extending `t` itself and reading the source
through `A'[0] ≅ A' ⊗_R R[0]`.

This is `Stacks.LimitHomDescent.Affine.extSingleSelfIso_inv_comp` with
`CategoryTheory.Functor.map_comp`. -/
theorem extSingleSelfIso_inv_comp_map (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f')
    {C' : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : (ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R R)) ⟶ (ext f).obj C') :
    (extSingleSelfIso β).inv ≫ (ext β).map ((extSingleSelfIso f).inv ≫ t) ≫
        (extCompIsoOf f β f' h C').hom =
      (extSingleSelfIso f').inv ≫
        (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R))).inv ≫
          (ext β).map t ≫ (extCompIsoOf f β f' h C').hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (extSingleSelfIso_inv_comp f β f' h)]

namespace RingSystem

variable {J : Type v} [Preorder J] (S : RingSystem.{v, u} R J) [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))
  {C' : CochainComplex (ModuleCat.{u} R) ℤ}

include hcol in
/-- **Every map out of the structure sheaf over the colimit comes from a stage, in the derived
category.**  A morphism `A[0] ⟶ A ⊗_R C'` of `D(A)` is `A ⊗_{A_j} t` for a chain map
`t : A_j[0] ⟶ A_j ⊗_R C'` at some stage `j`, the source being read through
`Stacks.LimitHomDescent.Affine.extSingleSelfIso` at both ends.

This is `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq` conjugated by
`extSingleSelfIso`, which is exactly what
`Stacks.LimitHomDescent.Affine.extSingleSelfIso_inv_comp_map` licenses.  There is no hypothesis
on `C'`, none on the complexes' boundedness or finite presentation, and no K-projectivity
instance: the first argument is `R[0]`, where all three are discharged. -/
theorem exists_Q_map_ext_single_eq_source
    (v : DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} S.lim)
        (ComplexShape.up ℤ) 0).obj (ModuleCat.of S.lim S.lim)) ⟶
      DerivedCategory.Q.obj ((ext S.φlim).obj C')) :
    ∃ (j : J) (t : (HomologicalComplex.single (ModuleCat.{u} (S.A j)) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (S.A j) (S.A j)) ⟶ (ext (S.φ j)).obj C'),
      DerivedCategory.Q.map ((extSingleSelfIso (S.γ j)).inv ≫ (ext (S.γ j)).map t ≫
        (extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C').hom) = v := by
  obtain ⟨j, t, ht⟩ := S.exists_Q_map_ext_single_eq hcol
    (DerivedCategory.Q.map (extSingleSelfIso S.φlim).hom ≫ v)
  refine ⟨j, (extSingleSelfIso (S.φ j)).inv ≫ t, ?_⟩
  rw [extSingleSelfIso_inv_comp_map (S.φ j) (S.γ j) S.φlim (S.φ_γ j) t, Functor.map_comp, ht,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end RingSystem

end Stacks.LimitHomDescent.Affine

end
