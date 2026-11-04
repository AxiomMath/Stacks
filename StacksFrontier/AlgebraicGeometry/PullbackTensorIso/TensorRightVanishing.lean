module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Tensoring by an invertible module does not change which morphisms pull back to zero

Let `k : Y ⟶ Z` be a morphism of schemes, let `B` be an invertible module on `Z`, and let
`t : N ⟶ N'` be a morphism of modules on `Z`. Then `k^* t = 0` if and only if
`k^* (t ⊗ 𝟙_B) = 0`.

The tautological section of a line bundle is the dual of the tautological functional: the two
differ by tensoring with an invertible module, so the statement that one pulls back to zero has
to be transported to the other.

## Main results

* `AlgebraicGeometry.pullback_map_tensorRight_map_eq_zero_iff`: the equivalence above.

## The route

The single mathematical input is Tag 01CD in its bifunctor form,
`Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom`, read naturally at the
morphism `(t, 𝟙 B)` of the product category. Its naturality square has
`k^*(t ⊗ 𝟙_B)` down one side and `(k^* t) ⊗ 𝟙_{k^* B}` down the other, with isomorphisms
across; since tensoring by the invertible module `k^* B` is an equivalence, hence faithful,
and is additive, a morphism vanishes exactly when its tensor does.

Two steps of that are isolated as statements about an arbitrary bifunctor and an arbitrary
preadditive category: `AlgebraicGeometry.tensorSheaf_map_prod_map_id`, replacing `k^* (𝟙 B)` by
`𝟙 (k^* B)` in the right-hand side of the square, and
`AlgebraicGeometry.eq_zero_iff_of_isIso_comm_sq` with
`AlgebraicGeometry.map_eq_zero_iff_of_additive_faithful`, moving a zero across two isomorphisms
and through a faithful additive functor.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Applying a bifunctor to a pair of morphisms whose second component is `F.map (𝟙 B)` is the
same as applying it with that component replaced by `𝟙 (F.obj B)`. -/
private lemma tensorSheaf_map_prod_map_id {C : Type*} {D : Type*} {E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (T : D × D ⥤ E)
    {N N' : C} (t : N ⟶ N') (B : C) :
    T.map ((F.map t, F.map (𝟙 B)) : ((F.obj N, F.obj B) : D × D) ⟶ (F.obj N', F.obj B)) =
      T.map ((F.map t, 𝟙 (F.obj B)) : ((F.obj N, F.obj B) : D × D) ⟶ (F.obj N', F.obj B)) := by
  rw [F.map_id]

/-- In a commuting square whose two vertical sides are isomorphisms, one horizontal side
vanishes exactly when the other does. -/
private lemma eq_zero_iff_of_isIso_comm_sq {D : Type*} [Category D] [Preadditive D]
    {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (h : f ≫ b = a ≫ g) (ha : IsIso a) (hb : IsIso b) : f = 0 ↔ g = 0 := by
  have := ha
  have := hb
  constructor
  · intro hf
    rw [hf, Limits.zero_comp] at h
    exact (cancel_epi a).mp (h.symm.trans Limits.comp_zero.symm)
  · intro hg
    rw [hg, Limits.comp_zero] at h
    exact (cancel_mono b).mp (h.trans Limits.zero_comp.symm)

/-- A faithful additive functor reflects vanishing of morphisms. -/
private lemma map_eq_zero_iff_of_additive_faithful {C : Type*} {D : Type*}
    [Category C] [Category D] [Preadditive C] [Preadditive D] (T : C ⥤ D) [T.Additive]
    [T.Faithful] {X Y : C} (u : X ⟶ Y) : T.map u = 0 ↔ u = 0 := by
  refine ⟨fun h => T.map_injective (h.trans (T.map_zero _ _).symm), fun h => ?_⟩
  rw [h, T.map_zero]

/-- **The naturality square of Tag 01CD at the morphism `(t, 𝟙 B)`.** The pullback
`k^*(t ⊗ 𝟙_B)` and the tensor `(k^* t) ⊗ 𝟙_{k^* B}` of the pullback are the two horizontal sides
of a commuting square whose vertical sides are isomorphisms: they are the components of
`Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom` at `(N, B)` and `(N', B)`, the
isomorphism of bifunctors of Tag 01CD, and the square is its naturality square, with `k^* (𝟙 B)`
replaced by `𝟙 (k^* B)` on both sides of the product category. -/
private theorem exists_isIso_comm_sq_pullback_map_tensorRight {Z Y : Scheme.{u}} (k : Y ⟶ Z)
    (B : Z.Modules) {N N' : Z.Modules} (t : N ⟶ N') :
    ∃ (a : _ ⟶ _) (b : _ ⟶ _), IsIso a ∧ IsIso b ∧
      (Scheme.Modules.pullback k).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ Z.sheaf.obj (forget₂ CommRingCat RingCat)
                Z.ringCatSheaf.property⟩).flip.obj B).map t) ≫ b =
        a ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
              Y.ringCatSheaf.property⟩).flip.obj
            ((Scheme.Modules.pullback k).obj B)).map ((Scheme.Modules.pullback k).map t) := by
  have hright : ((Functor.prod (Stacks.RingedSpace.pullbackFunctor k.toLRSHom.toShHom)
        (Stacks.RingedSpace.pullbackFunctor k.toLRSHom.toShHom) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).map
          ((t, 𝟙 B) : ((N, B) : _ × _) ⟶ (N', B))) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.property⟩).flip.obj
          ((Scheme.Modules.pullback k).obj B)).map ((Scheme.Modules.pullback k).map t) :=
    (tensorSheaf_map_prod_map_id (Stacks.RingedSpace.pullbackFunctor k.toLRSHom.toShHom)
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)) t B).trans
      ((Functor.uncurry_obj_map _ _).trans
        ((congrArg (fun m => _ ≫ m) (CategoryTheory.Functor.map_id _ _)).trans
          (Category.comp_id _)))
  have hleft : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
          ((t, 𝟙 B) : ((N, B) : _ × _) ⟶ (N', B)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ Z.sheaf.obj (forget₂ CommRingCat RingCat)
          Z.ringCatSheaf.property⟩).flip.obj B).map t :=
    (Functor.uncurry_obj_map _ _).trans
      ((congrArg (fun m => ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).map t).app B ≫ m)
        (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _))
  have e := Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom
  have : IsIso e.hom := e.isIso_hom
  refine ⟨e.hom.app (N, B), e.hom.app (N', B), NatIso.isIso_app_of_isIso e.hom _,
    NatIso.isIso_app_of_isIso e.hom _, ?_⟩
  exact (congrArg (fun m => (Stacks.RingedSpace.pullbackFunctor k.toLRSHom.toShHom).map m ≫
      e.hom.app (N', B)) hleft).symm.trans
    ((e.hom.naturality ((t, 𝟙 B) : ((N, B) : _ × _) ⟶ (N', B))).trans
      (congrArg (fun m => e.hom.app (N, B) ≫ m) hright))

/-- Tensoring on the right by an invertible module does not change whether a morphism pulls
back to zero. For a morphism of schemes `k : Y ⟶ Z`, an invertible module `B` on `Z` and a
morphism `t : N ⟶ N'` of modules on `Z`, the pullback of `t ⊗ 𝟙_B` vanishes if and only if the
pullback of `t` does.

The input is Tag 01CD as an isomorphism of bifunctors, read at the morphism `(t, 𝟙 B)`: its
naturality square compares `k^*(t ⊗ 𝟙_B)` with `(k^* t) ⊗ 𝟙_{k^* B}` across two isomorphisms.
Tensoring by `k^* B` is an equivalence by Tag 0B8L (the pullback of an invertible module is
invertible) and Tag 01CS, hence faithful, and it is additive, so it reflects vanishing. -/
theorem pullback_map_tensorRight_map_eq_zero_iff {Z Y : Scheme.{u}} (k : Y ⟶ Z)
    (B : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property B]
    {N N' : Z.Modules} (t : N ⟶ N') :
    (Scheme.Modules.pullback k).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ Z.sheaf.obj (forget₂ CommRingCat RingCat)
            Z.ringCatSheaf.property⟩).flip.obj B).map t) = 0 ↔
      (Scheme.Modules.pullback k).map t = 0 := by
  have hBk : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback k).obj B) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry k.toLRSHom.toShHom B
        ‹AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property B›)
  have hT : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
        Y.ringCatSheaf.property⟩).flip.obj
      ((Scheme.Modules.pullback k).obj B)).IsEquivalence :=
    (Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor_iff _ _ _).mpr
      (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence _ _ _)
  have hA : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
        Y.ringCatSheaf.property⟩).flip.obj
      ((Scheme.Modules.pullback k).obj B)).Additive :=
    Stacks.ProjTwistFunctor.additive_tensorRightFunctor _ _ _
  obtain ⟨a, b, ha, hb, hnat⟩ := exists_isIso_comm_sq_pullback_map_tensorRight k B t
  exact (eq_zero_iff_of_isIso_comm_sq hnat ha hb).trans
    (map_eq_zero_iff_of_additive_faithful
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.property⟩).flip.obj ((Scheme.Modules.pullback k).obj B)) _)

end AlgebraicGeometry

end
