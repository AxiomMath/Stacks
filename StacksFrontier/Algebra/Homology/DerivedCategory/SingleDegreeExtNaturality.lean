module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExt

/-!
# Naturality of the identification of single-degree morphisms with `Ext`-groups

`DerivedCategory.singleHomEquivExt` identifies `Hom_{D(𝒜)}(A[p], B[q])` with `Ext^i_𝒜(A, B)`,
where `q + i = p`. It is a bijection of `Hom`-sets only; this file supplies the two
compatibilities that an application of it to the dévissage of [Stacks, Tag 0G2H] needs.

## Naturality in the source

Precomposing with `(singleFunctor 𝒜 p).map a` for `a : A' ⟶ A` corresponds to Yoneda composition
with `CategoryTheory.Abelian.Ext.mk₀ a`
(`DerivedCategory.singleHomEquivExt_singleFunctor_map_comp`). This is the compatibility with the
transition maps of an inverse system in the source variable, which is what the tag's source
system `n ↦ 𝓘^n𝓕` reduces to.

Everything is read off `DerivedCategory.singleHomEquivExt_symm_apply`, which writes out the
morphism attached to an `Ext`-class: the identification is conjugation by
`CategoryTheory.SingleFunctors.shiftIso`, so naturality in the source is the naturality of
`shiftIso`, and the `Ext`-side statement is `CategoryTheory.ShiftedHom.mk₀_comp`.

## Compatibility with an exact functor

For an exact `Φ : 𝒜 ⥤ ℬ` the identification intertwines `Φ.mapDerivedCategory` on morphisms with
`CategoryTheory.Abelian.Ext.mapExactFunctor` on `Ext`-classes
(`CategoryTheory.Functor.singleHomEquivExt_mapSingleFunctorIso_conj`). This is the compatibility
with restriction along an open immersion, which in the situation of the tag is
`Stacks.AlgebraicGeometry.IdealPowerColimit.extRestrict`.

The source and target of a morphism have to be transported along a comparison
`Φ(A[p]) ≅ Φ(A)[p]`, and the one used here is **not**
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor p`: Mathlib provides no compatibility of
that family with the shift — that would be the assertion that it is a morphism of
`CategoryTheory.SingleFunctors`, for which neither a `precomp` on `SingleFunctors` nor a
shift-compatibility of `HomologicalComplex.singleMapHomologicalComplex` exists. Instead
`CategoryTheory.Functor.mapSingleFunctorIso` is built **through degree zero**, as

`Φ(A[p]) ≅ Φ((A[0])⟦-p⟧) ≅ (Φ(A[0]))⟦-p⟧ ≅ (Φ(A)[0])⟦-p⟧ ≅ Φ(A)[p]`,

using only `mapDerivedCategorySingleFunctor 0` — which is the degree
`CategoryTheory.Abelian.Ext.mapExactFunctor_hom` is stated at — together with
`CategoryTheory.Functor.commShiftIso`. Its compatibility with the shift is then nothing but the
splitting of a commutation isomorphism in a degree `c = a + b`,
`CategoryTheory.Functor.commShiftIso_inv_app_map_shiftFunctorAdd'_inv_app`.

## Main results

* `DerivedCategory.singleHomEquivExt_symm_apply`: the morphism attached to an `Ext`-class.
* `DerivedCategory.singleHomEquivExt_symm_mk₀_comp` and
  `DerivedCategory.singleHomEquivExt_singleFunctor_map_comp`: **naturality in the source.**
* `CategoryTheory.Functor.mapSingleFunctorIso`: the comparison `Φ(A[p]) ≅ Φ(A)[p]`.
* `CategoryTheory.Functor.mapSingleFunctorIso_conj_singleHomEquivExt_symm` and
  `CategoryTheory.Functor.singleHomEquivExt_mapSingleFunctorIso_conj`: **compatibility with an
  exact functor.**

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' t t' v u v' u'

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜] [HasExt.{w} 𝒜]

/-- The morphism of `D(𝒜)` that `DerivedCategory.singleHomEquivExt` attaches to an `Ext`-class,
written out. -/
public lemma singleHomEquivExt_symm_apply (A B : 𝒜) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p)
    (ξ : Ext.{w} A B i) :
    (singleHomEquivExt A B p q i hi).symm ξ =
      ((singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).inv.app A ≫
        (shiftFunctor (DerivedCategory 𝒜) (-p)).map ξ.hom ≫
          ((shiftFunctorAdd' (DerivedCategory 𝒜) (i : ℤ) (-p) (-q) (by lia)).inv.app
              ((singleFunctor 𝒜 0).obj B) ≫
            ((singleFunctors 𝒜).shiftIso (-q) q 0 (by lia)).hom.app B) := rfl

/-- **Naturality in the source.** -/
public lemma singleHomEquivExt_symm_mk₀_comp {A A' B : 𝒜} (a : A' ⟶ A) (p q : ℤ) (i : ℕ)
    (hi : q + (i : ℤ) = p) (ξ : Ext.{w} A B i) :
    (singleHomEquivExt A' B p q i hi).symm ((Ext.mk₀ a).comp ξ (zero_add i)) =
      (singleFunctor 𝒜 p).map a ≫ (singleHomEquivExt A B p q i hi).symm ξ := by
  rw [singleHomEquivExt_symm_apply, singleHomEquivExt_symm_apply]
  have hh : ((Ext.mk₀ a).comp ξ (zero_add i)).hom = (singleFunctor 𝒜 0).map a ≫ ξ.hom := by
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  have hnat : (singleFunctor 𝒜 p).map a ≫
        ((singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).inv.app A =
      ((singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).inv.app A' ≫
        (shiftFunctor (DerivedCategory 𝒜) (-p)).map ((singleFunctor 𝒜 0).map a) :=
    (((singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).inv).naturality a
  rw [hh, Functor.map_comp]
  simp only [Category.assoc]
  conv_rhs => rw [← Category.assoc, hnat, Category.assoc]

/-- **Naturality in the source, forward form.** -/
public lemma singleHomEquivExt_singleFunctor_map_comp {A A' B : 𝒜} (a : A' ⟶ A) (p q : ℤ) (i : ℕ)
    (hi : q + (i : ℤ) = p) (f : (singleFunctor 𝒜 p).obj A ⟶ (singleFunctor 𝒜 q).obj B) :
    singleHomEquivExt A' B p q i hi ((singleFunctor 𝒜 p).map a ≫ f) =
      (Ext.mk₀ a).comp (singleHomEquivExt A B p q i hi f) (zero_add i) := by
  rw [← Equiv.eq_symm_apply, singleHomEquivExt_symm_mk₀_comp, Equiv.symm_apply_apply]

end DerivedCategory

namespace CategoryTheory.Functor

section CommShift

variable {M : Type*} [AddMonoid M] {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]
  [HasShift 𝒞 M] [HasShift 𝒟 M]

/-- Splitting a commutation isomorphism of a functor with the shift by `c = a + b` into the
commutation isomorphisms in the degrees `a` and `b`, in the shape the identification of
single-degree morphisms with `Ext`-groups consumes. -/
public lemma commShiftIso_inv_app_map_shiftFunctorAdd'_inv_app (R : 𝒞 ⥤ 𝒟) [R.CommShift M]
    {a b c : M} (h : a + b = c) (Y : 𝒞) :
    (R.commShiftIso b).inv.app (Y⟦a⟧) ≫
        R.map ((shiftFunctorAdd' 𝒞 a b c h).inv.app Y) ≫ (R.commShiftIso c).hom.app Y =
      ((R.commShiftIso a).hom.app Y)⟦b⟧' ≫ (shiftFunctorAdd' 𝒟 a b c h).inv.app (R.obj Y) := by
  have hadd := NatTrans.congr_app (congr_arg Iso.hom (R.commShiftIso_add' h)) Y
  simp only [CommShift.isoAdd'_hom_app] at hadd
  rw [hadd, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end CommShift

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ]
  (Φ : 𝒜 ⥤ ℬ) [Φ.Additive] [Limits.PreservesFiniteLimits Φ] [Limits.PreservesFiniteColimits Φ]
  [HasDerivedCategory.{w'} 𝒜] [HasDerivedCategory.{t'} ℬ]

/-- The comparison `Φ(A)[p] ≅ Φ(A[p])` for an exact functor `Φ`, built from the degree-zero
comparison `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and the commutation of
`Φ.mapDerivedCategory` with the shift.

This is *not* `Φ.mapDerivedCategorySingleFunctor p`: it is the composite through degree zero,
which is what makes its compatibility with the shift available. -/
public noncomputable def mapSingleFunctorIso (p : ℤ) :
    DerivedCategory.singleFunctor 𝒜 p ⋙ Φ.mapDerivedCategory ≅
      Φ ⋙ DerivedCategory.singleFunctor ℬ p :=
  isoWhiskerRight ((DerivedCategory.singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).symm
      Φ.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (DerivedCategory.singleFunctor 𝒜 0)
      (Φ.mapDerivedCategory.commShiftIso (-p)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Φ.mapDerivedCategorySingleFunctor 0)
      (shiftFunctor (DerivedCategory ℬ) (-p)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Φ ((DerivedCategory.singleFunctors ℬ).shiftIso (-p) p 0 (by lia))

/-- The component at `A` of `CategoryTheory.Functor.mapSingleFunctorIso`, written out as the
composite of `Φ.mapDerivedCategory` applied to the inverse of the shift isomorphism of
`DerivedCategory.singleFunctors 𝒜`, the commutation of `Φ.mapDerivedCategory` with the shift by
`-p`, the shifted degree-zero comparison `Φ.mapDerivedCategorySingleFunctor 0` and the shift
isomorphism of `DerivedCategory.singleFunctors ℬ`. -/
public lemma mapSingleFunctorIso_hom_app (p : ℤ) (A : 𝒜) :
    (Φ.mapSingleFunctorIso p).hom.app A =
      Φ.mapDerivedCategory.map
          (((DerivedCategory.singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).inv.app A) ≫
        (Φ.mapDerivedCategory.commShiftIso (-p)).hom.app
            ((DerivedCategory.singleFunctor 𝒜 0).obj A) ≫
          (shiftFunctor (DerivedCategory ℬ) (-p)).map
              ((Φ.mapDerivedCategorySingleFunctor 0).hom.app A) ≫
            ((DerivedCategory.singleFunctors ℬ).shiftIso (-p) p 0 (by lia)).hom.app (Φ.obj A) := by
  simp [mapSingleFunctorIso]

/-- The inverse of the component at `A` of `CategoryTheory.Functor.mapSingleFunctorIso`, written
out as the composite, in the reverse order, of the inverses of the four isomorphisms of
`CategoryTheory.Functor.mapSingleFunctorIso_hom_app`. -/
public lemma mapSingleFunctorIso_inv_app (p : ℤ) (A : 𝒜) :
    (Φ.mapSingleFunctorIso p).inv.app A =
      ((DerivedCategory.singleFunctors ℬ).shiftIso (-p) p 0 (by lia)).inv.app (Φ.obj A) ≫
        (shiftFunctor (DerivedCategory ℬ) (-p)).map
            ((Φ.mapDerivedCategorySingleFunctor 0).inv.app A) ≫
          (Φ.mapDerivedCategory.commShiftIso (-p)).inv.app
              ((DerivedCategory.singleFunctor 𝒜 0).obj A) ≫
            Φ.mapDerivedCategory.map
              (((DerivedCategory.singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).hom.app A) := by
  simp [mapSingleFunctorIso]

/-- **Compatibility of `DerivedCategory.singleHomEquivExt` with an exact functor.** -/
public lemma mapSingleFunctorIso_conj_singleHomEquivExt_symm [HasExt.{w} 𝒜] [HasExt.{t} ℬ]
    (A B : 𝒜) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p) (ξ : Ext.{w} A B i) :
    (Φ.mapSingleFunctorIso p).inv.app A ≫
        Φ.mapDerivedCategory.map
          ((DerivedCategory.singleHomEquivExt A B p q i hi).symm ξ) ≫
        (Φ.mapSingleFunctorIso q).hom.app B =
      (DerivedCategory.singleHomEquivExt (Φ.obj A) (Φ.obj B) p q i hi).symm
        (ξ.mapExactFunctor Φ) := by
  have hpq : (i : ℤ) + -p = -q := by lia
  have hR : Φ.mapDerivedCategory.map
          (((DerivedCategory.singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).hom.app A) ≫
        Φ.mapDerivedCategory.map
          ((DerivedCategory.singleHomEquivExt A B p q i hi).symm ξ) ≫
        Φ.mapDerivedCategory.map
          (((DerivedCategory.singleFunctors 𝒜).shiftIso (-q) q 0 (by lia)).inv.app B) =
      Φ.mapDerivedCategory.map ((shiftFunctor (DerivedCategory 𝒜) (-p)).map ξ.hom) ≫
        Φ.mapDerivedCategory.map ((shiftFunctorAdd' (DerivedCategory 𝒜) (i : ℤ) (-p) (-q)
          hpq).inv.app ((DerivedCategory.singleFunctor 𝒜 0).obj B)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.singleHomEquivExt_symm_apply]
    exact congrArg _ (by simp)
  conv_rhs => rw [DerivedCategory.singleHomEquivExt_symm_apply]
  rw [Abelian.Ext.mapExactFunctor_hom, Φ.mapSingleFunctorIso_inv_app,
    Φ.mapSingleFunctorIso_hom_app]
  have middle :
      (Φ.mapDerivedCategory.commShiftIso (-p)).inv.app
            ((DerivedCategory.singleFunctor 𝒜 0).obj A) ≫
          Φ.mapDerivedCategory.map ((shiftFunctor (DerivedCategory 𝒜) (-p)).map ξ.hom) ≫
          Φ.mapDerivedCategory.map ((shiftFunctorAdd' (DerivedCategory 𝒜) (i : ℤ) (-p) (-q)
              hpq).inv.app ((DerivedCategory.singleFunctor 𝒜 0).obj B)) ≫
          (Φ.mapDerivedCategory.commShiftIso (-q)).hom.app
            ((DerivedCategory.singleFunctor 𝒜 0).obj B) ≫
          (shiftFunctor (DerivedCategory ℬ) (-q)).map
            ((Φ.mapDerivedCategorySingleFunctor 0).hom.app B) =
        (shiftFunctor (DerivedCategory ℬ) (-p)).map (Φ.mapDerivedCategory.map ξ.hom) ≫
          (shiftFunctor (DerivedCategory ℬ) (-p)).map
            ((Φ.mapDerivedCategory.commShiftIso (i : ℤ)).hom.app
              ((DerivedCategory.singleFunctor 𝒜 0).obj B)) ≫
          (shiftFunctor (DerivedCategory ℬ) (-p)).map
            ((shiftFunctor (DerivedCategory ℬ) (i : ℤ)).map
              ((Φ.mapDerivedCategorySingleFunctor 0).hom.app B)) ≫
          (shiftFunctorAdd' (DerivedCategory ℬ) (i : ℤ) (-p) (-q) hpq).inv.app
            ((DerivedCategory.singleFunctor ℬ 0).obj (Φ.obj B)) := by
    have hnat2 : (shiftFunctorAdd' (DerivedCategory ℬ) (i : ℤ) (-p) (-q) hpq).inv.app
            (Φ.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 0).obj B)) ≫
          (shiftFunctor (DerivedCategory ℬ) (-q)).map
            ((Φ.mapDerivedCategorySingleFunctor 0).hom.app B) =
        (shiftFunctor (DerivedCategory ℬ) (-p)).map
            ((shiftFunctor (DerivedCategory ℬ) (i : ℤ)).map
              ((Φ.mapDerivedCategorySingleFunctor 0).hom.app B)) ≫
          (shiftFunctorAdd' (DerivedCategory ℬ) (i : ℤ) (-p) (-q) hpq).inv.app
            ((DerivedCategory.singleFunctor ℬ 0).obj (Φ.obj B)) :=
      ((shiftFunctorAdd' (DerivedCategory ℬ) (i : ℤ) (-p) (-q) hpq).inv.naturality
        ((Φ.mapDerivedCategorySingleFunctor 0).hom.app B)).symm
    rw [← Functor.commShiftIso_inv_naturality_assoc,
      reassoc_of% (Φ.mapDerivedCategory.commShiftIso_inv_app_map_shiftFunctorAdd'_inv_app hpq
        ((DerivedCategory.singleFunctor 𝒜 0).obj B)), hnat2]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hR, reassoc_of% middle]

/-- **Compatibility of `DerivedCategory.singleHomEquivExt` with an exact functor**, forward
form: reading a morphism `A[p] ⟶ B[q]` of `D(𝒜)` as an `Ext`-class and then applying `Φ` to the
class is the same as applying `Φ.mapDerivedCategory` to the morphism, transporting its source and
target by `CategoryTheory.Functor.mapSingleFunctorIso`, and reading the result as an
`Ext`-class. -/
public lemma singleHomEquivExt_mapSingleFunctorIso_conj [HasExt.{w} 𝒜] [HasExt.{t} ℬ]
    (A B : 𝒜) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p)
    (f : (DerivedCategory.singleFunctor 𝒜 p).obj A ⟶ (DerivedCategory.singleFunctor 𝒜 q).obj B) :
    DerivedCategory.singleHomEquivExt (Φ.obj A) (Φ.obj B) p q i hi
        ((Φ.mapSingleFunctorIso p).inv.app A ≫ Φ.mapDerivedCategory.map f ≫
          (Φ.mapSingleFunctorIso q).hom.app B) =
      (DerivedCategory.singleHomEquivExt A B p q i hi f).mapExactFunctor Φ := by
  rw [← Equiv.eq_symm_apply,
    ← Φ.mapSingleFunctorIso_conj_singleHomEquivExt_symm A B p q i hi
      (DerivedCategory.singleHomEquivExt A B p q i hi f), Equiv.symm_apply_apply]

end CategoryTheory.Functor

end
