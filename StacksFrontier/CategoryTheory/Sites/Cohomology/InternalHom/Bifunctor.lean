module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
import StacksCore.Tactic.StacksAttribute

/-! # The internal Hom complex as a bifunctor on a ringed site

Let `(C, O)` be a ringed site. The internal Hom complex `SheafHom(K, M)` of two cochain
complexes of `O`-modules is constructed in `StacksDraft.Ch21.Sec34.InternalHomComplexOnASite`
and made functorial in both variables, by `AlgebraicGeometry.RingedSite.homMap`, in
`StacksDraft.Ch21.Sec34.HomComplexTensorCurrying`. This file supplies the one identity that
functoriality still lacked — that `homMap` composes — and packages the construction as a
bifunctor

`SheafHom(-, -) : K(O)ᵒᵖ ⥤ K(O) ⥤ K(O)`

on cochain complexes of `O`-modules, contravariant in its first variable.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`: the internal Hom complex as a
  bifunctor, contravariant in its source.

## Main results

* `AlgebraicGeometry.RingedSite.cochainConj_comp` and
  `AlgebraicGeometry.RingedSite.homMap_comp`: pre- and postcomposition, and the induced maps
  of internal Hom complexes, compose.

## Implementation notes

The internal Hom complex is available only through its characterising data, so `homMap_comp`
is proved the same way `homMap_id` is: the two sides are compared on sections over an object
through the additive equivalence `SheafHomComplex.sectionsEquiv`, where `homMap` becomes the
pre- and postcomposition operation `cochainConj`, and there the statement is the associativity
of composition of cochains.

Both induced maps of the bifunctor are special cases of `homMap` with an identity in the other
variable, and the naturality square and the two functor laws are each one application of
`homMap_comp` on either side. `homMap` is therefore never unfolded here.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m u v w

namespace AlgebraicGeometry.RingedSite

/-! ### The composition laws, at unequal site universes and an arbitrary module universe

These two lemmas need no relation between the site universes or the module universe: both sides
of each already live in the same universe, so nothing has to be absorbed to state them.  They
are therefore stated here in full generality, and the collapsed case `RingedSite.{u, u, u}` with
modules in `u` is the instance `v := u`, `w := u`, `m := u`. -/

section General

variable (X : RingedSite.{u, v, w})

/-- Applying a composite of morphisms of sheaves of modules to a section. -/
lemma comp_val_app_apply' {A B D : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : A ⟶ B) (ψ : B ⟶ D) (W : X.Cᵒᵖ) (x : A.val.obj W) :
    ((φ ≫ ψ).val.app W) x = (ψ.val.app W) ((φ.val.app W) x) := rfl

section Conj

variable {K K' K'' M M' M'' :
    CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Pre- and postcomposition compose: conjugating by `k` and `m` and then by `k'` and `m'` is
conjugating by `k' ≫ k` and `m ≫ m'`. -/
lemma cochainConj_comp (U : X.C) (k : K' ⟶ K) (k' : K'' ⟶ K') (m : M ⟶ M') (m' : M' ⟶ M'')
    {n : ℤ} (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U k' m' (cochainConj X U k m c) = cochainConj X U (k' ≫ k) (m ≫ m') c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, cochainConj_v, cochainConj_v]
  simp [Functor.map_comp]

end Conj

section HomMap

variable {K K' K'' M M' M'' :
    CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The induced maps of internal Hom complexes compose: `homMap k m` followed by
`homMap k' m'` is `homMap (k' ≫ k) (m ≫ m')`. -/
lemma homMap_comp (k : K' ⟶ K) (k' : K'' ⟶ K') (m : M ⟶ M') (m' : M' ⟶ M'') :
    homMap X k m ≫ homMap X k' m' = homMap X (k' ≫ k) (m ≫ m') := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply ((sheafHomComplex X K'' M'').sectionsEquiv U n).injective
  rw [HomologicalComplex.comp_f, homMap_f, homMap_f, homMap_f, comp_val_app_apply',
    sectionsEquiv_homMapHom, sectionsEquiv_homMapHom, sectionsEquiv_homMapHom,
    cochainConj_comp]

end HomMap

end General

variable (X : RingedSite.{u, u, u})

/-- The internal Hom complex of complexes of `O`-modules as a bifunctor, contravariant in its
source and covariant in its target. -/
noncomputable def sheafHomComplexBifunctor :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ where
  obj K :=
    { obj := fun M => (sheafHomComplex X K.unop M).obj
      map := fun m => homMap X (𝟙 K.unop) m
      map_id := fun M => homMap_id X K.unop M
      map_comp := fun m m' => by rw [homMap_comp, Category.comp_id] }
  map k :=
    { app := fun M => homMap X k.unop (𝟙 M)
      naturality := fun M M' m => by
        change homMap X (𝟙 _) m ≫ homMap X k.unop (𝟙 M') =
          homMap X k.unop (𝟙 M) ≫ homMap X (𝟙 _) m
        rw [homMap_comp, homMap_comp, Category.comp_id, Category.id_comp, Category.comp_id,
          Category.id_comp] }
  map_id K := NatTrans.ext (funext fun M => homMap_id X K.unop M)
  map_comp k k' := NatTrans.ext (funext fun M => by
    change homMap X (k'.unop ≫ k.unop) (𝟙 M) =
      homMap X k.unop (𝟙 M) ≫ homMap X k'.unop (𝟙 M)
    rw [homMap_comp, Category.comp_id])

/-- The internal Hom bifunctor has the internal Hom complexes as its values. -/
lemma sheafHomComplexBifunctor_obj_obj
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor X).obj (op K)).obj M = (sheafHomComplex X K M).obj := rfl

/-- The internal Hom bifunctor acts on a morphism of targets by postcomposition. -/
lemma sheafHomComplexBifunctor_obj_map
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    ((sheafHomComplexBifunctor X).obj (op K)).map m = homMap X (𝟙 K) m := rfl

/-- The internal Hom bifunctor acts on a morphism of sources by precomposition. -/
lemma sheafHomComplexBifunctor_map_app
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor X).map (op k)).app M = homMap X k (𝟙 M) := rfl

end AlgebraicGeometry.RingedSite

end
