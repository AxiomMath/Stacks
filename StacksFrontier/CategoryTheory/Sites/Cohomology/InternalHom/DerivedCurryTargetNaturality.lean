module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality

/-! # Naturality of Stacks 08JA and 08J8 in the target variable, and Stacks 08J8 as an adjunction

Let `(C, O)` be a ringed site. This file completes the functoriality of the
tensor–internal-Hom bijection of **Stacks 08J8**,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, by proving it natural in its **target**
variable, and bundles the result as an adjunction

`- ⊗^L_O B ⊣ RSheafHom(B, -)`

on `D(O)`, for every object `B`.

The target variable is the covariant one, and the step it needs is the target half of the
naturality of **Stacks 0A94** at arbitrary objects of `D(O)`. That step is *not* a mirror of the
source one. The source half of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality` reduces an
arbitrary morphism of `D(O)` to morphisms of complexes by the calculus of fractions, repairing
the apex of the fraction to be K-flat with Stacks 06YS; in the target variable the apex would
have to be repaired to be K-injective and the legs point the other way, so that argument does
not transfer.

It is also not needed. Both target representatives are already K-injective — Stacks 08JA
globally is set up at a K-flat representative of the source and a K-injective representative of
the target — and every morphism of `D(O)` into the class of a K-injective complex *is* the class
of a morphism of complexes, by
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`. So in the target variable the
reduction to morphisms of complexes is immediate and no fraction, and no second resolution, is
involved. This is a strictly shorter route than the source one, and it is the whole content of
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived_snd` below.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction`: **Stacks 08J8 as an
  adjunction.** For an object `B` of `D(O)`, the derived tensor product with `B` is left adjoint
  to the derived internal Hom out of `B`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_snd`:
  Stacks 08JA at a K-flat source and K-injective targets is natural in the target for a morphism
  of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived_snd`:
  the same for an arbitrary morphism of `D(O)` between the classes of the two K-injective
  targets.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap`:
  **Stacks 08JA globally is natural in the target variable**, at arbitrary objects of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target`: **Stacks 08J8 is
  natural in its target variable.**

## What this file does not contain

The **middle** variable of Stacks 08J8 is not treated. Naturality there is naturality of
`derivedCurryHomEquiv` in `B`, and it is not a clause of the adjunction below: the adjunction is
stated at a fixed `B`, and a morphism `B' ⟶ B` moves both the left and the right adjoint, so the
statement would be a compatibility of two adjunctions rather than a naturality square for one.
The object-level input for it is available — it is the middle clause of
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` — but the morphism-group statement is not
derived here.

Nothing here carries the tag 08J9; the object-level naturality of the derived currying
isomorphism is tagged where it is proved, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality`.

## Implementation notes

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived-internal-Hom cluster.

The left adjoint is `(Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj B`, which is
`- ⊗^L_O B`; its action on morphisms unfolds to
`((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B`, which is exactly the
shape in which the source clause is stated, so the left-naturality field of
`CategoryTheory.Adjunction.CoreHomEquiv` is the source clause and needs no bridging
lemma.

The hom-set equivalence of the adjunction is given as an explicit `Equiv` rather than as
`(derivedCurryHomEquiv X A B Z).toEquiv.symm`, so that the *inverse* appearing in the
left-naturality field is syntactically `derivedCurryHomEquiv` itself rather than a double
`Equiv.symm`; normalising such a double symm away at these arguments exhausts the recursion
depth, in `rw`, `simp` and `dsimp` alike. For the same reason the left-naturality field is
closed by `rw` with the source clause rather than by `exact`: the two statements are
definitionally equal but not syntactically so, and the defeq check is the one that
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual` records as
exhausting the recursion depth, which `rw` avoids by matching the two sides. The
right-naturality field needs no such care and is closed by `exact`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The target-variable half of
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality`. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_snd
    {A I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    [I.IsKInjective] [I'.IsKInjective] (m : I ⟶ I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I' hA
        (derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj A)) (DerivedCategory.Q.map m) x) =
      derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x ≫ DerivedCategory.Q.map m := by
  have h := derivedSheafHomGlobalSectionsEquivOfKFlat_naturality X hA hA (𝟙 A) m x
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- **The identification of Stacks 08JA at a K-flat source and a K-injective target is natural
in the target for an arbitrary morphism of `D(O)`**, not only for a morphism of complexes.

No calculus of fractions is needed here, unlike in the source variable: the target of the
morphism is the class of the K-injective complex `I'`, so the morphism is already the class of a
morphism of complexes by `exists_Q_map_eq_of_isKInjective`, and
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_snd` applies directly. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived_snd
    {A I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    [I.IsKInjective] [I'.IsKInjective]
    (g : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I' hA
        (derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj A)) g x) =
      derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x ≫ g := by
  obtain ⟨m, rfl⟩ := exists_Q_map_eq_of_isKInjective X g
  exact derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_snd X hA m x

/-- **Stacks 08JA globally is natural in the target variable, for an arbitrary morphism of
`D(O)`**: the identification of the degree-zero global hypercohomology of `RSheafHom(A, W)`
with `Hom_{D(O)}(A, W)` carries the map induced by `v : W ⟶ W'` to postcomposition with `v`.

This is the target half of the naturality of Stacks 0A94 read at arbitrary objects of `D(O)`:
the two sides are compared at the chosen K-flat representative of the source and the chosen
K-injective representatives of the two targets, where it is
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived_snd`. -/
@[stacks 08JA "global sections, naturality in the target variable"]
theorem derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap
    {A W W' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (v : W ⟶ W')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj W)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X A W' (derivedHomGlobalMap X (𝟙 A) v x) =
      derivedSheafHomGlobalSectionsEquiv X A W x ≫ v := by
  have ht : derivedHomGlobalMap X (kFlatModelIso X A).hom (kInjectiveModelIso X W').inv
        (derivedHomGlobalMap X (𝟙 A) v x) =
      derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj (kFlatModel X A)))
        ((kInjectiveModelIso X W).hom ≫ v ≫ (kInjectiveModelIso X W').inv)
        (derivedHomGlobalMap X (kFlatModelIso X A).hom (kInjectiveModelIso X W).inv x) := by
    have h1 := derivedHomGlobalMap_comp X (𝟙 A) (kFlatModelIso X A).hom v
      (kInjectiveModelIso X W').inv
    have h2 := derivedHomGlobalMap_comp X (kFlatModelIso X A).hom
      (𝟙 (DerivedCategory.Q.obj (kFlatModel X A))) (kInjectiveModelIso X W).inv
      ((kInjectiveModelIso X W).hom ≫ v ≫ (kInjectiveModelIso X W').inv)
    rw [Category.comp_id] at h1
    simp only [Category.id_comp, Iso.inv_hom_id_assoc] at h2
    exact (ConcreteCategory.congr_hom h1 x).trans (ConcreteCategory.congr_hom h2 x).symm
  rw [derivedSheafHomGlobalSectionsEquiv_eq_globalMap,
    derivedSheafHomGlobalSectionsEquiv_eq_globalMap, ht,
    derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived_snd X
      (isKFlat_kFlatModel X A)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
    (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)] in
/-- With an identity in the source variable, `derivedHomGlobalMap` is the map induced by the
derived internal Hom in the target variable alone. -/
theorem derivedHomGlobalMap_snd_eq
    {L M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (v : M ⟶ M') :
    derivedHomGlobalMap X (𝟙 L) v =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj (op L)).map v)) := by
  dsimp only [derivedHomGlobalMap]
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- **Naturality of the derived currying isomorphism in the target variable alone**: the
three-variable square of Stacks 08J9 with identities in the source and the middle. -/
theorem derivedCurryIso_natural_thd
    {A B Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (w : Z ⟶ Z') :
    ((derivedSheafHomBifunctor X).obj (op A)).map
          (((derivedSheafHomBifunctor X).obj (op B)).map w) ≫
        (derivedCurryIso X A B Z').hom =
      (derivedCurryIso X A B Z).hom ≫
        ((derivedSheafHomBifunctor X).obj
          (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B))).map w := by
  have h := derivedCurryIso_natural X (𝟙 A) (𝟙 B) w
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- **Naturality of the derived currying equivalence of Stacks 08J9 on degree-zero global
hypercohomology, in the target variable.** -/
theorem derivedCurryGlobalEquiv_naturality_target
    {A B Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (w : Z ⟶ Z')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    derivedCurryGlobalEquiv X A B Z'
        (derivedHomGlobalMap X (𝟙 A)
          (((derivedSheafHomBifunctor X).obj (op B)).map w) x) =
      derivedHomGlobalMap X
          (𝟙 (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B)) w
        (derivedCurryGlobalEquiv X A B Z x) := by
  have hsq : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op A)).map
              (((derivedSheafHomBifunctor X).obj (op B)).map w))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X A B Z').hom) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X A B Z).hom) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj
              (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj
                B))).map w)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      derivedCurryIso_natural_thd]
  rw [derivedCurryGlobalEquiv_apply, derivedCurryGlobalEquiv_apply, derivedHomGlobalMap_snd_eq,
    derivedHomGlobalMap_snd_eq]
  exact ConcreteCategory.congr_hom hsq x

/-- **Stacks 08J8 is natural in its target variable.** Postcomposing a morphism
`h : A ⟶ RSheafHom(B, Z)` with `RSheafHom(B, w)`, for `w : Z ⟶ Z'`, corresponds under the
tensor–internal-Hom bijection `derivedCurryHomEquiv` to postcomposing the morphism
`A ⊗^L_O B ⟶ Z` matched with `h` by `w`.

The bijection is the derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology with both sides identified with morphism groups by Stacks 08JA, so this is the
object-level naturality `derivedCurryIso_natural` together with the naturality of Stacks 08JA
in its target variable, `derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap`. -/
@[stacks 08J8 "the tensor-internal-Hom bijection is natural in the target variable"]
theorem derivedCurryHomEquiv_naturality_target
    {A B Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (w : Z ⟶ Z')
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurryHomEquiv X A B Z'
        (h ≫ ((derivedSheafHomBifunctor X).obj (op B)).map w) =
      derivedCurryHomEquiv X A B Z h ≫ w := by
  obtain ⟨x, rfl⟩ : ∃ x, derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z) x = h :=
    ⟨_, (derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).apply_symm_apply h⟩
  rw [← derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap X
      (((derivedSheafHomBifunctor X).obj (op B)).map w) x,
    derivedCurryHomEquiv_globalSections, derivedCurryHomEquiv_globalSections,
    derivedCurryGlobalEquiv_naturality_target,
    derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap]

/-- `derivedCurryHomEquiv_naturality_target` read through the inverse bijection: the transpose
of `f ≫ w` is the transpose of `f` followed by `RSheafHom(B, w)`. -/
theorem derivedCurryHomEquiv_symm_naturality_target
    {A B Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (w : Z ⟶ Z')
    (f : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B ⟶ Z) :
    (derivedCurryHomEquiv X A B Z').symm (f ≫ w) =
      (derivedCurryHomEquiv X A B Z).symm f ≫
        ((derivedSheafHomBifunctor X).obj (op B)).map w := by
  apply (derivedCurryHomEquiv X A B Z').injective
  rw [AddEquiv.apply_symm_apply, derivedCurryHomEquiv_naturality_target,
    AddEquiv.apply_symm_apply]

/-- **Stacks 08J8 as an adjunction.** For an object `B` of `D(O)`, the derived tensor product
with `B` is left adjoint to the derived internal Hom out of `B`:

`Hom_{D(O)}(A ⊗^L_O B, Z) ≅ Hom_{D(O)}(A, RSheafHom(B, Z))`,

naturally in `A` and `Z`. The bijection is `derivedCurryHomEquiv`, its naturality in `A` is
`derivedCurryHomEquiv_naturality_source` and its naturality in `Z` is
`derivedCurryHomEquiv_naturality_target`. -/
@[stacks 08J8 "the tensor-internal-Hom bijection as an adjunction, at a fixed middle object"]
def derivedTensorSheafHomAdjunction
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj B ⊣
      (derivedSheafHomBifunctor X).obj (op B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A Z =>
        { toFun := (derivedCurryHomEquiv X A B Z).symm
          invFun := derivedCurryHomEquiv X A B Z
          left_inv := (derivedCurryHomEquiv X A B Z).apply_symm_apply
          right_inv := (derivedCurryHomEquiv X A B Z).symm_apply_apply }
      homEquiv_naturality_left_symm := by
        intro A' A Z u h
        dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map, Equiv.coe_fn_symm_mk]
        rw [derivedCurryHomEquiv_naturality_source X u h]
      homEquiv_naturality_right := by
        intro A Z Z' f w
        dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map, Equiv.coe_fn_mk]
        exact derivedCurryHomEquiv_symm_naturality_target X w f }

end AlgebraicGeometry.RingedSite

end
