module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNatTransDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralDirectImagePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeMapBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeReduction

/-!
# The canonical map of Tag 0F1J against the projection map, given base change

Let

```
X' <-h-- Y
|f'      |e
S' <-g-- T
```

be a commutative square of schemes. The canonical map of [Stacks, Tag 0F1J] on
`D(-_étale, Λ)`,

`A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)`,

is by construction the base change map `(f')⁻¹Rg_*F ⟶ Rh_*e⁻¹F` in the second factor followed by
the projection map `A ⊗^L_Λ Rh_*B ⟶ Rh_*(h⁻¹A ⊗^L_Λ B)` of `h` at `B = e⁻¹F`. This file proves:

* **Base change on `D(-_étale, ℤ/m)` from the derived base change condition.** If derived base
  change holds for sheaves annihilated by `m` along `f : X ⟶ S`
  (`Stacks.EtaleCohomology.BaseChangeOverField.DerivedBaseChangeHolds f m`, the condition
  `BC(f, m, q)` of [Stacks, Tag 0F02] in every degree), then for every pair of cartesian squares
  over `f` with `g` quasi-compact and quasi-separated, the base change map of
  `D(-_étale, ℤ/m)` is an isomorphism at every object of `D⁺`
  (`isIso_baseChangeMap_app_of_derivedBaseChangeHolds`). For `f : X ⟶ Spec K` and `m`
  invertible in `K` this condition is the content of [Stacks, Tag 0F1I].
* **The canonical map against the projection map.** Wherever the base change map is invertible,
  the canonical map of Tag 0F1J is invertible exactly when the projection map of `h` at
  `(A, e⁻¹F)` is (`isIso_tensorBaseChangeMap_iff_isIso_projectionMap`).

Together: in the setting of Tag 0F1J, granted the base change of Tag 0F1I for the scheme `X`
itself, the statement of Tag 0F1J is the projection formula for `h` at `(p⁻¹E, e⁻¹F)`
(`isIso_tensorBaseChangeMap_iff_isIso_projectionMap_of_field`).

## Main definitions

* `Stacks.EtaleCohomology.EtaleCoefficients.projectionMap` — the projection map
  `A ⊗^L_Λ Rh_*B ⟶ Rh_*(h⁻¹A ⊗^L_Λ B)` on `D(-_étale, Λ)`.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isIso_baseChangeMap_app_of_derivedBaseChangeHolds`
* `isIso_baseChangeMap_app_of_isIntegralHom` — base change along an integral morphism on
  `D⁺(-_étale, ℤ/m)`, the finite base change the last paragraph of the source's proof uses.
* `isIso_tensorBaseChangeMap_iff_isIso_projectionMap`
* `isIso_tensorBaseChangeMap_iff_isIso_projectionMap_of_field`
* `isIso_tensorBaseChangeMap_of_field_of_isIso_projectionMap_single`
  — Tag 0F1J, given base change over `X` and the projection formula for `h` at a flat sheaf and
  a sheaf placed in single degrees. Not registered: both are explicit arguments.

## Implementation notes

The base change maps on both sides of the bridge `isIso_baseChangeMap_app_iff` are built on the
standard model of the derived category (line 394 of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean`),
which fixes the model here.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` is stated for the standard model of the derived category, at line 394 of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean`
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing)

/-! ### Annihilation by `m` on the derived categories -/

section Annihilation

variable (m : ℕ) (X : Scheme.{u})

/-- A morphism `m • 𝟙 G` is zero if it is after applying a faithful additive functor. -/
private theorem nsmul_id_eq_zero_of_map {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] [Φ.Faithful] {G : C} (h : m • 𝟙 (Φ.obj G) = 0) :
    m • 𝟙 G = 0 := by
  apply Φ.map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, h, Functor.map_zero]

/-- A sheaf of `ℤ/mℤ̲`-modules is annihilated by `m`. -/
theorem nsmul_id_sheafOfModules_eq_zero
    (M : SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X)) : m • 𝟙 M = 0 :=
  nsmul_id_eq_zero_of_map m (etaleToSheaf (ULift.{u + 1} (ZMod m)) X)
    ((mem_essImage_etaleToSheaf_iff m X _).1 ((etaleToSheaf _ X).obj_mem_essImage M))

/-- Every object of `D(X_étale, ℤ/m)` is annihilated by `m`. -/
theorem nsmul_id_derivedModules_eq_zero (K : DerivedModules (ULift.{u + 1} (ZMod m)) X) :
    m • 𝟙 K = 0 :=
  nsmul_id_eq_zero_of_iso m (DerivedCategory.Q.objObjPreimageIso K) <|
    nsmul_id_map_eq_zero m _ <| HomologicalComplex.hom_ext _ _ fun i => by
      rw [HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f,
        HomologicalComplex.zero_f_apply]
      exact nsmul_id_sheafOfModules_eq_zero m X _

/-- Every bounded below object of `D(X_étale, ℤ/m)` is annihilated by `m`. -/
theorem nsmul_id_derivedModulesPlus_eq_zero
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X))) :
    m • 𝟙 K = 0 :=
  nsmul_id_eq_zero_of_map m DerivedCategory.Plus.ι (nsmul_id_derivedModules_eq_zero m X _)

/-- The cohomology sheaves of the underlying complex of abelian sheaves of a bounded below object
of `D(X_étale, ℤ/m)` are annihilated by `m`. -/
theorem nsmul_eq_zero_homology_forgetDerivedPlus
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X)))
    (q : ℤ) (U : X.Etale)
    (x : ToType ((((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) X).obj K)).obj.obj (Opposite.op U)))) :
    (m : ℤ) • x = 0 := by
  have h := nsmul_id_map_eq_zero m (DerivedCategory.Plus.homologyFunctor _ q)
    (nsmul_id_map_eq_zero m (forgetDerivedPlus (ULift.{u + 1} (ZMod m)) X)
      (nsmul_id_derivedModulesPlus_eq_zero m X K))
  rw [natCast_zsmul]
  exact (nsmul_id_eq_zero_iff m _).1 h (Opposite.op U) x

end Annihilation

/-! ### Base change on `D(-_étale, ℤ/m)` from the derived base change condition -/

section BaseChange

open Stacks.EtaleCohomology.BaseChangeOverField

/-- **Base change on `D(-_étale, ℤ/m)` from the derived base change condition.** Let `f : X ⟶ S`
be a morphism of schemes along which derived base change holds for abelian sheaves annihilated by
`m` (`DerivedBaseChangeHolds f m`). For cartesian squares

```
X  <-p-- X' <-h-- Y
|f       |f'      |e
S  <-s-- S' <-g-- T
```

with `g` quasi-compact and quasi-separated, the base change map `(f')⁻¹Rg_*F ⟶ Rh_*e⁻¹F` of
`D(-_étale, ℤ/m)` is an isomorphism at every `F ∈ D⁺(T_étale, ℤ/m)`.

The map is invertible exactly when the abelian base change map is invertible at the underlying
complex of abelian sheaves of `F` (`isIso_baseChangeMap_app_iff`); that one is a shift-compatible
transformation between triangulated functors preserving `D^{≥k}`, so it is invertible at the
bounded below complex as soon as it is at each of its cohomology sheaves placed in degree zero,
which are annihilated by `m`. -/
theorem isIso_baseChangeMap_app_of_derivedBaseChangeHolds (m : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : DerivedBaseChangeHolds f m) {S' X' T Y : Scheme.{u}} (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w).app
      (DerivedCategory.Plus.ι.obj K)) := by
  rw [isIso_baseChangeMap_app_iff]
  obtain ⟨b, hb⟩ := K.property
  have := commShift_smallEtaleDerivedBaseChangeAb f' g h e sq.w
  have hUK : ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K).IsGE b :=
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) T).isGE_mapDerivedCategoryPlus_obj K b
      ((DerivedCategory.Plus.isGE_ι_obj_iff K b).1 hb)
  refine DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single
    (smallEtaleDerivedBaseChangeAb f' g h e sq.w) ?_ ?_ _ b hUK fun q => ?_
  · intro L k hL
    have := hL
    have := (smallEtalePushforwardAb g).isGE_rightDerivedFunctorPlus_obj L k
    exact (smallEtalePullbackAb f').isGE_rightDerivedFunctorPlus_obj _ k
  · intro L k hL
    have := hL
    have := (smallEtalePullbackAb e).isGE_rightDerivedFunctorPlus_obj L k
    exact (smallEtalePushforwardAb h).isGE_rightDerivedFunctorPlus_obj _ k
  · exact hf s p f' hp g h e sq _ (nsmul_eq_zero_homology_forgetDerivedPlus m T K q)

/-- `isIso_baseChangeMap_app_of_derivedBaseChangeHolds` at a sheaf of `ℤ/mℤ̲`-modules placed in a
single degree. -/
theorem isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds (m : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : DerivedBaseChangeHolds f m) {S' X' T Y : Scheme.{u}} (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)) (j : ℤ) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w).app
      ((DerivedCategory.singleFunctor _ j).obj G)) :=
  (NatTrans.isIso_app_iff_of_iso (baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w)
    (X := DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ j).obj G))
    (Y := (DerivedCategory.singleFunctor _ j).obj G)
    ((DerivedCategory.Plus.singleFunctorιIso _ j).app G)).1
    (isIso_baseChangeMap_app_of_derivedBaseChangeHolds m f hf s p f' hp g h e sq _)

/-- **Base change along an integral morphism on `D⁺(-_étale, ℤ/m)`.** For a cartesian square

```
Y  <-π'-- Y'
|e        |e'
T  <-π--- T'
```

with `π` integral, the base change map `e⁻¹Rπ_* ⟶ Rπ'_*(e')⁻¹` of `D(-_étale, ℤ/m)` is an
isomorphism at every object of `D⁺(T'_étale, ℤ/m)`: by `isIso_baseChangeMap_app_iff` it is the
abelian one, which is invertible by
`Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom` (Stacks 04C2 and
0EYP). -/
theorem isIso_baseChangeMap_app_of_isIntegralHom (m : ℕ) {Y Y' T T' : Scheme.{u}} (e : Y ⟶ T)
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq : IsPullback π' e' e π) [IsIntegralHom π]
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T').O))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) e π π' e' sq.w).app
      (DerivedCategory.Plus.ι.obj K)) := by
  rw [isIso_baseChangeMap_app_iff]
  have := isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom e π π' e' sq
  infer_instance

end BaseChange

/-! ### The canonical map against the projection map -/

section Projection

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The projection map** `A ⊗^L_Λ Rh_*B ⟶ Rh_*(h⁻¹A ⊗^L_Λ B)` on `D(-_étale, Λ)` of a morphism
of schemes `h : Y ⟶ X'`: the adjoint of `h⁻¹(A ⊗^L Rh_*B) ≅ h⁻¹A ⊗^L h⁻¹Rh_*B ⟶ h⁻¹A ⊗^L B`
(Stacks 07A4 and the counit of `h⁻¹ ⊣ Rh_*`). -/
def projectionMap {X' Y : Scheme.{u}} (h : Y ⟶ X') (A : DerivedModules Λ X')
    (B : DerivedModules Λ Y) :
    ((tensor Λ X').obj A).obj ((pushforward Λ h).obj B) ⟶
      (pushforward Λ h).obj (((tensor Λ Y).obj ((pullback Λ h).obj A)).obj B) :=
  Stacks.Cohomology.AbstractKunnethMap.projectionMap (Functor.uncurry.obj (tensor Λ X'))
    (Functor.uncurry.obj (tensor Λ Y)) (adjunction Λ h) (pullbackTensorIso Λ h).hom A B

variable {X' S' T Y : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The canonical map of Tag 0F1J is the base change map followed by the projection map**: at
`(A, F)` it is `A ⊗^L` of the base change map `(f')⁻¹Rg_*F ⟶ Rh_*e⁻¹F`, followed by the
projection map of `h` at `(A, e⁻¹F)`. -/
theorem tensorBaseChangeMap_eq (A : DerivedModules Λ X') (F : DerivedModules Λ T) :
    tensorBaseChangeMap Λ f' g h e w A F =
      ((tensor Λ X').obj A).map ((baseChangeMap Λ f' g h e w).app F) ≫
        projectionMap Λ h A ((pullback Λ e).obj F) := by
  simp only [tensorBaseChangeMap, Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap,
    projectionMap, baseChangeMap]
  congr 1
  simp [Functor.uncurry_obj_map]

/-- **The canonical map of Tag 0F1J against the projection map.** Where the base change map
`(f')⁻¹Rg_*F ⟶ Rh_*e⁻¹F` is invertible, the canonical map
`A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)` is invertible exactly when the projection map
`A ⊗^L_Λ Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)` of `h` is. -/
theorem isIso_tensorBaseChangeMap_iff_isIso_projectionMap (A : DerivedModules Λ X')
    (F : DerivedModules Λ T) (hbc : IsIso ((baseChangeMap Λ f' g h e w).app F)) :
    IsIso (tensorBaseChangeMap Λ f' g h e w A F) ↔
      IsIso (projectionMap Λ h A ((pullback Λ e).obj F)) := by
  rw [tensorBaseChangeMap_eq]
  exact isIso_comp_left_iff _ _

end Projection

/-! ### In the setting of Tag 0F1J -/

section Field

open Stacks.EtaleCohomology.BaseChangeOverField

/-- **In the setting of Tag 0F1J, granted base change over `X`, the canonical map is the projection
map.** Let `K` be a field, `n ≥ 1`, `X ⟶ Spec(K)`, `S' ⟶ Spec(K)`, `X' = X ×_{Spec(K)} S'` with
projections `p` and `f'`, `g : T ⟶ S'` quasi-compact and quasi-separated, and
`Y = X' ×_{S'} T` with projections `h` and `e`. If derived base change holds along `X ⟶ Spec(K)`
for sheaves annihilated by `n` (for `n` invertible in `K` this is [Stacks, Tag 0F1I] for `X`), then
for every `A ∈ D(X'_étale, ℤ/n)` and `F ∈ D⁺(T_étale, ℤ/n)` the canonical map

`A ⊗^L_{ℤ/n} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_{ℤ/n} e⁻¹F)`

is an isomorphism exactly when the projection map
`A ⊗^L_{ℤ/n} Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹A ⊗^L_{ℤ/n} e⁻¹F)` of `h` is. -/
theorem isIso_tensorBaseChangeMap_iff_isIso_projectionMap_of_field (k : Type u) [Field k]
    (n : ℕ) {X X' S' T Y : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (s : S' ⟶ Spec (.of k))
    (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX n) (A : DerivedModules (ULift.{u + 1} (ZMod n)) X')
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) T).O))) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w A
        (DerivedCategory.Plus.ι.obj F)) ↔
      IsIso (projectionMap (ULift.{u + 1} (ZMod n)) h A
        ((pullback (ULift.{u + 1} (ZMod n)) e).obj (DerivedCategory.Plus.ι.obj F))) :=
  isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w A _
    (isIso_baseChangeMap_app_of_derivedBaseChangeHolds n πX hBC s p f' hX' g h e hY F)

/-- **[Stacks, Tag 0F1J], given base change over `X` and the projection formula for `h` at single
objects.** In the setting of Tag 0F1J (`K` a field, `n ≥ 1` invertible in `K`,
`X' = X ×_{Spec(K)} S'`, `g : T ⟶ S'` quasi-compact and quasi-separated, `Y = X' ×_{S'} T`), let
`E ∈ D^+(X_étale, ℤ/nℤ)` have Tor amplitude in `[a, ∞]` and `F ∈ D^+(T_étale, ℤ/nℤ)`. Suppose

* `hBC`: derived base change holds along `X ⟶ Spec(K)` for sheaves annihilated by `n` (for this
  `X`, the content of [Stacks, Tag 0F1I]);
* `hproj`: for every flat sheaf of `ℤ/nℤ`-modules `M` on `X_étale` and every sheaf of
  `ℤ/nℤ`-modules `G` on `T_étale`, placed in single degrees, the projection map
  `p⁻¹M ⊗^L Rh_*(e⁻¹G) ⟶ Rh_*(h⁻¹p⁻¹M ⊗^L e⁻¹G)` of `h` is an isomorphism.

Then the canonical map `p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)` is an
isomorphism. The case of single objects of the canonical map is `hproj` by
`isIso_tensorBaseChangeMap_iff_isIso_projectionMap` and `hBC`, and the rest is
`isIso_tensorBaseChangeMap_of_isIso_single_of_field`. The source proves `hproj` in the last two
paragraphs of its proof, from Tags 03SA, 09Z1, 09Z7, 0959, 0F0G and [Stacks, Tag 0F1I] for the
finite `X`-schemes `X_i`. -/
theorem isIso_tensorBaseChangeMap_of_field_of_isIso_projectionMap_single (k : Type u) [Field k]
    (n : ℕ) [NeZero n] (hn : IsUnit (n : k)) {X X' S' T Y : Scheme.{u}} (πX : X ⟶ Spec (.of k))
    (s : S' ⟶ Spec (.of k)) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g]
    [QuasiSeparated g] (hBC : DerivedBaseChangeHolds πX n)
    (hproj : ∀ (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod n)) X).O)),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
        (O := (ringedTopos (ULift.{u + 1} (ZMod n)) X).O) M →
      ∀ (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod n)) T).O)) (i j : ℤ),
      IsIso (projectionMap (ULift.{u + 1} (ZMod n)) h
        ((pullback (ULift.{u + 1} (ZMod n)) p).obj ((DerivedCategory.singleFunctor _ i).obj M))
        ((pullback (ULift.{u + 1} (ZMod n)) e).obj ((DerivedCategory.singleFunctor _ j).obj G))))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (hE : ∃ c : ℤ, E.IsGE c) (a : ℤ)
    (hEa : HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (hF : ∃ b : ℤ, F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  refine isIso_tensorBaseChangeMap_of_isIso_single_of_field k n hn πX s p f' hX' g h e hY
    (fun M hM G i j => ?_) E hE a hEa F hF
  have hbc := isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds n πX hBC s p f'
    hX' g h e hY G j
  exact (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _ hbc).2
    (hproj M hM G i j)

end Field

end Stacks.EtaleCohomology.EtaleCoefficients

end
