module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.KFlatTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for a derived tensor product

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` such that
the map of Stacks 0DJ7 is an isomorphism at every point of `X'` and in every degree, which is
condition (1) of Stacks 0DJ8.  Then for every `E ∈ D(𝒪_X)` the same holds for the comparison

`L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'`.

This is Stacks 0DJA (1). For K-flat representatives of `E` and `K` the statement is
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_tensor_of_kFlat`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback`: if
  the map of Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point and in every degree, then
  so is the one at the comparison `L(g')^*(E ⊗^L K) ⟶ L(g')^*E ⊗^L K'`.

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace CategoryTheory

private theorem chase_nat {C : Type*} [Category C] {A B Cc Dd E F G H : C}
    (L : A ⟶ B) (U₂ : B ⟶ Cc) (m₂ : Cc ⟶ Dd) (U₁ : A ⟶ E) (m₁ : E ⟶ F) (du : F ⟶ G)
    (mv' : G ⟶ Dd) (du' : E ⟶ H) (mv : H ⟶ Cc) (mφ : H ⟶ G)
    (h79 : L ≫ U₂ = U₁ ≫ du' ≫ mv) (hnat : m₁ ≫ du = du' ≫ mφ) (hφ : mv ≫ m₂ = mφ ≫ mv') :
    L ≫ (U₂ ≫ m₂) = (U₁ ≫ m₁) ≫ du ≫ mv' := by
  rw [Category.assoc, reassoc_of% h79, hφ, reassoc_of% hnat]

private theorem fac_aux {C : Type*} [Category C] {A B Cc D E G : C} (p : A ⟶ B) [IsIso p]
    (u₁ : A ⟶ G) (u₂ : G ⟶ Cc) (i : E ≅ Cc) (q : B ⟶ D) (r : D ⟶ E)
    (hf : inv p ≫ u₁ ≫ u₂ ≫ i.inv = q ≫ r) : u₁ ≫ u₂ = (p ≫ q) ≫ r ≫ i.hom := by
  rw [Category.assoc, ← reassoc_of% hf]
  simp

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedPullbackTensor Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- Every object `E` of the derived category of `𝒪_X`-modules is isomorphic to the image of a
K-flat complex of `𝒪_X`-modules. -/
theorem exists_kFlat_iso (E : DerivedCategory
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)) :
    ∃ (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ), AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat
        X.toRingedSpace P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E) := by
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X.toRingedSpace
      (DerivedCategory.Q.objPreimage E)
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- The comparison `L(g')^*(E ⊗^L K) ⟶ L(g')^*E ⊗^L K'` is natural in `E` and in the triple
`(K, K', φ)`: for `u : E₁ ⟶ E₂` and maps `v : K₁ ⟶ K₂`, `v' : K₁' ⟶ K₂'` compatible with `φ₁` and
`φ₂`, the comparisons for `(E₁, K₁, K₁', φ₁)` and `(E₂, K₂, K₂', φ₂)` commute with the maps
induced by `u ⊗ v` and `L(g')^*u ⊗ v'`. -/
theorem btc_naturality {E₁ E₂ K₁ K₂ : DerivedCategory
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)}
    {K₁' K₂' : DerivedCategory
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace)}
    (u : E₁ ⟶ E₂) (v : K₁ ⟶ K₂) (v' : K₁' ⟶ K₂')
    (φ₁ : (derivedPullback g'.toLRSHom.toShHom).obj K₁ ⟶ K₁')
    (φ₂ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K₂')
    (hφ : (derivedPullback g'.toLRSHom.toShHom).map v ≫ φ₂ = φ₁ ≫ v') :
    (derivedPullback g'.toLRSHom.toShHom).map
        (((derivedTensorProductFunctor X.sheaf).map u).app K₁ ≫
          ((derivedTensorProductFunctor X.sheaf).obj E₂).map v) ≫
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom E₂ K₂ K₂' φ₂ =
    Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom E₁ K₁ K₁' φ₁ ≫
      ((derivedTensorProductFunctor X'.sheaf).map
          ((derivedPullback g'.toLRSHom.toShHom).map u)).app K₁' ≫
        ((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E₂)).map v' := by
  have h79 : (derivedPullback g'.toLRSHom.toShHom).map
        (((derivedTensorProductFunctor X.sheaf).map u).app K₁ ≫
          ((derivedTensorProductFunctor X.sheaf).obj E₂).map v) ≫
      (derivedPullbackTensorIso g'.toLRSHom.toShHom).hom.app (E₂, K₂) =
      (derivedPullbackTensorIso g'.toLRSHom.toShHom).hom.app (E₁, K₁) ≫
        ((derivedTensorProductFunctor X'.sheaf).map
          ((derivedPullback g'.toLRSHom.toShHom).map u)).app
            ((derivedPullback g'.toLRSHom.toShHom).obj K₁) ≫
        ((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E₂)).map
            ((derivedPullback g'.toLRSHom.toShHom).map v) :=
    (derivedPullbackTensorIso g'.toLRSHom.toShHom).hom.naturality
      (X := (E₁, K₁)) (Y := (E₂, K₂)) (u, v)
  have hnat := ((derivedTensorProductFunctor X'.sheaf).map
    ((derivedPullback g'.toLRSHom.toShHom).map u)).naturality φ₁
  have hφ' := ((Functor.map_comp _ _ _).symm.trans (congrArg
    ((derivedTensorProductFunctor X'.sheaf).obj
      ((derivedPullback g'.toLRSHom.toShHom).obj E₂)).map hφ)).trans (Functor.map_comp _ _ _)
  exact chase_nat _ _ _ _ _ _ _ _ _ _ h79 hnat hφ'

/-- **Stacks 0DJA (1).** For a cartesian square of schemes, if the map of Stacks 0DJ7 at
`(K, K', φ)` is an isomorphism at every point of `X'` and in every degree, then so is the one at
the comparison `L(g')^*(E ⊗^L K) ⟶ L(g')^*E ⊗^L K'`, for every `E` in `D(𝒪_X)`. -/
@[stacks 0DJA "(1)"]
theorem isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback
    (hpb : IsPullback g' f' f g) (E K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj K')
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom E K K' φ) x' n) := by
  obtain ⟨P, hP, ⟨eE⟩⟩ := exists_kFlat_iso E
  obtain ⟨N, hN, ⟨eK⟩⟩ := exists_kFlat_iso K
  have hpcN := isIso_derivedPullbackNatTrans_app g'.toLRSHom.toShHom N hN
  obtain ⟨W, a, s, hs, hfac⟩ := DerivedCategory.left_fac
    (X := (pullbackComplex g'.toLRSHom.toShHom).obj N) (Y := DerivedCategory.Q.objPreimage K')
    (@inv _ _ _ _ ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N) hpcN ≫
      (derivedPullback g'.toLRSHom.toShHom).map eK.hom ≫ φ ≫
        (DerivedCategory.Q.objObjPreimageIso K').inv)
  let ψ₀ : DerivedCategory.Q.obj W ≅ K' :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K'
  have hφ₀ : (derivedPullback g'.toLRSHom.toShHom).map eK.hom ≫ φ =
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a) ≫
        ψ₀.hom :=
    @fac_aux _ _ _ _ _ _ _ _ ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N) hpcN _ _
      (DerivedCategory.Q.objObjPreimageIso K') _ _ hfac
  have hK : ∀ (x' : X') (m : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj W)
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a) x' m) := by
    intro x' m
    refine (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ ψ₀.hom
      ψ₀.isIso_hom x' m).1 ?_
    refine isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ hφ₀.symm x' m ?_
    exact (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w
      _ _ _ eK.hom eK.isIso_hom φ x' m).2 (h x' m)
  have hnat := btc_naturality (g' := g') eE.hom eK.hom ψ₀.hom
    ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a) φ hφ₀
  have hθ : IsIso (((derivedTensorProductFunctor X.sheaf).map eE.hom).app
      (DerivedCategory.Q.obj N) ≫ ((derivedTensorProductFunctor X.sheaf).obj E).map eK.hom) :=
    (((derivedTensorProductFunctor X.sheaf).mapIso eE).app (DerivedCategory.Q.obj N) ≪≫
      ((derivedTensorProductFunctor X.sheaf).obj E).mapIso eK).isIso_hom
  refine (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w _ _ _ _ hθ _ x' n).1 ?_
  refine isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ hnat x' n ?_
  exact (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ _
    (((derivedTensorProductFunctor X'.sheaf).mapIso
      ((derivedPullback g'.toLRSHom.toShHom).mapIso eE)).app (DerivedCategory.Q.obj W) ≪≫
      ((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).mapIso ψ₀).isIso_hom x' n).2
      (isIso_baseChangeCohomologyMap_tensor_of_kFlat hpb P N hP hN W a hK x' n)

end AlgebraicGeometry
