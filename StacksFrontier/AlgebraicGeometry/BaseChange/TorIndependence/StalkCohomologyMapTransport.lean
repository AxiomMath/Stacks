module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap

/-!
# The pointwise base-change map depends on its datum only up to isomorphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes. The datum the pointwise base-change map of Stacks 0DJ7 is
built from is a triple `(K, K', φ)` with `K` in `D(𝒪_X)`, `K'` in `D(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`. This module shows that the invertibility of that map — condition (1) of
Stacks 0DJ8 — is unchanged when the triple is replaced by an isomorphic one, in either
argument:

* replacing `K` by an isomorphic `K₂` and `φ` by `L(g')^*θ ≫ φ` for an isomorphism
  `θ : K₁ ≅ K₂`;
* replacing `K'` by an isomorphic `K''` and `φ` by `φ ≫ ψ` for an isomorphism `ψ : K' ≅ K''`.

The second is immediate from `AlgebraicGeometry.baseChangeCohomologyMap_comp`, the naturality of
the map in the target. The first is not: the *source* of the map of Stacks 0DJ7 at `(K, K', φ)`
is `𝒪_{X', x'} ⊗_{𝒪_{X, x} ⊗ 𝒪_{S', s'}} H^n(K_x ⊗^L_{𝒪_{S, s}} 𝒪_{S', s'})`, so a morphism of
the source has to be carried through the derived base change of the stalk and through the
ordinary tensor product over `𝒪_{X,x} ⊗ 𝒪_{S',s'}`. The functoriality of the middle object is
built here, as `RingTheory.TorIndependence.baseChangeCohomologyFunctor`.

Both statements are unconditional: no flatness, cartesianness, Tor independence or
quasi-coherence is used, and the square need only commute.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologyMapHom`: the map
  `H^n(K₁ ⊗^L_R R') ⟶ H^n(K₂ ⊗^L_R R')` induced by `θ : K₁ ⟶ K₂`, as a map of
  `A ⊗_R R'`-modules.
* `RingTheory.TorIndependence.baseChangeCohomologyFunctor`: the resulting functor
  `D(A) ⥤ ModuleCat (A ⊗_R R')`, whose object part is
  `RingTheory.TorIndependence.baseChangeCohomology`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_of_isIso_source`: for an isomorphism
  `θ : K₁ ⟶ K₂` in `D(𝒪_X)`, the map of Stacks 0DJ7 at `(K₁, K', L(g')^*θ ≫ φ)` is invertible
  exactly when the one at `(K₂, K', φ)` is.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_of_isIso_target`: for an isomorphism
  `ψ : K' ⟶ K''` in `D(𝒪_{X'})`, the map at `(K, K'', φ ≫ ψ)` is invertible exactly when the
  one at `(K, K', φ)` is.

## Implementation notes

`RingTheory.TorIndependence.baseChangeCohomology` is the cohomology of the derived base change
with one further action installed, and that action is pinned only by
`RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul` and
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`; so the `A ⊗_R R'`-linearity
of the induced map is proved from those two equations on the generators `a ⊗ 1` and `1 ⊗ r` of
the tensor product, and not by transporting a known linear map.

The geometric statements are proved by exhibiting the map of Stacks 0DJ7 at
`(K₁, K', L(g')^*θ ≫ φ)` as the extension of scalars of
`baseChangeCohomologyMapHom` followed by the map at `(K₂, K', φ)`. That factorization is read
off the unique characterization of the map on pure tensors `1 ⊗ m`, using the naturality of the
comparison of Stacks 065Z and the naturality of
`AlgebraicGeometry.derivedPullbackStalkIso` in the complex.

The model of the derived category is free: the statements take `[HasDerivedCategory.{w} ·]` for
the categories involved as binders rather than fixing `HasDerivedCategory.standard`, since a
statement proved for one model says nothing about another.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.TorIndependence
open scoped TensorProduct
open scoped ChangeOfRings

universe u w w'

namespace RingTheory.TorIndependence

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The map on the cohomology of a derived base change induced by a morphism of the source**,
as an `R'`-linear map. It is the `n`-th cohomology of the derived base change of `θ`, read over
`R`. -/
abbrev baseChangeCohomologyOverBaseMap (K₁ K₂ : DerivedCategory (ModuleCat.{u} A))
    (θ : K₁ ⟶ K₂) (n : ℤ) :
    baseChangeCohomologyOverBase (R := R) (R' := R') K₁ n ⟶
      baseChangeCohomologyOverBase (R := R) (R' := R') K₂ n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor.map
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map θ))

/-- The `R'`-linear induced map of the identity is the identity. -/
private theorem baseChangeCohomologyOverBaseMap_id (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) : baseChangeCohomologyOverBaseMap (R := R) (R' := R') K K (𝟙 K) n = 𝟙 _ := by
  simp only [baseChangeCohomologyOverBaseMap, CategoryTheory.Functor.map_id]

/-- The `R'`-linear induced map of a composition is the composition of the induced maps. -/
private theorem baseChangeCohomologyOverBaseMap_comp {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{u} A)}
    (θ : K₁ ⟶ K₂) (θ' : K₂ ⟶ K₃) (n : ℤ) :
    baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₃ (θ ≫ θ') n =
      baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n ≫
        baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₂ K₃ θ' n := by
  simp only [baseChangeCohomologyOverBaseMap, CategoryTheory.Functor.map_comp]

/-- The induced map is linear for the action of the right tensor factor, which on both sides is
the `R'`-action already present. -/
theorem baseChangeCohomologyOverBaseMap_includeRight_smul
    (K₁ K₂ : DerivedCategory (ModuleCat.{u} A)) (θ : K₁ ⟶ K₂) (n : ℤ)
    (r : R') (m : baseChangeCohomology (R := R) (R' := R') K₁ n) :
    (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom
        ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
      (Algebra.TensorProduct.includeRight r : A ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R') K₂ n from
          (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom m) := by
  rw [baseChangeCohomology_includeRight_smul, baseChangeCohomology_includeRight_smul]
  exact (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom.map_smul r m

/-- The induced map is linear for the action of the left tensor factor: scalar multiplication by
`a` on `K` is a central endomorphism, so it commutes with `θ`. -/
theorem baseChangeCohomologyOverBaseMap_includeLeft_smul
    (K₁ K₂ : DerivedCategory (ModuleCat.{u} A)) (θ : K₁ ⟶ K₂) (n : ℤ)
    (a : A) (m : baseChangeCohomology (R := R) (R' := R') K₁ n) :
    (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R') K₂ n from
          (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom m) := by
  rw [baseChangeCohomology_includeLeft_smul, baseChangeCohomology_includeLeft_smul]
  have hc : baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₁ (a • 𝟙 K₁) n ≫
        baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n =
      baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n ≫
        baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₂ K₂ (a • 𝟙 K₂) n := by
    rw [← baseChangeCohomologyOverBaseMap_comp, ← baseChangeCohomologyOverBaseMap_comp]
    simp only [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]
  exact congrArg (fun l => l.hom m) hc

/-- **The map on the cohomology of a derived base change induced by a morphism of the source**,
as a map of `A ⊗_R R'`-modules. The two actions of the tensor product are pinned by
`RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul` and
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, and the map respects each. -/
def baseChangeCohomologyMapHom (K₁ K₂ : DerivedCategory (ModuleCat.{u} A)) (θ : K₁ ⟶ K₂)
    (n : ℤ) :
    baseChangeCohomology (R := R) (R' := R') K₁ n ⟶
      baseChangeCohomology (R := R) (R' := R') K₂ n :=
  ModuleCat.ofHom
    (X := baseChangeCohomology (R := R) (R' := R') K₁ n)
    (Y := baseChangeCohomology (R := R) (R' := R') K₂ n)
    (show baseChangeCohomology (R := R) (R' := R') K₁ n →ₗ[A ⊗[R] R']
        baseChangeCohomology (R := R) (R' := R') K₂ n from
      { toFun := fun m =>
          (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom m
        map_add' := fun x y => map_add _ x y
        map_smul' := fun t m => by
          induction t using TensorProduct.inductionOn with
          | add x y hx hy =>
            simp only [RingHom.id_apply] at hx hy ⊢
            rw [add_smul]
            exact (map_add _ _ _).trans
              ((congrArg₂ (· + ·) hx hy).trans (add_smul x y _).symm)
          | tmul a r =>
            have ht : a ⊗ₜ[R] r =
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') *
                  Algebra.TensorProduct.includeRight r := by
              change a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [ht, mul_smul, baseChangeCohomologyOverBaseMap_includeLeft_smul,
              baseChangeCohomologyOverBaseMap_includeRight_smul, ← mul_smul, ← ht]
            rfl })

/-- The induced map of the identity is the identity. -/
theorem baseChangeCohomologyMapHom_id (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    baseChangeCohomologyMapHom (R := R) (R' := R') K K (𝟙 K) n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K K (𝟙 K) n).hom m = m
  rw [baseChangeCohomologyOverBaseMap_id]
  rfl

/-- The induced map of a composition is the composition of the induced maps. -/
theorem baseChangeCohomologyMapHom_comp {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{u} A)}
    (θ : K₁ ⟶ K₂) (θ' : K₂ ⟶ K₃) (n : ℤ) :
    baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₃ (θ ≫ θ') n =
      baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₂ θ n ≫
        baseChangeCohomologyMapHom (R := R) (R' := R') K₂ K₃ θ' n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₃ (θ ≫ θ') n).hom m = _
  rw [baseChangeCohomologyOverBaseMap_comp]
  rfl

/-- **The cohomology of the derived base change is a functor** of the object of `D(A)`, valued
in `A ⊗_R R'`-modules. -/
def baseChangeCohomologyFunctor (n : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} (A ⊗[R] R') where
  obj K := baseChangeCohomology (R := R) (R' := R') K n
  map θ := baseChangeCohomologyMapHom (R := R) (R' := R') _ _ θ n
  map_id K := baseChangeCohomologyMapHom_id K n
  map_comp θ θ' := baseChangeCohomologyMapHom_comp θ θ' n

/-- The induced map of an isomorphism is an isomorphism. -/
theorem isIso_baseChangeCohomologyMapHom {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)}
    (θ : K₁ ⟶ K₂) (hθ : IsIso θ) (n : ℤ) :
    IsIso (baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₂ θ n) := by
  let := hθ
  exact ⟨baseChangeCohomologyMapHom (R := R) (R' := R') K₂ K₁ (inv θ) n,
    by rw [← baseChangeCohomologyMapHom_comp, IsIso.hom_inv_id, baseChangeCohomologyMapHom_id],
    by rw [← baseChangeCohomologyMapHom_comp, IsIso.inv_hom_id, baseChangeCohomologyMapHom_id]⟩

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance] hasDerivedCategory_ringedSpaceModules

attribute [local implicit_reducible] structureSheafRing

/-- **The pointwise base-change map of Stacks 0DJ7 transports along an isomorphism of the
source.** For an isomorphism `θ : K₁ ⟶ K₂` in `D(𝒪_X)` the map at
`(K₁, K', L(g')^*θ ≫ φ)` is the extension of scalars of
`RingTheory.TorIndependence.baseChangeCohomologyMapHom` followed by the map at `(K₂, K', φ)`,
so the two are invertible together. Nothing is assumed of the square beyond commutativity, and
nothing of `K₁`, `K₂`, `K'` or `φ`.

This is the invariance of condition (1) of Stacks 0DJ8 under replacing `K` by an isomorphic
complex, which is what lets a proof of that condition replace the stalk of the source by a
convenient model. -/
theorem isIso_baseChangeCohomologyMap_iff_of_isIso_source {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w'} X.Modules] [HasDerivedCategory.{w'} X'.Modules]
    (K₁ K₂ : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (θ : K₁ ⟶ K₂) (hθ : IsIso θ)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K') (x' : X')
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w K₁ K'
        ((derivedPullback g'.toLRSHom.toShHom).map θ ≫ φ) x' n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' w K₂ K' φ x' n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  have key : baseChangeCohomologyMap f g f' g' w K₁ K'
        ((derivedPullback g'.toLRSHom.toShHom).map θ ≫ φ) x' n =
      (ModuleCat.extendScalars _).map
          (baseChangeCohomologyMapHom ((derivedStalkFunctor (g' x')).obj K₁)
            ((derivedStalkFunctor (g' x')).obj K₂) ((derivedStalkFunctor (g' x')).map θ) n) ≫
        baseChangeCohomologyMap f g f' g' w K₂ K' φ x' n := by
    let R := S.presheaf.stalk (f (g' x'))
    let A := X.presheaf.stalk (g' x')
    let R' := S'.presheaf.stalk (f' x')
    let A' := X'.presheaf.stalk x'
    let fR : R →+* A := algebraMap R A
    let gR : R →+* R' := algebraMap R R'
    let hR : A →+* A' := algebraMap A A'
    let iR : R' →+* A' := algebraMap R' A'
    let sq : hR.comp fR = iR.comp gR :=
      (IsScalarTower.algebraMap_eq R A A').symm.trans (IsScalarTower.algebraMap_eq R R' A')
    let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} gR
    let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} hR
    let τ := (@derivedBaseChangeComparison.{u, u, u, u, u, w', w', w', w'}
      R A R' A' _ _ _ _ _ _ _ _ fR gR hR iR sq Tg.functor Th.functor Tg.comparison
      Th.comparison Tg.isLeftDerived Th.isLeftDerived).2.1
    let C := (ModuleCat.restrictScalars iR).mapDerivedCategory
    let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
    let K₁x := (derivedStalkFunctor (g' x')).obj K₁
    let K₂x := (derivedStalkFunctor (g' x')).obj K₂
    let Kx' := (derivedStalkFunctor x').obj K'
    let θx := (derivedStalkFunctor (g' x')).map θ
    let ι₁ := (derivedPullbackStalkIso g' x').inv.app K₁
    let ι₂ := (derivedPullbackStalkIso g' x').inv.app K₂
    let ψ₁ := ι₁ ≫ (derivedStalkFunctor x').map
      ((derivedPullback g'.toLRSHom.toShHom).map θ ≫ φ)
    let ψ₂ := ι₂ ≫ (derivedStalkFunctor x').map φ
    have hι : Th.functor.map θx ≫ ι₂ =
        ι₁ ≫ (derivedStalkFunctor x').map ((derivedPullback g'.toLRSHom.toShHom).map θ) :=
      (derivedPullbackStalkIso g' x').inv.naturality θ
    have hin : ψ₁ = Th.functor.map θx ≫ ψ₂ := by
      dsimp only [ψ₁, ψ₂]
      rw [← Category.assoc, hι, Category.assoc]
      exact congrArg (fun z => ι₁ ≫ z) ((derivedStalkFunctor x').map_comp _ _)
    have hτ : τ.app K₁x ≫ C.map (Th.functor.map θx) =
        Tg.functor.map ((ModuleCat.restrictScalars fR).mapDerivedCategory.map θx) ≫ τ.app K₂x :=
      (τ.naturality θx).symm
    have hnat : J.map (τ.app K₁x ≫ C.map ψ₁) =
        baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁x K₂x θx n ≫
          J.map (τ.app K₂x ≫ C.map ψ₂) := by
      rw [hin, CategoryTheory.Functor.map_comp C, ← Category.assoc, hτ, Category.assoc,
        CategoryTheory.Functor.map_comp J]
    let P₁ := exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K₁x Kx' ψ₁ n
    let P₂ := exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K₂x Kx' ψ₂ n
    have h₁ := Classical.choose_spec P₁.exists
    have h₂ := Classical.choose_spec P₂.exists
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let m₀ : baseChangeCohomologyOverBase (R := R) (R' := R') K₁x n := m
    let m₁ : baseChangeCohomologyOverBase (R := R) (R' := R') K₂x n :=
      (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁x K₂x θx n).hom m
    dsimp only [baseChangeCohomologyMap]
    change (Classical.choose P₁.exists).hom
        ((1 : A') ⊗ₜ[((A ⊗[R] R')),
          (Algebra.TensorProduct.lift
            (IsScalarTower.toAlgHom R A A')
            (IsScalarTower.toAlgHom R R' A')
            (fun _ _ ↦ Commute.all _ _)).toRingHom] m) =
      (Classical.choose P₂.exists).hom
        ((1 : A') ⊗ₜ[((A ⊗[R] R')),
          (Algebra.TensorProduct.lift
            (IsScalarTower.toAlgHom R A A')
            (IsScalarTower.toAlgHom R R' A')
            (fun _ _ ↦ Commute.all _ _)).toRingHom] m₁)
    rw [h₁ m₀, h₂ m₁]
    exact congrArg (fun z => (((ModuleCat.restrictScalars iR).mapDerivedCategoryHomologyIso
      n).app Kx').hom.hom z) (congrArg (fun l => l.hom m) hnat)
  rw [key]
  have hθx : IsIso ((derivedStalkFunctor (g' x')).map θ) :=
    ((derivedStalkFunctor (g' x')).mapIso (@asIso _ _ _ _ _ hθ)).isIso_hom
  have hb := isIso_baseChangeCohomologyMapHom (R := S.presheaf.stalk (f (g' x')))
    (R' := S'.presheaf.stalk (f' x')) ((derivedStalkFunctor (g' x')).map θ) hθx n
  exact isIso_comp_left_iff _ _

/-- **The pointwise base-change map of Stacks 0DJ7 transports along an isomorphism of the
target.** For an isomorphism `ψ : K' ⟶ K''` in `D(𝒪_{X'})` the map at `(K, K'', φ ≫ ψ)` differs
from the map at `(K, K', φ)` by the stalkwise cohomology of `ψ`, so the two are invertible
together. This is the invariance of condition (1) of Stacks 0DJ8 under replacing `K'` by an
isomorphic complex. -/
theorem isIso_baseChangeCohomologyMap_iff_of_isIso_target {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w'} X.Modules] [HasDerivedCategory.{w'} X'.Modules]
    (K : DerivedCategory X.Modules) (K' K'' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (ψ : K' ⟶ K'') (hψ : IsIso ψ)
    (x' : X')
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w K K'' (φ ≫ ψ) x' n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n) := by
  rw [baseChangeCohomologyMap_comp]
  have hm : IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (X'.presheaf.stalk x')) n).map ((derivedStalkFunctor x').map ψ)) := by
    let := hψ
    infer_instance
  exact isIso_comp_right_iff _ _

end AlgebraicGeometry

end
