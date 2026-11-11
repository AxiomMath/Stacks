module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport

/-!
# The pointwise base-change map is natural in its datum

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes. For a triple `(K, K', φ)` with `K ∈ D(𝒪_X)`,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, the map of Stacks 0DJ7 at a point `x'` of `X'` and in a
degree `n` is

`𝒪_{X', x'} ⊗_{𝒪_{X, x} ⊗ 𝒪_{S', s'}} H^n(K_x ⊗^L_{𝒪_{S, s}} 𝒪_{S', s'}) ⟶ H^n(K'_{x'})`.

This module records its naturality for an arbitrary morphism of triples: morphisms `θ : K₁ ⟶ K₂`
and `θ' : K₁' ⟶ K₂'` with `φ₁ ≫ θ' = L(g')^*θ ≫ φ₂` make the two maps form a commutative square
whose horizontal sides are the extension of scalars of the map
`H^n(θ_x ⊗^L_{𝒪_{S, s}} 𝒪_{S', s'})` and the map `H^n(θ'_{x'})`. So the invertibility of the map
at one triple passes to the other as soon as those two sides are invertible, which is what an
approximation argument in a single degree consumes.

## Main results

* `AlgebraicGeometry.baseChangeCohomologyMap_map_comp`: the map at `(K₁, K', L(g')^*θ ≫ φ)` is
  the extension of scalars of `RingTheory.TorIndependence.baseChangeCohomologyMapHom` at `θ`
  followed by the map at `(K₂, K', φ)`, for an arbitrary `θ`.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_of_square`: invertibility of the map transports
  along a morphism of triples whose two sides are invertible in the given degree.

## References

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

/-- The map of `A ⊗_R R'`-modules induced by `θ` is invertible as soon as the underlying map
`H^n(θ ⊗^L_R R')` of `R'`-modules is. -/
theorem isIso_baseChangeCohomologyMapHom_of_isIso {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)}
    (θ : K₁ ⟶ K₂) (n : ℤ)
    (hθ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R R')).functor.map
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map θ)))) :
    IsIso (baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₂ θ n) := by
  have hb : Function.Bijective
      (baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom :=
    ConcreteCategory.bijective_of_isIso _
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance] hasDerivedCategory_ringedSpaceModules

attribute [local implicit_reducible] structureSheafRing

/-- **The pointwise base-change map of Stacks 0DJ7 is natural in the source.** For an arbitrary
morphism `θ : K₁ ⟶ K₂` in `D(𝒪_X)`, the map at `(K₁, K', L(g')^*θ ≫ φ)` is the extension of
scalars of `RingTheory.TorIndependence.baseChangeCohomologyMapHom` at the stalk of `θ`, followed
by the map at `(K₂, K', φ)`. Nothing is assumed of the square beyond commutativity. -/
theorem baseChangeCohomologyMap_map_comp {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w'} X.Modules] [HasDerivedCategory.{w'} X'.Modules]
    (K₁ K₂ : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (θ : K₁ ⟶ K₂)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K') (x' : X')
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' w x').toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
    baseChangeCohomologyMap f g f' g' w K₁ K'
        ((derivedPullback g'.toLRSHom.toShHom).map θ ≫ φ) x' n =
      (ModuleCat.extendScalars _).map
          (baseChangeCohomologyMapHom ((derivedStalkFunctor (g' x')).obj K₁)
            ((derivedStalkFunctor (g' x')).obj K₂) ((derivedStalkFunctor (g' x')).map θ) n) ≫
        baseChangeCohomologyMap f g f' g' w K₂ K' φ x' n := by
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

end AlgebraicGeometry

end
