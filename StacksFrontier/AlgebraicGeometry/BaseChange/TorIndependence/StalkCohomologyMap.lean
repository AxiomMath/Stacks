module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The pointwise base-change map on stalkwise cohomology

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes, `K` an object of the derived category of `𝒪_X`-modules,
`K'` an object of the derived category of `𝒪_{X'}`-modules and `φ : L(g')^* K ⟶ K'`. At a point
`x'` of `X'` and in each degree `n` this induces the canonical map

`H^n(K_{g' x'} ⊗ᴸ_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}) ⊗_{𝒪_{X, g' x'} ⊗ 𝒪_{S', f' x'}} 𝒪_{X', x'}
  ⟶ H^n(K'_{x'})`

of Stacks 0DJ7. No flatness, cartesianness or Tor independence is required; the square need
only commute.

## Main definitions

* `AlgebraicGeometry.baseStalkMap`: the map of base stalk rings `𝒪_{S, f(g' x')} ⟶
  `𝒪_{S', f' x'}` attached to the square.
* `AlgebraicGeometry.baseChangeCohomologyMap`: the map of Stacks 0DJ7.

## Main results

* `AlgebraicGeometry.stalkMap_square`: the four stalk maps of the square commute, which is what
  makes the four local rings a commutative square of rings.
* `AlgebraicGeometry.baseChangeCohomologyMap_comp`: the map is natural in the target of `φ`.

## Implementation notes

The two images of `x'` in `S` agree only up to the commutativity of the square, so the base
stalk map is the specialization isomorphism `TopCat.Presheaf.stalkCongr` followed by the stalk
map of `g`. Transporting along that isomorphism is what `stalkMap_square` records, and it is
the scalar tower `IsScalarTower R R' A'` that the ring-level statement consumes.

The map itself is extracted from
`RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap` applied to the derived
stalks, with the scheme-level morphism transported to the stalks by
`AlgebraicGeometry.derivedPullbackStalkIso`.

The model of the derived category is free: the two statements below take
`[HasDerivedCategory.{w'} ·]` for the two categories of sheaves of modules and for the four
local rings of the square as binders rather than fixing `HasDerivedCategory.standard`. A
statement proved for one model says nothing about another, the two derived categories being
merely equivalent and not equal, and both the locally small model with morphisms in `Type u` and
the standard model with morphisms in `Type (u + 1)` are wanted here.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.TorIndependence
open scoped TensorProduct
open scoped ChangeOfRings

universe u w'

namespace AlgebraicGeometry

attribute [local instance] hasDerivedCategory_ringedSpaceModules

/-- **The base stalk map of a commutative square of schemes.** For a commutative square with
`f : X ⟶ S`, `g : S' ⟶ S`, `f' : X' ⟶ S'`, `g' : X' ⟶ X` and a point `x'` of `X'`, the two
images of `x'` in `S` agree, and the stalk map of `g` transported along that agreement is a ring
map `𝒪_{S, f(g' x')} ⟶ 𝒪_{S', f' x'}`. -/
def baseStalkMap {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (x' : X') :
    S.presheaf.stalk (f (g' x')) →+* S'.presheaf.stalk (f' x') :=
  ((S.presheaf.stalkCongr (.of_eq (congrArg (fun h : X' ⟶ S ↦ h x') w))).hom ≫
    g.stalkMap (f' x')).hom

/-- **The square of stalk rings of a commutative square of schemes commutes.** Going round by
`X` and going round by `S'` give the same ring map `𝒪_{S, f(g' x')} ⟶ 𝒪_{X', x'}`. -/
theorem stalkMap_square {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (x' : X') :
    (g'.stalkMap x').hom.comp (f.stalkMap (g' x')).hom =
      (f'.stalkMap x').hom.comp (baseStalkMap f g f' g' w x') := by
  have h := congrArg CommRingCat.Hom.hom
    (Scheme.Hom.stalkMap_congr_hom (g' ≫ f) (f' ≫ g) w x')
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  dsimp [baseStalkMap]
  rw [← RingHom.comp_assoc]
  exact h

/-- **Stacks 0DJ7.** The canonical pointwise base-change map on stalkwise cohomology induced by
a morphism `φ : L(g')^* K ⟶ K'` over a commutative square of schemes. No flatness,
cartesianness or Tor independence is required. -/
@[stacks 0DJ7]
def baseChangeCohomologyMap {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w'} X.Modules] [HasDerivedCategory.{w'} X'.Modules]
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g'.toLRSHom.toShHom).obj K ⟶ K')
    (x' : X')
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :=
  let R := S.presheaf.stalk (f (g' x'))
  let A := X.presheaf.stalk (g' x')
  let R' := S'.presheaf.stalk (f' x')
  let A' := X'.presheaf.stalk x'
  let a := (f.stalkMap (g' x')).hom
  let b := baseStalkMap f g f' g' w x'
  let c := (g'.stalkMap x').hom
  let d := (f'.stalkMap x').hom
  letI : Algebra R A := a.toAlgebra
  letI : Algebra R R' := b.toAlgebra
  letI : Algebra R A' := (c.comp a).toAlgebra
  letI : Algebra A A' := c.toAlgebra
  letI : Algebra R' A' := d.toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  Classical.choose (exists_unique_ringBaseChangeCohomologyMap
    (R := R) (A := A) (R' := R') (A' := A')
    ((derivedStalkFunctor (g' x')).obj K) ((derivedStalkFunctor x').obj K')
    ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map φ) n).exists

/-- The pointwise base-change map is natural in the target of the scheme-level morphism:
composing `φ` with `ψ : K' ⟶ K''` composes the induced map with the stalkwise cohomology of
`ψ`. -/
theorem baseChangeCohomologyMap_comp {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w'} X.Modules] [HasDerivedCategory.{w'} X'.Modules]
    (K : DerivedCategory X.Modules) (K' K'' : DerivedCategory X'.Modules)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g'.toLRSHom.toShHom).obj K ⟶ K')
    (ψ : K' ⟶ K'') (x' : X')
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :
    baseChangeCohomologyMap f g f' g' w K K'' (φ ≫ ψ) x' n =
      baseChangeCohomologyMap f g f' g' w K K' φ x' n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X'.presheaf.stalk x')) n).map
          ((derivedStalkFunctor x').map ψ) := by
  let R := S.presheaf.stalk (f (g' x'))
  let A := X.presheaf.stalk (g' x')
  let R' := S'.presheaf.stalk (f' x')
  let A' := X'.presheaf.stalk x'
  let a := (f.stalkMap (g' x')).hom
  let b := baseStalkMap f g f' g' w x'
  let c := (g'.stalkMap x').hom
  let d := (f'.stalkMap x').hom
  let _ : Algebra R A := a.toAlgebra
  let _ : Algebra R R' := b.toAlgebra
  let _ : Algebra R A' := (c.comp a).toAlgebra
  let _ : Algebra A A' := c.toAlgebra
  let _ : Algebra R' A' := d.toAlgebra
  let _ : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  let Pφ := exists_unique_ringBaseChangeCohomologyMap (R := R) (A := A)
    (R' := R') (A' := A') ((derivedStalkFunctor (g' x')).obj K)
    ((derivedStalkFunctor x').obj K')
    ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map φ) n
  let Pψ := exists_unique_ringBaseChangeCohomologyMap (R := R) (A := A)
    (R' := R') (A' := A') ((derivedStalkFunctor (g' x')).obj K)
    ((derivedStalkFunctor x').obj K'')
    ((derivedPullbackStalkIso g' x').inv.app K ≫
      (derivedStalkFunctor x').map (φ ≫ ψ)) n
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
  let αψ := τ.app ((derivedStalkFunctor (g' x')).obj K) ≫
    (ModuleCat.restrictScalars iR).mapDerivedCategory.map
      ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map (φ ≫ ψ))
  let qψ := (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map αψ
  let αφ := τ.app ((derivedStalkFunctor (g' x')).obj K) ≫
    (ModuleCat.restrictScalars iR).mapDerivedCategory.map
      ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map φ)
  let qφ := (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map αφ
  let ψ' := (derivedStalkFunctor x').map ψ
  let qR := (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((ModuleCat.restrictScalars iR).mapDerivedCategory.map ψ')
  have hq : qψ = qφ ≫ qR := by
    dsimp only [qψ, qφ, qR, αφ, αψ]
    rw [show (derivedStalkFunctor x').map (φ ≫ ψ) =
      (derivedStalkFunctor x').map φ ≫ ψ' from Functor.map_comp _ _ _]
    simp only [Functor.map_comp, Category.assoc]
  let e'φ := ((ModuleCat.restrictScalars iR).mapDerivedCategoryHomologyIso n).app
    ((derivedStalkFunctor x').obj K')
  let e'ψ := ((ModuleCat.restrictScalars iR).mapDerivedCategoryHomologyIso n).app
    ((derivedStalkFunctor x').obj K'')
  have hφ := Classical.choose_spec Pφ.exists
  have hψ := Classical.choose_spec Pψ.exists
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let m₀ : baseChangeCohomologyOverBase (R := R) (R' := R')
    ((derivedStalkFunctor (g' x')).obj K) n := m
  dsimp only [baseChangeCohomologyMap]
  let t : A ⊗[R] R' →+* A' := (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom
  change (Classical.choose Pψ.exists).hom ((1 : A') ⊗ₜ[((A ⊗[R] R')), t] m) =
    ((Classical.choose Pφ.exists) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
        ((derivedStalkFunctor x').map ψ)).hom ((1 : A') ⊗ₜ[((A ⊗[R] R')), t] m)
  rw [hψ m₀]
  change e'ψ.hom.hom (qψ.hom m₀) =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
      ((derivedStalkFunctor x').map ψ)).hom
      ((Classical.choose Pφ.exists).hom ((1 : A') ⊗ₜ[((A ⊗[R] R')), t] m))
  rw [hφ m₀, hq, ModuleCat.comp_apply]
  exact congrArg (fun l => l.hom (qφ.hom m₀))
    (((ModuleCat.restrictScalars iR).mapDerivedCategoryHomologyIso n).hom.naturality ψ')

end AlgebraicGeometry

end
