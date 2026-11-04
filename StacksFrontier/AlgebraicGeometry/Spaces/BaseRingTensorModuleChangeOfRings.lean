module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat

/-!
# `𝒪_X ⊗_R -` under a change of the base ring

Let `X` be an algebraic space and `φ : R' →+* Γ(X, 𝒪_X)` a base-ring datum of the module
`𝒪_X ⊗_{R'} -` of [Stacks Project, Tag 0D3F] (`AlgebraicGeometry.Space.baseRingTensorModule`).
For a ring map `ψ : R →+* R'` the composite `φ ∘ ψ` is a base-ring datum for `R`, and

`𝒪_X ⊗_R M ≅ 𝒪_X ⊗_{R'} (R' ⊗_R M)`

naturally in the `R`-module `M`: both functors are left adjoint to global sections read as
`R`-modules. When `ψ` is surjective restriction of scalars along `ψ` is fully faithful, so the
counit `R' ⊗_R N ⟶ N` is invertible for every `R'`-module `N`, and

`𝒪_X ⊗_R N ≅ 𝒪_X ⊗_{R'} N`

for an `R'`-module `N` read as an `R`-module. This is the form in which the ideal
`𝒪_X ⊗_{k[V]} V` of the closed fibre of a deformation over `k[V]` is the module `𝒪_{X₀} ⊗_k V`
of [Stacks Project, Tag 0D1K].

The base-ring datum of a composite `X ⟶ T ⟶ T'` of morphisms to objects of the site is the
composite of the datum of `X ⟶ T` with pullback of functions along `T ⟶ T'`
(`AlgebraicGeometry.Space.baseRingHomOfMap_comp`).

## Main definitions

* `ModuleCat.restrictScalarsFullyFaithfulOfSurjective`: restriction of scalars along a
  surjective ring map is fully faithful.
* `AlgebraicGeometry.Space.baseRingTensorModuleCompIso`:
  `𝒪_X ⊗_{R'} (R' ⊗_R -) ≅ 𝒪_X ⊗_R -`.
* `AlgebraicGeometry.Space.baseRingTensorModuleRestrictScalarsIso`: for surjective `ψ`,
  `𝒪_X ⊗_R N ≅ 𝒪_X ⊗_{R'} N`, naturally in the `R'`-module `N`.

## Main results

* `AlgebraicGeometry.Space.baseRingHomOfMap_comp`: the base-ring datum of `X ⟶ T ⟶ T'`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace ModuleCat

variable {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] (ψ : R →+* R')

/-- **Restriction of scalars along a surjective ring map is fully faithful**: an `R`-linear map
of `R'`-modules is `R'`-linear, every element of `R'` being the image of one of `R`. -/
def restrictScalarsFullyFaithfulOfSurjective (hψ : Function.Surjective ψ) :
    (restrictScalars.{u} ψ).FullyFaithful where
  preimage {M N} g := ModuleCat.ofHom
    { toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun r' m => by
        obtain ⟨r, rfl⟩ := hψ r'
        exact g.hom.map_smul r m }
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Restriction of scalars along a surjective ring map is full. -/
instance [hψ : Fact (Function.Surjective ψ)] : (restrictScalars.{u} ψ).Full :=
  (restrictScalarsFullyFaithfulOfSurjective ψ hψ.out).full

end ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R R' : Type u} [CommRing R] [CommRing R'] (ψ : R →+* R')
  (φ : R' →+* modelGlobalFunctions B S hS X)

/-- Global sections read as `R`-modules through `φ ∘ ψ` are global sections read as
`R'`-modules through `φ`, restricted along `ψ`. -/
def baseRingGlobalSectionsModuleCompIso :
    baseRingGlobalSectionsModule B S hS X (φ.comp ψ) ≅
      baseRingGlobalSectionsModule B S hS X φ ⋙ ModuleCat.restrictScalars.{u} ψ :=
  Functor.isoWhiskerLeft ((smallEtaleModelModulesEquiv B S hS X).functor ⋙
      globalSectionsFunctor (ringSheafOfSite.{u, u, u} (smallEtaleModelStructureSheaf B S hS X)))
    (ModuleCat.restrictScalarsComp'.{u} ψ φ (φ.comp ψ) rfl)

/-- **`𝒪_X ⊗_{R'} (R' ⊗_R M) ≅ 𝒪_X ⊗_R M`**, naturally in the `R`-module `M`, the base ring
`R` acting through `φ ∘ ψ`: both are left adjoint to global sections read as `R`-modules. -/
def baseRingTensorModuleCompIso :
    ModuleCat.extendScalars.{u, u, u} ψ ⋙ baseRingTensorModule B S hS X φ ≅
      baseRingTensorModule B S hS X (φ.comp ψ) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).comp
      (baseRingTensorModuleAdjunction B S hS X φ)).leftAdjointUniq
    ((baseRingTensorModuleAdjunction B S hS X (φ.comp ψ)).ofNatIsoRight
      (baseRingGlobalSectionsModuleCompIso B S hS X ψ φ))

/-- **`𝒪_X ⊗_R N ≅ 𝒪_X ⊗_{R'} N` for a surjective `ψ : R →+* R'`**, naturally in the
`R'`-module `N` read as an `R`-module, the base ring `R` acting through `φ ∘ ψ`. -/
def baseRingTensorModuleRestrictScalarsIso (hψ : Function.Surjective ψ) :
    ModuleCat.restrictScalars.{u} ψ ⋙ baseRingTensorModule B S hS X (φ.comp ψ) ≅
      baseRingTensorModule B S hS X φ :=
  haveI : Fact (Function.Surjective ψ) := ⟨hψ⟩
  Functor.isoWhiskerLeft (ModuleCat.restrictScalars.{u} ψ)
      (baseRingTensorModuleCompIso B S hS X ψ φ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).counit)
      (baseRingTensorModule B S hS X φ) ≪≫
    Functor.leftUnitor _

variable {X} {T T' : BigFppfOver B S hS}

/-- The chart map of a composite `X ⟶ T ⟶ T'` is the chart map of `X ⟶ T` followed by
`T ⟶ T'`. -/
theorem chartToBaseOfMap_comp (f : X ⟶ schemeSpace T) (j : T ⟶ T') (U : SmallEtale B S hS X.1) :
    chartToBaseOfMap (f ≫ (schemeSpaceFunctor B S hS).map j) U = chartToBaseOfMap f U ≫ j := by
  apply yoneda.map_injective
  refine (yoneda_map_chartToBaseOfMap _ _).trans ?_
  rw [Functor.map_comp, yoneda_map_chartToBaseOfMap]
  exact (Category.assoc _ _ _).symm

/-- **The base-ring datum of a composite `X ⟶ T ⟶ T'`** is that of `X ⟶ T` precomposed with
pullback of functions along `T ⟶ T'`. -/
theorem baseRingHomOfMap_comp (f : X ⟶ schemeSpace T) (j : T ⟶ T') :
    baseRingHomOfMap (f ≫ (schemeSpaceFunctor B S hS).map j) =
      (baseRingHomOfMap f).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom := by
  refine RingHom.ext fun r => Subtype.ext (funext fun V => ?_)
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap
      (f ≫ (schemeSpaceFunctor B S hS).map j) _)).op).hom r =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f _)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom r)
  rw [chartToBaseOfMap_comp, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

end AlgebraicGeometry.Space

end
