module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# Derived global sections on an affine scheme commute with base change

Let `φ : R ⟶ R'` be a homomorphism of commutative rings, `g = Spec φ : Spec R' ⟶ Spec R`, and let
`P` be an object of `D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent. Then

`RΓ(Spec R, P) ⊗_R^𝐋 R' ≅ RΓ(Spec R', Lg^*P)`

in `D(R')`, by the canonical map: the derived base-change map adjoint to

`RΓ(Spec R, P) ⟶ RΓ(Spec R, Rg_* Lg^*P) = φ^* RΓ(Spec R', Lg^*P)`,

the image of the unit of `Lg^* ⊣ Rg_*` followed by the Leray identification
`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso`.

## Main definitions

* `AlgebraicGeometry.affineBaseChangeNatTrans` and its component
  `AlgebraicGeometry.affineBaseChangeMap` — the map `RΓ(Spec R, P) ⟶ φ^* RΓ(Spec R', Lg^*P)`.

## Main results

* `AlgebraicGeometry.isIso_homEquiv_symm_affineBaseChangeMap` — its adjoint transpose under any
  adjunction `L' ⊣ φ^*` is invertible.
* `AlgebraicGeometry.isIso_derivedBaseChangeComparison_affineBaseChangeMap` — the same for the
  derived base-change map `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison`.
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_map_unit_comp_app` — in a square of adjunctions
  whose vertical functors are right adjoints with invertible counit at the relevant objects and,
  on the target, invertible unit, the mate of an invertible square is invertible at those
  objects.

## Implementation notes

The geometric declarations take all four derived categories at `HasDerivedCategory.standard`,
scoped to each declaration by `attribute [local instance 10000] HasDerivedCategory.standard in`:
the Leray identification for the derived pushforward,
`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso`, is only stated
there (a binder `[HasDerivedCategory X.Modules]` is not found for the ringed-space spelling
`SheafOfModules (structureSheafRing X.toSheafedSpace)` in which `Rg_*` and `Lg^*` are stated),
and `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison` is only stated at the standard
model on module categories.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ w₄ u

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']

/-- For an adjunction `T ⊣ E` whose counit is invertible at `X`, the functor `E` is bijective on
morphisms out of `X`: `E.map f` is the adjoint transpose of `ε_X ≫ f`. -/
theorem bijective_map_of_isIso_counit_app {T : D ⥤ C} {E : C ⥤ D} (a : T ⊣ E) (X Z : C)
    [IsIso (a.counit.app X)] : Function.Bijective (fun f : X ⟶ Z => E.map f) := by
  have h : (fun f : X ⟶ Z => E.map f) =
      (a.homEquiv _ _) ∘ (fun f : X ⟶ Z => a.counit.app X ≫ f) := by
    funext f
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (a.homEquiv _ _).bijective.comp ((isIso_iff_coyoneda_map_bijective _).1 inferInstance Z)

/-- **The mate of an invertible square along partial equivalences is invertible.** Consider
adjunctions `L ⊣ R` (between `C` and `C'`) and `L' ⊣ R'` (between `D` and `D'`), functors
`E₁ : C ⥤ D` and `E₂ : C' ⥤ D'` with left adjoints `T₁ ⊣ E₁`, `T₂ ⊣ E₂`, and an invertible
square `β : R ⋙ E₁ ⟶ E₂ ⋙ R'`. If the counit of `T₁ ⊣ E₁` is invertible at `P`, the counit of
`T₂ ⊣ E₂` is invertible at `L P`, and the unit of `T₂ ⊣ E₂` is invertible, then the adjoint
transpose `L' E₁ P ⟶ E₂ L P` of `E₁(η_P) ≫ β_{LP}` is an isomorphism. -/
theorem isIso_homEquiv_symm_map_unit_comp_app {L : C ⥤ C'} {R : C' ⥤ C} (adj : L ⊣ R)
    {L' : D ⥤ D'} {R' : D' ⥤ D} (adj' : L' ⊣ R') {E₁ : C ⥤ D} {E₂ : C' ⥤ D'}
    {T₁ : D ⥤ C} {T₂ : D' ⥤ C'} (a₁ : T₁ ⊣ E₁) (a₂ : T₂ ⊣ E₂)
    (β : R ⋙ E₁ ⟶ E₂ ⋙ R') [IsIso β] (P : C) (h₁ : IsIso (a₁.counit.app P))
    (h₂ : IsIso (a₂.counit.app (L.obj P))) (h₃ : IsIso a₂.unit) :
    IsIso ((adj'.homEquiv _ _).symm (E₁.map (adj.unit.app P) ≫ β.app (L.obj P))) := by
  refine isIso_of_coyoneda_map_bijective _ fun Y => ?_
  let Φ : (E₂.obj (L.obj P) ⟶ Y) → (E₁.obj P ⟶ R'.obj Y) := fun h =>
    E₁.map (adj.unit.app P) ≫ β.app (L.obj P) ≫ R'.map h
  have hτ : (fun h : E₂.obj (L.obj P) ⟶ Y =>
      (adj'.homEquiv _ _).symm (E₁.map (adj.unit.app P) ≫ β.app (L.obj P)) ≫ h) =
      (adj'.homEquiv _ _).symm ∘ Φ := by
    funext h
    simp only [Function.comp_apply, Φ]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
    rfl
  rw [hτ]
  refine (adj'.homEquiv _ _).symm.bijective.comp ?_
  let u := a₂.unit.app Y
  let Q := T₂.obj Y
  let Θ : (L.obj P ⟶ Q) → (E₂.obj (L.obj P) ⟶ Y) := fun k => E₂.map k ≫ inv u
  have hΘ : Function.Bijective Θ :=
    ((isIso_iff_yoneda_map_bijective (inv u)).1 inferInstance _).comp
      (bijective_map_of_isIso_counit_app a₂ (L.obj P) Q)
  have hΦΘ : Φ ∘ Θ = (fun f : E₁.obj P ⟶ E₁.obj (R.obj Q) => f ≫ β.app Q ≫ R'.map (inv u)) ∘
      (fun f : P ⟶ R.obj Q => E₁.map f) ∘ (adj.homEquiv _ _) := by
    funext k
    have hβ := β.naturality k
    simp only [Functor.comp_map] at hβ
    simp only [Function.comp_apply, Φ, Θ, Adjunction.homEquiv_unit, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% hβ]
  have hbij : Function.Bijective (Φ ∘ Θ) := by
    rw [hΦΘ]
    refine Function.Bijective.comp ?_ ((bijective_map_of_isIso_counit_app a₁ P _).comp
      (adj.homEquiv _ _).bijective)
    exact (isIso_iff_yoneda_map_bijective (β.app Q ≫ R'.map (inv u))).1 inferInstance _
  exact (Function.Bijective.of_comp_iff Φ hΘ).1 hbij

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')

/-- The square `Spec φ ≫ 𝟙 = 𝟙 ≫ Spec φ` commutes. -/
theorem specMap_comp_id_eq :
    Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (.of R)) =
      𝟙 (Spec (.of R')) ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The affine base-change map** `RΓ(Spec R, P) ⟶ φ^* RΓ(Spec R', Lg^*P)` for `g = Spec φ`:
derived global sections of the unit `P ⟶ Rg_* Lg^* P` of `Lg^* ⊣ Rg_*`, followed by the Leray
identification `RΓ(Spec R, Rg_* -) ≅ φ^* RΓ(Spec R', -)`
(`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso`). -/
def affineBaseChangeMap (P : DerivedCategory (Spec (.of R)).Modules) :
    (derivedGlobalSectionsOver (𝟙 (Spec (.of R)))).obj P ⟶
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
        ((derivedGlobalSectionsOver (𝟙 (Spec (.of R')))).obj
          ((derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj P)) :=
  (derivedGlobalSectionsOver (𝟙 (Spec (.of R)))).map
      ((derivedAdjunction (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).unit.app P) ≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso
      (Spec.map (CommRingCat.ofHom φ)) (𝟙 _) (𝟙 _) φ (specMap_comp_id_eq φ)).hom.app
      ((derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj P)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The affine base-change map, naturally in `P`**: the natural transformation
`RΓ(Spec R, -) ⟶ φ^* RΓ(Spec R', Lg^* -)`, the whiskered unit of `Lg^* ⊣ Rg_*` followed by the
whiskered Leray identification, whose components are `AlgebraicGeometry.affineBaseChangeMap`. -/
def affineBaseChangeNatTrans :
    derivedGlobalSectionsOver (𝟙 (Spec (.of R))) ⟶
      (derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom :
          DerivedCategory (Spec (.of R)).Modules ⥤ DerivedCategory (Spec (.of R')).Modules) ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (.of R'))) ⋙
          (ModuleCat.restrictScalars φ).mapDerivedCategory :=
  Functor.whiskerRight (derivedAdjunction (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).unit
      (derivedGlobalSectionsOver (𝟙 (Spec (.of R)))) ≫
    Functor.whiskerLeft
      (derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom :
          DerivedCategory (Spec (.of R)).Modules ⥤ DerivedCategory (Spec (.of R')).Modules)
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso
        (Spec.map (CommRingCat.ofHom φ)) (𝟙 _) (𝟙 _) φ (specMap_comp_id_eq φ)).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The components of `AlgebraicGeometry.affineBaseChangeNatTrans` are the maps
`AlgebraicGeometry.affineBaseChangeMap`. -/
theorem affineBaseChangeNatTrans_app (P : DerivedCategory (Spec (.of R)).Modules) :
    (affineBaseChangeNatTrans φ).app P = affineBaseChangeMap φ P :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ(Spec R, P) ⊗_R^𝐋 R' ≅ RΓ(Spec R', Lg^*P)` by the canonical map.** For
`g = Spec φ` and `P` in `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves, the adjoint
transpose of `AlgebraicGeometry.affineBaseChangeMap` under any adjunction `L' ⊣ φ^*` of derived
categories of modules is an isomorphism. -/
theorem isIso_homEquiv_symm_affineBaseChangeMap
    {L' : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R')}
    (adj' : L' ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (P : DerivedCategory (Spec (.of R)).Modules)
    (hP : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj P).IsQuasicoherent) :
    IsIso ((adj'.homEquiv _ _).symm (affineBaseChangeMap φ P)) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  let LP : DerivedCategory (Spec (.of R')).Modules := (derivedPullback g.toLRSHom.toShHom).obj P
  have hLP : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj LP).IsQuasicoherent :=
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g P hP
  exact Adjunction.isIso_homEquiv_symm_map_unit_comp_app (derivedAdjunction g.toLRSHom.toShHom)
    adj' (derivedTildeGlobalSectionsAdjunction (CommRingCat.of R)).val
    (derivedTildeGlobalSectionsAdjunction (CommRingCat.of R')).val
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g (𝟙 _) (𝟙 _) φ
      (specMap_comp_id_eq φ)).hom P
    (isIso_derivedTildeGlobalSectionsAdjunction_counit_app (CommRingCat.of R) ⟨P, hP⟩)
    (isIso_derivedTildeGlobalSectionsAdjunction_counit_app (CommRingCat.of R') ⟨LP, hLP⟩)
    (isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of R'))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ(Spec R, P) ⊗_R^𝐋 R' ≅ RΓ(Spec R', Lg^*P)` by the derived base-change map.** For
`g = Spec φ` and `P` in `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves, the derived
base-change map `RΓ(Spec R, P) ⊗_R^𝐋 R' ⟶ RΓ(Spec R', Lg^*P)` adjoint to
`AlgebraicGeometry.affineBaseChangeMap` is an isomorphism. -/
theorem isIso_derivedBaseChangeComparison_affineBaseChangeMap
    (P : DerivedCategory (Spec (.of R)).Modules)
    (hP : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj P).IsQuasicoherent) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      (affineBaseChangeMap φ P)) :=
  isIso_homEquiv_symm_affineBaseChangeMap φ _ P hP

end AlgebraicGeometry

end
