module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.Algebra.Homology.ShortComplex.ShortExactMkOfIso

/-!
# The conormal sequence of two stacked squares as the pullback of a sequence of ideal sheaves

Let `W ⟶ X₀`, `Z ⟶ X₁` and `Y ⟶ X₂` be morphisms of ringed spaces, with ideal sheaves
`𝓘_W`, `𝓘_Z` and `𝓘_Y`, and let two commutative squares carry the first into the second along
`g₀ : X₀ ⟶ X₁` and the second into the third along `g₁ : X₁ ⟶ X₂`.  The two morphisms of conormal
sheaves `Stacks.ClosedImmersion.conormalSheafMap` form a sequence

```
  f₀^*f₁^*𝒞_{Y/X₂} ⟶ f₀^*𝒞_{Z/X₁} ⟶ 𝒞_{W/X₀}
```

whose first arrow is the pullback along `f₀ : W ⟶ Z` of the morphism of the lower square.  Each
morphism of conormal sheaves is the identification `Stacks.ClosedImmersion.pullbackCompIso`
followed by the pullback along `ι : W ⟶ X₀` of a morphism of ideal sheaves, and the
identifications are natural, so the sequence is isomorphic to the pullback along `ι` of

```
  g₀^*g₁^*𝓘_Y ⟶ g₀^*𝓘_Z ⟶ 𝓘_W .
```

The two sequences are therefore short exact together.

## Main results

* `Stacks.ClosedImmersion.pullbackCompIso_hom_naturality`: the identification
  `f^*j^* ≅ i^*k^*` of a commutative square is natural.
* `Stacks.ClosedImmersion.shortExact_conormalSequence_iff_idealForm`: the sequence of conormal
  sheaves is short exact exactly when the pullback of the sequence of ideal sheaves is.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- **The identification `f^*j^* ≅ i^*k^*` of a commutative square is natural.** -/
theorem pullbackCompIso_hom_naturality {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'}
    {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'} (comm : i ≫ k = f ≫ j)
    {M N : SheafOfModules.{u} (structureSheafRing W')} (φ : M ⟶ N) :
    (modulePullback f).map ((modulePullback j).map φ) ≫ (pullbackCompIso comm N).hom =
      (pullbackCompIso comm M).hom ≫ (modulePullback i).map ((modulePullback k).map φ) := by
  have h₁ := (modulePullbackComp f j).inv.naturality φ
  have h₂ := (modulePullbackCongr comm.symm).hom.naturality φ
  have h₃ := (modulePullbackComp i k).hom.naturality φ
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [pullbackCompIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

section Composition

variable {Z₀ Z₁ Z₂ X₀ X₁ X₂ : RingedSpace.{u, u}} {i₀ : Z₀ ⟶ X₀} {i₁ : Z₁ ⟶ X₁} {i₂ : Z₂ ⟶ X₂}
  {f₀ : Z₀ ⟶ Z₁} {g₀ : X₀ ⟶ X₁} {f₁ : Z₁ ⟶ Z₂} {g₁ : X₁ ⟶ X₂}

/-- **The map of ideal sheaves of a vertically stacked pair of squares** is the composition
comparison of the pullbacks, followed by the pullback of the map of the lower square, followed by
the map of the upper square.  Both sides lift the same morphism into `𝒪_{X₀}` through the
monomorphism `𝓘₀ ⟶ 𝒪_{X₀}`. -/
theorem idealSheafMap_comp (c₀ : i₀ ≫ g₀ = f₀ ≫ i₁) (c₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (c : i₀ ≫ g₀ ≫ g₁ = (f₀ ≫ f₁) ≫ i₂) :
    idealSheafMap c = (modulePullbackComp g₀ g₁).hom.app (idealSheaf i₂) ≫
      (modulePullback g₀).map (idealSheafMap c₁) ≫ idealSheafMap c₀ := by
  have : Mono (idealSheafι i₀) := inferInstanceAs (Mono (kernel.ι _))
  rw [← cancel_mono (idealSheafι i₀), idealSheafMap_comp_ι, Category.assoc, Category.assoc,
    idealSheafMap_comp_ι, ← Functor.map_comp_assoc, idealSheafMap_comp_ι, Functor.map_comp,
    Category.assoc]
  have hnat := (modulePullbackComp g₀ g₁).hom.naturality (idealSheafι i₂)
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat.symm]
  congr 1
  exact (Stacks.Conormal.modulePullbackUnitToUnit_comp g₁ g₀).symm

/-- The map of ideal sheaves of a commutative square, transported along an equality of the
morphisms of ambient spaces. -/
theorem idealSheafMap_congr {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f f' : Z ⟶ W} {k k' : Z' ⟶ W'} (hk : k = k') (comm : i ≫ k = f ≫ j)
    (comm' : i ≫ k' = f' ≫ j) :
    idealSheafMap comm =
      (eqToHom (congrArg (fun g => modulePullback g) hk)).app (idealSheaf j) ≫
        idealSheafMap comm' := by
  subst hk
  exact (Category.id_comp _).symm

end Composition

section Squares

variable {W X₀ Z X₁ Y X₂ : RingedSpace.{u, u}} (ιW : W ⟶ X₀) (ιZ : Z ⟶ X₁) (ιY : Y ⟶ X₂)
  (g₀ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₂) (f₀ : W ⟶ Z) (f₁ : Z ⟶ Y)
  (comm₀ : ιW ≫ g₀ = f₀ ≫ ιZ) (comm₁ : ιZ ≫ g₁ = f₁ ≫ ιY)

/-- **The first arrow of the conormal sequence of two stacked squares, read at the middle term
through the identification of the upper square, is a pullback of a morphism of ideal sheaves.**
-/
theorem map_conormalSheafMap_comp_pullbackCompIso :
    (modulePullback f₀).map (conormalSheafMap comm₁) ≫ (pullbackCompIso comm₀ (idealSheaf ιZ)).hom =
      ((modulePullback f₀).map (pullbackCompIso comm₁ (idealSheaf ιY)).hom ≫
          (pullbackCompIso comm₀ ((modulePullback g₁).obj (idealSheaf ιY))).hom) ≫
        (modulePullback ιW).map ((modulePullback g₀).map (idealSheafMap comm₁)) := by
  rw [conormalSheafMap, Functor.map_comp, Category.assoc, Category.assoc,
    pullbackCompIso_hom_naturality comm₀ (idealSheafMap comm₁)]

/-- **The conormal sequence of two stacked squares is short exact exactly when the pullback along
`ι : W ⟶ X₀` of the sequence of ideal sheaves `g₀^*g₁^*𝓘_Y ⟶ g₀^*𝓘_Z ⟶ 𝓘_W` is.** -/
theorem shortExact_conormalSequence_iff_idealForm :
    (∃ h : (modulePullback f₀).map (conormalSheafMap comm₁) ≫ conormalSheafMap comm₀ = 0,
        (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : (modulePullback ιW).map ((modulePullback g₀).map (idealSheafMap comm₁)) ≫
          (modulePullback ιW).map (idealSheafMap comm₀) = 0,
        (ShortComplex.mk _ _ h).ShortExact :=
  CategoryTheory.ShortComplex.exists_shortExact_mk_iff_of_isIso _ _ _ _
    ((modulePullback f₀).map (pullbackCompIso comm₁ (idealSheaf ιY)).hom ≫
      (pullbackCompIso comm₀ ((modulePullback g₁).obj (idealSheaf ιY))).hom)
    (pullbackCompIso comm₀ (idealSheaf ιZ)).hom
    (map_conormalSheafMap_comp_pullbackCompIso ιW ιZ ιY g₀ g₁ f₀ f₁ comm₀ comm₁) rfl

end Squares

end Stacks.ClosedImmersion

end
