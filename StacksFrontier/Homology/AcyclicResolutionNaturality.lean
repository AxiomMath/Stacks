module

public import StacksFrontier.Homology.CompositeCollapse

/-!
# Naturality of the computation of right derived functors by acyclic resolutions

`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic` identifies `Rⁿ T (X)` with the degree-`n`
cohomology of `T` applied to a resolution `ε : X[0] ⟶ K` of `X` by `T`-acyclic objects. This file
proves that the identification is natural: for resolutions `ε : X[0] ⟶ K`, `ε' : Y[0] ⟶ L`, a
morphism `φ : X ⟶ Y` and a morphism of complexes `Φ : K ⟶ L` compatible with the augmentations,
`Rⁿ T (φ)` corresponds to `Hⁿ (T (Φ))`.

## Main results

* `Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_hom_naturality`: the identification of
  `Rⁿ T (X)` with `Hⁿ (T (K))` is natural in the resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [HasInjectiveResolutions D] [EnoughInjectives D]
  (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

/-- **The computation of `Rⁿ T` by acyclic resolutions is natural**: for resolutions
`ε : X[0] ⟶ K` and `ε' : Y[0] ⟶ L` by `T`-acyclic objects and `Φ : K ⟶ L` compatible with
`φ : X ⟶ Y`, the map `Rⁿ T (φ)` corresponds to `Hⁿ (T (Φ))`. -/
theorem isoRightDerivedObjOfAcyclic_hom_naturality {X Y : D} {K L : CochainComplex D ℕ}
    (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε]
    (ε' : (CochainComplex.single₀ D).obj Y ⟶ L) [QuasiIso ε']
    (hK : ∀ q, acyclic T (K.X q)) (hL : ∀ q, acyclic T (L.X q))
    (φ : X ⟶ Y) (Φ : K ⟶ L) (hΦ : ε ≫ Φ = (CochainComplex.single₀ D).map φ ≫ ε') (n : ℕ) :
    (T.rightDerived n).map φ ≫ (isoRightDerivedObjOfAcyclic T ε' hL n).hom =
      (isoRightDerivedObjOfAcyclic T ε hK n).hom ≫
        (HomologicalComplex.homologyFunctor E _ n).map ((T.mapHomologicalComplex _).map Φ) := by
  let JX := injectiveResolution X
  let JY := injectiveResolution Y
  let βX := descOfResolution ε JX
  let βY := descOfResolution ε' JY
  let ψ := InjectiveResolution.desc φ JY JX
  have hψ : JX.ι.f 0 ≫ ψ.f 0 = φ ≫ JY.ι.f 0 := InjectiveResolution.desc_commutes_zero φ JY JX
  have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality φ JX JY ψ hψ T n
  have hw : ε ≫ (βX ≫ ψ) = ε ≫ (Φ ≫ βY) := by
    rw [← Category.assoc, comp_descOfResolution, ← Category.assoc, hΦ, Category.assoc,
      comp_descOfResolution]
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    show JX.ι.f 0 ≫ ψ.f 0 = ((CochainComplex.single₀ D).map φ).f 0 ≫ JY.ι.f 0
    rw [hψ, CochainComplex.single₀_map_f_zero]
    rfl
  obtain ⟨h⟩ := InjectiveResolution.nonempty_descHomotopy_of_quasiIso JY ε hw
  have h2 : HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map βX) n ≫
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map ψ) n =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map Φ) n ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map βY) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    exact (T.mapHomotopy h).homologyMap_eq n
  have h1' : (JX.isoRightDerivedObj T n).inv ≫ (T.rightDerived n).map φ =
      (T.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map ψ ≫
        (JY.isoRightDerivedObj T n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key : (isoRightDerivedObjOfAcyclic T ε hK n).inv ≫ (T.rightDerived n).map φ =
      (HomologicalComplex.homologyFunctor E _ n).map ((T.mapHomologicalComplex _).map Φ) ≫
        (isoRightDerivedObjOfAcyclic T ε' hL n).inv :=
    (Category.assoc (HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map βX) n)
      (JX.isoRightDerivedObj T n).inv ((T.rightDerived n).map φ)).trans
      ((congrArg (HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map βX) n ≫ ·)
        h1').trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (JY.isoRightDerivedObj T n).inv) h2).trans (Category.assoc _ _ _))))
  rw [← Iso.inv_comp_eq, ← Category.assoc, key, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Stacks.RightDerivedComp

end
