module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedSectionsBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSndComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompOfEqConjugate
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePasting

/-!
# `RΓ(X, Rg'_* -) = RΓ(X', -)` over an affine base, for two stacked squares

For morphisms `g : U' ⟶ U` and `g₂ : U'' ⟶ U'` between objects with affine underlying schemes,
`R → R' → R''` the maps of rings of global functions, and two stacked commutative squares

```
X'' --g₂'--> X' --g'--> X
|f''         |f'        |f
U'' --g₂-->  U' --g-->  U
```

the square `affineBaseDerivedSectionsSquareIso` of the outer rectangle is the pasting of the
squares of the two halves, and the identification `affineBaseDerivedSectionsPushforwardIso`,
`RΓ(X, Rg'_* -) ≅ RΓ(X', -)` read in `D(R)`, of the outer rectangle is the one of the right
square followed by the one of the left square, through `Rg'_* Rg₂'_* ⟶ R(g₂' ≫ g')_*` and the
composition law of derived restriction of scalars.

## Main results

* `AlgebraicGeometry.Space.affineBaseDerivedSectionsSquareIso_hom_app_comp`.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardIso_hom_comp`, and
  `AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardIso_hom_comp_of_eq` along equations.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

section PushforwardIsoComp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
  (w₃ : (g₂' ≫ g') ≫ f = f'' ≫ representedSpaceMap B S hS (g₂ ≫ g))

/-- **The square of `RΓ` over an affine base for two stacked squares** is the pasting of the
squares of the two halves, through the composition laws of derived extensions of scalars and of
derived pullbacks. This is read off `affineBaseDerivedSectionsBaseChangeMap_comp`, the base change
map determining the square. -/
theorem affineBaseDerivedSectionsSquareIso_hom_app_comp
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (affineBaseDerivedSectionsSquareIso B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃).hom.app M =
      (representedAffineDerivedAssociated B S hS U'' ⋙
          smallEtaleDerivedModulePullback B S hS f'').map
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
          (representedAffineRingHom_comp B S hS g₂ g).symm).inv.app M) ≫
        (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂).hom.app
          ((representedAffineDerivedExtension B S hS g).functor.obj M) ≫
        (smallEtaleDerivedModulePullback B S hS g₂').map
          ((affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom.app M) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g').hom.app
          ((representedAffineDerivedAssociated B S hS U ⋙
            smallEtaleDerivedModulePullback B S hS f).obj M) :=
  squareIso_hom_app_eq_of_baseChangeMap (aF := affineBaseDerivedSectionsAdjunction B S hS f)
    (aF₁ := affineBaseDerivedSectionsAdjunction B S hS f')
    (aF₂ := affineBaseDerivedSectionsAdjunction B S hS f'')
    (s₁ := affineBaseDerivedSectionsSquareIso B S hS g f f' g' w)
    (s₂ := affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂)
    (s₀ := affineBaseDerivedSectionsSquareIso B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃)
    (ρ := RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
      (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineCommRingCatHom B S hS g₂).hom
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
      (representedAffineRingHom_comp B S hS g₂ g).symm)
    (γ := smallEtaleDerivedModulePullbackCompIso B S hS g₂' g')
    (fun K => affineBaseDerivedSectionsBaseChangeMap_comp B S hS g g₂ f f' f'' g' g₂' w w₂ w₃ K) M

/-- **`RΓ(X, Rg'_* -) = RΓ(X', -)` for two stacked squares**: the identification of the outer
rectangle, after `RΓ(X, -)` of `Rg'_* Rg₂'_* ⟶ R(g₂' ≫ g')_*`, is the one of the right square at
`Rg₂'_*` followed by the one of the left square and the conjugate of the composition law of derived
extension of scalars `R → R' → R''`. -/
theorem affineBaseDerivedSectionsPushforwardIso_hom_comp :
    Functor.whiskerRight (smallEtaleDerivedPushforwardCompConjugate g₂' g')
        (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U) ≫
      (affineBaseDerivedSectionsPushforwardIso B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃).hom =
    Functor.whiskerLeft _ (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w).hom ≫
      Functor.whiskerRight (affineBaseDerivedSectionsPushforwardIso B S hS g₂ f' f'' g₂' w₂).hom
        (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory ≫
      Functor.whiskerLeft
        (derivedModulePushforward B S hS f'' ⋙ representedAffineDerivedSections B S hS U'')
        (conjugateEquiv ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g).hom).comp
          (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
            (representedAffineCommRingCatHom B S hS g₂).hom))
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom)
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
          (representedAffineRingHom_comp B S hS g₂ g).symm).inv) :=
  conjugateIsoEquiv_pasting_of_baseChangeMap_natTrans (affineBaseDerivedSectionsAdjunction B S hS f)
    (affineBaseDerivedSectionsAdjunction B S hS f') (affineBaseDerivedSectionsAdjunction B S hS f'')
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₂).hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom)
    (smallEtaleDerivedModuleAdjunction B S hS g') (smallEtaleDerivedModuleAdjunction B S hS g₂')
    (smallEtaleDerivedModuleAdjunction B S hS (g₂' ≫ g'))
    (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w)
    (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂)
    (affineBaseDerivedSectionsSquareIso B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
      (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineCommRingCatHom B S hS g₂).hom
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
      (representedAffineRingHom_comp B S hS g₂ g).symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g')
    (fun K => affineBaseDerivedSectionsBaseChangeMap_comp B S hS g g₂ f f' f'' g' g₂' w w₂ w₃ K)

omit w₃ in
/-- **`affineBaseDerivedSectionsPushforwardIso_hom_comp` along equations** `g₂ ≫ g = g₃` and
`g₂' ≫ g' = g₃'`, with the comparison `Rg'_* Rg₂'_* ⟶ Rg₃'_*` the conjugate of the composition
isomorphism `Lg'^* ⋙ Lg₂'^* ≅ Lg₃'^*` and the comparison of restrictions of scalars
`derivedRestrictScalarsComp`. -/
theorem affineBaseDerivedSectionsPushforwardIso_hom_comp_of_eq (g₃ : U'' ⟶ U) (hg : g₂ ≫ g = g₃)
    (g₃' : X'' ⟶ X) (hg' : g₂' ≫ g' = g₃') (w₃ : g₃' ≫ f = f'' ≫ representedSpaceMap B S hS g₃)
    (hc : (representedAffineCommRingCatHom B S hS g₃).hom =
      (representedAffineCommRingCatHom B S hS g₂).hom.comp
        (representedAffineCommRingCatHom B S hS g).hom) :
    Functor.whiskerRight (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g').comp
          (smallEtaleDerivedModuleAdjunction B S hS g₂'))
          (smallEtaleDerivedModuleAdjunction B S hS g₃')
          (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hg').inv)
        (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U) ≫
      (affineBaseDerivedSectionsPushforwardIso B S hS g₃ f f'' g₃' w₃).hom =
    Functor.whiskerLeft _ (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w).hom ≫
      Functor.whiskerRight (affineBaseDerivedSectionsPushforwardIso B S hS g₂ f' f'' g₂' w₂).hom
        (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory ≫
      Functor.whiskerLeft
        (derivedModulePushforward B S hS f'' ⋙ representedAffineDerivedSections B S hS U'')
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS g₃).hom hc).hom := by
  subst hg hg'
  rw [← StacksDraft.DerivedInverseLimit.conjugateEquiv_totalDerivedExtensionScalarsCompOfEq_inv
    (representedAffineCommRingCatHom B S hS g).hom (representedAffineCommRingCatHom B S hS g₂).hom
    (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom hc.symm]
  have hr : smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS (rfl : g₂' ≫ g' = g₂' ≫ g') =
        smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' := Iso.trans_refl _
  rw [hr]
  exact affineBaseDerivedSectionsPushforwardIso_hom_comp B S hS g g₂ f f' f'' g' g₂' w w₂ w₃

end PushforwardIsoComp

end AlgebraicGeometry.Space

end
