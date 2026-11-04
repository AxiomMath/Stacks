module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeTriangle

/-!
# Transitivity of the base change map of `RΓ` over an affine base

For morphisms `g : U' ⟶ U` and `g₂ : U'' ⟶ U'` between objects with affine underlying schemes,
`R → R' → R''` the maps of rings of global functions, and two stacked commutative squares

```
X'' --g₂'--> X' --g'--> X
|f''         |f'        |f
U'' --g₂-->  U' --g-->  U
```

the base change map `RΓ(X, H) ⊗ᴸ_R R'' ⟶ RΓ(X'', L(g₂' ≫ g')^*H)` of the outer rectangle is
`- ⊗ᴸ_{R'} R''` of the one of the right square followed by the one of the left square, through the
composition laws of derived extensions of scalars and of derived pullbacks.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedSectionsBaseChangeMap_comp`: the affine case.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsBaseChangeMap_comp`: the general case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace Stacks.CategoryTheory.BaseChange

/-- Inverting an identity between two threefold composites of isomorphisms. -/
theorem inv_comp₃_eq_of_comp₃_eq {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ Y₁ Y₂ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₀ ≅ Y₁) (e : Y₁ ≅ Y₂) (f : Y₂ ≅ X₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    c.inv ≫ b.inv ≫ a.inv ≫ d.hom ≫ e.hom = f.inv := by
  rw [← cancel_mono f.hom, Iso.inv_hom_id]
  simp only [Category.assoc, ← h, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-- **Horizontal composition of base change maps of squares with an identity side.**  For three
adjunctions `F ⊣ R`, `F' ⊣ R'`, `F'' ⊣ R''` and isomorphisms `β : F ⋙ G ≅ H ⋙ F'`,
`β' : F' ⋙ G' ≅ H' ⋙ F''`, `β₀ : F ⋙ G₀ ≅ H₀ ⋙ F''` compatible with `eG : G ⋙ G' ≅ G₀` and
`eH : H ⋙ H' ≅ H₀`, the base change maps of the squares `(β⁻¹, 1)` compose. -/
theorem map_symm_refl_horizontal {A : Type u₁} {A' : Type u₂} {A'' : Type u₃} {B : Type u₄}
    {B' : Type u₅} {B'' : Type u₆} [Category.{v₁} A] [Category.{v₂} A'] [Category.{v₃} A'']
    [Category.{v₄} B] [Category.{v₅} B'] [Category.{v₆} B'']
    {F : B ⥤ A} {R : A ⥤ B} {F' : B' ⥤ A'} {R' : A' ⥤ B'} {F'' : B'' ⥤ A''} {R'' : A'' ⥤ B''}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (adj'' : F'' ⊣ R'')
    {G : A ⥤ A'} {G' : A' ⥤ A''} {H : B ⥤ B'} {H' : B' ⥤ B''} {G₀ : A ⥤ A''} {H₀ : B ⥤ B''}
    (eG : G ⋙ G' ≅ G₀) (eH : H ⋙ H' ≅ H₀) (β : F ⋙ G ≅ H ⋙ F') (β' : F' ⋙ G' ≅ H' ⋙ F'')
    (β₀ : F ⋙ G₀ ≅ H₀ ⋙ F'')
    (hs : ∀ M, F''.map (eH.inv.app M) ≫ β'.inv.app (H.obj M) ≫ G'.map (β.inv.app M) ≫
      eG.hom.app (F.obj M) = β₀.inv.app M) (K : A) :
    eH.inv.app (R.obj K) ≫ H'.map (map adj adj' β.symm (Iso.refl _) K) ≫
        map adj' adj'' β'.symm (Iso.refl _) (G.obj K) ≫ R''.map (eG.hom.app K) =
      map adj adj'' β₀.symm (Iso.refl _) K := by
  refine Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal adj adj' adj'' eG eH
    (fun M => β.inv.app M) β'.inv (𝟙 _) (𝟙 _) (fun M => β₀.inv.app M) (fun M => ?_) K _ _ _
    ?_ ?_ ?_
  · simpa only [NatTrans.id_app, Category.comp_id] using hs M
  all_goals rw [homEquiv_symm_map]; simp

/-- Bookkeeping for the transitivity of a base change map that factors as `r ≫ R(b)`: the
naturality `hn` of the second map, the pasting `hh` of the second factors and the transitivity
`ha` of the first factors give the transitivity of the composites. -/
theorem comp_assemble {C D E : Type*} [Category* C] [Category* D] [Category* E] (L : C ⥤ D)
    (R : E ⥤ D) {A : D} {B₀ B₁ B₂ : C} {E₀ E₁ E₂ E₃ E₄ E₅ : E} (i : A ⟶ L.obj B₀)
    {bc₁ : B₀ ⟶ B₂} {r₁ : B₀ ⟶ B₁} {b₁ : B₁ ⟶ B₂} (hb₁ : bc₁ = r₁ ≫ b₁)
    {bc₂ : L.obj B₂ ⟶ R.obj E₂} {r₂ : L.obj B₂ ⟶ R.obj E₁} {v : E₁ ⟶ E₂}
    (hb₂ : bc₂ = r₂ ≫ R.map v) (x : E₂ ⟶ E₃) {r₂' : L.obj B₁ ⟶ R.obj E₀} {u' : E₀ ⟶ E₁}
    (hn : L.map b₁ ≫ r₂ = r₂' ≫ R.map u') {y₁ : E₀ ⟶ E₄} {y₂ : E₄ ⟶ E₅} {z : E₅ ⟶ E₃}
    (hh : u' ≫ v ≫ x = y₁ ≫ y₂ ≫ z) {r₃ : A ⟶ R.obj E₅}
    (ha : i ≫ L.map r₁ ≫ r₂' ≫ R.map (y₁ ≫ y₂) = r₃) {bc₃ : A ⟶ R.obj E₃}
    (hb₃ : bc₃ = r₃ ≫ R.map z) :
    i ≫ L.map bc₁ ≫ bc₂ ≫ R.map x = bc₃ := by
  subst hb₁ hb₂ hb₃ ha
  rw [L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← R.map_comp, Category.assoc, hh]

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Affine

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')

/-- The composition law of the affine base change isomorphisms along a triangle, for their
inverses. -/
theorem representedAffineDerivedBaseChangeIso_inv_comp
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (representedAffineDerivedAssociated B S hS U'').map
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
          (representedAffineRingHom_comp B S hS g₂ g).symm).inv.app M) ≫
      (representedAffineDerivedBaseChangeIso B S hS g₂).inv.app
        ((representedAffineDerivedExtension B S hS g).functor.obj M) ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).map
        ((representedAffineDerivedBaseChangeIso B S hS g).inv.app M) ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
        (representedSpaceMap B S hS g)).hom.app
          ((representedAffineDerivedAssociated B S hS U).obj M) ≫
      (eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ)
        (representedSpaceMap_comp B S hS g₂ g).symm)).inv.app
        ((representedAffineDerivedAssociated B S hS U).obj M) =
    (representedAffineDerivedBaseChangeIso B S hS (g₂ ≫ g)).inv.app M :=
  Stacks.CategoryTheory.BaseChange.inv_comp₃_eq_of_comp₃_eq
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).mapIso
      ((representedAffineDerivedBaseChangeIso B S hS g).app M))
    ((representedAffineDerivedBaseChangeIso B S hS g₂).app
      ((representedAffineDerivedExtension B S hS g).functor.obj M))
    ((representedAffineDerivedAssociated B S hS U'').mapIso
      ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
          (representedAffineRingHom_comp B S hS g₂ g).symm).app M))
    ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
        (representedSpaceMap B S hS g)).app ((representedAffineDerivedAssociated B S hS U).obj M))
    ((eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ)
        (representedSpaceMap_comp B S hS g₂ g).symm)).app
        ((representedAffineDerivedAssociated B S hS U).obj M)).symm
    ((representedAffineDerivedBaseChangeIso B S hS (g₂ ≫ g)).app M)
    (representedAffineToposDerivedBaseChange_comp B S hS g g₂ M)

/-- **Transitivity of the affine base change map of `RΓ`**: `- ⊗ᴸ_{R'} R''` of the base change
map along `g` followed by the one along `g₂` is the one along `g₂ ≫ g`, through the composition
laws of derived extensions of scalars and of derived pullbacks. -/
theorem representedAffineDerivedSectionsBaseChangeMap_comp
    (F : DerivedCategory
      (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) :
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g).symm).inv.app
        ((representedAffineDerivedSections B S hS U).obj F) ≫
      (representedAffineDerivedExtension B S hS g₂).functor.map
        (representedAffineDerivedSectionsBaseChangeMap B S hS g F) ≫
      representedAffineDerivedSectionsBaseChangeMap B S hS g₂
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj F) ≫
      (representedAffineDerivedSections B S hS U'').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
            (representedSpaceMap B S hS g)).hom.app F ≫
          (eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ)
            (representedSpaceMap_comp B S hS g₂ g).symm)).inv.app F) =
    representedAffineDerivedSectionsBaseChangeMap B S hS (g₂ ≫ g) F :=
  Stacks.CategoryTheory.BaseChange.map_symm_refl_horizontal
    (representedAffineDerivedAdjunction B S hS U) (representedAffineDerivedAdjunction B S hS U')
    (representedAffineDerivedAdjunction B S hS U'')
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
        (representedSpaceMap B S hS g) ≪≫
      (eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ)
        (representedSpaceMap_comp B S hS g₂ g).symm)).symm)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g).symm)
    (representedAffineDerivedBaseChangeIso B S hS g)
    (representedAffineDerivedBaseChangeIso B S hS g₂)
    (representedAffineDerivedBaseChangeIso B S hS (g₂ ≫ g))
    (representedAffineDerivedBaseChangeIso_inv_comp B S hS g g₂) F

end Affine

section Congr

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits


variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- The base change map of Stacks 07A7 along equal morphisms `h = h'`, through the transport of
derived pullbacks. -/
theorem smallEtaleDerivedBaseChangeMap_congr (f : X ⟶ Y) {h h' : Y' ⟶ Y} (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (e : h = h') (w : g' ≫ f = f' ≫ h) (w' : g' ≫ f = f' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedModuleBaseChangeMap B S hS f h' f' g' w' K =
      (eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ) e)).inv.app _ ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS f h f' g' w K := by
  subst e
  simp

end Congr

section General

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits


variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
  (w₃ : (g₂' ≫ g') ≫ f = f'' ≫ representedSpaceMap B S hS (g₂ ≫ g))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] in
/-- Stacks 07A7 for two stacked squares over affines, with the composite of the represented
maps read as the represented map of the composite. -/
theorem smallEtaleDerivedBaseChangeMap_comp_represented
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).map
        (smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS g) f' g' w H) ≫
      smallEtaleDerivedModuleBaseChangeMap B S hS f' (representedSpaceMap B S hS g₂) f'' g₂' w₂
        ((smallEtaleDerivedModulePullback B S hS g').obj H) ≫
      (derivedModulePushforward B S hS f'').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g₂' g').hom.app H) =
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
        (representedSpaceMap B S hS g)).hom.app
        ((derivedModulePushforward B S hS f).obj H) ≫
      (eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback B S hS φ)
        (representedSpaceMap_comp B S hS g₂ g).symm)).inv.app
        ((derivedModulePushforward B S hS f).obj H) ≫
      smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS (g₂ ≫ g)) f''
        (g₂' ≫ g') w₃ H := by
  refine (Iso.inv_comp_eq ((smallEtaleDerivedModulePullbackCompIso B S hS
    (representedSpaceMap B S hS g₂) (representedSpaceMap B S hS g)).app
      ((derivedModulePushforward B S hS f).obj H))).1 (Eq.trans ?_
    (smallEtaleDerivedBaseChangeMap_congr B S hS f f'' (g₂' ≫ g')
      (representedSpaceMap_comp B S hS g₂ g).symm w₃
      (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g₂'
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS g₂) w w₂) H))
  exact smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g₂'
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS g₂) w w₂ H

/-- **Transitivity of the base change map of `RΓ` over an affine base**: for two stacked
squares, `- ⊗ᴸ_{R'} R''` of the base change map of the right square followed by the one of the
left square is the one of the outer rectangle, through the composition laws of derived extensions
of scalars and of derived pullbacks. -/
theorem affineBaseDerivedSectionsBaseChangeMap_comp
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g).symm).inv.app
        ((representedAffineDerivedSections B S hS U).obj
          ((derivedModulePushforward B S hS f).obj H)) ≫
      (representedAffineDerivedExtension B S hS g₂).functor.map
        (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w H) ≫
      affineBaseDerivedSectionsBaseChangeMap B S hS g₂ f' f'' g₂' w₂
        ((smallEtaleDerivedModulePullback B S hS g').obj H) ≫
      (representedAffineDerivedSections B S hS U'').map ((derivedModulePushforward B S hS f'').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g₂' g').hom.app H)) =
    affineBaseDerivedSectionsBaseChangeMap B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃ H := by
  have hn : (representedAffineDerivedExtension B S hS g₂).functor.map
        ((representedAffineDerivedSections B S hS U').map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f
            (representedSpaceMap B S hS g) f' g' w H)) ≫
      representedAffineDerivedSectionsBaseChangeMap B S hS g₂
        ((derivedModulePushforward B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj H)) =
      representedAffineDerivedSectionsBaseChangeMap B S hS g₂
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((derivedModulePushforward B S hS f).obj H)) ≫
      (representedAffineDerivedSections B S hS U'').map
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f
            (representedSpaceMap B S hS g) f' g' w H)) :=
    Stacks.CategoryTheory.BaseChange.map_naturality _ _ _ _ _
  exact Stacks.CategoryTheory.BaseChange.comp_assemble _ _ _
    (affineBaseDerivedSectionsBaseChangeMap_eq B S hS g f f' g' w H)
    (affineBaseDerivedSectionsBaseChangeMap_eq B S hS g₂ f' f'' g₂' w₂ _) _ hn
    (smallEtaleDerivedBaseChangeMap_comp_represented B S hS g g₂ f f' f'' g' g₂' w w₂ w₃ H)
    (representedAffineDerivedSectionsBaseChangeMap_comp B S hS g g₂
      ((derivedModulePushforward B S hS f).obj H))
    (affineBaseDerivedSectionsBaseChangeMap_eq B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃ H)

end General

end AlgebraicGeometry.Space

end
