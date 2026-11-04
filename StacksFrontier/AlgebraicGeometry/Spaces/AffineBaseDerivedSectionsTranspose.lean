module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposDerivedCategory
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel

/-!
# The transpose of `RΓ(X, a)` followed by `RΓ(X, Rg'_* -) ≅ RΓ(X', -)`

Let `g : U' ⟶ U` be a morphism of the big fppf site with affine source and target,
`R = Γ(U, 𝒪)`, `R' = Γ(U', 𝒪)`, and consider a commutative square of algebraic spaces

```
X' --g'--> X
|f'        |f
U' --g---> U
```

For `H ∈ D(𝒪_X)`, `Y ∈ D(𝒪_{X'})`, a map `a : H ⟶ Rg'_*Y` and `z : RΓ(X', Y) ⟶ W` in `D(R')`, the
composite

`RΓ(X, H) ⟶ RΓ(X, Rg'_*Y) ≅ RΓ(X', Y) ⟶ W`

of `D(R)` (`AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardIso` in the middle, the
last two read in `D(R)` by restriction of scalars) has as transpose, under derived extension and
restriction of scalars along `R ⟶ R'`, the base change map
`RΓ(X, H) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*H)` followed by `RΓ(X', -)` of the transpose
`L(g')^*H ⟶ Y` of `a` and by `z`.

## Main definitions

* `AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardComp`: the composite above.

## Main results

* `homEquiv_symm_map_comp_conjugateIsoEquiv_hom_app`: the abstract statement for a square of
  adjunctions.
* `AlgebraicGeometry.Space.homEquiv_symm_affineBaseDerivedSectionsPushforwardComp`: its transpose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### The transpose of a map through the conjugate of a square of left adjoints -/

section Abstract

variable {𝒜 ℬ 𝒜' ℬ' : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒜'] [Category* ℬ']
  {Lf : 𝒜 ⥤ ℬ} {Rf : ℬ ⥤ 𝒜} {Lf' : 𝒜' ⥤ ℬ'} {Rf' : ℬ' ⥤ 𝒜'} {Lg : 𝒜 ⥤ 𝒜'} {Rg : 𝒜' ⥤ 𝒜}
  {Lg' : ℬ ⥤ ℬ'} {Rg' : ℬ' ⥤ ℬ} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (ag : Lg ⊣ Rg)
  (ag' : Lg' ⊣ Rg') (e : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- **The transpose of `Rf(a)` followed by the conjugate of a square of left adjoints**: for
`a : H ⟶ Rg' Y` and `z : Rf' Y ⟶ W`, the transpose under `Lg ⊣ Rg` of
`Rf(a) ≫ (Rg' ⋙ Rf ≅ Rf' ⋙ Rg)_Y ≫ Rg(z)` is the base change map at `H` followed by `Rf'` of the
transpose of `a` under `Lg' ⊣ Rg'` and by `z`. -/
theorem homEquiv_symm_map_comp_conjugateIsoEquiv_hom_app {H : ℬ} {Y : ℬ'} {W : 𝒜'}
    (a : H ⟶ Rg'.obj Y) (z : Rf'.obj Y ⟶ W) :
    (ag.homEquiv _ _).symm (Rf.map a ≫
        (conjugateIsoEquiv (adjf.comp ag') (ag.comp adjf') e).hom.app Y ≫ Rg.map z) =
      Stacks.CategoryTheory.BaseChange.map adjf adjf' e (Iso.refl _) H ≫
        Rf'.map ((ag'.homEquiv _ _).symm a) ≫ z := by
  set â := (ag'.homEquiv _ _).symm a with hâ
  have ha : a = ag'.unit.app H ≫ Rg'.map â := by
    rw [hâ]
    exact ((ag'.homEquiv _ _).apply_symm_apply a).symm.trans (ag'.homEquiv_unit _ _ _)
  have hc : (Stacks.CategoryTheory.BaseChange.pullbackComparison e (Iso.refl _)).natTrans =
      e.hom := by
    ext X
    simp [Stacks.CategoryTheory.BaseChange.pullbackComparison]
  have hβ := Stacks.CategoryTheory.BaseChange.homEquiv_map_eq_unit_comp adjf adjf' e (Iso.refl _)
    ag ag' H
  rw [hc] at hβ
  have hn := (conjugateIsoEquiv (adjf.comp ag') (ag.comp adjf') e).hom.naturality â
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, ha, Functor.map_comp,
    Category.assoc, hn, ← Category.assoc]
  change (ag.homEquiv _ _).symm ((Rf.map (ag'.unit.app H) ≫
      (conjugateEquiv (adjf.comp ag') (ag.comp adjf') e.hom).app (Lg'.obj H)) ≫
        Rg.map (Rf'.map â)) ≫ z = _
  rw [← hβ, Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.id_obj, Equiv.symm_apply_apply, Category.assoc]

end Abstract

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  {X X' : AlgebraicSpaces B S hS} (g : U' ⟶ U)
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)

/-- **`RΓ(X, a)` followed by `RΓ(X, Rg'_* -) ≅ RΓ(X', -)` and `z`**: for `a : H ⟶ Rg'_*Y` and
`z : RΓ(X', Y) ⟶ W` in `D(R')`, the composite `RΓ(X, H) ⟶ RΓ(X, Rg'_*Y) ≅ RΓ(X', Y) ⟶ W` of
`D(R)`, the last two read in `D(R)` by restriction of scalars along `R ⟶ R'`. -/
def affineBaseDerivedSectionsPushforwardComp
    {H : smallEtaleToposDerivedCategory X} {Y : smallEtaleToposDerivedCategory X'}
    {W : StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)}
    (a : H ⟶ (derivedModulePushforward B S hS g').obj Y)
    (z : (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').obj Y ⟶
      W) :
    (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U).obj H ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g).hom).obj W :=
  (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U).map a ≫
    (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w).hom.app Y ≫
    (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g).hom).map z

/-- **The transpose of `affineBaseDerivedSectionsPushforwardComp`** under derived extension and
restriction of scalars along `R ⟶ R'` is the base change map `RΓ(X, H) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*H)`
followed by `RΓ(X', -)` of the transpose `L(g')^*H ⟶ Y` of `a` and by `z`. -/
theorem homEquiv_symm_affineBaseDerivedSectionsPushforwardComp
    {H : smallEtaleToposDerivedCategory X} {Y : smallEtaleToposDerivedCategory X'}
    {W : StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)}
    (a : H ⟶ (derivedModulePushforward B S hS g').obj Y)
    (z : (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').obj Y ⟶
      W) :
    ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom B S hS g).hom).homEquiv _ _).symm
      (affineBaseDerivedSectionsPushforwardComp B S hS g f f' g' w a z) =
      affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w H ≫
        (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
          (((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _).symm a) ≫ z := by
  rw [affineBaseDerivedSectionsPushforwardComp,
    show affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w =
      conjugateIsoEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g).hom).comp
            (affineBaseDerivedSectionsAdjunction B S hS f'))
        (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w) from rfl,
    affineBaseDerivedSectionsBaseChangeMap]
  exact homEquiv_symm_map_comp_conjugateIsoEquiv_hom_app
    (affineBaseDerivedSectionsAdjunction B S hS f)
    (affineBaseDerivedSectionsAdjunction B S hS f')
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom)
    (smallEtaleDerivedModuleAdjunction B S hS g')
    (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w) a z

end AlgebraicGeometry.Space
