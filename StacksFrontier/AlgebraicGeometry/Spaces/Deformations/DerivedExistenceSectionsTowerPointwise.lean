module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsTowerStep

/-!
# The tower step of Situation 0DIK for `RΓ(X, E ⊗^L -)`, at one object `E`

The tower step of `DerivedExistenceSectionsTower` at a fixed `E`: the transition of the tower
`RΓ(X, E ⊗^L Rpₙ,* Kₙ)`, read through the identifications `RΓ(X, E ⊗^L Rpₙ,* Kₙ) ⟶ res Mₙ`
(projection formula, then Stacks 08IN's conjugate), is the restriction of the transpose of the
canonical map `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`, with `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)`.

## Implementation notes

The maps are applications of generic definitions over arbitrary categories
(`Stacks.CategoryTheory.TowerStep.sectionsHom`, `…towerSectionsHom`, `…baseChangeTensor`,
`…baseChangeTensorTranspose`), and the statement over variable spaces is the instance of a generic
lemma (`towerSectionsHom_comp_baseChangeTensorTranspose`). When the kernel compares a projection
(`NatTrans.app`, `Functor.obj`, …) applied to two terms that are equal only after unfolding, it
unfolds the projection instead of comparing argument by argument; a body written once over
variable categories and instantiated keeps every such projection inside a regular definition
whose arguments are compared directly. The equation of natural transformations
`tensorSections_towerStep_natTrans` cannot be specialised to the fibre products `Xₙ₊₁` and `Xₙ`
for the same reason (functor composites associated differently on the two sides of a
composition).

## Main results

* `Stacks.CategoryTheory.TowerStep.towerSectionsHom_comp_baseChangeTensorTranspose`: the tower
  step over two stacked squares at one object, with the second square read through the transpose
  of its base change map.
* `AlgebraicGeometry.Space.tensorSections_towerStep_app`: its instance for algebraic spaces over
  affine bases.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.tensorSections_towerStep`: its instance in
  Situation 0DIK.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.towerMap_eq_smallEtaleToposPushforward`:
  `towerMap_eq` with its middle factor in the vocabulary of `smallEtaleDerivedModuleAdjunction`.

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace Stacks.CategoryTheory.TowerStep

universe w₁ w₂ w₃ w₄ w₅ w₆ t₁ t₂ t₃ t₄ t₅ t₆

section Defs

variable {𝒳 : Type t₁} {𝒳' : Type t₂} {𝒳'' : Type t₃} {𝒜 : Type t₄} {𝒜' : Type t₅}
  {𝒜'' : Type t₆} [Category.{w₁} 𝒳] [Category.{w₂} 𝒳'] [Category.{w₃} 𝒳''] [Category.{w₄} 𝒜]
  [Category.{w₅} 𝒜'] [Category.{w₆} 𝒜'']

/-- **The identification of one square at `E`**: `Γ(E ⊗ P' K') ⟶ r Γ'(Lp' E ⊗ K')`, the
projection formula map `pf` followed by the comparison `PF : P' ⋙ Γ ⟶ Γ' ⋙ r`. -/
def sectionsHom (Γ : 𝒳 ⥤ 𝒜) (Γ' : 𝒳' ⥤ 𝒜') (r : 𝒜' ⥤ 𝒜) (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳)
    (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (Lp' : 𝒳 ⥤ 𝒳') (P' : 𝒳' ⥤ 𝒳) (K' : 𝒳')
    (pf : T.flip.obj (P'.obj K') ⟶ Lp' ⋙ T'.flip.obj K' ⋙ P') (PF : P' ⋙ Γ ⟶ Γ' ⋙ r)
    (E : 𝒳) :
    Γ.obj ((T.obj E).obj (P'.obj K')) ⟶ r.obj (Γ'.obj ((T'.obj (Lp'.obj E)).obj K')) :=
  Γ.map (pf.app E) ≫ PF.app ((T'.obj (Lp'.obj E)).obj K')

/-- **`sectionsHom` after an identification `β : P' ≅ P'₀`.** -/
def towerSectionsHom (Γ : 𝒳 ⥤ 𝒜) (Γ' : 𝒳' ⥤ 𝒜') (r : 𝒜' ⥤ 𝒜) (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳)
    (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (Lp' : 𝒳 ⥤ 𝒳') (P' : 𝒳' ⥤ 𝒳) (K' : 𝒳')
    (pf : T.flip.obj (P'.obj K') ⟶ Lp' ⋙ T'.flip.obj K' ⋙ P') (PF : P' ⋙ Γ ⟶ Γ' ⋙ r)
    {P'₀ : 𝒳' ⥤ 𝒳} (β : P' ≅ P'₀) (E : 𝒳) :
    Γ.obj ((T.obj E).obj (P'₀.obj K')) ⟶ r.obj (Γ'.obj ((T'.obj (Lp'.obj E)).obj K')) :=
  Γ.map ((T.obj E).map (β.inv.app K')) ≫ sectionsHom Γ Γ' r T T' Lp' P' K' pf PF E

variable {Lf' : 𝒜' ⥤ 𝒳'} {Γ' : 𝒳' ⥤ 𝒜'} {Lf'' : 𝒜'' ⥤ 𝒳''} {Γ'' : 𝒳'' ⥤ 𝒜''}
  {Lg : 𝒜' ⥤ 𝒜''} {Lh : 𝒳' ⥤ 𝒳''}

/-- **The base change map at a tensor product**, `Lg Γ'(E' ⊗ K') ⟶ Γ''(E'' ⊗ K'')`: the base
change map of the square `e` followed by `Γ''` of `μ`, `c ⊗ Lh K'` and `E'' ⊗ φ`. -/
def baseChangeTensor (adjf' : Lf' ⊣ Γ') (adjf'' : Lf'' ⊣ Γ'') (e : Lg ⋙ Lf'' ≅ Lf' ⋙ Lh)
    (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (T'' : 𝒳'' ⥤ 𝒳'' ⥤ 𝒳'')
    (μ : Functor.uncurry.obj T' ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T'')
    {Lp' : 𝒳 ⥤ 𝒳'} {Lp₃ : 𝒳 ⥤ 𝒳''} (γ : Lp' ⋙ Lh ⟶ Lp₃) (E : 𝒳) {K' : 𝒳'} {K'' : 𝒳''}
    (φ : Lh.obj K' ⟶ K'') :
    Lg.obj (Γ'.obj ((T'.obj (Lp'.obj E)).obj K')) ⟶ Γ''.obj ((T''.obj (Lp₃.obj E)).obj K'') :=
  BaseChange.map adjf' adjf'' e (Iso.refl _) ((T'.obj (Lp'.obj E)).obj K') ≫
    Γ''.map (μ.app (Lp'.obj E, K') ≫ (T''.map (γ.app E)).app (Lh.obj K') ≫
      (T''.obj (Lp₃.obj E)).map φ)

/-- **The transpose of `baseChangeTensor`** under `Lg ⊣ r`. -/
def baseChangeTensorTranspose {r : 𝒜'' ⥤ 𝒜'} (adjf' : Lf' ⊣ Γ') (adjf'' : Lf'' ⊣ Γ'')
    (ag : Lg ⊣ r) (e : Lg ⋙ Lf'' ≅ Lf' ⋙ Lh)
    (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (T'' : 𝒳'' ⥤ 𝒳'' ⥤ 𝒳'')
    (μ : Functor.uncurry.obj T' ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T'')
    {Lp' : 𝒳 ⥤ 𝒳'} {Lp₃ : 𝒳 ⥤ 𝒳''} (γ : Lp' ⋙ Lh ⟶ Lp₃) (E : 𝒳) {K' : 𝒳'} {K'' : 𝒳''}
    (φ : Lh.obj K' ⟶ K'') :
    Γ'.obj ((T'.obj (Lp'.obj E)).obj K') ⟶ r.obj (Γ''.obj ((T''.obj (Lp₃.obj E)).obj K'')) :=
  ag.homEquiv _ _ (baseChangeTensor adjf' adjf'' e T' T'' μ γ E φ)

end Defs

variable {𝒳 : Type t₁} {𝒳' : Type t₂} {𝒳'' : Type t₃} {𝒜 : Type t₄} {𝒜' : Type t₅}
  {𝒜'' : Type t₆} [Category.{w₁} 𝒳] [Category.{w₂} 𝒳'] [Category.{w₃} 𝒳''] [Category.{w₄} 𝒜]
  [Category.{w₅} 𝒜'] [Category.{w₆} 𝒜'']
  {Γ : 𝒳 ⥤ 𝒜} {Γ' : 𝒳' ⥤ 𝒜'} {Γ'' : 𝒳'' ⥤ 𝒜''}
  {P' : 𝒳' ⥤ 𝒳} {P₂ : 𝒳'' ⥤ 𝒳'} {P₃ : 𝒳'' ⥤ 𝒳}
  {Lp' : 𝒳 ⥤ 𝒳'} {Lp₂ : 𝒳' ⥤ 𝒳''} {Lp₃ : 𝒳 ⥤ 𝒳''}
  {r : 𝒜' ⥤ 𝒜} {r₂ : 𝒜'' ⥤ 𝒜'} {r₃ : 𝒜'' ⥤ 𝒜}
  {T : 𝒳 ⥤ 𝒳 ⥤ 𝒳} {T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳'} {T'' : 𝒳'' ⥤ 𝒳'' ⥤ 𝒳''}
  {Lf' : 𝒜' ⥤ 𝒳'} {Lf'' : 𝒜'' ⥤ 𝒳''} {Lg₂ : 𝒜' ⥤ 𝒜''}

/-- **The tower step over two stacked squares at one object, with the second square's
contribution the transpose of its base change map.** This is `tensorSections_comp` with
`PF2` the conjugate of the square `e₂`, `pf₂` the projection formula map of `ah₂` and `μ₂`
(`hpf₂`), and `t₂` read through `BaseChange.homEquiv_map_comp_tensor_curried`, and with the
identifications of the first and of the outer square read through isomorphisms `β' : P' ≅ P'₀`,
`β'' : P₃ ≅ P''₀`. -/
theorem towerSectionsHom_comp_baseChangeTensorTranspose
    (conjP : P₂ ⋙ P' ⟶ P₃)
    (PF1 : P' ⋙ Γ ⟶ Γ' ⋙ r) (PF3 : P₃ ⋙ Γ ⟶ Γ'' ⋙ r₃) (ρ : r₂ ⋙ r ⟶ r₃)
    (adjf' : Lf' ⊣ Γ') (adjf'' : Lf'' ⊣ Γ'') (ag₂ : Lg₂ ⊣ r₂) (ah₂ : Lp₂ ⊣ P₂)
    (e₂ : Lg₂ ⋙ Lf'' ≅ Lf' ⋙ Lp₂)
    (hC1 : whiskerRight conjP Γ ≫ PF3 =
      whiskerLeft P₂ PF1 ≫
        whiskerRight (conjugateEquiv (adjf'.comp ah₂) (ag₂.comp adjf'') e₂.hom) r ≫
        whiskerLeft Γ'' ρ)
    (pf' : ∀ W : 𝒳', T.flip.obj (P'.obj W) ⟶ Lp' ⋙ T'.flip.obj W ⋙ P')
    (pf₂ : ∀ W : 𝒳'', T'.flip.obj (P₂.obj W) ⟶ Lp₂ ⋙ T''.flip.obj W ⋙ P₂)
    (pf₃ : ∀ W : 𝒳'', T.flip.obj (P₃.obj W) ⟶ Lp₃ ⋙ T''.flip.obj W ⋙ P₃)
    (γ : Lp' ⋙ Lp₂ ⟶ Lp₃) (K' : 𝒳') (K'' : 𝒳'')
    (hC2 : T.flip.map (conjP.app K'') ≫ pf₃ K'' =
      pf' (P₂.obj K'') ≫
        whiskerRight (whiskerLeft Lp' (pf₂ K'') ≫ whiskerRight γ (T''.flip.obj K'' ⋙ P₂)) P' ≫
        whiskerLeft (Lp₃ ⋙ T''.flip.obj K'') conjP)
    (φ : Lp₂.obj K' ⟶ K'')
    (hn : T.flip.map (P'.map (ah₂.homEquiv _ _ φ)) ≫ pf' (P₂.obj K'') =
      pf' K' ≫ whiskerLeft Lp' (whiskerRight (T'.flip.map (ah₂.homEquiv _ _ φ)) P'))
    (μ₂ : Functor.uncurry.obj T' ⋙ Lp₂ ⟶ Lp₂.prod Lp₂ ⋙ Functor.uncurry.obj T'')
    (E : 𝒳)
    (hpf₂ : (pf₂ K'').app (Lp'.obj E) = ProjectionFormula.adjunctionTensorMapSnd ah₂
      (Functor.uncurry.obj T') (Functor.uncurry.obj T'') μ₂ (Lp'.obj E) K'')
    {P'₀ : 𝒳' ⥤ 𝒳} {P''₀ : 𝒳'' ⥤ 𝒳} (β' : P' ≅ P'₀) (β'' : P₃ ≅ P''₀)
    (s : P'₀.obj K' ⟶ P''₀.obj K'')
    (hs : s = β'.inv.app K' ≫ (P'.map (ah₂.homEquiv _ _ φ) ≫ conjP.app K'') ≫ β''.hom.app K'') :
    Γ.map ((T.obj E).map s) ≫ towerSectionsHom Γ Γ'' r₃ T T'' Lp₃ P₃ K'' (pf₃ K'') PF3 β'' E =
      towerSectionsHom Γ Γ' r T T' Lp' P' K' (pf' K') PF1 β' E ≫
        (r.map (baseChangeTensorTranspose adjf' adjf'' ag₂ e₂ T' T'' μ₂ γ E φ) ≫
          ρ.app (Γ''.obj ((T''.obj (Lp₃.obj E)).obj K''))) := by
  have hT := BaseChange.homEquiv_map_comp_tensor_curried adjf' adjf'' ag₂ ah₂ e₂ T' T'' μ₂
    (Lp'.obj E) K' (γ.app E) K'' φ
  rw [← hpf₂] at hT
  have h := tensorSections_comp conjP PF1
    (conjugateEquiv (adjf'.comp ah₂) (ag₂.comp adjf'') e₂.hom) PF3 ρ hC1 pf' pf₂ pf₃ γ K' K''
    hC2 E (ah₂.homEquiv _ _ φ) hn _ hT
  subst hs
  simp only [towerSectionsHom, sectionsHom, baseChangeTensorTranspose, baseChangeTensor]
  rw [← Category.assoc (Γ.map _), ← Γ.map_comp, ← (T.obj E).map_comp, Category.assoc,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [h]

end Stacks.CategoryTheory.TowerStep

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

section OneSquare

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)
  {X X' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)

/-- **`RΓ(X, E ⊗^L Rg'_* K') ⟶ res RΓ(X', Lg'^*E ⊗^L K')` after an identification
`β : Rg'_* ≅ P`**, for a cartesian square over affine bases: `RΓ(X, -)` of `β⁻¹` and of the
projection formula map, then the conjugate of the square
(`affineBaseDerivedSectionsPushforwardIso`, Stacks 08IN). -/
def tensorTowerSectionsHom
    (P : smallEtaleToposDerivedCategory X' ⥤ smallEtaleToposDerivedCategory X)
    (β : smallEtaleToposPushforward B S hS g' ≅ P) (E : smallEtaleToposDerivedCategory X)
    (K' : smallEtaleToposDerivedCategory X') :
    (affineBaseToposSections B S hS f).obj (((smallEtaleDerivedTensor B S hS X).obj E).obj
        (P.obj K')) ⟶
      (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj
        ((affineBaseToposSections B S hS f').obj (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')) :=
  Stacks.CategoryTheory.TowerStep.towerSectionsHom (affineBaseToposSections B S hS f)
    (affineBaseToposSections B S hS f')
    (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedModulePullback B S hS g') (smallEtaleToposPushforward B S hS g') K'
    (smallEtaleProjectionFormulaSndNatTrans g' K')
    (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f'))
        (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom) β E

end OneSquare

section TwoSquares

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
  (g₃ : U'' ⟶ U) (hg : g₂ ≫ g = g₃)
  (g₃' : X'' ⟶ X) (hg' : g₂' ≫ g' = g₃') (w₃ : g₃' ≫ f = f'' ≫ representedSpaceMap B S hS g₃)
  (hc : (representedAffineCommRingCatHom B S hS g₃).hom =
    (representedAffineCommRingCatHom B S hS g₂).hom.comp
      (representedAffineCommRingCatHom B S hS g).hom)
  (K' : smallEtaleToposDerivedCategory X') (K'' : smallEtaleToposDerivedCategory X'')
  (φ : (smallEtaleDerivedModulePullback B S hS g₂').obj K' ⟶ K'')
  (E : smallEtaleToposDerivedCategory X)

/-- **The canonical map of the second square**,
`RΓ(X', Lg'^*E ⊗^L K') ⊗^L_{A'} A'' ⟶ RΓ(X'', Lg₃'^*E ⊗^L K'')`: the base change map of `RΓ`, then
`RΓ(X'', -)` of Stacks 07A4, of `Lg₂'^* Lg'^* ≅ Lg₃'^*` and of `φ`. -/
def transitionTensorSectionsBaseChange :
    (representedAffineDerivedExtension B S hS g₂).functor.obj
        ((affineBaseToposSections B S hS f').obj (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')) ⟶
      (affineBaseToposSections B S hS f'').obj (((smallEtaleDerivedTensor B S hS X'').obj
          ((smallEtaleDerivedModulePullback B S hS g₃').obj E)).obj K'') :=
  Stacks.CategoryTheory.TowerStep.baseChangeTensor (affineBaseDerivedSectionsAdjunction B S hS f')
    (affineBaseDerivedSectionsAdjunction B S hS f'')
    (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedTensor B S hS X'')
    (smallEtaleDerivedPullbackTensorIso g₂').hom
    (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hg').hom E φ

/-- **The transpose of `transitionTensorSectionsBaseChange`**,
`RΓ(X', Lg'^*E ⊗^L K') ⟶ res RΓ(X'', Lg₃'^*E ⊗^L K'')`, under `- ⊗^L_{A'} A'' ⊣` restriction. -/
def transitionTensorSectionsTranspose :
    (affineBaseToposSections B S hS f').obj (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K') ⟶
      (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g₂).hom).mapDerivedCategory.obj
        ((affineBaseToposSections B S hS f'').obj (((smallEtaleDerivedTensor B S hS X'').obj
          ((smallEtaleDerivedModulePullback B S hS g₃').obj E)).obj K'')) :=
  Stacks.CategoryTheory.TowerStep.baseChangeTensorTranspose
    (affineBaseDerivedSectionsAdjunction B S hS f') (affineBaseDerivedSectionsAdjunction B S hS f'')
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₂).hom)
    (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedTensor B S hS X'')
    (smallEtaleDerivedPullbackTensorIso g₂').hom
    (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hg').hom E φ

include hg in
/-- **The tower step over two stacked squares, at one object `E`.** Let `X'' → X' → X` lie over
`Spec A'' → Spec A' → Spec A` through cartesian squares, with composite `g₃' = g₂' ≫ g'`, and let
`φ : Lg₂'^* K' ⟶ K''`. For isomorphisms `β' : Rg'_* ≅ P'` and `β'' : Rg₃'_* ≅ P''` and a map
`s : P' K' ⟶ P'' K''` equal to `Rg'_*` of the adjoint of `φ` followed by `Rg'_* Rg₂'_* ⟶ Rg₃'_*`,
read through `β'` and `β''`, the map `RΓ(X, E ⊗^L s)` read through the identifications
`tensorTowerSectionsHom` is the restriction of the transpose of the canonical map of the second
square, followed by the composition of restrictions of scalars. -/
theorem tensorSections_towerStep_app
    (P' : smallEtaleToposDerivedCategory X' ⥤ smallEtaleToposDerivedCategory X)
    (P'' : smallEtaleToposDerivedCategory X'' ⥤ smallEtaleToposDerivedCategory X)
    (β' : smallEtaleToposPushforward B S hS g' ≅ P')
    (β'' : smallEtaleToposPushforward B S hS g₃' ≅ P'') (s : P'.obj K' ⟶ P''.obj K'')
    (hs : s = β'.inv.app K' ≫ ((smallEtaleToposPushforward B S hS g').map
        ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ) ≫
      (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g').comp
            (smallEtaleDerivedModuleAdjunction B S hS g₂'))
          (smallEtaleDerivedModuleAdjunction B S hS g₃')
          (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hg').inv).app K'') ≫ β''.hom.app K'') :
    (affineBaseToposSections B S hS f).map (((smallEtaleDerivedTensor B S hS X).obj E).map s) ≫
        tensorTowerSectionsHom B S hS g₃ f f'' g₃' w₃ P'' β'' E K'' =
      tensorTowerSectionsHom B S hS g f f' g' w P' β' E K' ≫
        ((ModuleCat.restrictScalars
            (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.map
            (transitionTensorSectionsTranspose B S hS g₂ f' f'' g' g₂' w₂ g₃' hg' K' K'' φ E) ≫
          (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
            (representedAffineCommRingCatHom B S hS g).hom
            (representedAffineCommRingCatHom B S hS g₂).hom
            (representedAffineCommRingCatHom B S hS g₃).hom hc).hom.app
            ((affineBaseToposSections B S hS f'').obj (((smallEtaleDerivedTensor B S hS X'').obj
              ((smallEtaleDerivedModulePullback B S hS g₃').obj E)).obj K''))) := by
  have h1 := affineBaseDerivedSectionsPushforwardIso_hom_comp_of_eq B S hS g g₂ f f' f'' g' g₂' w w₂
    g₃ hg g₃' hg' w₃ hc
  simp only [affineBaseDerivedSectionsPushforwardIso_hom_eq_conjugateEquiv] at h1
  exact Stacks.CategoryTheory.TowerStep.towerSectionsHom_comp_baseChangeTensorTranspose
    (𝒳 := smallEtaleToposDerivedCategory X) (𝒳' := smallEtaleToposDerivedCategory X')
    (𝒳'' := smallEtaleToposDerivedCategory X'')
    (Γ := affineBaseToposSections B S hS f) (Γ' := affineBaseToposSections B S hS f')
    (Γ'' := affineBaseToposSections B S hS f'')
    (P' := smallEtaleToposPushforward B S hS g') (P₂ := smallEtaleToposPushforward B S hS g₂')
    (P₃ := smallEtaleToposPushforward B S hS g₃')
    (Lp' := smallEtaleDerivedModulePullback B S hS g')
    (Lp₂ := smallEtaleDerivedModulePullback B S hS g₂')
    (Lp₃ := smallEtaleDerivedModulePullback B S hS g₃')
    (r := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory)
    (r₂ := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₂).hom).mapDerivedCategory)
    (r₃ := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₃).hom).mapDerivedCategory)
    (T := smallEtaleDerivedTensor B S hS X) (T' := smallEtaleDerivedTensor B S hS X')
    (T'' := smallEtaleDerivedTensor B S hS X'')
    (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g').comp
            (smallEtaleDerivedModuleAdjunction B S hS g₂'))
          (smallEtaleDerivedModuleAdjunction B S hS g₃')
          (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hg').inv)
    (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f'))
        (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom)
    (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g₃'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g₃).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f''))
        (affineBaseDerivedSectionsSquareIso B S hS g₃ f f'' g₃' w₃).hom)
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS g₃).hom hc).hom
    (affineBaseDerivedSectionsAdjunction B S hS f') (affineBaseDerivedSectionsAdjunction B S hS f'')
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₂).hom)
    (smallEtaleDerivedModuleAdjunction B S hS g₂')
    (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂) h1
    (fun W => smallEtaleProjectionFormulaSndNatTrans g' W)
    (fun W => smallEtaleProjectionFormulaSndNatTrans g₂' W)
    (fun W => smallEtaleProjectionFormulaSndNatTrans g₃' W)
    (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hg').hom K' K''
    (smallEtaleProjectionFormulaSndNatTrans_comp_of_eq g₂' g' g₃' hg' K'') φ
    (smallEtaleProjectionFormulaSndNatTrans_naturality g'
      ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ))
    (smallEtaleDerivedPullbackTensorIso g₂').hom E rfl β' β'' s hs

end TwoSquares

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- **The transition maps of the tower of Situation 0DIK through `smallEtaleToposPushforward`**:
`towerMap_eq` with its middle factor in the vocabulary of `smallEtaleDerivedModuleAdjunction`. -/
theorem towerMap_eq_smallEtaleToposPushforward (n : ℕ) :
    D.towerMap n =
      (D.stageToposDerivedPushforwardIso (n + 1)).inv.app (D.K (n + 1)) ≫
        ((smallEtaleToposPushforward D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))).map
          ((smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
            (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).homEquiv
            (D.K (n + 1)) (D.K n) (D.φ n)) ≫
        (conjugateEquiv ((smallEtaleDerivedModuleAdjunction D.B (limitBase D.system)
            D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))).comp
            (smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
              (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)))
          (smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
          (smallEtaleDerivedModulePullbackCompIso D.B (limitBase D.system) D.containsLimitBase
              (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
            smallEtaleDerivedModulePullbackCongr D.B (limitBase D.system) D.containsLimitBase
              (transitionSpace_spaceProjection D.system D.B D.containsLimitBase
                D.containsBaseAt D.X n)).inv).app (D.K n)) ≫
        (D.stageToposDerivedPushforwardIso n).hom.app (D.K n) := by
  rw [D.towerMap_eq n, D.stageToposDerivedPushforward_map_homEquiv_eq n,
    D.conjugateEquiv_stageDerivedPullbackCompIso_inv_eq n]

/-- **`RΓ(X, E ⊗^L Rpₙ,* Kₙ) ⟶ res Mₙ`** in Situation 0DIK, with `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)`:
`tensorTowerSectionsHom` for the square `Xₙ = X ×_{Spec A} Spec Aₙ` and the identification of
the two direct images along `pₙ`. -/
abbrev towerTensorSectionsHom (E : smallEtaleToposDerivedCategory D.X.left) (n : ℕ) :=
  tensorTowerSectionsHom D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip.w
    (D.stagePushforward n) (D.stageToposDerivedPushforwardIso n) E (D.K n)

/-- **The transpose `Mₙ₊₁ ⟶ res Mₙ` of the canonical map `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`** in
Situation 0DIK. -/
abbrev stageTensorSectionsTranspose (E : smallEtaleToposDerivedCategory D.X.left) (n : ℕ) :=
  transitionTensorSectionsTranspose D.B (limitBase D.system) D.containsLimitBase
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.isPullback_transitionSpace n).w
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.K (n + 1)) (D.K n) (D.φ n) E

/-- **The tower step of Situation 0DIK at one object `E`**: the transition `RΓ(X, E ⊗^L sₙ)` of
the tower `RΓ(X, E ⊗^L Rpₙ,* Kₙ)`, read through the identifications
`RΓ(X, E ⊗^L Rpₙ,* Kₙ) ⟶ res Mₙ` (`towerTensorSectionsHom`), is the restriction of the
transpose `Mₙ₊₁ ⟶ res Mₙ` of the canonical map `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`, followed by the
composition of restrictions of scalars along `A → Aₙ₊₁ → Aₙ`. -/
theorem tensorSections_towerStep (E : smallEtaleToposDerivedCategory D.X.left) (n : ℕ) :
    (affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase D.X.hom).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
          E).map (D.towerMap n)) ≫ D.towerTensorSectionsHom E n =
      D.towerTensorSectionsHom E (n + 1) ≫
        ((ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B (limitBase D.system)
            D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
              D.containsBaseAt (n + 1))).hom).mapDerivedCategory.map
            (D.stageTensorSectionsTranspose E n) ≫
          (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
            (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
              (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))).hom
            (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
              (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
            (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
              (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
            (D.stageRingHom_comp n)).hom.app
            ((affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
              (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
              (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
                (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                ((smallEtaleDerivedModulePullback D.B (limitBase D.system)
                  D.containsLimitBase (spaceProjection D.system D.B D.containsLimitBase
                    D.containsBaseAt D.X n)).obj E)).obj (D.K n)))) :=
  tensorSections_towerStep_app D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    D.X.hom
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)).flip.w
    (D.isPullback_transitionSpace n).w
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (baseObjectTransition_baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip.w
    (D.stageRingHom_comp n) (D.K (n + 1)) (D.K n) (D.φ n) E (D.stagePushforward (n + 1))
    (D.stagePushforward n) (D.stageToposDerivedPushforwardIso (n + 1))
    (D.stageToposDerivedPushforwardIso n) (D.towerMap n)
    (D.towerMap_eq_smallEtaleToposPushforward n)

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
