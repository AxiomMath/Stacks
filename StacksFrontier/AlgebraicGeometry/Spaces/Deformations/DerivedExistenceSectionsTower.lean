module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSndComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineBaseDerivedSectionsPushforwardIsoComp
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeTensorTranspose
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompOfEqConjugate
public import StacksFrontier.Homology.Tor.StandardModelExtensionScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposDerivedCategory

/-!
# The tower `RΓ(X, E ⊗^L Rpₙ,* Kₙ)` of Situation 0DIK is the restricted tower `(Mₙ)`

In Situation [Stacks, Tag 0DIK] the tower `Rpₙ,* Kₙ` of [Stacks, Tag 0DIL] has transitions
`Rpₙ₊₁,* Kₙ₊₁ ⟶ Rpₙ₊₁,* Riₙ,* Kₙ ≅ Rpₙ,* Kₙ`, the first map induced by the adjoint of `φₙ` and the
second the composition isomorphism of derived direct images, conjugate to Stacks 0D6D. Applying
`Ψ = RΓ(X, E ⊗^L -)` over `A` and identifying `Ψ(Rpₙ,* Kₙ)` with `Mₙ = RΓ(Xₙ, Eₙ ⊗^L Kₙ)` read
over `A` (Stacks 08IN and `RΓ(X, Rpₙ,* -) = RΓ(Xₙ, -)`), the transitions become the restrictions
of the transposes of the canonical maps `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`. This is the compatibility
that lets [Stacks, Tag 0CQF] be applied to the derived limit `RΓ(X, E ⊗^L K)`.

## Main results

* `Stacks.CategoryTheory.BaseChange.homEquiv_map_comp_tensor_curried`: the transpose of a base
  change map at a tensor product, for curried bifunctors.
* `Stacks.CategoryTheory.TowerStep.tensorSections_comp`: the tower step over two stacked squares,
  for abstract functors, given the pasting of the identifications (`hC1`), the projection formula
  along the composite (`hC2`), its naturality (`hn`, as natural transformations) and the
  transpose of the second square (`hST`).
* `Stacks.CategoryTheory.TowerStep.tensorSections_comp_natTrans`: the same as an equation of
  natural transformations in `E`.
* `AlgebraicGeometry.Space.tensorSections_towerStep_natTrans`: its instance for algebraic spaces
  over affine bases, on the topos spelling.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsBaseChangeMap_tensor_homEquiv`: the transpose
  of the base change map of `RΓ` at a tensor product, for algebraic spaces over affine bases.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardIso_hom_eq_conjugateEquiv`.
* `AlgebraicGeometry.Space.smallEtaleToposPushforward` and
  `AlgebraicGeometry.Space.affineBaseToposSections`: `Rf_*` and `RΓ(X, -)` typed on
  `smallEtaleToposDerivedCategory`.

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lh : B ⥤ B'} {Rh : B' ⥤ B}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
  (e : Lg ⋙ Lf' ≅ Lf ⋙ Lh)
  (F : B ⥤ B ⥤ B) (F' : B' ⥤ B' ⥤ B')
  (μ : Functor.uncurry.obj F ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj F')

/-- **`homEquiv_map_comp_tensor` for curried bifunctors, with a map in the first factor as
well**: for `c : Lh E ⟶ E'` and `τ : Lh K ⟶ Kₙ`, the transpose of the base change map at `E ⊗ K`
followed by `Rf'` of `μ`, `c ⊗ Lh K` and `E' ⊗ τ` is `Rf` of `E ⊗ u` (`u` the transpose of `τ`),
of the projection formula map and of `Rh (c ⊗ Kₙ)`, followed by the conjugate comparison at
`E' ⊗ Kₙ`. -/
theorem homEquiv_map_comp_tensor_curried (E K : B) {E' : B'} (c : Lh.obj E ⟶ E') (Kₙ : B')
    (τ : Lh.obj K ⟶ Kₙ) :
    ag.homEquiv _ _ (map adjf adjf' e (Iso.refl _) ((F.obj E).obj K) ≫
        Rf'.map (μ.app (E, K) ≫ (F'.map c).app (Lh.obj K) ≫ (F'.obj E').map τ)) =
      Rf.map ((F.obj E).map (ah.homEquiv _ _ τ) ≫
          ProjectionFormula.adjunctionTensorMapSnd ah (Functor.uncurry.obj F)
            (Functor.uncurry.obj F') μ E Kₙ ≫ Rh.map ((F'.map c).app Kₙ)) ≫
        (conjugateEquiv (adjf.comp ah) (ag.comp adjf') e.hom).app ((F'.obj E').obj Kₙ) := by
  have h := homEquiv_map_comp_tensor adjf adjf' ag ah e (Functor.uncurry.obj F)
    (Functor.uncurry.obj F') μ E K Kₙ τ
  simp only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [← (F'.map c).naturality τ, ← Category.assoc (μ.app (E, K)), Functor.map_comp,
    ← Category.assoc, Adjunction.homEquiv_naturality_right]
  refine (congrArg (· ≫ _) h).trans ?_
  have hn := (conjugateEquiv (adjf.comp ah) (ag.comp adjf') e.hom).naturality ((F'.map c).app Kₙ)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc]

end Stacks.CategoryTheory.BaseChange

namespace Stacks.CategoryTheory.TowerStep

open Functor

universe w₁ w₂ w₃ w₄ w₅ w₆ t₁ t₂ t₃ t₄ t₅ t₆

variable {𝒳 : Type t₁} {𝒳' : Type t₂} {𝒳'' : Type t₃} {𝒜 : Type t₄} {𝒜' : Type t₅}
  {𝒜'' : Type t₆} [Category.{w₁} 𝒳] [Category.{w₂} 𝒳'] [Category.{w₃} 𝒳''] [Category.{w₄} 𝒜]
  [Category.{w₅} 𝒜'] [Category.{w₆} 𝒜'']
  {Γ : 𝒳 ⥤ 𝒜} {Γ' : 𝒳' ⥤ 𝒜'} {Γ'' : 𝒳'' ⥤ 𝒜''}
  {P' : 𝒳' ⥤ 𝒳} {P₂ : 𝒳'' ⥤ 𝒳'} {P₃ : 𝒳'' ⥤ 𝒳}
  {Lp' : 𝒳 ⥤ 𝒳'} {Lp₂ : 𝒳' ⥤ 𝒳''} {Lp₃ : 𝒳 ⥤ 𝒳''}
  {r : 𝒜' ⥤ 𝒜} {r₂ : 𝒜'' ⥤ 𝒜'} {r₃ : 𝒜'' ⥤ 𝒜}
  {T : 𝒳 ⥤ 𝒳 ⥤ 𝒳} {T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳'} {T'' : 𝒳'' ⥤ 𝒳'' ⥤ 𝒳''}

/-- **The tower step over two stacked squares, abstractly.** Let `Γ, Γ', Γ''` be "sections"
functors, `P', P₂, P₃` "direct images" with `conjP : P₂ ⋙ P' ⟶ P₃`, `PF1, PF2, PF3` the
identifications `RΓ(-, P -) ⟶ res RΓ(-, -)` of three squares pasting as in `hC1`, and
`pf', pf₂, pf₃` projection formula maps compatible with the composite as in `hC2`, `pf'` natural
in its pushed argument (`hn`, as natural transformations). If `t₂` is read through `PF2` as in
`hST`, then the map `Γ(E ⊗ (P' u ≫ conjP))` read through the identification of the outer square
is the one of the first square followed by `r t₂` and `ρ`. -/
theorem tensorSections_comp
    (conjP : P₂ ⋙ P' ⟶ P₃)
    (PF1 : P' ⋙ Γ ⟶ Γ' ⋙ r) (PF2 : P₂ ⋙ Γ' ⟶ Γ'' ⋙ r₂) (PF3 : P₃ ⋙ Γ ⟶ Γ'' ⋙ r₃)
    (ρ : r₂ ⋙ r ⟶ r₃)
    (hC1 : whiskerRight conjP Γ ≫ PF3 =
      whiskerLeft P₂ PF1 ≫ whiskerRight PF2 r ≫ whiskerLeft Γ'' ρ)
    (pf' : ∀ W : 𝒳', T.flip.obj (P'.obj W) ⟶ Lp' ⋙ T'.flip.obj W ⋙ P')
    (pf₂ : ∀ W : 𝒳'', T'.flip.obj (P₂.obj W) ⟶ Lp₂ ⋙ T''.flip.obj W ⋙ P₂)
    (pf₃ : ∀ W : 𝒳'', T.flip.obj (P₃.obj W) ⟶ Lp₃ ⋙ T''.flip.obj W ⋙ P₃)
    (γ : Lp' ⋙ Lp₂ ⟶ Lp₃) (K' : 𝒳') (K'' : 𝒳'')
    (hC2 : T.flip.map (conjP.app K'') ≫ pf₃ K'' =
      pf' (P₂.obj K'') ≫
        whiskerRight (whiskerLeft Lp' (pf₂ K'') ≫ whiskerRight γ (T''.flip.obj K'' ⋙ P₂)) P' ≫
        whiskerLeft (Lp₃ ⋙ T''.flip.obj K'') conjP)
    (E : 𝒳) (u : K' ⟶ P₂.obj K'')
    (hn : T.flip.map (P'.map u) ≫ pf' (P₂.obj K'') =
      pf' K' ≫ whiskerLeft Lp' (whiskerRight (T'.flip.map u) P'))
    (t₂ : Γ'.obj ((T'.obj (Lp'.obj E)).obj K') ⟶ r₂.obj (Γ''.obj ((T''.obj (Lp₃.obj E)).obj K'')))
    (hST : t₂ = Γ'.map ((T'.obj (Lp'.obj E)).map u ≫ (pf₂ K'').app (Lp'.obj E) ≫
        P₂.map ((T''.map (γ.app E)).app K'')) ≫ PF2.app ((T''.obj (Lp₃.obj E)).obj K'')) :
    Γ.map ((T.obj E).map (P'.map u ≫ conjP.app K'')) ≫ Γ.map ((pf₃ K'').app E) ≫
        PF3.app ((T''.obj (Lp₃.obj E)).obj K'') =
      (Γ.map ((pf' K').app E) ≫ PF1.app ((T'.obj (Lp'.obj E)).obj K')) ≫ r.map t₂ ≫
        ρ.app (Γ''.obj ((T''.obj (Lp₃.obj E)).obj K'')) := by
  have h1 := NatTrans.congr_app hC1 ((T''.obj (Lp₃.obj E)).obj K'')
  have h2 := NatTrans.congr_app hC2 E
  have hn := NatTrans.congr_app hn E
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.comp_obj,
    Functor.flip_map_app, Functor.flip_obj_obj, Functor.comp_map, Functor.flip_obj_map,
    Functor.map_comp, Category.assoc] at h1 h2 hn
  subst hST
  have hN := fun {a b : 𝒳'} (x : a ⟶ b) => PF1.naturality x
  simp only [Functor.comp_map] at hN
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc Γ ((T.obj E).map (conjP.app K'')), h2]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc Γ ((T.obj E).map (P'.map u)), hn, h1]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hN]

/-- **`tensorSections_comp` as an equation of natural transformations in `E`.** The second
square's contribution is the natural composite `Γ'(- ⊗ u) ≫ Γ'(pf₂) ≫ Γ'(P₂(γ ⊗ K'')) ≫ PF2`. -/
theorem tensorSections_comp_natTrans
    (conjP : P₂ ⋙ P' ⟶ P₃)
    (PF1 : P' ⋙ Γ ⟶ Γ' ⋙ r) (PF2 : P₂ ⋙ Γ' ⟶ Γ'' ⋙ r₂) (PF3 : P₃ ⋙ Γ ⟶ Γ'' ⋙ r₃)
    (ρ : r₂ ⋙ r ⟶ r₃)
    (hC1 : whiskerRight conjP Γ ≫ PF3 =
      whiskerLeft P₂ PF1 ≫ whiskerRight PF2 r ≫ whiskerLeft Γ'' ρ)
    (pf' : ∀ W : 𝒳', T.flip.obj (P'.obj W) ⟶ Lp' ⋙ T'.flip.obj W ⋙ P')
    (pf₂ : ∀ W : 𝒳'', T'.flip.obj (P₂.obj W) ⟶ Lp₂ ⋙ T''.flip.obj W ⋙ P₂)
    (pf₃ : ∀ W : 𝒳'', T.flip.obj (P₃.obj W) ⟶ Lp₃ ⋙ T''.flip.obj W ⋙ P₃)
    (γ : Lp' ⋙ Lp₂ ⟶ Lp₃) (K' : 𝒳') (K'' : 𝒳'')
    (hC2 : T.flip.map (conjP.app K'') ≫ pf₃ K'' =
      pf' (P₂.obj K'') ≫
        whiskerRight (whiskerLeft Lp' (pf₂ K'') ≫ whiskerRight γ (T''.flip.obj K'' ⋙ P₂)) P' ≫
        whiskerLeft (Lp₃ ⋙ T''.flip.obj K'') conjP)
    (u : K' ⟶ P₂.obj K'')
    (hn : T.flip.map (P'.map u) ≫ pf' (P₂.obj K'') =
      pf' K' ≫ whiskerLeft Lp' (whiskerRight (T'.flip.map u) P')) :
    whiskerRight (T.flip.map (P'.map u ≫ conjP.app K'')) Γ ≫ whiskerRight (pf₃ K'') Γ ≫
        whiskerLeft (Lp₃ ⋙ T''.flip.obj K'') PF3 =
      whiskerRight (pf' K') Γ ≫ whiskerLeft (Lp' ⋙ T'.flip.obj K') PF1 ≫
        whiskerRight (whiskerLeft Lp' (whiskerRight (T'.flip.map u) Γ' ≫
            whiskerRight (pf₂ K'') Γ') ≫
          whiskerRight (whiskerRight γ (T''.flip.obj K'' ⋙ P₂)) Γ' ≫
          whiskerLeft (Lp₃ ⋙ T''.flip.obj K'') PF2) r ≫
        whiskerLeft (Lp₃ ⋙ T''.flip.obj K'' ⋙ Γ'') ρ := by
  ext E
  simpa using tensorSections_comp conjP PF1 PF2 PF3 ρ hC1 pf' pf₂ pf₃ γ K' K'' hC2 E u hn _ rfl

end Stacks.CategoryTheory.TowerStep

namespace Stacks.CategoryTheory.Adjunction

/-- The right adjoint of an adjunction `L ⊣ R`, read off the adjunction: `R` itself, spelled with
the categories and instances of the adjunction's type. -/
abbrev rightFunctor {C : Type*} {D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (_ : L ⊣ R) : D ⥤ C :=
  R

end Stacks.CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

section ToposSpelling

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Rf_*` on the topos spelling** `smallEtaleToposDerivedCategory`: the right adjoint of
`smallEtaleDerivedModuleAdjunction f`, with that adjunction's categories and instances. -/
abbrev smallEtaleToposPushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleToposDerivedCategory X ⥤ smallEtaleToposDerivedCategory Y :=
  Stacks.CategoryTheory.Adjunction.rightFunctor (smallEtaleDerivedModuleAdjunction B S hS f)

/-- **`RΓ(X, -)` over an affine base on the topos spelling** `smallEtaleToposDerivedCategory X`:
the derived direct image to `Spec A` followed by the derived sections of `Spec A`. -/
abbrev affineBaseToposSections {U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) :
    smallEtaleToposDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :=
  derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U

end ToposSpelling

section SquareTranspose

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)
  {X X' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)

/-- **The transpose of the base change map of `RΓ` at a tensor product**: under
`- ⊗^L_R R' ⊣` restriction, the base change map at `E ⊗^L K` followed by `RΓ(X', -)` of
Stacks 07A4, of `c ⊗^L K` and of `E' ⊗^L τ` is `RΓ(X, -)` of `E ⊗^L u` (`u` the adjoint of `τ`), of
the projection formula map and of `Rg'_*(c ⊗^L Kₙ)`, followed by the conjugate comparison of the
square (whose isomorphism is `affineBaseDerivedSectionsPushforwardIso`). -/
theorem affineBaseDerivedSectionsBaseChangeMap_tensor_homEquiv
    (E K : smallEtaleToposDerivedCategory X) {E' : smallEtaleToposDerivedCategory X'}
    (c : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ E')
    (Kₙ : smallEtaleToposDerivedCategory X')
    (τ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ Kₙ) :
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom B S hS g).hom).homEquiv _ _
      (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
        (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
          ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
            ((smallEtaleDerivedTensor B S hS X').map c).app
              ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
            ((smallEtaleDerivedTensor B S hS X').obj E').map τ)) =
      (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U).map
          (((smallEtaleDerivedTensor B S hS X).obj E).map
              ((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _ τ) ≫
            smallEtaleProjectionFormulaMapSnd g' E Kₙ ≫
            (Stacks.Cohomology.DerivedPushforward.derivedPushforward
              (X := smallEtaleRingedTopos B S hS _)
              (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS g')).map
              (((smallEtaleDerivedTensor B S hS X').map c).app Kₙ)) ≫
        (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
            (smallEtaleDerivedModuleAdjunction B S hS g'))
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
            (representedAffineCommRingCatHom B S hS g).hom).comp
            (affineBaseDerivedSectionsAdjunction B S hS f'))
          (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom).app
          (((smallEtaleDerivedTensor B S hS X').obj E').obj Kₙ) :=
  Stacks.CategoryTheory.BaseChange.homEquiv_map_comp_tensor_curried
    (affineBaseDerivedSectionsAdjunction B S hS f) (affineBaseDerivedSectionsAdjunction B S hS f')
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom)
    (smallEtaleDerivedModuleAdjunction B S hS g')
    (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w)
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedPullbackTensorIso g').hom E K c Kₙ τ

end SquareTranspose

section TowerStepSquares

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)

/-- `affineBaseDerivedSectionsPushforwardIso` is, by definition, the conjugate of the square. -/
theorem affineBaseDerivedSectionsPushforwardIso_hom_eq_conjugateEquiv :
    (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w).hom =
      conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f'))
        (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom :=
  rfl

open Functor in
/-- **The tower step over two stacked squares, as natural transformations in `E`.** Let
`X'' → X' → X` lie over `Spec A'' → Spec A' → Spec A` through cartesian squares, with composite
`g₃' = g₂' ≫ g'` over `g₃ = g₂ ≫ g`. For `φ : Lg₂'^* K' ⟶ K''`, the natural map
`RΓ(X, - ⊗ Rg'_* K') ⟶ RΓ(X, - ⊗ Rg₃'_* K'')` induced by the transpose of `φ` and
`Rg'_* Rg₂'_* ⟶ Rg₃'_*`, read through the identifications
`RΓ(X, - ⊗ Rg'_* -) ⟶ RΓ(X', Lg'^*(-) ⊗ -)` (projection formula, then the conjugate of the
square), is the identification of the first square followed by the restriction of the second
square's identification of `RΓ(X', - ⊗ φ)` and the composition of restrictions of scalars.
Stated on the topos spelling, as the instance of
`Stacks.CategoryTheory.TowerStep.tensorSections_comp_natTrans`. -/
theorem tensorSections_towerStep_natTrans (g₃ : U'' ⟶ U) (hg : g₂ ≫ g = g₃)
    (g₃' : X'' ⟶ X) (hg' : g₂' ≫ g' = g₃') (w₃ : g₃' ≫ f = f'' ≫ representedSpaceMap B S hS g₃)
    (hc : (representedAffineCommRingCatHom B S hS g₃).hom =
      (representedAffineCommRingCatHom B S hS g₂).hom.comp
        (representedAffineCommRingCatHom B S hS g).hom)
    (K' : smallEtaleToposDerivedCategory X') (K'' : smallEtaleToposDerivedCategory X'')
    (φ : (smallEtaleDerivedModulePullback B S hS g₂').obj K' ⟶ K'') :
    whiskerRight ((smallEtaleDerivedTensor B S hS X).flip.map
          ((smallEtaleToposPushforward B S hS g').map
              ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ) ≫
            (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g').comp
                (smallEtaleDerivedModuleAdjunction B S hS g₂'))
              (smallEtaleDerivedModuleAdjunction B S hS g₃')
              (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
                smallEtaleDerivedModulePullbackCongr B S hS hg').inv).app K''))
        (affineBaseToposSections B S hS f) ≫
        whiskerRight (smallEtaleProjectionFormulaSndNatTrans g₃' K'')
          (affineBaseToposSections B S hS f) ≫
        whiskerLeft ((smallEtaleDerivedModulePullback B S hS g₃') ⋙
            (smallEtaleDerivedTensor B S hS X'').flip.obj K'')
          (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
              (smallEtaleDerivedModuleAdjunction B S hS g₃'))
            ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
              (representedAffineCommRingCatHom B S hS g₃).hom).comp
              (affineBaseDerivedSectionsAdjunction B S hS f''))
            (affineBaseDerivedSectionsSquareIso B S hS g₃ f f'' g₃' w₃).hom) =
      whiskerRight (smallEtaleProjectionFormulaSndNatTrans g' K')
          (affineBaseToposSections B S hS f) ≫
        whiskerLeft ((smallEtaleDerivedModulePullback B S hS g') ⋙
            (smallEtaleDerivedTensor B S hS X').flip.obj K')
          (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
              (smallEtaleDerivedModuleAdjunction B S hS g'))
            ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
              (representedAffineCommRingCatHom B S hS g).hom).comp
              (affineBaseDerivedSectionsAdjunction B S hS f'))
            (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w).hom) ≫
        whiskerRight
          (whiskerLeft (smallEtaleDerivedModulePullback B S hS g')
              (whiskerRight ((smallEtaleDerivedTensor B S hS X').flip.map
                  ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ))
                (affineBaseToposSections B S hS f') ≫
                whiskerRight (smallEtaleProjectionFormulaSndNatTrans g₂' K'')
                  (affineBaseToposSections B S hS f')) ≫
            whiskerRight (whiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
                smallEtaleDerivedModulePullbackCongr B S hS hg').hom
                ((smallEtaleDerivedTensor B S hS X'').flip.obj K'' ⋙
                  (smallEtaleToposPushforward B S hS g₂')))
              (affineBaseToposSections B S hS f') ≫
            whiskerLeft ((smallEtaleDerivedModulePullback B S hS g₃') ⋙
                (smallEtaleDerivedTensor B S hS X'').flip.obj K'')
              (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f').comp
                  (smallEtaleDerivedModuleAdjunction B S hS g₂'))
                ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
                  (representedAffineCommRingCatHom B S hS g₂).hom).comp
                  (affineBaseDerivedSectionsAdjunction B S hS f''))
                (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂).hom))
          (ModuleCat.restrictScalars
            (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory ≫
        whiskerLeft ((smallEtaleDerivedModulePullback B S hS g₃') ⋙
            (smallEtaleDerivedTensor B S hS X'').flip.obj K'' ⋙
              (affineBaseToposSections B S hS f''))
          (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
            (representedAffineCommRingCatHom B S hS g).hom
            (representedAffineCommRingCatHom B S hS g₂).hom
            (representedAffineCommRingCatHom B S hS g₃).hom hc).hom := by
  have h1 := affineBaseDerivedSectionsPushforwardIso_hom_comp_of_eq B S hS g g₂ f f' f'' g' g₂' w w₂
    g₃ hg g₃' hg' w₃ hc
  simp only [affineBaseDerivedSectionsPushforwardIso_hom_eq_conjugateEquiv] at h1
  exact Stacks.CategoryTheory.TowerStep.tensorSections_comp_natTrans
    (𝒳 := smallEtaleToposDerivedCategory X) (𝒳' := smallEtaleToposDerivedCategory X')
    (𝒳'' := smallEtaleToposDerivedCategory X'')
    (Γ := (affineBaseToposSections B S hS f)) (Γ' := (affineBaseToposSections B S hS f'))
    (Γ'' := (affineBaseToposSections B S hS f''))
    (P' := (smallEtaleToposPushforward B S hS g')) (P₂ := (smallEtaleToposPushforward B S hS g₂'))
    (P₃ := (smallEtaleToposPushforward B S hS g₃'))
    (Lp' := (smallEtaleDerivedModulePullback B S hS g'))
    (Lp₂ := (smallEtaleDerivedModulePullback B S hS g₂'))
    (Lp₃ := (smallEtaleDerivedModulePullback B S hS g₃'))
    (r := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory)
    (r₂ := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₂).hom).mapDerivedCategory)
    (r₃ := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₃).hom).mapDerivedCategory)
    (T := (smallEtaleDerivedTensor B S hS X)) (T' := (smallEtaleDerivedTensor B S hS X'))
    (T'' := (smallEtaleDerivedTensor B S hS X''))
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
    (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f').comp
          (smallEtaleDerivedModuleAdjunction B S hS g₂'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g₂).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f''))
        (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂).hom)
    (conjugateEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
          (smallEtaleDerivedModuleAdjunction B S hS g₃'))
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
          (representedAffineCommRingCatHom B S hS g₃).hom).comp
          (affineBaseDerivedSectionsAdjunction B S hS f''))
        (affineBaseDerivedSectionsSquareIso B S hS g₃ f f'' g₃' w₃).hom)
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS g₃).hom hc).hom h1
    (fun W => smallEtaleProjectionFormulaSndNatTrans g' W)
    (fun W => smallEtaleProjectionFormulaSndNatTrans g₂' W)
    (fun W => smallEtaleProjectionFormulaSndNatTrans g₃' W)
    (smallEtaleDerivedModulePullbackCompIso B S hS g₂' g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hg').hom K' K''
    (smallEtaleProjectionFormulaSndNatTrans_comp_of_eq g₂' g' g₃' hg' K'')
    ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ)
    (smallEtaleProjectionFormulaSndNatTrans_naturality g'
      ((smallEtaleDerivedModuleAdjunction B S hS g₂').homEquiv K' K'' φ))

end TowerStepSquares

end AlgebraicGeometry.Space

end
