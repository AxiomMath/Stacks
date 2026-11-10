module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructibleUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
public import
  StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecompositionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreModules
import StacksCore.Tactic.StacksAttribute

/-!
# Descent of constructibility and finite direct images in the model `EtaleModules`

The library proves Stacks 095Q (constructibility of a sheaf of modules descends along a surjective
morphism of quasi-compact quasi-separated schemes) and Stacks 095H (the direct image along a
finite étale morphism of a constructible sheaf of modules is constructible) on the small étale
site of Tag 021B of a big étale site, for a Noetherian ring `Λ : Type (u + 1)`. This file reads
both in the model `Stacks.EtaleCohomology.EtaleModules Λ X` of Mathlib's small étale site, in
which the derived lower shriek `Stacks.EtaleCohomology.derivedLowerShriekUnbounded` lives,
through `Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf` and
the comparisons of inverse and direct images between the two presentations of the small étale
site.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_inverseImage_of_surjective` —
  Stacks 095Q for sheaves of modules in the model `EtaleModules`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_finite_of_etale`
  — Stacks 095H for sheaves of modules in the model `EtaleModules`.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_app_of_isFinite` — Stacks 0959 for sheaves
  of modules: base change of a finite direct image.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite` —
  **Stacks 095R** for sheaves of modules: the direct image along a finite morphism of finite
  presentation of a constructible sheaf is constructible.

## Implementation notes

The coefficient ring is `Λ : Type (u + 1)`, the universe at which the library's module versions
of Stacks 095Q and 095H are stated (their proofs pass through the shriek presentations of
Stacks 095N, which are available only there). A big étale site containing the two schemes
involved is `AlgebraicGeometry.BigEtaleSite.ofSet`; by
`Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf`
constructibility may be read in it.

## References

* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 095H](https://stacks.math.columbia.edu/tag/095H)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- A morphism of schemes is the image of a morphism in a big étale site containing both. -/
private theorem exists_bigEtaleSite_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (B : BigEtaleSite.{u}) (hX : B.Contains X) (hY : B.Contains Y)
      (fb : B.obj X hX ⟶ B.obj Y hY), B.inclusion.map fb = f := by
  have hX : (BigEtaleSite.ofSet {X, Y}).Contains X := BigEtaleSite.contains_ofSet _ (by simp)
  have hY : (BigEtaleSite.ofSet {X, Y}).Contains Y := BigEtaleSite.contains_ofSet _ (by simp)
  exact ⟨_, hX, hY, (BigEtaleSite.ofSet {X, Y}).inclusion.preimage f, Functor.map_preimage _ _⟩

/-- **Stacks 095Q for sheaves of modules, in the model `EtaleModules`.** Let `f : X ⟶ Y` be a
surjective morphism of quasi-compact quasi-separated schemes, `Λ` a Noetherian ring and `ℱ` a
sheaf of `Λ`-modules on `Y_étale` whose inverse image `f⁻¹ℱ` is constructible. Then `ℱ` is
constructible.

This is `AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective` read in a big
étale site containing `X` and `Y`, through
`Stacks.EtaleCohomology.etaleModuleToBoundedSiteInverseImageIso`. The converse is Stacks 095G. -/
theorem isConstructibleEtaleModule_of_inverseImage_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (F : EtaleModules.{u, u + 1} Λ Y)
    (hF : IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, u + 1} Λ f).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  obtain ⟨B, hX, hY, fb, hfb⟩ := exists_bigEtaleSite_map_eq f
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hY]
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hX] at hF
  refine (isConstructibleModuleSheaf_pullback_iff_of_surjective B Λ fb ‹CompactSpace Y›
    ‹QuasiSeparatedSpace Y› ‹CompactSpace X› ‹QuasiSeparatedSpace X›
    (by rw [hfb]; exact f.surjective) _).2 ?_
  refine isConstructibleModuleSheaf_congr.{u, u + 1, u + 1} B Λ _
    (etaleModuleToBoundedSiteInverseImageIso.{u, u + 1} Λ B fb F).symm ?_
  rw [hfb]
  exact hF

/-- **The direct image of the model `EtaleModules` is the bounded direct image**, conjugated by
the transport to the small étale site of Tag 021B. -/
def etaleModuleToBoundedSiteDirectImageIso (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (G : EtaleModules.{u, u + 1} Λ T.obj) :
    (etaleModuleToBoundedSite.{u, u + 1} Λ B S.property).obj
        ((etaleModuleDirectImage.{u, u + 1} Λ (B.inclusion.map f)).obj G) ≅
      (B.smallPushforward f (ModuleCat.{u + 1} Λ)).obj
        ((etaleModuleToBoundedSite.{u, u + 1} Λ B T.property).obj G) :=
  (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ)).app G

/-- **Stacks 095H for sheaves of modules, in the model `EtaleModules`.** Let `p : T ⟶ S` be a
finite étale morphism of schemes, `Λ` a Noetherian ring and `ℱ` a constructible sheaf of
`Λ`-modules on `T_étale`. Then `p_*ℱ` is constructible.

This is `AlgebraicGeometry.isConstructibleModuleSheaf_pushforward` read in a big étale site
containing `S` and `T`. -/
theorem isConstructibleEtaleModule_etaleModuleDirectImage_of_finite_of_etale {S T : Scheme.{u}}
    (p : T ⟶ S) [IsFinite p] [Etale p] (F : EtaleModules.{u, u + 1} Λ T)
    (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, u + 1} Λ p).obj F) := by
  obtain ⟨B, hT, hS, pb, hpb⟩ := exists_bigEtaleSite_map_eq p
  have : IsFinite (B.inclusion.map pb) := by rw [hpb]; infer_instance
  have : Etale (B.inclusion.map pb) := by rw [hpb]; infer_instance
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hT] at hF
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hS]
  rw [← hpb]
  refine isConstructibleModuleSheaf_congr.{u, u + 1, u + 1} B Λ _
    (etaleModuleToBoundedSiteDirectImageIso Λ B pb F).symm ?_
  exact isConstructibleModuleSheaf_pushforward B pb Λ _ hF

/-! ### Finite base change for sheaves of modules -/

section FiniteBaseChange

variable (Λ : Type r) [Ring Λ]

/-- **Stacks 0959 for sheaves of `Λ`-modules.** For a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `f` finite, the base change map `g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` of sheaves of `Λ`-modules is an
isomorphism: after forgetting the module structure it is the base change map of abelian sheaves,
which is invertible
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional`), and
forgetting reflects isomorphisms. -/
theorem isIso_etaleModuleBaseChange_app_of_isFinite {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) [IsFinite f]
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app F) := by
  have h := etaleModuleBaseChange_forget.{u, r} Λ f g g' f' sq.w F
  have := isIso_etaleAbelianBaseChange_of_isFinite_unconditional.{u, r} f g g' f' sq
  have : IsIso ((etaleModuleInverseImageForget.{u, r} Λ g).app
      ((etaleModuleDirectImage.{u, r} Λ f).obj F) ≫
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map
      ((etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app F)) := by
    rw [h]
    have : IsIso ((etaleAbelianBaseChange.{u, r} f g g' f' sq.w).app
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj F)) :=
      NatIso.isIso_app_of_isIso _ _
    have : IsIso ((etaleModuleInverseImageForget.{u, r} Λ g').app F) :=
      NatIso.isIso_app_of_isIso _ _
    refine IsIso.comp_isIso' ?_ ?_
    · exact NatIso.isIso_app_of_isIso _ _
    · exact Functor.map_isIso _ _
  have : IsIso ((etaleModuleInverseImageForget.{u, r} Λ g).app
      ((etaleModuleDirectImage.{u, r} Λ f).obj F)) := NatIso.isIso_app_of_isIso _ _
  have := IsIso.of_isIso_comp_left ((etaleModuleInverseImageForget.{u, r} Λ g).app
      ((etaleModuleDirectImage.{u, r} Λ f).obj F))
    ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map
      ((etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app F))
  exact isIso_of_reflects_iso _ (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y')

/-- Restriction of a direct image along a finite morphism to an open is the direct image of the
restriction (Stacks 0959 for an open immersion). -/
def etaleModuleInverseImageDirectImageIsoOfIsFinite {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) [IsFinite f]
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleInverseImage.{u, r} Λ g).obj ((etaleModuleDirectImage.{u, r} Λ f).obj F) ≅
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleInverseImage.{u, r} Λ g').obj F) :=
  haveI := isIso_etaleModuleBaseChange_app_of_isFinite Λ f g g' f' sq F
  asIso ((etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app F)

end FiniteBaseChange

/-! ### Finite direct images -/

section FiniteDirectImage

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- Constructibility of `g⁻¹ f_* ℱ` follows from that of `f'_* g'⁻¹ ℱ` in a cartesian square with
`f` finite. -/
private theorem isConstructibleEtaleModule_inverseImage_directImage {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} [IsFinite f]
    (sq : IsPullback g' f' f g) (F : EtaleModules.{u, u + 1} Λ X)
    (h : IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, u + 1} Λ f').obj
      ((etaleModuleInverseImage.{u, u + 1} Λ g').obj F))) :
    IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, u + 1} Λ g).obj
      ((etaleModuleDirectImage.{u, u + 1} Λ f).obj F)) :=
  (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageDirectImageIsoOfIsFinite Λ f g g' f' sq F).symm h

/-- Stacks 095R over an affine base. -/
private theorem isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsAffine Y] (hfp : FinitePresentation f)
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, u + 1} Λ f).obj F) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨Y', _, g, hg, -, Z', i, hi, hfin, het⟩ :=
    exists_surjective_affine_baseChange_thickening_finiteEtale_general f hfp
  have := hi.1
  have : IsFinite (i ≫ pullback.snd f g) := hfin
  have : Etale (i ≫ pullback.snd f g) := het
  have : Surjective g := hg
  have : UniversalHomeomorphism i :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi.2
  have := isIso_etaleModuleInverseImageAdj_unit_of_universalHomeomorphism.{u, u + 1} Λ i
  refine isConstructibleEtaleModule_of_inverseImage_of_surjective Λ g _ ?_
  refine isConstructibleEtaleModule_inverseImage_directImage Λ (IsPullback.of_hasPullback f g) F ?_
  let G := (etaleModuleInverseImage.{u, u + 1} Λ (pullback.fst f g)).obj F
  refine (IsConstructibleEtaleModule Λ).prop_of_iso
    ((etaleModuleDirectImage.{u, u + 1} Λ (pullback.snd f g)).mapIso
      (asIso ((etaleModuleInverseImageAdj.{u, u + 1} Λ i).unit.app G)).symm) ?_
  refine (IsConstructibleEtaleModule Λ).prop_of_iso
    ((etaleModuleDirectImageComp.{u, u + 1} Λ i (pullback.snd f g) _ rfl).symm.app _) ?_
  exact isConstructibleEtaleModule_etaleModuleDirectImage_of_finite_of_etale Λ _ _
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ i _
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ _ F hF))

/-- **Stacks 095R for sheaves of modules, in the model `EtaleModules`.** Let `f : X ⟶ Y` be a
finite morphism of finite presentation, `Λ` a Noetherian ring and `ℱ` a constructible sheaf of
`Λ`-modules on `X_étale`. Then `f_* ℱ` is constructible.

By Stacks 095F it suffices to work over the affine opens of `Y`, the direct image commuting with
restriction to an open by Stacks 0959. Over an affine `Y`, Stacks 095K (1) gives a
surjective affine `Y' ⟶ Y` and a thickening `Z' ⊆ Y' ×_Y X` with `Z' ⟶ Y'` finite étale; by
Stacks 095Q and 0959 it suffices to treat the base change, where the direct image is that along
the finite étale `Z' ⟶ Y'` of the inverse image to `Z'` (a thickening induces an equivalence of
small étale topoi), constructible by Stacks 095H.

The coefficient ring lives in `Type (u + 1)`, the universe of the library's Stacks 095Q and 095H
for sheaves of modules. -/
@[stacks 095R "sheaves of modules over a Noetherian ring"]
theorem isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (hfp : FinitePresentation f) (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, u + 1} Λ f).obj F) := by
  let 𝒰 := Y.affineCover
  refine (isConstructibleEtaleModule_iff_forall_etaleModuleRestriction Λ _ 𝒰.X 𝒰.f
    𝒰.iUnion_range).2 fun k ↦ ?_
  have : IsAffine (𝒰.X k) := Scheme.isAffine_affineCover Y k
  refine (IsConstructibleEtaleModule Λ).prop_of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, u + 1} Λ (𝒰.f k)).app _) ?_
  refine isConstructibleEtaleModule_inverseImage_directImage Λ
    (IsPullback.of_hasPullback f (𝒰.f k)) F ?_
  exact isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite_of_isAffine Λ _
    (FinitePresentation.of_isPullback (IsPullback.of_hasPullback f (𝒰.f k)) hfp) _
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ _ F hF)

end FiniteDirectImage

/-! ### Subsheaves and quotients -/

section StrongSerre

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 09BH (3), subsheaves, in the model `EtaleModules`.** On a Noetherian scheme a
subsheaf of a constructible sheaf of `Λ`-modules is constructible. -/
theorem isConstructibleEtaleModule_of_mono {X : Scheme.{u}} [IsNoetherian X]
    {G F : EtaleModules.{u, u + 1} Λ X} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleEtaleModule Λ F) : IsConstructibleEtaleModule Λ G := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have : IsNoetherian (B.obj X hX).obj := ‹IsNoetherian X›
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hX] at hF ⊢
  exact isConstructibleModuleSheaf_of_mono B (B.obj X hX) Λ
    ((etaleModuleToBoundedSite.{u, u + 1} Λ B hX).map i) hF

/-- **Stacks 09BH (3), quotient sheaves, in the model `EtaleModules`.** On a Noetherian scheme a
quotient of a constructible sheaf of `Λ`-modules is constructible. -/
theorem isConstructibleEtaleModule_of_epi {X : Scheme.{u}} [IsNoetherian X]
    {G Q : EtaleModules.{u, u + 1} Λ X} (p : G ⟶ Q) [Epi p]
    (hG : IsConstructibleEtaleModule Λ G) : IsConstructibleEtaleModule Λ Q := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have : IsNoetherian (B.obj X hX).obj := ‹IsNoetherian X›
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B hX] at hG ⊢
  exact isConstructibleModuleSheaf_of_epi B (B.obj X hX) Λ
    ((etaleModuleToBoundedSite.{u, u + 1} Λ B hX).map p) hG

end StrongSerre

end Stacks.EtaleCohomology

end
