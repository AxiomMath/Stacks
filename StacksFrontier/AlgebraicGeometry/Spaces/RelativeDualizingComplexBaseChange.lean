module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor

/-!
# Base change of relative dualizing complexes of algebraic spaces

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation with a
relative dualizing complex `(ω, τ)`, and let `g : Y' ⟶ Y` be a morphism with base change
`f' : X' ⟶ Y'`. Then `(L(g')^* ω, Lg^* τ)` is a relative dualizing complex for `f'`, where
`Lg^* τ` is read through the base change isomorphism `Lg^* Rf_* ω ≅ Rf'_* L(g')^* ω` of
Stacks 08IR (Stacks 0E6C).

## Main results

* `AlgebraicGeometry.Space.RelativeDualizingComplex.baseChange`: the relative dualizing complex
  `(L(g')^* ω, Lg^* τ)` for `f'`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.baseChange_spec`: **Stacks 0E6C**.
-/

@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hfp : IsFinitePresentation B S hS f.hom)
  (hY' : IsAffineSpace B S hS Y'.1)

/-- A pair `(ω, τ)` is isomorphic to `(a'(𝒪_{Y'}), Tr)` after base change as soon as `Lg^* τ`,
read through the base change map, is the trace map up to an automorphism of `𝒪_{Y'}`: the
automorphism is absorbed by `a'`, the trace map being natural. -/
theorem isAffineBaseChangePair_of_comp_iso (ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (τ : (derivedModulePushforward B S hS f).obj ω ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj)
    (e : (smallEtaleDerivedModulePullback B S hS g').obj ω ≅
      ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
        (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj)
    (α : (derivedStructureSheaf B S hS Y'.1 Y'.2).obj ≅
      (derivedStructureSheaf B S hS Y'.1 Y'.2).obj)
    (h : (smallEtaleDerivedModulePullback B S hS g).map τ ≫
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom =
      smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w ω ≫
        (derivedModulePushforward B S hS f').map e.hom ≫ affineBaseChangeTrace hZ sq hfp hY' ≫
          α.hom) :
    IsAffineBaseChangePair hZ sq hfp hY' ω τ := by
  let αQ : derivedStructureSheaf B S hS Y'.1 Y'.2 ≅ derivedStructureSheaf B S hS Y'.1 Y'.2 :=
    ObjectProperty.isoMk _ α
  refine ⟨e ≪≫ (ObjectProperty.ι _).mapIso
    ((affineBaseChangeRightAdjoint hZ sq hfp hY').mapIso αQ), ?_⟩
  have hc := congrArg InducedCategory.Hom.hom
    ((quasicoherentDerivedRightAdjointAdjunction hZ f'
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f'
        (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp) hY')
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f'
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp) hY')
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
      (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp)
      (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp)).counit.naturality αQ.hom)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at hc
  have key : affineBaseChangeTrace hZ sq hfp hY' ≫ α.hom =
      (derivedModulePushforward B S hS f').map
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').map αQ.hom).hom ≫
        affineBaseChangeTrace hZ sq hfp hY' := hc.symm
  exact h.trans (whisker_eq _ ((whisker_eq _ key).trans (Functor.map_comp_assoc _ _ _ _).symm))

end Square

/-- The diagram chase behind the transitivity of base change of relative dualizing pairs, in an
arbitrary category: `b` is the derived pullback of the base change map of the first square
followed by its inverse, `p` the horizontal pasting of base change maps, `w` the base change
property along the composite square and `n` the naturality of the composition isomorphism. -/
theorem relativeDualizingPair_paste_aux {C : Type*} [Category C]
    {P Q R O₁ O₂ O₃ O₄ T₁ T₂ T₃ : C} (bh : P ⟶ Q) (bi : Q ⟶ P) (hb : bi ≫ bh = 𝟙 Q)
    (cR : P ⟶ R) (cRi : R ⟶ P) (hc : cR ≫ cRi = 𝟙 P) (s : P ⟶ O₁) (v : O₁ ⟶ O₂) (uh : O₂ ⟶ O₃)
    (t : R ⟶ O₄) (cOi : O₄ ⟶ O₁) (uhg : O₄ ⟶ O₃) (uhgi : O₃ ⟶ O₄) (hu : uhg ≫ uhgi = 𝟙 O₄)
    (bc₂ : Q ⟶ T₁) (m : T₁ ⟶ T₂) (bco : R ⟶ T₂) (n : T₂ ⟶ T₃) (tr : T₃ ⟶ O₃)
    (p : cRi ≫ bh ≫ bc₂ ≫ m = bco) (w : t ≫ uhg = bco ≫ n ≫ tr)
    (hn : t ≫ cOi = cRi ≫ s) :
    bi ≫ s ≫ v ≫ uh = bc₂ ≫ m ≫ n ≫ tr ≫ uhgi ≫ cOi ≫ v ≫ uh := by
  have p' : bc₂ ≫ m = bi ≫ cR ≫ bco := by
    rw [← p, reassoc_of% hc, reassoc_of% hb]
  rw [reassoc_of% p', ← reassoc_of% w, reassoc_of% hu, reassoc_of% hn, reassoc_of% hc]

namespace RelativeDualizingPair

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  (D : RelativeDualizingPair f hfl hfp)
  {X' Y' : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)

/-- The complex of a relative dualizing pair lies in `D_QCoh(𝒪_X)`, being pseudo-coherent. -/
theorem qcohDerived_ω : QcohDerived B S hS X D.ω :=
  derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 D.ω D.isPerfectRelativeTo.1

include sq in
/-- The base change map `Lg^* Rf_* ω ⟶ Rf'_* L(g')^* ω` of a relative dualizing pair is an
isomorphism (Stacks 08IR, `X` and `Y'` being Tor independent over `Y` as `f` is flat). -/
theorem isIso_smallEtaleDerivedBaseChangeMap :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω) :=
  isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g f' g' sq hfp.2.1 hfp.2.2
    (torIndependent_of_isFlat_left f g hfl) D.ω D.qcohDerived_ω

include sq in
/-- The map `Rf'_* L(g')^* ω ⟶ 𝒪_{Y'}` induced by `Lg^* τ` through the base change isomorphism
`Lg^* Rf_* ω ≅ Rf'_* L(g')^* ω` and `Lg^* 𝒪_Y ≅ 𝒪_{Y'}`. -/
def baseChangeTrace :
    (derivedModulePushforward B S hS f').obj ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) ⟶
      (derivedStructureSheaf B S hS Y'.1 Y'.2).obj :=
  (@asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω)
      (D.isIso_smallEtaleDerivedBaseChangeMap sq)).inv ≫
    (smallEtaleDerivedModulePullback B S hS g).map D.τ ≫
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom

include sq in
/-- `baseChangeTrace` is `Lg^* τ` read through the base change map. -/
theorem smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace :
    smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω ≫ D.baseChangeTrace sq =
      (smallEtaleDerivedModulePullback B S hS g).map D.τ ≫
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom :=
  (@asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω)
    (D.isIso_smallEtaleDerivedBaseChangeMap sq)).hom_inv_id_assoc _

include sq in
/-- The base change `(L(g')^* ω, Lg^* τ)` of a relative dualizing pair to `X'`. -/
def baseChange :
    RelativeDualizingPair f' ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) where
  ω := (smallEtaleDerivedModulePullback B S hS g').obj D.ω
  isPerfectRelativeTo := isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback f hfl hfp.1
    sq D.ω D.isPerfectRelativeTo
  τ := D.baseChangeTrace sq

include sq in
/-- **Base change of a pair to a further affine `Y''`**: if the base change of `(ω, τ)` along the
composite square to an affine `Y''` is `(a''(𝒪_{Y''}), Tr)`, then so is the base change of
`(L(g')^* ω, Lg^* τ)` along the second square, by transitivity of fibre products. -/
theorem isAffineBaseChangePair_baseChange (hZ : B.Contains (⊤_ Scheme.{u}))
    ⦃X'' Y'' : AlgebraicSpaces B S hS⦄ (f'' : X'' ⟶ Y'')
    (h : Y'' ⟶ Y') (g'' : X'' ⟶ X') (sq₂ : IsPullback g'' f'' f' h)
    (hY'' : IsAffineSpace B S hS Y''.1)
    (h₀ : IsAffineBaseChangePair hZ (sq₂.paste_horiz sq) hfp hY'' D.ω D.τ) :
    IsAffineBaseChangePair hZ sq₂
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) hY''
      ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) (D.baseChangeTrace sq) := by
  obtain ⟨e₀, h₀⟩ := h₀
  let β := @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω)
    (D.isIso_smallEtaleDerivedBaseChangeMap sq)
  let c := smallEtaleDerivedModulePullbackCompIso B S hS h g
  let ug := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g
  let uh := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) h
  let uhg := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (h ≫ g)
  let Lh := smallEtaleDerivedModulePullback B S hS h
  refine isAffineBaseChangePair_of_comp_iso hZ sq₂ _ hY'' _ _
    ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').app D.ω ≪≫ e₀)
    (uhg.symm ≪≫ (c.app _).symm ≪≫ Lh.mapIso ug ≪≫ uh) ?_
  refine (Functor.map_comp_assoc Lh _ _ _).trans
    ((whisker_eq _ (Functor.map_comp_assoc Lh _ _ _)).trans ?_)
  refine Eq.trans ?_ (whisker_eq _ (Functor.map_comp_assoc _ _ _ _)).symm
  exact relativeDualizingPair_paste_aux
    (C := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'')))
    (Lh.map β.hom) (Lh.map β.inv) (Lh.mapIso β).inv_hom_id
    (c.hom.app ((derivedModulePushforward B S hS f).obj D.ω))
    (c.inv.app ((derivedModulePushforward B S hS f).obj D.ω))
    (c.hom_inv_id_app ((derivedModulePushforward B S hS f).obj D.ω))
    (Lh.map ((smallEtaleDerivedModulePullback B S hS g).map D.τ)) (Lh.map ug.hom) uh.hom
    ((smallEtaleDerivedModulePullback B S hS (h ≫ g)).map D.τ)
    (c.inv.app (derivedStructureSheaf B S hS Y.1 Y.2).obj) uhg.hom uhg.inv uhg.hom_inv_id
    (smallEtaleDerivedModuleBaseChangeMap B S hS f' h f'' g'' sq₂.w
      ((smallEtaleDerivedModulePullback B S hS g').obj D.ω))
    ((derivedModulePushforward B S hS f'').map
      ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app D.ω))
    (smallEtaleDerivedModuleBaseChangeMap B S hS f (h ≫ g) f'' (g'' ≫ g')
      (sq₂.paste_horiz sq).w D.ω)
    ((derivedModulePushforward B S hS f'').map e₀.hom)
    (affineBaseChangeTrace hZ (sq₂.paste_horiz sq) hfp hY'')
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g'' g h sq.w sq₂.w D.ω)
    h₀ (c.inv.naturality D.τ)

end RelativeDualizingPair

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {hf : IsProper B S hS f.hom}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  (D : RelativeDualizingComplex hZ f hf hfl hfp)
  {X' Y' : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)

include sq in
/-- The base change of `(ω, τ)` to a further affine `Y''` over `Y'` is `(a''(𝒪_{Y''}), Tr)`, by
transitivity of fibre products. -/
theorem isAffineBaseChangePair_baseChange ⦃X'' Y'' : AlgebraicSpaces B S hS⦄ (f'' : X'' ⟶ Y'')
    (h : Y'' ⟶ Y') (g'' : X'' ⟶ X') (sq₂ : IsPullback g'' f'' f' h)
    (hY'' : IsAffineSpace B S hS Y''.1) :
    IsAffineBaseChangePair hZ sq₂
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) hY''
      ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) (D.baseChangeTrace sq) :=
  D.toRelativeDualizingPair.isAffineBaseChangePair_baseChange sq hZ f'' h g'' sq₂ hY''
    (D.isAffineBaseChangePair f'' (h ≫ g) (g'' ≫ g') (sq₂.paste_horiz sq) hY'')

include sq in
/-- **Stacks 0E6C.** Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces over `S`
with `f : X ⟶ Y` proper, flat and of finite presentation, and let `(ω, τ)` be a relative
dualizing complex for `f`. Then `(L(g')^* ω, Lg^* τ)` is a relative dualizing complex for `f'`:
`L(g')^* ω` is `Y'`-perfect, and the map `τ' : Rf'_* L(g')^* ω ⟶ 𝒪_{Y'}` which is `Lg^* τ`
through the base change map has the base change property of Stacks 0E5X. -/
@[stacks 0E6C]
theorem baseChange_spec :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
        ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
        ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq
          hfp.1)
        ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) ∧
      ∃ τ' : (derivedModulePushforward B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) ⟶
            (derivedStructureSheaf B S hS Y'.1 Y'.2).obj,
        smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w D.ω ≫ τ' =
            (smallEtaleDerivedModulePullback B S hS g).map D.τ ≫
              (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom ∧
          ∀ ⦃X'' Y'' : AlgebraicSpaces B S hS⦄ (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
            (g'' : X'' ⟶ X') (sq₂ : IsPullback g'' f'' f' h) (hY'' : IsAffineSpace B S hS Y''.1),
            IsAffineBaseChangePair hZ sq₂
              ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp)
              hY'' ((smallEtaleDerivedModulePullback B S hS g').obj D.ω) τ' :=
  ⟨isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback f hfl hfp.1 sq D.ω
      D.isPerfectRelativeTo,
    D.baseChangeTrace sq, D.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq,
    D.isAffineBaseChangePair_baseChange sq⟩

include sq in
/-- The relative dualizing complex `(L(g')^* ω, Lg^* τ)` for the base change `f'` of `f`
(Stacks 0E6C). -/
def baseChange :
    RelativeDualizingComplex hZ f'
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) where
  toRelativeDualizingPair := D.toRelativeDualizingPair.baseChange sq
  isAffineBaseChangePair := D.isAffineBaseChangePair_baseChange sq

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end
