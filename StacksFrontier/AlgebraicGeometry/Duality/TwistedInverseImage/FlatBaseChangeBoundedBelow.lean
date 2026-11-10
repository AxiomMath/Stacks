module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonCharts
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback

/-!
# Flat base change of the twisted inverse image of a proper morphism on `D^+_QCoh`

Let `f : X ⟶ Y` be a proper morphism and `g : Y' ⟶ Y` a flat morphism of Noetherian schemes, with
base change `f' : X' ⟶ Y'`. The base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of
[Stacks, Tag 0AA6] is an isomorphism for every `K ∈ D^+_QCoh(𝒪_Y)`.

This is the step of the proof of [Stacks, Tag 0E9U] about the compactification: formation of `a`
and `a'` commutes with restriction to opens of `Y` and `Y'` on `D^+_QCoh`
([Stacks, Tag 0A9P] (2)), so by [Stacks, Tag 0E9S] (pasting of base change maps,
`Stacks.Duality.isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent`) the question is
local on affine opens of `Y` and `Y'`, where it is [Stacks, Tag 0AA8] part (3): a flat ring map
has finite Tor dimension.

## Main results

* `Stacks.Duality.hasFiniteTorDimensionRingHom_of_flat` — a flat ring map has finite Tor
  dimension.
* `Stacks.Duality.isBoundedBelow_quasiCoherentDerivedPullback_obj_of_flat` — `Lg^*` preserves
  `D^+` for `g` flat.
* `Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right` — the
  base change map is invertible on `D^+_QCoh(𝒪_Y)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **A flat ring map has finite Tor dimension**: `S`, in degree zero, is its own flat
representative. -/
theorem hasFiniteTorDimensionRingHom_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) : HasFiniteTorDimensionRingHom φ := by
  let := φ.toAlgebra
  have : Module.Flat R S := hφ
  refine ⟨0, 0, (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    R _ 0 0).2 ⟨(CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S),
      fun i => ?_, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩⟩
  obtain rfl | h := eq_or_ne i 0
  · exact Module.Flat.of_linearEquiv
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R S)).toLinearEquiv)
  · have : Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R S)).X i) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)
    infer_instance

/-- **Derived pullback along a flat morphism preserves boundedness below**: it is degreewise
pullback, which is exact. -/
theorem isBoundedBelow_quasiCoherentDerivedPullback_obj_of_flat {Z W : Scheme.{u}} (e : Z ⟶ W)
    [Flat e] (K : quasiCoherentDerivedCategory W)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow ((quasiCoherentDerivedPullback' e).obj K).obj := by
  have := preservesFiniteLimits_modulesPullback_of_flat e
  have := AlgebraicGeometry.preservesFiniteColimits_modulesPullback e
  obtain ⟨n₀, hn₀⟩ := hK
  exact ⟨n₀, fun m hm => ((Scheme.Modules.pullback e).map_isZero (hn₀ m hm)).of_iso
    ((DerivedCategory.homologyFunctor Z.Modules m).mapIso
        ((derivedPullbackMapDerivedIso e).app K.obj) ≪≫
      (DerivedCategoryB.mapDerivedCategoryHomologyIso (Scheme.Modules.pullback e) m).app K.obj)⟩

section Chart

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [IsProper f] [Flat g] [IsNoetherian Y] [IsNoetherian Y']

/-- **The base change map of [Stacks, Tag 0AA6] for `f` proper and `g` flat over Noetherian bases
is invertible over an affine chart on `D^+_QCoh`**: over affine opens `V' ⊆ g⁻¹V`, the
restriction of `L(g')^* a(K) ⟶ a'(Lg^*K)` to `f'⁻¹V'` is invertible for `K` bounded below. -/
theorem isIso_map_rightAdjointBaseChange_app_of_isAffineOpen_of_flat_right
    (sq : IsPullback g' f' f g) (V : Y.Opens) (hV : IsAffineOpen V) (V' : Y'.Opens)
    (hV' : IsAffineOpen V') (hVV' : V' ≤ g ⁻¹ᵁ V) (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI := isIso_rightAdjointSquare_of_torIndependent sq (torIndependent_of_flat_right f g)
    IsIso ((quasiCoherentDerivedPullback' (f' ⁻¹ᵁ V').ι).map
      ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K)) := by
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsNoetherian V.toScheme := isNoetherian_of_isOpenImmersion V.ι
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have sq₂ := (isPullback_morphismRestrict f' V').flip
  have sqC := (isPullback_morphismRestrict f V).flip
  have : CompactSpace (f' ⁻¹ᵁ V').toScheme := compactSpace_of_isPullback sq₂
  have : QuasiSeparatedSpace (f' ⁻¹ᵁ V').toScheme :=
    (f' ⁻¹ᵁ V').ι.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace (f ⁻¹ᵁ V).toScheme := compactSpace_of_isPullback sqC
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    (f ⁻¹ᵁ V).ι.isOpenEmbedding.quasiSeparatedSpace
  have : IsProper (f ∣_ V) := MorphismProperty.of_isPullback sqC inferInstance
  have sqO := sq₂.paste_horiz sq
  have hk : f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    intro x hx
    change f.base (g'.base x) ∈ V
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hVV' hx
  have hp : g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hk ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g' :=
    Scheme.Hom.resLE_comp_ι _ _
  have hq : g.resLE V V' hVV' ≫ V.ι = V'.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have sqD : IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hk) (f' ∣_ V') (f ∣_ V)
      (g.resLE V V' hVV') := by
    refine IsPullback.of_right (by rwa [hp, hq]) ?_ sqC
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hq,
      ← Category.assoc, hp, Category.assoc, sq.w, ← Category.assoc, ← Category.assoc,
      morphismRestrict_ι]
  have hT := torIndependent_of_flat_right (f ∣_ V) (g.resLE V V' hVV')
  -- over the affine chart: [Stacks, Tag 0AA8] part (3)
  have hflat : (g.resLE V V' hVV').appTop.hom.Flat := by
    have h := (g.resLE V V' hVV').flat_appLE (isAffineOpen_top V.toScheme)
      (isAffineOpen_top V'.toScheme) (by simp)
    have happ : (g.resLE V V' hVV').appLE ⊤ ⊤ (by simp) = (g.resLE V V' hVV').appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rwa [happ] at h
  have hD := isIso_twistedInverseImageBaseChangeMap_app_of_finiteTorDimension sqD hT
    (hasFiniteTorDimensionRingHom_of_flat _ hflat) ((quasiCoherentDerivedPullback' V.ι).obj K)
    (isBoundedBelow_quasiCoherentDerivedPullback_obj V.ι K hK)
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqD hT
  have := isIso_rightAdjointSquare_of_torIndependent sqD hT
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange] at hD
  -- the open immersions: [Stacks, Tag 0A9P] (2)
  have : IsNoetherian X := isNoetherian_of_isProper f
  have hC := isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap _ _ _ _
    sqC K (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ sqC K hK)
  have hO := (isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent sqC sqD sqO hp hq
    (torIndependent_of_flat_right f V.ι) hT (torIndependent_of_flat_right f (V'.ι ≫ g)) K hD).2
    (Functor.map_isIso _ _)
  have hB := isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap _ _ _ _
    sq₂ ((quasiCoherentDerivedPullback' g).obj K)
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ sq₂ _
      (isBoundedBelow_quasiCoherentDerivedPullback_obj_of_flat g K hK))
  exact (isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent sq sq₂ sqO rfl rfl
    (torIndependent_of_flat_right f g) (torIndependent_of_flat_right f' V'.ι)
    (torIndependent_of_flat_right f (V'.ι ≫ g)) K hB).1 hO

end Chart

/-- **Flat base change of the twisted inverse image of a proper morphism on `D^+_QCoh`.** Let
`f : X ⟶ Y` be proper and `g : Y' ⟶ Y` flat, with `Y` and `Y'` Noetherian, and `f' : X' ⟶ Y'` the
base change of `f`. Then the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6]
is an isomorphism for every `K ∈ D^+_QCoh(𝒪_Y)`. This is the core of [Stacks, Tag 0E9U]. -/
theorem isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right
    {X' X Y' Y : Scheme.{u}} [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [IsProper f] [Flat g] [IsNoetherian Y] [IsNoetherian Y']
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
      (torIndependent_of_flat_right f g)
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_right f g)
  have := isIso_rightAdjointSquare_of_torIndependent sq (torIndependent_of_flat_right f g)
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  let I := {VV : Y.affineOpens × Y'.affineOpens // (VV.2 : Y'.Opens) ≤ g ⁻¹ᵁ (VV.1 : Y.Opens)}
  have hU : TopologicalSpace.IsOpenCover (fun i : I => f' ⁻¹ᵁ (i.1.2 : Y'.Opens)) := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨V, hV⟩ := (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top Y)).exists_mem
      (g.base (f'.base x))
    obtain ⟨V', hV', hxV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f'.base x) (U := g ⁻¹ᵁ (V : Y.Opens)) hV
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(V, ⟨V', hV'⟩), hV'V⟩, hxV'⟩
  exact isIso_of_forall_isIso_quasiCoherentDerivedPullback _ hU _ fun i =>
    isIso_map_rightAdjointBaseChange_app_of_isAffineOpen_of_flat_right sq _ i.1.1.2 _ i.1.2.2 i.2
      K hK

end Stacks.Duality

end
