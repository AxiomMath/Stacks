module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalization
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperPerfectSupport
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceAtPoints

/-!
# Base change of the twisted inverse image of a perfect proper morphism

Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes and `g : Y' ⟶ Y` a morphism
with `Y'` Noetherian, such that `X` and `Y'` are Tor independent over `Y`; let
`X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. Then the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is an isomorphism for every
`K ∈ D_QCoh(𝒪_Y)`: [Stacks, Tag 0BZG].

Following the source: by [Stacks, Tag 0AAA] the formation of `a` and `a'` commutes with
restriction to opens of `Y` and `Y'` (for `a'` because `f'` is again perfect, being a Tor
independent base change of `f` over a Noetherian base), so by pasting squares
([Stacks, Tag 0ATR], as in [Stacks, Tag 0E9S]) the restriction of the base change map to
`f'⁻¹(V')`, for affine opens `V' ⊆ g⁻¹(V)`, is the base change map of a square over the affine
morphism `V' ⟶ V`, which is invertible by [Stacks, Tag 0AA8] (2).

## Main results

* `AlgebraicGeometry.torIndependent_comp_of_isOpenImmersion` — Tor independence survives
  restricting the second morphism to an open.
* `Stacks.Duality.isIso_map_rightAdjointBaseChange_app_of_isAffineOpen_of_perfect` — the base
  change map is invertible over an affine chart.
* `Stacks.Duality.isIso_torIndependentTwistedInverseImageBaseChange_app_of_perfect` —
  [Stacks, Tag 0BZG].

## References

* [Stacks Project, Tag 0BZG](https://stacks.math.columbia.edu/tag/0BZG)
* [Stacks Project, Tag 0E9S](https://stacks.math.columbia.edu/tag/0E9S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Tor independence survives restricting the second morphism to an open**: if `f : X ⟶ S` and
`g : Y ⟶ S` are Tor independent and `j : W ⟶ Y` is an open immersion, then `f` and `j ≫ g` are
Tor independent, the local rings of `W` being those of `Y`. -/
theorem torIndependent_comp_of_isOpenImmersion {S X Y W : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} (h : TorIndependent f g) (j : W ⟶ Y) [IsOpenImmersion j] :
    TorIndependent f (j ≫ g) := by
  rw [torIndependent_iff_forall_torIndependentAt] at h ⊢
  intro x w hxw
  have h₁ : f.base ((𝟙 X : X ⟶ X).base x) = g.base (j.base w) := by
    simpa using hxw
  exact (torIndependentAt_iff_of_isIso_stalkMap (𝟙 X) j (𝟙 S) (by simp) (by simp) hxw h₁).1
    (h _ _ h₁)

end AlgebraicGeometry

namespace Stacks.Duality

section Chart

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [IsNoetherian X]
  [IsNoetherian Y'] [IsNoetherian Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [IsProper f] [AlgebraicGeometry.Perfect f]

/-- **The base change map of [Stacks, Tag 0AA6] for a perfect proper `f` is invertible over an
affine chart**: over affine opens `V' ⊆ g⁻¹V`, the restriction of `L(g')^* a(K) ⟶ a'(Lg^*K)` to
`f'⁻¹V'` is invertible. -/
theorem isIso_map_rightAdjointBaseChange_app_of_isAffineOpen_of_perfect
    (sq : IsPullback g' f' f g) (hTor : TorIndependent f g)
    (V : Y.Opens) (hV : IsAffineOpen V) (V' : Y'.Opens) (hV' : IsAffineOpen V')
    (hVV' : V' ≤ g ⁻¹ᵁ V) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_rightAdjointSquare_of_torIndependent sq hTor
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
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : PseudoCoherent f' := (pseudoCoherent_iff_locallyOfFiniteType f').2 inferInstance
  have : AlgebraicGeometry.Perfect f' := perfect_of_isPullback_of_torIndependent sq hTor
  have : IsNoetherian X' := isNoetherian_of_isProper f'
  have sq₂ := (isPullback_morphismRestrict f' V').flip
  have sqC := (isPullback_morphismRestrict f V).flip
  have : IsNoetherian V.toScheme := isNoetherian_of_isOpenImmersion V.ι
  have : IsNoetherian (f ⁻¹ᵁ V).toScheme := isNoetherian_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  have : IsNoetherian (f' ⁻¹ᵁ V').toScheme := isNoetherian_of_isOpenImmersion (f' ⁻¹ᵁ V').ι
  have : IsProper (f ∣_ V) := MorphismProperty.of_isPullback sqC inferInstance
  have : AlgebraicGeometry.Perfect (f ∣_ V) := perfect_of_isPullback_of_flat sqC
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
  have hTorD : TorIndependent (f ∣_ V) (g.resLE V V' hVV') :=
    torIndependent_morphismRestrict_resLE f g hTor hVV'
  have hTorO : TorIndependent f (V'.ι ≫ g) := torIndependent_comp_of_isOpenImmersion hTor V'.ι
  have hD := isIso_twistedInverseImageBaseChangeMap_app_of_perfect sqD hTorD
    ((quasiCoherentDerivedPullback' V.ι).obj K)
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqD hTorD
  have := isIso_rightAdjointSquare_of_torIndependent sqD hTorD
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange] at hD
  have hC := isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_perfect _ _ _ _ sqC K
  have hO := (isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent sqC sqD sqO hp hq
    (torIndependent_of_flat_right f V.ι) hTorD hTorO K hD).2 (Functor.map_isIso _ _)
  exact (isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent sq sq₂ sqO rfl rfl
    hTor (torIndependent_of_flat_right f' V'.ι) hTorO K
    (isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_perfect _ _ _ _ sq₂
      ((quasiCoherentDerivedPullback' g).obj K))).1 hO

end Chart

/-- **[Stacks, Tag 0BZG].** Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes and
`g : Y' ⟶ Y` a morphism with `Y'` Noetherian, and let `X' = X ×_Y Y'`, with projections
`g' : X' ⟶ X` and `f' : X' ⟶ Y'`. If `X` and `Y'` are Tor independent over `Y`, then the base
change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is an isomorphism for every
`K ∈ D_QCoh(𝒪_Y)`, where `a` and `a'` are the right adjoints of `Rf_*` and `Rf'_*` on `D_QCoh`
([Stacks, Tag 0A9E]). -/
@[stacks 0BZG]
theorem isIso_torIndependentTwistedInverseImageBaseChange_app_of_perfect {X' X Y' Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y'] {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsProper f]
    [AlgebraicGeometry.Perfect f] (hTor : TorIndependent f g)
    (K : quasiCoherentDerivedCategory Y) :
    haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    IsIso ((torIndependentTwistedInverseImageBaseChange sq hTor).app K) := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have := isIso_rightAdjointSquare_of_torIndependent sq hTor
  change IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app K)
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  have hU : TopologicalSpace.IsOpenCover fun i : {VV : Y.affineOpens × Y'.affineOpens //
      (VV.2 : Y'.Opens) ≤ g ⁻¹ᵁ (VV.1 : Y.Opens)} => f' ⁻¹ᵁ (i.1.2 : Y'.Opens) := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨V, hV⟩ := (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top Y)).exists_mem
      (g.base (f'.base x))
    obtain ⟨V', hV', hxV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f'.base x) (U := g ⁻¹ᵁ (V : Y.Opens)) hV
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(V, ⟨V', hV'⟩), hV'V⟩, hxV'⟩
  exact isIso_of_forall_isIso_quasiCoherentDerivedPullback _ hU _ fun i =>
    isIso_map_rightAdjointBaseChange_app_of_isAffineOpen_of_perfect sq hTor _ i.1.1.2 _ i.1.2.2
      i.2 K

end Stacks.Duality
