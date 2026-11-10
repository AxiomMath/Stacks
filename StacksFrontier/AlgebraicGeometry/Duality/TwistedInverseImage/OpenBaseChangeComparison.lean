module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangeUnitCounit

/-!
# The base change map of twisted inverse images along an open immersion

For a cartesian square of schemes

```
  U --j'--> X
  |f'       |f
  v         v
  V --j---> Y
```

with `j` an open immersion, the base change map `α : (j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0AA6]
can be built with derived pullback `Lj^* ⊣ Rj_*` — this is
`Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange` at the adjunctions of
`Stacks.Duality.quasiCoherentDerivedAdjunction`, which is what the base change identities of
[Stacks, Tag 0B6J], [Stacks, Tag 0B6K] and [Stacks, Tag 0B6P] are about — or with restriction
`j^* ⊣ Rj_*`, which is the map of [Stacks, Tag 0A9L] whose invertibility on `D^+_QCoh` is
[Stacks, Tag 0A9P]. The two are mates of the same transformation `ξ⁻¹` under two choices of the
left adjoints of `Rj_*` and `Rj'_*`, so they differ by the comparisons of those left adjoints;
in particular the first is invertible on `D^+_QCoh` for `f` proper over a Noetherian base.

## Main results

* `Stacks.Duality.twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare` — the
  transformation `ξ` of [Stacks, Tag 0A9K] is `Stacks.CategoryTheory.BaseChange.rightAdjointSquare`
  at the quasi-coherent derived adjunctions.
* `Stacks.Duality.isIso_rightAdjointBaseChange_app_of_isOpenImmersion` — `α` at `K` is invertible
  for `K ∈ D^+_QCoh`, `f` proper and `Y` Noetherian.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

section Square

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [CompactSpace X] [CompactSpace Y] [CompactSpace Y'] [CompactSpace X']
  [QuasiCompact g'] [QuasiSeparated g'] [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact f'] [QuasiSeparated f'] [QuasiCompact g] [QuasiSeparated g]
  [(quasiCoherentDerivedPushforward f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f'
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).IsLeftAdjoint]

omit [CompactSpace X'] in
/-- **`ξ` of [Stacks, Tag 0A9K] is the mate of the conjugate of the comparison of composite
derived pullbacks**: the transformation `twistedInverseImagePushforwardBaseChange` is
`Stacks.CategoryTheory.BaseChange.rightAdjointSquare` at the quasi-coherent derived adjunctions
and the composition isomorphisms of derived pullback. -/
theorem twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare
    (sq : IsPullback g' f' f g) :
    twistedInverseImagePushforwardBaseChange g' f' f g
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq =
      (Stacks.CategoryTheory.BaseChange.rightAdjointSquare
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
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))) :=
  congrArg (fun γ => (mateEquiv (twistedInverseImageAdjunction f'
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
      (TwoSquare.mk _ _ _ _ γ)))
    (quasiCoherentDerivedPushforwardSquareIso_hom_eq g' f' f g _ _ _ _ sq.w)

omit [CompactSpace X'] in
/-- `ξ` of a cartesian square along an open immersion is invertible, in the shape of
`Stacks.CategoryTheory.BaseChange.rightAdjointSquare`. -/
theorem isIso_rightAdjointSquare_of_isOpenImmersion [IsOpenImmersion g]
    (sq : IsPullback g' f' f g) :
    IsIso (Stacks.CategoryTheory.BaseChange.rightAdjointSquare
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
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip inferInstance
  rw [← twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare]
  exact isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion g' f' f g _ _ _ _ sq

omit [CompactSpace X'] in
/-- **The base change map `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` along an open immersion is
invertible**: its conjugate is `ξ`, which is invertible. -/
theorem isIso_twoSquare_of_isOpenImmersion [IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫
          quasiCoherentDerivedPullbackCongr sq.w)) := by
  have h := isIso_rightAdjointSquare_of_isOpenImmersion g' f' f g sq
  rw [Stacks.CategoryTheory.BaseChange.rightAdjointSquare_natTrans_eq] at h
  exact conjugateEquiv_of_iso (adj₁ := (quasiCoherentDerivedAdjunction g'
      (isQuasicoherent_homology_derivedPullback' g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')).comp
      (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')))
    (adj₂ := (twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comp
      (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g))) _

end Square

section Generic

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- The inverse mate of `ξ⁻¹` does not depend on the proof that `ξ` is invertible, nor on its
spelling up to equality. -/
private lemma mateEquiv_symm_inv_congr {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {x y : H ⋙ R₂ ⟶ R₁ ⋙ G} (h : x = y) [IsIso x] [IsIso y]
    (K : C) :
    ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ (inv x))).app K =
      ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ (inv y))).app K := by
  subst h; rfl

/-- The map of [Stacks, Tag 0A9L] at `K` is the inverse mate of `ξ⁻¹` under the restriction
adjunctions `j^* ⊣ Rj_*` and `(j')^* ⊣ Rj'_*`. -/
private lemma twistedInverseImageRestrictionMap_app_eq_mateEquiv_symm
    (sq : IsPullback j' f' f j) (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq
    (OpenImmersion.twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict j') sq).app K =
      ((mateEquiv (OpenImmersion.quasiCoherentDerivedRestrictAdjunction j
        (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
      (OpenImmersion.quasiCoherentDerivedRestrictAdjunction j'
        (OpenImmersion.isQuasicoherent_homology_derivedRestrict j')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))).symm
      (TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange j' f' f j
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq)))).app K := by
  simp [OpenImmersion.twistedInverseImageRestrictionMap, mateEquiv]

/-- **The base change map `α : L(j')^* ∘ a ⟶ a' ∘ Lj^*` along an open immersion is invertible at
`K` as soon as the map of [Stacks, Tag 0A9L] is**: the two are mates of the same `ξ⁻¹` under the
two choices of the left adjoints of `Rj_*` and `Rj'_*`, so they differ by the comparisons of
those left adjoints. -/
theorem isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap
    (sq : IsPullback j' f' f j) (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    IsIso ((OpenImmersion.twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict j') sq).app K) →
    haveI := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
    IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f' j)
        (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  intro hγ
  have := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
  have := isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq
  have hξ := twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare j' f' f j sq
  rw [Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange,
    Stacks.CategoryTheory.BaseChange.mateEquiv_symm_app_leftAdjointUniq _ _ _ _ _ K,
    mateEquiv_symm_inv_congr _ _ hξ.symm K,
    ← twistedInverseImageRestrictionMap_app_eq_mateEquiv_symm j' f' f j sq K]
  infer_instance

/-- **The base change map `α` along an open immersion through the map of [Stacks, Tag 0A9L]**:
`α` at `K` is the map of Tag 0A9L at `K`, conjugated by the comparisons
(`CategoryTheory.Adjunction.leftAdjointUniq`) of restriction `j^*` with derived pullback `Lj^*`
and of `(j')^*` with `L(j')^*` as left adjoints of `Rj_*` and `Rj'_*`. -/
theorem rightAdjointBaseChange_app_eq_twistedInverseImageRestrictionMap
    (sq : IsPullback j' f' f j) (K : quasiCoherentDerivedCategory Y) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq
    (Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f' j)
        (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K =
      (Adjunction.leftAdjointUniq
          (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
          (OpenImmersion.quasiCoherentDerivedRestrictAdjunction j'
            (OpenImmersion.isQuasicoherent_homology_derivedRestrict j')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))).hom.app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ≫
        (OpenImmersion.twistedInverseImageRestrictionMap j' f' f j
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict j') sq).app K ≫
        (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
          ((Adjunction.leftAdjointUniq
            (OpenImmersion.quasiCoherentDerivedRestrictAdjunction j
              (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
            (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs j))).hom.app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
  have := isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq
  have hξ := twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare j' f' f j sq
  rw [Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange,
    Stacks.CategoryTheory.BaseChange.mateEquiv_symm_app_leftAdjointUniq _ _ _ _ _ K,
    mateEquiv_symm_inv_congr _ _ hξ.symm K,
    ← twistedInverseImageRestrictionMap_app_eq_mateEquiv_symm j' f' f j sq K]

end Generic

section Proper

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [IsNoetherian Y] [IsProper f]

/-- **The base change map of twisted inverse images along an open immersion is invertible on
`D^+_QCoh`** ([Stacks, Tag 0A9P] read through derived pullback): for `Y` Noetherian, `f` proper
and `j` an open immersion, the base change map `α : L(j')^* ∘ a ⟶ a' ∘ Lj^*` of
[Stacks, Tag 0AA6], built with the adjunctions `Lj^* ⊣ Rj_*` and `L(j')^* ⊣ Rj'_*`, is invertible
at every `K ∈ D^+_QCoh(𝒪_Y)`. It is the map of [Stacks, Tag 0A9L] conjugated by the comparisons
of the two left adjoints of `Rj_*` and of `Rj'_*`. -/
theorem isIso_rightAdjointBaseChange_app_of_isOpenImmersion (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isNoetherian_of_isProper f
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isOpenImmersion j
    haveI := isNoetherian_of_isProper f'
    haveI := isIso_rightAdjointSquare_of_isOpenImmersion j' f' f j sq
    IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f' j)
        (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isNoetherian_of_isProper f
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have := isNoetherian_of_isOpenImmersion j
  have := isNoetherian_of_isProper f'
  exact isIso_rightAdjointBaseChange_app_of_isIso_twistedInverseImageRestrictionMap j' f' f j sq K
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper j' f' f j sq K hK)

end Proper

end Stacks.Duality

end
