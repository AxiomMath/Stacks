module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ReadingBundleTwistComparison

/-!
# The twist of the projective bundle of an inverse image

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `ℰ` a finite locally free `𝒪_X`-module and
`φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` the comparison over `f`, which identifies `𝐏(f^*ℰ)` with `Y ×_X 𝐏(ℰ)`
(`AlgebraicGeometry.Space.PrivateChern.isPullback_projectiveBundleSpacePullback`). Then
`φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(f^*ℰ)}(1)`, compatibly with the tautological quotients (Stacks 01O3 for
projective bundles of algebraic spaces).

Both `φ^*π^*ℰ ⟶ φ^*𝒪_{𝐏(ℰ)}(1)` and `π'^*f^*ℰ ⟶ 𝒪_{𝐏(f^*ℰ)}(1)` are quotients of
`(π' ≫ f)^*ℰ`, so they may be compared after the étale surjective comparison
`κ' : 𝐏((f^*ℰ)_U) ⟶ 𝐏(f^*ℰ)` from the projective bundle of the reading of `f^*ℰ` on the presenting
chart `U` of `Y`. There `κ' ≫ φ` factors as `𝐏((f^*ℰ)_U) ⟶ 𝐏(ℰ_{U → X}) ⟶ 𝐏(ℰ)`; the comparisons of
reading bundles pull the tautological quotients back to the tautological quotients
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_readingBundleSpaceMap_quotient`), and so does
the base change `𝐏((f^*ℰ)_U) ⟶ 𝐏(ℰ_{U → X})` of schemes.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.projectiveBundlePullbackMap`: the comparison
  `φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` as a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.readingBundleToSpace_comp_projectiveBundleSpacePullback`:
  `φ` restricts on the reading bundles of `f^*ℰ` to the comparisons of the reading bundles of `ℰ`.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_projectiveBundlePullbackMap_twist`:
  `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(f^*ℰ)}(1)`, compatibly with the tautological quotients.

## Implementation notes

The quotients are compared factor by factor along explicitly typed comparison morphisms, with
the composites of morphisms of algebraic spaces named once, so that no two descriptions of the
same module are compared inside a composite; the constructions of projective bundles of schemes
and of inverse images of modules are not unfolded in this file.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w w'

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

attribute [local irreducible] AlgebraicGeometry.Space.modulePullback
  Stacks.RelativeProj.symmetricSituationOfQuasicoherent
  Stacks.RelativeProj.symmetricSituation
  Stacks.RelativeProj.Situation.relativeProj
  Stacks.RelativeProj.Data.relativeProj
  SheafOfModules.sheafifiedSymmetricAlgebra
  presheafToSheaf
  Stacks.RelativeProj.Situation.relativeProjToBase
  Stacks.RelativeProj.Data.toBase
  AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace
  AlgebraicGeometry.Space.presentationOfAtlas
  AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison
  AlgebraicGeometry.Space.modulePullbackCompIso

/-- Composites in two descriptions of one category agree as soon as their factors do. -/
private theorem comp_heq_comp_of_category {C₁ C₂ : Type w} [i₁ : Category.{w'} C₁]
    [i₂ : Category.{w'} C₂]
    (hC : C₁ = C₂) (hi : HEq i₁ i₂) {P₁ Q₁ R₁ : C₁} {P₂ Q₂ R₂ : C₂} (hP : HEq P₁ P₂)
    (hQ : HEq Q₁ Q₂) (hR : HEq R₁ R₂) (a₁ : P₁ ⟶ Q₁) (a₂ : P₂ ⟶ Q₂) (ha : HEq a₁ a₂)
    (b₁ : Q₁ ⟶ R₁) (b₂ : Q₂ ⟶ R₂) (hb : HEq b₁ b₂) : HEq (a₁ ≫ b₁) (a₂ ≫ b₂) := by
  subst hC
  cases hi
  cases hP
  cases hQ
  cases hR
  cases ha
  cases hb
  rfl

/-- Images under two descriptions of one functor agree as soon as the morphisms do. -/
private theorem map_heq_map {C₁ C₂ : Type w} {D : Type*} [i₁ : Category.{w'} C₁]
    [i₂ : Category.{w'} C₂] [Category D]
    (hC : C₁ = C₂) (hi : HEq i₁ i₂) (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D) (hF : HEq F₁ F₂)
    {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (hX : HEq X₁ X₂) (hY : HEq Y₁ Y₂) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hf : HEq f₁ f₂) : HEq (F₁.map f₁) (F₂.map f₂) := by
  subst hC
  cases hi
  cases hF
  cases hX
  cases hY
  cases hf
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : Y ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The comparison `φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)`**, as a morphism of algebraic spaces. -/
abbrev projectiveBundlePullbackMap :
    projectiveBundle (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ⟶
      projectiveBundle E hfree :=
  ObjectProperty.homMk (projectiveBundleSpacePullback f E hfree)

/-- `φ` lies over `f`. -/
theorem projectiveBundlePullbackMap_comp_proj :
    projectiveBundlePullbackMap f E hfree ≫ projectiveBundleProj E hfree =
      projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫ f :=
  ObjectProperty.hom_ext _ (projectiveBundleSpacePullback_comp_proj f E hfree)

/-- **`φ` restricts on `𝐏((f^*ℰ)_ψ)` to the comparison of `𝐏(ℰ_{ψ ≫ f})`**: for `ψ : T ⟶ Y`,
`κ_ψ' ≫ φ = 𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f}) ⟶ 𝐏(ℰ)`. -/
theorem readingBundleToSpace_comp_projectiveBundleSpacePullback {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    readingBundleToSpace ψ (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫
        projectiveBundleSpacePullback f E hfree =
      readingBundlePullbackToSpace f E hfree ψ := by
  refine readingBundleSite_hom_ext ψ (pullbackModule f E)
    (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) (projectiveBundle E hfree).property.isSheaf
    ?_
  rw [← Category.assoc, bundleCover_comp_readingBundleToSpace, bundleCoverToSpace,
    Category.assoc, projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback,
    readingBundleSiteMap_comp_readingBundlePullbackToSpace]
  exact readingBundleSiteMap_comp_readingBundlePullbackToSpace f E hfree _ (chartBaseChange_w ψ)

/-- The morphism `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`, between the represented algebraic spaces. -/
abbrev pullbackSiteMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶
      representedAlgebraicSpace B S hS (readingBundleSite E hfree (ψ ≫ f)) :=
  representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ)

/-- `κ_ψ' ≫ φ = κ_{ψ ≫ f} ∘ (𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f}))`, as morphisms of algebraic spaces. -/
theorem readingBundleSpaceMap_comp_projectiveBundlePullbackMap {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    readingBundleSpaceMap (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
        ψ ≫ projectiveBundlePullbackMap f E hfree =
      pullbackSiteMap f E hfree ψ ≫ readingBundleSpaceMap E hfree (ψ ≫ f) :=
  ObjectProperty.hom_ext _ (readingBundleToSpace_comp_projectiveBundleSpacePullback f E hfree ψ)

/-- **Stacks 01O3 along `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`**, read through `pullbackSiteMap`. -/
theorem exists_iso_pullbackSiteMap_readingBundleQuotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree (ψ ≫ f)) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree (ψ ≫ f)) ≫ (ψ ≫ f) = v)
    {v' : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ Y}
    (hv' : representedSpaceMap B S hS (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ≫ ψ = v')
    {u : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ X}
    (hu : v' ≫ f = u) (h' : pullbackSiteMap f E hfree ψ ≫ v = u) :
    ∃ θ : (modulePullback B S hS (pullbackSiteMap f E hfree ψ)).obj
        (readingBundleTwist E hfree (ψ ≫ f)) ≅
        readingBundleTwist (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
          ψ,
      ((QuasiCoherentDescent.pullbackComparison B S hS (pullbackSiteMap f E hfree ψ) v u h' E).hom ≫
        (modulePullback B S hS (pullbackSiteMap f E hfree ψ)).map
          ((Iso.refl _).inv ≫ readingBundleQuotient E hfree (ψ ≫ f) hv)) ≫ θ.hom =
        (QuasiCoherentDescent.pullbackComparison B S hS v' f u hu E).hom ≫ (Iso.refl _).inv ≫
          readingBundleQuotient (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ hv' := by
  have key := exists_iso_readingBundleSitePullback_quotient E hfree f ψ hv hv' hu h'
    (isQuasicoherentOnSite_readingBundleTwist E hfree _)
    (readingBundleQuotient E hfree _ hv) (Iso.refl _) (readingBundleTwistReadingIso E hfree _)
    (quotientReadingHyp_readingBundleQuotient E hfree _ hv)
    (isQuasicoherentOnSite_readingBundleTwist (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) _)
    (readingBundleQuotient (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) _ hv') (Iso.refl _)
    (readingBundleTwistReadingIso (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) _)
    (quotientReadingHyp_readingBundleQuotient (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) _ hv')
  obtain ⟨θ, e⟩ := key
  refine ⟨θ, Eq.trans (eq_of_heq ?_) (e.trans (eq_of_heq ?_))⟩
  · refine comp_eq_comp_of_heq _ _ _ _ rfl rfl (comp_eq_comp_of_heq _ _ _ _ rfl rfl HEq.rfl ?_)
      HEq.rfl
    exact map_heq_map rfl HEq.rfl _ _ HEq.rfl HEq.rfl HEq.rfl _ _
      (comp_heq_comp_of_category rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl _ _ HEq.rfl _ _ HEq.rfl)
  · refine comp_eq_comp_of_heq _ _ _ _ rfl rfl HEq.rfl ?_
    exact comp_heq_comp_of_category rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl _ _ HEq.rfl _ _ HEq.rfl

/-- **On `𝐏((f^*ℰ)_ψ)`, the two quotients `φ^*π^*ℰ ⟶ φ^*𝒪_{𝐏(ℰ)}(1)` and
`π'^*f^*ℰ ⟶ 𝒪_{𝐏(f^*ℰ)}(1)` of `(π' ≫ f)^*ℰ` agree**, after the inverse image along the comparison
`𝐏((f^*ℰ)_ψ) ⟶ 𝐏(f^*ℰ)`, up to an isomorphism of the targets. -/
theorem exists_iso_readingBundleSpaceMap_map_twistPullback {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree (ψ ≫ f)) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree (ψ ≫ f)) ≫ (ψ ≫ f) = v)
    {v' : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ Y}
    (hv' : representedSpaceMap B S hS (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ≫ ψ = v')
    {u : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ X}
    (hu : v' ≫ f = u) :
    ∃ θ : (modulePullback B S hS (readingBundleSpaceMap (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).obj
          ((modulePullback B S hS (projectiveBundlePullbackMap f E hfree)).obj
            (projectiveBundleTwist E hfree).obj) ≅
        (modulePullback B S hS (readingBundleSpaceMap (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).obj
          (projectiveBundleTwist (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).obj,
      (modulePullback B S hS (readingBundleSpaceMap (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).map
          ((QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap f E hfree)
              (projectiveBundleProj E hfree) _ (projectiveBundlePullbackMap_comp_proj f E hfree)
              E).hom ≫
            (modulePullback B S hS (projectiveBundlePullbackMap f E hfree)).map
              (projectiveBundleTautological E hfree).hom) ≫ θ.hom =
        (modulePullback B S hS (readingBundleSpaceMap (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).map
          ((QuasiCoherentDescent.pullbackComparison B S hS
            (projectiveBundleProj (pullbackModule f E)
              (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)) f _ rfl E).hom ≫
            (projectiveBundleTautological (pullbackModule f E)
              (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom) := by
  have hκ' : readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ ≫
      projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) =
      v' := (ObjectProperty.hom_ext _ (readingBundleToSpace_comp_proj ψ _ _)).trans hv'
  have hκ : readingBundleSpaceMap E hfree (ψ ≫ f) ≫ projectiveBundleProj E hfree = v :=
    (ObjectProperty.hom_ext _ (readingBundleToSpace_comp_proj (ψ ≫ f) E hfree)).trans hv
  have hN := readingBundleSpaceMap_comp_projectiveBundlePullbackMap f E hfree ψ
  have h₀ : readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ ≫
      (projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫ f) = u := by
    rw [← Category.assoc, hκ', hu]
  have h₀' : (readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ ≫
      projectiveBundlePullbackMap f E hfree) ≫ projectiveBundleProj E hfree = u := by
    rw [Category.assoc, projectiveBundlePullbackMap_comp_proj, h₀]
  have h₀'' : (pullbackSiteMap f E hfree ψ ≫ readingBundleSpaceMap E hfree (ψ ≫ f)) ≫
      projectiveBundleProj E hfree = u :=
    (congrArg (· ≫ projectiveBundleProj E hfree) hN).symm.trans h₀'
  have h4 : pullbackSiteMap f E hfree ψ ≫ v = u := by
    rw [← hκ, ← Category.assoc, h₀'']
  have e1 := pullbackComparison_hom_comp_map_pullbackComparison_hom_comp_map E
    (readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
    (projectiveBundlePullbackMap f E hfree) (projectiveBundlePullbackMap_comp_proj f E hfree) h₀ h₀'
    (projectiveBundleTautological E hfree).hom
  obtain ⟨θ₂, e2⟩ := exists_iso_pullbackComparison_hom_comp_map_of_eq E hN h₀' h₀''
    (projectiveBundleTautological E hfree).hom
  have e3 := pullbackComparison_hom_comp_map_pullbackComparison_hom_comp_map E
    (pullbackSiteMap f E hfree ψ) (readingBundleSpaceMap E hfree (ψ ≫ f)) hκ h4 h₀''
    (projectiveBundleTautological E hfree).hom
  have e3' := comp_inv_app_eq_of_comp_hom_app_eq (modulePullbackCompIso B S hS
    (pullbackSiteMap f E hfree ψ) (readingBundleSpaceMap E hfree (ψ ≫ f)))
    (projectiveBundleTwist E hfree).obj _ _ e3
  obtain ⟨θ₄, e4⟩ := exists_iso_pullbackComparison_hom_comp_map_of_exists_iso E
    (pullbackSiteMap f E hfree ψ) h4
    (exists_iso_readingBundleSpaceMap_quotient E hfree (ψ ≫ f) hκ hv)
  obtain ⟨θ₅, e5⟩ := exists_iso_pullbackSiteMap_readingBundleQuotient f E hfree ψ hv hv' hu h4
  have c1 := exists_iso_comp_eq_of_chain
    ((modulePullbackCompIso B S hS (readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
      (projectiveBundlePullbackMap f E hfree)).app (projectiveBundleTwist E hfree).obj) θ₂
    ((modulePullbackCompIso B S hS (pullbackSiteMap f E hfree ψ)
      (readingBundleSpaceMap E hfree (ψ ≫ f))).app (projectiveBundleTwist E hfree).obj).symm θ₄ θ₅
    e1 e2 e3' e4 e5
  obtain ⟨θ₁, c1⟩ := c1
  have f1 := pullbackComparison_hom_comp_map_pullbackComparison_hom_comp E f
    (readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hκ' rfl hu h₀
    (projectiveBundleTautological (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom
  obtain ⟨θ₂, f2⟩ := exists_iso_readingBundleSpaceMap_quotient (pullbackModule f E)
    (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ hκ' hv'
  have c2 : ((QuasiCoherentDescent.pullbackComparison B S hS (readingBundleSpaceMap
        (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
        (projectiveBundleProj (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫ f) u h₀ E).hom ≫
      (modulePullback B S hS (readingBundleSpaceMap (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).map
          ((QuasiCoherentDescent.pullbackComparison B S hS
            (projectiveBundleProj (pullbackModule f E)
              (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)) f _ rfl E).hom ≫
            (projectiveBundleTautological (pullbackModule f E)
              (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom)) ≫ θ₂.hom =
      (QuasiCoherentDescent.pullbackComparison B S hS v' f u hu E).hom ≫ (Iso.refl _).inv ≫
        readingBundleQuotient (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ hv' := by
    rw [f1, Category.assoc]
    refine congrArg (_ ≫ ·) (Eq.trans (eq_of_heq ?_) f2)
    exact comp_eq_comp_of_heq _ _ _ _ rfl rfl (comp_eq_comp_of_heq _ _ _ _ rfl rfl HEq.rfl HEq.rfl)
      HEq.rfl
  exact ⟨_, comp_hom_eq_of_iso_comp _ _ _ θ₁ θ₂ c1 c2⟩

/-- **The comparison `φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` pulls the twist back to the twist** (Stacks 01O3 for
projective bundles of algebraic spaces): there is an isomorphism `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(f^*ℰ)}(1)`
carrying the inverse image of the tautological quotient of `𝐏(ℰ)` to the tautological quotient of
`𝐏(f^*ℰ)`, both read as quotients of `(π' ≫ f)^*ℰ`. -/
theorem exists_iso_projectiveBundlePullbackMap_twist :
    ∃ e : (modulePullback B S hS (projectiveBundlePullbackMap f E hfree)).obj
        (projectiveBundleTwist E hfree).obj ≅
        (projectiveBundleTwist (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).obj,
      ((QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap f E hfree)
          (projectiveBundleProj E hfree) _ (projectiveBundlePullbackMap_comp_proj f E hfree)
          E).hom ≫
        (modulePullback B S hS (projectiveBundlePullbackMap f E hfree)).map
          (projectiveBundleTautological E hfree).hom) ≫ e.hom =
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleProj (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)) f _ rfl E).hom ≫
          (projectiveBundleTautological (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom := by
  have sq := (isPullback_readingBundleToSpace (chartToSpace B S hS Y (bundleBaseChart Y))
    (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).flip
  have hψ : IsEtale B S hS (chartToSpace B S hS Y (bundleBaseChart Y)).hom :=
    presentationAtlas_isEtale (projectiveBundlePresentation Y)
  have hflat : IsFlat B S hS (readingBundleSpaceMap (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
        (chartToSpace B S hS Y (bundleBaseChart Y))).hom :=
    isFlat_of_isEtale B S hS (isEtale_of_isPullback_yoneda B S hS sq hψ)
  have hsurj : IsJointlySurjective B S hS (fun _ : Unit =>
      (representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
          (chartToSpace B S hS Y (bundleBaseChart Y)))).1)
      (fun _ => (readingBundleSpaceMap (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
          (chartToSpace B S hS Y (bundleBaseChart Y))).hom) :=
    (isJointlySurjective_const_iff B S hS _).2 (surjective_pointsMap_of_isPullback B S hS sq
      ((surjective_iff_surjective_pointsMap B S hS _ Y.property _ _).1
        (projectiveBundlePresentation Y).surjective))
  have hepi : Epi ((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundlePullbackMap f E hfree) (projectiveBundleProj E hfree) _
        (projectiveBundlePullbackMap_comp_proj f E hfree) E).hom ≫
      (modulePullback B S hS (projectiveBundlePullbackMap f E hfree)).map
        (projectiveBundleTautological E hfree).hom) :=
    epi_comp' (IsIso.epi_of_iso _) (epi_modulePullback_map B S hS _ _
      (epi_projectiveBundleTautological E hfree))
  have hepi' : Epi ((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)) f _ rfl E).hom ≫
      (projectiveBundleTautological (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom) :=
    epi_comp' (IsIso.epi_of_iso _) (epi_projectiveBundleTautological _ _)
  exact exists_iso_comp_eq_of_modulePullback (fun _ : Unit => readingBundleSpaceMap
    (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
      (chartToSpace B S hS Y (bundleBaseChart Y))) (fun _ => hflat) hsurj _ _
    (fun _ => exists_iso_readingBundleSpaceMap_map_twistPullback f E hfree _ rfl rfl rfl)

end AlgebraicGeometry.Space.PrivateChern

end
