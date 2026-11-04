module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.UniversalFlatteningOfPure
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# The flattening of the universal family over the Grassmannian

Let `m = regularityIndex n r hr P`, `N = freeRank n r m`, `p = quotRank n r hr P` and
`G = G(N - p, N)`. The universal quotient `q_G` gives the twisted family
`ℱ_G = ℱ^{(m)}_{q_G} = coker(u_m)` on `ℙⁿ_G`, of finite presentation. By Stacks 05UH(3) (universal
flattening for a proper morphism of finite presentation) there is a monomorphism of finite
presentation `Z ⟶ G` through which `t : T ⟶ G` factors exactly when `(ℙⁿ_t)^* ℱ_G` is flat over
`T`. This is the step of the proof of Stacks 0DPA that cuts the flat locus out of `G`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.quotGrassmannian`: `G = G(N - p, N)`.
* `AlgebraicGeometry.ProjectiveQuot.universalFamily`: `ℱ_G` on `ℙⁿ_G`.
* `AlgebraicGeometry.ProjectiveQuot.flatLocus`: `Z ⟶ G`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isFlatOver_modulePullback_of_isPullback`: flatness of a base
  change does not depend on the choice of the cartesian square.
* `AlgebraicGeometry.ProjectiveQuot.exists_lift_flatLocus_iff`: `t` factors through `Z` iff
  `(ℙⁿ_t)^* ℱ_G` is flat over `T`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 05UH](https://stacks.math.columbia.edu/tag/05UH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.ProjectiveQuot

/-- **Flatness of a base change does not depend on the cartesian square**: for two cartesian
squares over the same `f : X ⟶ S` and `g : S' ⟶ S`, the inverse image of a quasi-coherent module
along the first top arrow is flat over `S'` iff along the second. -/
theorem isFlatOver_modulePullback_of_isPullback {X S X₁ X₂ S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {h₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ S'} {h₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ S'}
    (H₁ : IsPullback h₁ f₁ f g) (H₂ : IsPullback h₂ f₂ f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (hF : IsFlatOver f₁.toLRSHom.toShHom ((modulePullback h₁.toLRSHom.toShHom).obj F)) :
    IsFlatOver f₂.toLRSHom.toShHom ((modulePullback h₂.toLRSHom.toShHom).obj F) := by
  let e := H₂.isoIsPullback _ _ H₁
  have hsq : IsPullback e.hom f₂ f₁ (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by rw [H₂.isoIsPullback_hom_snd _ _ H₁, Category.comp_id]⟩
  have := SheafOfModules.modulePullback_isQuasicoherent h₁.toLRSHom.toShHom F
  rw [← H₂.isoIsPullback_hom_fst _ _ H₁]
  exact isFlatOver_of_moduleIso _ ((schemeModulePullbackCompIso e.hom h₁).app F)
    (modulePullback_isFlatOver hsq _ hF)

variable (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ)

/-- **The Grassmannian `G = G(N - p, N)`** of the proof of Stacks 0DPA, with
`N = freeRank n r m`, `p = quotRank n r hr P` and `m = regularityIndex n r hr P`. -/
abbrev quotGrassmannian : Scheme.{u} :=
  Grassmannian.scheme.{u}
    (freeRank.{u} n r (regularityIndex.{u} n r hr P) - quotRank.{u} n r hr P)
    (freeRank.{u} n r (regularityIndex.{u} n r hr P))

/-- **The universal family `ℱ_G = ℱ^{(m)}_{q_G}`** on `ℙⁿ_G`. -/
def universalFamily : (projectiveSpaceOver n (quotGrassmannian.{u} n r hr P)).Modules :=
  presentationCokernel (regularityIndex.{u} n r hr P) (Grassmannian.universalPresentation _ _)

/-- The universal family `ℱ_G` is of finite presentation. -/
instance : (universalFamily.{u} n r hr P).IsFinitePresentation :=
  isFinitePresentation_presentationCokernel _ _

/-- The universal family `ℱ_G` is quasi-coherent. -/
instance : (universalFamily.{u} n r hr P).IsQuasicoherent :=
  isQuasicoherent_presentationCokernel _ _

/-- The flatness situation of `ℱ_G` over `G` (Stacks 05MW). -/
def flatnessSituation : FlatnessSituation.{u} where
  S := quotGrassmannian.{u} n r hr P
  X := projectiveSpaceOver n (quotGrassmannian.{u} n r hr P)
  f := projectiveSpaceOver n (quotGrassmannian.{u} n r hr P) ↘ quotGrassmannian.{u} n r hr P
  F := universalFamily.{u} n r hr P
  isQuasicoherent := isQuasicoherent_presentationCokernel _ _

/-- **Stacks 05UH(3) for `ℱ_G`**: the universal flattening exists and is a monomorphism of
finite presentation. -/
theorem exists_flatLocus :
    ∃ Z : Over (quotGrassmannian.{u} n r hr P), Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty ((flatnessSituation.{u} n r hr P).flatFunctor.RepresentableBy Z) := by
  have := isProper_projectiveSpaceOver n (quotGrassmannian.{u} n r hr P)
  exact exists_mono_finitePresentation_representableBy_of_isProper _
    (universalFamily.{u} n r hr P)

/-- **The flat locus `Z ⟶ G`** of `ℱ_G`. -/
def flatLocus : Over (quotGrassmannian.{u} n r hr P) :=
  (exists_flatLocus.{u} n r hr P).choose

/-- The flat locus `Z ⟶ G` is a monomorphism. -/
instance mono_flatLocus_hom : Mono (flatLocus.{u} n r hr P).hom :=
  (exists_flatLocus.{u} n r hr P).choose_spec.1

/-- The flat locus `Z ⟶ G` is of finite presentation. -/
theorem finitePresentation_flatLocus_hom : FinitePresentation (flatLocus.{u} n r hr P).hom :=
  (exists_flatLocus.{u} n r hr P).choose_spec.2.1

/-- The representability of the flatness functor by `Z`. -/
def flatLocusRepresentableBy :
    (flatnessSituation.{u} n r hr P).flatFunctor.RepresentableBy (flatLocus.{u} n r hr P) :=
  (exists_flatLocus.{u} n r hr P).choose_spec.2.2.some

variable {n r hr P}

/-- The base-change condition of the flatness situation at `t : T ⟶ G`, read on `ℙⁿ_T`. -/
theorem isFlatAfterBaseChange_iff {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    (flatnessSituation.{u} n r hr P).IsFlatAfterBaseChange (Over.mk t) ↔
      IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj
          (universalFamily.{u} n r hr P)) := by
  have H₁ := IsPullback.of_hasPullback
    (projectiveSpaceOver n (quotGrassmannian.{u} n r hr P) ↘ quotGrassmannian.{u} n r hr P) t
  have H₂ := isPullback_projectiveSpaceOverMap n t
  have e := (Stacks.ProjectiveBundleQuotients.pullbackIso (projectiveSpaceOverMap n t)).app
    (universalFamily.{u} n r hr P)
  have hq := (flatnessSituation.{u} n r hr P).isQuasicoherent
  exact ⟨fun h ↦ (isFlatOver_iff_of_iso _ e).2
      (@isFlatOver_modulePullback_of_isPullback _ _ _ _ _ _ _ _ _ _ _ H₁ H₂
        (flatnessSituation.{u} n r hr P).F hq h),
    fun h ↦ @isFlatOver_modulePullback_of_isPullback _ _ _ _ _ _ _ _ _ _ _ H₂ H₁
      (flatnessSituation.{u} n r hr P).F hq ((isFlatOver_iff_of_iso _ e).1 h)⟩

/-- **`t : T ⟶ G` factors through the flat locus `Z` iff `(ℙⁿ_t)^* ℱ_G` is flat over `T`.** -/
theorem exists_lift_flatLocus_iff {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    (∃ z : T ⟶ (flatLocus.{u} n r hr P).left, z ≫ (flatLocus.{u} n r hr P).hom = t) ↔
      IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj
          (universalFamily.{u} n r hr P)) := by
  rw [← isFlatAfterBaseChange_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ((flatLocusRepresentableBy n r hr P).homEquiv (Over.homMk z hz : Over.mk t ⟶ _)).down
  · intro h
    let w := (flatLocusRepresentableBy n r hr P).homEquiv.symm (PLift.up h)
    exact ⟨w.left, Over.w w⟩

end AlgebraicGeometry.ProjectiveQuot

end
