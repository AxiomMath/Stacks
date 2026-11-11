module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsTowerPointwise
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherentIsoTower

/-!
# `RΓ(X, E ⊗^L K)` in Situation 0DIK: Stacks 0DIM

In Situation [Stacks, Tag 0DIK], let `K` be as in [Stacks, Tag 0DIL] and `E` perfect on `X`.
[Stacks, Tag 0DIM]: `M = RΓ(X, K ⊗^L E)` is pseudo-coherent in `D(A)`, and
`RΓ(Xₙ, Kₙ ⊗^L E|_{Xₙ}) = M ⊗^L_A Aₙ` canonically.

## Main results

* `StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso_of_seq`:
  [Stacks, Tag 0CQF] for a tower of rings given as a sequence of maps.

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace StacksDraft.DerivedInverseLimit

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0CQF] for a tower isomorphic to the restricted one, with the transition and
projection maps named.** `derivedLimit_isPseudoCoherent_and_baseChange_iso_of_iso` with the maps
`A.map (n + 1 ⟶ n)` and `c.π.app n` given as `t n` and `π n`. -/
theorem derivedLimit_isPseudoCoherent_and_baseChange_iso_of_eq
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (t : ∀ n : ℕ, A.obj (op (n + 1)) ⟶ A.obj (op n))
    (ht : ∀ n : ℕ, A.map (homOfLE (Nat.le_succ n)).op = t n)
    (π : ∀ n : ℕ, c.pt ⟶ A.obj (op n)) (hπ : ∀ n : ℕ, c.π.app (op n) = π n)
    (hcomp : ∀ n : ℕ, (π n).hom = (t n).hom.comp (π (n + 1)).hom)
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A.obj (op n))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (t n).hom).mapDerivedCategory.obj (Kₙ n))
    (hSurjective : ∀ n : ℕ, Function.Surjective (t n).hom)
    (hLocallyNilpotent : ∀ n : ℕ, (RingHom.ker (t n).hom).IsLocallyNilpotent)
    (hPseudoCoherent : ∀ n : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n))
    (hBaseChange : ∀ n : ℕ, IsIso (derivedBaseChangeComparison (t n).hom (φ n)))
    (Y : ℕ → DerivedCategory (ModuleCat.{u} c.pt)) (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (e : ∀ n : ℕ, Y n ⟶ (ModuleCat.restrictScalars (π n).hom).mapDerivedCategory.obj (Kₙ n))
    [he' : ∀ n : ℕ, IsIso (e n)]
    (he : ∀ n : ℕ, s n ≫ e n = e (n + 1) ≫
      ((ModuleCat.restrictScalars (π (n + 1)).hom).mapDerivedCategory.map (φ n) ≫
        (derivedRestrictScalarsComp (π (n + 1)).hom (t n).hom (π n).hom (hcomp n)).hom.app
          (Kₙ n)))
    [HasProduct Y] (K : DerivedCategory (ModuleCat.{u} c.pt))
    (p : K ⟶ ∏ᶜ Y) (δ : ∏ᶜ Y ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈
      distTriang (DerivedCategory (ModuleCat.{u} c.pt))) :
    PseudoCoherence.IsPseudoCoherent K ∧
      ∀ n : ℕ, IsIso (derivedBaseChangeComparison (π n).hom (p ≫ Pi.π Y n ≫ e n)) := by
  obtain rfl : t = fun n ↦ A.map (homOfLE (Nat.le_succ n)).op := (funext ht).symm
  obtain rfl : π = fun n ↦ c.π.app (op n) := (funext hπ).symm
  exact derivedLimit_isPseudoCoherent_and_baseChange_iso_of_iso.{u, u} A c hc Kₙ φ hSurjective
    hLocallyNilpotent (Or.inl hPseudoCoherent) hBaseChange Y s (fun n ↦ asIso (e n)) he K p δ hT

/-- The cone `R₀ ⟶ Rₙ` over the tower of rings `Functor.ofOpSequence t` given by maps `π n`
compatible with the transitions. -/
def seqCone {R : ℕ → CommRingCat.{u}} {R₀ : CommRingCat.{u}} (t : ∀ n : ℕ, R (n + 1) ⟶ R n)
    (π : ∀ n : ℕ, R₀ ⟶ R n) (hcomp : ∀ n : ℕ, (π n).hom = (t n).hom.comp (π (n + 1)).hom) :
    Cone (Functor.ofOpSequence t) where
  pt := R₀
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj R₀) (fun n ↦ π n) fun n ↦ by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    ext x
    exact (congrArg (fun f : R₀.carrier →+* (R n).carrier => f x) (hcomp n))

/-- **[Stacks, Tag 0CQF] for a tower of rings given as a sequence**: rings `Rₙ` with transitions
`t n : Rₙ₊₁ ⟶ Rₙ`, a limit `R₀` with projections `π n`, and a tower `(Yₙ, sₙ)` of `D(R₀)`
identified (`e n`, invertible) with the restriction of a tower `(Kₙ, φₙ)` of pseudo-coherent
objects whose base change maps are isomorphisms. Every derived limit `K` of `(Yₙ, sₙ)`, with
structure map `p`, is pseudo-coherent, and `K ⊗^L_{R₀} Rₙ ⟶ Kₙ` adjoint to `p ≫ πₙ ≫ eₙ` is an
isomorphism. -/
theorem derivedLimit_isPseudoCoherent_and_baseChange_iso_of_seq
    {R : ℕ → CommRingCat.{u}} {R₀ : CommRingCat.{u}} (t : ∀ n : ℕ, R (n + 1) ⟶ R n)
    (π : ∀ n : ℕ, R₀ ⟶ R n) (hcomp : ∀ n : ℕ, (π n).hom = (t n).hom.comp (π (n + 1)).hom)
    (hc : IsLimit (seqCone t π hcomp))
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (R n)))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (t n).hom).mapDerivedCategory.obj (Kₙ n))
    (hSurjective : ∀ n : ℕ, Function.Surjective (t n).hom)
    (hLocallyNilpotent : ∀ n : ℕ, (RingHom.ker (t n).hom).IsLocallyNilpotent)
    (hPseudoCoherent : ∀ n : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n))
    (hBaseChange : ∀ n : ℕ, IsIso (derivedBaseChangeComparison (t n).hom (φ n)))
    (Y : ℕ → DerivedCategory (ModuleCat.{u} R₀)) (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (e : ∀ n : ℕ, Y n ⟶ (ModuleCat.restrictScalars (π n).hom).mapDerivedCategory.obj (Kₙ n))
    [he' : ∀ n : ℕ, IsIso (e n)]
    (he : ∀ n : ℕ, s n ≫ e n = e (n + 1) ≫
      ((ModuleCat.restrictScalars (π (n + 1)).hom).mapDerivedCategory.map (φ n) ≫
        (derivedRestrictScalarsComp (π (n + 1)).hom (t n).hom (π n).hom (hcomp n)).hom.app
          (Kₙ n)))
    [HasProduct Y] (K : DerivedCategory (ModuleCat.{u} R₀))
    (p : K ⟶ ∏ᶜ Y) (δ : ∏ᶜ Y ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈
      distTriang (DerivedCategory (ModuleCat.{u} R₀))) :
    PseudoCoherence.IsPseudoCoherent K ∧
      ∀ n : ℕ, IsIso (derivedBaseChangeComparison (π n).hom (p ≫ Pi.π Y n ≫ e n)) :=
  derivedLimit_isPseudoCoherent_and_baseChange_iso_of_eq (Functor.ofOpSequence t)
    (seqCone t π hcomp) hc t (fun n ↦ Functor.ofOpSequence_map_homOfLE_succ t n) π
    (fun _ ↦ rfl) hcomp Kₙ φ hSurjective hLocallyNilpotent hPseudoCoherent hBaseChange Y s e
    (he' := fun n ↦ he' n) he K p δ hT

end StacksDraft.DerivedInverseLimit

namespace Stacks.CategoryTheory.TowerStep

universe w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄

variable {𝒳 : Type t₁} {𝒳' : Type t₂} {𝒜 : Type t₃} {𝒜' : Type t₄}
  [Category.{w₁} 𝒳] [Category.{w₂} 𝒳'] [Category.{w₃} 𝒜] [Category.{w₄} 𝒜']

/-- `towerSectionsHom` is invertible when the projection formula map and the comparison are. -/
theorem isIso_towerSectionsHom (Γ : 𝒳 ⥤ 𝒜) (Γ' : 𝒳' ⥤ 𝒜') (r : 𝒜' ⥤ 𝒜) (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳)
    (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (Lp' : 𝒳 ⥤ 𝒳') (P' : 𝒳' ⥤ 𝒳) (K' : 𝒳')
    (pf : T.flip.obj (P'.obj K') ⟶ Lp' ⋙ T'.flip.obj K' ⋙ P') (PF : P' ⋙ Γ ⟶ Γ' ⋙ r)
    {P'₀ : 𝒳' ⥤ 𝒳} (β : P' ≅ P'₀) (E : 𝒳) (hpf : IsIso (pf.app E)) (hPF : IsIso PF) :
    IsIso (towerSectionsHom Γ Γ' r T T' Lp' P' K' pf PF β E) := by
  unfold towerSectionsHom sectionsHom
  infer_instance

section BaseChangeIso

variable {𝒳' : Type t₁} {𝒳'' : Type t₂} {𝒜' : Type t₃} {𝒜'' : Type t₄} {𝒳 : Type*}
  [Category.{w₁} 𝒳'] [Category.{w₂} 𝒳''] [Category.{w₃} 𝒜'] [Category.{w₄} 𝒜''] [Category 𝒳]
  {Lf' : 𝒜' ⥤ 𝒳'} {Γ' : 𝒳' ⥤ 𝒜'} {Lf'' : 𝒜'' ⥤ 𝒳''} {Γ'' : 𝒳'' ⥤ 𝒜''}
  {Lg : 𝒜' ⥤ 𝒜''} {Lh : 𝒳' ⥤ 𝒳''}

/-- `baseChangeTensor` is invertible when the base change map, `μ`, `γ` and `φ` are. -/
theorem isIso_baseChangeTensor (adjf' : Lf' ⊣ Γ') (adjf'' : Lf'' ⊣ Γ'')
    (e : Lg ⋙ Lf'' ≅ Lf' ⋙ Lh) (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳') (T'' : 𝒳'' ⥤ 𝒳'' ⥤ 𝒳'')
    (μ : Functor.uncurry.obj T' ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T'')
    {Lp' : 𝒳 ⥤ 𝒳'} {Lp₃ : 𝒳 ⥤ 𝒳''} (γ : Lp' ⋙ Lh ⟶ Lp₃) (E : 𝒳) {K' : 𝒳'} {K'' : 𝒳''}
    (φ : Lh.obj K' ⟶ K'')
    (hbc : IsIso (BaseChange.map adjf' adjf'' e (Iso.refl _) ((T'.obj (Lp'.obj E)).obj K')))
    (hμ : IsIso μ) (hγ : IsIso γ) (hφ : IsIso φ) :
    IsIso (baseChangeTensor adjf' adjf'' e T' T'' μ γ E φ) := by
  unfold baseChangeTensor
  infer_instance

end BaseChangeIso

end Stacks.CategoryTheory.TowerStep

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

section Spaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
  (g₃' : X'' ⟶ X) (hg' : g₂' ≫ g' = g₃')
  (K' : smallEtaleToposDerivedCategory X') (K'' : smallEtaleToposDerivedCategory X'')
  (φ : (smallEtaleDerivedModulePullback B S hS g₂').obj K' ⟶ K'')
  (E : smallEtaleToposDerivedCategory X)

/-- `tensorTowerSectionsHom` is invertible when the projection formula map is. -/
theorem isIso_tensorTowerSectionsHom
    (P : smallEtaleToposDerivedCategory X' ⥤ smallEtaleToposDerivedCategory X)
    (β : smallEtaleToposPushforward B S hS g' ≅ P)
    (hpf : IsIso (smallEtaleProjectionFormulaMapSnd g' E K')) :
    IsIso (tensorTowerSectionsHom B S hS g f f' g' w P β E K') :=
  Stacks.CategoryTheory.TowerStep.isIso_towerSectionsHom _ _ _ _ _ _ _ _ _ _ β E hpf
    inferInstance

/-- `transitionTensorSectionsBaseChange` is invertible when the base change map of `RΓ` at
`Lg'^*E ⊗^L K'` and `φ` are. -/
theorem isIso_transitionTensorSectionsBaseChange
    (hbc : IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g₂ f' f'' g₂' w₂
      (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')))
    (hφ : IsIso φ) :
    IsIso (transitionTensorSectionsBaseChange B S hS g₂ f' f'' g' g₂' w₂ g₃' hg' K' K'' φ E) :=
  Stacks.CategoryTheory.TowerStep.isIso_baseChangeTensor _ _ _ _ _ _ _ E φ hbc inferInstance
    inferInstance hφ

/-- **The base change comparison of `transitionTensorSectionsTranspose` is
`transitionTensorSectionsBaseChange`**, hence invertible when that is. -/
theorem isIso_derivedBaseChangeComparison_transitionTensorSectionsTranspose
    (h : IsIso (transitionTensorSectionsBaseChange B S hS g₂ f' f'' g' g₂' w₂ g₃' hg' K' K'' φ E)) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
      (representedAffineCommRingCatHom B S hS g₂).hom
      (transitionTensorSectionsTranspose B S hS g₂ f' f'' g' g₂' w₂ g₃' hg' K' K'' φ E)) := by
  rw [StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison_eq_adjunction_homEquiv_symm]
  change IsIso (((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₂).hom).homEquiv _ _).symm
    ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₂).hom).homEquiv _ _
      (transitionTensorSectionsBaseChange B S hS g₂ f' f'' g' g₂' w₂ g₃' hg' K' K'' φ E)))
  rw [Equiv.symm_apply_apply]
  exact h

end Spaces

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **`Γ(Spec A, 𝒪) = lim Γ(Spec Aₙ, 𝒪)`** for the tower of rings given by the transitions and
projections of the affine bases. -/
def isLimitStageSeqCone :
    IsLimit (StacksDraft.DerivedInverseLimit.seqCone
      (fun n ↦ representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n))
      (fun n ↦ representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n))
      D.stageRingHom_comp) := by
  let α :=
    NatTrans.ofOpSequence (F := Functor.ofOpSequence (X := fun n ↦ Γ((BigFppfOver.toScheme D.B
        (limitBase D.system) D.containsLimitBase).obj (baseObjectAt D.system D.B
          D.containsLimitBase D.containsBaseAt n), ⊤))
      (fun n ↦ representedAffineCommRingCatHom D.B
        (limitBase D.system) D.containsLimitBase (baseObjectTransition D.system D.B
          D.containsLimitBase D.containsBaseAt n)))
      (G := baseSectionsSystem D.system) (fun n ↦ 𝟙 ((baseSectionsSystem D.system).obj (op n)))
      fun n ↦ by
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  haveI : IsIso α := by
    have : ∀ n, IsIso (α.app n) := fun n ↦ by
      change IsIso (𝟙 _)
      infer_instance
    exact NatIso.isIso_of_isIso_app α
  refine (IsLimit.postcomposeHomEquiv (asIso α) _).1
    (IsLimit.ofIsoLimit (isLimitBaseSectionsCone D.system)
      (Cone.ext (Iso.refl _) fun n ↦ ?_))
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

variable (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)

/-- **`RΓ(X, E ⊗^L Rpₙ,* Kₙ) ≅ res Mₙ`**: `towerTensorSectionsHom` is invertible for `E` with
quasi-coherent cohomology (Stacks 08IN and the conjugate of the square). -/
theorem isIso_towerTensorSectionsHom
    (hE : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left E) (n : ℕ) :
    IsIso (D.towerTensorSectionsHom E n) :=
  isIso_tensorTowerSectionsHom D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip.w
    (D.K n) E (D.stagePushforward n) (D.stageToposDerivedPushforwardIso n)
    (D.isIso_stageProjectionFormula E n hE)

/-- **`Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ≅ Mₙ`** in the form of 0CQF: the base change comparison of the
transpose `Mₙ₊₁ ⟶ res Mₙ` is invertible, for `E` with quasi-coherent cohomology. -/
theorem isIso_derivedBaseChangeComparison_stageTensorSectionsTranspose
    (hE : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left E) (n : ℕ) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
      (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
      (D.stageTensorSectionsTranspose E n)) :=
  isIso_derivedBaseChangeComparison_transitionTensorSectionsTranspose D.B (limitBase D.system)
    D.containsLimitBase (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.isPullback_transitionSpace n).w
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.K (n + 1)) (D.K n) (D.φ n) E
    (isIso_transitionTensorSectionsBaseChange D.B (limitBase D.system) D.containsLimitBase
      (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (D.isPullback_transitionSpace n).w
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (D.K (n + 1)) (D.K n) (D.φ n) E
      (D.isIso_transitionSectionsBaseChange n (D.stageTensor E (n + 1))
        (qcohDerived_smallEtaleDerivedTensor _ _ _
          (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
            D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) E hE)
          (fun q => D.isQuasicoherentOnSite_homology_K (n + 1) q)))
      (D.φ_isIso n))

/-- **`Mₙ` is pseudo-coherent** for `E` perfect, in the spelling of `towerTensorSectionsHom`. -/
theorem isPseudoCoherent_stageTensorSections (hpc : D.StageSectionsPseudoCoherent)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) (n : ℕ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
        (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
          (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj E)).obj
          (D.K n))) :=
  hpc E hE n

/-- **[Stacks, Tag 0CQF] applied to the tower `RΓ(X, E ⊗^L Rpₙ,* Kₙ)`.** For `E` perfect, let
`(Yₙ, sₙ)` be a tower of `D(A)` with isomorphisms `eₙ : Yₙ ⟶ res Mₙ` carrying `sₙ` to the
restricted transposes of `Mₙ₊₁ ⊗^L Aₙ ⟶ Mₙ`, and `M` a derived limit of `(Yₙ, sₙ)` with
structure map `p`. Then `M` is pseudo-coherent, and the map `M ⊗^L_A Aₙ ⟶ Mₙ` adjoint to
`p ≫ πₙ ≫ eₙ` is an isomorphism. -/
theorem isPseudoCoherent_and_isIso_of_distTriang (hpc : D.StageSectionsPseudoCoherent)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (Y : ℕ → DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme D.B (limitBase D.system)
      D.containsLimitBase).obj (limitBaseObject D.system D.B D.containsLimitBase), ⊤)))
    (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (e : ∀ n : ℕ, Y n ⟶
      (ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B (limitBase D.system)
        D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
          D.containsBaseAt n)).hom).mapDerivedCategory.obj
        ((affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
            (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
            ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                E)).obj (D.K n))))
    [he' : ∀ n : ℕ, IsIso (e n)]
    (he : ∀ n : ℕ, s n ≫ e n = e (n + 1) ≫
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
              ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
                (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                  E)).obj (D.K n)))))
    [HasProduct Y]
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme D.B (limitBase D.system)
      D.containsLimitBase).obj (limitBaseObject D.system D.B D.containsLimitBase), ⊤)))
    (p : M ⟶ ∏ᶜ Y) (δ : ∏ᶜ Y ⟶ M⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈
      distTriang _) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧ ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
        (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
        (p ≫ Pi.π Y n ≫ e n)) := by
  have hq := qcohDerived_of_isPerfect _ _ _ _ _ hE
  exact StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso_of_seq
    (R := fun n ↦ Γ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n), ⊤))
    (fun n ↦ representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
      (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n))
    (fun n ↦ representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n))
    D.stageRingHom_comp D.isLimitStageSeqCone
    (fun n ↦ (affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
        (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
          (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj E)).obj
          (D.K n)))
    (fun n ↦ D.stageTensorSectionsTranspose E n)
    (fun n ↦ surjective_baseSectionsSystem_map D.system (homOfLE (Nat.le_succ n)).op
      (D.transition_surjective n))
    (fun n ↦ isLocallyNilpotent_ker_baseSectionsSystem_map D.system (homOfLE (Nat.le_succ n)).op
      (D.transition_locallyNilpotent n))
    (fun n ↦ D.isPseudoCoherent_stageTensorSections E hpc hE n)
    (fun n ↦ D.isIso_derivedBaseChangeComparison_stageTensorSectionsTranspose E hq n)
    Y s e (he' := he') he M p δ hT

/-- **The tower `RΓ(X, E ⊗^L Rpₙ,* Kₙ)` is carried to the restricted tower `(Mₙ)`**: Stacks 0DIM's
compatibility, with the transitions `RΓ(X, E ⊗^L -)` of those of `(Rpₙ,* Kₙ)`. -/
theorem limitTensorSections_map_towerTensorSectionsHom (n : ℕ) :
    (D.limitTensorSections E).map (D.spaceTower.map (homOfLE (Nat.le_succ n)).op) ≫
        D.towerTensorSectionsHom E n =
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
                ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
                  (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                    E)).obj (D.K n)))) := by
  have h : D.spaceTower.map (homOfLE (Nat.le_succ n)).op = D.towerMap n :=
    D.pushforwardTower_map_succ n
  rw [h]
  exact D.tensorSections_towerStep E n

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/- `D_QCoh(𝒪_X)` and its triangulated structure are read at the standard model, with the
instances of `DerivedExistencePseudoCoherent`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **[Stacks, Tag 0DIM], first half, for every derived limit in `D_QCoh(𝒪_X)`.** In Situation
0DIK, for every derived limit `K` of the tower `(Rpₙ,* Kₙ)` in `D_QCoh(𝒪_X)` and every perfect `E`,
`RΓ(X, E ⊗^L K)` is pseudo-coherent in `D(A)`. -/
theorem isPseudoCoherent_limitTensorSections_of_isDerivedLimit
    (hpc : D.StageSectionsPseudoCoherent)
    (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
    (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory)
    (hK : IsDerivedLimit D.quasicoherentTower K)
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((D.limitTensorSections E).obj
        ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
          D.X.left).ι.obj K)) := by
  let hT : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
      E).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).commShift_right E
  have hTtri : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      D.X.left).obj E).IsTriangulated :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).exact_right E
  let hι : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).ι.CommShift ℤ := inferInstance
  let hRf : (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      D.X.hom).CommShift ℤ := inferInstance
  let hRΓ : (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).CommShift ℤ := inferInstance
  let h₁ : D.limitSectionsFunctor.CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase D.system)
        D.containsLimitBase D.X.hom) (representedAffineDerivedSections D.B (limitBase D.system)
        D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) ℤ _ _ _ _ hRf hRΓ
  have : D.limitSectionsFunctor.IsTriangulated := ⟨fun Tr hTr ↦ isomorphic_distinguished _
    ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).map_distinguished _
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          D.X.hom).map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase
          D.system) D.containsLimitBase D.X.hom) hRf (representedAffineDerivedSections D.B
          (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) hRΓ).app Tr)⟩
  let h₂ : (D.limitTensorSections E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase D.system)
        D.containsLimitBase D.X.left).obj E) D.limitSectionsFunctor ℤ _ _ _ _ hT h₁
  have : (D.limitTensorSections E).IsTriangulated := ⟨fun Tr hTr ↦ isomorphic_distinguished _
    (D.limitSectionsFunctor.map_distinguished _ (hTtri.map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase
          D.system) D.containsLimitBase D.X.left).obj E) hT D.limitSectionsFunctor h₁).app Tr)⟩
  let : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (spaceQuasicoherentProp D.B (limitBase D.system)
        D.containsLimitBase D.X.left).ι (D.limitTensorSections E) ℤ _ _ _ _ hι h₂
  have : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).IsTriangulated := ⟨fun Tr hTr ↦
    isomorphic_distinguished _
      ((D.limitTensorSections E).map_distinguished _ ((spaceQuasicoherentProp D.B (limitBase
          D.system) D.containsLimitBase D.X.left).ι.map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ (spaceQuasicoherentProp D.B (limitBase
          D.system) D.containsLimitBase D.X.left).ι hι (D.limitTensorSections E) h₂).app Tr)⟩
  have : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).IsRightAdjoint := (Adjunction.liftLeftAdjoint
    (P := spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (D.limitTensorSectionsAdjunction E hE)
    (D.qcohDerived_limitTensorSections_leftAdjoint_obj E hE)).isRightAdjoint
  obtain ⟨h, p, δ, hT⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E)
    D.quasicoherentTower K hK
  have hq := qcohDerived_of_isPerfect _ _ _ _ _ hE
  exact (D.isPseudoCoherent_and_isIso_of_distTriang E hpc hE
    (fun n ↦ (D.quasicoherentTower ⋙ ((spaceQuasicoherentProp D.B (limitBase D.system)
        D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E)).obj ⟨n⟩)
    (fun n ↦ (D.quasicoherentTower ⋙ ((spaceQuasicoherentProp D.B (limitBase D.system)
        D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E)).map (homOfLE (Nat.le_succ n)).op)
    (fun n ↦ D.towerTensorSectionsHom E n) (he' := fun n ↦ D.isIso_towerTensorSectionsHom E hq n)
    (fun n ↦ D.limitTensorSections_map_towerTensorSectionsHom E n) (((spaceQuasicoherentProp D.B
        (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).obj K) p δ hT).1


end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
