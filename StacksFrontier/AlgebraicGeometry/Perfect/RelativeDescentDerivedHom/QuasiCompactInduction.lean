module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom.RestrictToSmaller

/-!
# Derived morphism sets along a relative descent situation: the quasi-compact induction

This file contains the third part of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom`: derived pullback along an
isomorphism, the restriction of a relative descent situation to the whole fixed stage
(`HomDescent` follows from `RestrictHomDescent` for `⊤`), and the induction over the
quasi-compact opens of the fixed stage reducing `HomDescent` to affine opens and the
Mayer--Vietoris union step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Cohomology.DerivedPushforwardAssociativity (derivedPullbackCompIsoCanonical_assoc
  derivedPullbackIdIso derivedPullbackCompIsoCanonical_id_comp)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.DerivedPullback

/-! ### Derived pullback along an isomorphism -/

section IsoRingedSpaces

variable {X Y : RingedSpace.{u, u}}

/-- Derived pullback along an isomorphism of ringed spaces is an equivalence. -/
theorem isEquivalence_derivedPullback (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X)
    (hgf : g ≫ f = 𝟙 Y) : (derivedPullback f).IsEquivalence :=
  Functor.IsEquivalence.mk' (derivedPullback g)
    (factorIso g f (𝟙 Y) hgf ≪≫ derivedPullbackIdIso Y).symm
    (factorIso f g (𝟙 X) hfg ≪≫ derivedPullbackIdIso X)

/-- Derived pullback along an isomorphism of ringed spaces is bijective on derived morphism
sets. -/
theorem bijective_derivedPullback_map (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X)
    (hgf : g ≫ f = 𝟙 Y) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    Function.Bijective ((derivedPullback f).map :
      (K ⟶ L) → ((derivedPullback f).obj K ⟶ (derivedPullback f).obj L)) := by
  have := isEquivalence_derivedPullback f g hfg hgf
  exact ⟨(derivedPullback f).map_injective, (derivedPullback f).map_surjective⟩

end IsoRingedSpaces

section IsoSchemes

variable {V W Y Z : Scheme.{u}}

/-- The map on derived Hom of a commutative square of schemes whose vertical edge is an isomorphism
is bijective. -/
theorem bijective_schemeFactorSquareHom (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z)
    (h : r ≫ g = e ≫ ι) (r' : W ⟶ V) (hrr' : r ≫ r' = 𝟙 V) (hr'r : r' ≫ r = 𝟙 W)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    Function.Bijective (schemeFactorSquareHom r g e ι h K L) := by
  have key : schemeFactorSquareHom r g e ι h K L =
      (Iso.homCongr ((schemeFactorSquareIso r g e ι h).app K).symm
          ((schemeFactorSquareIso r g e ι h).app L).symm) ∘
        (derivedPullback r.toLRSHom.toShHom).map :=
    funext (schemeFactorSquareHom_eq r g e ι h K L)
  rw [key]
  exact (Equiv.bijective _).comp
    (bijective_derivedPullback_map r.toLRSHom.toShHom r'.toLRSHom.toShHom
      (congrArg (fun m : V ⟶ V ↦ m.toLRSHom.toShHom) hrr')
      (congrArg (fun m : W ⟶ W ↦ m.toLRSHom.toShHom) hr'r) _ _)

end IsoSchemes

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
variable (hT : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left))

/-! ### Restriction to the whole of the fixed stage -/

/-- The inverse of the inclusion `Uᵢ ⟶ Xᵢ` for `U₀ = X₀`: the base change along `f_{i0}` of the
inverse of the isomorphism `⊤ ≅ X₀`. -/
def restrictTopToAmbientInv (i : D.LaterIndex) :
    D.schemeAt i ⟶ (D.restrict ⊤ hT).schemeAt i :=
  pullback.lift (D.toFixedStage i ≫ D.X₀.left.topIso.inv)
    (pullback.snd D.X₀.hom (D.baseMap i))
    (by
      change (D.toFixedStage i ≫ D.X₀.left.topIso.inv) ≫
          (⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom =
        pullback.snd D.X₀.hom (D.baseMap i) ≫ D.baseMap i
      rw [Category.assoc, Scheme.toIso_inv_ι_assoc]
      exact pullback.condition)

/-- The inverse of `Uᵢ ⟶ Xᵢ` for `U₀ = X₀` lies over the inverse of `⊤ ≅ X₀`. -/
theorem restrictTopToAmbientInv_comp_toFixedStage (i : D.LaterIndex) :
    D.restrictTopToAmbientInv hT i ≫ (D.restrict ⊤ hT).toFixedStage i =
      D.toFixedStage i ≫ D.X₀.left.topIso.inv :=
  pullback.lift_fst _ _ _

/-- The inverse of `Uᵢ ⟶ Xᵢ` for `U₀ = X₀` is a morphism over `Sᵢ`. -/
theorem restrictTopToAmbientInv_comp_snd (i : D.LaterIndex) :
    D.restrictTopToAmbientInv hT i ≫
        pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom) (D.baseMap i) =
      pullback.snd D.X₀.hom (D.baseMap i) :=
  pullback.lift_snd _ _ _

/-- For `U₀ = X₀`, the inclusion `Uᵢ ⟶ Xᵢ` composed with `restrictTopToAmbientInv` is `𝟙`. -/
theorem restrictToAmbient_comp_restrictTopToAmbientInv (i : D.LaterIndex) :
    D.restrictToAmbient ⊤ hT i ≫ D.restrictTopToAmbientInv hT i =
      𝟙 ((D.restrict ⊤ hT).schemeAt i) := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictTopToAmbientInv_comp_toFixedStage hT i, ← Category.assoc,
      D.restrictToAmbient_comp_toFixedStage ⊤ hT i, Category.assoc, Scheme.ι_toIso_inv,
      Category.id_comp]
    exact Category.comp_id _
  · change _ ≫ pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom) (D.baseMap i) =
      _ ≫ pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom) (D.baseMap i)
    rw [Category.assoc, D.restrictTopToAmbientInv_comp_snd hT i,
      D.restrictToAmbient_comp_snd ⊤ hT i, Category.id_comp]

/-- For `U₀ = X₀`, `restrictTopToAmbientInv` composed with the inclusion `Uᵢ ⟶ Xᵢ` is `𝟙`. -/
theorem restrictTopToAmbientInv_comp_restrictToAmbient (i : D.LaterIndex) :
    D.restrictTopToAmbientInv hT i ≫ D.restrictToAmbient ⊤ hT i = 𝟙 (D.schemeAt i) := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbient_comp_toFixedStage ⊤ hT i, ← Category.assoc,
      D.restrictTopToAmbientInv_comp_toFixedStage hT i, Category.assoc, Scheme.toIso_inv_ι,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, D.restrictToAmbient_comp_snd ⊤ hT i,
      D.restrictTopToAmbientInv_comp_snd hT i, Category.id_comp]

/-- The inverse of the inclusion `U ⟶ X` for `U₀ = X₀`: the base change along `f₀` of the
inverse of the isomorphism `⊤ ≅ X₀`. -/
def restrictTopToAmbientLimitInv : D.limitScheme ⟶ (D.restrict ⊤ hT).limitScheme :=
  pullback.lift (D.limitToFixedStage ≫ D.X₀.left.topIso.inv)
    (pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)))
    (by
      change (D.limitToFixedStage ≫ D.X₀.left.topIso.inv) ≫
          (⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom =
        pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) ≫
          D.descent.limitCone.π.app (op D.descent.base)
      rw [Category.assoc, Scheme.toIso_inv_ι_assoc]
      exact pullback.condition)

/-- The inverse of `U ⟶ X` for `U₀ = X₀` lies over the inverse of `⊤ ≅ X₀`. -/
theorem restrictTopToAmbientLimitInv_comp_limitToFixedStage :
    D.restrictTopToAmbientLimitInv hT ≫ (D.restrict ⊤ hT).limitToFixedStage =
      D.limitToFixedStage ≫ D.X₀.left.topIso.inv :=
  pullback.lift_fst _ _ _

/-- The inverse of `U ⟶ X` for `U₀ = X₀` is a morphism over `S`. -/
theorem restrictTopToAmbientLimitInv_comp_snd :
    D.restrictTopToAmbientLimitInv hT ≫
        pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom)
          (D.descent.limitCone.π.app (op D.descent.base)) =
      pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) :=
  pullback.lift_snd _ _ _

/-- For `U₀ = X₀`, the inclusion `U ⟶ X` composed with `restrictTopToAmbientLimitInv` is `𝟙`. -/
theorem restrictToAmbientLimit_comp_restrictTopToAmbientLimitInv :
    D.restrictToAmbientLimit ⊤ hT ≫ D.restrictTopToAmbientLimitInv hT =
      𝟙 ((D.restrict ⊤ hT).limitScheme) := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictTopToAmbientLimitInv_comp_limitToFixedStage hT,
      ← Category.assoc, D.restrictToAmbientLimit_comp_limitToFixedStage ⊤ hT, Category.assoc,
      Scheme.ι_toIso_inv, Category.id_comp]
    exact Category.comp_id _
  · change _ ≫ pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom)
          (D.descent.limitCone.π.app (op D.descent.base)) =
      _ ≫ pullback.snd ((⊤ : D.X₀.left.Opens).ι ≫ D.X₀.hom)
          (D.descent.limitCone.π.app (op D.descent.base))
    rw [Category.assoc, D.restrictTopToAmbientLimitInv_comp_snd hT,
      D.restrictToAmbientLimit_comp_snd ⊤ hT, Category.id_comp]

/-- For `U₀ = X₀`, `restrictTopToAmbientLimitInv` composed with the inclusion `U ⟶ X` is `𝟙`. -/
theorem restrictTopToAmbientLimitInv_comp_restrictToAmbientLimit :
    D.restrictTopToAmbientLimitInv hT ≫ D.restrictToAmbientLimit ⊤ hT =
      𝟙 D.limitScheme := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbientLimit_comp_limitToFixedStage ⊤ hT, ← Category.assoc,
      D.restrictTopToAmbientLimitInv_comp_limitToFixedStage hT, Category.assoc,
      Scheme.toIso_inv_ι, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, D.restrictToAmbientLimit_comp_snd ⊤ hT,
      D.restrictTopToAmbientLimitInv_comp_snd hT, Category.id_comp]

/-- Restriction to `U₀ = X₀` is bijective on derived morphism sets at a stage. -/
theorem bijective_homRestrictToOpen_top (i : D.LaterIndex) :
    Function.Bijective (D.homRestrictToOpen K₀ L₀ ⊤ hT i) :=
  Stacks.DerivedPullback.bijective_schemeFactorSquareHom (D.restrictToAmbient ⊤ hT i)
    (D.toFixedStage i) ((D.restrict ⊤ hT).toFixedStage i) (⊤ : D.X₀.left.Opens).ι
    (D.restrictToAmbient_comp_toFixedStage ⊤ hT i) (D.restrictTopToAmbientInv hT i)
    (D.restrictToAmbient_comp_restrictTopToAmbientInv hT i)
    (D.restrictTopToAmbientInv_comp_restrictToAmbient hT i) K₀ L₀

/-- Restriction to `U₀ = X₀` is bijective on derived morphism sets at the limit. -/
theorem bijective_homRestrictToOpenLimit_top :
    Function.Bijective (D.homRestrictToOpenLimit K₀ L₀ ⊤ hT) :=
  Stacks.DerivedPullback.bijective_schemeFactorSquareHom (D.restrictToAmbientLimit ⊤ hT)
    D.limitToFixedStage (D.restrict ⊤ hT).limitToFixedStage (⊤ : D.X₀.left.Opens).ι
    (D.restrictToAmbientLimit_comp_limitToFixedStage ⊤ hT) (D.restrictTopToAmbientLimitInv hT)
    (D.restrictToAmbientLimit_comp_restrictTopToAmbientLimitInv hT)
    (D.restrictTopToAmbientLimitInv_comp_restrictToAmbientLimit hT) K₀ L₀

/-- `HomDescent` follows from `RestrictHomDescent` for `U₀ = X₀`. -/
theorem homDescent_of_restrictHomDescent_top (h : D.RestrictHomDescent K₀ L₀ ⊤ hT) :
    D.HomDescent K₀ L₀ := by
  obtain ⟨hs, hi⟩ := h
  constructor
  · intro ψ
    obtain ⟨i, φ', hφ'⟩ := hs (D.homRestrictToOpenLimit K₀ L₀ ⊤ hT ψ)
    obtain ⟨φ, hφ⟩ := (D.bijective_homRestrictToOpen_top K₀ L₀ hT i).surjective φ'
    rw [← hφ] at hφ'
    exact ⟨i, φ, (D.bijective_homRestrictToOpenLimit_top K₀ L₀ hT).injective
      ((D.homComparison_homRestrictToOpen K₀ L₀ ⊤ hT i φ).symm.trans hφ')⟩
  · intro i φ φ' hφ
    obtain ⟨j, hij, hj⟩ := hi i (D.homRestrictToOpen K₀ L₀ ⊤ hT i φ)
      (D.homRestrictToOpen K₀ L₀ ⊤ hT i φ')
      ((D.homComparison_homRestrictToOpen K₀ L₀ ⊤ hT i φ).trans
        ((congrArg (D.homRestrictToOpenLimit K₀ L₀ ⊤ hT) hφ).trans
          (D.homComparison_homRestrictToOpen K₀ L₀ ⊤ hT i φ').symm))
    exact ⟨j, hij, (D.bijective_homRestrictToOpen_top K₀ L₀ hT j).injective
      ((D.homTransition_homRestrictToOpen K₀ L₀ ⊤ hT hij φ).symm.trans
        (hj.trans (D.homTransition_homRestrictToOpen K₀ L₀ ⊤ hT hij φ')))⟩

/-! ### The induction over the quasi-compact opens of the fixed stage -/

/-- If `RestrictHomDescent` holds for every affine open of `X₀`, and holds for `U₀ ⊔ V₀` whenever
it holds for a quasi-compact `U₀`, an affine `V₀` and `U₀ ⊓ V₀`, then it holds for every
quasi-compact open of `X₀`. -/
theorem restrictHomDescent_of_isAffineOpen_of_sup
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictHomDescent K₀ L₀ U₀ hU₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact →
        D.RestrictHomDescent K₀ L₀ (U₀ ⊓ V₀) hinf →
          D.RestrictHomDescent K₀ L₀ (U₀ ⊔ V₀) hsupc)
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) :
    D.RestrictHomDescent K₀ L₀ U₀ hU₀ := by
  have : QuasiSeparated D.X₀.hom := D.finitePresentation.quasiSeparated
  have : QuasiSeparatedSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiSeparated D.descent.base
  have : QuasiSeparatedSpace D.X₀.left := quasiSeparatedSpace_of_quasiSeparated D.X₀.hom
  refine _root_.Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact
    (P := fun W ↦ ∀ h : IsCompact (W : Set D.X₀.left), D.RestrictHomDescent K₀ L₀ W h)
    (fun W hW _ ↦ haffine W hW) ?_ U₀ hU₀ hU₀
  intro W V hW hV hPW hPV hPinf hsupc
  have hinf : IsCompact ((W ⊓ V : D.X₀.left.Opens) : Set D.X₀.left) :=
    QuasiSeparatedSpace.inter_isCompact (W : Set D.X₀.left) (V : Set D.X₀.left) W.isOpen hW
      V.isOpen hV.isCompact
  exact hsup W V hW hV hinf hsupc (hPW hW) (hPV hV.isCompact) (hPinf hinf)

/-- If `RestrictHomDescent` holds for every affine open of `X₀` and is stable under the
Mayer--Vietoris union step `U₀, V₀, U₀ ⊓ V₀ ⊢ U₀ ⊔ V₀`, then `HomDescent` holds. -/
theorem homDescent_of_isAffineOpen_of_sup
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictHomDescent K₀ L₀ U₀ hU₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact →
        D.RestrictHomDescent K₀ L₀ (U₀ ⊓ V₀) hinf →
          D.RestrictHomDescent K₀ L₀ (U₀ ⊔ V₀) hsupc) :
    D.HomDescent K₀ L₀ := by
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiCompact D.descent.base
  have : CompactSpace D.X₀.left := QuasiCompact.compactSpace_of_compactSpace D.X₀.hom
  have hTop : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  exact D.homDescent_of_restrictHomDescent_top K₀ L₀ hTop
    (D.restrictHomDescent_of_isAffineOpen_of_sup K₀ L₀ haffine hsup ⊤ hTop)

end AlgebraicGeometry.RelativeDescentSituation

end
