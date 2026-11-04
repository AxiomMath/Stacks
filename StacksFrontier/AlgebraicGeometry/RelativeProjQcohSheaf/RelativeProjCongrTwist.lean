module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrProjMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual

/-!
# Serre twists along the isomorphism of relative Proj induced by an isomorphism of algebras

Let `Y` be a scheme and `Φ : 𝒜₁ ⟶ 𝒜₂` a unital homomorphism of quasi-coherent graded
`𝒪_Y`-algebras all of whose components are isomorphisms, and let
`e = ...RelativeProjQcohSheaf.relativeProjCongr Φ : Proj_Y(𝒜₁) ≅ Proj_Y(𝒜₂)` be the induced
isomorphism. This file shows that the twists of Tag 01NR are natural in `Φ`: the inverse image
along `e` of `⨁_{n ∈ ℤ} 𝒪_{Proj_Y(𝒜₂)}(n)` is isomorphic, as a sheaf of `ℤ`-graded algebras, to
`⨁_{n ∈ ℤ} 𝒪_{Proj_Y(𝒜₁)}(n)` (`...RelativeProjQcohSheaf.congrTwistIso`), and the isomorphism
carries `Φ` followed by the inverse image of `ψ : 𝒜₂ ⟶ ⨁_{n ≥ 0} π_*𝒪(n)` to `ψ` for `𝒜₁`
(`...RelativeProjQcohSheaf.congrPsi_comp_congrTwistIso`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.congrTwistHom`: the map of Serre twists along
  `relativeProjCongr Φ`, as a map of sheaves of graded algebras.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.congrTwistIso`: **the isomorphism
  `e^*(⨁_n 𝒪_{Proj_Y(𝒜₂)}(n)) ≅ ⨁_n 𝒪_{Proj_Y(𝒜₁)}(n)` of sheaves of graded algebras.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.congrPsi`: `Φ`, followed by `ψ` for `𝒜₂` and the
  inverse image along `e`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.congrPsi_comp_congrTwistIso`: **the isomorphism
  carries `congrPsi` to `ψ` for `𝒜₁`**, in every degree `n ≥ 0`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)
open Stacks.AlgebraicGeometry.Tag07ZGTwist (twistAlgebra relativeTwist)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp hom_app_map map_map_homOfLE)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [-instance] CategoryTheory.catToReflQuiver

section Congr

variable {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- The components of the map of Serre twists along Tag 07ZG's morphism for `Φ⁻¹` are
isomorphisms (Tag 07ZJ). -/
theorem isIso_projTwistHom_congrInvHom_app (n : ℤ) :
    IsIso ((ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ)
      (eventually_isIso_congrInvHom Φ hΦ)).app n) := by
  have := Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso (congrInvHom Φ hΦ)
    (eventually_isIso_congrInvHom Φ hΦ) n
  rw [ProjectiveDeformation.projTwistHom, ProjectiveDeformation.projTwistHomOf_app]
  exact IsIso.comp_isIso' (Iso.isIso_inv ((Scheme.Modules.pullbackComp _ _).app _))
    (IsIso.comp_isIso' (Functor.map_isIso _ _)
      (IsIso.comp_isIso' (Iso.isIso_hom ((Scheme.Modules.pullbackComp _ _).app _))
        (IsIso.comp_isIso' (Iso.isIso_hom ((Scheme.Modules.pullbackCongr _).app _))
          (Iso.isIso_hom ((Scheme.Modules.pullbackId _).app _)))))

/-- **The map of Serre twists along `relativeProjCongr Φ`**: the identification of
`relativeProjCongr Φ` with Tag 07ZG's morphism for `Φ⁻¹`, followed by the map of Serre twists of
Tag 07ZJ along that morphism, as a map of sheaves of `ℤ`-graded algebras. -/
def congrTwistHom :
    Stacks.Conormal.gradedPullback (relativeProjCongr Φ hΦ).hom (twistAlgebra A₂) ⟶
      twistAlgebra A₁ :=
  (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso (twistAlgebra A₂)
      (relativeProjCongr_hom_eq Φ hΦ)).hom ≫
    ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ) (eventually_isIso_congrInvHom Φ hΦ)

/-- The degree-`n` component of `congrTwistHom`. -/
theorem congrTwistHom_app (n : ℤ) :
    (congrTwistHom Φ hΦ).app n =
      (Scheme.Modules.pullbackCongr (relativeProjCongr_hom_eq Φ hΦ)).hom.app (relativeTwist A₂ n)
        ≫ (ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ)).app n :=
  rfl

/-- The components of `congrTwistHom` are isomorphisms. -/
theorem isIso_congrTwistHom_app (n : ℤ) : IsIso ((congrTwistHom Φ hΦ).app n) := by
  rw [congrTwistHom_app]
  exact IsIso.comp_isIso' (Iso.isIso_hom ((Scheme.Modules.pullbackCongr _).app _))
    (isIso_projTwistHom_congrInvHom_app Φ hΦ n)

/-- **The Serre twists are natural in isomorphisms of graded algebras**: the inverse image along
`relativeProjCongr Φ : Proj_Y(𝒜₁) ≅ Proj_Y(𝒜₂)` of `⨁_{n ∈ ℤ} 𝒪_{Proj_Y(𝒜₂)}(n)` is isomorphic,
as a sheaf of `ℤ`-graded algebras, to `⨁_{n ∈ ℤ} 𝒪_{Proj_Y(𝒜₁)}(n)`. -/
def congrTwistIso :
    pbAlgS (relativeProjCongr Φ hΦ).hom (twistAlgebra A₂) ≅ twistAlgebra A₁ :=
  SheafOfModules.GradedAlgebra.isoOfIsIsoApp (congrTwistHom Φ hΦ) (isIso_congrTwistHom_app Φ hΦ)

/-- The degree-`n` component of `congrTwistIso`. -/
theorem congrTwistIso_hom_app (n : ℤ) :
    (congrTwistIso Φ hΦ).hom.app n = (congrTwistHom Φ hΦ).app n :=
  rfl

/-- **The homogeneous-section map of the pulled-back twists**: `Φ`, followed by Tag 01NR's `ψ` for
`𝒜₂` and the inverse image along `relativeProjCongr Φ`, which lies over the base. -/
def congrPsi (n : ℕ) :
    A₁.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A₁).toBase).obj
      ((pbAlgS (relativeProjCongr Φ hΦ).hom (twistAlgebra A₂)).piece (n : ℤ)) :=
  (congrHom Φ).app (n : ℤ) ≫ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₂).ψ n ≫
    (Scheme.Modules.pushforward (relativeProj A₂).toBase).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjCongr Φ hΦ).hom).unit.app
        (relativeTwist A₂ n)) ≫
    (Scheme.Modules.pushforwardComp (relativeProjCongr Φ hΦ).hom
      (relativeProj A₂).toBase).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (relativeProjCongr_hom_comp_toBase Φ hΦ)).hom.app _

/-- `congrPsi` on sections: the restriction of the inverse image of `ψ(Φ(a))`. -/
theorem congrPsi_app (n : ℕ) (V : Y.Opens) (a : Γ(A₁.piece (n : ℤ), V))
    (hW : (relativeProj A₁).toBase ⁻¹ᵁ V ≤
      (relativeProjCongr Φ hΦ).hom ⁻¹ᵁ ((relativeProj A₂).toBase ⁻¹ᵁ V)) :
    (congrPsi Φ hΦ n).app V a =
      ((Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).obj (relativeTwist A₂ n)).presheaf.map
        (homOfLE hW).op
        (unitApp (relativeProjCongr Φ hΦ).hom (relativeTwist A₂ n)
          ((relativeProj A₂).toBase ⁻¹ᵁ V) (psiU A₂ n V (((congrHom Φ).app (n : ℤ)).app V a))) := by
  refine Eq.trans (b := ((Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).obj
      (relativeTwist A₂ n)).presheaf.map
        (eqToHom (congrArg (fun φ => φ ⁻¹ᵁ V)
          (relativeProjCongr_hom_comp_toBase Φ hΦ)).symm).op
        (unitApp (relativeProjCongr Φ hΦ).hom (relativeTwist A₂ n)
          ((relativeProj A₂).toBase ⁻¹ᵁ V) (psiU A₂ n V (((congrHom Φ).app (n : ℤ)).app V a))))
    rfl ?_
  exact congrArg (fun r => ((Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).obj
      (relativeTwist A₂ n)).presheaf.map r _) (Subsingleton.elim _ _)

/-- **A transport along an equality of morphisms followed by a map, on a restricted inverse image
of a section.** -/
theorem pullbackCongr_comp_app_map_unitApp {X Z : Scheme.{u}} {r C : X ⟶ Z} (hC : r = C)
    (M : Z.Modules) {N : X.Modules} (θ : (Scheme.Modules.pullback C).obj M ⟶ N)
    (φ : (Scheme.Modules.pullback r).obj M ⟶ N)
    (hφ : φ = (Scheme.Modules.pullbackCongr hC).hom.app M ≫ θ) (O : Z.Opens) {W : X.Opens}
    (hW : W ≤ r ⁻¹ᵁ O) (hW' : W ≤ C ⁻¹ᵁ O) (s : Γ(M, O)) :
    φ.app W (((Scheme.Modules.pullback r).obj M).presheaf.map (homOfLE hW).op
        (unitApp r M O s)) =
      N.presheaf.map (homOfLE hW').op (θ.app (C ⁻¹ᵁ O) (unitApp C M O s)) := by
  subst hC hφ
  rw [hom_app_map, Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply,
    Stacks.AlgebraicGeometry.TwistMulLeg.pullbackCongr_hom_app_unitApp rfl, hom_app_map,
    map_map_homOfLE]

/-- On sections over `V`, `congrTwistIso` carries `congrPsi` of `a` to the section of
`𝒪_{Proj_Y(𝒜₁)}(n)` attached to `a`. -/
theorem congrTwistIso_app_congrPsi_app (n : ℕ) (V : Y.Opens) (a : Γ(A₁.piece (n : ℤ), V)) :
    Scheme.Modules.Hom.app
        (M := (Scheme.Modules.pullback (relativeProjCongr Φ hΦ).hom).obj (relativeTwist A₂ n))
        (N := relativeTwist A₁ n) ((congrTwistIso Φ hΦ).hom.app (n : ℤ))
        ((relativeProj A₁).toBase ⁻¹ᵁ V) ((congrPsi Φ hΦ n).app V a) = psiU A₁ n V a := by
  rw [congrPsi_app Φ hΦ n V a (by rw [← Scheme.Hom.comp_preimage,
    relativeProjCongr_hom_comp_toBase])]
  have hinv : ((congrInvHom Φ hΦ).app (n : ℤ)).app V (((congrHom Φ).app (n : ℤ)).app V a) = a :=
    val_app_roundtrip (Φ.app (n : ℤ)) (@inv _ _ _ _ (Φ.app (n : ℤ)) (hΦ n))
      (@IsIso.hom_inv_id _ _ _ _ (Φ.app (n : ℤ)) (hΦ n)) (op V) a
  have hpsi : Scheme.Modules.Hom.app
      (M := (Scheme.Modules.pullback (ProjectiveDeformation.projMapOfEventuallyIso
        (congrInvHom Φ hΦ) (eventually_isIso_congrInvHom Φ hΦ))).obj (relativeTwist A₂ n))
      (N := relativeTwist A₁ n)
      ((ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ)
        (eventually_isIso_congrInvHom Φ hΦ)).app (n : ℤ))
      (ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
        (eventually_isIso_congrInvHom Φ hΦ) ⁻¹ᵁ ((relativeProj A₂).toBase ⁻¹ᵁ V))
      (unitApp (ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
        (eventually_isIso_congrInvHom Φ hΦ)) (relativeTwist A₂ n)
        ((relativeProj A₂).toBase ⁻¹ᵁ V) (psiU A₂ n V (((congrHom Φ).app (n : ℤ)).app V a))) =
      (relativeTwist A₁ n).presheaf.map
        (homOfLE (ProjectiveDeformation.projMapOfEventuallyIso_preimage_toBase_le _ _ V)).op
        (psiU A₁ n V (((congrInvHom Φ hΦ).app (n : ℤ)).app V
          (((congrHom Φ).app (n : ℤ)).app V a))) := by
    rw [ProjectiveDeformation.projTwistHom, ProjectiveDeformation.projTwistHomOf_app]
    exact GradedAlgebraHomSections.retract_chase _ (Tag07ZGMorphism.relativeMapHom _)
      (congrInvHom Φ hΦ).relativeMapDomain.ι
      (ProjectiveDeformation.projRetract_comp_ι _ (eventually_isIso_congrInvHom Φ hΦ))
      (Tag07ZGTwist.relativeTwistMap (congrInvHom Φ hΦ) n) ((relativeProj A₂).toBase ⁻¹ᵁ V)
      ((relativeProj A₁).toBase ⁻¹ᵁ V)
      (Tag07ZGTwist.relativeMapHom_preimage_toBase (congrInvHom Φ hΦ) V).le
      (psiU A₂ n V (((congrHom Φ).app (n : ℤ)).app V a))
      (psiU A₁ n V (((congrInvHom Φ hΦ).app (n : ℤ)).app V
        (((congrHom Φ).app (n : ℤ)).app V a)))
      (Tag07ZGTwist.relativeTwistMap_unitApp_psiU (congrInvHom Φ hΦ) n V _)
      (ProjectiveDeformation.projMapOfEventuallyIso_preimage_toBase_le _ _ V)
  rw [hinv] at hpsi
  have hφ : (congrTwistIso Φ hΦ).hom.app (n : ℤ) =
      (Scheme.Modules.pullbackCongr (relativeProjCongr_hom_eq Φ hΦ)).hom.app (relativeTwist A₂ n)
        ≫ (ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ)
          (eventually_isIso_congrInvHom Φ hΦ)).app n :=
    (congrTwistIso_hom_app Φ hΦ n).trans (congrTwistHom_app Φ hΦ n)
  have hW' : (relativeProj A₁).toBase ⁻¹ᵁ V ≤
      ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
        (eventually_isIso_congrInvHom Φ hΦ) ⁻¹ᵁ ((relativeProj A₂).toBase ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ProjectiveDeformation.projMapOfEventuallyIso_comp_toBase]
  have key := pullbackCongr_comp_app_map_unitApp (r := (relativeProjCongr Φ hΦ).hom)
    (W := (relativeProj A₁).toBase ⁻¹ᵁ V)
    (C := ProjectiveDeformation.projMapOfEventuallyIso (congrInvHom Φ hΦ)
      (eventually_isIso_congrInvHom Φ hΦ)) (N := relativeTwist A₁ n)
    (relativeProjCongr_hom_eq Φ hΦ) (relativeTwist A₂ n)
    ((ProjectiveDeformation.projTwistHom (congrInvHom Φ hΦ)
      (eventually_isIso_congrInvHom Φ hΦ)).app (n : ℤ))
    ((congrTwistIso Φ hΦ).hom.app (n : ℤ)) hφ ((relativeProj A₂).toBase ⁻¹ᵁ V)
    (by rw [← Scheme.Hom.comp_preimage, relativeProjCongr_hom_comp_toBase]) hW'
    (psiU A₂ n V (((congrHom Φ).app (n : ℤ)).app V a))
  rw [key, hpsi, map_map_homOfLE _ _ _ le_rfl]
  simp

/-- **The isomorphism `congrTwistIso` carries `congrPsi` to Tag 01NR's `ψ` for `𝒜₁`.** -/
theorem congrPsi_comp_congrTwistIso (n : ℕ) :
    congrPsi Φ hΦ n ≫ (Scheme.Modules.pushforward (relativeProj A₁).toBase).map
        ((congrTwistIso Φ hΦ).hom.app (n : ℤ)) =
      (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁).ψ n := by
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  exact congrTwistIso_app_congrPsi_app Φ hΦ n V a

end Congr

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
