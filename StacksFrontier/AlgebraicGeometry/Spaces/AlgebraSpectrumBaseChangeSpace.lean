module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeAlgebraSpectrumSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.ReesBaseChangeSpace

/-!
# Base change of a space over an affine object to the spectrum of a finitely generated algebra

For an affine object `T` of the site, a finitely generated `A`-algebra `R` (`A = Γ(T₀, ⊤)`) and
`f : X ⟶ h_T`, the base change `X_R = X ×_{h_T} h_{Spec R}` has affine projection to `X` and proper
projection to `h_{Spec R}` when `f` is proper; an `A`-algebra map `R ⟶ R'` induces
`X_{R'} ⟶ X_R` over `X`. For the Rees embedding `A[Jt] ⊆ A[s]` this is the morphism `ψ` of the
proof of [Stacks, Tag 08AW].

## Main definitions

* `AlgebraicGeometry.Space.algebraBaseChange`: the base change `X_R = X ×_{h_T} h_{Spec R}`.
* `AlgebraicGeometry.Space.algebraBaseChangeProjection`: the projection `X_R ⟶ X`.
* `AlgebraicGeometry.Space.algebraBaseChangeStructure`: the projection `X_R ⟶ h_{Spec R}`.
* `AlgebraicGeometry.Space.algebraBaseChangeMap`: the morphism `X_{R'} ⟶ X_R` over `X` induced by
  an `A`-algebra map `R →ₐ R'`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_algebraBaseChangeProjection`: `X_R ⟶ X` is affine.
* `AlgebraicGeometry.Space.isProper_algebraBaseChangeStructure`: `X_R ⟶ h_{Spec R}` is proper
  when `f` is proper.
* `AlgebraicGeometry.Space.isPullback_algebraBaseChangeMap`: `X_{R'} ⟶ X_R` is the base change of
  `h_{Spec R'} ⟶ h_{Spec R}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]

/-- `X_R = X ×_{h_T} h_{Spec R}`. -/
abbrev algebraBaseChange : AlgebraicSpaces B S hS :=
  pullback f (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R))

/-- The projection `X_R ⟶ X`. -/
abbrev algebraBaseChangeProjection : algebraBaseChange B S hS T f R ⟶ X :=
  pullback.fst f (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R))

/-- The projection `X_R ⟶ h_{Spec R}`. -/
abbrev algebraBaseChangeStructure :
    algebraBaseChange B S hS T f R ⟶ schemeSpace (algebraSpectrumOver B S hS T R) :=
  pullback.snd f (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R))

/-- The square formed by `X_R ⟶ X`, `X_R ⟶ h_{Spec R}`, `f` and `h_{Spec R} ⟶ h_T` is
cartesian. -/
theorem isPullback_algebraBaseChange :
    IsPullback (algebraBaseChangeProjection B S hS T f R).hom
      (algebraBaseChangeStructure B S hS T f R).hom f.hom
      (yoneda.map (algebraSpectrumSiteHom B S hS T R)) :=
  AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _)

/-- The projection `X_R ⟶ X` is affine. -/
theorem isAffineHom_algebraBaseChangeProjection :
    IsAffineHom B S hS (algebraBaseChangeProjection B S hS T f R).hom :=
  isAffineHom_of_isPullback' B S hS (isPullback_algebraBaseChange B S hS T f R).flip
    (isAffineHom_yoneda_map B S hS (algebraSpectrumSiteHom B S hS T R))

/-- If `f : X ⟶ h_T` is proper, then the projection `X_R ⟶ h_{Spec R}` is proper. -/
theorem isProper_algebraBaseChangeStructure (hf : IsProper B S hS f.hom) :
    IsProper B S hS (algebraBaseChangeStructure B S hS T f R).hom :=
  isProper_of_isPullback B S hS (algebraBaseChange B S hS T f R).2 X.2
    (schemeSpace (algebraSpectrumOver B S hS T R)).2 (schemeSpace T).2
    (isPullback_algebraBaseChange B S hS T f R) hf

/-- The morphism `X_{R'} ⟶ X_R` over `X` induced by an `A`-algebra map `φ : R →ₐ R'`. -/
def algebraBaseChangeMap (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    algebraBaseChange B S hS T f R' ⟶ algebraBaseChange B S hS T f R :=
  pullback.map f (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R')) f
    (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R))
    (𝟙 X) (schemeSpaceMap (algebraSpectrumSiteMap B S hS T R R' φ)) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id])
    (by
      rw [Category.comp_id]
      apply ObjectProperty.hom_ext
      exact ((yoneda.map_comp _ _).symm.trans
        (congrArg yoneda.map (algebraSpectrumSiteMap_comp_siteHom B S hS T R R' φ))).symm)

/-- The morphism `X_{R'} ⟶ X_R` commutes with the projections to `X`. -/
theorem algebraBaseChangeMap_projection (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    algebraBaseChangeMap B S hS T f R R' φ ≫ algebraBaseChangeProjection B S hS T f R =
      algebraBaseChangeProjection B S hS T f R' := by
  rw [algebraBaseChangeMap, pullback.lift_fst, Category.comp_id]

/-- The morphism `X_{R'} ⟶ X_R` lies over the morphism `h_{Spec R'} ⟶ h_{Spec R}` induced by
`φ`. -/
theorem algebraBaseChangeMap_structure (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    algebraBaseChangeMap B S hS T f R R' φ ≫ algebraBaseChangeStructure B S hS T f R =
      algebraBaseChangeStructure B S hS T f R' ≫
        schemeSpaceMap (algebraSpectrumSiteMap B S hS T R R' φ) := by
  rw [algebraBaseChangeMap, pullback.lift_snd]

/-- The morphism `X_{R'} ⟶ X_R` is the base change of `h_{Spec R'} ⟶ h_{Spec R}` along
`X_R ⟶ h_{Spec R}`. -/
theorem isPullback_algebraBaseChangeMap (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    IsPullback (algebraBaseChangeMap B S hS T f R R' φ).hom
      (algebraBaseChangeStructure B S hS T f R').hom
      (algebraBaseChangeStructure B S hS T f R).hom
      (yoneda.map (algebraSpectrumSiteMap B S hS T R R' φ)) := by
  have hR := isPullback_algebraBaseChange B S hS T f R
  have hR' := isPullback_algebraBaseChange B S hS T f R'
  refine IsPullback.of_right ?_ (congrArg (fun k => k.hom)
    (algebraBaseChangeMap_structure B S hS T f R R' φ)) hR
  have e : (algebraBaseChangeMap B S hS T f R R' φ).hom ≫
      (algebraBaseChangeProjection B S hS T f R).hom =
      (algebraBaseChangeProjection B S hS T f R').hom :=
    congrArg (fun k => k.hom) (algebraBaseChangeMap_projection B S hS T f R R' φ)
  have e2 : yoneda.map (algebraSpectrumSiteMap B S hS T R R' φ) ≫
      yoneda.map (algebraSpectrumSiteHom B S hS T R) =
      yoneda.map (algebraSpectrumSiteHom B S hS T R') :=
    (yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (algebraSpectrumSiteMap_comp_siteHom B S hS T R R' φ))
  rw [e]
  exact (congrArg (fun k => IsPullback (algebraBaseChangeProjection B S hS T f R').hom
    (algebraBaseChangeStructure B S hS T f R').hom f.hom k) e2).mpr hR'

end AlgebraicGeometry.Space

end
