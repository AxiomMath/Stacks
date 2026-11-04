module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# The comparison around a relative square of `Coh_{X/B}`, in the spelling of the cube lemma

For a commuting square `i ≫ f = k = p ≫ t` of morphisms of algebraic spaces, the comparison
`AlgebraicGeometry.Space.modulePullbackSquare` of iterated inverse images of modules (Stacks 03LU)
is `Deformation.ToposThickening.cubeSideIso` of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, between the identifications of the pullbacks along the
two four-field readings of the morphisms of small étale ringed topoi
(`Space.modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom`).
This is `AlgebraicGeometry.Space.modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app` read with the
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` pullbacks and in the categories of the
adjunctions, which is the shape of the side hypotheses of
`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`. It is stated over
plain categories with every identification a separate hypothesis
(`Deformation.ToposThickening.cubeSideIso_hom_app_eq_of_triangles`), instantiated once at fvar
spaces, and then at the relative squares of `Coh_{X/B}`
(`CoherentSituation.relativeSquare_modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app`).

The cube lemma itself is recorded at fvar spaces too
(`AlgebraicGeometry.Space.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj`); its
side hypotheses are syntactically the statements of the fvar-space comparison above. For the
relative squares, both are instantiated with the spaces given explicitly
(`D.relativeSquareSituation.space`, `(schemeSpaceFunctor B S hS).obj (·).left`) and with the
comparison `σ` of the side given with all its implicit arguments, so that the side hypotheses of
the instance of the cube lemma are matched without comparing the two spellings `Comma.left` and
`CostructuredArrow.left` of the test schemes, or the two spellings of the base. The categories of
modules are those of the adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`: retyping them
through `AlgebraicGeometry.Space.spaceModulesCategory` is expensive to compare.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA).

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace Deformation.ToposThickening

/-- **A comparison around a square, read through equal functors.** Let `τ₁ : M_k ≅ M_f ⋙ M_i` and
`τ₂ : M_k ≅ M_t ⋙ M_p` be isomorphisms between functors equal to the left adjoints whose inverses
are the comparisons of left adjoints of the two triangles, and let `σ : P_f ⋙ P_i ≅ P_t ⋙ P_p` be
`τ₁⁻¹ ≫ τ₂` read through equalities `P = M` of functors. Then `σ` at an object is
`Deformation.ToposThickening.cubeSideIso`, between the identifications of the objects given by
`L = P`. -/
theorem cubeSideIso_hom_app_eq_of_triangles {𝒱 𝒯 : Type*} [Category* 𝒱] [Category* 𝒯]
    {Lp : 𝒯 ⥤ 𝒱} {Rp : 𝒱 ⥤ 𝒯} (ap : Lp ⊣ Rp) {𝒴 𝒯' : Type*} [Category* 𝒴] [Category* 𝒯']
    {Li : 𝒴 ⥤ 𝒱} {Ri : 𝒱 ⥤ 𝒴} (ai : Li ⊣ Ri) {Lf : 𝒯' ⥤ 𝒴} {Rf : 𝒴 ⥤ 𝒯'} (af : Lf ⊣ Rf)
    {Lt : 𝒯' ⥤ 𝒯} {Rt : 𝒯 ⥤ 𝒯'} (at' : Lt ⊣ Rt) {Lk : 𝒯' ⥤ 𝒱} {Rk : 𝒱 ⥤ 𝒯'} (ak : Lk ⊣ Rk)
    (a : Ri ⋙ Rf ≅ Rk) (b : Rp ⋙ Rt ≅ Rk)
    {Pi : 𝒴 ⥤ 𝒱} {Pp : 𝒯 ⥤ 𝒱} {Pf : 𝒯' ⥤ 𝒴} {Pt : 𝒯' ⥤ 𝒯}
    (hf : Lf = Pf) (hi : Li = Pi) (ht : Lt = Pt) (hp : Lp = Pp)
    {Mi : 𝒴 ⥤ 𝒱} {Mf : 𝒯' ⥤ 𝒴} {Mt : 𝒯' ⥤ 𝒯} {Mp : 𝒯 ⥤ 𝒱} {Mk : 𝒯' ⥤ 𝒱}
    (hiM : Li = Mi) (hfM : Lf = Mf) (htM : Lt = Mt) (hpM : Lp = Mp) (hkM : Lk = Mk)
    (τ₁ : Mk ≅ Mf ⋙ Mi) (τ₂ : Mk ≅ Mt ⋙ Mp) (N : 𝒯')
    (h₁ : τ₁.inv.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) hfM hiM)).symm ≫
        (Adjunction.leftAdjointCompIso af ai ak a).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) hkM))
    (h₂ : τ₂.inv.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) htM hpM)).symm ≫
        (Adjunction.leftAdjointCompIso at' ap ak b).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) hkM))
    (ePf : Pf = Mf) (ePi : Pi = Mi) (ePt : Pt = Mt) (ePp : Pp = Mp)
    (σ : Pf ⋙ Pi ≅ Pt ⋙ Pp) (eσ : HEq σ (τ₁.symm ≪≫ τ₂)) :
    σ.hom.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) hf hi)).symm ≫
        (cubeSideIso ap ai af at' ak a b).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) ht hp)) := by
  subst ePf ePi ePt ePp
  obtain rfl := eq_of_heq eσ
  exact inv_app_comp_hom_app_eq_cubeSideIso_hom_app ai af at' ap ak a b hiM hfM htM hpM hkM τ₁ τ₂ N
    h₁ h₂



end Deformation.ToposThickening

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V W T T' : AlgebraicSpaces B S hS} (p : V ⟶ T) (i : V ⟶ W) (f : W ⟶ T') (t : T ⟶ T')
  (kk : V ⟶ T') (hf : i ≫ f = kk) (ht : p ≫ t = kk) (N : spaceModules T')

/-- **The comparison of iterated inverse images around a commuting square `i ≫ f = k = p ≫ t`,
read with the `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` pullbacks**:
`AlgebraicGeometry.Space.modulePullbackSquare` at `N` is
`Deformation.ToposThickening.cubeSideIso` of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, between the identifications
`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom`
of the iterated inverse images. -/
theorem modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom :
    type_of% (Deformation.ToposThickening.cubeSideIso_hom_app_eq_of_triangles
      (spaceModuleAdj p) (spaceModuleAdj i) (spaceModuleAdj f) (spaceModuleAdj t)
      (spaceModuleAdj kk)
      (modulePushforwardCompIsoOfEq i f kk hf) (modulePushforwardCompIsoOfEq p t kk ht)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_modulePullback i)
      (pullbackModules_toModulesHom_eq_modulePullback f)
      (pullbackModules_toModulesHom_eq_modulePullback t)
      (pullbackModules_toModulesHom_eq_modulePullback p)
      (pullbackModules_toModulesHom_eq_modulePullback kk)
      (modulePullbackTriangle B S hS hf) (modulePullbackTriangle B S hS ht) N
      (modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app i f kk hf N)
      (modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app p t kk ht N)
      rfl rfl rfl rfl (modulePullbackSquare B S hS hf ht) HEq.rfl) :=
  Deformation.ToposThickening.cubeSideIso_hom_app_eq_of_triangles
      (spaceModuleAdj p) (spaceModuleAdj i) (spaceModuleAdj f) (spaceModuleAdj t)
      (spaceModuleAdj kk)
      (modulePushforwardCompIsoOfEq i f kk hf) (modulePushforwardCompIsoOfEq p t kk ht)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_modulePullback i)
      (pullbackModules_toModulesHom_eq_modulePullback f)
      (pullbackModules_toModulesHom_eq_modulePullback t)
      (pullbackModules_toModulesHom_eq_modulePullback p)
      (pullbackModules_toModulesHom_eq_modulePullback kk)
      (modulePullbackTriangle B S hS hf) (modulePullbackTriangle B S hS ht) N
      (modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app i f kk hf N)
      (modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app p t kk ht N)
      rfl rfl rfl rfl (modulePullbackSquare B S hS hf ht) HEq.rfl


section Cube

variable {V W X T T₂ T₁ : AlgebraicSpaces B S hS} (i₂ : V ⟶ W) (j : W ⟶ X) (i₁ : V ⟶ X)
  (hi : i₂ ≫ j = i₁) (p : V ⟶ T) (f₂ : W ⟶ T₂) (f₁ : X ⟶ T₁) (t₂ : T ⟶ T₂) (γ : T₂ ⟶ T₁)
  (t₁ : T ⟶ T₁) (ht : t₂ ≫ γ = t₁) (k : W ⟶ T₁) (hk : j ≫ f₁ = k) (hk' : f₂ ≫ γ = k)
  (k₁ : V ⟶ T₁) (h₁ : i₁ ≫ f₁ = k₁) (h₁' : p ≫ t₁ = k₁) (k₂ : V ⟶ T₂) (h₂ : i₂ ≫ f₂ = k₂)
  (h₂' : p ≫ t₂ = k₂)

/-- **The cube comparison of Stacks 03LU at the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj` of a commutative cube of algebraic spaces**:
`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq` with the
comparisons of direct images `AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq` and the
pullbacks read through
`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom`.
Its side hypotheses are the statements of
`modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom` for the two
sides of the cube. -/
theorem homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj :
    type_of% (Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq
      (spaceModuleAdj i₁) (spaceModuleAdj i₂) (spaceModuleAdj j) (spaceModuleAdj p)
      (spaceModuleAdj f₁) (spaceModuleAdj f₂) (spaceModuleAdj t₁) (spaceModuleAdj t₂)
      (spaceModuleAdj γ) (spaceModuleAdj k₁) (spaceModuleAdj k₂) (spaceModuleAdj k)
      _ _ _ _ _ _ _ _ _ _
      (modulePushforwardCompIsoOfEq_assoc i₂ j f₁ i₁ k k₁ hi hk h₁
        (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁))
      (modulePushforwardCompIsoOfEq_assoc i₂ f₂ γ k₂ k k₁ h₂ hk'
        (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂')
        (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁))
      (modulePushforwardCompIsoOfEq_assoc p t₂ γ k₂ t₁ k₁ h₂' ht
        (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂') h₁')
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)) :=
  Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq
      (spaceModuleAdj i₁) (spaceModuleAdj i₂) (spaceModuleAdj j) (spaceModuleAdj p)
      (spaceModuleAdj f₁) (spaceModuleAdj f₂) (spaceModuleAdj t₁) (spaceModuleAdj t₂)
      (spaceModuleAdj γ) (spaceModuleAdj k₁) (spaceModuleAdj k₂) (spaceModuleAdj k)
      _ _ _ _ _ _ _ _ _ _
      (modulePushforwardCompIsoOfEq_assoc i₂ j f₁ i₁ k k₁ hi hk h₁
        (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁))
      (modulePushforwardCompIsoOfEq_assoc i₂ f₂ γ k₂ k k₁ h₂ hk'
        (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂')
        (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁))
      (modulePushforwardCompIsoOfEq_assoc p t₂ γ k₂ t₁ k₁ h₂' ht
        (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂') h₁')
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)

end Cube

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- **The comparison around the relative square of `h : T ⟶ T'`, in the spelling of the cube
lemma**: `AlgebraicGeometry.Space.modulePullbackSquare` of `X_h ≫ (X_{T'} ⟶ T') = (X_T ⟶ T) ≫ h`
at the ideal of `T ⊂ T'` is `Deformation.ToposThickening.cubeSideIso` of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, between the identifications of the pullbacks along the
two four-field readings of the morphisms of small étale ringed topoi. This is the side hypothesis
of `Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq` for the cube of
the relative squares of `Coh_{X/B}` (instantiated as
`AlgebraicGeometry.Space.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj` with the
spaces `V := D.relativeSquareSituation.space ξ.T`, `T := (schemeSpaceFunctor B S hS).obj ξ.T.left`,
and so on, given explicitly), with `σ` the comparison
`AlgebraicGeometry.Space.modulePullbackSquare` with the same spaces and the maps
`D.relativeSquareSituation.relativeMap h`, `D.relativeSquareSituation.projection T'`,
`D.relativeSquareSituation.projection ξ.T`, `(schemeSpaceFunctor B S hS).map h.left` and their
composite given explicitly. -/
theorem relativeSquare_modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app :
    type_of% (modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T')
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T' := (schemeSpaceFunctor B S hS).obj T'.left)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.relativeMap h)
      (D.relativeSquareSituation.projection T') ((schemeSpaceFunctor B S hS).map h.left)
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h) rfl
      (D.relativeSquareSituation.testSchemeFirstOrderThickening h hh).idealOfThickening.I) :=
  modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom ..

end AlgebraicGeometry.Space.CoherentSituation
