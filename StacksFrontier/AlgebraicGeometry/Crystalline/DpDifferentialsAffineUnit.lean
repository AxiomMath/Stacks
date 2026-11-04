module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsAffineSections

/-!
# The sheafification unit of the divided power differentials over an affine open

Let `(T, J, δ)` be a divided power scheme and `f : T → Y` a morphism of schemes. The sheaf
`Ω_{T/Y,δ}` of divided power differentials is the sheaf of `𝒪_T`-modules associated with the
presheaf `Crystalline.dpDifferentialsPresheaf`. Over an affine open `W` lying over an affine open
`V` of the base, the sheafification unit `Crystalline.dpDifferentialsToSheaf` is bijective on the
sections over `W`, and both sides are identified with `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`.

## Main results

* `Crystalline.toSheaf_comp_affineSectionsHom` — the sheafification unit followed by the
  identification of [Stacks, Tag 07IY] clause (2) is the identification of [Stacks, Tag 07J0].
* `Crystalline.bijective_dpToSheafApp` — **the sheafification unit of the presheaf of divided
  power differentials is bijective on the sections over an affine open lying over an affine open
  of the base.**
* `Crystalline.bijective_toSheafify_app_dpDifferentialsPresheaf` — the same statement read on
  the underlying presheaf of abelian groups, where the unit is `CategoryTheory.toSheafify`.
* `Crystalline.dpDifferentialsAffineUnitEquiv` — that bijection as an equivalence.
* `Crystalline.isLocalizedModule_presheafRestrictₗ` — the sections of the presheaf over a basic
  open of an affine open lying over an affine open of the base are the localization of its
  sections over that affine open.
* `Crystalline.GlobalCrystallineSituation.bijective_restrictedToSheaf_app` — the comparison of
  [Stacks, Tag 07IZ] from the restriction of `Ω_{X/S}` to the ambient scheme of an object of
  `CRIS(X/S)` into the sheaf `Ω_{T/S,δ}` is bijective on the sections over an affine open lying
  over an affine open of the divided power base.

## References

* [Stacks Project, Tag 07IW](https://stacks.math.columbia.edu/tag/07IW)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace Crystalline

section Affine

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  {W : T.scheme.Opens} (hW : IsAffineOpen W) {V : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

omit hW hV in
/-- The sheafification unit of the presheaf of divided power differentials on the sections over
`W`, as a morphism of `Γ(W, 𝒪_T)`-modules. -/
def dpToSheafApp :
    (dpDifferentialsPresheaf T Y f).obj (op W) ⟶
      ModuleCat.of Γ(T.scheme, W) Γ(dpDifferentialsSheaf T Y f, W) :=
  (dpDifferentialsToSheaf T Y f).app (op W)

/-- `Crystalline.affineSectionsEquiv`, the identification of [Stacks, Tag 07IY] clause (2), read
as a morphism of `ModuleCat`. -/
def affineSectionsHom :
    ModuleCat.of Γ(T.scheme, W) Γ(dpDifferentialsSheaf T Y f, W) ⟶ affineDpObj T Y f h :=
  ModuleCat.ofHom (affineSectionsEquiv T Y f hW h hV).toLinearMap

/-- `Crystalline.affineSectionsHom` acts as `Crystalline.affineSectionsEquiv`. -/
@[simp]
theorem affineSectionsHom_apply (x : Γ(dpDifferentialsSheaf T Y f, W)) :
    (affineSectionsHom T Y f hW h hV).hom x = affineSectionsEquiv T Y f hW h hV x := rfl

include hW hV in
/-- **The triangle.** The sheafification unit of the presheaf of divided power differentials,
followed by the identification of its sections over an affine open with
`Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` of [Stacks, Tag 07IY] clause (2), is the identification of the
*presheaf's* sections with the same module of [Stacks, Tag 07J0]. -/
theorem toSheaf_comp_affineSectionsHom :
    dpToSheafApp T Y f ≫ affineSectionsHom T Y f hW h hV = affineDpHom T Y f h hW hV :=
  dpConstDifferentials_ext fun b ↦
    (affineSectionsEquiv_apply T Y f hW h hV b).trans (affineDpHom_d T Y f h hW hV b).symm

include hW h hV in
/-- **The sheafification unit of the presheaf of divided power differentials is bijective on the
sections over an affine open lying over an affine open of the base.** -/
theorem bijective_dpToSheafApp :
    Function.Bijective (ConcreteCategory.hom (dpToSheafApp T Y f (W := W))) := by
  have hA : Function.Bijective (ConcreteCategory.hom (affineDpHom T Y f h hW hV)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom (affineDpIso T Y f h hW hV))
  rw [← toSheaf_comp_affineSectionsHom T Y f hW h hV] at hA
  exact ((affineSectionsEquiv T Y f hW h hV).bijective.of_comp_iff' _).1 hA

include hW h hV in
/-- `Crystalline.bijective_dpToSheafApp` read on the underlying presheaf of abelian
groups, where the unit is `CategoryTheory.toSheafify`. -/
theorem bijective_toSheafify_app_dpDifferentialsPresheaf :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology T.scheme)
        (dpDifferentialsPresheaf T Y f).presheaf).app (op W))) :=
  bijective_dpToSheafApp T Y f hW h hV

include hW h hV in
/-- **The sections of the presheaf of divided power differentials over an affine open lying over
an affine open of the base are the sections of the sheaf `Ω_{T/Y,δ}` there**, as an equivalence
given by the sheafification unit. -/
def dpDifferentialsAffineUnitEquiv :
    ↑((dpDifferentialsPresheaf T Y f).obj (op W)) ≃ Γ(dpDifferentialsSheaf T Y f, W) :=
  Equiv.ofBijective _ (bijective_dpToSheafApp T Y f hW h hV)

include hW h hV in
/-- `Crystalline.dpDifferentialsAffineUnitEquiv` acts as the sheafification unit
`Crystalline.dpToSheafApp`. -/
@[simp]
theorem dpDifferentialsAffineUnitEquiv_apply (x : ↑((dpDifferentialsPresheaf T Y f).obj (op W))) :
    dpDifferentialsAffineUnitEquiv T Y f hW h hV x =
      ConcreteCategory.hom (dpToSheafApp T Y f (W := W)) x := rfl

end Affine

/-! ### Localization on the basic opens -/

section Localization

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  {W' W : T.scheme.Opens} (hle : W' ≤ W)

/-- The `Γ(W, 𝒪_T)`-module structure on the sections of the presheaf of divided power
differentials over a smaller open, by restriction of the functions. -/
@[instance_reducible]
noncomputable def presheafModuleOfLE :
    Module Γ(T.scheme, W) ↑((dpDifferentialsPresheaf T Y f).obj (op W')) :=
  Module.compHom _ (T.scheme.presheaf.map (homOfLE hle).op).hom

/-- The restriction map of the presheaf of divided power differentials, as a linear map over the
sections of `𝒪_T` on the larger open. -/
noncomputable def presheafRestrictₗ :
    letI := presheafModuleOfLE T Y f hle
    ↑((dpDifferentialsPresheaf T Y f).obj (op W)) →ₗ[Γ(T.scheme, W)]
      ↑((dpDifferentialsPresheaf T Y f).obj (op W')) :=
  letI := presheafModuleOfLE T Y f hle
  { toFun := (dpDifferentialsPresheaf T Y f).map (homOfLE hle).op
    map_add' := map_add _
    map_smul' := fun r x ↦
      (dpDifferentialsPresheaf T Y f).map_smul (homOfLE hle).op r x }

/-- The sheafification unit on the sections over an open, as a linear map over the sections of
`𝒪_T` there. -/
noncomputable def dpToSheafAppₗ (W'' : T.scheme.Opens) :
    ↑((dpDifferentialsPresheaf T Y f).obj (op W'')) →ₗ[Γ(T.scheme, W'')]
      Γ(dpDifferentialsSheaf T Y f, W'') :=
  (dpToSheafApp T Y f (W := W'')).hom

/-- The sheafification unit over the smaller open, as a linear map over the sections of `𝒪_T` on
the larger one: both module structures are restricted along the same map of functions. -/
noncomputable def dpToSheafAppOfLE :
    letI := presheafModuleOfLE T Y f hle
    letI := moduleOfLE (dpDifferentialsSheaf T Y f) hle
    ↑((dpDifferentialsPresheaf T Y f).obj (op W')) →ₗ[Γ(T.scheme, W)]
      Γ(dpDifferentialsSheaf T Y f, W') :=
  letI := presheafModuleOfLE T Y f hle
  letI := moduleOfLE (dpDifferentialsSheaf T Y f) hle
  { toFun := dpToSheafAppₗ T Y f W'
    map_add' := map_add _
    map_smul' := fun _ x ↦ (dpToSheafAppₗ T Y f W').map_smul _ x }

/-- **The sheafification unit is natural**: restricting a section of the presheaf of divided power
differentials and then mapping it into the sheaf is mapping it into the sheaf and then
restricting. -/
theorem dpToSheafAppOfLE_comp_presheafRestrictₗ :
    letI := presheafModuleOfLE T Y f hle
    letI := moduleOfLE (dpDifferentialsSheaf T Y f) hle
    (dpToSheafAppOfLE T Y f hle) ∘ₗ (presheafRestrictₗ T Y f hle) =
      (restrictₗ (dpDifferentialsSheaf T Y f) hle) ∘ₗ dpToSheafAppₗ T Y f W := by
  let := presheafModuleOfLE T Y f hle
  let := moduleOfLE (dpDifferentialsSheaf T Y f) hle
  exact LinearMap.ext fun x ↦
    PresheafOfModules.naturality_apply (dpDifferentialsToSheaf T Y f) (homOfLE hle).op x

variable (hW : IsAffineOpen W) {V : Y.Opens} (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V)

include hW h hV in
/-- **The sections of the presheaf of divided power differentials over a basic open of an affine
open lying over an affine open of the base are the corresponding localization.** -/
theorem isLocalizedModule_presheafRestrictₗ (g : Γ(T.scheme, W)) :
    letI := presheafModuleOfLE T Y f (T.scheme.basicOpen_le g)
    IsLocalizedModule.Away g (presheafRestrictₗ T Y f (T.scheme.basicOpen_le g)) := by
  let := presheafModuleOfLE T Y f (T.scheme.basicOpen_le g)
  let := moduleOfLE (dpDifferentialsSheaf T Y f) (T.scheme.basicOpen_le g)
  have hs : IsLocalizedModule.Away g
      (restrictₗ (dpDifferentialsSheaf T Y f) (T.scheme.basicOpen_le g)) :=
    isLocalizedModule_restrictₗ (dpDifferentialsSheaf T Y f) hW g rfl (T.scheme.basicOpen_le g)
  have he : Function.Bijective (dpToSheafAppₗ T Y f W) :=
    bijective_dpToSheafApp T Y f hW h hV
  have he' : Function.Bijective
      (dpToSheafAppOfLE T Y f (T.scheme.basicOpen_le g)) :=
    bijective_dpToSheafApp T Y f (hW.basicOpen g)
      ((T.scheme.basicOpen_le g).trans h) hV
  have hcomp : IsLocalizedModule (Submonoid.powers g)
      ((restrictₗ (dpDifferentialsSheaf T Y f) (T.scheme.basicOpen_le g)) ∘ₗ
        dpToSheafAppₗ T Y f W) :=
    (IsLocalizedModule.comp_iff_of_bijective_right _ _ he).2 hs
  rw [← dpToSheafAppOfLE_comp_presheafRestrictₗ T Y f (T.scheme.basicOpen_le g)] at hcomp
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _ he').1 hcomp

end Localization

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S)
  {W : A.thickening.target.scheme.Opens} (hW : IsAffineOpen W) {V : S.S.scheme.Opens}
  (h : W ≤ A.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V)

include hW h hV in
/-- **The comparison of [Stacks, Tag 07IZ] is bijective on the sections over an affine open lying
over an affine open of the divided power base.** That is, the restriction of `Ω_{X/S}` to the
ambient scheme `T` of an object `(U, T, δ)` of `CRIS(X/S)` has, over such an open `W`, exactly the
sections of the sheaf `Ω_{T/S,δ}` that it generates. -/
theorem bijective_restrictedToSheaf_app :
    Function.Bijective (ConcreteCategory.hom ((restrictedToSheaf A).app (op W))) := by
  have hunit := bijective_dpToSheafApp A.thickening.target S.S.scheme
    A.toBase.hom hW h hV
  have hcomp : (restrictedToSheaf A).app (op W) =
      (comparisonIsoApp A W).symm.hom ≫
        dpToSheafApp A.thickening.target S.S.scheme A.toBase.hom (W := W) := rfl
  rw [hcomp]
  exact hunit.comp
    ((ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom (comparisonIsoApp A W).symm))

end GlobalCrystallineSituation

end Crystalline

end
