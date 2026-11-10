module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.AffineDeRham
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.AbsoluteFormsComparison
public import StacksFrontier.RingTheory.KaehlerDifferentialIso

/-!
# Relative differential forms on affine opens

Let `g : X ⟶ S` be a morphism of schemes and `U ⊆ X`, `W ⊆ S` affine opens with `U ≤ g⁻¹W`,
`A = Γ(S, W)`, `B = Γ(X, U)`, with `A → B` given by `g.appLE W U h`. This file identifies the
sections over `U` of the sheaf `Ω^p_{X/S}` of relative differential forms with
`⋀ᵖ_B Ω[B⁄A]` (Stacks 01UT, 01V0 and 01I8), and proves that the identification is natural under
restriction, carries the absolute-to-relative comparison `Ω^p_{X/ℤ} ⟶ Ω^p_{X/S}` to
`KaehlerDifferential.absoluteToRelative A B p`, and carries the differential of the relative de
Rham complex `AlgebraicGeometry.Scheme.Hom.deRhamComplex g` to
`KaehlerDifferential.deRhamDifferential` of `B` over `A`.

## Main definitions

* `AlgebraicGeometry.Scheme.relativeDifferentialsSectionsEquiv`:
  `Γ(Ω_{X/S}, U) ≃ Ω[Γ(X, U)⁄Γ(S, W)]`.
* `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv`:
  `Γ(Ω^p_{X/S}, U) ≃ ⋀ᵖ Ω[Γ(X, U)⁄Γ(S, W)]`.
* `AlgebraicGeometry.Scheme.Hom.absoluteToRelativeDifferentials`,
  `AlgebraicGeometry.Scheme.Hom.absoluteToRelativeFormsMap`: the canonical maps
  `Ω_{X/ℤ} ⟶ Ω_{X/S}` and `Ω^n_{X/ℤ} ⟶ Ω^n_{X/S}`.

## Main results

* `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv_restrict`,
  `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv_restrict_map`: naturality under
  restriction, where restriction becomes `⋀ᵖ` of
  `KaehlerDifferential.map Γ(S, W) Γ(S, W') Γ(X, U) Γ(X, U')`.
* `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv_absoluteToRelativeFormsMap`: the
  absolute-to-relative comparison is `KaehlerDifferential.absoluteToRelative`.
* `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv_deRhamComplex_d`: the differential of the
  relative de Rham complex is `KaehlerDifferential.deRhamDifferential`.

## Implementation notes

Terms elaborated under a proof-local `letI` for the algebra `Γ(S, W) → Γ(X, U)` are compared with
the statement's inlined instance only at great cost, so several proofs avoid proof-local
algebra instances, use `simp only` with ground equations to cross between spellings, or pass the
instance explicitly.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra relativeDifferentialFormsGenerator)

variable {X S : Scheme.{u}} (g : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {W : S.Opens}
  (hW : IsAffineOpen W) (h : U ≤ g ⁻¹ᵁ W)

/-- **The relative differentials of a morphism of schemes on affine opens** (Stacks 01UT):
`Γ(Ω_{X/S}, U) ≃ Ω[Γ(X, U)⁄Γ(S, W)]` for affine `U`, `W` with `U ≤ g⁻¹W`. -/
def relativeDifferentialsSectionsEquiv :
    letI := (g.appLE W U h).hom.toAlgebra
    Γ(Hom.relativeDifferentials g, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] :=
  letI := (g.appLE W U h).hom.toAlgebra
  haveI := Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections g hU h hW
  let e := asIso (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections g W U h)
  let φ : Γ(Hom.relativeDifferentials g, U) →ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] :=
    { toFun := fun m => e.inv.hom m
      map_add' := fun a c => map_add _ a c
      map_smul' := fun c a => map_smul _ c a }
  let ψ : Ω[Γ(X, U)⁄Γ(S, W)] →ₗ[Γ(X, U)] Γ(Hom.relativeDifferentials g, U) :=
    { toFun := fun m => e.hom.hom m
      map_add' := fun a c => map_add _ a c
      map_smul' := fun c a => map_smul _ c a }
  LinearEquiv.ofLinearMap φ ψ
    (LinearMap.ext fun x => congrArg (fun k => k.hom x) e.hom_inv_id)
    (LinearMap.ext fun x => congrArg (fun k => k.hom x) e.inv_hom_id)

/-- `relativeDifferentialsSectionsEquiv` carries `D b` back to the universal relative
differential `d b`. -/
theorem relativeDifferentialsSectionsEquiv_symm_D (b : Γ(X, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    (relativeDifferentialsSectionsEquiv g hU hW h).symm (KaehlerDifferential.D Γ(S, W) Γ(X, U) b) =
      (Hom.universalRelativeDerivation g).d b :=
  Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d g W U h b

/-- `relativeDifferentialsSectionsEquiv` carries the universal relative differential `d b` to
`D b`. -/
theorem relativeDifferentialsSectionsEquiv_d (b : Γ(X, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeDifferentialsSectionsEquiv g hU hW h ((Hom.universalRelativeDerivation g).d b) =
      KaehlerDifferential.D Γ(S, W) Γ(X, U) b := by
  let := (g.appLE W U h).hom.toAlgebra
  rw [← relativeDifferentialsSectionsEquiv_symm_D g hU hW h, LinearEquiv.apply_symm_apply]

/-- **The relative differential `p`-forms of a morphism of schemes on affine opens**
(Stacks 01UT, 01I8): `Γ(Ω^p_{X/S}, U) ≃ ⋀ᵖ Ω[Γ(X, U)⁄Γ(S, W)]`. -/
def relativeFormsSectionsEquiv (p : ℕ) :
    letI := (g.appLE W U h).hom.toAlgebra
    Γ(Hom.relativeDifferentialForms g p, U) ≃ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄Γ(S, W)] :=
  letI := (g.appLE W U h).hom.toAlgebra
  (affineOpenExteriorPowerΓIso (Hom.relativeDifferentials g) hU
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) p).toLinearEquiv ≪≫ₗ
    exteriorPowerCongr (relativeDifferentialsSectionsEquiv g hU hW h) p

/-- `relativeFormsSectionsEquiv` unfolded. -/
theorem relativeFormsSectionsEquiv_apply_hom (p : ℕ) (ω : Γ(Hom.relativeDifferentialForms g p, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h p ω =
      exteriorPower.map p (relativeDifferentialsSectionsEquiv g hU hW h).toLinearMap
        ((affineOpenExteriorPowerΓIso (Hom.relativeDifferentials g) hU
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) p).hom.hom ω) :=
  rfl

include hU hW h in
/-- The universal relative differentials of the sections span the relative differentials over an
affine open. -/
theorem span_range_universalRelativeDerivation_d_relative :
    Submodule.span Γ(X, U) (Set.range fun b : Γ(X, U) =>
      show Γ(Hom.relativeDifferentials g, U) from
        (Hom.universalRelativeDerivation g).d b) = ⊤ := by
  let := (g.appLE W U h).hom.toAlgebra
  have hs := congrArg
    (Submodule.map (relativeDifferentialsSectionsEquiv g hU hW h).symm.toLinearMap)
    (KaehlerDifferential.span_range_derivation Γ(S, W) Γ(X, U))
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at hs
  refine Eq.trans (congrArg _ (congrArg Set.range (funext fun b => ?_))) hs
  exact (relativeDifferentialsSectionsEquiv_symm_D g hU hW h b).symm

variable {g} {U' : X.Opens} (hU' : IsAffineOpen U') {W' : S.Opens} (hW' : IsAffineOpen W')
  (h' : U' ≤ g ⁻¹ᵁ W')

/-- **The identification of relative forms is natural under restriction**: for affine
`U' ≤ U`, `W' ≤ W` with `U' ≤ g⁻¹W'`, restricting a form from `U` to `U'` is `⋀ᵖ` of a
semilinear map `u : Ω[Γ(X, U)⁄Γ(S, W)] → Ω[Γ(X, U')⁄Γ(S, W')]` over the restriction of functions
carrying `D b` to `D b|_{U'}`, for instance `Stacks.KaehlerDifferentialSquare.map`, which is
`KaehlerDifferential.map Γ(S, W) Γ(S, W') Γ(X, U) Γ(X, U')`
(`relativeFormsSectionsEquiv_restrict_map`). -/
theorem relativeFormsSectionsEquiv_restrict (hUU : U' ≤ U) (p : ℕ)
    (u : letI := (g.appLE W U h).hom.toAlgebra
      letI := (g.appLE W' U' h').hom.toAlgebra
      Ω[Γ(X, U)⁄Γ(S, W)] →ₛₗ[(X.presheaf.map (homOfLE hUU).op).hom] Ω[Γ(X, U')⁄Γ(S, W')])
    (hu : letI := (g.appLE W U h).hom.toAlgebra
      letI := (g.appLE W' U' h').hom.toAlgebra
      ∀ b, u (KaehlerDifferential.D Γ(S, W) Γ(X, U) b) =
        KaehlerDifferential.D Γ(S, W') Γ(X, U') ((X.presheaf.map (homOfLE hUU).op).hom b))
    (η : Γ(Hom.relativeDifferentialForms g p, U)) :
    relativeFormsSectionsEquiv g hU' hW' h' p
        ((Hom.relativeDifferentialForms g p).presheaf.map (homOfLE hUU).op η) =
      ExteriorAlgebra.powMapₛₗ p (X.presheaf.map (homOfLE hUU).op).hom u
        (relativeFormsSectionsEquiv g hU hW h p η) := by
  let := (g.appLE W U h).hom.toAlgebra
  let := (g.appLE W' U' h').hom.toAlgebra
  let T : Γ(Hom.relativeDifferentialForms g p, U) →ₛₗ[(X.presheaf.map (homOfLE hUU).op).hom]
      Γ(Hom.relativeDifferentialForms g p, U') :=
    { toFun := (Hom.relativeDifferentialForms g p).presheaf.map (homOfLE hUU).op
      map_add' := map_add _
      map_smul' := Scheme.Modules.map_smul _ (homOfLE hUU) }
  have hg : ∀ b : Γ(X, U), relativeDifferentialsSectionsEquiv g hU' hW' h'
      ((Hom.universalRelativeDerivation g).d ((X.presheaf.map (homOfLE hUU).op).hom b)) =
      u (relativeDifferentialsSectionsEquiv g hU hW h ((Hom.universalRelativeDerivation g).d b))
      := fun b => by
    rw [relativeDifferentialsSectionsEquiv_d, relativeDifferentialsSectionsEquiv_d, hu]
  have hT : ∀ c : Fin p → Γ(X, U), T ((Hom.relativeDifferentialFormsAlgebra
      g).toPresheafGradedAlgebra.homogeneousProd (op U) p fun i =>
        (relativeDifferentialFormsGenerator g).val.app (op U)
          ((Hom.universalRelativeDerivation g).d (c i))) =
      (Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra.homogeneousProd (op U') p
        fun i => (relativeDifferentialFormsGenerator g).val.app (op U')
          ((Hom.universalRelativeDerivation g).d
            ((X.presheaf.map (homOfLE hUU).op).hom (c i))) := fun c => by
    refine ((Hom.relativeDifferentialFormsAlgebra
      g).toPresheafGradedAlgebra.homogeneousProd_naturality (homOfLE hUU).op p _).trans ?_
    refine congrArg ((Hom.relativeDifferentialFormsAlgebra
      g).toPresheafGradedAlgebra.homogeneousProd (op U') p) (funext fun i => ?_)
    refine (PresheafOfModules.naturality_apply
      (relativeDifferentialFormsGenerator g).val (homOfLE hUU).op _).symm.trans ?_
    exact congrArg ((relativeDifferentialFormsGenerator g).val.app (op U'))
      ((Hom.universalRelativeDerivation g).d_map (homOfLE hUU).op (c i)).symm
  have key := map_affineOpenExteriorPowerΓIso_hom_semilinear hU hU'
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
    (relativeDifferentialsSectionsEquiv g hU hW h)
    (relativeDifferentialsSectionsEquiv g hU' hW' h') u
    (fun b : Γ(X, U) => show Γ(Hom.relativeDifferentials g, U) from
      (Hom.universalRelativeDerivation g).d b)
    (fun b : Γ(X, U) => show Γ(Hom.relativeDifferentials g, U') from
      (Hom.universalRelativeDerivation g).d ((X.presheaf.map (homOfLE hUU).op).hom b))
    (span_range_universalRelativeDerivation_d_relative g hU hW h) hg p T hT η
  have hTη : (Hom.relativeDifferentialForms g p).presheaf.map (homOfLE hUU).op η = T η := rfl
  refine (relativeFormsSectionsEquiv_apply_hom g hU' hW' h' p _).trans (Eq.trans ?_ (key.trans ?_))
  · exact congrArg (fun z => exteriorPower.map p
      (relativeDifferentialsSectionsEquiv g hU' hW' h').toLinearMap
      ((affineOpenExteriorPowerΓIso (Hom.relativeDifferentials g) hU'
        (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) p).hom.hom z)) hTη
  exact congrArg _ (relativeFormsSectionsEquiv_apply_hom g hU hW h p η).symm

omit hU' hW' in
/-- The square of rings of a restriction `U' ≤ U`, `W' ≤ W` of an affine chart commutes. -/
theorem algebraMap_restrict_comm (hUU : U' ≤ U) (hWW : W' ≤ W) (r : Γ(S, W)) :
    letI := (g.appLE W U h).hom.toAlgebra
    letI := (g.appLE W' U' h').hom.toAlgebra
    (X.presheaf.map (homOfLE hUU).op).hom (algebraMap Γ(S, W) Γ(X, U) r) =
      algebraMap Γ(S, W') Γ(X, U') ((S.presheaf.map (homOfLE hWW).op).hom r) := by
  change (g.appLE W U h ≫ X.presheaf.map (homOfLE hUU).op).hom r =
    (S.presheaf.map (homOfLE hWW).op ≫ g.appLE W' U' h').hom r
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- **The identification of relative forms is natural under restriction**, with the map on
differentials `Stacks.KaehlerDifferentialSquare.map`, whose underlying function is
`KaehlerDifferential.map Γ(S, W) Γ(S, W') Γ(X, U) Γ(X, U')`: restriction of forms from `U` to
`U'` becomes `⋀ᵖ` of that map. -/
theorem relativeFormsSectionsEquiv_restrict_map (hUU : U' ≤ U) (hWW : W' ≤ W) (p : ℕ)
    (η : Γ(Hom.relativeDifferentialForms g p, U)) :
    relativeFormsSectionsEquiv g hU' hW' h' p
        ((Hom.relativeDifferentialForms g p).presheaf.map (homOfLE hUU).op η) =
      ExteriorAlgebra.powMapₛₗ p (X.presheaf.map (homOfLE hUU).op).hom
        (letI := (g.appLE W U h).hom.toAlgebra;
          letI := (g.appLE W' U' h').hom.toAlgebra;
          Stacks.KaehlerDifferentialSquare.map (algebraMap_restrict_comm h h' hUU hWW))
        (relativeFormsSectionsEquiv g hU hW h p η) :=
  let := (g.appLE W U h).hom.toAlgebra
  let := (g.appLE W' U' h').hom.toAlgebra
  relativeFormsSectionsEquiv_restrict hU hW h hU' hW' h' hUU p _
    (Stacks.KaehlerDifferentialSquare.map_D (algebraMap_restrict_comm h h' hUU hWW)) η

end AlgebraicGeometry.Scheme

/-! ### The absolute-to-relative comparison -/

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra)

variable {X S : Scheme.{u}} (g : X ⟶ S)

/-- The square of `g` over the morphisms to `Spec ℤ` commutes. -/
theorem id_comp_toSpecZ_eq : 𝟙 X ≫ X.toSpecZ = g ≫ S.toSpecZ :=
  specULiftZIsTerminal.hom_ext _ _

/-- **The canonical map `Ω_{X/ℤ} ⟶ Ω_{X/S}`** from the absolute to the relative differentials of
`g : X ⟶ S`: the canonical map of Tag 01UV of the square of `g` over `Spec ℤ`, read through
`(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def absoluteToRelativeDifferentials :
    relativeDifferentials X.toSpecZ ⟶ relativeDifferentials g :=
  (Scheme.Modules.pullbackId X).inv.app (relativeDifferentials X.toSpecZ) ≫
    relativeDifferentialsMap (𝟙 X) X.toSpecZ g S.toSpecZ (id_comp_toSpecZ_eq g)

/-- `absoluteToRelativeDifferentials` carries the universal absolute differential `d b` to the
universal relative differential `d b`. -/
theorem absoluteToRelativeDifferentials_app_d (V : X.Opens) (b : Γ(X, V)) :
    (absoluteToRelativeDifferentials g).app V ((universalRelativeDerivation X.toSpecZ).d b) =
      (universalRelativeDerivation g).d b := by
  have hd := (isRelativeDifferentialsMap_iff_eq (𝟙 X) X.toSpecZ g S.toSpecZ
    (id_comp_toSpecZ_eq g) _).mpr rfl V b
  refine (pullbackId_adjoint_apply _ _ _ V _).symm.trans (hd.trans ?_)
  rw [Scheme.Hom.id_app]
  rfl

/-- **The canonical map `Ω^n_{X/ℤ} ⟶ Ω^n_{X/S}`** from absolute to relative differential forms:
the map on degree-`n` exterior powers induced by `absoluteToRelativeDifferentials`. -/
noncomputable abbrev absoluteToRelativeFormsMap (n : ℤ) :
    absoluteDifferentialForms X n ⟶ relativeDifferentialForms g n :=
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ).pieceMap
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) (absoluteToRelativeDifferentials g) n

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra)

variable {X S : Scheme.{u}} (g : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {W : S.Opens}
  (hW : IsAffineOpen W) (h : U ≤ g ⁻¹ᵁ W)

/-- On sections over an affine chart, `Ω_{X/ℤ} ⟶ Ω_{X/S}` is the canonical surjection
`Ω[Γ(X, U)⁄ℤ] → Ω[Γ(X, U)⁄Γ(S, W)]`. -/
theorem relativeDifferentialsSectionsEquiv_absoluteToRelativeDifferentials :
    letI := (g.appLE W U h).hom.toAlgebra
    (relativeDifferentialsSectionsEquiv g hU hW h).toLinearMap ∘ₗ
        Scheme.Modules.sectionsLinearMap (g.absoluteToRelativeDifferentials) U =
      KaehlerDifferential.map ℤ Γ(S, W) Γ(X, U) Γ(X, U) ∘ₗ
        (absoluteDifferentialsSectionsEquiv X hU).toLinearMap := by
  let := (g.appLE W U h).hom.toAlgebra
  refine LinearMap.ext_on (span_range_universalRelativeDerivation_d X hU) ?_
  rintro _ ⟨b, rfl⟩
  change relativeDifferentialsSectionsEquiv g hU hW h
      ((g.absoluteToRelativeDifferentials).app U
        ((Hom.universalRelativeDerivation X.toSpecZ).d b)) =
    KaehlerDifferential.map ℤ Γ(S, W) Γ(X, U) Γ(X, U)
      (absoluteDifferentialsSectionsEquiv X hU ((Hom.universalRelativeDerivation X.toSpecZ).d b))
  rw [Hom.absoluteToRelativeDifferentials_app_d, relativeDifferentialsSectionsEquiv_d,
    absoluteDifferentialsSectionsEquiv_d, KaehlerDifferential.map_D]
  rfl

/-- **The absolute-to-relative comparison of forms on an affine chart** is
`KaehlerDifferential.absoluteToRelative`: through `absoluteFormsSectionsEquiv` and
`relativeFormsSectionsEquiv`, the sections over `U` of `Ω^p_{X/ℤ} ⟶ Ω^p_{X/S}` are
`Ω^p_{Γ(X, U)/ℤ} → Ω^p_{Γ(X, U)/Γ(S, W)}`. -/
theorem relativeFormsSectionsEquiv_absoluteToRelativeFormsMap (p : ℕ)
    (ω : Γ(absoluteDifferentialForms X p, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h p ((g.absoluteToRelativeFormsMap p).app U ω) =
      KaehlerDifferential.absoluteToRelative Γ(S, W) Γ(X, U) p
        (absoluteFormsSectionsEquiv X hU p ω) := by
  let := (g.appLE W U h).hom.toAlgebra
  have hnat := congr($(affineOpenExteriorPowerΓIso_conj_pieceMap hU
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ)
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
    (φ := g.absoluteToRelativeDifferentials) p) ω)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply] at hnat
  have key := relativeDifferentialsSectionsEquiv_absoluteToRelativeDifferentials g hU hW h
  refine (relativeFormsSectionsEquiv_apply_hom g hU hW h p _).trans ?_
  refine (congrArg (exteriorPower.map p (relativeDifferentialsSectionsEquiv g hU hW h).toLinearMap)
    ((congrArg (affineOpenExteriorPowerΓIso (Hom.relativeDifferentials g) hU
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) p).hom.hom
        (Scheme.Modules.sectionsLinearMap_apply _ U ω).symm).trans hnat)).trans ?_
  refine (LinearMap.congr_fun (exteriorPower.map_comp (n := p) _ _) _).symm.trans ?_
  refine (congrArg (fun L => exteriorPower.map p L
    ((affineOpenExteriorPowerΓIso (Hom.relativeDifferentials X.toSpecZ) hU
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ) p).hom.hom ω)) key).trans ?_
  refine (LinearMap.congr_fun (exteriorPower.map_comp (n := p) _ _) _).trans ?_
  exact congrArg (KaehlerDifferential.absoluteToRelative Γ(S, W) Γ(X, U) p)
    (absoluteFormsSectionsEquiv_apply_hom X hU p ω).symm

end AlgebraicGeometry.Scheme

/-! ### The relative de Rham differential -/

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra relativeDifferentialFormsGenerator)

variable {X S : Scheme.{u}} (g : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {W : S.Opens}
  (hW : IsAffineOpen W) (h : U ≤ g ⁻¹ᵁ W)

/-- The identification of relative forms on an affine chart carries the ordered product of the
degree-one forms `d c₁, …, d c_p` of `Ω^•_{X/S}` to the wedge `D c₁ ∧ ⋯ ∧ D c_p`. -/
theorem relativeFormsSectionsEquiv_homogeneousProd_d (p : ℕ) (c : Fin p → Γ(X, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h p
        ((Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun i => (relativeDifferentialFormsGenerator g).val.app (op U)
            ((Hom.universalRelativeDerivation g).d (c i))) =
      exteriorPower.ιMulti Γ(X, U) p fun i => KaehlerDifferential.D Γ(S, W) Γ(X, U) (c i) := by
  let := (g.appLE W U h).hom.toAlgebra
  refine (relativeFormsSectionsEquiv_apply_hom g hU hW h p _).trans ?_
  refine (congrArg (exteriorPower.map p (relativeDifferentialsSectionsEquiv g hU hW h).toLinearMap)
    (affineOpenExteriorPowerΓIso_hom_homogeneousProd (Hom.relativeDifferentials g) hU
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) p _)).trans ?_
  refine (exteriorPower.map_apply_ιMulti _ _).trans ?_
  exact congrArg (exteriorPower.ιMulti Γ(X, U) p)
    (funext fun i => relativeDifferentialsSectionsEquiv_d g hU hW h (c i))

/-- The exact wedges of the de Rham package of `g` are the ordered products of the degree-one
forms `d cᵢ` of `Ω^•_{X/S}`, by definition. -/
private theorem homogeneousProd_exactOne_eq_relative (p : ℕ) (c : Fin p → Γ(X, U)) :
    (Hom.deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProd
        (op U) p (fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras g) (op U) (c i)) =
      (Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun i => (relativeDifferentialFormsGenerator g).val.app (op U)
            ((Hom.universalRelativeDerivation g).d (c i)) := rfl

/-- **The identification of relative forms on an affine chart, on an exact wedge**: it carries
`d c₁ ∧ ⋯ ∧ d c_p`, in the spelling of the de Rham package of `g`, to `D c₁ ∧ ⋯ ∧ D c_p`. -/
theorem relativeFormsSectionsEquiv_exactWedge (p : ℕ) (c : Fin p → Γ(X, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h p
        ((Hom.deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProd
          (op U) p fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras g) (op U) (c i)) =
      exteriorPower.ιMulti Γ(X, U) p fun i => KaehlerDifferential.D Γ(S, W) Γ(X, U) (c i) :=
  (congrArg (relativeFormsSectionsEquiv g hU hW h p)
    (homogeneousProd_exactOne_eq_relative g p c)).trans
    (relativeFormsSectionsEquiv_homogeneousProd_d g hU hW h p c)

/-- The de Rham rule of `g.deRhamComplex` on sections over `U`, with the exact wedges written as
ordered products: `d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`. -/
theorem deRhamComplex_d_smul_homogeneousProd (p : ℕ)
    (b : Fin (p + 1) → ↥(X.sheaf.obj.obj (op U))) :
    (g.deRhamComplex.d p (p + 1)).val.app (op U)
        (b 0 • (Hom.deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras g) (op U) (b i.succ)) =
      (Hom.deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProd (op U) (p + 1)
        fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras g) (op U) (b i) := by
  have h0 := Hom.deRhamComplex_d_homogeneousProdLeft g (op U) p b
  rw [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd,
    Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd] at h0
  exact h0

/-- The differential of `g.deRhamComplex` on sections over `U` is additive. -/
theorem deRhamComplex_d_app_add (p : ℕ) (s t : Γ(Hom.relativeDifferentialForms g p, U)) :
    (g.deRhamComplex.d p (p + 1)).val.app (op U) (s + t) =
      (g.deRhamComplex.d p (p + 1)).val.app (op U) s +
        (g.deRhamComplex.d p (p + 1)).val.app (op U) t :=
  map_add ((g.deRhamComplex.d p (p + 1)).val.app (op U)).hom s t

/-- The elements `b₀ · D b₁ ∧ ⋯ ∧ D b_p` generate `⋀ᵖ Ω[Γ(X, U)⁄Γ(S, W)]` as an additive
group. -/
theorem closure_smul_ιMulti_D_relative (p : ℕ) :
    letI := (g.appLE W U h).hom.toAlgebra
    AddSubgroup.closure (Set.range fun b : Fin (p + 1) → Γ(X, U) =>
      b 0 • exteriorPower.ιMulti Γ(X, U) p fun i =>
        KaehlerDifferential.D Γ(S, W) Γ(X, U) (b i.succ)) = ⊤ := by
  let := (g.appLE W U h).hom.toAlgebra
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  convert congrArg Submodule.toAddSubgroup (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
    (KaehlerDifferential.D Γ(S, W) Γ(X, U))
    (KaehlerDifferential.span_range_derivation Γ(S, W) Γ(X, U)) p)

/-- The relative de Rham differential on an affine chart, on `b₀ · D b₁ ∧ ⋯ ∧ D b_p`: through
the identification it is `D b₀ ∧ D b₁ ∧ ⋯ ∧ D b_p`. -/
theorem relativeFormsSectionsEquiv_deRhamComplex_d_smul_ιMulti (p : ℕ)
    (b : Fin (p + 1) → Γ(X, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h (p + 1)
        ((g.deRhamComplex.d p (p + 1)).val.app (op U)
          ((relativeFormsSectionsEquiv g hU hW h p).symm
            (b 0 • exteriorPower.ιMulti Γ(X, U) p fun i =>
              KaehlerDifferential.D Γ(S, W) Γ(X, U) (b i.succ)))) =
      exteriorPower.ιMulti Γ(X, U) (p + 1) fun i =>
        KaehlerDifferential.D Γ(S, W) Γ(X, U) (b i) := by
  have h0 := deRhamComplex_d_smul_homogeneousProd g p b
  have h1 := congrArg (relativeFormsSectionsEquiv g hU hW h (p + 1)) h0
  have h2 := relativeFormsSectionsEquiv_exactWedge g hU hW h (p + 1) b
  have h3 := (relativeFormsSectionsEquiv g hU hW h p).map_smul (b 0)
    ((Hom.deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProd
        (op U) p fun i => SheafOfModules.exactOne (Hom.deRhamAlgebras g) (op U) (b i.succ))
  rw [relativeFormsSectionsEquiv_exactWedge] at h3
  have h12 := h1.trans (by convert h2 using 3)
  have hs := (LinearEquiv.symm_apply_eq _).mpr h3.symm
  refine Eq.trans ?_ h12
  refine congrArg (relativeFormsSectionsEquiv g hU hW h (p + 1)) ?_
  refine congrArg ((g.deRhamComplex.d p (p + 1)).val.app (op U)).hom ?_
  refine hs.trans ?_
  congr 1

/-- **The relative de Rham complex on an affine chart is the de Rham complex of the ring map**:
the identification `Γ(Ω^p_{X/S}, U) ≃ ⋀ᵖ Ω[Γ(X, U)⁄Γ(S, W)]` carries the differential of
`g.deRhamComplex`, evaluated on sections over `U`, to `KaehlerDifferential.deRhamDifferential`
of `Γ(X, U)` over `Γ(S, W)`. -/
theorem relativeFormsSectionsEquiv_deRhamComplex_d (p : ℕ)
    (ω : Γ(Hom.relativeDifferentialForms g p, U)) :
    letI := (g.appLE W U h).hom.toAlgebra
    relativeFormsSectionsEquiv g hU hW h (p + 1)
        ((g.deRhamComplex.d p (p + 1)).val.app (op U) ω) =
      KaehlerDifferential.deRhamDifferential (A := Γ(S, W)) p
        (relativeFormsSectionsEquiv g hU hW h p ω) := by
  obtain ⟨ξ, rfl⟩ := (relativeFormsSectionsEquiv g hU hW h p).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  let F : (let := (g.appLE W U h).hom.toAlgebra; ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄Γ(S, W)]) →+
      (let := (g.appLE W U h).hom.toAlgebra; ⋀[Γ(X, U)]^(p + 1) Ω[Γ(X, U)⁄Γ(S, W)]) :=
    { toFun := fun z => relativeFormsSectionsEquiv g hU hW h (p + 1)
        ((g.deRhamComplex.d p (p + 1)).val.app (op U)
          ((relativeFormsSectionsEquiv g hU hW h p).symm z))
      map_zero' := by
        refine Eq.trans ?_ (map_zero (relativeFormsSectionsEquiv g hU hW h (p + 1)))
        refine congrArg (relativeFormsSectionsEquiv g hU hW h (p + 1)) ?_
        refine Eq.trans ?_ (map_zero ((g.deRhamComplex.d p (p + 1)).val.app (op U)).hom)
        refine congrArg ((g.deRhamComplex.d p (p + 1)).val.app (op U)).hom ?_
        exact (relativeFormsSectionsEquiv g hU hW h p).symm.map_zero
      map_add' := fun x y => by
        refine Eq.trans ?_ (map_add (relativeFormsSectionsEquiv g hU hW h (p + 1)) _ _)
        refine congrArg (relativeFormsSectionsEquiv g hU hW h (p + 1)) ?_
        refine Eq.trans ?_ (deRhamComplex_d_app_add g p _ _)
        refine congrArg ((g.deRhamComplex.d p (p + 1)).val.app (op U)).hom ?_
        exact (relativeFormsSectionsEquiv g hU hW h p).symm.map_add x y }
  let G := (@KaehlerDifferential.deRhamDifferential Γ(S, W) Γ(X, U) _ _
      (g.appLE W U h).hom.toAlgebra p).toAddMonoidHom
  have hFG : F = G := AddMonoidHom.eq_of_eqOn_dense (closure_smul_ιMulti_D_relative g h p)
    (by
      rintro _ ⟨b, rfl⟩
      have hm := relativeFormsSectionsEquiv_deRhamComplex_d_smul_ιMulti g hU hW h p b
      have hd := @KaehlerDifferential.deRhamDifferential_smul_ιMulti_D Γ(S, W) Γ(X, U) _ _
        (g.appLE W U h).hom.toAlgebra p b
      dsimp only
      simp only [F, G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.toAddMonoidHom_coe, hm, hd])
  have hξ := DFunLike.congr_fun hFG ξ
  simp only [F, G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.toAddMonoidHom_coe] at hξ
  simp only [hξ]

end AlgebraicGeometry.Scheme

end
