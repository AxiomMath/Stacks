module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitStalk
public import StacksFrontier.AlgebraicGeometry.Pullback.OpenImmersionPushforwardStalkLinear

/-!
# The stalk of `j_*𝒪_U` and the unit germ

Let `j : U → X` be the open immersion of the section locus of a section `s` of a coherent sheaf
`F` on a normal integral locally Noetherian scheme `X`, and let `U_x` be its base change to
`Spec 𝒪_{X, x}`. This file constructs an `𝒪_{X, x}`-linear equivalence

`e : (j_*𝒪_U)_x ≃ₗ Γ(U_x, 𝒪_{U_x})` with `e (germ of the unit section) = 1`,

where the left side is the stalk of the module `j_*𝒪_U` over the local ring, and deduces the
pointwise colimit clause `Γ(U_x, 𝒪_{U_x}) = colim_n ℱ^{[n]}_x` from the sheaf-level one.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictReflexivePowerUnitIso_zero_hom`: at `0` the
  trivialization `ℱ^{[n]}|_U ≅ 𝒪_U` is the canonical `𝒪_X|_U ≅ 𝒪_U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.cocone_ι_app_zero_app_top_one`: the cocone's leg at
  `0` carries the unit section of `𝒪_X` to the unit section of `𝒪_U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.modulesStalkFunctor_map_cocone_ι_app_zero_unit`: the
  stalk of that leg carries `reflexivePowerUnit F x` to the germ of the unit section.
* `Stacks.AlgebraicGeometry.ReflexivePowers.exists_linearEquiv_stalk_pushforwardCocone`: the
  equivalence `e` above.
* `Stacks.AlgebraicGeometry.ReflexivePowers.nonempty_isStalkColimit_of_isColimit` and
  `Stacks.AlgebraicGeometry.ReflexivePowers.nonempty_isStalkColimit_of_isColimit_of_isAffineHom`:
  if the cocone with vertex `j_*𝒪_U` is colimiting, then `Γ(U_x, 𝒪_{U_x})` is the colimit of the
  stalks `ℱ^{[n]}_x`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBR](https://stacks.math.columbia.edu/tag/0EBR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

open Stacks.ModuleSkyscraper (modulesStalkFunctor)
open Stacks.AlgebraicGeometry.SectionLocusAffine (IsStalkColimit isStalkColimitOfIsColimit
  specRes stalkLocus)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)
  [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme]

/-- At `0` the trivialization `ℱ^{[n]}|_U ≅ 𝒪_U` is the canonical isomorphism
`𝒪_X|_U ≅ 𝒪_U`. -/
theorem restrictReflexivePowerUnitIso_zero_hom :
    (restrictReflexivePowerUnitIso F s 0).hom =
      (Scheme.Modules.restrictUnitIso (sectionIsomorphismOpen X F s).ι).hom := by
  rw [restrictReflexivePowerUnitIso_eq, restrictPowerIso_zero, tensorPowerUnitIso_zero]
  exact Category.comp_id _

/-- On sections over `⊤`, the leg at `0` of the cocone `reflexivePowerSystemPushforwardCocone`
carries the unit section of `𝒪_X` to the unit section of `𝒪_U`. -/
theorem cocone_ι_app_zero_app_top_one :
    ((reflexivePowerSystemPushforwardCocone F s).ι.app 0).app (⊤ : X.Opens)
        (1 : Γ(X, (⊤ : X.Opens))) =
      (1 : Γ((sectionIsomorphismOpen X F s).toScheme,
        (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (⊤ : X.Opens))) := by
  rw [reflexivePowerSystemPushforwardCocone_ι_app_eq_unit_comp,
    restrictReflexivePowerUnitIso_zero_hom]
  change (Scheme.Modules.restrictUnitIso (sectionIsomorphismOpen X F s).ι).hom.app
      ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (⊤ : X.Opens))
      ((X.presheaf.map
        (homOfLE ((sectionIsomorphismOpen X F s).ι.image_preimage_le ⊤)).op).hom
          (1 : Γ(X, (⊤ : X.Opens)))) =
      (1 : Γ((sectionIsomorphismOpen X F s).toScheme,
        (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (⊤ : X.Opens)))
  rw [map_one]
  exact map_one ((sectionIsomorphismOpen X F s).ι.appIso
    ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (⊤ : X.Opens))).hom.hom

/-- The stalk at `x` of the leg at `0` of the cocone carries `reflexivePowerUnit F x` to the germ
of the unit section of `𝒪_U`. -/
theorem modulesStalkFunctor_map_cocone_ι_app_zero_unit (x : X) :
    ((modulesStalkFunctor X x).map ((reflexivePowerSystemPushforwardCocone F s).ι.app 0)).hom
        (reflexivePowerUnit F x) =
      (pushforwardUnitGerm (sectionIsomorphismOpen X F s) x ⊤ trivial).hom
        (1 : Γ((sectionIsomorphismOpen X F s).toScheme,
          (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (⊤ : X.Opens))) :=
  (Stacks.ModuleSkyscraper.modulesStalkFunctor_map_hom_apply X x _ _).trans
    ((Stacks.ModuleSkyscraper.stalkMapLinear_germ
          ((reflexivePowerSystemPushforwardCocone F s).ι.app 0).val x ⊤ trivial
          (1 : Γ(X, (⊤ : X.Opens)))).trans
      (congrArg (pushforwardUnitGerm (sectionIsomorphismOpen X F s) x ⊤ trivial).hom
        (cocone_ι_app_zero_app_top_one F s)))

/-- If `j` is quasi-compact and the `𝒪_{X, x}`-algebra structure on `Γ(U_x, 𝒪_{U_x})` is the
canonical one (`halg`), there is an `𝒪_{X, x}`-linear equivalence from the stalk at `x` of the
cocone's vertex `j_*𝒪_U` onto `Γ(U_x, 𝒪_{U_x})` carrying the image of the unit germ under the
leg at `0` to `1`. -/
theorem exists_linearEquiv_stalk_pushforwardCocone
    [QuasiCompact (sectionIsomorphismOpen X F s).ι] (x : X)
    [Algebra ↑(X.presheaf.stalk x) ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x)]
    (halg : algebraMap ↑(X.presheaf.stalk x)
        ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x) =
      (specRes (X.presheaf.stalk x) (stalkLocus X F s x)).hom) :
    ∃ e : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (reflexivePowerSystemPushforwardCocone F s).pt.val.presheaf x) ≃ₗ[
          ↑(X.presheaf.stalk x)] ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x),
      e (((modulesStalkFunctor X x).map
        ((reflexivePowerSystemPushforwardCocone F s).ι.app 0)).hom
          (reflexivePowerUnit F x)) = 1 := by
  obtain ⟨e, he⟩ := AlgebraicGeometry.exists_linearEquiv_pushforwardUnitStalk_of_quasiCompact
    (sectionIsomorphismOpen X F s) x halg
  exact ⟨e, (congrArg e (modulesStalkFunctor_map_cocone_ι_app_zero_unit F s x)).trans he⟩

/-- If the cocone `reflexivePowerSystemPushforwardCocone` is colimiting, `j` is quasi-compact and
the `𝒪_{X, x}`-algebra structure on `Γ(U_x, 𝒪_{U_x})` is the canonical one (`halg`), then
`Γ(U_x, 𝒪_{U_x})` is a colimit of the stalks at `x` of the reflexive powers. -/
theorem nonempty_isStalkColimit_of_isColimit
    (hc : IsColimit (reflexivePowerSystemPushforwardCocone F s))
    [QuasiCompact (sectionIsomorphismOpen X F s).ι] (x : X)
    [Algebra ↑(X.presheaf.stalk x) ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x)]
    (halg : algebraMap ↑(X.presheaf.stalk x)
        ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x) =
      (specRes (X.presheaf.stalk x) (stalkLocus X F s x)).hom) :
    Nonempty (IsStalkColimit F s x ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x)) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_stalk_pushforwardCocone F s x halg
  exact ⟨isStalkColimitOfIsColimit F s x hc _ e he⟩

/-- `nonempty_isStalkColimit_of_isColimit` with the quasi-compactness of `j` replaced by its
affineness. -/
theorem nonempty_isStalkColimit_of_isColimit_of_isAffineHom
    (hc : IsColimit (reflexivePowerSystemPushforwardCocone F s))
    (hj : IsAffineHom (sectionIsomorphismOpen X F s).ι) (x : X)
    [Algebra ↑(X.presheaf.stalk x) ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x)]
    (halg : algebraMap ↑(X.presheaf.stalk x)
        ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x) =
      (specRes (X.presheaf.stalk x) (stalkLocus X F s x)).hom) :
    Nonempty (IsStalkColimit F s x ↑Γ(Spec (X.presheaf.stalk x), stalkLocus X F s x)) :=
  have : IsAffineHom (sectionIsomorphismOpen X F s).ι := hj
  nonempty_isStalkColimit_of_isColimit F s hc x halg

end Stacks.AlgebraicGeometry.ReflexivePowers

end
