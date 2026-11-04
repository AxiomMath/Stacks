module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorSections

/-!
# The tensor identity for the presheaves of sectionwise localizations

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. The components
`AlgebraicGeometry.RingedSite.awayTensorSectionIso` of `AwayTensorSections.lean` identify
`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪(U)[1/g|_U]` with `𝒪(U)[1/(f g)|_U]` over every object `U`. This file
proves those components natural in `U`, so that they assemble into an isomorphism

`𝒪[1/f] ⊗_𝒪 𝒪[1/g] = 𝒪[1/(f g)]`

of presheaves of `𝒪`-modules.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayTensorPresheafIso`: **the identity above**, as an
  isomorphism of presheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.awayTensorSectionIso_naturality`: the comparison of
  `AwayTensorSections.lean` is natural in the object of the site.
* `AlgebraicGeometry.RingedSite.awayPresheaf_map_comp_toMulLeft` and
  `AlgebraicGeometry.RingedSite.awayPresheaf_map_comp_toMulRight`: the two canonical maps
  `𝒪(U)[1/f] ⟶ 𝒪(U)[1/(f g)]` and `𝒪(U)[1/g] ⟶ 𝒪(U)[1/(f g)]` commute with restriction.

## Implementation notes

The naturality square is not formal. Its leg
`(MonoidalCategoryStruct.tensorObj _ _).map i` is only given as a map of modules, so the
uniqueness of algebra maps out of a localization — `IsLocalization.algHom_subsingleton`, which is
what makes the two comparisons of `IsLocalization.Away.tensorProductAlgEquiv_tmul` agree — does
not apply to the square itself. The square is therefore checked on pure tensors, by
`TensorProduct.ext'`: on `x ⊗ₜ y` both legs are computed by
`PresheafOfModules.Monoidal.tensorObj_map_tmul` and
`IsLocalization.Away.tensorProductAlgEquiv_tmul`, and what remains is that the two canonical maps
into `𝒪(U)[1/(f g)]` commute with restriction. *That* is formal: both composites with the
localization map `𝒪(U) ⟶ 𝒪(U)[1/f]` are the canonical map `𝒪(U) ⟶ 𝒪(V)[1/(f g)]`, by the
naturality of `AlgebraicGeometry.RingedSite.toAwayPresheaf` and `AlgHom.commutes`, so
`IsLocalization.ringHom_ext` identifies them.

`AwayTensorNaturality.lean` proves the analogous naturality in the *second global section*, by
the same device: there the two canonical maps are compared by
`IsLocalization.algHom_subsingleton`, since both legs of that square are maps of
`𝒪(U)`-algebras.

Every statement here carries the algebra instances
`((toAwayPresheaf f).app U).hom.toAlgebra` as a `letI` preamble, and repeats it in the proof.
This is forced, for the reason recorded in `AwayTensorSections.lean`: that instance's module
structure is *definitionally* the one `awayModulePresheaf` carries, while the instance that
search finds is equal to it only propositionally. Repeating the preamble in the proof is needed
because the instances a `letI` in a statement provides are not in the local instance cache while
the proof term is elaborated, so the instance arguments of the lemmas used would otherwise be
resynthesized to the wrong ones.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.SheafOfModules
open IsLocalization.Away

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- Restriction commutes with the canonical map into the presheaf of sectionwise
localizations. -/
theorem awayPresheaf_map_toAwayPresheaf
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    {U V : X.Cᵒᵖ} (i : U ⟶ V) (a : X.O.obj.obj U) :
    ((awayPresheaf h).map i).hom (((toAwayPresheaf h).app U).hom a) =
      ((toAwayPresheaf h).app V).hom ((X.O.obj.map i).hom a) :=
  (RingHom.congr_fun (congrArg CommRingCat.Hom.hom ((toAwayPresheaf h).naturality i)) a).symm

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- Restriction commutes with the canonical map, read as the algebra map of the algebra
structure the presheaf of modules of sectionwise localizations carries. -/
theorem awayPresheaf_map_algebraMap
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    {U V : X.Cᵒᵖ} (i : U ⟶ V) (a : X.O.obj.obj U) :
    letI := ((toAwayPresheaf h).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h).app V).hom.toAlgebra
    ((awayPresheaf h).map i).hom (algebraMap _ _ a) =
      algebraMap _ _ ((X.O.obj.map i).hom a) :=
  awayPresheaf_map_toAwayPresheaf X h i a

variable (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- **The comparison on sections carries a pure tensor to the product of the images of its two
factors**, which is what pins it down: it is the only `𝒪(U)`-algebra map out of a localization of
`𝒪(U)`. -/
theorem awayTensorSectionIso_hom_tmul (U : X.Cᵒᵖ)
    (x : (awayPresheaf f).obj U) (y : (awayPresheaf g).obj U) :
    letI := ((toAwayPresheaf f).app U).hom.toAlgebra
    letI := ((toAwayPresheaf g).app U).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
    letI := isLocalizationAway_away X f U
    letI := isLocalizationAway_away X g U
    letI := isLocalizationAway_away_mul X f g U
    toMulLeft (globalSectionVal f U) (globalSectionVal g U) _
          ((awayPresheaf (mulGlobalSection X f g)).obj U) x *
        toMulRight (globalSectionVal f U) (globalSectionVal g U) _
          ((awayPresheaf (mulGlobalSection X f g)).obj U) y =
      (awayTensorSectionIso X f g U).hom.hom (x ⊗ₜ y) :=
  let := ((toAwayPresheaf f).app U).hom.toAlgebra
  let := ((toAwayPresheaf g).app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  let := isLocalizationAway_away X f U
  let := isLocalizationAway_away X g U
  let := isLocalizationAway_away_mul X f g U
  (tensorProductAlgEquiv_tmul _ _ _ _ _ x y).symm

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- **The canonical map `𝒪(U)[1/f] ⟶ 𝒪(U)[1/(f g)]` commutes with restriction.** Both
composites with the localization map out of `𝒪(U)` are the canonical map `𝒪(U) ⟶ 𝒪(V)[1/(f g)]`,
so `IsLocalization.ringHom_ext` identifies them. -/
theorem awayPresheaf_map_comp_toMulLeft {U V : X.Cᵒᵖ} (i : U ⟶ V) :
    letI := ((toAwayPresheaf f).app U).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
    letI := ((toAwayPresheaf f).app V).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app V).hom.toAlgebra
    letI := isLocalizationAway_away X f U
    letI := isLocalizationAway_away_mul X f g U
    letI := isLocalizationAway_away X f V
    letI := isLocalizationAway_away_mul X f g V
    (toMulLeft (globalSectionVal f V) (globalSectionVal g V) _
          ((awayPresheaf (mulGlobalSection X f g)).obj V)).toRingHom.comp
        ((awayPresheaf f).map i).hom =
      ((awayPresheaf (mulGlobalSection X f g)).map i).hom.comp
        (toMulLeft (globalSectionVal f U) (globalSectionVal g U) _
          ((awayPresheaf (mulGlobalSection X f g)).obj U)).toRingHom := by
  let := ((toAwayPresheaf f).app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  let := ((toAwayPresheaf f).app V).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app V).hom.toAlgebra
  let := isLocalizationAway_away X f U
  let := isLocalizationAway_away_mul X f g U
  let := isLocalizationAway_away X f V
  let := isLocalizationAway_away_mul X f g V
  refine IsLocalization.ringHom_ext (Submonoid.powers (globalSectionVal f U))
    (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    awayPresheaf_map_algebraMap, AlgHom.commutes]

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- **The canonical map `𝒪(U)[1/g] ⟶ 𝒪(U)[1/(f g)]` commutes with restriction.** -/
theorem awayPresheaf_map_comp_toMulRight {U V : X.Cᵒᵖ} (i : U ⟶ V) :
    letI := ((toAwayPresheaf g).app U).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
    letI := ((toAwayPresheaf g).app V).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app V).hom.toAlgebra
    letI := isLocalizationAway_away X g U
    letI := isLocalizationAway_away_mul X f g U
    letI := isLocalizationAway_away X g V
    letI := isLocalizationAway_away_mul X f g V
    (toMulRight (globalSectionVal f V) (globalSectionVal g V) _
          ((awayPresheaf (mulGlobalSection X f g)).obj V)).toRingHom.comp
        ((awayPresheaf g).map i).hom =
      ((awayPresheaf (mulGlobalSection X f g)).map i).hom.comp
        (toMulRight (globalSectionVal f U) (globalSectionVal g U) _
          ((awayPresheaf (mulGlobalSection X f g)).obj U)).toRingHom := by
  let := ((toAwayPresheaf g).app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  let := ((toAwayPresheaf g).app V).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app V).hom.toAlgebra
  let := isLocalizationAway_away X g U
  let := isLocalizationAway_away_mul X f g U
  let := isLocalizationAway_away X g V
  let := isLocalizationAway_away_mul X f g V
  refine IsLocalization.ringHom_ext (Submonoid.powers (globalSectionVal g U))
    (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    awayPresheaf_map_algebraMap, AlgHom.commutes]

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- **The comparison of `AwayTensorSections.lean` is natural in the object of the site.** -/
theorem awayTensorSectionIso_naturality {U V : X.Cᵒᵖ} (i : U ⟶ V) :
    (MonoidalCategoryStruct.tensorObj (awayModulePresheafAlt X f)
          (awayModulePresheafAlt X g)).map i ≫
        (ModuleCat.restrictScalars (X.O.obj.map i).hom).map (awayTensorSectionIso X f g V).hom =
      (awayTensorSectionIso X f g U).hom ≫
        (awayModulePresheafAlt X (mulGlobalSection X f g)).map i := by
  let := ((toAwayPresheaf f).app U).hom.toAlgebra
  let := ((toAwayPresheaf g).app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  let := ((toAwayPresheaf f).app V).hom.toAlgebra
  let := ((toAwayPresheaf g).app V).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app V).hom.toAlgebra
  let := isLocalizationAway_away X f U
  let := isLocalizationAway_away X g U
  let := isLocalizationAway_away_mul X f g U
  let := isLocalizationAway_away X f V
  let := isLocalizationAway_away X g V
  let := isLocalizationAway_away_mul X f g V
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_)
  exact (awayTensorSectionIso_hom_tmul X f g V _ _).symm.trans
    ((congrArg₂ (· * ·)
        (RingHom.congr_fun (awayPresheaf_map_comp_toMulLeft X f g i) x)
        (RingHom.congr_fun (awayPresheaf_map_comp_toMulRight X f g i) y)).trans
      ((map_mul ((awayPresheaf (mulGlobalSection X f g)).map i).hom _ _).symm.trans
        (congrArg (fun z => ((awayPresheaf (mulGlobalSection X f g)).map i).hom z)
          (awayTensorSectionIso_hom_tmul X f g U x y))))

/-- **`𝒪[1/f] ⊗_𝒪 𝒪[1/g] = 𝒪[1/(f g)]` as presheaves of `𝒪`-modules.** -/
def awayTensorPresheafIso :
    MonoidalCategoryStruct.tensorObj (awayModulePresheafAlt X f) (awayModulePresheafAlt X g) ≅
      awayModulePresheafAlt X (mulGlobalSection X f g) :=
  PresheafOfModules.isoMk (awayTensorSectionIso X f g)
    fun {_ _} i => awayTensorSectionIso_naturality X f g i

end AlgebraicGeometry.RingedSite

end
