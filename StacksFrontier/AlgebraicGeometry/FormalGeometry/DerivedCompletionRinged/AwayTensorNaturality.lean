module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTransitionGeneral

/-!
# `𝒪_g ⊗_𝒪 𝒪_h = 𝒪_{g h}`, naturally in `h`

Let `(𝒞, 𝒪)` be a ringed site and let `g`, `h`, `h'` be global sections of `𝒪` with `h` dividing
`h'` over every object. `AwayTensorSheaf.lean` identifies `𝒪_g ⊗_𝒪 𝒪_h` with `𝒪_{g h}` at a fixed
pair of sections; this file proves that identification **natural in the second section**: the
square formed by it and the transition maps `𝒪_h ⟶ 𝒪_{h'}`, `𝒪_{g h} ⟶ 𝒪_{g h'}` commutes.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayPresheafTransitionOfIsUnit`: the transition map
  `𝒪[1/h] ⟶ 𝒪[1/h']` of presheaves of rings, built sectionwise from the universal property of a
  localization, with `AlgebraicGeometry.RingedSite.awayModulePresheafTransitionAlt` its reading
  as a map of presheaves of `𝒪`-modules and
  `AlgebraicGeometry.RingedSite.awayPresheafTransitionAlgHomOfIsUnit` its reading on sections as a
  map of `𝒪(U)`-algebras.

## Main results

* `AlgebraicGeometry.RingedSite.awayTensorSectionIso_naturality_right`: the comparison on
  sections is natural in the second global section.
* `AlgebraicGeometry.RingedSite.awayTensorPresheafIso_naturality_right` and
  `AlgebraicGeometry.RingedSite.awayTensorPresheafIso_naturality_tensorHom`: so is
  `𝒪[1/g] ⊗_𝒪 𝒪[1/h] = 𝒪[1/(g h)]`, as presheaves of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule_naturality` and
  `AlgebraicGeometry.RingedSite.awayModuleSheafificationIso_naturality`: the identification of
  `𝒪_h` with the sheafification of the presheaf of sectionwise localizations is natural in `h`.
* `AlgebraicGeometry.RingedSite.awayTensorSheafIso_naturality_right`:
  **`𝒪_g ⊗_𝒪 𝒪_h ≅ 𝒪_{g h}` is natural in `h`.**
* `AlgebraicGeometry.RingedSite.isIso_sheafTensor_map_awayModuleMapOfComp`: consequently
  tensoring with `𝒪_g` inverts a transition map `𝒪_h ⟶ 𝒪_{h'}` as soon as the transition
  `𝒪_{g h} ⟶ 𝒪_{g h'}` is invertible.
* `AlgebraicGeometry.RingedSite.isUnit_toAwayPresheaf_of_dvd` and
  `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_of_dvd`: a global section dividing `h'` over
  every object becomes invertible in `𝒪[1/h']`, resp. in `𝒪_{h'}`.

## Implementation notes

The hypothesis is divisibility of the *values* over every object of the site, which is what the
Čech application supplies: the values of `f_S` divide those of `f_T` for `S ⊆ T`, and then the
values of `g f_S` divide those of `g f_T`.

The section-level square is checked on pure tensors, as the naturality in the object of the site
of `AwayTensorPresheaf.lean` is, but the four comparisons it reduces to are all settled by
uniqueness rather than by computation: each is a map of `𝒪(U)`-algebras out of a localization of
`𝒪(U)`, and `IsLocalization.algHom_subsingleton` says there is at most one such map. The
transition map therefore has to be available as an `AlgHom`, which is what
`awayPresheafTransitionAlgHomOfIsUnit` is for.

Those uniqueness statements are taken as local `have`s inside the proof rather than as standalone
lemmas, and that is forced. A standalone lemma must carry the algebra instances in a `letI`
preamble, so its *type* mentions `RingHom.toAlgebra` applied to a map of sections; feeding such a
lemma to `DFunLike.congr_fun` then asks the unifier to compare that instance with the one the
goal carries, and the comparison does not terminate — a four-million-heartbeat budget was not
enough. Inside the proof the instances are local hypotheses, so the same comparisons are
immediate.

The final assembly expands `awayTensorSheafIso` into its four factors and pushes the transition
map through them one at a time with `reassoc_of%`. The middle factor is free: Stacks 0GMW is a
natural isomorphism of bifunctors, so its naturality at `(𝟙, τ)` is exactly the square needed.

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

section Dvd

variable {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}

/-- Every power of `h` is invertible in the sectionwise localization at `h`. -/
theorem isUnit_toAwayPresheaf_self
    (k : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwayPresheaf k).app U).hom (globalSectionVal k U ^ n)) :=
  IsLocalization.map_units ((awayPresheaf k).obj U)
    (⟨globalSectionVal k U ^ n, n, rfl⟩ : (awayMultiplicativeSubpresheaf k).obj U)

/-- **A global section whose value divides that of `h'` becomes invertible in `𝒪[1/h']`**: its
image times the image of the complementary factor is the image of a power of `h'`. -/
theorem isUnit_toAwayPresheaf_of_dvd (U : X.Cᵒᵖ)
    (hd : globalSectionVal h U ∣ globalSectionVal h' U) (n : ℕ) :
    IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)) :=
  isUnit_of_dvd_unit (map_dvd _ (pow_dvd_pow_of_dvd hd n)) (isUnit_toAwayPresheaf_self X h' U n)

/-- **A global section whose value divides that of `h'` becomes invertible in `𝒪_{h'}`.** -/
theorem isUnit_toAwaySheaf_of_dvd (U : X.Cᵒᵖ)
    (hd : globalSectionVal h U ∣ globalSectionVal h' U) (n : ℕ) :
    IsUnit (((toAwaySheaf h').hom.app U).hom (globalSectionVal h U ^ n)) :=
  isUnit_of_dvd_unit (map_dvd _ (pow_dvd_pow_of_dvd hd n)) (isUnit_toAwaySheaf h' U n)

/-- Divisibility of the values is inherited by the products with a fixed global section. -/
theorem dvd_globalSectionVal_mulGlobalSection
    (g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ)
    (hd : globalSectionVal h U ∣ globalSectionVal h' U) :
    globalSectionVal (mulGlobalSection X g h) U ∣
      globalSectionVal (mulGlobalSection X g h') U := by
  rw [globalSectionVal_mulGlobalSection, globalSectionVal_mulGlobalSection]
  exact mul_dvd_mul_left _ hd

end Dvd

section PresheafTransition

variable {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
  (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
    IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))

include hu

/-- The invertibility hypothesis, read at the multiplicative subpresheaf of powers, which is the
shape `IsLocalization.lift` asks for. -/
theorem isUnit_toAwayPresheaf_powers (U : X.Cᵒᵖ)
    (s : (awayMultiplicativeSubpresheaf h).obj U) :
    IsUnit (((toAwayPresheaf h').app U).hom (s : X.O.obj.obj U)) := by
  obtain ⟨n, hn⟩ := s.2
  exact hn ▸ hu U n

/-- The transition map commutes with restriction: both composites with the localization map out
of `𝒪(U)` are the canonical map `𝒪(U) ⟶ 𝒪(V)[1/h']`, so `IsLocalization.ringHom_ext` identifies
them. -/
theorem awayPresheafTransitionOfIsUnit_naturality {U V : X.Cᵒᵖ} (i : U ⟶ V) :
    (IsLocalization.lift (M := (awayMultiplicativeSubpresheaf h).obj V)
          (isUnit_toAwayPresheaf_powers X hu V)).comp ((awayPresheaf h).map i).hom =
      ((awayPresheaf h').map i).hom.comp
        (IsLocalization.lift (M := (awayMultiplicativeSubpresheaf h).obj U)
          (isUnit_toAwayPresheaf_powers X hu U)) := by
  refine IsLocalization.ringHom_ext ((awayMultiplicativeSubpresheaf h).obj U)
    (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply]
  rw [show ((awayPresheaf h).map i).hom
        (algebraMap (X.O.obj.obj U) ((awayPresheaf h).obj U) x) =
      algebraMap (X.O.obj.obj V) ((awayPresheaf h).obj V) ((X.O.obj.map i).hom x) from
    awayPresheaf_map_toAwayPresheaf X h i x, IsLocalization.lift_eq, IsLocalization.lift_eq]
  exact (awayPresheaf_map_toAwayPresheaf X h' i x).symm

/-- **The transition map `𝒪[1/h] ⟶ 𝒪[1/h']` of presheaves of rings**, for a global section `h`
all of whose powers are invertible in `𝒪[1/h']`. Over every object it is the unique lift of the
canonical map `𝒪(U) ⟶ 𝒪(U)[1/h'|_U]` through the localization at `h|_U`. -/
def awayPresheafTransitionOfIsUnit : awayPresheaf h ⟶ awayPresheaf h' where
  app U := CommRingCat.ofHom (IsLocalization.lift
    (M := (awayMultiplicativeSubpresheaf h).obj U) (isUnit_toAwayPresheaf_powers X hu U))
  naturality {_ _} i := CommRingCat.hom_ext (awayPresheafTransitionOfIsUnit_naturality X hu i)

/-- On the image of a section of `𝒪` the transition map is the canonical map into `𝒪[1/h']`. -/
theorem awayPresheafTransitionOfIsUnit_app_toAwayPresheaf (U : X.Cᵒᵖ) (a : X.O.obj.obj U) :
    ((awayPresheafTransitionOfIsUnit X hu).app U).hom (((toAwayPresheaf h).app U).hom a) =
      ((toAwayPresheaf h').app U).hom a :=
  IsLocalization.lift_eq (S := (awayPresheaf h).obj U)
    (isUnit_toAwayPresheaf_powers X hu U) a

/-- **The transition map is a map over `𝒪`.** -/
theorem toAwayPresheaf_comp_awayPresheafTransitionOfIsUnit :
    toAwayPresheaf h ≫ awayPresheafTransitionOfIsUnit X hu = toAwayPresheaf h' :=
  NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun a =>
    awayPresheafTransitionOfIsUnit_app_toAwayPresheaf X hu U a))

/-- **The transition map, read as a map of presheaves of `𝒪`-modules**, at the spelling of the
presheaf of rings that the monoidal structure on presheaves of modules uses. -/
def awayModulePresheafTransitionAlt :
    awayModulePresheafAlt X h ⟶ awayModulePresheafAlt X h' :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (awayPresheafTransitionOfIsUnit X hu)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
    (fun U r m => by
      let r' : X.O.obj.obj U := r
      let m' : (awayPresheaf h).obj U := m
      change ((awayPresheafTransitionOfIsUnit X hu).app U).hom
            (((toAwayPresheaf h).app U).hom r' * m') =
          ((toAwayPresheaf h').app U).hom r' *
            ((awayPresheafTransitionOfIsUnit X hu).app U).hom m'
      rw [map_mul, awayPresheafTransitionOfIsUnit_app_toAwayPresheaf])

/-- The transition map of presheaves of modules, at the spelling of the presheaf of rings that
`AlgebraicGeometry.RingedSite.awayModulePresheaf` and the sheafification of presheaves of modules
use. -/
abbrev awayModulePresheafTransitionOfIsUnit : awayModulePresheaf X h ⟶ awayModulePresheaf X h' :=
  awayModulePresheafTransitionAlt X hu

/-- On sections the transition map of presheaves of modules is the transition map of presheaves
of rings. -/
theorem awayModulePresheafTransitionOfIsUnit_app_apply (U : X.Cᵒᵖ) (x : (awayPresheaf h).obj U) :
    ((awayModulePresheafTransitionOfIsUnit X hu).app U).hom x =
      ((awayPresheafTransitionOfIsUnit X hu).app U).hom x := rfl

/-- **The transition map of presheaves of modules is a map over `𝒪`.** -/
theorem unitToAwayModulePresheaf_comp_awayModulePresheafTransitionOfIsUnit :
    unitToAwayModulePresheaf X h ≫ awayModulePresheafTransitionOfIsUnit X hu =
      unitToAwayModulePresheaf X h' :=
  PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x =>
    awayPresheafTransitionOfIsUnit_app_toAwayPresheaf X hu U x)

end PresheafTransition

section SectionNaturality

variable (g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
  (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
    IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
  (huM : ∀ (U : X.Cᵒᵖ) (n : ℕ),
    IsUnit (((toAwayPresheaf (mulGlobalSection X g h')).app U).hom
      (globalSectionVal (mulGlobalSection X g h) U ^ n)))

/-- The transition map on the image of a section of `𝒪`, read as the algebra map of the algebra
structure the presheaf of sectionwise localizations carries. -/
theorem awayPresheafTransitionOfIsUnit_app_algebraMap (U : X.Cᵒᵖ) (a : X.O.obj.obj U) :
    letI := ((toAwayPresheaf h).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h').app U).hom.toAlgebra
    ((awayPresheafTransitionOfIsUnit X hu).app U).hom (algebraMap _ _ a) = algebraMap _ _ a :=
  awayPresheafTransitionOfIsUnit_app_toAwayPresheaf X hu U a

/-- **The transition map on sections, as a map of `𝒪(U)`-algebras.** This is the form in which
`IsLocalization.algHom_subsingleton` applies to it, which is what makes every comparison below a
one-line consequence of uniqueness rather than a computation. -/
def awayPresheafTransitionAlgHomOfIsUnit (U : X.Cᵒᵖ) :
    letI := ((toAwayPresheaf h).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h').app U).hom.toAlgebra
    (awayPresheaf h).obj U →ₐ[X.O.obj.obj U] (awayPresheaf h').obj U :=
  letI := ((toAwayPresheaf h).app U).hom.toAlgebra
  letI := ((toAwayPresheaf h').app U).hom.toAlgebra
  { __ := ((awayPresheafTransitionOfIsUnit X hu).app U).hom
    commutes' := awayPresheafTransitionOfIsUnit_app_toAwayPresheaf X hu U }

/-- The algebra map is the transition map. -/
theorem awayPresheafTransitionAlgHomOfIsUnit_apply (U : X.Cᵒᵖ) (x : (awayPresheaf h).obj U) :
    letI := ((toAwayPresheaf h).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h').app U).hom.toAlgebra
    awayPresheafTransitionAlgHomOfIsUnit X hu U x =
      ((awayPresheafTransitionOfIsUnit X hu).app U).hom x := rfl

include huM

/-- **The naturality square of the section comparison, on a pure tensor.**
`AlgebraicGeometry.RingedSite.awayTensorSectionIso_hom_tmul` computes both legs on `x ⊗ y` as a
product of the images of `x` and of `y`, and what remains is that the transition map
`𝒪(U)[1/(g h)] ⟶ 𝒪(U)[1/(g h')]` carries the two canonical maps out of `𝒪(U)[1/g]` and
`𝒪(U)[1/h]` to the corresponding ones at `h'`. That is uniqueness: all four composites are
`𝒪(U)`-algebra maps out of a localization of `𝒪(U)`, of which there is at most one. -/
theorem awayTensorSectionIso_naturality_right_tmul (U : X.Cᵒᵖ)
    (x : (awayPresheaf g).obj U) (y : (awayPresheaf h).obj U) :
    letI := ((toAwayPresheaf g).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h).app U).hom.toAlgebra
    letI := ((toAwayPresheaf h').app U).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X g h)).app U).hom.toAlgebra
    letI := ((toAwayPresheaf (mulGlobalSection X g h')).app U).hom.toAlgebra
    letI := isLocalizationAway_away X g U
    letI := isLocalizationAway_away X h U
    letI := isLocalizationAway_away X h' U
    letI := isLocalizationAway_away_mul X g h U
    letI := isLocalizationAway_away_mul X g h' U
    (awayTensorSectionIso X g h' U).hom.hom
        (x ⊗ₜ ((awayPresheafTransitionOfIsUnit X hu).app U).hom y) =
      ((awayPresheafTransitionOfIsUnit X huM).app U).hom
        ((awayTensorSectionIso X g h U).hom.hom (x ⊗ₜ y)) := by
  let := ((toAwayPresheaf g).app U).hom.toAlgebra
  let := ((toAwayPresheaf h).app U).hom.toAlgebra
  let := ((toAwayPresheaf h').app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X g h)).app U).hom.toAlgebra
  let := ((toAwayPresheaf (mulGlobalSection X g h')).app U).hom.toAlgebra
  let := isLocalizationAway_away X g U
  let := isLocalizationAway_away X h U
  let := isLocalizationAway_away X h' U
  let := isLocalizationAway_away_mul X g h U
  let := isLocalizationAway_away_mul X g h' U
  have hL : (awayPresheafTransitionAlgHomOfIsUnit X huM U).comp
        (toMulLeft (globalSectionVal g U) (globalSectionVal h U) ((awayPresheaf g).obj U)
          ((awayPresheaf (mulGlobalSection X g h)).obj U)) =
      toMulLeft (globalSectionVal g U) (globalSectionVal h' U) ((awayPresheaf g).obj U)
        ((awayPresheaf (mulGlobalSection X g h')).obj U) :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers (globalSectionVal g U))).elim _ _
  have hR : (awayPresheafTransitionAlgHomOfIsUnit X huM U).comp
        (toMulRight (globalSectionVal g U) (globalSectionVal h U) ((awayPresheaf h).obj U)
          ((awayPresheaf (mulGlobalSection X g h)).obj U)) =
      (toMulRight (globalSectionVal g U) (globalSectionVal h' U) ((awayPresheaf h').obj U)
          ((awayPresheaf (mulGlobalSection X g h')).obj U)).comp
        (awayPresheafTransitionAlgHomOfIsUnit X hu U) :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers (globalSectionVal h U))).elim _ _
  have hLx : ((awayPresheafTransitionOfIsUnit X huM).app U).hom
        (toMulLeft (globalSectionVal g U) (globalSectionVal h U) ((awayPresheaf g).obj U)
          ((awayPresheaf (mulGlobalSection X g h)).obj U) x) =
      toMulLeft (globalSectionVal g U) (globalSectionVal h' U) ((awayPresheaf g).obj U)
        ((awayPresheaf (mulGlobalSection X g h')).obj U) x :=
    DFunLike.congr_fun hL x
  have hRy : ((awayPresheafTransitionOfIsUnit X huM).app U).hom
        (toMulRight (globalSectionVal g U) (globalSectionVal h U) ((awayPresheaf h).obj U)
          ((awayPresheaf (mulGlobalSection X g h)).obj U) y) =
      toMulRight (globalSectionVal g U) (globalSectionVal h' U) ((awayPresheaf h').obj U)
        ((awayPresheaf (mulGlobalSection X g h')).obj U)
        (((awayPresheafTransitionOfIsUnit X hu).app U).hom y) :=
    DFunLike.congr_fun hR y
  rw [← awayTensorSectionIso_hom_tmul X g h' U x
      (((awayPresheafTransitionOfIsUnit X hu).app U).hom y),
    ← awayTensorSectionIso_hom_tmul X g h U x y,
    map_mul ((awayPresheafTransitionOfIsUnit X huM).app U).hom, hLx, hRy]

/-- **The comparison of `AwayTensorSections.lean` is natural in the second global section.** -/
theorem awayTensorSectionIso_naturality_right (U : X.Cᵒᵖ) :
    (MonoidalCategoryStruct.whiskerLeft (awayModulePresheafAlt X g)
          (awayModulePresheafTransitionAlt X hu)).app U ≫
        (awayTensorSectionIso X g h' U).hom =
      (awayTensorSectionIso X g h U).hom ≫
        (awayModulePresheafTransitionAlt X huM).app U :=
  ModuleCat.hom_ext (TensorProduct.ext' fun x y =>
    awayTensorSectionIso_naturality_right_tmul X g hu huM U x y)

/-- **`𝒪[1/g] ⊗_𝒪 𝒪[1/h] = 𝒪[1/(g h)]` is natural in `h`**, as presheaves of `𝒪`-modules. -/
theorem awayTensorPresheafIso_naturality_right :
    MonoidalCategoryStruct.whiskerLeft (awayModulePresheafAlt X g)
          (awayModulePresheafTransitionAlt X hu) ≫
        (awayTensorPresheafIso X g h').hom =
      (awayTensorPresheafIso X g h).hom ≫ awayModulePresheafTransitionAlt X huM :=
  PresheafOfModules.hom_ext fun U => awayTensorSectionIso_naturality_right X g hu huM U

end SectionNaturality

section Sheafification

variable {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}

/-- The map from a sheaf of modules into a sheafification is natural in the presheaf: this is
the functoriality of sheafification, the comparison being the sheafification of the given map
preceded by the inverse of the counit. -/
theorem toModuleSheafification_comp_sheafification_map
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    (can : F.val ⟶ P) (ψ : P ⟶ Q) :
    toModuleSheafification can ≫
        (PresheafOfModules.sheafification
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map ψ =
      toModuleSheafification (can ≫ ψ) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun k => inv ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app F) ≫ k)
      (Functor.map_comp (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) can ψ).symm)

/-- **`𝒪_h` as the sheafification of the presheaf of sectionwise localizations is natural in
`h`.** Both legs are maps out of `𝒪_h` into `𝒪_{h'}`, on whose sections every power of `h` acts
bijectively, so they are equal as soon as they agree on the canonical map out of `𝒪` — and both
composites with it are the canonical map `𝒪 ⟶ 𝒪_{h'}`. -/
theorem awaySheafificationIsoAwayModule_naturality
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
    {φ : awaySheaf h ⟶ awaySheaf h'} (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    (hd : ∀ U : X.Cᵒᵖ, globalSectionVal h U ∣ globalSectionVal h' U) :
    (awaySheafificationIsoAwayModule X h).hom ≫ awayModuleMapOfComp X φ hφ =
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
          (awayModulePresheafTransitionOfIsUnit X hu) ≫
        (awaySheafificationIsoAwayModule X h').hom := by
  refine (cancel_epi (awaySheafificationIsoAwayModule X h).inv).mp ?_
  refine hom_ext_unitToAwayModule X h (awayModule X h')
    (fun U n => bijective_smul_awayModule_of_isUnit X U n
      (isUnit_toAwaySheaf_of_dvd X U (hd U) n)) ?_
  have hinv : unitToAwayModule X h ≫ (awaySheafificationIsoAwayModule X h).inv =
      toModuleSheafification (unitToAwayModulePresheaf X h) :=
    (Iso.comp_inv_eq _).mpr
      (toModuleSheafification_comp_awaySheafificationToAwayModule X h).symm
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, hinv, ← Category.assoc,
    toModuleSheafification_comp_sheafification_map,
    unitToAwayModulePresheaf_comp_awayModulePresheafTransitionOfIsUnit,
    show (awaySheafificationIsoAwayModule X h').hom = awaySheafificationToAwayModule X h' from rfl,
    toModuleSheafification_comp_awaySheafificationToAwayModule,
    unitToAwayModule_comp_awayModuleMapOfComp]

end Sheafification

section SheafNaturality

variable (g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
  (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
    IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
  (huM : ∀ (U : X.Cᵒᵖ) (n : ℕ),
    IsUnit (((toAwayPresheaf (mulGlobalSection X g h')).app U).hom
      (globalSectionVal (mulGlobalSection X g h) U ^ n)))

include hu huM

/-- **`𝒪[1/g] ⊗_𝒪 𝒪[1/h] = 𝒪[1/(g h)]` is natural in `h`**, at the monoidal tensor product of
morphisms, which is the form `PresheafOfModules.sheafificationTensorIso` is
natural for. -/
theorem awayTensorPresheafIso_naturality_tensorHom :
    MonoidalCategoryStruct.tensorHom (𝟙 (awayModulePresheafAlt X g))
          (awayModulePresheafTransitionAlt X hu) ≫ (awayTensorPresheafIso X g h').hom =
      (awayTensorPresheafIso X g h).hom ≫ awayModulePresheafTransitionAlt X huM :=
  awayTensorPresheafIso_naturality_right X g hu huM

end SheafNaturality

section Bridge

variable {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}

/-- **The bridge of `AwayTensorBridge.lean` is natural in `h`**: the same statement as
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule_naturality`, at the spelling of
the sheafification functor that `sheafificationTensorIso` speaks. The two spellings of the
presheaf of rings are definitionally equal, so there is nothing to prove. -/
theorem awayModuleSheafificationIso_naturality
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
    {φ : awaySheaf h ⟶ awaySheaf h'} (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    (hd : ∀ U : X.Cᵒᵖ, globalSectionVal h U ∣ globalSectionVal h' U) :
    (awayModuleSheafificationIso X h).hom ≫ awayModuleMapOfComp X φ hφ =
      (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map
          (awayModulePresheafTransitionAlt X hu) ≫
        (awayModuleSheafificationIso X h').hom :=
  awaySheafificationIsoAwayModule_naturality X hu hφ hd

end Bridge

section Assembly

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable (g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}

/-- The fourfold composite that `AlgebraicGeometry.RingedSite.awayTensorSheafIso` is, written
out. -/
theorem awayTensorSheafIso_hom
    (k : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    (awayTensorSheafIso X g k).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map
          (((awayModuleSheafificationIso X g).inv, (awayModuleSheafificationIso X k).inv) :
            (awayModule X g, awayModule X k) ⟶
              ((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X g),
                (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X k))) ≫
        ((PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u} X.J (Osharp := X.O)
              (𝟙 X.O.obj)).hom.app
            (awayModulePresheafAlt X g, awayModulePresheafAlt X k) ≫
          ((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map
              (awayTensorPresheafIso X g k).hom ≫
            (awayModuleSheafificationIso X (mulGlobalSection X g k)).hom)) := rfl

/-- **`𝒪_g ⊗_𝒪 𝒪_h ≅ 𝒪_{g h}` is natural in `h`.** The comparison is a fourfold composite and
each factor is natural: the first and the last by
`AlgebraicGeometry.RingedSite.awayModuleSheafificationIso_naturality`, the middle one because
`PresheafOfModules.sheafificationTensorIso` is a natural isomorphism of
bifunctors, and the third by
`AlgebraicGeometry.RingedSite.awayTensorPresheafIso_naturality_tensorHom`. -/
theorem awayTensorSheafIso_naturality_right
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
    (huM : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf (mulGlobalSection X g h')).app U).hom
        (globalSectionVal (mulGlobalSection X g h) U ^ n)))
    (hd : ∀ U : X.Cᵒᵖ, globalSectionVal h U ∣ globalSectionVal h' U)
    {φ : awaySheaf h ⟶ awaySheaf h'} (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    {φM : awaySheaf (mulGlobalSection X g h) ⟶ awaySheaf (mulGlobalSection X g h')}
    (hφM : toAwaySheaf (mulGlobalSection X g h) ≫ φM =
      toAwaySheaf (mulGlobalSection X g h')) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map
          ((𝟙 (awayModule X g), awayModuleMapOfComp X φ hφ) :
            (awayModule X g, awayModule X h) ⟶ (awayModule X g, awayModule X h')) ≫
        (awayTensorSheafIso X g h').hom =
      (awayTensorSheafIso X g h).hom ≫ awayModuleMapOfComp X φM hφM := by
  have h3 := awayModuleSheafificationIso_naturality X hu hφ hd
  have h3M := awayModuleSheafificationIso_naturality X huM hφM
    (fun U => dvd_globalSectionVal_mulGlobalSection X g U (hd U))
  have h2 := awayTensorPresheafIso_naturality_tensorHom X g hu huM
  have hprod :
      (((𝟙 (awayModule X g), awayModuleMapOfComp X φ hφ) :
            (awayModule X g, awayModule X h) ⟶ (awayModule X g, awayModule X h')) ≫
          (((awayModuleSheafificationIso X g).inv,
              (awayModuleSheafificationIso X h').inv) :
            (awayModule X g, awayModule X h') ⟶
              ((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X g),
                (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X h')))) =
        (((awayModuleSheafificationIso X g).inv, (awayModuleSheafificationIso X h).inv) :
            (awayModule X g, awayModule X h) ⟶
              ((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X g),
                (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj
                  (awayModulePresheafAlt X h))) ≫
          (Functor.prod (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj))
              (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj))).map
            ((𝟙 (awayModulePresheafAlt X g), awayModulePresheafTransitionAlt X hu) :
              (awayModulePresheafAlt X g, awayModulePresheafAlt X h) ⟶
                (awayModulePresheafAlt X g, awayModulePresheafAlt X h')) := by
    refine Prod.ext ?_ ?_
    · change 𝟙 (awayModule X g) ≫ (awayModuleSheafificationIso X g).inv =
        (awayModuleSheafificationIso X g).inv ≫
          (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map
            (𝟙 (awayModulePresheafAlt X g))
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · change awayModuleMapOfComp X φ hφ ≫ (awayModuleSheafificationIso X h').inv =
        (awayModuleSheafificationIso X h).inv ≫
          (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map
            (awayModulePresheafTransitionAlt X hu)
      rw [Iso.eq_inv_comp, ← Category.assoc, h3, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  have hsq1 :=
    (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map_comp _ _).symm.trans
      (congrArg (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map hprod)).trans
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map_comp _ _)
  have hsq2 := (PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u} X.J (Osharp := X.O)
      (𝟙 X.O.obj)).hom.naturality
    ((𝟙 (awayModulePresheafAlt X g), awayModulePresheafTransitionAlt X hu) :
      (awayModulePresheafAlt X g, awayModulePresheafAlt X h) ⟶
        (awayModulePresheafAlt X g, awayModulePresheafAlt X h'))
  have h2' : (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor X.O.obj)).map
          ((𝟙 (awayModulePresheafAlt X g), awayModulePresheafTransitionAlt X hu) :
            (awayModulePresheafAlt X g, awayModulePresheafAlt X h) ⟶
              (awayModulePresheafAlt X g, awayModulePresheafAlt X h')) ≫
        (awayTensorPresheafIso X g h').hom =
      (awayTensorPresheafIso X g h).hom ≫ awayModulePresheafTransitionAlt X huM :=
    (eq_whisker (PresheafOfModules.tensorBifunctor_uncurry_map _ _) _).trans h2
  have hsq3 := (((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map_comp _ _).symm.trans
    (congrArg (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map h2')).trans
      ((PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).map_comp _ _)
  rw [awayTensorSheafIso_hom, awayTensorSheafIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hsq1, reassoc_of% hsq2, reassoc_of% hsq3, h3M]

/-- Tensoring with a fixed sheaf of modules is the uncurried tensor bifunctor at the identity in
the first variable: the uncurried map at `(𝟙 A, φ)` is the identity of `A ⊗ B` followed by
`A ⊗ φ`. -/
theorem uncurry_sheafTensor_map_id_fst
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : B ⟶ C) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O)).map
        ((𝟙 A, φ) : (A, B) ⟶ (A, C)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).map φ := by
  change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).map (𝟙 A)).app B ≫ _ = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- **Tensoring with `𝒪_g` inverts a transition map between localizations of `𝒪`** as soon as
it inverts the corresponding transition map at the products with `g`. By the naturality above the
transported map *is* that transition map. -/
theorem isIso_sheafTensor_map_awayModuleMapOfComp
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf h').app U).hom (globalSectionVal h U ^ n)))
    (huM : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwayPresheaf (mulGlobalSection X g h')).app U).hom
        (globalSectionVal (mulGlobalSection X g h) U ^ n)))
    (hd : ∀ U : X.Cᵒᵖ, globalSectionVal h U ∣ globalSectionVal h' U)
    {φ : awaySheaf h ⟶ awaySheaf h'} (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    {φM : awaySheaf (mulGlobalSection X g h) ⟶ awaySheaf (mulGlobalSection X g h')}
    (hφM : toAwaySheaf (mulGlobalSection X g h) ≫ φM =
      toAwaySheaf (mulGlobalSection X g h'))
    (hσ : IsIso (awayModuleMapOfComp X φM hφM)) :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj
      (awayModule X g)).map (awayModuleMapOfComp X φ hφ)) := by
  have hnat := awayTensorSheafIso_naturality_right X g hu huM hd hφ hφM
  have key : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj
        (awayModule X g)).map (awayModuleMapOfComp X φ hφ) =
      (awayTensorSheafIso X g h).hom ≫ awayModuleMapOfComp X φM hφM ≫
        (awayTensorSheafIso X g h').inv := by
    rw [← uncurry_sheafTensor_map_id_fst, ← Category.assoc, ← hnat, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have : IsIso (awayModuleMapOfComp X φM hφM) := hσ
  rw [key]
  exact (awayTensorSheafIso X g h ≪≫ asIso (awayModuleMapOfComp X φM hφM) ≪≫
    (awayTensorSheafIso X g h').symm).isIso_hom

end Assembly


end AlgebraicGeometry.RingedSite

end
