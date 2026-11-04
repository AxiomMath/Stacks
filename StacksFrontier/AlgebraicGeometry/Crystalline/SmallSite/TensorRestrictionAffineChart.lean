module

public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.DpDifferentialsAffineUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafObjectSections
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import StacksFrontier.RingTheory.Localization.TensorComparison

/-!
# The restriction of `F ⊗ Ω^i_{X/S}` to an affine ambient scheme, over an affine chart

Fix a global crystalline situation `(p, (S, I, γ), X)`, a sheaf of `𝒪_{X/S}`-modules `F` and an
`i : ℕ`. Over an object `A = (U, T, δ)` of `Cris(X/S)` with `T` affine, the sections of the
Zariski sheafification of the restriction `...SmallSite.tensorRestriction A F i` of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to `T` agree with the sections of the restriction itself, as soon as
that restriction localizes on the basic opens of `T`; on the crystalline site this says that the
sections over `A` of the crystalline sheafification of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the tensor
product of the sections of the two factors. The localization hypothesis is reduced to the
localization of the restriction of `Ω^i_{X/S}` alone.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ambientModule`, `tensorRestrictionAmbient` — a presheaf of modules over the restriction of
  `𝒪_{X/S}` to the opens of `T`, read over `𝒪_T` by restriction of scalars along
  `...Thickening.restrictOpenRingHom`; the underlying presheaf of abelian groups is unchanged.
* `ambientCoefficientModule` — the restriction `F_T`, as a module on the scheme `T`.
* `RestrictedLocalizes` and `TensorRestrictionLocalizes` — localization on the basic opens of
  `T`, over the restriction of `𝒪_{X/S}` and over `𝒪_T` respectively.

## Main results

* `isLocalizedModule_ambientRestrictₗ_iff` — a restriction map of a presheaf of modules over the
  restriction of `𝒪_{X/S}` is a localization if and only if it is one read over `𝒪_T`.
* `isLocalization_restrictedCommRing` — the restriction of `𝒪_{X/S}` localizes on basic opens.
* `restrictedLocalizes_coefficientRestriction` — `F_T` localizes on basic opens, for a locally
  quasi-coherent `F`.
* `restrictedLocalizes_tensorObj` — a tensor product of two presheaves of modules that localize
  on basic opens localizes there too.
* `tensorRestrictionLocalizes_of_forms`,
  `bijective_toSheafify_tensorRestriction_app_top_of_localizes` and
  `bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_localizes` — the sections of the
  sheafification of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over an object with affine ambient scheme are the
  tensor product of the sections of the two factors, given the localization of the restriction
  of `Ω^i_{X/S}`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 00DL](https://stacks.math.columbia.edu/tag/00DL)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.AffineChartLocalization
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open scoped AlgebraicGeometry

attribute [local instance] Stacks.AlgebraicGeometry.AffineChartLocalization.sectionsModule

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)
  (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)

/-- **The restriction of `𝒪_{X/S}` to the ambient scheme of an object is the structure sheaf of
rings of that scheme**, as an isomorphism of sheaves of rings whose inverse is
`...Thickening.restrictOpenRingHom`. -/
def ambientRingSheafIso :
    Thickening.ringRestrictionSheaf A.obj ≅ A.obj.thickening.target.scheme.ringCatSheaf where
  hom := ⟨restrictOpenRingHomInv S A.obj⟩
  inv := ⟨Thickening.restrictOpenRingHom A.obj⟩
  hom_inv_id := Sheaf.hom_ext (IsIso.inv_hom_id (Thickening.restrictOpenRingHom A.obj))
  inv_hom_id := Sheaf.hom_ext (IsIso.hom_inv_id (Thickening.restrictOpenRingHom A.obj))

/-- **A presheaf of modules over the restriction of `𝒪_{X/S}` to the ambient scheme of an
object, read over the structure sheaf of that scheme.**  A change of scalars along an
isomorphism: neither the sections nor the restriction maps move. -/
abbrev ambientModule
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} A.obj.thickening.target.scheme.ringCatSheaf.obj :=
  (PresheafOfModules.restrictScalars (Thickening.restrictOpenRingHom A.obj)).obj M

/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to the ambient scheme of an object, read over
the structure sheaf of that scheme.**  The same presheaf of abelian groups as
`...SmallSite.tensorRestriction`, with its scalars read in `𝒪_T` rather than in the restriction
of `𝒪_{X/S}`. -/
def tensorRestrictionAmbient :
    PresheafOfModules.{u} A.obj.thickening.target.scheme.ringCatSheaf.obj :=
  ambientModule A (tensorRestriction A F i)

/-- A change of scalars does not touch the underlying presheaf of abelian groups. -/
theorem presheaf_tensorRestrictionAmbient :
    (tensorRestrictionAmbient A F i).presheaf = (tensorRestriction A F i).presheaf := rfl

/-- **The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object,
read over the structure sheaf of that scheme**, as a module on the scheme `T`. -/
def ambientCoefficientModule : A.obj.thickening.target.scheme.Modules :=
  (SheafOfModules.restrictScalars (ambientRingSheafIso A).inv).obj
    (restrictedCoefficientSheaf A F)

variable {F} in
/-- **`F_T` is quasi-coherent** as a module on the scheme `T`, for a locally quasi-coherent
`F`. -/
theorem isQuasicoherent_ambientCoefficientModule (hF : IsLocallyQuasiCoherent F) :
    (ambientCoefficientModule A F).IsQuasicoherent :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
    (ambientRingSheafIso A).inv _ (hF A).choose_spec).isQuasicoherent

/-! ### Scalars on the restriction of `𝒪_{X/S}` -/

/-- The `Γ(W, 𝒪_T)`-algebra structure on the sections over `W` of the restriction of `𝒪_{X/S}`
to the ambient scheme, along `Crystalline.openTopRes`. -/
@[instance_reducible]
def restrictedAlgebra (W : A.obj.thickening.target.scheme.Opens) :
    Algebra Γ(A.obj.thickening.target.scheme, W)
      ((restrictedCommRing A).obj (op W) : Type u) :=
  (_root_.Crystalline.openTopRes W).hom.toAlgebra

/-- The algebra structure carried by a restriction map of the restriction of `𝒪_{X/S}`. -/
@[instance_reducible]
def restrictedAlgebraOfLE {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) :
    Algebra ((restrictedCommRing A).obj (op W) : Type u)
      ((restrictedCommRing A).obj (op W') : Type u) :=
  ((restrictedCommRing A).map (homOfLE h).op).hom.toAlgebra

/-- **The sections of `𝒪_T` over an open and the sections there of the restriction of
`𝒪_{X/S}` are the same ring**, by `Crystalline.openTopRes`. -/
def openTopResEquiv (W : A.obj.thickening.target.scheme.Opens) :
    Γ(A.obj.thickening.target.scheme, W) ≃+*
      ((restrictedCommRing A).obj (op W) : Type u) where
  toFun := (_root_.Crystalline.openTopRes W).hom
  invFun := (_root_.Crystalline.openTopResInv W).hom
  left_inv r := congr($(_root_.Crystalline.openTopRes_openTopResInv W).hom r)
  right_inv s := congr($(_root_.Crystalline.openTopResInv_openTopRes W).hom s)
  map_mul' := map_mul _
  map_add' := map_add _

/-- **The restriction maps of `𝒪_T` and of the restriction of `𝒪_{X/S}` agree** under the
identification `Crystalline.openTopRes` of their sections. -/
theorem restrictedCommRing_map_openTopRes
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (r : Γ(A.obj.thickening.target.scheme, W)) :
    ((restrictedCommRing A).map (homOfLE h).op).hom
        ((_root_.Crystalline.openTopRes W).hom r) =
      (_root_.Crystalline.openTopRes W').hom
        (A.obj.thickening.target.scheme.presheaf.map (homOfLE h).op r) :=
  (congrArg (fun φ : Γ(A.obj.thickening.target.scheme, W) ⟶
      (restrictedCommRing A).obj (op W') ↦ (CommRingCat.Hom.hom φ) r)
    (Thickening.openTopRes_naturality A.obj (homOfLE h).op)).symm

/-- The sections of `ambientModule A M`, read back as a module over the sections of the
restriction of `𝒪_{X/S}`.  The two sides are the same module; only the spelling of the scalars
differs. -/
@[instance_reducible]
def ambientSectionsModule
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    (W : A.obj.thickening.target.scheme.Opens) :
    Module ((restrictedCommRing A).obj (op W) : Type u) ↥((ambientModule A M).obj (op W)) :=
  (M.obj (op W)).isModule

/-- The module structure, over the sections of the restriction of `𝒪_{X/S}` on the larger open,
on the sections of a presheaf of modules over a smaller one. -/
@[instance_reducible]
def ambientSectionsModuleOfLE
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) :
    Module ((restrictedCommRing A).obj (op W) : Type u) ↥((ambientModule A M).obj (op W')) :=
  letI := ambientSectionsModule A M W'
  Module.compHom _ ((restrictedCommRing A).map (homOfLE h).op).hom

/-- A restriction map of a presheaf of modules over the restriction of `𝒪_{X/S}`, as a linear
map over the sections of that ring on the larger open. -/
def ambientRestrictₗ
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) :
    letI := ambientSectionsModule A M W
    letI := ambientSectionsModuleOfLE A M h
    ↥((ambientModule A M).obj (op W)) →ₗ[((restrictedCommRing A).obj (op W) : Type u)]
      ↥((ambientModule A M).obj (op W')) :=
  letI := ambientSectionsModule A M W
  letI := ambientSectionsModuleOfLE A M h
  { toFun := M.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x ↦ M.map_smul (homOfLE h).op r x }

attribute [local instance] restrictedAlgebra

variable {A} in
/-- **Whether a restriction map of a presheaf of modules over the restriction of `𝒪_{X/S}` is a
localization is the same question read over `𝒪_T`.** -/
theorem isLocalizedModule_ambientRestrictₗ_iff
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (g : Γ(A.obj.thickening.target.scheme, W)) :
    letI := ambientSectionsModule A M W
    letI := ambientSectionsModuleOfLE A M h
    letI := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
      (ambientModule A M) h
    (IsLocalizedModule (Submonoid.powers (openTopResEquiv A W g)) (ambientRestrictₗ A M h) ↔
      IsLocalizedModule (Submonoid.powers g)
        (Stacks.AlgebraicGeometry.AffineChartLocalization.presheafRestrictₗ
          (ambientModule A M) h)) := by
  let := ambientSectionsModule A M W
  let := ambientSectionsModule A M W'
  let := ambientSectionsModuleOfLE A M h
  let := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
    (ambientModule A M) h
  let : IsScalarTower Γ(A.obj.thickening.target.scheme, W)
      ((restrictedCommRing A).obj (op W) : Type u)
      ↥((ambientModule A M).obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower Γ(A.obj.thickening.target.scheme, W)
      ((restrictedCommRing A).obj (op W) : Type u)
      ↥((ambientModule A M).obj (op W')) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      congrArg (fun s : ((restrictedCommRing A).obj (op W') : Type u) ↦ s • x)
        (restrictedCommRing_map_openTopRes A h r)
  refine ⟨fun hl ↦ ?_, fun hl ↦ ?_⟩
  · have : IsLocalizedModule (Submonoid.powers
        (algebraMap Γ(A.obj.thickening.target.scheme, W)
          ((restrictedCommRing A).obj (op W) : Type u) g)) (ambientRestrictₗ A M h) := hl
    exact IsLocalizedModule.restrictScalars_powers g (ambientRestrictₗ A M h)
  · have : IsLocalizedModule (Submonoid.powers g)
        ((ambientRestrictₗ A M h).restrictScalars
          Γ(A.obj.thickening.target.scheme, W)) := hl
    have hres := IsLocalizedModule.of_restrictScalars (Submonoid.powers g)
      (ambientRestrictₗ A M h)
    rwa [Algebra.algebraMapSubmonoid_powers] at hres

variable {A} in
/-- **The sections of the restriction of `𝒪_{X/S}` over a basic open of an affine ambient scheme
are the localization of its sections over the whole scheme away from the defining function.** -/
theorem isLocalization_restrictedCommRing [IsAffine A.obj.thickening.target.scheme]
    (g : Γ(A.obj.thickening.target.scheme, ⊤))
    {U : A.obj.thickening.target.scheme.Opens}
    (hU : U = A.obj.thickening.target.scheme.basicOpen g)
    (hUV : U ≤ (⊤ : A.obj.thickening.target.scheme.Opens)) :
    letI := restrictedAlgebraOfLE A hUV
    IsLocalization
      (Submonoid.powers (openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens) g))
      ((restrictedCommRing A).obj (op U) : Type u) := by
  subst hU
  let := restrictedAlgebraOfLE A hUV
  let : Algebra Γ(A.obj.thickening.target.scheme, ⊤)
      ((restrictedCommRing A).obj
        (op (A.obj.thickening.target.scheme.basicOpen g)) : Type u) :=
    ((_root_.Crystalline.openTopRes
          (A.obj.thickening.target.scheme.basicOpen g)).hom.comp
      (A.obj.thickening.target.scheme.presheaf.map (homOfLE hUV).op).hom).toAlgebra
  let eU : Γ(A.obj.thickening.target.scheme, A.obj.thickening.target.scheme.basicOpen g) ≃ₐ[
        Γ(A.obj.thickening.target.scheme, ⊤)]
      ((restrictedCommRing A).obj
        (op (A.obj.thickening.target.scheme.basicOpen g)) : Type u) :=
    { openTopResEquiv A (A.obj.thickening.target.scheme.basicOpen g) with
      commutes' := fun _ ↦ rfl }
  have : IsLocalization (Submonoid.powers g)
      ((restrictedCommRing A).obj
        (op (A.obj.thickening.target.scheme.basicOpen g)) : Type u) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g) eU
  refine IsLocalization.of_ringEquiv_left (M₁ := Submonoid.powers g)
    (openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens)).symm ?_ ?_
  · rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers
      ((openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens)).symm_apply_apply g)
  · intro x
    refine (restrictedCommRing_map_openTopRes A hUV
      ((_root_.Crystalline.openTopResInv
        (⊤ : A.obj.thickening.target.scheme.Opens)).hom x)).symm.trans ?_ |>.symm
    exact congrArg ((restrictedCommRing A).map (homOfLE hUV).op).hom
      ((openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens)).apply_symm_apply x)

/-- **A presheaf of modules over the restriction of `𝒪_{X/S}` localizes on the basic opens of
the ambient scheme**: over `T.basicOpen g` its sections are the localization away from `g` of its
sections over `T`, as modules over the restriction of `𝒪_{X/S}`. -/
def RestrictedLocalizes
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat)) : Prop :=
  ∀ (g : Γ(A.obj.thickening.target.scheme, ⊤))
    {U : A.obj.thickening.target.scheme.Opens}
    (_ : U = A.obj.thickening.target.scheme.basicOpen g)
    (hUV : U ≤ (⊤ : A.obj.thickening.target.scheme.Opens)),
    letI := ambientSectionsModule A M (⊤ : A.obj.thickening.target.scheme.Opens)
    letI := ambientSectionsModuleOfLE A M hUV
    IsLocalizedModule
      (Submonoid.powers (openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens) g))
      (ambientRestrictₗ A M hUV)

/-! ### The coefficient factor -/

/-- **The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an
object**, as a presheaf of modules over the restriction of `𝒪_{X/S}`.  This is the first factor
of `...SmallSite.tensorRestriction`. -/
abbrev coefficientRestriction :
    PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat) :=
  restrictedModule A
    (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))

variable {A F} in
/-- **For a locally quasi-coherent `F`, the restriction `F_T` localizes on the basic opens of an
affine ambient scheme**, read over the restriction of `𝒪_{X/S}`. -/
theorem restrictedLocalizes_coefficientRestriction
    [IsAffine A.obj.thickening.target.scheme] (hF : IsLocallyQuasiCoherent F) :
    RestrictedLocalizes A (coefficientRestriction A F) := by
  intro g U hU hUV
  have := isQuasicoherent_ambientCoefficientModule A hF
  exact (isLocalizedModule_ambientRestrictₗ_iff (coefficientRestriction A F) hUV g).2
    (isLocalizedModule_restrictₗ (ambientCoefficientModule A F)
      (isAffineOpen_top A.obj.thickening.target.scheme) g hU hUV)

/-! ### The tensor product of two factors that localize -/

/-- The sections of a presheaf of modules over a smaller open form a scalar tower over the sections
of the restriction of `𝒪_{X/S}` on the two opens. -/
private theorem isScalarTower_ambientModule_restrictedAlgebraOfLE
    (M : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) :
    letI := ambientSectionsModule A M W'
    letI := ambientSectionsModuleOfLE A M h
    letI := restrictedAlgebraOfLE A h
    IsScalarTower ((restrictedCommRing A).obj (op W) : Type u)
      ((restrictedCommRing A).obj (op W') : Type u) ↥((ambientModule A M).obj (op W')) :=
  by
    let := ambientSectionsModule A M W'
    let := ambientSectionsModuleOfLE A M h
    let := restrictedAlgebraOfLE A h
    exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable {A} in
/-- **A tensor product of two presheaves of modules that localize on the basic opens of an affine
ambient scheme localizes there too.** -/
theorem restrictedLocalizes_tensorObj [IsAffine A.obj.thickening.target.scheme]
    (M N : PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat))
    (hM : RestrictedLocalizes A M) (hN : RestrictedLocalizes A N) :
    RestrictedLocalizes A (M ⊗ N) := by
  intro g U hU hUV
  let := restrictedAlgebraOfLE A hUV
  have := isLocalization_restrictedCommRing g hU hUV
  let := ambientSectionsModule A M (⊤ : A.obj.thickening.target.scheme.Opens)
  let := ambientSectionsModule A M U
  let := ambientSectionsModuleOfLE A M hUV
  let := ambientSectionsModule A N (⊤ : A.obj.thickening.target.scheme.Opens)
  let := ambientSectionsModule A N U
  let := ambientSectionsModuleOfLE A N hUV
  have := isScalarTower_ambientModule_restrictedAlgebraOfLE A M hUV
  have := isScalarTower_ambientModule_restrictedAlgebraOfLE A N hUV
  have := hM g hU hUV
  have := hN g hU hUV
  exact IsLocalization.isLocalizedModule_of_tensor _
    ((restrictedCommRing A).obj (op U) : Type u) (ambientRestrictₗ A M hUV)
    (ambientRestrictₗ A N hUV) (ambientRestrictₗ A (M ⊗ N) hUV) (fun _ _ ↦ rfl)

/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to the ambient scheme of an object localizes
on the basic opens of that scheme**, read over `𝒪_T`.

Over `W = T.basicOpen g` the sections are
`F(A|_W) ⊗_{Γ(W, 𝒪)} Ω^i_{X/S}(A|_W)`, and the assertion is that the restriction map from the
sections over `T` exhibits them as the localization away from `g`. -/
def TensorRestrictionLocalizes : Prop :=
  ∀ (g : Γ(A.obj.thickening.target.scheme, ⊤))
    {U : A.obj.thickening.target.scheme.Opens}
    (_ : U = A.obj.thickening.target.scheme.basicOpen g) (hUV : U ≤ ⊤),
    letI := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
      (tensorRestrictionAmbient A F i) hUV
    IsLocalizedModule.Away g
      (Stacks.AlgebraicGeometry.AffineChartLocalization.presheafRestrictₗ
        (tensorRestrictionAmbient A F i) hUV)

variable {A F i} in
/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to an affine ambient scheme localizes on the
basic opens as soon as the restriction of `Ω^i_{X/S}` does**, for a locally quasi-coherent
`F`. -/
theorem tensorRestrictionLocalizes_of_forms [IsAffine A.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F)
    (hΩ : RestrictedLocalizes A (restrictedModule A (crysDifferentialForms S i))) :
    TensorRestrictionLocalizes A F i := fun g _ hU hUV ↦
  (isLocalizedModule_ambientRestrictₗ_iff (tensorRestriction A F i) hUV g).1
    (restrictedLocalizes_tensorObj _ _ (restrictedLocalizes_coefficientRestriction hF) hΩ
      g hU hUV)

variable {A F i} in
/-- **The sections over an affine ambient scheme of the Zariski sheafification of the restriction
of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the sections of the restriction itself**, as soon as that
restriction localizes on the basic opens. -/
theorem bijective_toSheafify_tensorRestriction_app_top_of_localizes
    [IsAffine A.obj.thickening.target.scheme] (hloc : TensorRestrictionLocalizes A F i) :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf).app
        (op (⊤ : A.obj.thickening.target.scheme.Opens)))) :=
  bijective_toSheafify_app_of_isAffineOpen (tensorRestrictionAmbient A F i)
    (isAffineOpen_top A.obj.thickening.target.scheme) hloc

variable {A F i} in
/-- **The sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over an object of `Cris(X/S)` with affine ambient
scheme are the tensor product of the sections of the two factors there**, as soon as the
restriction localizes on the basic opens. -/
theorem bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_localizes
    [IsAffine A.obj.thickening.target.scheme] (hloc : TensorRestrictionLocalizes A F i) :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (smallTopology S)
        (tensorDifferentialFormsPresheaf F i)).app (op A))) :=
  bijective_toSheafify_app_tensorDifferentialFormsPresheaf F i A
    (bijective_toSheafify_tensorRestriction_app_top_of_localizes hloc)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
