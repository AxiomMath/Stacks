module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The localization of the structure sheaf as a sequential colimit

Let `(𝒞, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`. This file proves that

`𝒪_f = colim( 𝒪 --f--> 𝒪 --f--> 𝒪 --f--> ⋯ )`

in the category of sheaves of `𝒪`-modules, the `n`-th leg of the colimit cocone being the
canonical map `𝒪 ⟶ 𝒪_f` divided by `f^n`.

This is not a sectionwise statement: `𝒪_f` is a sheafification
(`AlgebraicGeometry.RingedSite.awaySheaf`), so it has no description of its sections beyond the
one given in `AwaySections.lean`, namely that it *is* the sheafification of the presheaf of
sectionwise localizations. The proof uses only the universal property deduced there, together
with the general fact that a sequential colimit of an endomorphism inverts it.

## Main definitions

* `AlgebraicGeometry.RingedSite.awaySmul`: multiplication by the global section, as an
  endomorphism of the identity functor of `Mod(𝒪)`.
* `AlgebraicGeometry.RingedSite.awaySequence`: the sequential diagram `𝒪 --f--> 𝒪 --f--> ⋯`,
  for an endomorphism of `𝒪` which acts sectionwise by multiplication by `f`.
* `AlgebraicGeometry.RingedSite.awayModuleCocone`: the cocone on `𝒪_f` over that diagram.
* `AlgebraicGeometry.RingedSite.awayShift`: the shift endomorphism of the colimit, which is the
  inverse of multiplication by `f` there.

## Main results

* `AlgebraicGeometry.RingedSite.bijective_smul_awayModule`: every power of `f` acts bijectively
  on the sections of `𝒪_f`.
* `AlgebraicGeometry.RingedSite.isIso_awaySmul_pow_awayModule`: equivalently, multiplication by
  every power of `f` is an automorphism of `𝒪_f`.
* `AlgebraicGeometry.RingedSite.isIso_awaySmul_app_colimit`: multiplication by `f` is invertible
  on the colimit of the diagram, the shift being its inverse.
* `AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone`: **`𝒪_f` is the colimit of
  `𝒪 --f--> 𝒪 --f--> ⋯`.**

## Implementation notes

The diagram is taken with respect to an *arbitrary* endomorphism `a` of `𝒪` which acts
sectionwise by multiplication by `f`, rather than with respect to a chosen one. The hypothesis
`ha` determines `a` uniquely (`AlgebraicGeometry.RingedSite.eq_awaySmul_app_unit`), so no
generality is lost.

Both halves of the proof are the universal property of `𝒪_f` from `AwaySections.lean`:

* `𝒪_f ⟶ colim` is the lift of the zeroth leg `𝒪 ⟶ colim`, which exists because `f` acts
  bijectively on the sections of the colimit — multiplication by `f` on a sequential colimit of
  multiplication by `f` is invertible, the inverse being the shift, and an isomorphism of sheaves
  of modules is sectionwise bijective;
* `colim ⟶ 𝒪_f` is the descent of the cocone on `𝒪_f`, whose `n`-th leg is the canonical map
  divided by `f^n`, division being possible because `f` acts invertibly on `𝒪_f`.

That these are mutually inverse is checked on the legs of the colimit for one composite, and by
the uniqueness half of the universal property for the other. The conclusion is then transported
to the cocone on `𝒪_f` by `CategoryTheory.Limits.IsColimit.ofPointIso`.

Nothing here carries a `stacks` attribute: these are general facts about the localization of the
structure sheaf of a ringed site at a global section, and the source states none of them. The
colimit presentation is the sheaf-theoretic input to [Stacks, Tag 0913] and thence to
[Stacks, Tag 0A0E], but it is neither of those tags.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem bijective_val_app_of_isIso
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : M ⟶ N)
    [IsIso g] (U : X.Cᵒᵖ) : Function.Bijective (g.val.app U).hom := by
  have hiso : IsIso (((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
      PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map g).app U) :=
    inferInstance
  rwa [ConcreteCategory.isIso_iff_bijective] at hiso

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- A map of sheaves of modules which is bijective on sections is an isomorphism: the forgetful
functor to presheaves of abelian groups reflects isomorphisms. -/
theorem isIso_of_bijective_val_app
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : M ⟶ N)
    (hg : ∀ U : X.Cᵒᵖ, Function.Bijective (g.val.app U).hom) : IsIso g := by
  have hiso : IsIso ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
      PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map g) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hg U
  exact isIso_of_reflects_iso g
    (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
      PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- The global section `f`, as a compatible family of local sections of the sheaf of rings
underlying the structure sheaf. -/
def awayFamily :
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⋙ forget RingCat.{u}).sections where
  val U := globalSectionVal h U
  property {_U _V} g := globalSectionVal_map h g

/-- **Multiplication by the global section `f`**, as an endomorphism of the identity functor of
the category of sheaves of `𝒪`-modules. -/
def awaySmul : End (𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (awayFamily X h)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- On sections, multiplication by `f` is multiplication by the value of `f` there. -/
theorem awaySmul_app_apply (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (U : X.Cᵒᵖ) (x : M.val.obj U) :
    ((awaySmul X h).asHom.app M).val.app U x = globalSectionVal h U • x := rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- On sections, the `n`-th power of multiplication by `f` is multiplication by `f^n`. -/
theorem awaySmul_pow_app_apply
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ)
    (U : X.Cᵒᵖ) (x : M.val.obj U) :
    (((awaySmul X h) ^ n).asHom.app M).val.app U x = globalSectionVal h U ^ n • x :=
  Stacks.SheafOfModules.globalSectionToEnd_pow_apply _ _ M n U x

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- On sections, the underlying function of the `n`-th power of multiplication by `f` is
`t ↦ f^n • t`. -/
theorem awaySmul_pow_val_app_hom
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ) (U : X.Cᵒᵖ) :
    (fun t : M.val.obj U => globalSectionVal h U ^ n • t) =
      ⇑((((awaySmul X h) ^ n).asHom.app M).val.app U).hom :=
  (funext (awaySmul_pow_app_apply X h M n U)).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Multiplication by `f^{n+1}` is multiplication by `f^n` followed by multiplication by `f`. -/
theorem awaySmul_pow_app_succ
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ) :
    ((awaySmul X h ^ (n + 1)).asHom.app M) =
      ((awaySmul X h ^ n).asHom.app M) ≫ ((awaySmul X h).asHom.app M) := by
  rw [pow_succ']
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Multiplication by `f^{n+1}` is multiplication by `f` followed by multiplication by `f^n`. -/
theorem awaySmul_pow_app_succ'
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ) :
    ((awaySmul X h ^ (n + 1)).asHom.app M) =
      ((awaySmul X h).asHom.app M) ≫ ((awaySmul X h ^ n).asHom.app M) := by
  rw [pow_succ]
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Multiplication by `f^0` is the identity. -/
theorem awaySmul_pow_app_zero
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((awaySmul X h ^ 0).asHom.app M) = 𝟙 M := by
  rw [pow_zero]
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- If every power of `f` acts bijectively on the sections of a sheaf of `𝒪`-modules, then
multiplication by every power of `f` is an automorphism of it. -/
theorem isIso_awaySmul_pow_of_bijective
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      Function.Bijective fun t : M.val.obj U => globalSectionVal h U ^ n • t) (n : ℕ) :
    IsIso (((awaySmul X h) ^ n).asHom.app M) :=
  isIso_of_bijective_val_app X _ fun U => by
    rw [← awaySmul_pow_val_app_hom]
    exact hM U n

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Conversely, if multiplication by `f^n` is an automorphism then `f^n` acts bijectively on
sections. -/
theorem bijective_smul_of_isIso
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ)
    [IsIso (((awaySmul X h) ^ n).asHom.app M)] (U : X.Cᵒᵖ) :
    Function.Bijective fun t : M.val.obj U => globalSectionVal h U ^ n • t := by
  rw [awaySmul_pow_val_app_hom]
  exact bijective_val_app_of_isIso X _ U

/-- **Every power of the global section acts bijectively on the sections of `𝒪_f`**: it acts by
multiplication by its image, which `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf` says is a
unit. -/
theorem bijective_smul_awayModule (U : X.Cᵒᵖ) (n : ℕ) :
    Function.Bijective fun t : (awayModule X h).val.obj U => globalSectionVal h U ^ n • t := by
  show Function.Bijective fun t : (awaySheaf h).obj.obj U =>
    ((toAwaySheaf h).hom.app U).hom (globalSectionVal h U ^ n) * t
  exact IsUnit.isUnit_iff_mulLeft_bijective.1 (isUnit_toAwaySheaf h U n)

/-- **Multiplication by every power of `f` is an automorphism of `𝒪_f`.** -/
instance isIso_awaySmul_pow_awayModule (n : ℕ) :
    IsIso ((awaySmul X h ^ n).asHom.app (awayModule X h)) :=
  isIso_awaySmul_pow_of_bijective X h _ (bijective_smul_awayModule X h) n

/-- Multiplication by `f` is an automorphism of `𝒪_f`. -/
instance isIso_awaySmul_awayModule : IsIso ((awaySmul X h).asHom.app (awayModule X h)) := by
  have hone := isIso_awaySmul_pow_awayModule X h 1
  rwa [pow_one] at hone

/-- On `𝒪_f`, dividing by `f^{n+1}` is dividing by `f` and then by `f^n`. -/
theorem inv_awaySmul_pow_app_succ (n : ℕ) :
    inv ((awaySmul X h ^ (n + 1)).asHom.app (awayModule X h)) =
      inv ((awaySmul X h).asHom.app (awayModule X h)) ≫
        inv ((awaySmul X h ^ n).asHom.app (awayModule X h)) :=
  IsIso.inv_eq_of_hom_inv_id (by
    rw [awaySmul_pow_app_succ, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id])

/-- On `𝒪_f`, dividing by `f^0` is the identity. -/
theorem inv_awaySmul_pow_app_zero :
    inv ((awaySmul X h ^ 0).asHom.app (awayModule X h)) = 𝟙 (awayModule X h) :=
  IsIso.inv_eq_of_hom_inv_id (by simp)

section Sequence

variable (a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
  SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The sequential diagram `𝒪 --f--> 𝒪 --f--> ⋯`** attached to an endomorphism `a` of `𝒪`. -/
abbrev awaySequence : ℕ ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Functor.ofSequence
    (X := fun _ => SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (fun _ => a)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Each transition map `n ⟶ n + 1` of the sequential diagram is `a`. -/
theorem awaySequence_map_succ (n : ℕ) :
    (awaySequence X a).map (homOfLE (Nat.le_add_right n 1)) = a :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The `n`-th leg of the colimit cocone, with its source spelled `𝒪`. Every term of the
diagram *is* `𝒪`, but `CategoryTheory.Functor.ofSequence` does not say so reducibly, and
a composite of a leg with a map out of `𝒪` would then have two spellings of
one type. -/
def awayColimitι (n : ℕ) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      colimit (awaySequence X a) :=
  colimit.ι (awaySequence X a) n

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Two maps out of the colimit agree as soon as they agree on every leg. -/
theorem colimit_hom_ext {Z : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {φ ψ : colimit (awaySequence X a) ⟶ Z}
    (hφψ : ∀ n, awayColimitι X a n ≫ φ = awayColimitι X a n ≫ ψ) : φ = ψ :=
  colimit.hom_ext fun n => hφψ n

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The `(n+1)`-st leg of the colimit cocone precomposed with `a` is the `n`-th leg. -/
theorem comp_awayColimitι_succ (n : ℕ) :
    a ≫ awayColimitι X a (n + 1) = awayColimitι X a n := by
  have hw := colimit.w (awaySequence X a) (homOfLE (Nat.le_add_right n 1))
  rwa [awaySequence_map_succ] at hw

variable (ha : ∀ (U : X.Cᵒᵖ)
  (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U),
  (a.val.app U).hom x = globalSectionVal h U • x)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- An endomorphism of `𝒪` acting sectionwise by multiplication by `f` *is* multiplication by
`f`: a map of sheaves of modules is determined by its action on sections. -/
theorem eq_awaySmul_app_unit :
    a = (awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (ha U x).trans
      (awaySmul_app_apply X h _ U x).symm))

/-- The `n`-th leg of the cocone on `𝒪_f`: the canonical map `𝒪 ⟶ 𝒪_f` divided by `f^n`. -/
def awayModuleCoconeι (n : ℕ) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ awayModule X h :=
  unitToAwayModule X h ≫ inv ((awaySmul X h ^ n).asHom.app (awayModule X h))

/-- The zeroth leg of the cocone on `𝒪_f` is the canonical map `𝒪 ⟶ 𝒪_f`. -/
theorem awayModuleCoconeι_zero : awayModuleCoconeι X h 0 = unitToAwayModule X h := by
  rw [awayModuleCoconeι, inv_awaySmul_pow_app_zero, Category.comp_id]

include ha in
/-- The legs form a cocone: dividing by `f^{n+1}` after multiplying by `f` is dividing by
`f^n`. -/
theorem comp_awayModuleCoconeι_succ (n : ℕ) :
    a ≫ awayModuleCoconeι X h (n + 1) = awayModuleCoconeι X h n := by
  have hnat :
      (awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
        unitToAwayModule X h = unitToAwayModule X h ≫ (awaySmul X h).asHom.app (awayModule X h) :=
    ((awaySmul X h).asHom.naturality (unitToAwayModule X h)).symm
  simp only [awayModuleCoconeι]
  rw [eq_awaySmul_app_unit X h a ha, ← Category.assoc, hnat, Category.assoc,
    inv_awaySmul_pow_app_succ, IsIso.hom_inv_id_assoc]

/-- **The cocone on `𝒪_f`** over the sequential diagram `𝒪 --f--> 𝒪 --f--> ⋯`. -/
def awayModuleCocone : Cocone (awaySequence X a) where
  pt := awayModule X h
  ι := NatTrans.ofSequence (fun n => awayModuleCoconeι X h n) (fun n => by
    rw [awaySequence_map_succ]
    exact (comp_awayModuleCoconeι_succ X h a ha n).trans (Category.comp_id _).symm)

/-- The `n`-th leg of `awayModuleCocone` is `awayModuleCoconeι`. -/
theorem awayModuleCocone_ι_app (n : ℕ) :
    (awayModuleCocone X h a ha).ι.app n = awayModuleCoconeι X h n := rfl

/-- The shift cocone on the colimit of the diagram: the legs one step along. -/
def awayShiftCocone : Cocone (awaySequence X a) where
  pt := colimit (awaySequence X a)
  ι := NatTrans.ofSequence (fun n => colimit.ι (awaySequence X a) (n + 1)) (fun n => by
    rw [awaySequence_map_succ]
    exact (comp_awayColimitι_succ X a (n + 1)).trans (Category.comp_id _).symm)

/-- **The shift endomorphism of the colimit**, which inverts multiplication by `f` there. -/
def awayShift : colimit (awaySequence X a) ⟶ colimit (awaySequence X a) :=
  colimit.desc (awaySequence X a) (awayShiftCocone X a)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The shift carries the `n`-th leg of the colimit cocone to the `(n+1)`-st. -/
theorem awayColimitι_comp_awayShift (n : ℕ) :
    awayColimitι X a n ≫ awayShift X a = awayColimitι X a (n + 1) :=
  colimit.ι_desc _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- Multiplication by `f` on the colimit, pulled back along a leg, is multiplication by `f`
before the leg: the naturality of multiplication by `f`. -/
theorem awayColimitι_comp_awaySmul (n : ℕ) :
    awayColimitι X a n ≫ (awaySmul X h).asHom.app (colimit (awaySequence X a)) =
      a ≫ awayColimitι X a n := by
  have hnat : awayColimitι X a n ≫ (awaySmul X h).asHom.app (colimit (awaySequence X a)) =
      (awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
        awayColimitι X a n :=
    (awaySmul X h).asHom.naturality (awayColimitι X a n)
  rw [hnat, ← eq_awaySmul_app_unit X h a ha]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- **Multiplication by `f` is invertible on the colimit of `𝒪 --f--> 𝒪 --f--> ⋯`**, the shift
being its inverse. This is the general fact that a sequential colimit of an endomorphism inverts
it. -/
theorem isIso_awaySmul_app_colimit :
    IsIso ((awaySmul X h).asHom.app (colimit (awaySequence X a))) := by
  refine ⟨awayShift X a, ?_, ?_⟩ <;> refine colimit_hom_ext X a fun n => ?_ <;>
    simp [awayColimitι_comp_awayShift, reassoc_of% awayColimitι_comp_awayShift X a,
      awayColimitι_comp_awaySmul X h a ha, reassoc_of% awayColimitι_comp_awaySmul X h a ha,
      comp_awayColimitι_succ]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- Multiplication by every power of `f` is invertible on the colimit of the diagram. -/
theorem isIso_awaySmul_pow_app_colimit (n : ℕ) :
    IsIso ((awaySmul X h ^ n).asHom.app (colimit (awaySequence X a))) := by
  induction n with
  | zero =>
    rw [awaySmul_pow_app_zero]
    infer_instance
  | succ n ih =>
    have := isIso_awaySmul_app_colimit X h a ha
    rw [awaySmul_pow_app_succ']
    infer_instance

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- Every power of `f` acts bijectively on the sections of the colimit of the diagram. -/
theorem bijective_smul_colimit (U : X.Cᵒᵖ) (n : ℕ) :
    Function.Bijective fun t : (colimit (awaySequence X a)).val.obj U =>
      globalSectionVal h U ^ n • t := by
  have : IsIso ((awaySmul X h ^ n).asHom.app (colimit (awaySequence X a))) :=
    isIso_awaySmul_pow_app_colimit X h a ha n
  exact bijective_smul_of_isIso X h _ n U

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include ha in
/-- Multiplication by `f^n` carries the `n`-th leg of the colimit cocone to the zeroth. -/
theorem awayColimitι_comp_awaySmul_pow (n : ℕ) :
    awayColimitι X a n ≫ (awaySmul X h ^ n).asHom.app (colimit (awaySequence X a)) =
      awayColimitι X a 0 := by
  induction n with
  | zero => rw [awaySmul_pow_app_zero, Category.comp_id]
  | succ n ih =>
      rw [awaySmul_pow_app_succ', ← Category.assoc, awayColimitι_comp_awaySmul X h a ha,
        comp_awayColimitι_succ, ih]

include ha in
/-- The descent of the cocone on `𝒪_f` carries the `n`-th leg of the colimit cocone to the
`n`-th leg of the cocone on `𝒪_f`. -/
theorem awayColimitι_comp_desc (n : ℕ) :
    awayColimitι X a n ≫ colimit.desc (awaySequence X a) (awayModuleCocone X h a ha) =
      awayModuleCoconeι X h n :=
  colimit.ι_desc _ _

include ha in
/-- The lift of the zeroth leg through the canonical map `𝒪 ⟶ 𝒪_f` carries the cocone on `𝒪_f`
to the colimit cocone. -/
theorem awayModuleCoconeι_comp_lift (ψ : awayModule X h ⟶ colimit (awaySequence X a))
    (hψ : unitToAwayModule X h ≫ ψ = awayColimitι X a 0) (n : ℕ) :
    awayModuleCoconeι X h n ≫ ψ = awayColimitι X a n := by
  have : IsIso ((awaySmul X h ^ n).asHom.app (colimit (awaySequence X a))) :=
    isIso_awaySmul_pow_app_colimit X h a ha n
  have hnat : ψ ≫ (awaySmul X h ^ n).asHom.app (colimit (awaySequence X a)) =
      (awaySmul X h ^ n).asHom.app (awayModule X h) ≫ ψ :=
    (awaySmul X h ^ n).asHom.naturality ψ
  refine (cancel_mono ((awaySmul X h ^ n).asHom.app (colimit (awaySequence X a)))).1 ?_
  simp only [awayModuleCoconeι, Category.assoc]
  rw [hnat, IsIso.inv_hom_id_assoc, hψ, awayColimitι_comp_awaySmul_pow X h a ha]

include ha in
/-- The zeroth leg `𝒪 ⟶ colim` of the colimit cocone factors through the canonical map
`𝒪 ⟶ 𝒪_f`. -/
theorem exists_lift_colimit :
    ∃ ψ : awayModule X h ⟶ colimit (awaySequence X a),
      unitToAwayModule X h ≫ ψ = awayColimitι X a 0 :=
  (existsUnique_lift_unitToAwayModule X h (colimit (awaySequence X a))
    (awayColimitι X a 0) (bijective_smul_colimit X h a ha)).exists

include ha in
/-- **`𝒪_f` is the colimit of `𝒪 --f--> 𝒪 --f--> ⋯`.** -/
def isColimitAwayModuleCocone : IsColimit (awayModuleCocone X h a ha) := by
  have : IsIso ((colimit.isColimit (awaySequence X a)).desc
      (awayModuleCocone X h a ha)) := by
    obtain ⟨ψ, hψ⟩ := exists_lift_colimit X h a ha
    refine ⟨ψ, ?_, ?_⟩
    · refine colimit_hom_ext X a fun n => ?_
      calc awayColimitι X a n ≫
              colimit.desc (awaySequence X a) (awayModuleCocone X h a ha) ≫ ψ
          = (awayColimitι X a n ≫
              colimit.desc (awaySequence X a) (awayModuleCocone X h a ha)) ≫ ψ :=
            (Category.assoc _ _ _).symm
        _ = awayModuleCoconeι X h n ≫ ψ :=
            congrArg (fun k => k ≫ ψ) (awayColimitι_comp_desc X h a ha n)
        _ = awayColimitι X a n := awayModuleCoconeι_comp_lift X h a ha ψ hψ n
        _ = awayColimitι X a n ≫ 𝟙 _ := (Category.comp_id _).symm
    · refine hom_ext_unitToAwayModule X h _ (bijective_smul_awayModule X h) ?_
      have e1 := congrArg
        (fun k : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          colimit (awaySequence X a) =>
            k ≫ colimit.desc (awaySequence X a) (awayModuleCocone X h a ha)) hψ
      exact (Category.assoc _ _ _).symm.trans (e1.trans
        ((awayColimitι_comp_desc X h a ha 0).trans
          ((awayModuleCoconeι_zero X h).trans (Category.comp_id _).symm)))
  exact IsColimit.ofPointIso (colimit.isColimit (awaySequence X a))

end Sequence

end AlgebraicGeometry.RingedSite

end
