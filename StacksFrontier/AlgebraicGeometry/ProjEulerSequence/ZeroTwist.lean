module

public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Unit

/-!
# The zeroth twist is the structure sheaf

Let `S` be a nonnegatively graded ring and `X = Proj S`. The twisting sheaf `𝒪_X(0)` is the
sheaf associated to the graded module `S` with its own grading, so a section of it over an open
`U` is a family of fractions `m / s` with `m` and `s` homogeneous of the *same* degree — which is
exactly what a section of the structure sheaf is, read through
`HomogeneousLocalization.val`. This file turns that observation into an isomorphism
`𝒪_X(0) ≅ 𝒪_X` of sheaves of modules on all of `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.zeroTwistHom`: on each open, a section of the
  structure sheaf read as a section of `𝒪_X(0)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.zeroTwistEquiv`: that map as a linear equivalence
  on sections.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`: the isomorphism
  `𝒪_X(0) ≅ 𝒪_X` of sheaves of modules.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.bijective_zeroTwistHom`: on every open,
  `HomogeneousLocalization.val` is a bijection from the sections of `𝒪_X` to the sections of
  `𝒪_X(0)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.val_twistingSheafZeroIsoUnit_hom_apply`: the
  computation rule for the isomorphism `𝒪_X(0) ⟶ 𝒪_X`, stated through
  `HomogeneousLocalization.val`, which determines the image.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.val_comp_twistingSheafZeroIsoUnit_hom_apply`: the
  same rule for a morphism into `𝒪_X(0)` composed with the isomorphism.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.twistUnitMap_eq_twistingSheafZeroIsoUnit_inv` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.isIso_twistUnitMap`: the inverse isomorphism is the
  unit `𝒪_X ⟶ 𝒪_X(0)` of the graded twisting algebra, which is therefore invertible.

## Implementation notes

This is the unrestricted form of
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`, which
trivializes `𝒪_X(nd)` over a standard open `D₊(f)` by multiplication by `f ^ n`. At `n = 0` the
trivializing section is `1`, so no standard open and no power of `f` is needed and the
isomorphism exists over every open; the degree arithmetic of that file disappears, leaving only
the two directions of the comparison. Injectivity is `HomogeneousLocalization.val_injective`
pointwise, and surjectivity is pointwise as well: a local fraction `m / s` of `𝒪_X(0)` has
`m ∈ twistGrading 𝒮 0 k = integerGrading 𝒮 k` and `s ∈ 𝒮 k` for a *natural* number `k`, hence
numerator and denominator of equal degree, so it already is a homogeneous fraction. No gluing is
involved.

The whole construction rests on the definitional coincidence that `LocalizedModule P S` and
`Localization P` are the same type — both unfold to `OreLocalization P S` — so for the regular
module the fibres of the associated-module sheaf *are* the local rings in which the structure
sheaf takes its values, and `HomogeneousLocalization.val` lands in them with no transport. For
the same reason the scalar action of a section of `𝒪_X` on a section of `𝒪_X(0)` is
multiplication of values, which is why linearity is `HomogeneousLocalization.val_mul`.

Two further points, both consequences of the degree being zero:

* no transparency attributes are needed here, unlike in
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjStructureSheaf.lean` and the restricted
  trivialization, which both make `TopCat.Sheaf`, `sheafCompose` and `ProjectiveSpectrum.top`
  locally transparent. Those are needed to rewrite *inside* a fibre; at degree zero no step does
  so — every comparison of fibres is `rfl` or one `HomogeneousLocalization.val_mk` — and the
  default transparency suffices. For the same reason the comparison with
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap`, whose source is written over
  `(AlgebraicGeometry.Proj 𝒮).ringCatSheaf` rather than over
  `Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf`, needs no help either: the two
  sheaves of rings are equal by `rfl`, as
  `Stacks.AlgebraicGeometry.ProjTrivialization.ringCatSheaf_eq` records.
* the direction `𝒪_X(0) ⟶ 𝒪_X` is produced by `LinearEquiv.ofBijective`, so it is not given by a
  formula. It is pinned down instead by `val_twistingSheafZeroIsoUnit_hom_apply`, which says
  what its value is after `HomogeneousLocalization.val`; since `val` is injective that
  determines it, and it is the shape in which the rule composes with a morphism into `𝒪_X(0)`.
  The opposite direction `𝒪_X ⟶ 𝒪_X(0)` is `HomogeneousLocalization.val` pointwise, hence given
  by `rfl`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The underlying ideal of a point of `Proj 𝒮` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

omit [GradedRing 𝒮] in
/-- In the zeroth twist a homogeneous piece of natural-number degree is the homogeneous piece of
the grading itself: the shift is by zero and the degree is nonnegative. -/
lemma mem_of_mem_twistGrading_zero {k : ℕ} {m : S}
    (hm : m ∈ twistGrading (S := S) 𝒮 0 (k : ℤ)) : m ∈ 𝒮 k := by
  simpa using hm

/-- The value of a section of the structure sheaf at each point, read as a family of elements of
the module fibres. It is a section of `𝒪_X(0)`: a local homogeneous fraction `m / s` of equal
degrees has numerator in `twistGrading 𝒮 0` of the denominator's degree. -/
lemma val_mem_moduleSections (U : Opens (ProjectiveSpectrum.top 𝒮))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)) :
    (fun x : U => HomogeneousLocalization.val (r.1 x)) ∈
      moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U := by
  intro x
  obtain ⟨V, hxV, iV, k, num, den, hden, hw⟩ := r.2 x
  refine ⟨V, hxV, iV, k, num.1, den.1,
    mem_integerGrading_natCast 𝒮 num.2, den.2, hden, fun y => ?_⟩
  have hwy : r.1 (iV y) = HomogeneousLocalization.mk ⟨k, num, den, hden y⟩ := hw y
  show HomogeneousLocalization.val (r.1 (iV y)) = LocalizedModule.mk num.1 ⟨den.1, hden y⟩
  rw [hwy]
  rfl

/-- **A section of the structure sheaf, read as a section of `𝒪_X(0)`.** The underlying map is
`HomogeneousLocalization.val` at every point, and it is linear over the ring of sections of the
structure sheaf because the scalar action on the fibres of the twist is multiplication of
values. -/
def zeroTwistHom (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U) →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)]
      moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U where
  toFun r := ⟨fun x => HomogeneousLocalization.val (r.1 x), val_mem_moduleSections 𝒮 U r⟩
  map_add' _ _ := Subtype.ext (funext fun _ => HomogeneousLocalization.val_add _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => HomogeneousLocalization.val_mul _ _)

/-- The defining formula: the section of `𝒪_X(0)` attached to a section of the structure sheaf
takes at each point the value of the homogeneous fraction there. -/
@[simp]
lemma zeroTwistHom_apply (U : Opens (ProjectiveSpectrum.top 𝒮))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)) (x : U) :
    (zeroTwistHom 𝒮 U r).1 x = HomogeneousLocalization.val (r.1 x) := rfl

/-- Pointwise, every section of `𝒪_X(0)` is the value of a homogeneous fraction: its local
fraction `m / s` already has numerator and denominator of the same degree. -/
lemma exists_val_eq (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U) (x : U) :
    ∃ ρ : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal,
      HomogeneousLocalization.val ρ = a.1 x := by
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hnin, heq⟩ := a.2 x
  refine ⟨HomogeneousLocalization.mk
    ⟨k, ⟨m, mem_of_mem_twistGrading_zero 𝒮 hm⟩, ⟨s, hs⟩, hnin ⟨x.1, hxV⟩⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk]
  exact (heq ⟨x.1, hxV⟩).symm

/-- The pointwise homogeneous fraction underlying a section of `𝒪_X(0)`. -/
def zeroTwistInvFun (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U) (x : U) :
    HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal :=
  (exists_val_eq 𝒮 U a x).choose

/-- The pointwise homogeneous fraction of a section of `𝒪_X(0)` has that section's value. -/
lemma zeroTwistInvFun_spec (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U) (x : U) :
    HomogeneousLocalization.val (zeroTwistInvFun 𝒮 U a x) = a.1 x :=
  (exists_val_eq 𝒮 U a x).choose_spec

/-- The pointwise homogeneous fractions of a section of `𝒪_X(0)` form a section of the structure
sheaf: the local fraction of the given section is a local fraction for them, because
`HomogeneousLocalization.val` is injective. -/
lemma zeroTwistInvFun_mem (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒮).pred
      (zeroTwistInvFun 𝒮 U a) := by
  intro x
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hnin, heq⟩ := a.2 x
  refine ⟨V, hxV, i, k, ⟨m, mem_of_mem_twistGrading_zero 𝒮 hm⟩, ⟨s, hs⟩, hnin, fun y => ?_⟩
  refine HomogeneousLocalization.val_injective _ ?_
  rw [zeroTwistInvFun_spec, HomogeneousLocalization.val_mk]
  exact heq y

/-- **On every open, `HomogeneousLocalization.val` is a bijection from the sections of `𝒪_X` to
the sections of `𝒪_X(0)`.** Injectivity is injectivity of `val` at each point; surjectivity is
pointwise too, a local fraction of `𝒪_X(0)` having numerator and denominator of equal degree. -/
lemma bijective_zeroTwistHom (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    Function.Bijective (zeroTwistHom 𝒮 U) :=
  ⟨fun _ _ h => Subtype.ext (funext fun x =>
      HomogeneousLocalization.val_injective _ (congrFun (congrArg Subtype.val h) x)),
    fun a => ⟨⟨zeroTwistInvFun 𝒮 U a, zeroTwistInvFun_mem 𝒮 U a⟩,
      Subtype.ext (funext fun x => zeroTwistInvFun_spec 𝒮 U a x)⟩⟩

/-- The identification of the sections of `𝒪_X` with the sections of `𝒪_X(0)` over an open. -/
def zeroTwistEquiv (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U) ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)]
      moduleSections 𝒮 (twistGrading (S := S) 𝒮 0) U :=
  LinearEquiv.ofBijective _ (bijective_zeroTwistHom 𝒮 U)

/-- The identification of the structure sheaf with its zeroth twist, as an isomorphism of
presheaves of modules. Naturality is definitional: restriction on both sides is restriction of
dependent functions, and the comparison is `HomogeneousLocalization.val` at every point. -/
def unitValIsoTwistingSheafZeroVal :
    (SheafOfModules.unit (projRingSheaf 𝒮)).val ≅ (twistingSheaf 𝒮 0).val :=
  PresheafOfModules.isoMk (fun U => (zeroTwistEquiv 𝒮 U.unop).toModuleIso)
    (fun {_ _} _ => ModuleCat.hom_ext (LinearMap.ext fun _ =>
      Subtype.ext (funext fun _ => rfl)))

/-- **The zeroth twist is the structure sheaf**: `𝒪_X(0) ≅ 𝒪_X` as sheaves of modules on
`X = Proj S`. A section of `𝒪_X(0)` is a family of fractions whose numerator and denominator are
homogeneous of the same degree, which is precisely a section of `𝒪_X`. -/
def twistingSheafZeroIsoUnit :
    twistingSheaf 𝒮 0 ≅ SheafOfModules.unit (projRingSheaf 𝒮) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (unitValIsoTwistingSheafZeroVal 𝒮).symm

/-- The inverse of the isomorphism is `HomogeneousLocalization.val` at every point. -/
@[simp]
lemma twistingSheafZeroIsoUnit_inv_apply (U : Opens (ProjectiveSpectrum.top 𝒮))
    (r : (SheafOfModules.unit (projRingSheaf 𝒮)).val.obj (op U)) (x : U) :
    (((twistingSheafZeroIsoUnit 𝒮).inv.val.app (op U) r).1 x) =
      HomogeneousLocalization.val (r.1 x) := rfl

/-- **The computation rule for `𝒪_X(0) ⟶ 𝒪_X`**: the image of a section of `𝒪_X(0)` is the
family of homogeneous fractions whose values are the values of that section. Since
`HomogeneousLocalization.val` is injective this determines the image. -/
@[simp]
lemma val_twistingSheafZeroIsoUnit_hom_apply (U : Opens (ProjectiveSpectrum.top 𝒮))
    (a : (twistingSheaf 𝒮 0).val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
        (((twistingSheafZeroIsoUnit 𝒮).hom.val.app (op U) a).1 x) = a.1 x := by
  have h : zeroTwistHom 𝒮 U ((twistingSheafZeroIsoUnit 𝒮).hom.val.app (op U) a) = a :=
    (zeroTwistEquiv 𝒮 U).apply_symm_apply a
  exact congrFun (congrArg Subtype.val h) x

/-- **The computation rule for a morphism into `𝒪_X(0)` composed with the isomorphism**: the
values of the resulting section of `𝒪_X` are the values of the image under the given morphism. -/
@[simp]
lemma val_comp_twistingSheafZeroIsoUnit_hom_apply
    {M : SheafOfModules.{u} (projRingSheaf 𝒮)} (φ : M ⟶ twistingSheaf 𝒮 0)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (s : M.val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
        (((φ ≫ (twistingSheafZeroIsoUnit 𝒮).hom).val.app (op U) s).1 x) =
      (φ.val.app (op U) s).1 x :=
  val_twistingSheafZeroIsoUnit_hom_apply 𝒮 U (φ.val.app (op U) s) x

/-- The inverse isomorphism `𝒪_X ⟶ 𝒪_X(0)` is the unit of the graded twisting algebra: both are
`HomogeneousLocalization.val` at every point. -/
lemma twistUnitMap_eq_twistingSheafZeroIsoUnit_inv :
    ProjTwistCompare.twistUnitMap 𝒮 = (twistingSheafZeroIsoUnit 𝒮).inv :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)))

/-- **The unit of the graded twisting algebra `𝒪_X ⟶ 𝒪_X(0)` is an isomorphism.** -/
theorem isIso_twistUnitMap : IsIso (ProjTwistCompare.twistUnitMap 𝒮) := by
  rw [twistUnitMap_eq_twistingSheafZeroIsoUnit_inv]
  exact (twistingSheafZeroIsoUnit 𝒮).isIso_inv

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
