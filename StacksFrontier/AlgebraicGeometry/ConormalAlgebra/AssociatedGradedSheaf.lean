module

public import StacksFrontier.Algebra.Group.SurjectiveKerEq
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Graded
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated graded sheaf of a quasi-coherent ideal

Let `X` be a scheme and `ℐ : X.IdealSheafData` a quasi-coherent sheaf of ideals.  The powers
`ℐⁿ · 𝒪_X` form a descending filtration of `𝒪_X` by quasi-coherent subsheaves
(`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmulModule`), with one step of the filtration
given by `Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep`.  This file introduces the
successive quotients `ℐⁿ/ℐⁿ⁺¹` as sheaves of `𝒪_X`-modules and identifies their sections over an
affine open with the algebraic associated graded piece
`Stacks.AssociatedGraded.piece (ℐ(V)) n = ℐ(V)ⁿ/ℐ(V)ⁿ⁺¹`. These are the graded pieces of the
algebra `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹` of [Stacks, Tag 0633](https://stacks.math.columbia.edu/tag/0633).

## Main definitions

* `Stacks.Conormal.grPiece`: `ℐⁿ/ℐⁿ⁺¹`, as a sheaf of `𝒪_X`-modules — the cokernel of the
  inclusion `ℐⁿ⁺¹ · 𝒪_X ⟶ ℐⁿ · 𝒪_X`.

## Main results

* `Stacks.Conormal.grPiece_shortExact`: the defining short exact sequence
  `0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹ ⟶ 0`.
* `Stacks.Conormal.isQuasicoherent_grPiece`: `ℐⁿ/ℐⁿ⁺¹` is quasi-coherent.
* `Stacks.Conormal.surjective_grPieceπ_app`: over an affine open the sections of `ℐⁿ/ℐⁿ⁺¹` are a
  quotient of the sections of `ℐⁿ`.
* `Stacks.Conormal.grPieceSectionsEquiv`: over an affine open `V` the sections of `ℐⁿ/ℐⁿ⁺¹` are
  the algebraic associated graded piece `AssociatedGraded.piece (ℐ(V)) n = ℐ(V)ⁿ/ℐ(V)ⁿ⁺¹`.

## Implementation notes

`ℐⁿ · 𝒪_X` is taken as `idealPowSmulModule ℐ n 𝒪_X` with `𝒪_X = SheafOfModules.unit`, whose
sections over an affine open `V` are `ℐ(V)ⁿ • ⊤` by
`Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul`.  That submodule is *definitionally*
`Stacks.AssociatedGraded.power (ℐ(V)) n`.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GabberColimit Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- The structure sheaf, as a quasi-coherent `𝒪_X`-module. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [instance] Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit

/-- `ℐⁿ · 𝒪_X`, the degree-`n` term of the `ℐ`-adic filtration of the structure sheaf. -/
@[ega "0 15.2.1" "partial"]
abbrev idealPower : X.Modules :=
  Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmulModule I n (structureModule X)

/-- The inclusion `ℐⁿ⁺¹ · 𝒪_X ⟶ ℐⁿ · 𝒪_X`. -/
abbrev idealPowerStep : idealPower I (n + 1) ⟶ idealPower I n :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep I (structureModule X) n

/-- `ℐⁿ · 𝒪_X` is quasi-coherent. -/
instance isQuasicoherent_idealPower : (idealPower I n).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.IdealPowerSmul.isQuasicoherent_idealPowSmul I n (structureModule X)

/-- **`ℐⁿ/ℐⁿ⁺¹`, as a sheaf of `𝒪_X`-modules.** -/
def grPiece : X.Modules := cokernel (idealPowerStep I n)

/-- The quotient map `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹`. -/
def grPieceπ : idealPower I n ⟶ grPiece I n := cokernel.π (idealPowerStep I n)

/-- The quotient map `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹` is an epimorphism. -/
instance epi_grPieceπ : Epi (grPieceπ I n) :=
  inferInstanceAs (Epi (cokernel.π (idealPowerStep I n)))

/-- The composite `ℐⁿ⁺¹ · 𝒪_X ⟶ ℐⁿ · 𝒪_X ⟶ ℐⁿ/ℐⁿ⁺¹` is zero. -/
@[simp] lemma idealPowerStep_comp_grPieceπ :
    idealPowerStep I n ≫ grPieceπ I n = 0 := cokernel.condition _

/-- **The defining short exact sequence `0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹ ⟶ 0`.** -/
theorem grPiece_shortExact :
    (ShortComplex.mk (idealPowerStep I n) (grPieceπ I n)
      (idealPowerStep_comp_grPieceπ I n)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstance
  epi_g := inferInstance

/-- The inclusion `ℐⁿ⁺¹ · 𝒪_X ⟶ ℐⁿ · 𝒪_X` is a kernel of the quotient map `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹`. -/
noncomputable def idealPowerStepIsKernel :
    IsLimit (KernelFork.ofι (idealPowerStep I n) (idealPowerStep_comp_grPieceπ I n)) :=
  (grPiece_shortExact I n).fIsKernel

/-- `ℐⁿ/ℐⁿ⁺¹` is quasi-coherent. -/
instance isQuasicoherent_grPiece : (grPiece I n).IsQuasicoherent :=
  inferInstanceAs ((cokernel (idealPowerStep I n)).IsQuasicoherent)

/-! ### Sections over an affine open -/

/-- **Over an affine open the quotient map `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹` is surjective on sections.** -/
theorem surjective_grPieceπ_app (V : X.affineOpens) :
    Function.Surjective ((grPieceπ I n).app V.1) :=
  Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X (grPieceπ I n) V.1 V.2

/-- **Over an affine open the sections of `ℐⁿ` killed in `ℐⁿ/ℐⁿ⁺¹` are exactly those coming
from `ℐⁿ⁺¹`.** -/
theorem exact_grPieceπ_app (V : X.affineOpens) :
    Function.Exact ((idealPowerStep I n).app V.1) ((grPieceπ I n).app V.1) :=
  Stacks.Algebraization.affine_sections_cokernel_exact
    (idealPowerStep I n) V

/-- The sections of `ℐⁿ · 𝒪_X` over an affine open `V` are the degree-`n` term `ℐ(V)ⁿ` of the
`ℐ(V)`-adic filtration of `Γ(X, V)`. -/
def idealPowerSectionsEquiv (V : X.affineOpens) :
    ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n) ≃ₗ[Γ(X, V.1)]
      Γ(idealPower I n, V.1) :=
  LinearEquiv.ofEq
    (AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n)
    ((Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul I n
      (structureModule X)).toSubmodule.obj (op V.1))
    (Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul I n (structureModule X) V).symm

/-- The submodule `ℐ(V)ⁿ⁺¹` of `ℐ(V)ⁿ`, as a `Γ(X, V)`-submodule; the quotient by it is the
degree-`n` piece of the algebraic associated graded. -/
abbrev pieceRel (V : X.affineOpens) :
    Submodule Γ(X, V.1) ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n) :=
  (AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) (n + 1)).comap
    (Submodule.subtype (AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n))

/-- The composite `ℐ(V)ⁿ ≃ Γ(V, ℐⁿ) ⟶ Γ(V, ℐⁿ/ℐⁿ⁺¹)`: an element of the degree-`n` term of the
algebraic filtration, read as a section of `ℐⁿ` and then reduced mod `ℐⁿ⁺¹`. -/
def grPieceSectionsMk (V : X.affineOpens) :
    ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n) →+ Γ(grPiece I n, V.1) where
  toFun x := (grPieceπ I n).app V.1 (idealPowerSectionsEquiv I n V x)
  map_zero' := by simp
  map_add' x y := by simp

/-- `grPieceSectionsMk` sends `x ∈ ℐ(V)ⁿ` to the image in `Γ(V, ℐⁿ/ℐⁿ⁺¹)` of the corresponding
section of `ℐⁿ`. -/
@[simp] lemma grPieceSectionsMk_apply (V : X.affineOpens)
    (x : ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n)) :
    grPieceSectionsMk I n V x = (grPieceπ I n).app V.1 (idealPowerSectionsEquiv I n V x) := rfl

/-- Over an affine open `V`, every section of `ℐⁿ/ℐⁿ⁺¹` is the image of an element of `ℐ(V)ⁿ`. -/
theorem surjective_grPieceSectionsMk (V : X.affineOpens) :
    Function.Surjective (grPieceSectionsMk I n V) :=
  (surjective_grPieceπ_app I n V).comp (idealPowerSectionsEquiv I n V).surjective

/-- **An element of `ℐ(V)ⁿ` dies in `Γ(V, ℐⁿ/ℐⁿ⁺¹)` exactly when it lies in `ℐ(V)ⁿ⁺¹`.** -/
theorem grPieceSectionsMk_eq_zero_iff (V : X.affineOpens)
    (x : ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n)) :
    grPieceSectionsMk I n V x = 0 ↔ Submodule.mkQ (pieceRel I n V) x = 0 := by
  rw [grPieceSectionsMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    exact_grPieceπ_app I n V]
  constructor
  · rintro ⟨b, hb⟩
    have hval : (x : Γ(X, V.1)) =
        valSection (structureModule X) (idealPowFamily I (n + 1) (structureModule X))
          (isCompatible_idealPowFamily I (n + 1) (structureModule X)) b :=
      congrArg Subtype.val hb.symm
    have hmem := (isLocallyIn_iff_mem (structureModule X)
      (idealPowFamily I (n + 1) (structureModule X))
      (isCompatible_idealPowFamily I (n + 1) (structureModule X)) V _).mp
        (isLocallyIn_valSection (structureModule X)
          (idealPowFamily I (n + 1) (structureModule X))
          (isCompatible_idealPowFamily I (n + 1) (structureModule X)) b)
    rwa [← hval] at hmem
  · intro hx
    have hloc : IsLocallyIn (structureModule X) (idealPowFamily I (n + 1) (structureModule X))
        x.1 :=
      (isLocallyIn_iff_mem (structureModule X) (idealPowFamily I (n + 1) (structureModule X))
        (isCompatible_idealPowFamily I (n + 1) (structureModule X)) V _).mpr hx
    exact ⟨mkSection (structureModule X) (idealPowFamily I (n + 1) (structureModule X))
      (isCompatible_idealPowFamily I (n + 1) (structureModule X)) _ hloc,
      valSection_inj (structureModule X) (idealPowFamily I n (structureModule X))
        (isCompatible_idealPowFamily I n (structureModule X)) rfl⟩

/-- **Over an affine open the sections of `ℐⁿ/ℐⁿ⁺¹` are the algebraic associated graded piece
`ℐ(V)ⁿ/ℐ(V)ⁿ⁺¹`.** -/
def grPieceSectionsEquiv (V : X.affineOpens) :
    AssociatedGraded.piece (M := Γ(X, V.1)) (I.ideal V) n ≃+ Γ(grPiece I n, V.1) :=
  addEquivOfSurjectiveKerEq (Submodule.mkQ (pieceRel I n V)).toAddMonoidHom
    (grPieceSectionsMk I n V) (Submodule.mkQ_surjective _)
    (surjective_grPieceSectionsMk I n V)
    fun x => (grPieceSectionsMk_eq_zero_iff I n V x).symm

/-- `grPieceSectionsEquiv` sends the class of `x ∈ ℐ(V)ⁿ` in `ℐ(V)ⁿ/ℐ(V)ⁿ⁺¹` to the image of `x`
in `Γ(V, ℐⁿ/ℐⁿ⁺¹)`. -/
@[simp] lemma grPieceSectionsEquiv_mk (V : X.affineOpens)
    (x : ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n)) :
    grPieceSectionsEquiv I n V (AssociatedGraded.mk (I.ideal V) n x) =
      grPieceSectionsMk I n V x :=
  addEquivOfSurjectiveKerEq_apply _ _ _ _ _ x

end Stacks.Conormal

end
