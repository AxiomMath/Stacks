module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.PushforwardIdealPowerGradedModulePlus
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.ProperQcoh.Basic

/-!
# The homogeneous pieces of `⨁ₙ R ᵖ f_*(ℐⁿℱ)` are quasi-coherent

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, `ℱ` a quasi-coherent
`𝒪_X`-module and `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals. The graded
`𝒜 = ⨁ₙ ℐⁿ`-module `Stacks.Blowup.pushforwardReesGradedModulePlus` has `R ᵖ f_*(ℐⁿℱ)` in degree
`n`, for every *integer* `n`. This file proves that every one of those pieces is quasi-coherent.

## Main results

* `Stacks.Blowup.reesMultiple_isQuasicoherent'`: `ℐⁿℱ` is quasi-coherent in every integer
  degree. In nonnegative degrees this is `Stacks.Blowup.reesMultiple_isQuasicoherent`; in
  negative degrees `ℐⁿℱ` is the zero subsheaf of `ℱ`.
* `Stacks.Blowup.isQuasicoherent_piece_pushforwardReesGradedModulePlus`: every homogeneous piece
  of `⨁ₙ R ᵖ f_*(ℐⁿℱ)` is quasi-coherent.

## Implementation notes

The degrees of a `SheafOfModules.GradedModule` are integers while the source's sum ranges over
`n ≥ 0`, so the negative degrees have to be covered as well; there the piece is the zero
subsheaf (`Stacks.Blowup.reesMultiple_eq_bot_of_neg`), whose higher direct images vanish and are
therefore quasi-coherent.

Quasi-coherence of the higher direct image itself is [Stacks, Tag 01XJ] in the `ℕ`-indexing of
`CategoryTheory.Functor.rightDerived`, which is
`Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived`; that is the indexing
this whole chain uses.

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Blowup

/-- The zero subsheaf of a sheaf of modules is a zero object: all of its sections vanish. -/
public theorem isZero_toSheafOfModules_bot {X : Scheme.{u}} (F : X.Modules) :
    IsZero ((⊥ : F.Submodule).toSheafOfModules : X.Modules) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext y
  have h : ∀ w : ((⊥ : F.Submodule).toSheafOfModules).val.obj U, w = 0 := fun w =>
    Subtype.ext ((Submodule.mem_bot _).1 ((SheafOfModules.Submodule.bot_obj F U).le w.2))
  exact (h _).trans (h _).symm

/-- **`ℐⁿℱ` is quasi-coherent in every integer degree** when `ℱ` is. In nonnegative degrees this
is `Stacks.Blowup.reesMultiple_isQuasicoherent`; in negative degrees `ℐⁿℱ` is the zero subsheaf
of `ℱ`, hence a zero object. -/
public theorem reesMultiple_isQuasicoherent' {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (F : X.Modules) [F.IsQuasicoherent] :
    (reesMultiple I n F).toSheafOfModules.IsQuasicoherent := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact reesMultiple_isQuasicoherent I m F
  · have he : reesMultiple I n F = ⊥ := reesMultiple_eq_bot_of_neg I n F hn
    show ((reesMultiple I n F).toSheafOfModules : X.Modules).IsQuasicoherent
    rw [he]
    exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (R := X.ringCatSheaf) (isZero_toSheafOfModules_bot F)

/-- `ℐⁿℱ` for the inverse image ideal `ℐ𝒪_X` is quasi-coherent in every integer degree. -/
public theorem reesComapMod_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℤ) :
    (reesComapMod f I F n).IsQuasicoherent :=
  reesMultiple_isQuasicoherent' (I.comap f) n F

/-- **Every homogeneous piece of `⨁ₙ R ᵖ f_*(ℐⁿℱ)` is quasi-coherent.** The piece in degree `n`
is `R ᵖ f_*(ℐⁿℱ)`, and `ℐⁿℱ` is quasi-coherent, so this is [Stacks, Tag 01XJ].

This is the side condition of the affine criterion
`SheafOfModules.GradedModule.isFiniteType_of_affine_span` at this graded module. -/
public theorem isQuasicoherent_piece_pushforwardReesGradedModulePlus {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (I : Y.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (p : ℕ) (n : ℤ) :
    ((pushforwardReesGradedModulePlus f I F p).piece n).IsQuasicoherent :=
  have := reesComapMod_isQuasicoherent f I F n
  Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived f
    (reesComapMod f I F n) p

end Stacks.Blowup

end

end
