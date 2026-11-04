module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.QuasiFiniteGorenstein
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibility
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

/-!
# Invertibility of the relative dualizing module of a quasi-finite syntomic morphism

For a quasi-finite flat algebra `B` over a Noetherian ring `A` admitting a presentation
`B = A[x_1, …, x_n]/(f_1, …, f_n)` with as many relations as variables, the relative dualizing
module `ω_{B/A}` is an invertible `B`-module. Consequently, for a locally quasi-finite syntomic
morphism `f : Y ⟶ X` of locally Noetherian schemes, `ω_{Y/X}` is an invertible `𝒪_Y`-module.

## Main results

* `Stacks.Discriminant.dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection`: the
  affine case for a quasi-finite flat relative global complete intersection.
* `Stacks.Discriminant.dualizingModule_invertible_of_squarePresentation`: **Stacks 0BWF** in the
  affine case, which is the case the source reduces to.
* `Stacks.Discriminant.exists_chart_dualizingModule_invertible_of_locallyQuasiFinite_syntomic`:
  **Stacks 0BWF** at the scheme level, stated at the charts of `f`.
* `Stacks.Discriminant.isInvertible_of_locallyQuasiFinite_syntomic`: the same, read as
  invertibility of the glued sheaf of a chart datum for `ω_{Y/X}`.

## Implementation notes

This is the source's argument. A square presentation of a quasi-finite algebra is a relative
global complete intersection (Stacks 00SP), so each of its fibres `B ⊗_A κ(p)` is a global
complete intersection over `κ(p)`; quasi-finiteness makes those fibres artinian, hence of Krull
dimension `0`, so Stacks 0DWL gives invertibility of `ω_{B ⊗_A κ(p)/κ(p)}`, and Stacks 0DWK
lifts that to invertibility of `ω_{B/A}`. A fibre that is the zero ring is excluded from the
Krull dimension statement — its Krull dimension is `⊥`, not `0` — and is handled separately:
every module over the zero ring is invertible.

The relative dualizing module of the library is computed from a finite-open factorization of
`A → B` (Stacks 0BSZ); the choice is immaterial by `Stacks.Discriminant.dualizingModuleEquiv`,
so the statement is for an arbitrary one.

Flatness and finite presentation of `B` over `A` are not assumed: the source derives them from
syntomicity, and so do the statements here, through
`AlgebraicGeometry.flat` and `AlgebraicGeometry.locallyOfFinitePresentation`.

The reduction to the affine case is part (5) of Stacks 0BWE, which produces around every point
of `Y` an affine open `V = Spec B` over an affine open `U = Spec A` of `X` with
`B = A[x_1, …, x_n]/(f_1, …, f_n)`. The scheme-level statement is therefore stated at those
charts: invertibility of `ω_{Y/X}` as a sheaf refers to a chart datum
`Stacks.Discriminant.RelativeDualizingModuleData` for it, whose existence is Stacks 0BVG and is
not available in that packaged form, so
`Stacks.Discriminant.isInvertible_of_locallyQuasiFinite_syntomic` takes such a datum and carries
no tag; the chartwise form, which is condition (4) of
Stacks 0C16 and equivalent to invertibility of the sheaf by
`Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible`, is
unconditional.

## References

* [Stacks Project, Tag 0BWF](https://stacks.math.columbia.edu/tag/0BWF)
* [Stacks Project, Tag 0DWK](https://stacks.math.columbia.edu/tag/0DWK)
* [Stacks Project, Tag 0DWL](https://stacks.math.columbia.edu/tag/0DWL)
* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 0C16](https://stacks.math.columbia.edu/tag/0C16)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Stacks.Discriminant

/-- Every module over the zero ring is invertible. -/
theorem module_invertible_of_subsingleton (R : Type*) (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Subsingleton R] : Module.Invertible R M :=
  ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- Let `A → B` be a quasi-finite flat homomorphism of Noetherian rings which is a relative
global complete intersection. Then the relative dualizing module `ω_{B/A}` is an invertible
`B`-module. -/
theorem dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B] [Module.Flat A B]
    [Algebra.IsRelativeGlobalCompleteIntersection A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.Invertible B (dualizingModule F) := by
  obtain ⟨m, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection A B›.out
  have hfp : Algebra.FinitePresentation A B := P.finitePresentation_of_isFinite
  have : Algebra.FiniteType A B := inferInstance
  refine (dualizingModule_invertible_iff_fibers F).mpr fun p G ↦ ?_
  rcases subsingleton_or_nontrivial (p.asIdeal.Fiber B) with h | h
  · exact module_invertible_of_subsingleton _ _
  · exact dualizingModule_invertible_of_isGlobalCompleteIntersection G
      (hP.isGlobalCompleteIntersection_fiber p.asIdeal)
      (ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
        (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp
          (inferInstanceAs (IsArtinianRing (p.asIdeal.Fiber B)))).2)

/-- **Stacks Project, Tag 0BWF**, the affine case the source reduces to. Let `A → B` be a
quasi-finite flat homomorphism of Noetherian rings with a presentation
`B = A[x_1, …, x_n]/(f_1, …, f_n)` by as many relations as variables. Then the relative
dualizing module `ω_{B/A}` is an invertible `B`-module. -/
@[stacks 0BWF "the affine case: a square relative global complete intersection presentation,
which is part (5) of Stacks 0BWE"]
theorem dualizingModule_invertible_of_squarePresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B] [Module.Flat A B]
    {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.Invertible B (dualizingModule F) :=
  let : Algebra.IsRelativeGlobalCompleteIntersection A B := .of_card_eq P (by simp)
  dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection F

/-! ### The scheme-level statement -/

section Scheme

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f]

/-- **Stacks Project, Tag 0BWF.** Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism of
locally Noetherian schemes. Then every point of `Y` has an affine open neighbourhood
`V = Spec B` lying over an affine open `U = Spec A` of `X` for which the algebraic relative
dualizing module `ω_{B/A}` is an invertible `B`-module. -/
@[stacks 0BWF "the scheme-level statement, stated at the charts of `f`: every point of `Y` has an
affine open `V = Spec B` over an affine open `U = Spec A` of `X` on which `ω_{B/A}` is
invertible. This is condition (4) of Stacks 0C16, which
`Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible` identifies with
invertibility of `ω_{Y/X}` as a sheaf."]
theorem exists_chart_dualizingModule_invertible_of_locallyQuasiFinite_syntomic
    (hf : Syntomic f) :
    ∀ y : Y, ∃ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1), y ∈ V.1 ∧
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
        Module.Invertible Γ(Y, V.1) (dualizingModule F) := by
  have : Flat f := AlgebraicGeometry.flat hf
  intro y
  obtain ⟨V, U, hyV, hVU, n, P, -⟩ :=
    hasLocalSquareRelativeGlobalCompleteIntersection_of_locallyQuasiFinite_syntomic
      inferInstance hf y
  refine ⟨U, V, hVU, hyV, ?_⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  intro F
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  exact dualizingModule_invertible_of_squarePresentation P F

/-- The relative dualizing module of a locally quasi-finite syntomic morphism of locally
Noetherian schemes is an invertible `𝒪_Y`-module, for any chart datum `ω` of `ω_{Y/X}` in the
sense of Stacks 0BVG. -/
theorem isInvertible_of_locallyQuasiFinite_syntomic (hf : Syntomic f)
    (ω : RelativeDualizingModuleData f) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property ω.sheaf :=
  have : Flat f := AlgebraicGeometry.flat hf
  have : LocallyOfFinitePresentation f := AlgebraicGeometry.locallyOfFinitePresentation hf
  (isInvertible_iff_exists_chart_dualizingModule_invertible ω).mpr
    (exists_chart_dualizingModule_invertible_of_locallyQuasiFinite_syntomic hf)

end Scheme

end Stacks.Discriminant

end
