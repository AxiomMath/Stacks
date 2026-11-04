module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.Examples.QuasiCoherentPushforward.NonvanishingCohomology

/-!
# Derived sections computed in `QCoh(𝒪_X)` are not sheaf cohomology

Let `X` be a scheme and `U ⊆ X` an open. Sections over `U` restrict to a left exact functor
`Γ(U, -) : QCoh(𝒪_X) ⥤ Ab`, and `QCoh(𝒪_X)` has enough injectives, so that functor has right
derived functors `R^i_{QCoh}Γ(U, -)`. Sheaf cohomology `H^i(U, -)` is the right derived functor
of sections on *all* `𝒪_X`-modules, and the two disagree already on an affine scheme: an
injective object of `QCoh(𝒪_X)` has no higher derived sections computed in `QCoh(𝒪_X)`, yet it
can have nonzero first cohomology on a quasi-compact open.

## Main results

* `AlgebraicGeometry.exists_injective_quasicoherentSections_rightDerived_ne_cohomology` — an
  affine scheme, an injective quasi-coherent module on it and a quasi-compact open for which
  `R^1_{QCoh}Γ(U, ℱ) = 0` while `H^1(U, ℱ) ≠ 0`; no morphism between the two is an isomorphism.

## References

* [Stacks Project, Tag 0CRY](https://stacks.math.columbia.edu/tag/0CRY)
* [Stacks Project, Tag 0CRZ](https://stacks.math.columbia.edu/tag/0CRZ)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The functor of sections over the open `U`, restricted to quasi-coherent modules:
`Γ(U, -) : QCoh(𝒪_X) ⥤ Ab`. Its right derived functors are the `R^i_{QCoh}Γ(U, -)` of
[Stacks, Tag 0CRY]. -/
def quasicoherentSections (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ secF X.ringCatSheaf U

/-- The functor `quasicoherentSections X U` is additive. -/
instance quasicoherentSections_additive (X : Scheme.{u}) (U : X.Opens) :
    (quasicoherentSections X U).Additive :=
  inferInstanceAs
    (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ secF X.ringCatSheaf U).Additive)

/-- On an affine scheme the comparison from derived sections computed inside `QCoh(𝒪_X)` to sheaf
cohomology is not an isomorphism. There are a ring `A`, an injective object `ℱ` of
`QCoh(𝒪_{Spec A})` and a quasi-compact open `U ⊆ Spec A` with `R^1_{QCoh}Γ(U, ℱ) = 0` and
`H^1(U, ℱ) ≠ 0`; in particular no morphism from the first group to the second is an isomorphism,
so the canonical `t^1` is not one. -/
@[stacks 0CRY "R^1_QCoh Γ(U, ℱ) = 0 while H^1(U, ℱ) ≠ 0, for ℱ injective in QCoh(𝒪_{Spec A})"]
theorem exists_injective_quasicoherentSections_rightDerived_ne_cohomology :
    ∃ (A : CommRingCat.{u})
      (F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory)
      (U : (Spec A).Opens),
      Injective F ∧ IsCompact (U : Set (Spec A)) ∧
        IsZero (((quasicoherentSections (Spec A) U).rightDerived 1).obj F) ∧
        ¬ IsZero (Hgroup (Spec A).ringCatSheaf U 1
            ((SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι.obj F)) ∧
        ∀ t : ((quasicoherentSections (Spec A) U).rightDerived 1).obj F ⟶
            Hgroup (Spec A).ringCatSheaf U 1
              ((SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι.obj F),
          ¬ IsIso t := by
  obtain ⟨A, I, U, -, hI, hU, hne⟩ :=
    Stacks.Examples.InjectiveTilde.exists_injective_tilde_nonzero_firstCohomology.{u}
  have : Injective ((tildeEquiv (R := A)).functor.obj I) :=
    ((tildeEquiv (R := A)).map_injective_iff I).2 hI
  have hzero : IsZero (((quasicoherentSections (Spec A) U).rightDerived 1).obj
      ((tildeEquiv (R := A)).functor.obj I)) :=
    (quasicoherentSections (Spec A) U).isZero_rightDerived_obj_injective_succ 0 _
  refine ⟨A, (tildeEquiv (R := A)).functor.obj I, U, inferInstance, hU, hzero, hne, ?_⟩
  intro t ht
  have := ht
  exact hne (hzero.of_iso (asIso t).symm)

end AlgebraicGeometry

end
