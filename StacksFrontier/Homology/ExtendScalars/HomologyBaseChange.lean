module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Base change of the cohomology of a complex

Let `φ : B → B'` be a ring map and let `X^•` be a cochain complex of `B`-modules.  Termwise
extension of scalars along `φ` is a left adjoint, so it preserves cokernels, and the cohomology of
a complex in a degree is the cokernel of the map from the previous term into the cycles.  The
degree-`n` cohomology of `X^• ⊗_B B'` is therefore `H^n(X^•) ⊗_B B'` as soon as the cycles base
change, which is the one thing extension of scalars does not do for free: cycles are a kernel.

## Main definitions

* `StacksDraft.HomologyBaseChange.cyclesComparison` -- the canonical map
  `B' ⊗_B Z^n(X^•) ⟶ Z^n(X^• ⊗_B B')`.

## Main results

* `StacksDraft.HomologyBaseChange.nonempty_extendScalars_homology_iso_of_isIso_cyclesComparison`
  -- if the cycles base change in degree `n`, so does the cohomology:
  `B' ⊗_B H^n(X^•) ≅ H^n(X^• ⊗_B B')`.

## Implementation notes

The hypothesis is read on `StacksDraft.HomologyBaseChange.cyclesComparison` rather than as an
abstract isomorphism, because the proof needs it to be *that* map: it is the one making the square
with `HomologicalComplex.toCycles` commute, and the two cokernel presentations are compared through
that square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft.HomologyBaseChange

noncomputable section

variable {B B' : Type u} [CommRing B] [CommRing B'] (φ : B →+* B')

/-- Termwise extension of scalars along `φ`, on cochain complexes. -/
abbrev extendComplex :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B') ℤ :=
  (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The canonical comparison on cycles.**  The base change of the degree-`n` cycles of `X^•` maps
to the degree-`n` cycles of `X^• ⊗_B B'`, because the base change of the inclusion of the cycles is
killed by the differential. -/
def cyclesComparison (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (X.cycles n) ⟶
      ((extendComplex φ).obj X).cycles n :=
  ((extendComplex φ).obj X).liftCycles
    ((ModuleCat.extendScalars.{u, u, u} φ).map (X.iCycles n)) (n + 1) (by simp) (by
      have h : ((extendComplex φ).obj X).d n (n + 1) =
          (ModuleCat.extendScalars.{u, u, u} φ).map (X.d n (n + 1)) := rfl
      rw [h, ← Functor.map_comp, HomologicalComplex.iCycles_d, Functor.map_zero])

/-- The comparison on cycles, followed by the inclusion of the cycles of the base-changed complex,
is the base change of the inclusion of the cycles of `X^•`. -/
@[reassoc (attr := simp)]
theorem cyclesComparison_iCycles (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    cyclesComparison φ X n ≫ ((extendComplex φ).obj X).iCycles n =
      (ModuleCat.extendScalars.{u, u, u} φ).map (X.iCycles n) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The comparison on cycles makes the square with `HomologicalComplex.toCycles` commute: the base
change of the map from the previous term into the cycles, followed by the comparison, is that map
for the base-changed complex. -/
theorem map_toCycles_comp_cyclesComparison (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} φ).map (X.toCycles (n - 1) n) ≫
        cyclesComparison φ X n =
      ((extendComplex φ).obj X).toCycles (n - 1) n := by
  apply (cancel_mono (((extendComplex φ).obj X).iCycles n)).mp
  rw [Category.assoc, cyclesComparison_iCycles, ← Functor.map_comp,
    HomologicalComplex.toCycles_i, HomologicalComplex.toCycles_i]
  rfl

/-- **Base change of cohomology.**  If the comparison on degree-`n` cycles is an isomorphism, then
the base change of `H^n(X^•)` is `H^n(X^• ⊗_B B')`.  Both sides are cokernels of the map from the
term in degree `n - 1` into the degree-`n` cycles -- the left-hand one because extension of scalars
is a left adjoint and therefore preserves cokernels -- and the comparison on cycles identifies the
two presentations. -/
theorem nonempty_extendScalars_homology_iso_of_isIso_cyclesComparison
    (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) (h : IsIso (cyclesComparison φ X n)) :
    Nonempty ((ModuleCat.extendScalars.{u, u, u} φ).obj (X.homology n) ≅
      ((extendComplex φ).obj X).homology n) := by
  have := h
  let : Limits.PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u} φ).leftAdjoint_preservesColimits
  let : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits _
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by simp
  let cX := isColimitCoforkMapOfIsColimit' (ModuleCat.extendScalars.{u, u, u} φ)
    (X.toCycles_comp_homologyπ (n - 1) n) (X.homologyIsCokernel (n - 1) n hprev)
  let cY := ((extendComplex φ).obj X).homologyIsCokernel (n - 1) n hprev
  obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' cX
    (cyclesComparison φ X n ≫ ((extendComplex φ).obj X).homologyπ n)
    (by rw [← Category.assoc, map_toCycles_comp_cyclesComparison,
      HomologicalComplex.toCycles_comp_homologyπ])
  obtain ⟨e', he'⟩ := CokernelCofork.IsColimit.desc' cY
    (CategoryTheory.inv (cyclesComparison φ X n) ≫
      (ModuleCat.extendScalars.{u, u, u} φ).map (X.homologyπ n))
    (by rw [← map_toCycles_comp_cyclesComparison, Category.assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ, Functor.map_zero])
  rw [CokernelCofork.π_ofπ] at he he'
  refine ⟨{ hom := e, inv := e', hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · refine Cofork.IsColimit.hom_ext cX ?_
    simp [← Category.assoc, he]
    simp [he']
  · refine Cofork.IsColimit.hom_ext cY ?_
    simp [← Category.assoc, he']
    simp [he]

end

end StacksDraft.HomologyBaseChange

end
