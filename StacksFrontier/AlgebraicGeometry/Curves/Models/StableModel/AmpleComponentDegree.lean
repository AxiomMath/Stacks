module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# An invertible module of positive degree on every component of the special fibre

In the situation of [Stacks, Tag 0C61] the model `X` is projective over `R`
([Stacks, Tag 0C5P]), hence quasi-projective, and over the affine base `Spec R` its relatively
ample invertible module is ample ([Stacks, Tag 01VT]). Each irreducible component `C_Z` of the
special fibre is an integral proper curve over `k` whose closed immersion into `X` is affine, so
the restriction of an ample invertible module to `C_Z` has positive degree.

## Main results

* `exists_isInvertible_forall_specialFiberComponentDegree_pos`: there is an invertible
  `𝒪_X`-module whose degree on every irreducible component of the special fibre is positive.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **An invertible module of positive degree on every component of the special fibre.** An ample
invertible `𝒪_X`-module, which exists since the model is projective over `R`, has positive degree
on every irreducible component of the special fibre. -/
theorem exists_isInvertible_forall_specialFiberComponentDegree_pos :
    ∃ (L : S.X.Modules) (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
        (structureSheafRing S.X.toRingedSpace).property L),
      ∀ Z, 0 < S.specialFiberComponentDegree Z L hL := by
  have hmod : IsModel S.C_to_K S.X_to_R S.genericFiberIso :=
    ⟨S.flat, S.locallyOfFiniteType, S.quasiCompact, S.genericFiberIso_over_K⟩
  have hproj := isProjective_of_isModel_of_isRegular S.C_to_K S.X_to_R S.genericFiberIso hmod
    S.regular
  obtain ⟨-, L, hL, hrel⟩ := isQuasiProjective_of_isProjective hproj
  have hamp : Stacks.Ample.IsAmple S.X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine S.X_to_R L hrel
  have hLag : AlgebraicGeometry.SheafOfModules.IsInvertible S.X.toRingedSpace.presheaf
      (structureSheafRing S.X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have hmodAmp : Scheme.Modules.IsAmple S.X L :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple S.X L hamp
  have : AlgebraicGeometry.SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L := hLag
  refine ⟨L, hL, fun Z => ?_⟩
  exact invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom S.k
    (S.specialFiberComponentToSpec Z) (S.topologicalKrullDim_specialFiberComponent_eq_one Z)
    (S.specialFiberComponentIdeal Z).subschemeι L hmodAmp

end Stacks.Models.RegularProperModelSituation

end
