module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulaySchemeOfDualizingModule
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayConcentration
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
import StacksCore.Tactic.StacksAttribute

/-!
# The sections of a dualizing module over an affine open are a dualizing module

Let `X` be a locally Noetherian scheme and let `ω` be an `𝒪_X`-module whose complex `ω[n]` in
some degree is a dualizing complex on `X` ([Stacks, Tag 0A87]). For every affine open `U` the
`Γ(X, U)`-module `ω(U)` — in the form `Stacks.AlgebraicGeometry.CoherentTFAE.specModule`, the
sections read on `Spec Γ(X, U)` — has its degree-zero complex a dualizing complex over
`Γ(X, U)` ([Stacks, Tag 0A7B]).

This is the passage from the scheme-level predicate to the ring-level one for a module, and it
is what connects `Stacks.Duality.IsDualizingModule` to the commutative algebra of dualizing
complexes. It is the missing half of the gap recorded in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/NormalizedAtClosedPoint.lean`, where
the dualizing character of a stalk is carried as a hypothesis because
`Stacks.Duality.IsDualizingComplex` is connected to `Dualizing.IsDualizingComplex` only over
affine opens: over an affine open the connection is made here, and localization then carries it
to the stalks.

## Main results

* `Stacks.Duality.isDualizingComplex_single_specModule`: `ω(U)[0]` is a dualizing complex over
  `Γ(X, U)`.

## Implementation notes

The dualizing model `D` over `Γ(X, U)` provided by `Stacks.Duality.HasDualizingModelOn` is not
given as a module: the argument that its cohomology sits in the single degree `n` is the one in
the proof of `Stacks.Duality.isCohenMacaulayRing_sections_of_hasDualizingModelOn`, namely that
the two functors relating `D` to `ω[n]` are exact and that the associated-sheaf functor is fully
faithful, hence reflects zero objects. What is added here is the identification of the resulting
module with the sections of `ω`: the same comparison read in degree `n` says that `ω|_U`,
transported to `Spec Γ(X, U)`, is the associated sheaf of `H^n(D)`, and the sections functor of
the associated sheaf is the identity.

The degree is then moved to zero by `Dualizing.isDualizingComplex_shift`, the shift being
recognized through its cohomology.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

omit [IsLocallyNoetherian X] in
/-- A single complex placed in degree `n` has no cohomology away from degree `n`. -/
private theorem isZero_homology_singleFunctor_obj (F : X.Modules) (n i : ℤ) (hi : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules n).obj F)) := by
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact DerivedCategory.isZero_of_isGE _ n i hlt
  · exact DerivedCategory.isZero_of_isLE _ n i hgt

/-- **The sections of a dualizing module over an affine open are a dualizing module.** -/
theorem isDualizingComplex_single_specModule (ω : X.Modules) [ω.IsQuasicoherent] (n : ℤ)
    (hω : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj (specModule ω hU)) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨D, hD, ⟨e⟩⟩ := hω U hU
  set K := (DerivedCategory.singleFunctor X.Modules n).obj ω with hK
  set G := Scheme.Modules.restrictFunctor U.ι with hG
  set F := tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom with hF
  -- Restricting along the inverse of `U ≅ Spec Γ(X, U)` undoes the restriction along it.
  have hback : Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.inv ≅ 𝟭 (Spec Γ(X, U)).Modules :=
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId
  -- In each degree, the comparison `e` identifies `G (H^i ω[n])` with `F (H^i D)`.
  have hiso : ∀ i : ℤ, G.obj ((DerivedCategory.homologyFunctor X.Modules i).obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D) := fun i =>
    ((Dualizing.mapDerivedCategoryHomologyIso G i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor U.toScheme.Modules i).mapIso e ≪≫
      (Dualizing.mapDerivedCategoryHomologyIso F i).app D
  -- The cohomology of the dualizing model `D` vanishes outside degree `n`.
  have hvan : ∀ i : ℤ, i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D) := by
    intro i hi
    have hFH : IsZero (F.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D)) :=
      (G.map_isZero (isZero_homology_singleFunctor_obj ω n i hi)).of_iso (hiso i).symm
    exact IsZero.of_full_of_faithful_of_isZero (tilde.functor Γ(X, U)) _
      (((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map_isZero hFH).of_iso
        (hback.app _).symm)
  -- So `D` is the module `H^n(D)` placed in degree `n`.
  obtain ⟨eD⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero D n hvan
  -- That module is the sections of `ω` over `U`: read the comparison in degree `n`.
  have hcompare : specRestrict ω hU ≅
      (tilde.functor Γ(X, U)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) n).obj D) := by
    refine ?_ ≪≫ (hback.app _)
    exact (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
      (G.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n).app ω).symm
        ≪≫ hiso n)
  have hmod : specModule ω hU ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) n).obj D :=
    moduleSpecΓFunctor.mapIso hcompare ≪≫
      (tilde.isoTop ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) n).obj D)).symm
  -- Transport the dualizing property to the single complex on the sections, in degree `n`.
  have hn : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) n).obj (specModule ω hU)) :=
    ringIsDualizingComplex_of_iso
      (eD ≪≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) n).mapIso hmod).symm) hD
  -- Move the degree to zero: the `n`-fold shift of a single complex in degree `n` is the
  -- single complex in degree zero.
  have hshiftiso :
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) n).obj (specModule ω hU))⟦n⟧ ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj (specModule ω hU) := by
    refine (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ 0
      (fun j hj => ?_)).some ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).mapIso
        (Dualizing.homologyShiftIso _ n 0 ≪≫
          eqToIso (congrArg
            (fun k : ℤ => (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) k).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) n).obj
                (specModule ω hU))) (show n + 0 = n by ring)) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{u} Γ(X, U)) n).app (specModule ω hU))
    refine Dualizing.isZero_homology_shift.{u, u} _ n j ?_
    refine Dualizing.isZero_homology_of_iso_single.{u, u} _ n (specModule ω hU)
      ⟨Iso.refl _⟩ (n + j) (by omega)
  exact ringIsDualizingComplex_of_iso hshiftiso
    (Dualizing.isDualizingComplex_shift _ hn n)

end Stacks.Duality

end
