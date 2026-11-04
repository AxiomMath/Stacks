module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentHmap
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue

/-!
# Descent of finite locally free modules through a limit of schemes

Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated schemes
with affine transition morphisms.  [Stacks Project, Tag 0B8W] (1) asserts that every finite
locally free `𝒪_S`-module is the pullback of a finite locally free `𝒪_{Sᵢ}`-module for some `i`.

This file proves that statement under the hypothesis `hEventuallyFiniteLocallyFree`: a module of
finite presentation at a stage whose pullback to the limit is finite locally free is finite
locally free after some transition morphism (Tags 02JO and 00NX in the form the source uses).
The hypothesis is discharged in
`StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeUnconditional`, which proves
Tag 0B8W (1) unconditionally from this statement; the statement here is therefore untagged.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation`: a finite locally
  free sheaf of modules on a scheme is of finite presentation.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso_of_eventually`:
  Tag 0B8W (1) granted the eventual finite local freeness of the descended module.

## Implementation notes

The finite-local-freeness predicate used is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` is a reducible spelling of the same class, and
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree` is its pointwise form.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe v u

namespace AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree

/-- A finite locally free sheaf of modules on a scheme is of finite presentation. -/
theorem isFinitePresentation {X : Scheme.{u}} (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) : E.IsFinitePresentation :=
  (Stacks.FiniteLocallyFree.isLocallyFree_isFiniteType_isFinitePresentation E).2.2

end AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **A module on the limit which is the pullback of one from a stage is the pullback of one from
every earlier stage.**  If `E` on the cone point is the pullback of `Eᵢ` along the projection to
the stage `i`, then along any transition morphism `e : j ⟶ i` it is the pullback of the pullback
of `Eᵢ` to the stage `j`. -/
noncomputable def isoPullbackMapOfIsoPullback {i j : I} (e : j ⟶ i) {Eᵢ : (D.obj i).Modules}
    {E : c.pt.Modules} (h : E ≅ (Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) :
    E ≅ (Scheme.Modules.pullback (c.π.app j)).obj
      ((Scheme.Modules.pullback (D.map e)).obj Eᵢ) :=
  h ≪≫ ((canNatIso (c.π.app j) (D.map e) (c.π.app i) (c.w e)).app Eᵢ).symm

include c in
/-- **Stacks Project, Tag 0B8W (1), granted the eventual finite local freeness of the descended
module.**  Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated
schemes with affine transition morphisms.  Then every finite locally free `𝒪_S`-module is the
pullback of a finite locally free `𝒪_{Sᵢ}`-module for some `i`.

The hypothesis `hEventuallyFiniteLocallyFree` says that a module of finite presentation at a stage
whose pullback to the limit is finite locally free becomes finite locally free along some
transition morphism; it is discharged by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso`. -/
theorem exists_isFiniteLocallyFree_pullback_iso_of_eventually (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hEventuallyFiniteLocallyFree : ∀ (i : I) (Eᵢ : (D.obj i).Modules),
      Eᵢ.IsFinitePresentation →
      SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) →
        ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((Scheme.Modules.pullback (D.map e)).obj Eᵢ))
    (E : c.pt.Modules) (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    ∃ (i : I) (Eᵢ : (D.obj i).Modules),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eᵢ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) := by
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E := hE
  have : E.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation E hE
  obtain ⟨i, Eᵢ, hfp, ⟨eE⟩⟩ := exists_isFinitePresentation_pullback_iso_of_qcqs D c hc E
  have hpb : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) :=
    SheafOfModules.IsFiniteLocallyFree.of_iso eE
  obtain ⟨j, e, hj⟩ := hEventuallyFiniteLocallyFree i Eᵢ hfp hpb
  exact ⟨j, (Scheme.Modules.pullback (D.map e)).obj Eᵢ, hj,
    ⟨isoPullbackMapOfIsoPullback D c e eE⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
