module

public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphism
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# The derived pullback of a derived module along a morphism into its single-degree locus

Let `X` be a scheme, `E` an object of the derived category of sheaves of modules on `X`, `i` an
integer and `r` a natural number, and let `U = singleDegreeRankOpen E i r` be the largest open
subscheme of `X` on which `E` is a finite locally free module of rank `r` placed in degree `i`.
A morphism of schemes `f : Y ⟶ X` which factors through `U` has `Lf^* E` isomorphic to a finite
locally free module of rank `r` placed in degree `i`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank`: a sheaf of modules on
  a scheme which is finite locally free of rank `r` is flat.
* `AlgebraicGeometry.derivedPullbackSingleFlatIso`: for a flat sheaf of modules `M` on a ringed
  space and a degree `d`, the derived pullback `Lf^*(M[-d])` is the ordinary pullback `f^* M`
  placed in degree `d`.
* `Scheme.Modules.exists_isFiniteLocallyFreeOfRank_derivedPullback_of_factorsThrough`:
  a morphism of schemes factoring through `U` has `Lf^* E` a finite locally free module of rank
  `r` placed in degree `i`.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
* [The Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [The Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [The Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Flatness of a finite locally free module of a fixed rank -/

/-- A sheaf of modules on a scheme which is finite locally free of rank `r` is flat. -/
theorem SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules)
    (r : ℕ) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M :=
  have := hM
  AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree M
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r)

/-! ### The derived pullback of a flat module placed in one degree -/

section SingleFlat

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The canonical map `Lf^*(M[-d]) ⟶ (f^* M)[-d]` is invertible at a flat module `M`, in every
degree `d`. -/
theorem isIso_derivedToOrdinaryPullbackSingle_of_isFlat
    (M : SheafOfModules.{u} (structureSheafRing Y))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M) (d : ℤ) :
    IsIso (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle f M d) :=
  AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingle f M d
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf M hM d))

/-- For `M` a flat `𝒪_Y`-module and `d` an integer, `Lf^*(M[-d])` is the ordinary pullback
`f^* M` placed in degree `d`, by the canonical map
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle`. -/
def derivedPullbackSingleFlatIso (M : SheafOfModules.{u} (structureSheafRing Y))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M) (d : ℤ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((modulePullback f).obj M) :=
  @asIso _ _ _ _ _ (isIso_derivedToOrdinaryPullbackSingle_of_isFlat f M hM d)

end SingleFlat

/-! ### Morphisms factoring through the single-degree locus -/

namespace Scheme.Modules

/-- A morphism of schemes `f : Y ⟶ X` factoring through the open subscheme
`U = singleDegreeRankOpen E i r` has `Lf^* E` a finite locally free module of rank `r` placed in
degree `i`. -/
theorem exists_isFiniteLocallyFreeOfRank_derivedPullback_of_factorsThrough {X Y : Scheme.{u}}
    (E : DerivedCategory X.Modules) (i : ℤ) (r : ℕ) (f : Y ⟶ X)
    (hf : ∃ g : Y ⟶ (singleDegreeRankOpen E i r).toScheme,
      g ≫ (singleDegreeRankOpen E i r).ι = f) :
    ∃ M : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
          (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  obtain ⟨g, hg⟩ := hf
  have hN := isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen E i r
  have hflat := AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank _ r hN
  have hs : g.toLRSHom.toShHom ≫ (singleDegreeRankOpen E i r).ι.toLRSHom.toShHom =
      f.toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : Y ⟶ X => k.toLRSHom.toShHom) hg
  refine ⟨(modulePullback g.toLRSHom.toShHom).obj
      ((DerivedCategory.homologyFunctor (singleDegreeRankOpen E i r).toScheme.Modules i).obj
        ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E)),
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g _ r, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj E) hs).symm ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      g.toLRSHom.toShHom (singleDegreeRankOpen E i r).ι.toLRSHom.toShHom).app E).symm ≪≫
    (derivedPullback g.toLRSHom.toShHom).mapIso
      (((derivedRestrictIsoDerivedPullback (singleDegreeRankOpen E i r).ι).app E).symm ≪≫
        (nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen E i r).some) ≪≫
    derivedPullbackSingleFlatIso g.toLRSHom.toShHom _ hflat i

/-- For a morphism `p : Z ⟶ U` into the open subscheme `U = singleDegreeRankOpen E i r`, the
derived pullback of `E` along `p ≫ U.ι` is a finite locally free module of rank `r` placed in
degree `i`. -/
theorem exists_isFiniteLocallyFreeOfRank_derivedPullback_comp_ι {X Z : Scheme.{u}}
    (E : DerivedCategory X.Modules) (i : ℤ) (r : ℕ)
    (p : Z ⟶ (singleDegreeRankOpen E i r).toScheme) :
    ∃ M : Z.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((derivedPullback
            (p ≫ (singleDegreeRankOpen E i r).ι).toLRSHom.toShHom).obj E ≅
          (DerivedCategory.singleFunctor Z.Modules i).obj M) :=
  exists_isFiniteLocallyFreeOfRank_derivedPullback_of_factorsThrough E i r _ ⟨p, rfl⟩

end Scheme.Modules

end AlgebraicGeometry

end
