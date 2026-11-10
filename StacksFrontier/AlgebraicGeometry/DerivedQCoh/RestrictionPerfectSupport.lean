module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenSubspaceBaseRingLinear
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineCase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Restriction along an open immersion preserves perfectness and support

Let `g : Y ⟶ X` be an open immersion of schemes and let `E` be an object of the derived category
of `𝒪_X`-modules. If `E` is perfect then so is `E|_Y`, and if the cohomology sheaves of `E` have
vanishing stalks outside a subset `T` of `X` then those of `E|_Y` have vanishing stalks outside
the preimage of `T`. Both are needed to run the induction of [Stacks, Tag 08DR] on a statement
about the restrictions of a fixed pair of objects: the induction hypothesis is fed restrictions,
and the base case is the statement on a scheme isomorphic to a spectrum, which is reached by
restricting along an isomorphism.

## Main results

* `Stacks.DerivedQCoh.isPerfect_derivedRestrict`: restriction along an open immersion of
  schemes preserves perfectness.
* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor`: restriction along an open
  immersion of schemes pulls back the support.
* `Stacks.DerivedQCoh.isDQCoh_derivedRestrict`: restriction along an open immersion of schemes
  preserves quasi-coherence of the cohomology.
* `Stacks.DerivedQCoh.cohomologySupportedOn_shift`: the support condition is stable under
  shifting.
* `Stacks.DerivedQCoh.derivedJStarIsoDerivedRestrict`: the extension-by-zero spelling of derived
  restriction to an open subscheme, the one the Mayer--Vietoris material of [Stacks, Tag 08BW]
  is written in, is the functor induced on derived categories by Mathlib's restriction along
  `U.ι`.
* `Stacks.DerivedQCoh.smul_eq_zero_of_smul_map_eq_zero`: a morphism killed by a scalar after an
  `A`-linear functor with an `A`-linear retraction is killed by that scalar.

## Implementation notes

Perfectness is transported from the derived pullback: restriction along an open immersion is the
derived pullback along it (`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`),
and the derived pullback of a perfect object along *any* morphism of ringed spaces is perfect
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`, [Stacks, Tag
09UA]). Nothing is proved about perfect complexes here.

The support statement is `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrict` with the
inclusion of an open subscheme replaced by an arbitrary open immersion; the special case is not
reused because its proof runs on `TopCat.Presheaf.stalkRestrictIso`, which compares the stalks of
a sheaf and of its restriction to an open *subspace*, whereas the comparison for a general open
immersion is Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. The generality is
what the base case of the induction needs: there the open immersion is an isomorphism onto a
spectrum, which is not the inclusion of an open subscheme.

`Stacks.DerivedQCoh.smul_eq_zero_of_smul_map_eq_zero` is the mechanism by which a statement
"every morphism of this shape is killed by a power of `a`" is transported along an equivalence:
the functor and its retraction are `A`-linear, so the conclusion crosses, and no compatibility
of the two `A`-linear structures beyond linearity of the two functors is needed.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 20.28.12 (Tag 09UA)](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Lemma 30.3.2 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.SchemeCohomology (ringedSpace hom)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Perfectness and support under restriction -/

section Restriction

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

/-- **Restriction along an open immersion of schemes preserves perfectness.** Restriction is the
derived pullback along the same morphism, and the derived pullback of a perfect object is
perfect ([Stacks, Tag 09UA]). -/
theorem isPerfect_derivedRestrict (E : DerivedCategory X.Modules)
    (hE : IsPerfect (X := ringedSpace X) E) :
    IsPerfect (X := ringedSpace Y)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E) := by
  have h1 : IsPerfect (X := ringedSpace Y) ((derivedPullback (hom g)).obj E) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback (hom g) E hE
  have e : (derivedPullback (hom g)).obj E ≅
      (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E :=
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback g).app E).symm
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e h1

/-- **Restriction along an open immersion of schemes pulls back the support.** If every
cohomology sheaf of `E` has vanishing stalks outside `T`, the same holds for `E|_Y` and the
preimage of `T`.

This is `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrict` for an arbitrary open
immersion rather than the inclusion of an open subscheme; the comparison of the stalks is
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. -/
theorem cohomologySupportedOn_derivedRestrictFunctor (T : Set X)
    (E : DerivedCategory X.Modules) (hE : CohomologySupportedOn X.ringCatSheaf T E) :
    CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E) := by
  intro i y hy
  refine IsZero.of_iso (hE i (g.base y) hy) ?_
  refine ((Scheme.Modules.toPresheaf Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (Scheme.Modules.restrictFunctor g) i).app E)) ≪≫ ?_
  exact (Scheme.Modules.restrictStalkNatIso g y).app
    ((DerivedCategory.homologyFunctor X.Modules i).obj E)

/-- **Restriction along an open immersion of schemes preserves quasi-coherent cohomology.** The
cohomology sheaves of `E|_Y` are the restrictions of those of `E`, and the restriction of a
quasi-coherent module along an open immersion is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`). -/
theorem isDQCoh_derivedRestrict (E : DerivedCategory X.Modules)
    (hE : IsDQCoh (R := X.ringCatSheaf) E) :
    IsDQCoh (R := Y.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E) := by
  intro i
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor g) i).app E).symm ?_
  exact @Scheme.Modules.isQuasicoherent_restrictFunctor _ _ g _ _ (hE i)

end Restriction

/-- **The support condition is stable under shifting.** The cohomology sheaves of `E⟦m⟧` are
those of `E`, reindexed by `m`. -/
theorem cohomologySupportedOn_shift {X : Scheme.{u}} (T : Set X)
    (E : DerivedCategory X.Modules) (hE : CohomologySupportedOn X.ringCatSheaf T E) (m : ℤ) :
    CohomologySupportedOn X.ringCatSheaf T (E⟦m⟧) := by
  intro i x hx
  refine IsZero.of_iso (hE (m + i) x hx) ?_
  exact (Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso m i (m + i) rfl).app E)

/-! ### The two spellings of derived restriction to an open subscheme -/

/-- **Derived restriction to an open subscheme, in the extension-by-zero spelling, is the
functor induced on derived categories by Mathlib's restriction along `U.ι`.** The two underived
functors are both the derived pullback along the inclusion of the open subspace, by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso` and by
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`. Composing those two is
what pays for the crossing between the two spellings of the category of `𝒪_U`-modules: the
first of them carries the `ExtensionByZeroModules.resRing` spelling in its type ascription, so
no instance of the other spelling is ever asked for. -/
def derivedJStarIsoDerivedRestrict (X : Scheme.{u}) (U : X.Opens) :
    Stacks.ExtensionByZero.derivedRestriction X.ringCatSheaf U ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
      (ringedSpace X) U).symm ≪≫
    (Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι).symm

/-! ### Transporting a vanishing statement along a linear functor with a retraction -/

/-- **A morphism killed by a scalar after an `A`-linear functor with an `A`-linear retraction is
killed by that scalar.** If `R : C ⥤ D` and `S : D ⥤ C` are `A`-linear and `R ⋙ S` is
isomorphic to the identity, then `a • R.map α = 0` forces `a • α = 0`. -/
theorem smul_eq_zero_of_smul_map_eq_zero {A : Type*} [Semiring A] {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] [Linear A C] [Linear A D] (R : C ⥤ D)
    (S : D ⥤ C) [R.Linear A] [S.Linear A] [S.Additive] (Φ : R ⋙ S ≅ 𝟭 C) {E F : C}
    (α : E ⟶ F) (a : A) (h : a • R.map α = 0) : a • α = 0 := by
  have hRS : a • (R ⋙ S).map α = 0 := by
    change a • S.map (R.map α) = 0
    rw [← S.map_smul, h, S.map_zero]
  have hnat : (R ⋙ S).map α ≫ Φ.hom.app F = Φ.hom.app E ≫ α := Φ.hom.naturality α
  have h0 : Φ.hom.app E ≫ (a • α) = Φ.hom.app E ≫ 0 := by
    rw [Linear.comp_smul, ← hnat, ← Linear.smul_comp, hRS, Limits.zero_comp, Limits.comp_zero]
  exact (cancel_epi (Φ.hom.app E)).mp h0

end Stacks.DerivedQCoh

end
