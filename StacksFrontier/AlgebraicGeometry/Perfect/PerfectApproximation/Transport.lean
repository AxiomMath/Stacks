module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionPerfectSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme

/-!
# Restriction and transport of the approximation property

Restriction of unbounded derived modules along an open immersion of schemes is exact, so it
commutes with the cohomology sheaves and does not change their stalks at the points it hits.
Consequently it carries an `m`-pseudo-coherent object to an `m`-pseudo-coherent object and a
morphism approximating from `m` to a morphism approximating from `m`. Applied to the two
morphisms of an isomorphism of schemes this transports the approximation property of
[Stacks, Tag 08EN] from one scheme to any scheme isomorphic to it, and in particular carries
[Stacks, Tag 08EQ] from `Spec R` to an arbitrary affine scheme.

## Main results

* `AlgebraicGeometry.PerfectApproximation.isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion`:
  restriction along an open immersion preserves `m`-pseudo-coherence.
* `AlgebraicGeometry.PerfectApproximation.stalkHomologyDerivedRestrictIso`: the stalk of a
  cohomology sheaf of a restriction, at the image of the point.
* `DerivedCategory.approximatesFrom_mapDerivedCategory`: an exact functor carries a morphism
  approximating from `m` to one approximating from `m`.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_iso`: the property
  of [Stacks, Tag 08EN] transports along an isomorphism of schemes.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_isAffine`:
  **[Stacks, Tag 08EQ]** for an arbitrary affine scheme.

## Implementation notes

`AlgebraicGeometry.PerfectApproximation.isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion` is
Stacks 09U7 for the derived pullback, read along
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`; no flatness or
invertibility hypothesis is needed because the pullback statement has none.

The stalk comparison is the one behind
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor`, which states the vanishing in
*every* degree at once. The transport statements need it in a single degree, because the support
hypothesis of [Stacks, Tag 08EN] is restricted to the degrees above a bound, so the comparison
is given a name here.

An isomorphism of schemes is an open immersion in both directions, so both transports are
instances of the open-immersion statements; what the invertibility adds is
`Stacks.DerivedQCoh.derivedRestrictCompIso`, which identifies the composite of the two
restrictions with the identity and so turns the approximating morphism obtained on the other
scheme into one on this one.

## References

* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe w₁ w₂ u

/-! ### Approximation under an exact functor -/

namespace DerivedCategory

/-- **An exact functor carries a morphism approximating from `m` to one approximating from
`m`.** The functor induced on derived categories commutes with the cohomology functors, and
preserves isomorphisms and epimorphisms. -/
theorem approximatesFrom_mapDerivedCategory {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {D : Type*} [Category* D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {P E : DerivedCategory C} (α : P ⟶ E) (m : ℤ)
    (h : ApproximatesFrom α m) : ApproximatesFrom (F.mapDerivedCategory.map α) m := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := h.1 i hi
    exact (NatIso.isIso_map_iff
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i) α).mpr
      (Functor.map_isIso F _)
  · have := h.2
    exact (Stacks.PseudoCoherence.DerivedCharacterization.epi_map_iff_of_natIso
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F m) α).mpr
      (preserves_epi_of_preservesColimit F _)

/-- **Approximation from `m` is unchanged by composing with an isomorphism.** -/
theorem approximatesFrom_comp_of_isIso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {P E E' : DerivedCategory C} (α : P ⟶ E) (f : E ⟶ E')
    [IsIso f] (m : ℤ) (h : ApproximatesFrom α m) : ApproximatesFrom (α ≫ f) m := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := h.1 i hi
    rw [Functor.map_comp]
    infer_instance
  · have := h.2
    rw [Functor.map_comp]
    exact epi_comp _ _

end DerivedCategory

/-! ### Restriction along an open immersion -/

namespace AlgebraicGeometry.PerfectApproximation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Restriction along an open immersion of schemes preserves `m`-pseudo-coherence.** This is
Stacks 09U7 for the derived pullback, read through the identification of the restriction with
the derived pullback. -/
@[sga "6 I 2.16.1" "a), special case"]
theorem isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ)
    (h : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) :
    RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) ((derivedRestrict g).obj E) m :=
  (Scheme.Hom.isPseudoCoherentFrom_derivedPullback g E m h).ofIso
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback g).app E).symm

/-- **The stalks of one cohomology sheaf of a restriction.** At a point `y` of `Y`, the stalk of
the `i`-th cohomology sheaf of the restriction of `E` along an open immersion `g : Y ⟶ X` is the
stalk at `g y` of the `i`-th cohomology sheaf of `E`.

Restriction is exact, so it commutes with the cohomology sheaves, and it does not change stalks
at the points it hits, by `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. -/
def stalkHomologyDerivedRestrictIso {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (E : DerivedCategory.{u + 1} X.Modules) (i : ℤ) (y : Y) :
    TopCat.Presheaf.stalk (X := Y)
        (((DerivedCategory.homologyFunctor Y.Modules i).obj
          ((derivedRestrict g).obj E)).val.presheaf) y ≅
      TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) (g.base y) :=
  ((Scheme.Modules.toPresheaf Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (Scheme.Modules.restrictFunctor g) i).app E)) ≪≫
    (Scheme.Modules.restrictStalkNatIso g y).app
      ((DerivedCategory.homologyFunctor X.Modules i).obj E)

/-- A sheaf of modules which is a zero object has vanishing stalks. -/
theorem isZero_stalk_of_isZero {Y : Scheme.{u}} {M : Y.Modules} (hM : IsZero M) (y : Y) :
    IsZero (TopCat.Presheaf.stalk (X := Y) M.val.presheaf y) :=
  (Scheme.Modules.toPresheaf Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map_isZero hM

/-! ### Transport along an isomorphism of schemes -/

/-- **The condition of [Stacks, Tag 08EM] on a triple only depends on the isomorphism class of
the derived object.** -/
theorem approximationHolds_of_iso (Y : Scheme.{u}) (T : Set Y)
    {E E' : DerivedCategory.{u + 1} Y.Modules} (e : E ≅ E') (m : ℤ)
    (h : ApproximationHolds Y T E m) : ApproximationHolds Y T E' m := by
  obtain ⟨P, hP, hPT, α, hα⟩ := h
  exact ⟨P, hP, hPT, α ≫ e.hom, DerivedCategory.approximatesFrom_comp_of_isIso α e.hom m hα⟩

end AlgebraicGeometry.PerfectApproximation

end
