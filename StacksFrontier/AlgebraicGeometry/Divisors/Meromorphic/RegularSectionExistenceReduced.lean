module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.GenericStalkRankOne
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotientEpi
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Existence of regular meromorphic sections beyond the integral case

Let `X` be a scheme whose weakly associated points are generic points of irreducible components
and all of whose quasi-compact opens have finitely many irreducible components, and let `L` be an
invertible `𝒪_X`-module. The sheaf of meromorphic sections of a quasi-coherent module is the
product of its generic-point contributions, and the generic-point contribution of a module of
rank one does not depend on the module, so `K_X(L)` and `K_X(𝒪_X)` are isomorphic as
`𝒪_X`-modules. The canonical morphism `𝒪_X ⟶ K_X` is an epimorphism of sheaves of rings, so
restriction of scalars along it is fully faithful and that isomorphism is already an isomorphism
of `K_X`-modules. Finally `K_X(𝒪_X)` is `K_X` itself, so `K_X ≅ K_X(L)`, and the global section
of `K_X(L)` corresponding to the identity is a regular meromorphic section.

Both remaining cases of the source — a reduced scheme whose quasi-compact opens have finitely
many irreducible components, and a locally Noetherian scheme without embedded points — satisfy
those two hypotheses.

## Main results

* `AlgebraicGeometry.meromorphicSectionSheafUnitIso`: `K_X(𝒪_X) = K_X`.
* `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_isReduced` and
  `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_noEmbeddedPoints`: parts (2) and (3)
  of Tag 02OZ.

## Implementation notes

The isomorphism `K_X(𝒪_X) ≅ K_X` is the unitor of a base change, available for any left adjoint
of a restriction of scalars as `Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor`; the
adjunction is the one of Tag 03CZ.

Fullness of restriction of scalars along an epimorphism is Tag 0930, and the epimorphism is
`AlgebraicGeometry.epi_toTotalQuotientRingCatSheaf`, which needs no hypothesis on `X` at all.

## References

* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GenericPointDecomposition (meromorphicSections)

universe u

namespace AlgebraicGeometry

/-- **The sheaf of meromorphic sections of the structure sheaf is the sheaf of meromorphic
functions.** Extension of scalars takes the structure sheaf to the structure sheaf, this being
the unitor of the base change along `𝒪_X ⟶ K_X`. -/
def meromorphicSectionSheafUnitIso (X : Scheme.{u}) :
    meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X.totalQuotientRingCatSheaf :=
  Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor X.toTotalQuotientRingCatSheaf
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
      (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
      (Stacks.Sheaves.Differentials.ringSheaf X.sheaf).property
      (Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).property)

/-- An isomorphism of the sheaf of meromorphic functions with the sheaf of meromorphic sections
of `L` exhibits a regular meromorphic section of `L`: the global section it corresponds to
induces that isomorphism, which is in particular a monomorphism. -/
theorem exists_isRegularMeromorphicSection_of_iso (X : Scheme.{u}) (L : X.Modules)
    (e : SheafOfModules.unit X.totalQuotientRingCatSheaf ≅ meromorphicSectionSheaf X.sheaf L) :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s := by
  refine ⟨(meromorphicSectionSheaf X.sheaf L).unitHomEquiv e.hom, ?_⟩
  change Mono ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm
    ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv e.hom))
  simpa only [Equiv.symm_apply_apply] using (inferInstance : Mono e.hom)

/-- **An isomorphism of sheaves of meromorphic sections over `𝒪_X` is one over `K_X`.** The
canonical morphism `𝒪_X ⟶ K_X` is an epimorphism of sheaves of rings, so restriction of scalars
along it is fully faithful. -/
theorem nonempty_meromorphicSectionSheaf_iso_of_meromorphicSections_iso (X : Scheme.{u})
    (L : X.Modules)
    (e : meromorphicSections X (SheafOfModules.unit X.ringCatSheaf) ≅ meromorphicSections X L) :
    Nonempty (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf) ≅
      meromorphicSectionSheaf X.sheaf L) := by
  have : Epi (C := Sheaf (Opens.grothendieckTopology X) RingCat.{u})
      X.toTotalQuotientRingCatSheaf := epi_toTotalQuotientRingCatSheaf X
  obtain ⟨FF⟩ := Stacks.NoncommChangeOfRings.Silver.restrictScalars_fullyFaithful_of_epi.{u}
    X.toTotalQuotientRingCatSheaf
  exact ⟨FF.preimageIso e⟩

/-- **The sheaves of meromorphic sections of the structure sheaf and of a module of rank one are
isomorphic as `𝒪_X`-modules**, both being the product over the generic points of the irreducible
components of the generic-point contributions, which agree at every generic point. -/
theorem nonempty_meromorphicSections_unit_iso_of_rank_one (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (L : X.Modules) [L.IsQuasicoherent]
    (hL : Scheme.Modules.IsFiniteLocallyFreeOfRank L 1) :
    Nonempty (meromorphicSections X (SheafOfModules.unit X.ringCatSheaf) ≅
      meromorphicSections X L) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  obtain ⟨eU⟩ := nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf hass hfinite
    (SheafOfModules.unit X.ringCatSheaf)
  obtain ⟨eL⟩ := nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf hass hfinite L
  exact ⟨eU ≪≫ (Limits.Pi.mapIso fun η =>
    (nonempty_genericPointStalkModuleOf_iso_unit L hL η).some.symm) ≪≫ eL.symm⟩

/-- An invertible module on a scheme whose weakly associated points are generic and whose
quasi-compact opens have finitely many irreducible components has a regular meromorphic
section. -/
theorem exists_isRegularMeromorphicSection_of_schemeWeaklyAssociatedPoints_subset_genericPoints
    (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s := by
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  obtain ⟨e⟩ := nonempty_meromorphicSections_unit_iso_of_rank_one X hass hfinite L
    (Scheme.Modules.isFiniteLocallyFreeOfRank_one_of_isInvertible L)
  obtain ⟨eK⟩ := nonempty_meromorphicSectionSheaf_iso_of_meromorphicSections_iso X L e
  exact exists_isRegularMeromorphicSection_of_iso X L
    ((meromorphicSectionSheafUnitIso X).symm ≪≫ eK)

/-- **Stacks 02OZ, part (2).** An invertible sheaf of modules on a reduced scheme every
quasi-compact open of which has finitely many irreducible components has a regular meromorphic
section. -/
@[stacks 02OZ "part (2)"]
theorem exists_isRegularMeromorphicSection_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s :=
  exists_isRegularMeromorphicSection_of_schemeWeaklyAssociatedPoints_subset_genericPoints X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hX L

/-- **Stacks 02OZ, part (3).** An invertible sheaf of modules on a locally Noetherian scheme
without embedded points has a regular meromorphic section. -/
@[stacks 02OZ "part (3)"]
theorem exists_isRegularMeromorphicSection_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s :=
  exists_isRegularMeromorphicSection_of_schemeWeaklyAssociatedPoints_subset_genericPoints X
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X) L

end AlgebraicGeometry

end
