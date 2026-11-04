module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoof
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedHomotopy
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ClopenGlueing
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The envelope of the proof of Stacks 0GUE (3)

Stacks 0GUE (3) says that the Chern classes of a perfect object on a scheme whose irreducible
components are quasi-compact are defined. Its proof passes to an envelope `f : Y ⟶ X` which is a
disjoint union of Noetherian schemes with the resolution property; this file builds it.

## Main results

* `Stacks.Chow.isNoetherian_subscheme_vanishingIdeal` — the reduced induced closed subscheme on a
  quasi-compact closed subset of a locally Noetherian scheme is Noetherian.
* `Stacks.Chow.exists_isEnvelope_isClopenDecomposition_isNoetherian` — the envelope of the proof
  of (3): a disjoint union of Noetherian schemes with the resolution property.

## Implementation notes

The envelope of the source's proof of (3): let `X_i` be the irreducible components of `X` with
their reduced induced structures; each is quasi-compact by hypothesis and locally Noetherian, hence
Noetherian. Tag 0GTU gives a proper completely decomposed `X'_i ⟶ X_i` with `X'_i` carrying an
ample family of invertible modules, so `X'_i` has the resolution property (Tag 0GMM) and is
Noetherian. The morphism `f : Y = ∐ X'_i ⟶ X` is an envelope: it is proper because the components
form a locally finite family (Tag 0BE1), and completely decomposed because each point of `X` lies
on a component and a closed immersion does not change residue fields.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Quasi-compact irreducible components -/

/-- The reduced induced closed subscheme on a quasi-compact closed subset of a locally Noetherian
scheme is Noetherian: it is locally Noetherian, being of finite type over the scheme, and its
underlying space is the closed subset. -/
theorem isNoetherian_subscheme_vanishingIdeal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z : Closeds X) (hZ : IsCompact (Z : Set X)) :
    IsNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let ι := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ι
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    rwa [← isCompact_univ_iff, ι.isClosedEmbedding.isInducing.isCompact_iff, Set.image_univ,
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
  exact ⟨⟩

/-- **The envelope of the proof of Stacks 0GUE (3).** A locally Noetherian scheme whose
irreducible components are quasi-compact has an envelope `f : Y ⟶ X` together with a
decomposition of `Y` into open and closed subschemes each of which is Noetherian and has the
resolution property. `Y` is the disjoint union, over the irreducible components `Z` of `X` with
their reduced induced structures, of the schemes with an ample family of invertible modules
which Tag 0GTU provides over `Z`. -/
theorem exists_isEnvelope_isClopenDecomposition_isNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : ∀ Z ∈ irreducibleComponents X, IsCompact Z) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (I : Type u) (U : I → Y.Opens),
      IsClopenDecomposition U ∧
        ∀ k, IsNoetherian (U k : Scheme.{u}) ∧ HasResolutionProperty (U k : Scheme.{u}) := by
  classical
  let I := irreducibleComponents X
  let Zc : I → Closeds X := fun Z => ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩
  let Zs : I → Scheme.{u} := fun Z => (Scheme.IdealSheafData.vanishingIdeal (Zc Z)).subscheme
  let ι : ∀ Z, Zs Z ⟶ X := fun Z => (Scheme.IdealSheafData.vanishingIdeal (Zc Z)).subschemeι
  have hZs : ∀ Z, IsNoetherian (Zs Z) := fun Z =>
    isNoetherian_subscheme_vanishingIdeal (Zc Z) (hX Z.1 Z.2)
  choose T g hgfp hgp hgcd J N hN using fun Z =>
    have := hZs Z
    Stacks.BlowupAmpleFamily.exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily
      (Zs Z)
  have hTn : ∀ Z, IsNoetherian (T Z) := fun Z => by
    have := hZs Z
    have := hgp Z
    exact isNoetherian_source_of_isProper (g Z)
  let f : (∐ T) ⟶ X := Sigma.desc fun Z => g Z ≫ ι Z
  have hrange : ∀ Z, Set.range (g Z ≫ ι Z) = (Z : Set X) := fun Z => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (hgcd Z).surjective.range_eq, Set.image_univ,
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    rfl
  have hfp : IsProper f := by
    have : ∀ Z, IsProper (g Z ≫ ι Z) := fun Z => by
      have := hgp Z
      infer_instance
    refine Stacks.Chow.isProper_sigmaDesc_of_locallyFinite T _ ?_
    convert locallyFinite_irreducibleComponents_image (𝟙 X) using 1
    funext Z
    rw [hrange Z]
    ext y
    simp
  have hfcd : IsCompletelyDecomposed f := by
    rw [← IsCompletelyDecomposedFamily, isCompletelyDecomposedFamily_iff]
    intro x
    let Z : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    obtain ⟨z, hz⟩ : x ∈ Set.range (ι Z) := by
      rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact mem_irreducibleComponent
    obtain ⟨t, htz, ht⟩ := hgcd Z z
    refine ⟨Z, t, by rw [Scheme.Hom.comp_apply, htz, hz], ?_⟩
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (residueFieldMap_isIso_of_isClosedImmersion (ι Z) (g Z t)) ht
  refine ⟨∐ T, f, ⟨hfp, hfcd⟩, I, fun Z => (Sigma.ι T Z).opensRange,
    isClopenDecomposition_opensRange_sigmaι T, fun Z => ?_⟩
  let e := (Sigma.ι T Z).isoOpensRange
  have := hTn Z
  have := (hN Z).hasResolutionProperty
  have : IsLocallyNoetherian ((Sigma.ι T Z).opensRange : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian e.inv
  have : CompactSpace ((Sigma.ι T Z).opensRange : Scheme.{u}) :=
    (Scheme.homeoOfIso e).compactSpace
  exact ⟨⟨⟩, hasResolutionProperty_of_isAffineHom e.inv⟩

end Stacks.Chow

end
