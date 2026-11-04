module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.Topology.Noetherian.IrreducibleComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The envelope built from the irreducible components

Let `X` be a locally Noetherian scheme whose irreducible components are quasi-compact. The proof
of [Stacks, Tag 0GUE], which the proof of condition (3) of [Stacks, Tag 0F9F] refers to, builds
an envelope of `X` as follows. The irreducible components, with their reduced induced closed
subscheme structures `Xᵢ`, are integral, quasi-compact and locally Noetherian, hence Noetherian;
[Stacks, Tag 0GTU] gives for each of them a proper, completely decomposed `X'ᵢ ⟶ Xᵢ` whose
source carries an ample family of invertible modules, and the Noetherian case of
[Stacks, Tag 0GMM] gives `X'ᵢ` the resolution property. The morphism `∐ X'ᵢ ⟶ X` is then an
envelope: it is completely decomposed because every point of `X` lies on a component and both
stages are completely decomposed above it, and it is proper because the family of its summand
ranges is the family of the irreducible components, which is locally finite on a locally
Noetherian space.

## Main results

* `Stacks.Chow.locallyFinite_irreducibleComponents` — the irreducible components of a locally
  Noetherian scheme form a locally finite family of subsets.
* `Stacks.Chow.compactSpace_reducedComponent` — a quasi-compact irreducible component, with its
  reduced induced closed subscheme structure, is a quasi-compact scheme.
* `Stacks.Chow.isNoetherian_reducedComponent` — and a Noetherian one.
* `Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents` — **the envelope of
  the proof of [Stacks, Tag 0GUE]**: a locally Noetherian scheme whose irreducible components
  are quasi-compact is the target of an envelope whose source is a coproduct of Noetherian
  schemes with the resolution property and affine diagonal.

## Implementation notes

The index type is the subtype `irreducibleComponents X` of `Set X`, which lives in the same
universe as the scheme, so the coproduct of the chosen family is a scheme of that universe. The
family is genuinely infinite in general: this is the case of [Stacks, Tag 0F9F] in which `X`
itself is *not* quasi-compact, which is the whole point of its condition (3).

Properness of the assembled morphism is `Stacks.Chow.isProper_sigmaDesc_of_locallyFinite`,
whose local-finiteness hypothesis is about the *ranges* of the summand morphisms. Those ranges
are the irreducible components themselves: `X'ᵢ ⟶ Xᵢ` is surjective, being completely
decomposed, and the range of the closed immersion of `Xᵢ` is the component. So the hypothesis is
`Stacks.Chow.locallyFinite_irreducibleComponents`, which is
`TopologicalSpace.IsLocallyNoetherianSpace.locallyFinite_image_irreducibleComponents` at the
identity of `X`.

What this file does *not* do is reduce condition (3) of [Stacks, Tag 0F9F] to its condition (1).
That step needs the map `Lf^*E₁ ⟶ Lf^*E₂` to be represented by a map of locally bounded
complexes of finite locally free modules on `∐ X'ᵢ`, which [Stacks, Tag 0F8I] supplies on each
summand separately; assembling the summand representations into one on the coproduct asks for a
cochain complex of sheaves of modules on a coproduct of schemes built from complexes on the
summands, and for an isomorphism in `D(𝒪_{∐ X'ᵢ})` to be constructible from isomorphisms on the
summands. The second of those is not available: invertibility in the derived category is local
on an open cover (`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`), but the
*construction* of a morphism of `D(𝒪_{∐ X'ᵢ})` out of summand data is not, there being no
identification of `D(𝒪_{∐ X'ᵢ})` with the product of the `D(𝒪_{X'ᵢ})` in this development.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.BlowupAmpleFamily

universe u

namespace Stacks.Chow

variable (X : Scheme.{u})

/-- **The irreducible components of a locally Noetherian scheme form a locally finite family.**
Around every point there is a Noetherian open neighbourhood, and a Noetherian space has only
finitely many irreducible components, so only finitely many components of `X` meet that
neighbourhood. -/
@[ega "I 7.3.3" "special case", ega "IV 2.3.6" "special case"]
theorem locallyFinite_irreducibleComponents [IsLocallyNoetherian X] :
    LocallyFinite fun Z : irreducibleComponents X ↦ (Z : Set X) := by
  have h := TopologicalSpace.IsLocallyNoetherianSpace.locallyFinite_image_irreducibleComponents
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) (f := id) Topology.IsClosedEmbedding.id
  simpa using h

/-- A quasi-compact irreducible component of `X`, with its reduced induced closed subscheme
structure, is a quasi-compact scheme: its closed immersion into `X` is an embedding with the
component as range. -/
theorem compactSpace_reducedComponent (Z : irreducibleComponents X)
    (hZ : IsCompact (Z : Set X)) : CompactSpace (X.reducedComponent Z) := by
  rw [← isCompact_univ_iff]
  refine (X.reducedComponentι Z).isClosedEmbedding.isEmbedding.isCompact_iff.2 ?_
  rw [Set.image_univ]
  exact (X.range_reducedComponentι Z).symm ▸ hZ

/-- A quasi-compact irreducible component of a locally Noetherian scheme, with its reduced
induced closed subscheme structure, is a Noetherian scheme: it is locally Noetherian because its
closed immersion into `X` is locally of finite type. -/
@[ega "II 6.5.1" "partial"]
theorem isNoetherian_reducedComponent [IsLocallyNoetherian X] (Z : irreducibleComponents X)
    (hZ : IsCompact (Z : Set X)) : IsNoetherian (X.reducedComponent Z) := by
  have : IsLocallyNoetherian (X.reducedComponent Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (X.reducedComponentι Z)
  have := compactSpace_reducedComponent X Z hZ
  exact ⟨⟩

/-- **The envelope of the proof of [Stacks, Tag 0GUE].** Let `X` be a locally Noetherian scheme
whose irreducible components are quasi-compact. Then there is a family `W` of Noetherian schemes
with the resolution property and affine diagonal and a family of morphisms `W i ⟶ X` whose
induced morphism `∐ W ⟶ X` is an envelope.

Each irreducible component carries its reduced induced closed subscheme structure `Xᵢ`, which is
Noetherian by `Stacks.Chow.isNoetherian_reducedComponent`; [Stacks, Tag 0GTU] gives a proper,
completely decomposed `X'ᵢ ⟶ Xᵢ` with an ample family of invertible modules on `X'ᵢ`, which is
Noetherian as the source of a proper morphism onto a Noetherian scheme, hence has the resolution
property by the Noetherian case of [Stacks, Tag 0GMM]
(`Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian`) and affine diagonal by
the Noetherian case of [Stacks, Tag 0F8C]. The composite `X'ᵢ ⟶ Xᵢ ⟶ X` is proper, and its
range is the component, so the family of ranges is locally finite and the morphism out of the
coproduct is proper. It is completely decomposed because every point of `X` lies on some
component, lifts to `Xᵢ` with an unchanged residue field, the immersion being surjective on
stalks (`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`), and lifts
further to `X'ᵢ` with an unchanged residue field. -/
theorem exists_isEnvelope_sigma_of_isCompact_irreducibleComponents [IsLocallyNoetherian X]
    (hqc : ∀ Z ∈ irreducibleComponents X, IsCompact Z) :
    ∃ (I : Type u) (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      IsEnvelope (Sigma.desc g) ∧ ∀ i, IsNoetherian (W i) ∧ HasResolutionProperty (W i) ∧
        IsAffineHom (pullback.diagonal (terminal.from (W i))) := by
  classical
  have hnoeth : ∀ Z : irreducibleComponents X, IsNoetherian (X.reducedComponent Z) :=
    fun Z ↦ isNoetherian_reducedComponent X Z (hqc Z.1 Z.2)
  have key : ∀ Z : irreducibleComponents X, ∃ (T : Scheme.{u}) (h : T ⟶ X.reducedComponent Z),
      FinitePresentation h ∧ IsProper h ∧ IsCompletelyDecomposed h ∧
        ∃ (J : Type u) (N : J → T.Modules), T.IsAmpleFamily N := by
    intro Z
    have := hnoeth Z
    exact exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_isNoetherian _
  choose W g _hfp hproper hcd hamp using key
  choose _J _N hN using hamp
  have hsurj : ∀ Z : irreducibleComponents X, Function.Surjective (g Z) :=
    fun Z w ↦ (hcd Z w).imp fun _ h ↦ h.1
  have hp : ∀ Z : irreducibleComponents X, IsProper (g Z ≫ X.reducedComponentι Z) := by
    intro Z
    have := hproper Z
    infer_instance
  refine ⟨irreducibleComponents X, W, fun Z ↦ g Z ≫ X.reducedComponentι Z, ⟨?_, ?_⟩, fun Z ↦ ?_⟩
  · have hrange : ∀ Z : irreducibleComponents X,
        Set.range (g Z ≫ X.reducedComponentι Z) = (Z : Set X) := by
      intro Z
      rw [← X.range_reducedComponentι Z]
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨v, rfl⟩
        exact ⟨g Z v, rfl⟩
      · rintro y ⟨w, rfl⟩
        obtain ⟨v, hv⟩ := hsurj Z w
        exact ⟨v, by rw [← hv]; rfl⟩
    exact isProper_sigmaDesc_of_locallyFinite W (fun Z ↦ g Z ≫ X.reducedComponentι Z)
      (by simpa only [hrange] using locallyFinite_irreducibleComponents X)
  · refine (isCompletelyDecomposedFamily_iff _).2 fun x ↦ ?_
    obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (isIrreducible_singleton (x := x))
    obtain ⟨w, hw⟩ : x ∈ Set.range (X.reducedComponentι ⟨Z, hZ⟩) := by
      rw [X.range_reducedComponentι ⟨Z, hZ⟩]
      exact hxZ rfl
    obtain ⟨v, hv, hviso⟩ := hcd ⟨Z, hZ⟩ w
    have h₁ : IsIso ((X.reducedComponentι ⟨Z, hZ⟩).residueFieldMap (g ⟨Z, hZ⟩ v)) :=
      Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks _ _
    refine ⟨⟨Z, hZ⟩, v, ?_, ?_⟩
    · show X.reducedComponentι ⟨Z, hZ⟩ (g ⟨Z, hZ⟩ v) = x
      rw [hv, hw]
    · rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' h₁ hviso
  · have := hnoeth Z
    have := hproper Z
    have hWnoeth : IsNoetherian (W Z) := AlgebraicGeometry.isNoetherian_source_of_isProper (g Z)
    have hres : HasResolutionProperty (W Z) :=
      hasResolutionProperty_of_isAmpleFamily_of_isNoetherian (hN Z)
    exact ⟨hWnoeth, hres,
      AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian (W Z)⟩

end Stacks.Chow

end
