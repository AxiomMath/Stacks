module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumAlongRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackCompatibility
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.SourceFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DisjointUnion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# Effectivity of descent data along a refinement by an fpqc covering

Let `𝒱 = {V j ⟶ S}` be a family of morphisms of schemes with fixed target and let
`𝒰 = {U i ⟶ S}` refine it. If `𝒰` is an fpqc covering of `S` — nothing is asked of `𝒱` —
then pulling descent data back along the refinement is fully faithful, and consequently a
descent datum relative to `𝒱` whose pullback to `𝒰` is effective is itself effective.

Over an affine base this reduces effectivity along an arbitrary covering, for any of the five
covering types fpqc, fppf, étale, smooth and syntomic, to effectivity along a finite covering by
affine schemes.

## Main results

* `AlgebraicGeometry.DescentData.pullbackFunctor_fullyFaithful_of_fpqcRefiningFamily`: pullback
  of descent data along a refinement by an fpqc covering is fully faithful.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_refinement_of_fpqcRefiningFamily`:
  effectivity of descent data descends along a refinement by an fpqc covering.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_finiteAffineFlat`: over an affine base,
  effectivity along an fpqc covering follows from effectivity along the finite fpqc coverings by
  affine schemes, for a property of morphisms stable under base change.
* `AlgebraicGeometry.mem_fpqcPrecoverage_of_mem_coveringPrecoverage`: a covering
  family for the fpqc, fppf, étale, smooth or syntomic precoverage is an fpqc covering.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_finiteAffineFlat_of_mem`: the affine-base
  reduction for a covering of any of those five types.

## Implementation notes

The hypothesis on the refinement is weaker than asking both families to be fpqc coverings, and
it is also weaker than the fibrewise hypothesis of
`AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqcRefinement`, which asks that for each
member of `𝒱` the members of `𝒰` above it already cover it.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 040I](https://stacks.math.columbia.edu/tag/040I)
* [Stacks Project, Tag 040K](https://stacks.math.columbia.edu/tag/040K)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- A precoverage by morphisms which are flat and locally of finite presentation is contained in
the fpqc precoverage. -/
lemma precoverage_le_fpqcPrecoverage {Q : MorphismProperty Scheme.{u}}
    (hQ : Q ≤ (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) :
    Scheme.precoverage Q ≤ Scheme.fpqcPrecoverage :=
  le_trans (Scheme.precoverage_mono hQ) Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- **Each of the five covering types of Stacks 02W3 consists of fpqc coverings.** A covering
family for the fpqc, fppf, étale, smooth or syntomic precoverage is an fpqc covering: the last
four consist of flat morphisms locally of finite presentation, which are in particular open, so
no quasi-compactness has to be checked. -/
lemma mem_fpqcPrecoverage_of_mem_coveringPrecoverage (K : Precoverage Scheme.{u})
    (hK : K = Scheme.fpqcPrecoverage ∨ K = Scheme.fppfPrecoverage ∨
      K = Scheme.etalePrecoverage ∨ K = Scheme.precoverage (@Smooth.{u}) ∨
      K = Scheme.precoverage (@Syntomic.{u}))
    {T : Scheme.{u}} {R : Presieve T} (hR : R ∈ K T) : R ∈ Scheme.fpqcPrecoverage T := by
  obtain rfl | rfl | rfl | rfl | rfl := hK
  · exact hR
  · exact Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hR
  · exact precoverage_le_fpqcPrecoverage
      (fun _ _ f (_ : Etale f) ↦ ⟨inferInstance, inferInstance⟩) _ hR
  · exact precoverage_le_fpqcPrecoverage
      (fun _ _ f (_ : Smooth f) ↦ ⟨inferInstance, inferInstance⟩) _ hR
  · exact precoverage_le_fpqcPrecoverage
      (fun _ _ f hf ↦ ⟨AlgebraicGeometry.flat hf, AlgebraicGeometry.locallyOfFinitePresentation hf⟩)
      _ hR

namespace DescentData

open MorphismOfSchemeFamilies

variable {S : Scheme.{u}} {U V : PreZeroHypercover.{u} S}

/-- The morphism between the disjoint unions induced by a refinement lies over the base. -/
lemma coproductHom_comp_sigmaDesc (α : U.HomOver V (𝟙 S)) :
    (ofRefinement α).coproductHom ≫ Sigma.desc V.f = Sigma.desc U.f := by
  simpa using (ofRefinement α).coproductHom_comp

/-- **Descent data pull back fully faithfully along a refinement by an fpqc covering.** Let the
family `𝒰 = {U i ⟶ S}` refine the family `𝒱 = {V j ⟶ S}` and let `𝒰` be an fpqc covering of
`S`. Then the functor pulling descent data relative to `𝒱` back to descent data relative to `𝒰`
is fully faithful. No hypothesis is placed on `𝒱`; in particular the members of `𝒰` above a
fixed member of `𝒱` are not required to cover it. -/
theorem pullbackFunctor_fullyFaithful_of_fpqcRefiningFamily (α : U.HomOver V (𝟙 S))
    (hU : Presieve.ofArrows U.X U.f ∈ Scheme.fpqcPrecoverage S) :
    Nonempty (MorphismOfSchemeFamilies.pullbackFunctor
      (ofRefinement α)).functor.FullyFaithful := by
  have hsingle : Presieve.singleton (Sigma.desc U.f) ∈ Scheme.fpqcPrecoverage S :=
    (ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem U.X U.f).mp hU
  obtain ⟨hG⟩ := pullbackFunctor_fullyFaithful_of_source_fpqc (Sigma.desc U.f)
    (Sigma.desc V.f) (ofRefinement α).coproductHom (coproductHom_comp_sigmaDesc α) hsingle
  have hcomp : ((familyCoproductEquivalence V.f).equivalence.functor ⋙
      (pullbackFunctor (Sigma.desc V.f) (Sigma.desc U.f) (𝟙 S)
        (ofRefinement α).coproductHom
        (ofRefinement α).coproductHom_comp).functor).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful _).comp hG
  exact ⟨Functor.FullyFaithful.ofCompFaithful
    (hcomp.ofIso (pullbackCompatibility (ofRefinement α)).iso)⟩

/-- **Effectivity descends along a refinement by an fpqc covering.** Let the family
`𝒰 = {U i ⟶ S}` refine the family `𝒱 = {V j ⟶ S}` and let `𝒰` be an fpqc covering of `S`. A
descent datum relative to `𝒱` whose pullback along the refinement is effective is itself
effective. -/
theorem isFamilyEffective_of_refinement_of_fpqcRefiningFamily (α : U.HomOver V (𝟙 S))
    (hU : Presieve.ofArrows U.X U.f ∈ Scheme.fpqcPrecoverage S) {D : DescentData V.f}
    (h : ((MorphismOfSchemeFamilies.pullbackFunctor
      (ofRefinement α)).functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective :=
  have ⟨hff⟩ := pullbackFunctor_fullyFaithful_of_fpqcRefiningFamily α hU
  isFamilyEffective_of_pullback_of_refinement α hff h

/-- **Over an affine base, effectivity along an fpqc covering reduces to effectivity along a
finite covering by affine schemes.** Let `S` be affine, let `𝒰` be an fpqc covering of `S`, and
let `P` be a property of morphisms of schemes stable under base change. If every descent datum
whose components have `P`, relative to a finite fpqc covering of `S` by affine schemes, is
effective, then so is every descent datum relative to `𝒰` whose components have `P`. -/
theorem isFamilyEffective_of_finiteAffineFlat {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [IsAffine S]
    (h𝒰 : Presieve.ofArrows V.X V.f ∈ Scheme.fpqcPrecoverage S)
    (H : ∀ 𝒱 : PreZeroHypercover.{u} S, Finite 𝒱.I₀ → (∀ k, IsAffine (𝒱.X k)) →
      (∀ k, Flat (𝒱.f k)) → Presieve.ofArrows 𝒱.X 𝒱.f ∈ Scheme.fpqcPrecoverage S →
      ∀ E : DescentData 𝒱.f, (∀ k, P (E.obj k).hom) → E.IsFamilyEffective)
    (D : DescentData V.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  obtain ⟨𝒱, φ, hfin, hfpqc, -⟩ :=
    exists_finite_affineCover_flat_hom_of_mem_fpqcPrecoverage V h𝒰
  let W : PreZeroHypercover.{u} S := 𝒱.cover.toPreZeroHypercover
  let α : W.HomOver V (𝟙 S) := (PreZeroHypercover.homOverIdEquivHom W V).symm φ
  refine isFamilyEffective_of_refinement_of_fpqcRefiningFamily α hfpqc
    (H W hfin (fun k ↦ show IsAffine (Spec (𝒱.X k)) from inferInstance)
      (fun k ↦ show Flat (𝒱.f k) from 𝒱.map_prop k) hfpqc _ fun k ↦ ?_)
  rw [(MorphismOfSchemeFamilies.pullbackFunctor (ofRefinement α)).obj_eq D]
  exact MorphismProperty.baseChange_obj (α.h₀ k) (D.obj (α.s₀ k)) (hP _)

/-- **Over an affine base, effectivity along a covering of any of the five types of Stacks 02W3
reduces to effectivity along a finite covering by affine schemes.** Let `S` be affine, let `K` be
the fpqc, fppf, étale, smooth or syntomic precoverage, let `𝒰` be a `K`-covering of `S`, and let
`P` be a property of morphisms stable under base change. If every descent datum whose components
have `P`, relative to a finite fpqc covering of `S` by affine schemes, is effective, then so is
every descent datum relative to `𝒰` whose components have `P`. -/
theorem isFamilyEffective_of_finiteAffineFlat_of_mem {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [IsAffine S] (K : Precoverage Scheme.{u})
    (hK : K = Scheme.fpqcPrecoverage ∨ K = Scheme.fppfPrecoverage ∨
      K = Scheme.etalePrecoverage ∨ K = Scheme.precoverage (@Smooth.{u}) ∨
      K = Scheme.precoverage (@Syntomic.{u}))
    (h𝒰 : Presieve.ofArrows V.X V.f ∈ K S)
    (H : ∀ 𝒱 : PreZeroHypercover.{u} S, Finite 𝒱.I₀ → (∀ k, IsAffine (𝒱.X k)) →
      (∀ k, Flat (𝒱.f k)) → Presieve.ofArrows 𝒱.X 𝒱.f ∈ Scheme.fpqcPrecoverage S →
      ∀ E : DescentData 𝒱.f, (∀ k, P (E.obj k).hom) → E.IsFamilyEffective)
    (D : DescentData V.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_finiteAffineFlat
    (mem_fpqcPrecoverage_of_mem_coveringPrecoverage K hK h𝒰) H D hP

end DescentData

end AlgebraicGeometry

end

end
