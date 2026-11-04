module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The normalization criterion for a normal crossings divisor

A closed subscheme `D` of a locally Noetherian scheme `X` is a normal crossings divisor exactly
when it is reduced, its normalization `ν : D^ν ⟶ D` is unramified, and for every `n ≥ 1` the
scheme `Z_n`, obtained from the `n`-fold fibre power of `ν` by deleting the fat diagonal, is
regular and maps to `X` by a local complete intersection morphism whose conormal sheaf is
locally free of rank `n`. This file sets up the second condition and proves the reducedness
clause of it for a normal crossings divisor.

## Main definitions

* `AlgebraicGeometry.fibrePower` and `AlgebraicGeometry.fibrePowerProj` are the `n`-fold fibre
  power of a morphism over its target and its structure morphism.
* `AlgebraicGeometry.fibrePowerLeg` and `AlgebraicGeometry.fibrePowerPair` are the coordinates
  of a fibre power and the morphism to the fibre square reading off two of them.
* `AlgebraicGeometry.fibrePowerDistinctLocus` is the complement of the fat diagonal.
* `Stacks.Divisors.divisorNormalization` is the normalization of the subscheme cut out by a
  divisor, and `Stacks.Divisors.normalizationDistinct` is the scheme `Z_n`.
* `Stacks.Divisors.IsNormalizationCrossingsDivisor` is condition (2) of Tag 0CBR.

## Main results

* `AlgebraicGeometry.isClopen_fibrePowerDistinctLocus`: the fat diagonal of an unramified
  separated morphism is open and closed in each fibre power, so `Z_n` is an open and closed
  subscheme of it.
* `Stacks.Divisors.unramified_normalizationDistinctToAmbient` and
  `Stacks.Divisors.formallyUnramified_normalizationDistinctToAmbient`: once the normalization is
  unramified, `Z_n ⟶ X` is unramified, hence formally unramified, so its conormal sheaf is
  defined.
* `Stacks.Divisors.isReduced_of_isNormalCrossingsDivisor`: a normal crossings divisor is
  reduced, which is the first clause of condition (2).
* `Stacks.Divisors.isNormal_reducedComponent_of_isStrictNormalCrossingsDivisor`: an irreducible
  component of a strict normal crossings divisor, with its reduced induced closed subscheme
  structure, is normal.
* `Stacks.Divisors.unramified_divisorNormalization_of_isStrictNormalCrossingsDivisor`: the
  normalization of a strict normal crossings divisor is unramified, which is the second clause
  of condition (2) in the strict case.

## Implementation notes

The `n`-fold fibre power is built by recursion through `CategoryTheory.Over`, so that the scheme
and its structure morphism are produced together; `fibrePower f (n + 1)` is the pullback of
`fibrePowerProj f n` along `f` by definition, and `fibrePower f 0` is the target. The fat
diagonal is described pointwise, as the set of points some pair of whose coordinates lands in
the range of the diagonal of the morphism: inequality of the underlying points of two
coordinates would not describe the scheme-theoretic fat diagonal over a residue field that is
not separably closed.

Deleting the fat diagonal needs it to be closed, which holds for a separated morphism; the
normalization is integral, hence separated, so `Z_n` is available for any divisor on a locally
Noetherian scheme. That it is also open, so that `Z_n` is a closed subscheme as well, uses
unramifiedness of the morphism and is therefore recorded as a separate statement.

Condition (2) is an iterated conjunction rather than a structure, with the unramifiedness of the
normalization bound by an existential so that the conormal clause can refer to it; by proof
irrelevance the bound witness does not affect the conormal sheaf.

The equivalence itself is complete, in both directions and in general, at the hypotheses of the
source — `Stacks.Divisors.isNormalCrossingsDivisor_iff_reduced_unramified_normalization` in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationEquivalence`,
which carries Tag 0CBR. Its two halves are
`Stacks.Divisors.isNormalizationCrossingsDivisor_of_isNormalCrossingsDivisor`
(in `…NormalCrossings.NormalizationEquivalenceForward`) and
`Stacks.Divisors.isNormalCrossingsDivisor_of_isNormalizationCrossingsDivisor`.

The unramifiedness clause is proved in general by
`Stacks.Divisors.unramified_divisorNormalization_of_isNormalCrossingsDivisor` (in
`…NormalCrossings.UnramifiedNormalization`); the strict case below is the input it descends from.
In the strict case the normalization is identified with the disjoint union of the normalizations
of the irreducible components of `D` by Tag 0CDV; each component is regular by Tag 0BIA, hence
normal, so its own normalization morphism is an isomorphism by Tag 0H7D, and the resulting
morphism to `D` is a disjoint union of closed immersions. The opening steps of the converse
implication, through the étale-local splitting of the normalization supplied by Tag 04HJ, are in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationFiniteness`.

Tag 0BIA produces the regularity of a component as a statement about the closed subscheme of the
*ambient* scheme cut out by the vanishing ideal sheaf of that component, while Tag 0CDV produces
the normalization of the component as a closed subscheme of `D` itself. The two carry the reduced
induced structure on the same closed subset, so they are identified by lifting each closed
immersion through the other and cancelling the resulting monomorphisms; that is the content of
`Stacks.Divisors.exists_iso_reducedComponent_componentIdealSubscheme`.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 0BSF](https://stacks.math.columbia.edu/tag/0BSF)
* [Stacks Project, Tag 0BIA](https://stacks.math.columbia.edu/tag/0BIA)
* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {Y S : Scheme.{u}}

/-- The `n`-fold fibre power of `f : Y ⟶ S` over `S`, together with its structure morphism. -/
@[reducible] public noncomputable def fibrePowerOver (f : Y ⟶ S) : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | n + 1 => Over.mk (pullback.fst (fibrePowerOver f n).hom f ≫ (fibrePowerOver f n).hom)

/-- The `n`-fold fibre power `Y ×_S ⋯ ×_S Y` of `f : Y ⟶ S`, with `n` factors. -/
public noncomputable abbrev fibrePower (f : Y ⟶ S) (n : ℕ) : Scheme.{u} :=
  (fibrePowerOver f n).left

/-- The structure morphism of the `n`-fold fibre power of `f : Y ⟶ S`. -/
public noncomputable abbrev fibrePowerProj (f : Y ⟶ S) (n : ℕ) : fibrePower f n ⟶ S :=
  (fibrePowerOver f n).hom

/-- One more factor in a fibre power is one more pullback along `f`. -/
public theorem fibrePower_succ (f : Y ⟶ S) (n : ℕ) :
    fibrePower f (n + 1) = pullback (fibrePowerProj f n) f := rfl

/-- The structure morphism of a fibre power, after one more factor. -/
public theorem fibrePowerProj_succ (f : Y ⟶ S) (n : ℕ) :
    fibrePowerProj f (n + 1) =
      pullback.fst (fibrePowerProj f n) f ≫ fibrePowerProj f n := rfl

/-- The `i`-th coordinate of the `n`-fold fibre power of `f : Y ⟶ S`. -/
public noncomputable def fibrePowerLeg (f : Y ⟶ S) :
    (n : ℕ) → Fin n → (fibrePower f n ⟶ Y)
  | 0 => fun i => i.elim0
  | n + 1 => Fin.lastCases (pullback.snd (fibrePowerProj f n) f)
      (fun i => pullback.fst (fibrePowerProj f n) f ≫ fibrePowerLeg f n i)

/-- The last coordinate of a fibre power is the second projection of the last pullback. -/
public theorem fibrePowerLeg_last (f : Y ⟶ S) (n : ℕ) :
    fibrePowerLeg f (n + 1) (Fin.last n) = pullback.snd (fibrePowerProj f n) f := by
  simp only [fibrePowerLeg, Fin.lastCases_last]

/-- The earlier coordinates of a fibre power factor through the first projection. -/
public theorem fibrePowerLeg_castSucc (f : Y ⟶ S) (n : ℕ) (i : Fin n) :
    fibrePowerLeg f (n + 1) i.castSucc =
      pullback.fst (fibrePowerProj f n) f ≫ fibrePowerLeg f n i := by
  simp only [fibrePowerLeg, Fin.lastCases_castSucc]

/-- Every coordinate of a fibre power lies over the structure morphism. -/
public theorem fibrePowerLeg_comp (f : Y ⟶ S) :
    ∀ (n : ℕ) (i : Fin n), fibrePowerLeg f n i ≫ f = fibrePowerProj f n
  | 0, i => i.elim0
  | n + 1, i => by
      induction i using Fin.lastCases with
      | last =>
          rw [fibrePowerLeg_last, fibrePowerProj_succ]
          exact pullback.condition.symm
      | cast i =>
          rw [fibrePowerProj_succ, fibrePowerLeg_castSucc, Category.assoc,
            fibrePowerLeg_comp f n i]

/-- The morphism to the fibre square of `f` reading off the `i`-th and `j`-th coordinates of the
`n`-fold fibre power. -/
public noncomputable def fibrePowerPair (f : Y ⟶ S) (n : ℕ) (i j : Fin n) :
    fibrePower f n ⟶ pullback f f :=
  pullback.lift (fibrePowerLeg f n i) (fibrePowerLeg f n j)
    (by rw [fibrePowerLeg_comp, fibrePowerLeg_comp])

/-- The complement of the fat diagonal in the `n`-fold fibre power of `f`: the points no two of
whose coordinates agree, in the scheme-theoretic sense that no pair of them lands in the range
of the diagonal of `f`. -/
public def fibrePowerDistinctLocus (f : Y ⟶ S) (n : ℕ) : Set (fibrePower f n) :=
  {z | ∀ i j : Fin n, i ≠ j →
    (fibrePowerPair f n i j).base z ∉ Set.range (pullback.diagonal f).base}

/-- The complement of the fat diagonal, as the intersection over ordered pairs of distinct
indices of the preimages of the complement of the range of the diagonal. -/
public theorem fibrePowerDistinctLocus_eq_iInter (f : Y ⟶ S) (n : ℕ) :
    fibrePowerDistinctLocus f n =
      ⋂ p : {p : Fin n × Fin n // p.1 ≠ p.2},
        (fibrePowerPair f n p.1.1 p.1.2).base ⁻¹'
          (Set.range (pullback.diagonal f).base)ᶜ := by
  ext z
  simp only [fibrePowerDistinctLocus, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
    Set.mem_compl_iff, Subtype.forall, Prod.forall, ne_eq]

/-- Every fibre power of an unramified morphism is unramified over the target, being an iterated
base change of it. -/
public theorem unramified_fibrePowerProj (f : Y ⟶ S) [Unramified f] (n : ℕ) :
    Unramified (fibrePowerProj f n) := by
  induction n with
  | zero => exact (inferInstance : Unramified (𝟙 S))
  | succ n ih =>
      rw [fibrePowerProj_succ]
      exact MorphismProperty.comp_mem (@Unramified.{u}) _ _
        (unramified_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback (fibrePowerProj f n) f).flip inferInstance) ih

/-- For a separated morphism the fat diagonal is closed, so its complement is open. -/
public theorem isOpen_fibrePowerDistinctLocus (f : Y ⟶ S) [IsSeparated f] (n : ℕ) :
    IsOpen (fibrePowerDistinctLocus f n) := by
  rw [fibrePowerDistinctLocus_eq_iInter]
  exact isOpen_iInter_of_finite fun p => IsOpen.preimage
    (fibrePowerPair f n p.1.1 p.1.2).continuous
    (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl

/-- For an unramified morphism the fat diagonal is open, so its complement is closed. -/
public theorem isClosed_fibrePowerDistinctLocus (f : Y ⟶ S) [Unramified f] (n : ℕ) :
    IsClosed (fibrePowerDistinctLocus f n) := by
  rw [fibrePowerDistinctLocus_eq_iInter]
  exact isClosed_iInter fun p => IsClosed.preimage (fibrePowerPair f n p.1.1 p.1.2).continuous
    (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The complement of the fat diagonal in a fibre power of an unramified separated morphism is
open and closed. -/
public theorem isClopen_fibrePowerDistinctLocus (f : Y ⟶ S) [Unramified f] [IsSeparated f]
    (n : ℕ) : IsClopen (fibrePowerDistinctLocus f n) :=
  ⟨isClosed_fibrePowerDistinctLocus f n, isOpen_fibrePowerDistinctLocus f n⟩

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)

/-- The normalization of the closed subscheme cut out by a divisor on a locally Noetherian
scheme. -/
public noncomputable abbrev divisorNormalizationScheme : Scheme.{u} :=
  letI : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  Scheme.normalizationScheme D.subscheme
    (finite_irreducibleComponents_of_isCompact D.subscheme)

/-- The normalization morphism `ν : D^ν ⟶ D` of the closed subscheme cut out by a divisor on a
locally Noetherian scheme. -/
public noncomputable abbrev divisorNormalization :
    divisorNormalizationScheme D ⟶ D.subscheme :=
  letI : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  Scheme.normalization D.subscheme (finite_irreducibleComponents_of_isCompact D.subscheme)

/-- The complement of the fat diagonal in the `n`-fold fibre power of the normalization of `D`,
as an open of that fibre power. -/
public noncomputable abbrev normalizationDistinctOpens (n : ℕ) :
    (fibrePower (divisorNormalization D) n).Opens :=
  ⟨fibrePowerDistinctLocus (divisorNormalization D) n,
    isOpen_fibrePowerDistinctLocus (divisorNormalization D) n⟩

/-- The scheme `Z_n = D^ν ×_D ⋯ ×_D D^ν` with its fat diagonal deleted. -/
public noncomputable abbrev normalizationDistinct (n : ℕ) : Scheme.{u} :=
  (normalizationDistinctOpens D n).toScheme

/-- The canonical morphism `Z_n ⟶ X`. -/
public noncomputable abbrev normalizationDistinctToAmbient (n : ℕ) :
    normalizationDistinct D n ⟶ X :=
  (normalizationDistinctOpens D n).ι ≫
    fibrePowerProj (divisorNormalization D) n ≫ D.subschemeι

/-- `Z_n` is open and closed in the fibre power of the normalization, once the latter is
unramified. -/
@[stacks 0CBR "first paragraph of the proof: `Z_n` is an open and closed subscheme of the fibre
power of the normalization. Neither implication of the equivalence is asserted."]
public theorem isClopen_normalizationDistinctLocus [Unramified (divisorNormalization D)]
    (n : ℕ) : IsClopen (fibrePowerDistinctLocus (divisorNormalization D) n) :=
  isClopen_fibrePowerDistinctLocus (divisorNormalization D) n

/-- Once the normalization of `D` is unramified, `Z_n ⟶ X` is unramified: it is the composition
of an open immersion, an iterated base change of the normalization, and a closed immersion. -/
@[stacks 0CBR "first paragraph of the proof: `Z_n ⟶ X` is unramified. Neither implication of the
equivalence is asserted."]
public theorem unramified_normalizationDistinctToAmbient
    [Unramified (divisorNormalization D)] (n : ℕ) :
    Unramified (normalizationDistinctToAmbient D n) :=
  MorphismProperty.comp_mem (@Unramified.{u}) _ _ inferInstance
    (MorphismProperty.comp_mem (@Unramified.{u}) _ _
      (unramified_fibrePowerProj (divisorNormalization D) n) inferInstance)

/-- Once the normalization of `D` is unramified, `Z_n ⟶ X` is formally unramified, so that it
has a conormal sheaf. -/
@[stacks 0CBR "first paragraph of the proof: `Z_n ⟶ X` is formally unramified, so the conormal
sheaf `𝒞_n` exists. Neither implication of the equivalence is asserted."]
public theorem formallyUnramified_normalizationDistinctToAmbient
    [Unramified (divisorNormalization D)] (n : ℕ) :
    FormallyUnramified (normalizationDistinctToAmbient D n) :=
  ((unramified_iff_locallyOfFiniteType_and_formallyUnramified
    (normalizationDistinctToAmbient D n)).mp
      (unramified_normalizationDistinctToAmbient D n)).2

/-- Condition (2) of Tag 0CBR: the closed subscheme cut out by `D` is reduced, its normalization
is unramified, and every `Z_n` with `n ≥ 1` is regular and maps to the ambient scheme by a local
complete intersection morphism whose conormal sheaf is locally free of rank `n`. -/
@[stacks 0CBR "condition (2). Its equivalence with condition (1),
`Stacks.Divisors.IsNormalCrossingsDivisor`, is not asserted."]
public def IsNormalizationCrossingsDivisor : Prop :=
  IsReduced D.subscheme ∧
    ∃ hν : Unramified (divisorNormalization D), ∀ n : ℕ, 1 ≤ n →
      AlgebraicGeometry.IsRegular (normalizationDistinct D n) ∧
        IsLocalCompleteIntersectionMorphism (normalizationDistinctToAmbient D n) ∧
          (letI : Unramified (divisorNormalization D) := hν
           haveI := formallyUnramified_normalizationDistinctToAmbient D n
           SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
             (Stacks.Thickenings.universalConormalSheaf
               (normalizationDistinctToAmbient D n)) n)

/-- A normal crossings divisor is reduced, which is the first clause of condition (2) of
Tag 0CBR. Étale-locally the divisor has strict normal crossings, hence is reduced by Tag 0BIA,
and reducedness descends along the faithfully flat maps that an étale chart induces on stalks of
the divisor. -/
@[stacks 0CBR "the implication (1) to (2), restricted to its reducedness clause. The remaining
clauses of (2) under hypothesis (1), and the converse implication, are not asserted."]
public theorem isReduced_of_isNormalCrossingsDivisor (h : IsNormalCrossingsDivisor D) :
    IsReduced D.subscheme := by
  have hst : ∀ y : D.subscheme, _root_.IsReduced (D.subscheme.presheaf.stalk y) := by
    intro y
    obtain ⟨U, f, hU, hf, ⟨q, hq⟩, hsnc⟩ := h.2 y
    have := hU
    have := hf
    have : AlgebraicGeometry.IsReduced (D.comap f).subscheme :=
      ((isStrictNormalCrossingsDivisor_iff (D.comap f) hsnc.1).mp hsnc).1
    let g : (D.comap f).subscheme ⟶ D.subscheme :=
      Scheme.IdealSheafData.subschemeMap _ _ f (D.le_map_comap f)
    have hgeq : (D.comapIso f).hom ≫ pullback.snd f D.subschemeι = g :=
      Scheme.IdealSheafData.comapIso_hom_snd D f
    have : Flat g := by
      rw [← hgeq]
      infer_instance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback q y hq
    let y' : (D.comap f).subscheme := (D.comapIso f).inv z
    have hy' : g y' = y := by
      rw [← Scheme.Hom.comp_apply, ← hgeq, Iso.inv_hom_id_assoc]
      exact hz
    have hff : (g.stalkMap y').hom.FaithfullyFlat := by
      algebraize [(g.stalkMap y').hom]
      exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap g y')
        (g.toLRSHom.prop y')
    rw [← hy']
    exact isReduced_of_injective (g.stalkMap y').hom hff.injective
  exact isReduced_of_isReduced_stalk _

/-! ### The normalization of a strict normal crossings divisor -/

section

omit [IsLocallyNoetherian X]

/-- The range of the closed immersion into the ambient scheme of the subscheme cut out by an
irreducible component of a divisor is the image of that component. -/
public theorem range_subschemeι_componentIdeal (C : irreducibleComponents D.subscheme) :
    Set.range (componentIdeal D C).subschemeι = D.subschemeι '' (C : Set D.subscheme) := by
  have h : componentIdeal D C = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (D.subschemeι '' (C : Set D.subscheme)), isClosed_closure⟩ := rfl
  rw [h, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
  exact (D.subschemeι.isClosedEmbedding.isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ C.2)).closure_eq

/-- The closed subscheme of the ambient scheme cut out by an irreducible component of a divisor
is isomorphic over the ambient scheme to that component of the subscheme cut out by the divisor,
taken with its reduced induced closed subscheme structure. -/
public theorem exists_iso_reducedComponent_componentIdealSubscheme
    (C : irreducibleComponents D.subscheme) :
    ∃ e : D.subscheme.reducedComponent C ≅ (componentIdeal D C).subscheme,
      e.hom ≫ (componentIdeal D C).subschemeι =
        D.subscheme.reducedComponentι C ≫ D.subschemeι := by
  have hredI : IsReduced (componentIdeal D C).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hI := range_subschemeι_componentIdeal D C
  have hJ : Set.range (D.subscheme.reducedComponentι C ≫ D.subschemeι) =
      D.subschemeι '' (C : Set D.subscheme) := by
    rw [← D.subscheme.range_reducedComponentι C, ← Set.range_comp]
    rfl
  have hKsupp : ((Scheme.IdealSheafData.vanishingIdeal
      (D.subscheme.componentCloseds C)).support : Set D.subscheme) =
      (C : Set D.subscheme) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact D.subscheme.range_reducedComponentι C
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    (componentIdeal D C) (D.subscheme.reducedComponentι C ≫ D.subschemeι)).2 (by
      rw [hJ, ← hI, Scheme.IdealSheafData.range_subschemeι])
  obtain ⟨p, hp⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    D (componentIdeal D C).subschemeι).2 (by
      rw [hI, ← D.range_subschemeι]
      exact Set.image_subset_range _ _)
  have hprange : Set.range p ⊆ (C : Set D.subscheme) := by
    rintro y ⟨t, rfl⟩
    have ht : D.subschemeι (p t) ∈ D.subschemeι '' (C : Set D.subscheme) := by
      rw [← Scheme.Hom.comp_apply, hp, ← hI]
      exact Set.mem_range_self t
    obtain ⟨w, hw, hwe⟩ := ht
    exact (D.subschemeι.isClosedEmbedding.injective hwe) ▸ hw
  obtain ⟨q, hq⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    (Scheme.IdealSheafData.vanishingIdeal (D.subscheme.componentCloseds C)) p).2 (by
      rwa [hKsupp])
  have hq' : q ≫ D.subscheme.reducedComponentι C = p := hq
  refine ⟨⟨g, q, ?_, ?_⟩, hg⟩
  · rw [← cancel_mono (D.subscheme.reducedComponentι C ≫ D.subschemeι), Category.assoc,
      ← Category.assoc q, hq', hp, hg, Category.id_comp]
  · rw [← cancel_mono (componentIdeal D C).subschemeι, Category.assoc, hg,
      ← Category.assoc q, hq', hp, Category.id_comp]

end

/-- An irreducible component of a strict normal crossings divisor, with its reduced induced
closed subscheme structure, is a normal scheme: it is regular by Tag 0BIA, and a regular scheme
is normal. -/
@[stacks 0CBR "an input to the implication (1) to (2) in the strict case: an irreducible \
component of a strict normal crossings divisor, with its reduced induced closed subscheme \
structure, is normal. Neither implication of the equivalence is asserted."]
public theorem isNormal_reducedComponent_of_isStrictNormalCrossingsDivisor
    (h : IsStrictNormalCrossingsDivisor D) (C : irreducibleComponents D.subscheme) :
    IsNormal (D.subscheme.reducedComponent C) := by
  obtain ⟨e, -⟩ := exists_iso_reducedComponent_componentIdealSubscheme D C
  have hreg : AlgebraicGeometry.IsRegular (componentIdeal D C).subscheme := by
    simpa [componentIntersection] using
      (((isStrictNormalCrossingsDivisor_iff D h.1).mp h).2.2 {C} (Finset.singleton_nonempty C)).1
  have : IsNormal (componentIdeal D C).subscheme := isNormal_of_isRegular _ hreg
  exact isNormal_of_iso e

/-- The normalization of a strict normal crossings divisor is unramified, which is the
unramifiedness clause of condition (2) of Tag 0CBR in the strict case. The normalization is the
disjoint union of the normalizations of the irreducible components of the divisor, each component
is normal, so each of those normalization morphisms is an isomorphism, and what remains is a
disjoint union of closed immersions. -/
@[stacks 0CBR "the implication (1) to (2) for a strict normal crossings divisor, restricted to \
the clause that the normalization of the divisor is unramified. The general normal crossings \
case, the remaining clauses of (2), and the converse implication are not asserted."]
public theorem unramified_divisorNormalization_of_isStrictNormalCrossingsDivisor
    (h : IsStrictNormalCrossingsDivisor D) : Unramified (divisorNormalization D) := by
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  have : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Unramified.{u})
  obtain ⟨e, he⟩ := D.subscheme.exists_iso_normalizationScheme_sigma_reducedComponent
    (finite_irreducibleComponents_of_isCompact D.subscheme)
  have hleg : ∀ C : irreducibleComponents D.subscheme,
      Unramified ((D.subscheme.reducedComponent C).normalization
        (D.subscheme.finite_irreducibleComponents_reducedComponent C) ≫
          D.subscheme.reducedComponentι C) := by
    intro C
    have : IsNormal (D.subscheme.reducedComponent C) :=
      isNormal_reducedComponent_of_isStrictNormalCrossingsDivisor D h C
    have : IsIso ((D.subscheme.reducedComponent C).normalization
        (D.subscheme.finite_irreducibleComponents_reducedComponent C)) :=
      ((D.subscheme.reducedComponent C).isIso_normalization_iff_isNormal
        (D.subscheme.finite_irreducibleComponents_reducedComponent C)).2 inferInstance
    exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ inferInstance inferInstance
  show Unramified (Scheme.normalization D.subscheme
    (finite_irreducibleComponents_of_isCompact D.subscheme))
  rw [← Iso.inv_hom_id_assoc e (Scheme.normalization _ _), he]
  exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ inferInstance
    (IsZariskiLocalAtSource.sigmaDesc hleg)

end Stacks.Divisors

end
