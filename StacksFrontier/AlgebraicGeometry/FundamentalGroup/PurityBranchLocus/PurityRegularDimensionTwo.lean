module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularDimensionTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.NormalEquivalence

/-!
# Purity for a regular local ring of dimension two

Let `A` be a regular local ring of Krull dimension two, let `X = Spec A` and let
`U = X ∖ {𝔪}` be the punctured spectrum. Then every finite étale cover of `U` is the restriction
of a finite étale cover of `X`: purity holds for `A`. This is the first clause of
[Stacks, Tag 0BMA] in the case `d = 2`.

The proof is the source's. A regular local ring is normal ([Stacks, Tag 0567]), so clauses (1)
and (2) of the tag are equivalent by [Stacks, Tag 0BM9]; concretely, given `V ⟶ U` finite étale,
its ring of global sections `B = Γ(V, 𝒪_V)` is a finite normal `A`-algebra, torsion-free over
`A`, whose spectrum is étale over `U`
(`AlgebraicGeometry.NormalPurity.globalSections_finite_normal_torsionFree_etale`), the second
clause of the tag makes `A → B` étale
(`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`), and the extension
criterion of [Stacks, Tag 0BM9] turns that into an extension of `V` over `X`.

## Main results

* `Stacks.PurityDimensionTwo.hasPurity_of_ringKrullDim_eq_two` —
  **[Stacks, Tag 0BMA], clause (1), for `d = 2`.**

## What is *not* proved here

Clause (1) in dimension `d ≥ 3`, and hence also clause (2) in dimension `d ≥ 3`. The source
obtains both from the case `d = 2` by induction on `d`, the inductive step being
[Stacks, Tag 0BLM] (purity lifts from a hypersurface section) applied to `A ⧸ fA` for
`f ∈ 𝔪 ∖ 𝔪²`. That step is available in this library as
`AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth`, whose
own attribute records that it takes the unrestricted [Stacks, Tag 0BLS] as a named hypothesis. The
induction itself is run, with [Stacks, Tag 0BLS] as its one hypothesis, in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/PurityRegularLocal.lean`; the
tag 0BMA registrations stay on the unconditional dimension-two results here and in
`RegularDimensionTwo`.

## Implementation notes

**Purity** is `AlgebraicGeometry.HasPurity`, the predicate of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/ExtendFiniteEtale.lean`: the
restriction functor `FÉt_{Spec A} ⟶ FÉt_U` is essentially surjective. That is verbatim the
source's definition of "purity holds for `(A, 𝔪)`", given in the introduction to the section
"Purity in local case, I" ([Stacks, Tag 0BM7]).

**The dimension hypothesis** is `ringKrullDim A = 2`, matching the base case of the source's
induction. Dimension at least two is essential: purity is false for a discrete valuation ring,
whose punctured spectrum is the spectrum of its fraction field, and for a field, whose punctured
spectrum is empty.

**Torsion-freeness.** The second clause, as this library states it, carries the extra hypothesis
`Module.IsTorsionFree A B` — see the module docstring of `RegularDimensionTwo`, where the
counterexample to the literal statement of the source's clause (2) is recorded. Clause (1) needs
no such repair, and none is made: torsion-freeness of `Γ(V, 𝒪_V)` over `A` is *proved*, for every
finite étale `V ⟶ U`, by
`AlgebraicGeometry.NormalPurity.globalSections_finite_normal_torsionFree_etale`.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 0BM9](https://stacks.math.columbia.edu/tag/0BM9)
* [Stacks Project, Tag 0BM7](https://stacks.math.columbia.edu/tag/0BM7)
* [Stacks Project, Tag 0567](https://stacks.math.columbia.edu/tag/0567)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PurityDimensionTwo

/-! ### Recognising the essential image of restriction -/

/-- A finite étale cover of an open `U ⊆ X` which is the base change of a finite étale
`Y ⟶ X` lies in the essential image of the restriction functor `FÉt_X ⟶ FÉt_U`. -/
public lemma mem_essImage_finiteEtaleBaseChange_of_isPullback {X : Scheme.{u}} (U : X.Opens)
    (E : FiniteEtaleOver U.toScheme) {Y : Scheme.{u}} (p : Y ⟶ X) (g : E.left ⟶ Y)
    (hfin : IsFinite p) (het : Etale p) (h : IsPullback E.hom g U.ι p) :
    (finiteEtaleBaseChange U.ι).essImage E := by
  refine ⟨MorphismProperty.Over.mk ⊤ p ⟨hfin, het⟩, ⟨?_⟩⟩
  refine MorphismProperty.Over.isoMk h.flip.isoPullback.symm ?_
  show h.flip.isoPullback.inv ≫ E.hom = pullback.snd p U.ι
  exact h.flip.isoPullback_inv_snd

/-- Conversely, an object of the essential image of `FÉt_X ⟶ FÉt_U` is the base change of a
finite étale cover of `X`. -/
public lemma exists_isPullback_of_mem_essImage {X : Scheme.{u}} (U : X.Opens)
    (E : FiniteEtaleOver U.toScheme) (h : (finiteEtaleBaseChange U.ι).essImage E) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (g : E.left ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback E.hom g U.ι p := by
  obtain ⟨y, ⟨i⟩⟩ := h
  let eOver : Over.mk E.hom ≅ Over.mk (pullback.fst U.ι y.hom) :=
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤
        U.toScheme).mapIso i.symm ≪≫
      Over.isoMk (pullbackSymmetry y.hom U.ι) (by
        show (pullbackSymmetry y.hom U.ι).hom ≫ pullback.fst U.ι y.hom =
          pullback.snd y.hom U.ι
        exact pullbackSymmetry_hom_comp_fst y.hom U.ι)
  exact ⟨y.left, y.hom, eOver.hom.left ≫ pullback.snd U.ι y.hom, y.prop.1, y.prop.2,
    IsPullback.of_over_iso eOver⟩

/-! ### Purity in dimension two -/

/-- **Purity of the branch locus, [Stacks, Tag 0BMA] clause (1), in dimension two.** Let `A` be
a regular local ring of Krull dimension `2`. Then every finite étale cover of the punctured
spectrum of `A` is the restriction of a finite étale cover of `Spec A`.

This is the source's argument. A regular local ring is a normal ring, so [Stacks, Tag 0BM9]
applies to it: the global sections `B = Γ(V, 𝒪_V)` of a finite étale `V ⟶ U` are a finite normal
`A`-algebra, torsion-free over `A`, whose spectrum is étale over `U`, and `V` extends over
`Spec A` exactly when `B` is finite étale over `A`. The latter is clause (2) of the tag in
dimension two, `etale_of_isNormalRing_of_ringKrullDim_eq_two`, whose hypotheses — normality of
`B`, finiteness and torsion-freeness over `A`, and étaleness over the punctured spectrum — are
precisely what [Stacks, Tag 0BM9] supplies. -/
@[stacks 0BMA "clause (1) of the tag, and in the case `d = 2`: `A` regular local with \
`ringKrullDim A = 2`, and the conclusion is `AlgebraicGeometry.HasPurity A`, i.e. essential \
surjectivity of `FÉt_{Spec A} ⟶ FÉt_U`, which is the source's definition of purity for \
`(A, 𝔪)`. This is the base case of the source's induction on `d`; the inductive step is tag \
0BLM.", sga "2 X 3.4" "partial"]
public theorem hasPurity_of_ringKrullDim_eq_two (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdimA : ringKrullDim A = 2) :
    HasPurity A := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  have hA : IsNormalRing A := IsNormalRing.of_isIntegrallyClosed A
  have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A := hdimA.ge
  refine Functor.EssSurj.mk fun E => ?_
  let : Algebra A Γ(E.left, ⊤) := NormalPurity.globalSectionsAlgebra A E
  obtain ⟨hfinB, hnormB, htfB, hetB⟩ :=
    NormalPurity.globalSections_finite_normal_torsionFree_etale A hA hdim E
  have : IsFinite E.hom := E.prop.1
  have : Etale E.hom := E.prop.2
  have := hfinB
  have := htfB
  -- Étaleness over the punctured spectrum, in the restriction form clause (2) consumes.
  have hres : Etale (Spec.map (CommRingCat.ofHom (algebraMap A Γ(E.left, ⊤))) ∣_
      Stacks.puncturedSpectrum A) := by
    have hiso : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      (pullbackRestrictIsoRestrict
        (Spec.map (CommRingCat.ofHom (algebraMap A Γ(E.left, ⊤))))
        (Stacks.puncturedSpectrum A)).hom _).mp ?_
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact hetB
  have hetale : Algebra.Etale A Γ(E.left, ⊤) :=
    etale_of_isNormalRing_of_ringKrullDim_eq_two A Γ(E.left, ⊤) hnormB hdimA hres
  obtain ⟨Y, p, g, hfinp, hetp, hpb⟩ :=
    (NormalPurity.exists_finiteEtale_extension_iff_globalSections_finiteEtale A hA hdim
      E.left E.hom).mpr ⟨hfinB, hetale⟩
  exact mem_essImage_finiteEtaleBaseChange_of_isPullback _ E p g hfinp hetp hpb

end Stacks.PurityDimensionTwo

end
