module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisUnitMono

/-!
# The bounds of [Stacks, Tag 07QA] on the crystalline cohomology groups themselves

[Stacks, Tag 07QA] bounds the kernel and the cokernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

by `q^{i + 1}`.  That map is `...SmallSite.crisCohomologyMap` of
`SmallSite/AlphaPCoverTriangle.lean`.  The two bounds of
`SmallSite/HypercohomologyBound07QA.lean` are statements about

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`,

the map on *Zariski hypercohomology*, and carrying a bound across to `crisCohomologyMap` needs
the three inputs listed at `crisCohomologyMap`.  All three are available, and this file carries
the two bounds across.  The statements below are about `f^*` on
the crystalline cohomology groups of `SmallSite/Cohomology.lean` and about nothing else.

## How the transport runs

The two Leray factorizations

* `...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImage`,
  `RΓ(Cris(X/S), -) ≅ Ru_{X/S, *} ⋙ RΓ(X_Zar, -)`, and
* `...SmallSite.derivedZariskiGlobalSectionsIsoPushforward`,
  `RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`,

are **isomorphisms of functors and unconditional**, and
`...SmallSite.homologyDerivedGlobalSectionsIsoObj` identifies the cohomology of `RΓ(Cris(X/S), -)`
with the graded theory `H^i(Cris(X/S), -)`.  Composing them gives the two vertical isomorphisms

`H^i(Cris(X/S), ℱ) ≅ H^i(X_Zar, Ru_{X/S, *}ℱ)`,
`H^i(Cris(X'/S), ℱ') ≅ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`

of `crisCohomologyIsoZariskiHypercohomology` and
`crisCohomologyIsoZariskiHypercohomologyPushforward`.  That they conjugate `f^*` into the Zariski
comparison map is `crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward`,
whose single input is
`...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence` — the
coherence of the crystalline Leray factorization with the Zariski one across the square of topoi,
which carries nothing, `...SmallSite.crisZariskiSquare` and
`...SmallSite.crisZariskiLerayCoherence` both being theorems.  Kernels and cokernels are invariant
under conjugation by isomorphisms, so the two bounds transport verbatim, with the source's
exponent `q^{i + 1}` unchanged.

## The annihilation input, and where the tag is

No tag attribute is placed here.  Each bound below takes `...SmallSite.Annihilation07Q9` — the
conclusion of [Stacks, Tag 07Q9] that the third term of the triangle has cohomology sheaves
annihilated by `q` — as an input, so that it applies to any morphism and any annihilator `q`.
[Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, which states the bounds for the module-level map
`...SmallSite.crisModuleCohomologyMap` of a crystal in quasi-coherent modules under the source's
hypotheses, and discharges the annihilation by [Stacks, Tag 07Q9],
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` — whose content is [Stacks, Proposition
60.21.3, Tag 07LG], `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.

The cokernel half additionally takes the monomorphism of `ℋ^0` of the comparison map, in either of
the two forms `SmallSite/Bound07QAHypotheses.lean` and `SmallSite/CrisUnitMono.lean` reduce it to.
That is not an erratum in the source and not a weakening: `ℋ^{-1}(E)` is the kernel of
`ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(f_*Ru_{X'/S, *}ℱ')`, the filtration of `H^i(X_Zar, E)` runs over the
degrees `-1, 0, …, i` and so would give `q^{i + 2}`, and the source's `q^{i + 1}` holds exactly
when that kernel vanishes — which for an iterated `α_p`-cover is the splitness of `D ⟶ D'` of
[Stacks, Tag 07N1], proved in this library for a single `p`-th root extension, both uncompleted
(`Crystalline.PthRootExtension.primeRetraction_comp`,
`Crystalline.PthRootExtension.universallyInjective_toPrimeRing`) and over the `p`-adic
completions (`Crystalline.PthRootExtension.injective_completedToPrimeRing`).  The passage from
that to the monomorphism of `ℋ^0` on the site, for a crystal in quasi-coherent modules, is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover` of
`SmallSite/ModuleUnitMonoRings07QA.lean`.

So what this file measures is that the distance from [Stacks, Tag 07QA] *as a statement about its
own map* `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` to the Zariski-hypercohomology bounds is
nothing: the identification of the two maps costs nothing, and the remaining inputs are
[Stacks, Tag 07Q9] and, for the cokernel half, the monomorphism just named.

## Main definitions

* `crisCohomologyIsoZariskiHypercohomology` — `H^i(Cris(X/S), ℱ) ≅ H^i(X_Zar, Ru_{X/S, *}ℱ)`,
  unconditional.
* `crisCohomologyIsoZariskiHypercohomologyPushforward` —
  `H^i(Cris(X'/S), ℱ') ≅ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`, unconditional.

## Main results

* `crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward` — **`f^*` on
  crystalline cohomology is the Zariski comparison map conjugated by those two
  isomorphisms**, with nothing carried.
* `pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA` — **the kernel half of
  [Stacks, Tag 07QA] on `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`**, carrying only the
  annihilation of [Stacks, Tag 07Q9].
* `exists_crisCohomologyMap_eq_pow_smul_07QA` — **the cokernel half on the same map**, carrying
  the annihilation and the monomorphism of `ℋ^0` of the comparison.
* `exists_crisCohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit` — the cokernel half with the
  monomorphism in the exact form of `...SmallSite.CrisUnitMono`, namely
  `Mono (u_{X/S, *}(ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ))`.

## References

* [Stacks Project, Lemma 60.25.5, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.22.1, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### `H^i(Cris(X/S), ℱ)` is `H^i(X_Zar, Ru_{X/S, *}ℱ)` -/

section Source

variable (T : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **`H^i(Cris(X/S), ℱ) ≅ H^i(X_Zar, Ru_{X/S, *}ℱ)`.**  Unconditional: the graded crystalline
cohomology is the cohomology of `RΓ(Cris(X/S), ℱ)` by
`...SmallSite.homologyDerivedGlobalSectionsIsoObj`, and `RΓ(Cris(X/S), -)` factors through
`Ru_{X/S, *}` by the Leray isomorphism
`...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImage`, whose two inputs —
`u_{X/S, *}` preserving injective abelian sheaves and
`Γ(X_Zar, u_{X/S, *} -) ≅ Γ(Cris(X/S), -)` — are both theorems.

This is the left-hand vertical of the square that carries the bounds of [Stacks, Tag 07QA] from
Zariski hypercohomology to the crystalline cohomology groups. -/
def crisCohomologyIsoZariskiHypercohomology
    (F : Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor T i).obj F ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor T).obj ((derivedZariskiDirectImage T).obj F)) :=
  (homologyDerivedGlobalSectionsIsoObj T F i).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      ((derivedGlobalSectionsIsoDerivedZariskiDirectImage T).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) 0).obj F))

/-- `H^i(Cris(X/S), ℱ) ≃+ H^i(X_Zar, Ru_{X/S, *}ℱ)`, the additive-equivalence reading of
`crisCohomologyIsoZariskiHypercohomology`. -/
def crisCohomologyZariskiHypercohomologyAddEquiv
    (F : Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor T i).obj F ≃+
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor T).obj ((derivedZariskiDirectImage T).obj F)) :=
  (crisCohomologyIsoZariskiHypercohomology T F i).addCommGroupIsoToAddEquiv

/-- The additive equivalence `crisCohomologyZariskiHypercohomologyAddEquiv` acts as the forward
map of `crisCohomologyIsoZariskiHypercohomology`. -/
@[simp]
theorem crisCohomologyZariskiHypercohomologyAddEquiv_apply
    (F : Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) (i : ℕ)
    (x : (cohomologyFunctor T i).obj F) :
    crisCohomologyZariskiHypercohomologyAddEquiv T F i x =
      (crisCohomologyIsoZariskiHypercohomology T F i).hom x :=
  rfl

end Source

/-! ### The right-hand vertical, and the conjugation of `f^*` -/

section Transport

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- **`H^i(Cris(X'/S), ℱ') ≅ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`.**  Unconditional:
`crisCohomologyIsoZariskiHypercohomology` on `X'` followed by [Stacks, Tag 015M] for `f_{Zar}`,
`...SmallSite.derivedZariskiGlobalSectionsIsoPushforward`, whose two inputs —
`f_{Zar, *}` preserving injective abelian sheaves and `Γ(X, f_{Zar, *}G) = Γ(X', G)` — are both
theorems.

This is the right-hand vertical of the square that carries the bounds of [Stacks, Tag 07QA] to the
crystalline cohomology groups. -/
def crisCohomologyIsoZariskiHypercohomologyPushforward
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F) ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor S').obj
          ((derivedZariskiPushforwardFunctor S S' fX).obj
            ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))) :=
  crisCohomologyIsoZariskiHypercohomology S (crisPullback S S' fS fX hf F) i ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      ((derivedZariskiGlobalSectionsIsoPushforward S S' fX).app
        ((derivedZariskiDirectImageFunctor S).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
              (crisPullback S S' fS fX hf F))))

/-- `H^i(Cris(X'/S), ℱ') ≃+ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`, the additive-equivalence
reading of `crisCohomologyIsoZariskiHypercohomologyPushforward`. -/
def crisCohomologyZariskiHypercohomologyPushforwardAddEquiv
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F) ≃+
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor S').obj
          ((derivedZariskiPushforwardFunctor S S' fX).obj
            ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))) :=
  (crisCohomologyIsoZariskiHypercohomologyPushforward S S' fS fX hf F i).addCommGroupIsoToAddEquiv

/-- The additive equivalence `crisCohomologyZariskiHypercohomologyPushforwardAddEquiv` acts as
the forward map of `crisCohomologyIsoZariskiHypercohomologyPushforward`. -/
@[simp]
theorem crisCohomologyZariskiHypercohomologyPushforwardAddEquiv_apply
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ)
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i y =
      (crisCohomologyIsoZariskiHypercohomologyPushforward S S' fS fX hf F i).hom y :=
  rfl

/-- **`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` is the map on Zariski hypercohomology
conjugated by the two Leray isomorphisms**, with nothing carried.  The square

`H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`
`      ≅                     ≅          `
`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`

commutes, the bottom edge being `...SmallSite.zariskiHypercohomologyComparisonMap`.

The only input is
`...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence`, the
coherence of the crystalline Leray factorization with the Zariski one across the square of topoi;
it carries nothing, `...SmallSite.crisZariskiSquare` and `...SmallSite.crisZariskiLerayCoherence`
being theorems of this library.  This is what makes the two bounds of [Stacks, Tag 07QA] below
statements about `f^*` itself. -/
theorem crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    crisCohomologyMap S S' fS fX hf F i ≫
        (crisCohomologyIsoZariskiHypercohomologyPushforward S S' fS fX hf F i).hom =
      (crisCohomologyIsoZariskiHypercohomology S' F i).hom ≫
        zariskiHypercohomologyComparisonMap S S' fS fX hf F i := by
  rw [crisCohomologyMap, crisCohomologyIsoZariskiHypercohomologyPushforward,
    crisCohomologyIsoZariskiHypercohomology, crisCohomologyIsoZariskiHypercohomology,
    zariskiHypercohomologyComparisonMap]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence
    S S' fS fX hf F).symm

/-- The element-level form of
`crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward`. -/
theorem zariskiHypercohomologyComparisonMap_crisCohomologyZariskiHypercohomologyAddEquiv
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ)
    (x : (cohomologyFunctor S' i).obj F) :
    zariskiHypercohomologyComparisonMap S S' fS fX hf F i
        (crisCohomologyZariskiHypercohomologyAddEquiv S' F i x) =
      crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i
        (crisCohomologyMap S S' fS fX hf F i x) := by
  have h := crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward
    S S' fS fX hf F i
  have h' : (crisCohomologyMap S S' fS fX hf F i ≫
      (crisCohomologyIsoZariskiHypercohomologyPushforward S S' fS fX hf F i).hom) x =
      ((crisCohomologyIsoZariskiHypercohomology S' F i).hom ≫
        zariskiHypercohomologyComparisonMap S S' fS fX hf F i) x := by rw [h]
  simpa [AddCommGrpCat.comp_apply] using h'.symm

/-! ### The two bounds of [Stacks, Tag 07QA] on `f^*` -/

/-- **The kernel half of [Stacks, Tag 07QA] on the crystalline cohomology groups.**  Given the
conclusion of [Stacks, Tag 07Q9] — that the third term of a distinguished triangle on the
comparison map has cohomology sheaves annihilated by `q` — the kernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

is annihilated by `q^{i + 1}`.  This is
`...SmallSite.pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_07QA` transported along the two
Leray isomorphisms by
`crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward`; the transport carries
nothing, so the bound on `f^*` has exactly the hypotheses the bound on Zariski hypercohomology
has.

`hann` is the conclusion of [Stacks, Tag 07Q9] for the abelian comparison map, taken as an input
so that the bound applies to any annihilator `q`; no tag attribute is placed on this lemma.
[Stacks, Tag 07QA], under the source's hypotheses, is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`. -/
theorem pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (x : (cohomologyFunctor S' i).obj F)
    (hx : crisCohomologyMap S S' fS fX hf F i x = 0) :
    ((q : ℤ) ^ (i + 1)) • x = 0 := by
  apply (crisCohomologyZariskiHypercohomologyAddEquiv S' F i).injective
  rw [map_zsmul, map_zero]
  refine pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_07QA S S' fS fX hf q i F hann
    (crisCohomologyZariskiHypercohomologyAddEquiv S' F i x) ?_
  rw [zariskiHypercohomologyComparisonMap_crisCohomologyZariskiHypercohomologyAddEquiv, hx,
    map_zero]

/-- **The cokernel half of [Stacks, Tag 07QA] on the crystalline cohomology groups.**  Given
the conclusion of [Stacks, Tag 07Q9] and that `ℋ^0` of the comparison map of [Stacks, Tag 07Q9] is
a monomorphism, `q^{i + 1}` times any class in `H^i(Cris(X'/S), ℱ')` is in the image of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`.

This is `...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA` transported along the two Leray
isomorphisms; the transport carries nothing.

Two inputs remain, exactly those of the Zariski-hypercohomology form: `hann`, the conclusion of
[Stacks, Tag 07Q9], and `hmono`, which is what makes the exponent `q^{i + 1}` rather than
`q^{i + 2}` — the vanishing of `ℋ^{-1}` of the third term — whose geometric proof for an iterated
`α_p`-cover is the splitness of `D ⟶ D'` of [Stacks, Tag 07N1]; for a crystal in quasi-coherent
modules it is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.  No tag
attribute is placed on this lemma; [Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (hmono : Mono ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
        (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))))
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y = crisCohomologyMap S S' fS fX hf F i x := by
  obtain ⟨z, hz⟩ := exists_hypercohomologyMap_eq_pow_smul_07QA S S' fS fX hf q i F hann hmono
    (crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i y)
  refine ⟨(crisCohomologyZariskiHypercohomologyAddEquiv S' F i).symm z, ?_⟩
  apply (crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i).injective
  rwa [map_zsmul,
    ← zariskiHypercohomologyComparisonMap_crisCohomologyZariskiHypercohomologyAddEquiv,
    AddEquiv.apply_symm_apply]

/-- **The cokernel half of [Stacks, Tag 07QA] on the crystalline cohomology groups, with the
monomorphism hypothesis in its exact form.**  Given the conclusion of [Stacks, Tag 07Q9] and
that `u_{X/S, *}` of the crystalline unit `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a monomorphism,
`q^{i + 1}` times any class in `H^i(Cris(X'/S), ℱ')` is in the image of
`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`.

By `...SmallSite.mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` the hypothesis
is not merely sufficient but *equivalent* to the one `exists_crisCohomologyMap_eq_pow_smul_07QA`
consumes, so nothing is lost in this form.  No tag attribute is placed on this lemma: its two
inputs are [Stacks, Tag 07Q9] (`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`) and the
injectivity of the unit, both proved for a crystal in quasi-coherent modules, and the tag itself is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (hmono : Mono ((zariskiDirectImage S').map (crisUnit S S' fS fX hf F)))
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y = crisCohomologyMap S S' fS fX hf F i x :=
  exists_crisCohomologyMap_eq_pow_smul_07QA S S' fS fX hf q i F hann
    ((mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit S S' fS fX hf
      (crisZariskiSquare S S' fS fX hf) F).2 hmono) y

end Transport

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
