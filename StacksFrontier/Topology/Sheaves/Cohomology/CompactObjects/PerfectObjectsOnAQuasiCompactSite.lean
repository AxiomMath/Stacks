module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.IntersectionsFromPairwisePullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectDualReduction
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object of `D(O)` is compact, on a ringed site with a quasi-compact final object

Let `(C, O)` be a ringed site and assume `C` has the three properties of **Stacks 09JC**:

1. `C` has a quasi-compact final object `X₀`;
2. every quasi-compact object of `C` has a cofinal system of coverings which are finite and
   consist of quasi-compact objects;
3. for a finite covering `{U_i → U}` with `U` and the `U_i` quasi-compact the fibre products
   `U_i ×_U U_j` are quasi-compact.

Let `K` be a perfect object of `D(O)`. Then

* **(a)** `K` is a compact object of `D⁺(O)`: if `M = ⨁_{i ∈ I} M_i` is bounded below, then
  `Hom(K, M) = ⨁_{i ∈ I} Hom(K, M_i)`;
* **(b)** if `(C, O)` has finite cohomological dimension, that is if there is a `d` with
  `H^i(X₀, F) = 0` for `i > d` and every `O`-module `F`, then `K` is a compact object of `D(O)`.

Both clauses are asserted by the single theorem
`hom_coproduct_bijective_and_isCompactObject_of_isPerfect_of_isQuasiCompactObject`, which carries
the tag.

## Main results

* `Stacks.Cohomology.QuasiCompactSite.hasFiniteTorDimension_derivedDual_of_isPerfect`: the dual
  of a perfect object has finite Tor dimension, globally, on a site with a quasi-compact final
  object. This is Stacks 08G8 followed by the remark that on a quasi-compact site locally finite
  Tor dimension is finite Tor dimension.
* `Stacks.Cohomology.QuasiCompactSite.preservesCoproducts_rightDerived_evaluation_of_covers`:
  the cohomology functors over `X₀` commute with direct sums, from hypotheses (2) and (3).
* `Stacks.Cohomology.QuasiCompactSite.hom_coproduct_bijective_and_isCompactObject_of_isPerfect`:
  both clauses of Stacks 09JC, with hypotheses (2) and (3) in the form of the covering data of
  Stacks 0G22.
* **Stacks 09JC**, both clauses, under exactly the three hypotheses of the tag:
  `Stacks.Cohomology.QuasiCompactSite.`
  `hom_coproduct_bijective_and_isCompactObject_of_isPerfect_of_isQuasiCompactObject`.

## How the hypotheses of the tag are read

Hypothesis (1) is `X₀` together with `hterm : IsTerminal X₀` and
`hqc : X.J.IsQuasiCompactObject X₀`, quasi-compactness of an object of a site in the sense of
Stacks 090H. Hypothesis (2) says that every covering sieve of a quasi-compact object is refined
by a covering by finitely many quasi-compact objects. Hypothesis (3) says that for such a finite
covering `{U_i → U}` of a quasi-compact `U` each fibre product `U_i ×_U U_j` exists and is
quasi-compact: a Grothendieck topology, unlike a site in the sense of Stacks 00VH, does not
provide those fibre products.

Stacks 0G22 and 0739 are stated with covering data `B`, `Cov`: `B` a collection of objects,
`Cov U` covering families of `U` cofinal among the coverings of members of `B`, each finite with
its target, its members and all its iterated fibre products in `B`
(`Stacks.Cohomology.HasIntersectionsIn`). The theorem
`hom_coproduct_bijective_and_isCompactObject_of_isPerfect` takes that data;
the tagged theorem instantiates it at the quasi-compact objects and their finite coverings by
quasi-compact objects, the iterated fibre products being quasi-compact by
`Stacks.Cohomology.hasIntersectionsIn_of_exists_pullback`, which derives them from (3) by base
change.

## The argument

The source replaces morphisms out of `K` by morphisms out of `j_{X₀!}O_{X₀}`, using
`Hom_{D(O)}(K, N) = H⁰(X₀, K^∨ ⊗^L_O N)` and the commutation of `K^∨ ⊗^L_O -` with direct sums;
that step is
`StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectDualReduction`, and after it (a)
is Stacks 0G22 at `U = X₀` and (b) is Stacks 094D at `U = X₀`. Two inputs remain, and this file
supplies both.

For (a): `K^∨ ⊗^L_O ⨁ M_i` must be bounded below when `⨁ M_i` is, which needs the Tor amplitude
of `K^∨` *globally*. The dual of a perfect object is perfect (Stacks 08JJ), a perfect object
locally has finite Tor dimension (Stacks 08G8), and on a site whose final object is quasi-compact
locally finite Tor dimension is finite Tor dimension, which is
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`.
There finitely many members of the covering already cover, so the local intervals merge into one,
which then descends. This is the step the source passes over in silence.

For (b): the commutation of `F ↦ H^p(X₀, F)` with direct sums, which the source gets from
Stacks 0739 out of hypotheses (2) and (3). That derivation is
`Stacks.Cohomology.preservesCoproducts_rightDerived_evaluation`, in the module proving
Stacks 0G22.

## Implementation notes

`HasDerivedCategory.standard` is installed at priority `10000` rather than as a plain
`local instance`, for the reason recorded in `PerfectDualReduction`: the locally small model
`SheafOfModules.hasDerivedCategory` was once a global instance, which at the default priority won
and made the reduction inapplicable.

The derived tensor product measuring Tor dimension is
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU, on the site and on each of
its slices; nothing in the conclusion mentions it.

The index type of the direct sums lies in the universe of the site, which is where the derived
tensor product commutes with direct sums and where the cohomology of module sheaves does.

## References

* [Stacks Project, Lemma 21.52.7 (Tag 09JC)](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Tag 0G22](https://stacks.math.columbia.edu/tag/0G22)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u c

namespace Stacks.Cohomology.QuasiCompactSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ V : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over V).O).Additive]
  [∀ (V : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over V).O).obj M).Additive]
  [∀ (V : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over V).O) (ComplexShape.up ℤ)]

/-- Sheaves of modules on a ringed site have enough injectives. Reinstated from the public
statement because the module proving Stacks 094D declares it only locally. -/
local instance quasiCompactSiteEnoughInjectives :
    EnoughInjectives (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.Cohomology.enoughInjectives_of_ringedSite.{u, u, u, u} X

attribute [local instance] Stacks.Cohomology.perfectCompactEvaluationAdditive

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The dual of a perfect object has finite Tor dimension** on a ringed site whose final object
is quasi-compact, measured against the derived tensor product of Stacks 06YU.

The dual `K^∨` is perfect by Stacks 08JJ, a perfect object locally has finite Tor dimension by
the implication (1) ⟹ (2) of Stacks 08G8, and quasi-compactness of the final object turns that
into finite Tor dimension: finitely many members of the local covering already cover, so their
intervals merge into one, which descends to the site. -/
@[sga "6 I 7.3" "special case"]
theorem hasFiniteTorDimension_derivedDual_of_isPerfect (X₀ : X.C) (hterm : IsTerminal X₀)
    (hqc : X.J.IsQuasiCompactObject X₀)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (hK : X.IsPerfect K) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (RingedSite.derivedDual X K) :=
  Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension
    X _ (fun V => Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over V)) _
    (SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_isPerfect_anyUniverse
      (X := X) _ _
      (RingedSite.isPerfect_derivedDual X K hK))
    X₀ hterm hqc

omit [EssentiallySmall.{u} X.C]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ V : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over V).O).Additive]
  [∀ (V : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over V).O).obj M).Additive]
  [∀ (V : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over V).O) (ComplexShape.up ℤ)] in
/-- **The cohomology of module sheaves over `X₀` commutes with direct sums**, from hypotheses (2)
and (3) of Stacks 09JC. This is
`Stacks.Cohomology.preservesCoproducts_rightDerived_evaluation_of_hasIntersectionsIn`, the
derivation Stacks 0739 performs inside the module proving Stacks 0G22; the hypothesis Stacks
094D consumes is read off it here. -/
theorem preservesCoproducts_rightDerived_evaluation_of_covers
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F →
      Stacks.Cohomology.HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{c} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hX₀ : B X₀) (p : ℕ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((_root_.SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op X₀)).rightDerived p) :=
  Stacks.Cohomology.preservesCoproducts_rightDerived_evaluation_of_hasIntersectionsIn X B Cov
    hCov hfinite hcofinal X₀ hX₀ p I

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Compactness of a perfect object, for arbitrary covering data.** Let `B` be a collection of
objects of the site and `Cov` a choice of covering families as in Stacks 0G22: every covering of
an object of `B` is refined by one in `Cov`, and every member of `Cov` is finite with its target,
its members and all its iterated fibre products in `B`. Let `X₀ ∈ B` be a quasi-compact final
object and `K` a perfect object of `D(O)`. Then

* **(a)** if `M : I → D(O)` is a family whose coproduct `⨁ M_i` is bounded below, the canonical
  map `⨁ Hom(K, M_i) → Hom(K, ⨁ M_i)` is bijective; and
* **(b)** if `H^p(X₀, F) = 0` for `p > d` and every `O`-module `F`, then `K` is a compact object
  of `D(O)`.

This is the form of Stacks 09JC in which the covering hypotheses are those of Stacks 0G22 and
0739; `hom_coproduct_bijective_and_isCompactObject_of_isPerfect_of_isQuasiCompactObject`, which
carries the tag, is the instance at the quasi-compact objects and their finite coverings by
quasi-compact objects, with hypotheses (2) and (3) of the tag as stated.

Both clauses rest on the source's reduction to `j_{X₀!}O_{X₀}`, which is
`AlgebraicGeometry.RingedSite.derivedDualHomEquivOfIsoStructureSheaf` together with
`AlgebraicGeometry.RingedSite.preservesColimitsOfShape_derivedTensorFlip`. Clause (a) then needs
the global Tor amplitude of `K^∨`, which is
`hasFiniteTorDimension_derivedDual_of_isPerfect`; clause (b) needs the commutation of the
cohomology functors over `X₀` with direct sums, which is
`preservesCoproducts_rightDerived_evaluation_of_covers`. -/
theorem hom_coproduct_bijective_and_isCompactObject_of_isPerfect
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F →
      Stacks.Cohomology.HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{c} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hterm : IsTerminal X₀) (hqc : X.J.IsQuasiCompactObject X₀) (hX₀ : B X₀)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (hK : X.IsPerfect K) :
    (∀ {I : Type u} [DecidableEq I]
        (M : I → DerivedCategory (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) [HasCoproduct M],
        DerivedCategoryB.IsBoundedBelow (∐ M) →
        Function.Bijective
          (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j))) ∧
      ((∃ d : ℤ, ∀ (p : ℕ) (G : _root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), d < (p : ℤ) →
          IsZero (((_root_.SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op X₀)).rightDerived p).obj G)) →
        IsCompactObject.{u} K) := by
  refine ⟨fun {I} _ M _ hplus => ?_, fun hcd => ?_⟩
  · exact
      RingedSite.hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension_anyCoveringUniverse X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) B Cov hCov hfinite hcofinal
      X₀ hX₀ hterm K hK
      (hasFiniteTorDimension_derivedDual_of_isPerfect X X₀ hterm hqc K hK) M hplus
  · exact RingedSite.isCompactObject_of_isPerfect_of_isTerminal X X₀ hterm K hK hcd
      fun p I => preservesCoproducts_rightDerived_evaluation_of_covers X B Cov hCov hfinite
        hcofinal X₀ hX₀ p I

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 09JC.** Let `(C, O)` be a ringed site such that

1. `C` has a quasi-compact final object `X₀`,
2. every quasi-compact object of `C` has a cofinal system of coverings which are finite and
   consist of quasi-compact objects,
3. for a finite covering `{U_i → U}` with `U` and the `U_i` quasi-compact the fibre products
   `U_i ×_U U_j` are quasi-compact.

Let `K` be a perfect object of `D(O)`. Then

* **(a)** `K` is a compact object of `D⁺(O)` in the following sense: if `M : I → D(O)` is a
  family whose coproduct `M = ⨁ M_i` is bounded below, then the canonical map
  `⨁ Hom(K, M_i) → Hom(K, M)` is bijective;
* **(b)** if `(C, O)` has finite cohomological dimension, that is if there is a `d` with
  `H^p(X₀, F) = 0` for `p > d` and every `O`-module `F`, then `K` is a compact object of `D(O)`.

Quasi-compactness is that of Stacks 090H,
`CategoryTheory.GrothendieckTopology.IsQuasiCompactObject`. Hypothesis (1) is `hterm` and
`hqc`. Hypothesis (2) is `hcofinal`: every covering sieve of a quasi-compact object is refined by
a covering by finitely many quasi-compact objects. Hypothesis (3) is `hfibre`; since a
Grothendieck topology, unlike a site in the sense of Stacks 00VH, does not provide the fibre
products of a covering, (3) asserts that `U_i ×_U U_j` exists, as a limiting
pullback cone, and is quasi-compact.

The source's proof calls on Stacks 0739 and 0G22 with the quasi-compact objects as `B`; those
need every iterated fibre product `U_{i₀} ×_U ⋯ ×_U U_{iₙ}` of such a covering to be quasi-compact,
which follows from (3) by base change, `Stacks.Cohomology.hasIntersectionsIn_of_exists_pullback`.
The statement is then `hom_coproduct_bijective_and_isCompactObject_of_isPerfect`. -/
@[stacks 09JC "both clauses, under hypotheses (1)-(3) of the tag; the 08JJ reduction, the Tor \
  amplitude of the dual and the 0739 sums are all proved, none assumed"]
theorem hom_coproduct_bijective_and_isCompactObject_of_isPerfect_of_isQuasiCompactObject
    (X₀ : X.C) (hterm : IsTerminal X₀) (hqc : X.J.IsQuasiCompactObject X₀)
    (hcofinal : ∀ U : X.C, X.J.IsQuasiCompactObject U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{u} U, F.sieve₀ ∈ X.J U ∧ F.sieve₀ ≤ S ∧ Finite F.I₀ ∧
        ∀ i, X.J.IsQuasiCompactObject (F.X i))
    (hfibre : ∀ (U : X.C) (F : PreZeroHypercover.{u} U), F.sieve₀ ∈ X.J U → Finite F.I₀ →
      X.J.IsQuasiCompactObject U → (∀ i, X.J.IsQuasiCompactObject (F.X i)) →
      ∀ i j, ∃ t : PullbackCone (F.f i) (F.f j), Nonempty (IsLimit t) ∧
        X.J.IsQuasiCompactObject t.pt)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (hK : X.IsPerfect K) :
    (∀ {I : Type u} [DecidableEq I]
        (M : I → DerivedCategory (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) [HasCoproduct M],
        DerivedCategoryB.IsBoundedBelow (∐ M) →
        Function.Bijective
          (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j))) ∧
      ((∃ d : ℤ, ∀ (p : ℕ) (G : _root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), d < (p : ℤ) →
          IsZero (((_root_.SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op X₀)).rightDerived p).obj G)) →
        IsCompactObject.{u} K) :=
  hom_coproduct_bijective_and_isCompactObject_of_isPerfect X
    {U | X.J.IsQuasiCompactObject U}
    (fun U F => F.sieve₀ ∈ X.J U ∧ Finite F.I₀ ∧ X.J.IsQuasiCompactObject U ∧
      ∀ i, X.J.IsQuasiCompactObject (F.X i))
    (fun _ _ h => h.1)
    (fun _ F h => Stacks.Cohomology.hasIntersectionsIn_of_exists_pullback X.J
      {U | X.J.IsQuasiCompactObject U}
      (fun U F hfin hU hX hF => hfibre U F hF hfin hU hX) F h.2.1 h.2.2.1 h.2.2.2 h.1)
    (fun U hU S hS => by
      obtain ⟨F, hF, hle, hfin, hX⟩ := hcofinal U hU S hS
      exact ⟨F, ⟨hF, hfin, hU, hX⟩, hle⟩)
    X₀ hterm hqc hqc K hK

end Stacks.Cohomology.QuasiCompactSite

end
