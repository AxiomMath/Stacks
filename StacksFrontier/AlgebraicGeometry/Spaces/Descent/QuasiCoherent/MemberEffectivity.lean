module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDatumSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairCompatFromReading

/-!
# Effectivity of a descent datum from a reading of its members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  A **member-by-member reading** of a descent datum `D` relative
to that family — an `𝒪_X`-module `M`, its quasi-coherence, and for each `i` an isomorphism
`τ i : (f i)^*M ≅ D.F i` of the étale restriction of `M` with the `i`-th component of `D`,
compatible over the charts of the pairwise fibre products — gives the **effectivity** of `D`,
which is the effectivity clause of Stacks 04W6, and then the statement that the canonical
descent functor of a Zariski covering is an equivalence.

Two halves are joined here:
`AlgebraicGeometry.Space.QuasiCoherentDescent.transition_naturality_of_pairReading` turns the
compatibility of the readings over the charts of the pairwise fibre products into the pairwise
condition, in the form of the canonical comparisons of Stacks 04W5, and
`.isEtaleEffective_of_forall_iso` turns a family of isomorphisms satisfying that condition into
an isomorphism of `D` with the canonical descent datum of `M`, hence into effectivity.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_forall_iso_canonicalComparison`:
  **effectivity from a family of isomorphisms of the component modules with the inverse images of
  one quasi-coherent module, with the pairwise condition stated at the canonical comparisons of
  Stacks 04W5.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_memberReading`: **a descent
  datum of an étale family is effective as soon as its components have been read, member by
  member, as the étale restrictions of one quasi-coherent `𝒪_X`-module, compatibly over the
  charts of the pairwise fibre products.**
* `.isEquivalence_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective` and
  `.isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering`: **the canonical descent
  functor of a Zariski covering of an algebraic space is an equivalence**, granted that every
  descent datum relative to the covering is effective, respectively admits such a reading.

## Implementation notes

The reconciliation of the two halves is definitional.  The `i`-th component module of the
canonical descent datum of `M` is the inverse image `(f i)^*M` and its pairwise isomorphism is
the canonical comparison, both by
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleCanonicalDescentDatum_F` and
`.etaleCanonicalDescentDatum_transition`, which hold by `rfl`, so no transport is needed.

The isomorphism `θ i : D.F i ≅ (f i)^*M` the reading induces is the inverse of `τ i` followed by
the inverse of the comparison of Stacks 03LW, so its forward map is that composite by `rfl`;
that is exactly the hypothesis `hθ` of
`AlgebraicGeometry.Space.QuasiCoherentDescent.transition_naturality_of_pairReading`.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### Effectivity, with the pairwise condition at the canonical comparisons -/

/-- **A DESCENT DATUM OF AN ÉTALE FAMILY IS EFFECTIVE AS SOON AS ITS COMPONENT MODULES ARE THE
INVERSE IMAGES OF ONE QUASI-COHERENT MODULE COMPATIBLY WITH THE CANONICAL COMPARISONS.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_forall_iso` with the canonical
descent datum of `M` replaced by what it is: its `i`-th component module is the inverse image of
`M` along `f i` and its pairwise isomorphism is the canonical comparison of Stacks 04W5 of the
two inverse images of `M`, both definitionally. -/
theorem isEtaleEffective_of_forall_iso_canonicalComparison (D : DescentDatum B S hS Yi f)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (θ : ∀ i, D.F i ≅ (modulePullback B S hS (f i)).obj M)
    (hθ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
          (pair_condition B S hS Yi f i j) M).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) :
    IsEtaleEffective B S hS Yi f hf D :=
  isEtaleEffective_of_forall_iso B S hS Yi f hf D M hM θ hθ

/-! ### Effectivity from a reading of the members -/

/-- **STACKS 04W6, THE EFFECTIVITY CLAUSE, FROM A READING OF THE MEMBERS: a descent datum of an
étale family is effective as soon as its component modules have been identified with the étale
restrictions of one quasi-coherent `𝒪_X`-module, compatibly over the charts of the pairwise fibre
products.**

The reading is the family `τ`, an isomorphism `τ i : (f i)^*M ≅ D.F i` of the étale restriction
of `M` to the `i`-th member with the `i`-th component module of `D`.  Its compatibility `hT` is a
statement about sections alone: restricting a section of `M` along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of a chart of `Y i ×_X Y j` and
reading it through `τ j` is reading it through `τ i` and transporting it by the pairwise
isomorphism of `D`.

Through the comparison of Stacks 03LW the reading becomes a family of isomorphisms of `D.F i`
with the inverse image `(f i)^*M` of Stacks 03LU; the compatibility makes that family commute
with the canonical comparisons, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.transition_naturality_of_pairReading`; and
`.isEtaleEffective_of_forall_iso_canonicalComparison` then identifies `D` with the canonical
descent datum of `M`. -/
theorem isEtaleEffective_of_memberReading (D : DescentDatum B S hS Yi f)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
    (hT : ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (σ : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
      (τ j).hom.val.app
          (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
          (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
        etaleSect B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
          ((D.transition i j).hom.val.app (.op Z)
            (etaleSectInv B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
              ((τ i).hom.val.app
                (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                  (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ)))) :
    IsEtaleEffective B S hS Yi f hf D :=
  let θ := fun i => (τ i).symm ≪≫
    ((modulePullbackIsoEtaleModulePullback B S hS (f i) (hf i)).app M).symm
  isEtaleEffective_of_forall_iso_canonicalComparison B S hS Yi f hf D M hM θ
    (transition_naturality_of_pairReading B S hS Yi f hf D M τ θ (fun _ => rfl) hT)

/-! ### The equivalence -/

/-- **The canonical descent functor of a Zariski covering is an equivalence as soon as every
descent datum relative to the covering is effective.**  This is
`.isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj`
fed by `.essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective`. -/
theorem isEquivalence_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom))
    (h : ∀ D : DescentDatum B S hS Yi f, IsEtaleEffective B S hS Yi f hf D) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).IsEquivalence :=
  isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj B S hS Yi f hf hcov
    (essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective B S hS Yi f hf h)

/-- **STACKS 04W6 FOR A ZARISKI COVERING OF AN ALGEBRAIC SPACE: the canonical descent functor of
a Zariski covering is an equivalence**, granted that every descent datum relative to the covering
admits a reading of its members.

The hypothesis `heff` is the effectivity input, written out: for every descent datum `D` there is
a quasi-coherent `𝒪_X`-module `M` and a family of isomorphisms of the component modules of `D`
with the étale restrictions of `M` whose readings agree over the charts of the pairwise fibre
products, which is the hypothesis of
`AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_memberReading`.

Faithfulness and fullness need nothing beyond the covering; essential surjectivity is
`.essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective` applied to the effectivity
`heff` yields datum by datum, and the three are assembled by
`.isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj`. -/
theorem isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom))
    (heff : ∀ D : DescentDatum B S hS Yi f,
      ∃ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
        (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i),
        ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
          (σ : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
            ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
          (τ j).hom.val.app
              (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
              (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
            etaleSect B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
              ((D.transition i j).hom.val.app (.op Z)
                (etaleSectInv B S hS (pairFst B S hS Yi f i j)
                  (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
                  ((τ i).hom.val.app
                    (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                      (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ)))) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).IsEquivalence :=
  isEquivalence_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective B S hS Yi f hf hcov
    fun D => by
      obtain ⟨M, hM, τ, hT⟩ := heff D
      exact isEtaleEffective_of_memberReading B S hS Yi f hf D M hM τ hT

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
