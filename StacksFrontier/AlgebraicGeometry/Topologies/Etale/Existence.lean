module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Big étale sites exist

Every result in this library indexed by a big étale site `B : AlgebraicGeometry.BigEtaleSite`
takes `B` as a hypothesis. This file discharges that hypothesis: a big étale site is
constructed, for any prescribed initial data, so that the hypothesis can always be met.

The construction is the composition of the two halves that Stacks 000J and Stacks 000X supply
separately.

* Stacks 000J, in the form `AlgebraicGeometry.exists_size_cutoff`, produces the size cutoff:
  a cardinal `κ` with `ℵ₀ < κ`, `Cardinal.IsStrongPrelimit κ` and `ℵ₀ < κ.ord.cof` above the
  sizes of all the prescribed schemes. The three conditions on `κ` are exactly the fields
  `aleph0_lt_cutoff`, `cutoff_isStrongPrelimit` and `aleph0_lt_cutoff_cof`, and they are what
  makes the resulting category of schemes closed under the constructions of Stacks 000R; in
  particular `AlgebraicGeometry.Scheme.size_pullback_lt` gives it fibre products.
* Stacks 000X, in the form `exists_covBounded_isSite`, produces the covering bound: a cardinal
  `κ'` such that the étale covering families whose index type has cardinality at most `κ'`
  still satisfy the site axioms, still contain the prescribed initial coverings, and still
  represent every étale covering family up to combinatorial equivalence
  (Stacks 00VU (1)). Its input is that the *unbounded* étale covering families of the cutoff
  category satisfy the site axioms, which is `AlgebraicGeometry.isSite_etaleCutoff`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.ofCutoff` — a big étale site with a prescribed cutoff
  cardinal, prescribed initial set of schemes and prescribed initial set of covering families.
* `AlgebraicGeometry.BigEtaleSite.ofSet` — a big étale site containing a prescribed small set
  of schemes, the cutoff being chosen by Stacks 000J.
* `AlgebraicGeometry.BigEtaleSite.containing` — a big étale site containing a prescribed
  scheme.
* `AlgebraicGeometry.Scheme.smallEtaleSheafEquiv` — for a bare scheme `X`, an equivalence
  between the sheaves of the small étale site of Stacks 021B of a big étale site containing
  `X` and the sheaves of Mathlib's small étale site of `X`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.contains_ofSet`, `contains_containing` — the constructed site
  contains the schemes it was asked to contain.
* `AlgebraicGeometry.BigEtaleSite.exists_contains` and the `Nonempty` instance — the existence
  statements, with no data to pick.

## The covering bound is not a weakening

The selected covering families of a big étale site are bounded, so one may worry that the
construction buys existence at the price of a site with too few coverings. It does not: by
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`, every jointly surjective
family in the small étale category of a contained scheme already generates a covering sieve of
the resulting topology. That is because the representative produced by
`AlgebraicGeometry.BigEtaleSite.exists_covering_rep` matches a given family arrow for arrow
without preserving its index type, so a bounded representative of an unbounded family is a
reindexing of a subfamily, and a presieve remembers only the set of arrows. The identification
of sheaves in `AlgebraicGeometry.Scheme.smallEtaleSheafEquiv` is the same point at the level of
topoi.

## Implementation notes

The two halves cannot be chosen independently: the type `Covering (SchemeBelow κ)` of covering
families of the cutoff category mentions the cutoff, so the initial coverings can only be
prescribed once `κ` is fixed. Accordingly `ofCutoff` takes `κ` as a parameter, and `ofSet`
instantiates it with the cutoff of Stacks 000J and no initial coverings — the only choice
available before `κ` exists.

The existential content of Stacks 000X is extracted once, in `BigEtaleSite.boundedCoverings`,
as a subtype rather than by iterated `Exists.choose`. This keeps the `S₀` and `cutoff` fields of
`ofCutoff` definitionally equal to their arguments, which is what makes `s₀_ofCutoff` and
`cutoff_ofCutoff` hold by `rfl` and what `contains_ofSet` rests on.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open Cardinal CategoryTheory

universe v' u' u

namespace AlgebraicGeometry

namespace BigEtaleSite

/-- The conclusion of Stacks 000X for the étale covering families of the category of schemes
cut off at `κ`, packaged as data: a covering bound and a limit ordinal, together with the four
properties the fields of `AlgebraicGeometry.BigEtaleSite` ask of them. -/
public noncomputable def boundedCoverings (κ : Cardinal.{u})
    (Cov₀ : Set (Covering.{u + 1, u, u + 1} (SchemeBelow κ))) [Small.{u + 1} Cov₀]
    (hCov₀ : ∀ 𝒰 ∈ Cov₀, IsEtaleCovering 𝒰) :
    {p : Cardinal.{u + 1} × Ordinal.{u + 1} //
      Order.IsSuccLimit p.2 ∧
      (∀ 𝒰 ∈ Cov₀, CovBounded IsEtaleCovering p.1 𝒰) ∧
      IsSite (CovBounded (IsEtaleCovering (κ := κ)) p.1) ∧
      ∀ 𝒰 : Covering (SchemeBelow κ), IsEtaleCovering 𝒰 →
        ∃ 𝒱 : Covering (SchemeBelow κ),
          CovBounded IsEtaleCovering p.1 𝒱 ∧ Covering.CombEquiv 𝒰 𝒱} :=
  Classical.choice <| by
    obtain ⟨κ', α, hα, hinit, hsite, hrep⟩ :=
      exists_covBounded_isSite (IsEtaleCovering (κ := κ)) (isSite_etaleCutoff κ) Cov₀ hCov₀
    exact ⟨⟨(κ', α), hα, hinit, hsite, hrep⟩⟩

/-- **A big étale site with a prescribed cutoff and prescribed initial data.** The cutoff `κ`
must satisfy the three conditions of Stacks 000J and dominate the sizes of the initial schemes;
the initial covering families must be étale and have all their objects among the initial
schemes. The covering bound is then supplied by Stacks 000X. -/
public noncomputable def ofCutoff (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀] (hS₀ : ∀ X ∈ S₀, X.size < κ)
    (Cov₀ : Set (Covering.{u + 1, u, u + 1} (SchemeBelow κ))) [Small.{u + 1} Cov₀]
    (hobj : ∀ 𝒰 ∈ Cov₀, (schemeBelowInclusion κ).obj 𝒰.1 ∈ S₀ ∧
      ∀ i, (schemeBelowInclusion κ).obj (𝒰.2.X i) ∈ S₀)
    (hCov₀ : ∀ 𝒰 ∈ Cov₀, IsEtaleCovering 𝒰) :
    BigEtaleSite.{u} where
  S₀ := S₀
  small_S₀ := inferInstance
  cutoff := κ
  aleph0_lt_cutoff := hκ
  cutoff_isStrongPrelimit := hsl
  aleph0_lt_cutoff_cof := hcof
  mem_cutoff_of_mem := hS₀
  initialCoverings := Cov₀
  small_initialCoverings := inferInstance
  initial_objects_mem := hobj
  initialCoverings_etale := hCov₀
  coveringBound := (boundedCoverings κ Cov₀ hCov₀).1.1
  coveringOrdinal := (boundedCoverings κ Cov₀ hCov₀).1.2
  coveringOrdinal_isSuccLimit := (boundedCoverings κ Cov₀ hCov₀).2.1
  initialCoverings_bounded := (boundedCoverings κ Cov₀ hCov₀).2.2.1
  coverings_isSite := (boundedCoverings κ Cov₀ hCov₀).2.2.2.1
  exists_covering_rep := (boundedCoverings κ Cov₀ hCov₀).2.2.2.2

section OfCutoff

variable {κ : Cardinal.{u}} {hκ : ℵ₀ < κ} {hsl : Cardinal.IsStrongPrelimit κ}
  {hcof : ℵ₀ < κ.ord.cof} {S₀ : Set AlgebraicGeometry.Scheme.{u}} [Small.{u} S₀]
  {hS₀ : ∀ X ∈ S₀, X.size < κ}
  {Cov₀ : Set (Covering.{u + 1, u, u + 1} (SchemeBelow κ))} [Small.{u + 1} Cov₀]
  {hobj : ∀ 𝒰 ∈ Cov₀, (schemeBelowInclusion κ).obj 𝒰.1 ∈ S₀ ∧
    ∀ i, (schemeBelowInclusion κ).obj (𝒰.2.X i) ∈ S₀}
  {hCov₀ : ∀ 𝒰 ∈ Cov₀, IsEtaleCovering 𝒰}

/-- The cutoff of the big étale site `ofCutoff κ …` is `κ`. -/
@[simp]
public theorem cutoff_ofCutoff :
    (ofCutoff κ hκ hsl hcof S₀ hS₀ Cov₀ hobj hCov₀).cutoff = κ := rfl

/-- The initial set of schemes of the big étale site `ofCutoff κ hκ hsl hcof S₀ …` is `S₀`. -/
@[simp]
public theorem s₀_ofCutoff :
    (ofCutoff κ hκ hsl hcof S₀ hS₀ Cov₀ hobj hCov₀).S₀ = S₀ := rfl

end OfCutoff

/-- Every scheme in the initial set of a big étale site is contained in it. -/
public theorem contains_of_mem_s₀ (B : BigEtaleSite.{u}) {X : AlgebraicGeometry.Scheme.{u}}
    (hX : X ∈ B.S₀) : B.Contains X := B.mem_cutoff_of_mem X hX

/-- **A big étale site containing a prescribed small set of schemes.** The cutoff is the one
Stacks 000J provides for that set, and no covering families are prescribed — the only choice
possible, since a covering family of the cutoff category cannot be named before the cutoff
exists. -/
public noncomputable def ofSet (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀] :
    BigEtaleSite.{u} :=
  ofCutoff (exists_size_cutoff S₀).choose (exists_size_cutoff S₀).choose_spec.1
    (exists_size_cutoff S₀).choose_spec.2.1 (exists_size_cutoff S₀).choose_spec.2.2.1
    S₀ (exists_size_cutoff S₀).choose_spec.2.2.2 ∅ (by simp) (by simp)

/-- The initial set of schemes of the big étale site `ofSet S₀` is `S₀`. -/
@[simp]
public theorem s₀_ofSet (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀] :
    (ofSet S₀).S₀ = S₀ := rfl

/-- The big étale site built from a set of schemes contains every member of that set. -/
public theorem contains_ofSet (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀]
    {X : AlgebraicGeometry.Scheme.{u}} (hX : X ∈ S₀) : (ofSet S₀).Contains X :=
  (ofSet S₀).contains_of_mem_s₀ hX

/-- **A big étale site containing a prescribed scheme.** -/
public noncomputable def containing (X : AlgebraicGeometry.Scheme.{u}) : BigEtaleSite.{u} :=
  have := small_single.{u} X
  ofSet {X}

/-- The big étale site built from a scheme contains that scheme. -/
public theorem contains_containing (X : AlgebraicGeometry.Scheme.{u}) :
    (containing X).Contains X :=
  have := small_single.{u} X
  contains_ofSet {X} rfl

/-- **Every scheme lies in a big étale site.** -/
public theorem exists_contains (X : AlgebraicGeometry.Scheme.{u}) :
    ∃ B : BigEtaleSite.{u}, B.Contains X := ⟨containing X, contains_containing X⟩

/-- Every small set of schemes lies in a single big étale site. -/
public theorem exists_contains_of_small (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀] :
    ∃ B : BigEtaleSite.{u}, ∀ X ∈ S₀, B.Contains X :=
  ⟨ofSet S₀, fun _ hX => contains_ofSet S₀ hX⟩

/-- **Big étale sites exist.** -/
public instance nonempty : Nonempty BigEtaleSite.{u} := ⟨ofSet ∅⟩

end BigEtaleSite

/-- The small étale category of `AlgebraicGeometry.BigEtaleSite.containing X` on `X` itself:
the small étale site of Stacks 021B of a bare scheme, with no big étale site assumed. -/
public noncomputable abbrev Scheme.smallEtaleSite (X : Scheme.{u}) :=
  SmallEtale (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)

/-- The Grothendieck topology of Stacks 021B on the small étale site of a bare scheme. -/
public noncomputable abbrev Scheme.smallEtaleSiteTopology (X : Scheme.{u}) :
    GrothendieckTopology X.smallEtaleSite :=
  SmallEtale.topology (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)

/-- **The small étale site of Stacks 021B of a bare scheme has the same sheaves as Mathlib's.**
This is `AlgebraicGeometry.SmallEtale.sheafEquiv` with its big étale site discharged by
`AlgebraicGeometry.BigEtaleSite.containing`. -/
public noncomputable def Scheme.smallEtaleSheafEquiv (X : Scheme.{u}) (A : Type u')
    [Category.{v'} A] [Limits.HasLimitsOfSize.{u, u} A] :
    Sheaf X.smallEtaleSiteTopology A ≌ Sheaf X.smallEtaleTopology A :=
  SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X) A

end AlgebraicGeometry

end
