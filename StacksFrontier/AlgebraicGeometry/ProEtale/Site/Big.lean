module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
public import StacksCore.Tactic.StacksAttribute

/-!
# Big pro-étale sites

This file develops a cardinal-cutoff model of a big pro-étale site: the full subcategory of all
schemes whose size lies below a suitable cardinal, with the pro-étale covering families whose
index sets are bounded by a second cardinal. Neither the objects nor the coverings of this model
form a set; the big pro-étale site of Stacks 098G, built on a set of schemes as in Stacks 000J and
a set of coverings as in Stacks 000X, is `AlgebraicGeometry.ProEtale.SetBigProetaleSite` in
`StacksFrontier.AlgebraicGeometry.ProEtale.Site.BigSet`.

## Main definitions

* `Cardinal.proetaleBound` is the enlarged cardinal bound used for the pro-étale site.
* `AlgebraicGeometry.ProEtale.BoundedScheme` is the full subcategory of schemes whose size lies
  below a given cardinal.
* `AlgebraicGeometry.ProEtale.IsProetaleCovering` is the pro-étale covering condition on a
  covering family in that subcategory.
* `CategoryTheory.coveringPrecoverage` is the precoverage cut out by a predicate on bundled
  covering families.
* `AlgebraicGeometry.ProEtale.BigProetaleSite` is a cardinal-cutoff model of a big pro-étale
  site, on which the pro-étale sheaf theory of this library is developed. The big pro-étale site
  of Stacks 098G itself is `AlgebraicGeometry.ProEtale.SetBigProetaleSite`, in
  `StacksFrontier.AlgebraicGeometry.ProEtale.Site.BigSet`.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.precoverage` is the precoverage of its chosen
  covering presieves, `BigProetaleSite.pretopology` the pretopology they form and
  `BigProetaleSite.topology` the Grothendieck topology they generate.

## Main results

* `AlgebraicGeometry.ProEtale.BigProetaleSite.covering_iff` characterizes chosen covering
  families by the pro-étale condition and the bound on their index sets.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.precoverage_eq_comap` identifies the covering
  presieves with the restriction of the ambient pro-étale precoverage.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.mem_topology_iff` characterizes covering sieves
  by containment of a chosen covering family.

## References

* [Stacks Project, Tag 098G](https://stacks.math.columbia.edu/tag/098G), whose definition is
  formalized in `StacksFrontier.AlgebraicGeometry.ProEtale.Site.BigSet`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

/-- The enlarged cardinal bound used in the construction of a big pro-étale site:
`max { κ ^ (2 ^ (2 ^ (2 ^ κ))), κ ^ ℵ₀, κ⁺ }`, the last two terms being
`Cardinal.stacksBound κ`. -/
noncomputable abbrev Cardinal.proetaleBound (k : Cardinal.{u}) : Cardinal.{u} :=
  max (k ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ k))))
    (Cardinal.stacksBound k)

/-- The precoverage associated to a predicate on bundled covering families: a presieve is
covering when it is the presieve of a covering family satisfying the predicate. -/
def CategoryTheory.coveringPrecoverage {C : Type u} [Category.{v} C]
    (P : Covering.{u, v, max u v} C → Prop) : Precoverage C where
  coverings X := {R | ∃ E : PreZeroHypercover X, E.presieve₀ = R ∧ P ⟨X, E⟩}

namespace AlgebraicGeometry.ProEtale

/-- The property cutting out the full subcategory of schemes below `k`. -/
abbrev boundedSchemeProperty (k : Cardinal.{u}) : ObjectProperty Scheme.{u} :=
  fun X ↦ X.size < k

/-- The full subcategory of schemes whose size is below `k`. -/
abbrev BoundedScheme (k : Cardinal.{u}) := (boundedSchemeProperty k).FullSubcategory

/-- A covering family in the bounded category is pro-étale when its image in schemes is a
covering family for Mathlib's pro-étale precoverage. -/
def IsProetaleCovering (k : Cardinal.{u})
    (U : Covering.{u + 1, u, u + 1} (BoundedScheme k)) : Prop :=
  (U.2.map (boundedSchemeProperty k).ι).presieve₀ ∈
    Scheme.proetalePrecoverage.coverings U.1.obj

/-- Having size below `k` is invariant under isomorphism of schemes. -/
instance (k : Cardinal.{u}) : (boundedSchemeProperty k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    change X.size < k at h
    change Y.size < k
    rwa [← AlgebraicGeometry.Scheme.size_congr e]

/-- The schemes of size below `k` are closed under fibre products. -/
instance (k : Cardinal.{u}) :
    (boundedSchemeProperty k).IsClosedUnderLimitsOfShape WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    change (limit F).size < k
    rw [AlgebraicGeometry.Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact AlgebraicGeometry.Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

/-- A cardinal-cutoff model of a big pro-étale site: the underlying category is the full
subcategory of *all* schemes of size below an uncountable strong limit cardinal `cutoff` (a class
closed under isomorphism, not a set of schemes), and the coverings are *all* pro-étale families
whose index set has cardinality at most `coveringBound` (again not a set). The ordinal
`coveringOrdinal` plays no role. This is a convenient large-category model on which the
pro-étale sheaf theory of this library is developed, and not the site of Stacks 098G itself,
which is `AlgebraicGeometry.ProEtale.SetBigProetaleSite`: there the underlying category is a set
of schemes with the countable limit and colimit properties of Stacks 000J, and the coverings form
a set as in Stacks 000X. -/
structure BigProetaleSite where
  /-- The cardinal cutoff defining the underlying category of schemes. -/
  cutoff : Cardinal.{u}
  /-- The cutoff is uncountable. -/
  aleph0_lt_cutoff : aleph0 < cutoff
  /-- The cutoff is a strong limit cardinal. -/
  cutoff_isStrongPrelimit : Cardinal.IsStrongPrelimit cutoff
  /-- The cutoff has uncountable cofinality. -/
  aleph0_lt_cutoff_cof : aleph0 < cutoff.ord.cof
  /-- The initially chosen set of schemes. -/
  seedSchemes : Set Scheme.{u}
  /-- The initial collection of schemes is set-sized at the working universe. -/
  seedSchemes_small : Small.{u} seedSchemes
  /-- Every initially chosen scheme belongs to the bounded category. -/
  seedSchemes_mem : ∀ X ∈ seedSchemes, X.size < cutoff
  /-- Closure of the bounded category under the modified pro-étale bound. -/
  closed_under_proetaleBound :
    ∀ {X Y : Scheme.{u}}, X.size < cutoff →
      Y.size ≤ Cardinal.proetaleBound X.size → Y.size < cutoff
  /-- Closure under applying the modified bound to a countable supremum of object sizes. -/
  closed_under_proetaleBound_iSup :
    ∀ {I : Type u}, #I ≤ aleph0 → ∀ (F : I → Scheme.{u}),
      (∀ i, (F i).size < cutoff) → ∀ {X : Scheme.{u}},
        X.size ≤ Cardinal.proetaleBound (⨆ i, (F i).size) → X.size < cutoff
  /-- The cardinal bounding the index types of the chosen covering families. -/
  coveringBound : Cardinal.{u + 1}
  /-- The limit ordinal occurring in the set-sized choice of coverings. -/
  coveringOrdinal : Ordinal.{u + 1}
  /-- The covering ordinal is a limit ordinal. -/
  coveringOrdinal_isSuccLimit : Order.IsSuccLimit coveringOrdinal
  /-- The initially chosen set of pro-étale covering families. -/
  seedCoverings : Set (Covering (BoundedScheme cutoff))
  /-- The initial collection of covering families is set-sized. -/
  seedCoverings_small : Small.{u + 1} seedCoverings
  /-- All objects occurring in an initial covering belong to the initial set of schemes. -/
  seedCoverings_objects : ∀ U ∈ seedCoverings,
    U.1.obj ∈ seedSchemes ∧ ∀ i, (U.2.X i).obj ∈ seedSchemes
  /-- Every initially chosen covering family is pro-étale. -/
  seedCoverings_proetale : ∀ U ∈ seedCoverings, IsProetaleCovering cutoff U
  /-- Every initially chosen covering belongs to the bounded choice of coverings. -/
  seedCoverings_bounded : ∀ U ∈ seedCoverings,
    CovBounded (IsProetaleCovering cutoff) coveringBound U
  /-- The bounded pro-étale covering families satisfy the site axioms. -/
  covering_isSite : IsSite (CovBounded (IsProetaleCovering cutoff) coveringBound)
  /-- Every pro-étale covering has a combinatorially equivalent chosen representative. -/
  covering_representatives :
    ∀ U : Covering (BoundedScheme cutoff), IsProetaleCovering cutoff U →
      ∃ U' : Covering (BoundedScheme cutoff),
        CovBounded (IsProetaleCovering cutoff) coveringBound U' ∧
          Covering.CombEquiv U U'

namespace BigProetaleSite

/-- A scheme is contained in a big pro-étale site when it satisfies the site's size cutoff. -/
abbrev Contains (B : BigProetaleSite.{u}) (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  X.size < B.cutoff

/-- The underlying category of a big pro-étale site. -/
abbrev Scheme (B : BigProetaleSite.{u}) := BoundedScheme B.cutoff

/-- The fully faithful inclusion of a big pro-étale site's underlying category into schemes. -/
abbrev inclusion (B : BigProetaleSite.{u}) : Functor B.Scheme AlgebraicGeometry.Scheme.{u} :=
  (boundedSchemeProperty B.cutoff).ι

/-- The inclusion of a big pro-étale site's underlying category into schemes is full. -/
instance (B : BigProetaleSite.{u}) : B.inclusion.Full :=
  inferInstanceAs (boundedSchemeProperty B.cutoff).ι.Full

/-- The inclusion of a big pro-étale site's underlying category into schemes is faithful. -/
instance (B : BigProetaleSite.{u}) : B.inclusion.Faithful :=
  inferInstanceAs (boundedSchemeProperty B.cutoff).ι.Faithful

/-- The bounded category of a big pro-étale site has fibre products. -/
instance hasPullbacks (B : BigProetaleSite.{u}) : HasPullbacks B.Scheme :=
  inferInstanceAs (HasPullbacks (boundedSchemeProperty B.cutoff).FullSubcategory)

/-- Fibre products in the bounded category of a big pro-étale site are those of schemes. -/
noncomputable instance createsPullbacks (B : BigProetaleSite.{u}) :
    CreatesLimitsOfShape WalkingCospan B.inclusion :=
  inferInstanceAs (CreatesLimitsOfShape WalkingCospan (boundedSchemeProperty B.cutoff).ι)

/-- The inclusion of a big pro-étale site's underlying category into schemes preserves fibre
products. -/
noncomputable instance (B : BigProetaleSite.{u}) :
    PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance

/-- The ambient pro-étale covering predicate on the underlying category. -/
abbrev IsProetaleCovering (B : BigProetaleSite.{u}) : Covering B.Scheme → Prop :=
  ProEtale.IsProetaleCovering B.cutoff

/-- The chosen covering families of a big pro-étale site. -/
abbrev covering (B : BigProetaleSite.{u}) : Covering B.Scheme → Prop :=
  CovBounded B.IsProetaleCovering B.coveringBound

/-- The precoverage consisting of the chosen covering families. -/
def precoverage (B : BigProetaleSite.{u}) : Precoverage B.Scheme :=
  coveringPrecoverage B.covering

/-- The Grothendieck topology generated by the chosen pro-étale covering families. -/
abbrev topology (B : BigProetaleSite.{u}) : GrothendieckTopology B.Scheme :=
  B.precoverage.toGrothendieck

/-- Membership in the chosen covering system retains the index bound. -/
@[simp]
lemma covering_iff (B : BigProetaleSite.{u}) (U : Covering B.Scheme) :
    B.covering U ↔ (B.IsProetaleCovering U ∧ #U.2.I₀ ≤ B.coveringBound) := Iff.rfl

/-- The ambient covering condition is tested by mapping the family to schemes. -/
@[simp]
lemma isProetaleCovering_iff (B : BigProetaleSite.{u}) (U : Covering B.Scheme) :
    B.IsProetaleCovering U ↔
      (U.2.map B.inclusion).presieve₀ ∈
        AlgebraicGeometry.Scheme.proetalePrecoverage.coverings U.1.obj := Iff.rfl

/-- A covering presieve is the presieve of a chosen covering family. -/
lemma mem_precoverage_iff (B : BigProetaleSite.{u}) {X : B.Scheme} (R : Presieve X) :
    R ∈ B.precoverage.coverings X ↔
      ∃ E : PreZeroHypercover.{u + 1} X, E.presieve₀ = R ∧ B.covering ⟨X, E⟩ := Iff.rfl

/-- Combinatorial representatives ensure that passing from all pro-étale families to
the chosen families does not change the covering presieves. -/
lemma precoverage_eq_comap (B : BigProetaleSite.{u}) :
    B.precoverage = AlgebraicGeometry.Scheme.proetalePrecoverage.comap B.inclusion := by
  ext X R
  constructor
  · rintro ⟨E, rfl, hE⟩
    simpa only [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map,
      inclusion, ObjectProperty.ι_obj] using
      (B.isProetaleCovering_iff ⟨X, E⟩).mp hE.1
  · intro hR
    let E : PreZeroHypercover.{u + 1} X := R.preZeroHypercover
    have hE : E.presieve₀ = R := R.presieve₀_preZeroHypercover
    have hcov : B.IsProetaleCovering ⟨X, E⟩ := by
      change (E.map B.inclusion).presieve₀ ∈ _; rwa [PreZeroHypercover.presieve₀_map, hE]
    obtain ⟨⟨Y, F⟩, hF, hXY, hEF⟩ := B.covering_representatives ⟨X, E⟩ hcov
    obtain rfl : X = Y := hXY
    exact ⟨F, (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hEF).symm.trans hE, hF⟩

/-- The presieve of a single isomorphism is a covering presieve of a big pro-étale site. -/
instance (B : BigProetaleSite.{u}) : B.precoverage.HasIsos := by
  rw [B.precoverage_eq_comap]; infer_instance

/-- The coverings of a big pro-étale site are stable under base change. -/
instance (B : BigProetaleSite.{u}) : B.precoverage.IsStableUnderBaseChange := by
  rw [B.precoverage_eq_comap]; infer_instance

/-- The coverings of a big pro-étale site are stable under composition. -/
instance (B : BigProetaleSite.{u}) : B.precoverage.IsStableUnderComposition := by
  rw [B.precoverage_eq_comap]; infer_instance

/-- The pretopology of the chosen big pro-étale site. -/
abbrev pretopology (B : BigProetaleSite.{u}) : Pretopology B.Scheme :=
  B.precoverage.toPretopology

/-- A sieve covers precisely when it contains one of the chosen covering families. -/
lemma mem_topology_iff (B : BigProetaleSite.{u}) {X : B.Scheme} (S : Sieve X) :
    S ∈ B.topology X ↔
      ∃ E : PreZeroHypercover.{u + 1} X, B.covering ⟨X, E⟩ ∧ E.presieve₀ ≤ S := by
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]; constructor
  · rintro ⟨R, ⟨E, rfl, hE⟩, hRS⟩; exact ⟨E, hE, hRS⟩
  · rintro ⟨E, hE, hES⟩; exact ⟨E.presieve₀, ⟨E, rfl, hE⟩, hES⟩

end BigProetaleSite

end AlgebraicGeometry.ProEtale
