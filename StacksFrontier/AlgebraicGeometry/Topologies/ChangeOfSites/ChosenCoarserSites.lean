module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# The Zariski, étale, smooth and syntomic sites of a chosen big fppf site (Stacks 03FF)

Having chosen a big fppf site `B`, Stacks 03FF declares the big Zariski, étale, smooth and
syntomic sites on the *same* size-bounded category of schemes `Sch_κ`, their covering families
being those families chosen by `B` which are in addition coverings for the coarser topology.
`AlgebraicGeometry.BigFppfSite.zariskiCovering` and its three companions record those four
sub-collections. Each of them satisfies the site axioms and is combinatorially cofinal, hence
assembles into a term of the corresponding bundled site structure carrying `B`'s own cutoff and
covering bound.

The four sites so obtained have cutoff *syntactically* `B.cutoff` and covering bound
syntactically `B.coveringBound`. Consequently the slice
categories and their affine subcategories agree with the fppf ones on the nose — for instance
`AlgebraicGeometry.BigAffineEtale B.toBigEtaleSite S hS` and
`AlgebraicGeometry.BigAffineFppf B S hS` are the same category — so a result about one of the
coarser sites applies to a big fppf site with no transport and no cutoff-equality hypothesis.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.toBigZariskiSite`,
  `AlgebraicGeometry.BigFppfSite.toBigEtaleSite`,
  `AlgebraicGeometry.BigFppfSite.toBigSmoothSite` and
  `AlgebraicGeometry.BigFppfSite.toBigSyntomicSite`: the four coarser big sites carried by a
  big fppf site.

## Main results

* `AlgebraicGeometry.covBounded_iff_chosenCovering`: for a precoverage below the fppf one, the
  families lying in it whose index type meets `B`'s covering bound are exactly the families
  chosen by `B` which lie in it; being fppf is implied, so only the bound survives.
* `AlgebraicGeometry.isSite_covBounded_of_le_fppfPrecoverage` and
  `AlgebraicGeometry.exists_covBounded_combEquiv_of_le_fppfPrecoverage`: the site axioms and
  combinatorial cofinality for such a class of families, specialized to the four topologies in
  `AlgebraicGeometry.BigFppfSite.isSite_covBounded_isZariskiCovering` and its companions.
* `AlgebraicGeometry.isZariskiCovering_iff_mem_precoverage`,
  `AlgebraicGeometry.smoothCovering_iff_mem_precoverage` and
  `AlgebraicGeometry.syntomicCovering_iff_mem_precoverage`: the three covering predicates of
  the cutoff category, read as membership in a precoverage of schemes.
* `AlgebraicGeometry.BigFppfSite.toBigEtaleSite_cutoff` and its companions: the cutoffs and the
  covering bounds are `B`'s own, by `rfl`, and the covering families are the four
  sub-collections of Stacks 03FF.

## Implementation notes

The two general results are stated for an arbitrary precoverage `Q` of schemes below the fppf
precoverage, satisfying the three stability conditions; the four topologies differ only in
which `Q` they supply and in the identification of their covering predicate with membership in
it. The étale identification is `Iff.rfl`, since `AlgebraicGeometry.IsEtaleCovering` is defined
as that membership, and so are the Zariski and smooth ones; the syntomic one is
`AlgebraicGeometry.isSyntomicCovering_iff_mem_precoverage`, joint surjectivity being recorded
there as a union of ranges rather than as a lifting property.

Nothing here re-chooses a cutoff or a covering bound, so there is no appeal to Stacks 000X
(`exists_covBounded_isSite`) and no choice principle is involved: both bounds are read off `B`.
The initial data is carried across as well, the initial covering families being cut down to
those which are coverings for the coarser topology, as the structures require.

The site axioms themselves are `AlgebraicGeometry.isSite_and_precoverage` and combinatorial
cofinality is `AlgebraicGeometry.covering_has_representative`; both are general in `Q`. For the
étale case the resulting site conditions are also `AlgebraicGeometry.etaleCovering_isSite` and
`AlgebraicGeometry.etaleCovering_has_representative`.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The covering predicates of a cutoff category, as membership in a precoverage -/

/-- A family in a size-bounded category of schemes is a Zariski covering exactly when its image
in schemes lies in the Zariski precoverage. -/
theorem isZariskiCovering_iff_mem_precoverage {κ : Cardinal.{u}}
    (E : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) :
    IsZariskiCovering E ↔ (E.2.map (schemeBelowInclusion κ)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((schemeBelowInclusion κ).obj E.1) :=
  Iff.rfl

/-- A family in a size-bounded category of schemes is a smooth covering exactly when its image
in schemes lies in the precoverage of jointly surjective families of smooth morphisms. -/
theorem smoothCovering_iff_mem_precoverage (κ : Cardinal.{u})
    (E : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) :
    SmoothCovering κ E ↔ (E.2.map (schemeBelowInclusion κ)).presieve₀ ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})
        ((schemeBelowInclusion κ).obj E.1) :=
  Iff.rfl

/-- A family in a size-bounded category of schemes is a syntomic covering exactly when its
image in schemes lies in the precoverage of jointly surjective families of syntomic
morphisms. -/
theorem syntomicCovering_iff_mem_precoverage (κ : Cardinal.{u})
    (E : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) :
    SyntomicCovering κ E ↔ (E.2.map (schemeBelowInclusion κ)).presieve₀ ∈
      Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})
        ((schemeBelowInclusion κ).obj E.1) :=
  isSyntomicCovering_iff_mem_precoverage

/-! ### The two site conditions, for an arbitrary coarser precoverage -/

/-- A covering family of the underlying category of a big fppf site whose image in schemes lies
in a precoverage below the fppf precoverage is an fppf covering family. -/
theorem isFppfCovering_of_mem_precoverage (B : BigFppfSite.{u}) (Q : Precoverage Scheme.{u})
    (hQ : Q ≤ Scheme.fppfPrecoverage) {E : Covering B.Schemes}
    (hE : (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1)) :
    IsFppfCovering E := by
  show E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion E.1
  rw [Precoverage.mem_comap_iff]
  simpa [PreZeroHypercover.map] using hQ _ hE

/-- For a precoverage below the fppf precoverage, the families of a big fppf site's
category which lie in it and whose index type meets the site's covering bound are
exactly the families chosen by the site which lie in it: being fppf is implied, so only the
bound survives. -/
theorem covBounded_iff_chosenCovering (B : BigFppfSite.{u}) (Q : Precoverage Scheme.{u})
    (hQ : Q ≤ Scheme.fppfPrecoverage) (P : Covering B.Schemes → Prop)
    (hP : ∀ E, P E ↔ (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1))
    (E : Covering B.Schemes) :
    CovBounded P B.coveringBound E ↔ B.IsCovering E ∧ P E := by
  refine ⟨fun h => ⟨⟨?_, h.2⟩, h.1⟩, fun h => ⟨h.2, B.card_le_of_isCovering h.1⟩⟩
  exact isFppfCovering_of_mem_precoverage B Q hQ ((hP E).mp h.1)

/-- The equality of classes of covering families underlying
`AlgebraicGeometry.covBounded_iff_chosenCovering`, in the shape in which the site conditions
are transported. -/
theorem chosenCovering_eq_covBounded (B : BigFppfSite.{u}) (Q : Precoverage Scheme.{u})
    (hQ : Q ≤ Scheme.fppfPrecoverage) :
    (fun E : Covering B.Schemes => B.IsCovering E ∧
        (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1)) =
      CovBounded (fun E : Covering B.Schemes =>
        (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1)) B.coveringBound :=
  funext fun E => propext (covBounded_iff_chosenCovering B Q hQ _ (fun _ => Iff.rfl) E).symm

/-- For a precoverage of schemes below the fppf precoverage which has isomorphisms and is
stable under composition and base change, the families of a big fppf site's category which lie
in it and whose index type meets the site's covering bound satisfy the site axioms. -/
theorem isSite_covBounded_of_le_fppfPrecoverage (B : BigFppfSite.{u}) (Q : Precoverage Scheme.{u})
    [Precoverage.HasIsos Q] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (hQ : Q ≤ Scheme.fppfPrecoverage) (P : Covering B.Schemes → Prop)
    (hP : ∀ E, P E ↔ (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1)) :
    IsSite (CovBounded P B.coveringBound) := by
  obtain rfl : P = fun E : Covering B.Schemes =>
      (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1) :=
    funext fun E => propext (hP E)
  rw [← chosenCovering_eq_covBounded B Q hQ]
  exact isSite_and_precoverage B.inclusion B.IsCovering Q B.isSite

/-- For a precoverage of schemes below the fppf precoverage, every family of a big fppf
site's category which lies in it is combinatorially equivalent to one chosen by the
site, hence to one whose index type meets the site's covering bound. -/
theorem exists_covBounded_combEquiv_of_le_fppfPrecoverage (B : BigFppfSite.{u})
    (Q : Precoverage Scheme.{u}) (hQ : Q ≤ Scheme.fppfPrecoverage)
    (P : Covering B.Schemes → Prop)
    (hP : ∀ E, P E ↔ (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1))
    (E : Covering B.Schemes) (hE : P E) :
    ∃ E' : Covering B.Schemes, CovBounded P B.coveringBound E' ∧ Covering.CombEquiv E E' := by
  obtain ⟨E', hB, hQ', hCE⟩ := covering_has_representative B Q hQ E ((hP E).mp hE)
  exact ⟨E', ⟨(hP E').mpr hQ', B.card_le_of_isCovering hB⟩, hCE⟩

/-- The site axioms for the families of a big fppf site's category whose image lies in the
precoverage of jointly surjective families of a morphism property `P` below the fppf one. -/
private theorem isSite_covBounded_precoverage (B : BigFppfSite.{u})
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f], P f)
    (hQ : Scheme.precoverage P ≤ Scheme.fppfPrecoverage) (R : Covering B.Schemes → Prop)
    (hR : ∀ E, R E ↔ (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage P (B.inclusion.obj E.1)) :
    IsSite (CovBounded R B.coveringBound) := by
  have := schemePrecoverage_hasIsos P hP
  have := schemePrecoverage_stableUnderComposition P
  have := schemePrecoverage_stableUnderBaseChange P
  exact isSite_covBounded_of_le_fppfPrecoverage B _ hQ R hR

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-! ### The site axioms for the four coarser covering systems -/

/-- The Zariski coverings of a big fppf site's category whose index type meets its covering
bound satisfy the site axioms. -/
@[stacks 03FF "Zariski site axioms"]
theorem isSite_covBounded_isZariskiCovering :
    IsSite (CovBounded (IsZariskiCovering (κ := B.cutoff)) B.coveringBound) :=
  isSite_covBounded_of_le_fppfPrecoverage B Scheme.zariskiPrecoverage
    Scheme.zariskiPrecoverage_le_fppfPrecoverage _ isZariskiCovering_iff_mem_precoverage

/-- The étale coverings of a big fppf site's category whose index type meets its covering
bound satisfy the site axioms. -/
@[stacks 03FF "étale site axioms"]
theorem isSite_covBounded_isEtaleCovering :
    IsSite (CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound) := by
  rw [← chosenCovering_eq_covBounded B Scheme.etalePrecoverage
    Scheme.etalePrecoverage_le_fppfPrecoverage]
  exact etaleCovering_isSite B

/-- The smooth coverings of a big fppf site's category whose index type meets its covering
bound satisfy the site axioms. -/
@[stacks 03FF "smooth site axioms"]
theorem isSite_covBounded_smoothCovering :
    IsSite (CovBounded (SmoothCovering B.cutoff) B.coveringBound) := by
  exact isSite_covBounded_precoverage B (@Smooth : MorphismProperty Scheme.{u})
    (fun _ _ => inferInstance) Scheme.smoothPrecoverage_le_fppfPrecoverage _
    (smoothCovering_iff_mem_precoverage B.cutoff)

/-- The syntomic coverings of a big fppf site's category whose index type meets its covering
bound satisfy the site axioms. -/
@[stacks 03FF "syntomic site axioms"]
theorem isSite_covBounded_syntomicCovering :
    IsSite (CovBounded (SyntomicCovering B.cutoff) B.coveringBound) := by
  exact isSite_covBounded_precoverage B (@Syntomic : MorphismProperty Scheme.{u})
    (fun f _ => syntomic_of_isOpenImmersion f) Scheme.syntomicPrecoverage_le_fppfPrecoverage _
    (syntomicCovering_iff_mem_precoverage B.cutoff)

/-! ### The four coarser sites

Each of the four is assembled from `B`'s own data. The initial schemes are `B`'s, the cutoff and
its three cardinal conditions are `B`'s, the covering bound and the limit ordinal are `B`'s, and
the initial covering families are those of `B`'s which are coverings for the coarser topology.
The two site conditions are the lemmas above. -/

/-- The big Zariski site carried by a chosen big fppf site: the same size-bounded category of
schemes, with the chosen fppf covering families which are Zariski coverings. -/
@[stacks 03FF "the big Zariski site"]
def toBigZariskiSite : BigZariskiSite.{u} where
  initialSchemes := B.initialSchemes
  initialSchemes_small := B.initialSchemes_small
  schemeCardinal := B.cutoff
  aleph0_lt_schemeCardinal := B.aleph0_lt_cutoff
  schemeCardinal_isStrongPrelimit := B.cutoff_isStrongPrelimit
  aleph0_lt_schemeCardinal_cof := B.aleph0_lt_cutoff_cof
  initialSchemes_size_lt := B.initialSchemes_mem
  initialCoverings := {E ∈ B.initialCoverings | IsZariskiCovering E}
  initialCoverings_small := by
    have := B.initialCoverings_small
    exact small_subset fun _ hE => hE.1
  initialCoverings_among_initialSchemes := fun E hE => B.initialCoverings_supported E hE.1
  coveringCardinal := B.coveringBound
  coveringOrdinal := B.coveringOrdinal
  coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
  initialCoverings_mem := fun E hE =>
    ⟨hE.2, B.card_le_of_isCovering (B.initialCoverings_mem E hE.1)⟩
  coverings_isSite := B.isSite_covBounded_isZariskiCovering
  covering_representative :=
    exists_covBounded_combEquiv_of_le_fppfPrecoverage B Scheme.zariskiPrecoverage
      Scheme.zariskiPrecoverage_le_fppfPrecoverage _ isZariskiCovering_iff_mem_precoverage

/-- The big étale site carried by a chosen big fppf site: the same size-bounded category of
schemes, with the chosen fppf covering families which are étale coverings. -/
@[stacks 03FF "the big étale site"]
def toBigEtaleSite : BigEtaleSite.{u} where
  S₀ := B.initialSchemes
  small_S₀ := B.initialSchemes_small
  cutoff := B.cutoff
  aleph0_lt_cutoff := B.aleph0_lt_cutoff
  cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
  aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
  mem_cutoff_of_mem := B.initialSchemes_mem
  initialCoverings := {E ∈ B.initialCoverings | IsEtaleCovering E}
  small_initialCoverings := by
    have := B.initialCoverings_small
    exact small_subset fun _ hE => hE.1
  initial_objects_mem := fun E hE => B.initialCoverings_supported E hE.1
  initialCoverings_etale := fun _ hE => hE.2
  coveringBound := B.coveringBound
  coveringOrdinal := B.coveringOrdinal
  coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
  initialCoverings_bounded := fun E hE =>
    ⟨hE.2, B.card_le_of_isCovering (B.initialCoverings_mem E hE.1)⟩
  coverings_isSite := B.isSite_covBounded_isEtaleCovering
  exists_covering_rep :=
    exists_covBounded_combEquiv_of_le_fppfPrecoverage B Scheme.etalePrecoverage
      Scheme.etalePrecoverage_le_fppfPrecoverage _ fun _ => Iff.rfl

/-- The big smooth site carried by a chosen big fppf site: the same size-bounded category of
schemes, with the chosen fppf covering families which are smooth coverings. -/
@[stacks 03FF "the big smooth site"]
def toBigSmoothSite : BigSmoothSite.{u} where
  initialSchemes := B.initialSchemes
  initialSchemes_small := B.initialSchemes_small
  cutoff := B.cutoff
  aleph0_lt_cutoff := B.aleph0_lt_cutoff
  cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
  aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
  contains_initialScheme := B.initialSchemes_mem
  initialCoverings := {E ∈ B.initialCoverings | SmoothCovering B.cutoff E}
  initialCoverings_small := by
    have := B.initialCoverings_small
    exact small_subset fun _ hE => hE.1
  initialCoverings_smooth := fun _ hE => hE.2
  initialCoverings_among_initialSchemes := fun E hE => B.initialCoverings_supported E hE.1
  coveringBound := B.coveringBound
  coveringOrdinal := B.coveringOrdinal
  coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
  contains_initialCovering := fun E hE =>
    ⟨hE.2, B.card_le_of_isCovering (B.initialCoverings_mem E hE.1)⟩
  covering_isSite := B.isSite_covBounded_smoothCovering
  has_coveringRepresentative :=
    exists_covBounded_combEquiv_of_le_fppfPrecoverage B
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))
      Scheme.smoothPrecoverage_le_fppfPrecoverage _
      (smoothCovering_iff_mem_precoverage B.cutoff)

/-- The big syntomic site carried by a chosen big fppf site: the same size-bounded category of
schemes, with the chosen fppf covering families which are syntomic coverings. -/
@[stacks 03FF "the big syntomic site"]
def toBigSyntomicSite : BigSyntomicSite.{u} where
  initialSchemes := B.initialSchemes
  initialSchemes_small := B.initialSchemes_small
  cutoff := B.cutoff
  aleph0_lt_cutoff := B.aleph0_lt_cutoff
  cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
  aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
  contains_initialScheme := B.initialSchemes_mem
  initialCoverings := {E ∈ B.initialCoverings | SyntomicCovering B.cutoff E}
  initialCoverings_small := by
    have := B.initialCoverings_small
    exact small_subset fun _ hE => hE.1
  initialCoverings_syntomic := fun _ hE => hE.2
  initialCoverings_among_initialSchemes := fun E hE => B.initialCoverings_supported E hE.1
  coveringBound := B.coveringBound
  coveringOrdinal := B.coveringOrdinal
  coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
  contains_initialCovering := fun E hE =>
    ⟨hE.2, B.card_le_of_isCovering (B.initialCoverings_mem E hE.1)⟩
  covering_isSite := B.isSite_covBounded_syntomicCovering
  has_coveringRepresentative :=
    exists_covBounded_combEquiv_of_le_fppfPrecoverage B
      (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}))
      Scheme.syntomicPrecoverage_le_fppfPrecoverage _
      (syntomicCovering_iff_mem_precoverage B.cutoff)

/-! ### The cutoffs, bounds and covering families

The cutoff and covering bound identities hold by `rfl`: the underlying category of each coarser
site is the underlying category of the fppf site, not merely equivalent to it. -/

/-- The big Zariski site of a big fppf site has the same size cutoff. -/
@[simp]
theorem toBigZariskiSite_schemeCardinal : B.toBigZariskiSite.schemeCardinal = B.cutoff := rfl

/-- The big étale site of a big fppf site has the same size cutoff. -/
@[simp]
theorem toBigEtaleSite_cutoff : B.toBigEtaleSite.cutoff = B.cutoff := rfl

/-- The big smooth site of a big fppf site has the same size cutoff. -/
@[simp]
theorem toBigSmoothSite_cutoff : B.toBigSmoothSite.cutoff = B.cutoff := rfl

/-- The big syntomic site of a big fppf site has the same size cutoff. -/
@[simp]
theorem toBigSyntomicSite_cutoff : B.toBigSyntomicSite.cutoff = B.cutoff := rfl

/-- The big Zariski site of a big fppf site has the same covering bound. -/
@[simp]
theorem toBigZariskiSite_coveringCardinal :
    B.toBigZariskiSite.coveringCardinal = B.coveringBound := rfl

/-- The big étale site of a big fppf site has the same covering bound. -/
@[simp]
theorem toBigEtaleSite_coveringBound : B.toBigEtaleSite.coveringBound = B.coveringBound := rfl

/-- The big smooth site of a big fppf site has the same covering bound. -/
@[simp]
theorem toBigSmoothSite_coveringBound : B.toBigSmoothSite.coveringBound = B.coveringBound := rfl

/-- The big syntomic site of a big fppf site has the same covering bound. -/
@[simp]
theorem toBigSyntomicSite_coveringBound :
    B.toBigSyntomicSite.coveringBound = B.coveringBound := rfl

/-- A scheme is contained in the big Zariski site of a big fppf site exactly when it is
contained in the big fppf site. -/
theorem toBigZariskiSite_contains_iff (X : Scheme.{u}) :
    B.toBigZariskiSite.Contains X ↔ B.Contains X := Iff.rfl

/-- A scheme is contained in the big étale site of a big fppf site exactly when it is contained
in the big fppf site. -/
theorem toBigEtaleSite_contains_iff (X : Scheme.{u}) :
    B.toBigEtaleSite.Contains X ↔ B.Contains X := Iff.rfl

/-- A scheme lies below the cutoff of the big smooth site of a big fppf site exactly when it is
contained in the big fppf site. -/
theorem toBigSmoothSite_size_lt_cutoff_iff (X : Scheme.{u}) :
    X.size < B.toBigSmoothSite.cutoff ↔ B.Contains X := Iff.rfl

/-- A scheme is contained in the big syntomic site of a big fppf site exactly when it is
contained in the big fppf site. -/
theorem toBigSyntomicSite_contains_iff (X : Scheme.{u}) :
    B.toBigSyntomicSite.Contains X ↔ B.Contains X := Iff.rfl

/-- The covering families of the big Zariski site carried by a big fppf site are the chosen
Zariski covering families of Stacks 03FF. -/
theorem toBigZariskiSite_isCovering_iff (E : Covering B.Schemes) :
    B.toBigZariskiSite.IsCovering E ↔ B.zariskiCovering E :=
  covBounded_iff_chosenCovering B Scheme.zariskiPrecoverage
    Scheme.zariskiPrecoverage_le_fppfPrecoverage _ isZariskiCovering_iff_mem_precoverage E

/-- The covering families of the big étale site carried by a big fppf site are the chosen étale
covering families of Stacks 03FF. -/
theorem toBigEtaleSite_isCovering_iff (E : Covering B.Schemes) :
    B.toBigEtaleSite.IsCovering E ↔ B.etaleCovering E :=
  covBounded_iff_chosenCovering B Scheme.etalePrecoverage
    Scheme.etalePrecoverage_le_fppfPrecoverage _ (fun _ => Iff.rfl) E

/-- The covering families of the big smooth site carried by a big fppf site are the chosen
smooth covering families of Stacks 03FF. -/
theorem toBigSmoothSite_isCovering_iff (E : Covering B.Schemes) :
    B.toBigSmoothSite.IsCovering E ↔ B.smoothCovering E :=
  covBounded_iff_chosenCovering B
    (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))
    Scheme.smoothPrecoverage_le_fppfPrecoverage _
    (smoothCovering_iff_mem_precoverage B.cutoff) E

/-- The covering families of the big syntomic site carried by a big fppf site are the chosen
syntomic covering families of Stacks 03FF. -/
theorem toBigSyntomicSite_isCovering_iff (E : Covering B.Schemes) :
    B.toBigSyntomicSite.IsCovering E ↔ B.syntomicCovering E :=
  covBounded_iff_chosenCovering B
    (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}))
    Scheme.syntomicPrecoverage_le_fppfPrecoverage _
    (syntomicCovering_iff_mem_precoverage B.cutoff) E

end BigFppfSite

end AlgebraicGeometry

end
