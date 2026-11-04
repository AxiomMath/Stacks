module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverTopologyInstances
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardRefinement

/-!
# Standard coverings as covering sieves of a localized big site

Fix one of the five big sites `B` of a topology `τ` and localize it at a scheme `S` of the
site, giving the site `Over (base B S hS)` with the topology
`AlgebraicGeometry.overTopology`.  This file relates the *standard* `τ`-coverings of
[Stacks, Tag 03X9] — finite families of affines over an affine, of the standard affine form
attached to `τ` — to the covering sieves of that localized site, in both directions, and
uniformly in `τ`.

The two directions are:

* a standard `τ`-covering of the scheme underlying an object `U` lifts to a family in the
  localized site and generates a covering sieve of `U` (its members are below the cutoff of
  `B`, since a standard morphism is locally of finite presentation and quasi-compact, or an
  open immersion);
* every covering sieve of an object with affine total space contains such a lifted standard
  covering, by [Stacks, Tag 03XA].

Together these say that the lifted standard coverings are *cofinal* among the coverings of the
objects with affine total space, which is the hypothesis `hCovCofinal` of the Čech-vanishing
criterion `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`.

## Main definitions

* `AlgebraicGeometry.bigSitePrecoverage`: the precoverage presenting the topology of a big
  site, uniformly in `τ`.
* `AlgebraicGeometry.IsOverStandardCovering`: a family in a localized big site whose
  underlying family of schemes is a standard `τ`-covering of an affine.
* `AlgebraicGeometry.standardOverHypercover`: the family in the localized big site attached to
  a standard `τ`-covering of the scheme underlying an object.
* `AlgebraicGeometry.overToSlice`: the functor from a localized big site into the slice of all
  schemes over `S`.
* `AlgebraicGeometry.overAffineObjects` and `AlgebraicGeometry.overStandardCoverings`: the
  collections `B` and `Cov` of the Čech-vanishing criterion.

## Main results

* `AlgebraicGeometry.siteTopology_eq_toGrothendieck`,
  `AlgebraicGeometry.mem_bigSitePrecoverage_iff` and
  `AlgebraicGeometry.exists_isCovering_refining_sieve`: the uniform-in-`τ` form of the relation
  between a big site's chosen covering families and its covering sieves.  The remaining half of
  that relation, `AlgebraicGeometry.generate_mem_siteTopology`, is proved upstream in
  `StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites`.
* `AlgebraicGeometry.exists_isCovering_presieve₀_eq`: a family of the underlying category of a
  big site whose image in schemes is a `τ`-covering generates the same presieve as one of the
  site's chosen covering families.  This is the uniform form of [Stacks, Tag 03WV],
  [Stacks, Tag 03WW] and [Stacks, Tag 03WX];
  `AlgebraicGeometry.mem_precoverage_of_isCovering` is its converse.
* `AlgebraicGeometry.size_lt_cutoff_of_isStandardCovering`: the members of a standard
  `τ`-covering of an object of a big site are again objects of that big site.
* `AlgebraicGeometry.overTopology_eq_siteTopology_over`,
  `AlgebraicGeometry.mem_overTopology_iff` and
  `AlgebraicGeometry.sieve₀_mem_overTopology_iff`: the topology of a localized big site is the
  localization of the topology of the big site, so its covering sieves are detected on the
  underlying schemes.
* `AlgebraicGeometry.IsOverStandardCovering.sieve₀_mem_overTopology`: **the bridge** — a lifted
  standard `τ`-covering generates a covering sieve of the localized big site.
* `AlgebraicGeometry.exists_isOverStandardCovering_sieve₀_le` and
  `AlgebraicGeometry.overStandardCoverings_cofinal`: **the cofinality statement** — every
  covering sieve of an object with affine total space contains a lifted standard `τ`-covering.
  The second is the hypothesis `hCovCofinal` of the Čech-vanishing criterion verbatim.
* `AlgebraicGeometry.overStandardCoverings_hasProducts` and
  `AlgebraicGeometry.overStandardCoverings_hasImageProducts`: the hypotheses `hProducts` and
  `hImageProducts` of that criterion, both of them condition (2) of Sites, Definition 00WV for
  the selected coverings.
* `AlgebraicGeometry.mem_overAffineObjects_of_mem_overStandardCoverings`: the first two clauses
  of its hypothesis `hCovObjects`.

## Implementation notes

No `@[stacks]` attribute is attached to anything here.  The two mathematical inputs are
[Stacks, Tag 03XA] (`AlgebraicGeometry.exists_standardCovering_refinement`, already in the
library) and the per-topology statements that a `τ`-covering of an object of a big site has a
combinatorially equivalent chosen representative, which are structure fields of the five big
sites; what this file adds is their uniform-in-`τ` packaging and the transport to the
localization, neither of which is the content of a tag.

**What is not here.**  Of the hypotheses of the Čech-vanishing criterion, the third clause of
`hCovObjects` — that the iterated fibre products of a selected covering again have affine total
space — is *not* proved in this file, and neither is the Čech-vanishing hypothesis `hCech`
itself.  Nothing below assumes either of them: every statement in this file is unconditional.

Instance search cannot see through the `AlgebraicGeometry.overTopology` dispatch, which is why
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/OverTopologyInstances.lean` exists; for the
same reason every statement below that mentions a per-topology notion is proved by an explicit
five-way `cases τ` rather than by unfolding.

The chosen covering families of a big site are indexed in `Type (u + 1)`, while the
covering-index universe of the Čech-vanishing criterion is `Type u`.  Combinatorial
equivalence of [Stacks, Tag 00VU] (1) is universe-polymorphic in the two index types and
implies equality of the generated presieves, so a `Type u`-indexed family is compared with a
`Type (u + 1)`-indexed representative directly, with no reindexing lemma in between; the
`ULift` of the index type is what crosses the gap.

## References

* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 03WV](https://stacks.math.columbia.edu/tag/03WV)
* [Stacks Project, Tag 03WW](https://stacks.math.columbia.edu/tag/03WW)
* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
* [Stacks Project, Tag 00VU](https://stacks.math.columbia.edu/tag/00VU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### The chosen covering families of a big site, uniformly in the topology -/

section SiteTopology

variable (τ : CoveringTopology) (B : BigSite.{u} τ)

/-- The precoverage presenting the topology of a big site: its members are the presieves of the
site's own chosen covering families.  This is the uniform-in-`τ` form of the five
`precoverage` definitions. -/
public def bigSitePrecoverage : (τ : CoveringTopology) → (B : BigSite.{u} τ) →
    Precoverage (siteCategory B)
  | .zariski, B => B.precoverage
  | .etale, B => B.precoverage
  | .smooth, B => B.precoverage
  | .syntomic, B => B.precoverage
  | .fppf, B => B.precoverage

/-- The topology of a big site is generated by the presieves of its chosen covering
families. -/
public theorem siteTopology_eq_toGrothendieck :
    siteTopology τ B = (bigSitePrecoverage τ B).toGrothendieck := by
  cases τ <;> rfl

/-- A presieve belongs to the precoverage of a big site exactly when it is the presieve of one
of the site's chosen covering families. -/
public theorem mem_bigSitePrecoverage_iff {X : siteCategory B} {R : Presieve X} :
    R ∈ bigSitePrecoverage τ B X ↔
      ∃ E : PreZeroHypercover X, isCovering τ B ⟨X, E⟩ ∧ R = E.presieve₀ := by
  cases τ with
  | zariski => rfl
  | smooth => rfl
  | etale | syntomic | fppf =>
      constructor <;> rintro ⟨E, h₁, h₂⟩ <;> exact ⟨E, h₂, h₁⟩

/-- The chosen covering families of a big site satisfy the site axioms. -/
public alias isSite_isCovering := siteCoverings_isSite

/-- A covering sieve of a big site contains one of the site's own chosen covering families. -/
public theorem exists_isCovering_refining_sieve {X : siteCategory B} {R : Sieve X}
    (hR : R ∈ siteTopology τ B X) :
    ∃ E : PreZeroHypercover X, isCovering τ B ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [siteTopology_eq_toGrothendieck] at hR
  exact CategoryTheory.exists_covering_refining_sieve (isCovering τ B)
    (bigSitePrecoverage τ B) (fun h => (mem_bigSitePrecoverage_iff τ B).mp h)
    (isSite_isCovering τ B) hR

/-- A family of the underlying category of a big site whose image in schemes is a `τ`-covering
is combinatorially equivalent to one of the site's chosen covering families, and in particular
generates the same presieve.  This is the uniform-in-`τ` form of the per-topology statements
that every `τ`-covering has a chosen representative, which are structure fields of the five
big sites. -/
public theorem exists_isCovering_presieve₀_eq_aux {X : siteCategory B}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) X.obj) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      isCovering τ B ⟨X, F⟩ ∧ E.presieve₀ = F.presieve₀ := by
  suffices ∃ G : Covering (siteCategory B), isCovering τ B G ∧ Covering.CombEquiv ⟨X, E⟩ G by
    obtain ⟨⟨X', F⟩, hF, hX', hcomb⟩ := this
    cases hX'
    exact ⟨F, hF, PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb⟩
  cases τ with
  | zariski => exact B.covering_representative ⟨X, E⟩ hE
  | etale => exact B.exists_covering_rep ⟨X, E⟩ hE
  | smooth => exact B.has_coveringRepresentative ⟨X, E⟩ hE
  | syntomic =>
      exact B.has_coveringRepresentative ⟨X, E⟩ (isSyntomicCovering_iff_mem_precoverage.mpr hE)
  | fppf =>
      rw [PreZeroHypercover.presieve₀_map] at hE
      exact B.fppf_has_representative ⟨X, E⟩ hE

/-- `AlgebraicGeometry.exists_isCovering_presieve₀_eq_aux` for a family indexed one universe
lower, which is the indexing of the Čech-vanishing criterion. -/
public theorem exists_isCovering_presieve₀_eq {X : siteCategory B}
    (E : PreZeroHypercover.{u} X)
    (hE : (E.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) X.obj) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      isCovering τ B ⟨X, F⟩ ∧ E.presieve₀ = F.presieve₀ := by
  let E' : PreZeroHypercover.{u + 1} X :=
    { I₀ := ULift.{u + 1} E.I₀, X := fun i => E.X i.down, f := fun i => E.f i.down }
  have hcomb : PreZeroHypercover.CombinatoriallyEquivalent E E' :=
    ⟨⟨ULift.up, fun i => rfl, fun i => by simp [E']⟩,
      ⟨ULift.down, fun j => rfl, fun j => by simp [E']⟩⟩
  have hpre : E.presieve₀ = E'.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  obtain ⟨F, hF, hFeq⟩ := exists_isCovering_presieve₀_eq_aux τ B E' (by
    rw [PreZeroHypercover.presieve₀_map, ← hpre, ← PreZeroHypercover.presieve₀_map]
    exact hE)
  exact ⟨F, hF, hpre.trans hFeq⟩

/-- A chosen covering family of a big site is a `τ`-covering of schemes. -/
public theorem mem_precoverage_of_isCovering {X : siteCategory B}
    (E : PreZeroHypercover.{u + 1} X) (hE : isCovering τ B ⟨X, E⟩) :
    (E.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) X.obj := by
  cases τ with
  | zariski => exact hE.1
  | etale => exact hE.1
  | smooth => exact hE.1
  | syntomic => exact isSyntomicCovering_iff_mem_precoverage.mp hE.1
  | fppf =>
      have h : E.presieve₀.map (schemeBelowInclusion (cutoff CoveringTopology.fppf B)) ∈
          Scheme.fppfPrecoverage
            ((schemeBelowInclusion (cutoff CoveringTopology.fppf B)).obj X) := hE.1
      rw [PreZeroHypercover.presieve₀_map]
      exact h

end SiteTopology

/-! ### Size bounds inside a big site -/

section Size

variable (τ : CoveringTopology) (B : BigSite.{u} τ)

/-- The cutoff of a big site is uncountable. -/
public theorem aleph0_lt_cutoff' : Cardinal.aleph0 < cutoff τ B := by
  cases τ with
  | zariski => exact B.aleph0_lt_schemeCardinal
  | etale => exact B.aleph0_lt_cutoff
  | smooth => exact B.aleph0_lt_cutoff
  | syntomic => exact B.aleph0_lt_cutoff
  | fppf => exact B.aleph0_lt_cutoff

/-- The cutoff of a big site is a strong prelimit cardinal. -/
public theorem cutoff_isStrongPrelimit : Cardinal.IsStrongPrelimit (cutoff τ B) := by
  cases τ with
  | zariski => exact B.schemeCardinal_isStrongPrelimit
  | etale => exact B.cutoff_isStrongPrelimit
  | smooth => exact B.cutoff_isStrongPrelimit
  | syntomic => exact B.cutoff_isStrongPrelimit
  | fppf => exact B.cutoff_isStrongPrelimit

/-- An affine scheme locally of finite type over an object of a big site is again an object of
the big site: it is covered by the single affine open `⊤`, so
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_affineCover` applies with a
one-element index type. -/
public theorem size_lt_cutoff_of_isAffine_of_locallyOfFiniteType {X : Scheme.{u}} [IsAffine X]
    {Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (hY : Y.size < cutoff τ B) :
    X.size < cutoff τ B := by
  have hcov : (⨆ _ : ULift.{u} Unit, (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens).1) = ⊤ := by
    ext x; simp
  have hI : Cardinal.mk (ULift.{u} Unit) ≤ Y.size ^ Cardinal.aleph0 :=
    calc
      Cardinal.mk (ULift.{u} Unit) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ Y.size := Scheme.aleph0_le_size _
      _ ≤ Y.size ^ Cardinal.aleph0 := Cardinal.self_le_power _ (by simp)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover (aleph0_lt_cutoff' τ B)
    (cutoff_isStrongPrelimit τ B) f (fun _ => ⟨⊤, isAffineOpen_top X⟩) hcov hI hY

/-- A member of a standard `τ`-covering of an object of a big site is again an object of the
big site.  For the four topologies other than Zariski the member is affine and locally of
finite type over the target, and for the Zariski topology it is an open subscheme of it. -/
public theorem size_lt_cutoff_of_isStandardCovering {T : Scheme.{u}} [IsAffine T]
    {I : Type*} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering τ U f)
    (hT : T.size < cutoff τ B) (i : I) : (U i).size < cutoff τ B := by
  have hU : IsAffine (U i) := h.affine_source i
  have hprop : coveringMorphismProperty τ (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (coveringMorphismProperty τ)).mp
      (h.ofArrows_mem_precoverage τ U f)).2 i
  cases τ with
  | zariski => exact Scheme.size_lt_of_isOpenImmersion (f i) hT
  | fppf =>
      let : Flat (f i) := hprop.1
      let : LocallyOfFinitePresentation (f i) := hprop.2
      let : LocallyOfFiniteType (f i) := inferInstance
      exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .fppf B (f i) hT
  | syntomic =>
      let : LocallyOfFinitePresentation (f i) := locallyOfFinitePresentation hprop
      let : LocallyOfFiniteType (f i) := inferInstance
      exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .syntomic B (f i) hT
  | smooth =>
      let : Smooth (f i) := hprop
      let : LocallyOfFiniteType (f i) := inferInstance
      exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .smooth B (f i) hT
  | etale =>
      let : Etale (f i) := hprop
      let : LocallyOfFiniteType (f i) := inferInstance
      exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .etale B (f i) hT

end Size

/-! ### Covering sieves of a localized big site -/

section Localized

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- The topology of a localized big site is the localization of the topology of the big
site. -/
public theorem overTopology_eq_siteTopology_over :
    overTopology τ B S hS = (siteTopology τ B).over (base B S hS) := by
  cases τ with
  | zariski => exact BigZariskiOver.topology_eq_over B ⟨S, hS⟩
  | etale => exact bigEtaleOver_topology_eq B S hS
  | smooth => rfl
  | syntomic => rfl
  | fppf => rfl

/-- A sieve is a covering sieve of a localized big site exactly when the sieve it induces on
the underlying scheme is a covering sieve of the big site. -/
public theorem mem_overTopology_iff {U : Over (base B S hS)} (R : Sieve U) :
    R ∈ overTopology τ B S hS U ↔ Sieve.overEquiv U R ∈ siteTopology τ B U.left := by
  rw [overTopology_eq_siteTopology_over]
  exact GrothendieckTopology.mem_over_iff _ R

/-- A family in a localized big site generates a covering sieve exactly when the family it
induces in the big site does. -/
public theorem sieve₀_mem_overTopology_iff {U : Over (base B S hS)}
    (E : PreZeroHypercover.{v} U) :
    E.sieve₀ ∈ overTopology τ B S hS U ↔
      (E.map (Over.forget (base B S hS))).sieve₀ ∈ siteTopology τ B U.left := by
  rw [mem_overTopology_iff, Sieve.overEquiv_ofArrows]
  exact Iff.rfl

/-! ### Standard coverings in a localized big site -/

/-- A family in a localized big site is an *over-standard* `τ`-covering when its target has
affine total space and the family of schemes underlying it is a standard `τ`-covering of that
total space. -/
public def IsOverStandardCovering {U : Over (base B S hS)} (E : PreZeroHypercover.{v} U) :
    Prop :=
  ∃ h : IsAffine (overScheme τ B S hS U),
    @IsStandardCovering τ (overScheme τ B S hS U) h E.I₀
      (fun i => overScheme τ B S hS (E.X i))
      (fun i => (schemeBelowInclusion (cutoff τ B)).map (E.f i).left)

/-- The target of an over-standard `τ`-covering, and each of its members, has affine total
space. -/
public theorem IsOverStandardCovering.isAffine {U : Over (base B S hS)}
    {E : PreZeroHypercover.{v} U} (h : IsOverStandardCovering τ B S hS E) :
    IsAffine (overScheme τ B S hS U) ∧
      ∀ i, IsAffine (overScheme τ B S hS (E.X i)) := by
  obtain ⟨hT, hstd⟩ := h
  let := hT
  exact ⟨hT, hstd.affine_source⟩

/-- An over-standard `τ`-covering has finitely many members. -/
public theorem IsOverStandardCovering.finite {U : Over (base B S hS)}
    {E : PreZeroHypercover.{v} U} (h : IsOverStandardCovering τ B S hS E) : Finite E.I₀ := by
  obtain ⟨hT, hstd⟩ := h
  let := hT
  exact hstd.finite_index

/-- **The bridge from standard coverings to covering sieves.** An over-standard `τ`-covering
of an object of a localized big site generates a covering sieve of that object.

Its members are `τ`-covering morphisms of schemes, so the family it induces in the big site is
a `τ`-covering there and hence has, by
`AlgebraicGeometry.exists_isCovering_presieve₀_eq`, the same presieve as one of the site's
chosen covering families. -/
public theorem IsOverStandardCovering.sieve₀_mem_overTopology {U : Over (base B S hS)}
    (E : PreZeroHypercover.{u} U) (h : IsOverStandardCovering τ B S hS E) :
    E.sieve₀ ∈ overTopology τ B S hS U := by
  obtain ⟨hU, hstd⟩ := h
  rw [sieve₀_mem_overTopology_iff]
  obtain ⟨F, hF, hFeq⟩ :=
    exists_isCovering_presieve₀_eq τ B (E.map (Over.forget (base B S hS)))
      (hstd.ofArrows_mem_precoverage τ _ _)
  have hgen := generate_mem_siteTopology τ B F hF
  rw [← hFeq] at hgen
  exact hgen

/-- The family in a localized big site attached to a standard `τ`-covering of the scheme
underlying an object.  Each member of the covering is below the cutoff of the big site — being
affine and locally of finite type over the target, or an open subscheme of it — so it is an
object of the site, and the covering morphisms are morphisms over the object. -/
public def standardOverHypercover {U : Over (base B S hS)}
    [IsAffine (overScheme τ B S hS U)] {I : Type u} {V : I → Scheme.{u}}
    {g : ∀ i, V i ⟶ overScheme τ B S hS U} (hg : IsStandardCovering τ V g) :
    PreZeroHypercover.{u} U where
  I₀ := I
  X i := Over.mk ((ObjectProperty.homMk (g i) :
    (⟨V i, size_lt_cutoff_of_isStandardCovering τ B hg U.left.property i⟩ :
      siteCategory B) ⟶ U.left) ≫ U.hom)
  f i := Over.homMk (ObjectProperty.homMk (g i)) (by simp)

/-- The family attached to a standard `τ`-covering is an over-standard `τ`-covering. -/
public theorem isOverStandardCovering_standardOverHypercover {U : Over (base B S hS)}
    [IsAffine (overScheme τ B S hS U)] {I : Type u} {V : I → Scheme.{u}}
    {g : ∀ i, V i ⟶ overScheme τ B S hS U} (hg : IsStandardCovering τ V g) :
    IsOverStandardCovering τ B S hS (standardOverHypercover τ B S hS hg) :=
  ⟨inferInstance, hg⟩

/-- **Cofinality of the standard coverings.**  Every covering sieve of an object of a localized
big site with affine total space contains an over-standard `τ`-covering.

This is [Stacks, Tag 03XA] transported to the localized site: a covering sieve contains one of
the site's chosen covering families, which pushes down to a `τ`-covering of the underlying
affine scheme; that is refined by a standard covering, whose members are again objects of the
site. -/
public theorem exists_isOverStandardCovering_sieve₀_le {U : Over (base B S hS)}
    (hU : IsAffine (overScheme τ B S hS U)) {R : Sieve U}
    (hR : R ∈ overTopology τ B S hS U) :
    ∃ E : PreZeroHypercover.{u} U,
      IsOverStandardCovering τ B S hS E ∧ E.sieve₀ ≤ R := by
  classical
  let := hU
  let : IsAffine ((schemeBelowInclusion (cutoff τ B)).obj U.left) := hU
  rw [mem_overTopology_iff] at hR
  obtain ⟨V, hV, hVR⟩ := exists_isCovering_refining_sieve τ B hR
  obtain ⟨W, r, hW⟩ := exists_standardCovering_refinement τ
    (V.map (schemeBelowInclusion (cutoff τ B))) (mem_precoverage_of_isCovering τ B V hV)
  let := hW.finite_index
  let : Fintype W.I₀ := Fintype.ofFinite W.I₀
  let e : W.I₀ ≃ Fin (Fintype.card W.I₀) := Fintype.equivFin W.I₀
  let ix : ULift.{u} (Fin (Fintype.card W.I₀)) → W.I₀ := fun i => e.symm i.down
  have hW' : IsStandardCovering τ (fun i => W.X (ix i)) (fun i => W.f (ix i)) := by
    refine ⟨inferInstance, fun i => hW.affine_source (ix i), ?_,
      fun i => by cases τ <;> exact hW.standard (ix i)⟩
    refine Set.iUnion_eq_univ_iff.mpr fun x => ?_
    have hx : x ∈ ⋃ i, Set.range (W.f i) := by rw [hW.jointly_surjective]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine ⟨ULift.up (e i), ?_⟩
    rw [show ix (ULift.up (e i)) = i from e.symm_apply_apply i]
    exact hi
  refine ⟨standardOverHypercover τ B S hS hW',
    isOverStandardCovering_standardOverHypercover τ B S hS hW', ?_⟩
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
    Presieve.ofArrows_le_iff]
  intro i
  let j : V.I₀ := r.s₀ (ix i)
  let Xi : siteCategory B :=
    ⟨W.X (ix i), size_lt_cutoff_of_isStandardCovering τ B hW' U.left.property i⟩
  let a : Xi ⟶ V.X j := ObjectProperty.homMk (X := Xi) (Y := V.X j) (r.h₀ (ix i))
  let b : Xi ⟶ U.left := ObjectProperty.homMk (X := Xi) (Y := U.left) (W.f (ix i))
  have hfac : a ≫ V.f j = b := by
    apply ObjectProperty.hom_ext
    exact r.w₀ (ix i)
  exact (Sieve.overEquiv_iff R b).mp
    (hfac ▸ (Sieve.overEquiv U R).downward_closed (hVR _ _ (V.presieve₀_f j)) a)

/-! ### The data of the Čech-vanishing criterion -/

/-- The objects of a localized big site with affine total space: the collection `B` of
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`. -/
public def overAffineObjects : Set (Over (base B S hS)) :=
  {U | IsAffine (overScheme τ B S hS U)}

/-- Membership in `AlgebraicGeometry.overAffineObjects` is the affineness predicate
`AlgebraicGeometry.overIsAffine` of the localized big site. -/
public theorem mem_overAffineObjects_iff (U : Over (base B S hS)) :
    U ∈ overAffineObjects τ B S hS ↔ overIsAffine τ B S hS U :=
  (overIsAffine_iff τ B S hS U).symm

/-- The over-standard `τ`-coverings of an object of a localized big site: the collection `Cov`
of `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`. -/
public def overStandardCoverings (U : Over (base B S hS)) :
    Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U } :=
  {E | IsOverStandardCovering τ B S hS E.1}

/-- The target of an over-standard `τ`-covering, and each of its members, is an object with
affine total space.  These are the first two clauses of the hypothesis `hCovObjects` of
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`. -/
public theorem mem_overAffineObjects_of_mem_overStandardCoverings (U : Over (base B S hS))
    (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U })
    (hE : E ∈ overStandardCoverings τ B S hS U) :
    U ∈ overAffineObjects τ B S hS ∧
      ∀ i, E.1.X i ∈ overAffineObjects τ B S hS :=
  IsOverStandardCovering.isAffine τ B S hS hE

/-- The underlying category of a big site has finite wide pullbacks: it has finite limits by
[Stacks, Tag 022K]. -/
public instance hasFiniteWidePullbacks_siteCategory :
    HasFiniteWidePullbacks (siteCategory B) :=
  hasFiniteWidePullbacks_of_hasFiniteLimits _

/-- A localized big site has finite wide pullbacks, so each of its slices has finite limits.
This is what makes the iterated fibre products of a covering exist. -/
public instance hasFiniteWidePullbacks_overBase :
    HasFiniteWidePullbacks (Over (base B S hS)) :=
  hasFiniteWidePullbacks_of_hasFiniteLimits _

/-- The functor from a localized big site into the slice of *all* schemes over `S`: an object
below the cutoff of the big site, over `S`, regarded as an arbitrary scheme over `S`.  This is
the functor along which the Čech-vanishing criterion is transferred and along which the
associated module `Fᵃ` of [Stacks, Tag 03OG] is restricted. -/
public abbrev overToSlice : Over (base B S hS) ⥤ Over S :=
  Over.post (schemeBelowInclusion (cutoff τ B))

/-- **`hProducts` for a localized big site.**  The iterated fibre products of a covering of an
object of a localized big site exist, because the slice of the site at that object has finite
limits.  This is one half of condition (2) of Sites, Definition 00WV for the selected
coverings. -/
public theorem overStandardCoverings_hasProducts :
    ∀ {U : Over (base B S hS)}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U }),
      E ∈ overStandardCoverings τ B S hS U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
  fun _ _ _ _ => inferInstance

/-- **`hImageProducts` for a localized big site.**  The iterated fibre products of the image
under `AlgebraicGeometry.overToSlice` of a covering exist, because the slice of `Over S` at the
image object has finite limits.  This is the other half of condition (2) of Sites, Definition
00WV for the selected coverings. -/
public theorem overStandardCoverings_hasImageProducts :
    ∀ {U : Over (base B S hS)}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U }),
      E ∈ overStandardCoverings τ B S hS U → ∀ (p : ℕ)
        (i : Fin (p + 1) → (E.1.map (overToSlice τ B S hS)).I₀),
        HasProduct (fun a ↦ Over.mk ((E.1.map (overToSlice τ B S hS)).f (i a))) :=
  fun _ _ _ _ => inferInstance

/-- **`hCovCofinal` for a localized big site.**  The over-standard `τ`-coverings are cofinal
among the covering sieves of the objects with affine total space, in exactly the shape the
Čech-vanishing criterion
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` takes it. -/
public theorem overStandardCoverings_cofinal :
    ∀ U ∈ overAffineObjects τ B S hS, ∀ R ∈ overTopology τ B S hS U,
      ∃ E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U },
        E ∈ overStandardCoverings τ B S hS U ∧ E.1.sieve₀ ≤ R := by
  intro U hU R hR
  obtain ⟨E, hEstd, hER⟩ := exists_isOverStandardCovering_sieve₀_le τ B S hS hU hR
  exact ⟨⟨E, IsOverStandardCovering.sieve₀_mem_overTopology τ B S hS E hEstd⟩, hEstd, hER⟩

end Localized

end AlgebraicGeometry
