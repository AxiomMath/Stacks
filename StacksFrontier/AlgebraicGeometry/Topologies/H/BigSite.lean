module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.H.StandardCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Big h sites

A big h site is a size-bounded full subcategory of schemes together with a chosen, set-sized
system of h covering families on it.  The system contains prescribed initial schemes and
coverings, satisfies the site axioms, and contains a combinatorial representative of every h
covering.  For such a site containing a scheme `S`, the big h category over `S` is the slice
over `S`, and the big affine h category is its full subcategory on objects with affine
underlying scheme; the covering families of the latter are the standard h coverings which
cover in the big h site over `S`.

## Main definitions

* `AlgebraicGeometry.IsHCoveringInCutoff`: recognizes h coverings in a cutoff category.
* `AlgebraicGeometry.BigHSite`: packages the choices defining a big h site.
* `AlgebraicGeometry.BigHOver` and `AlgebraicGeometry.BigAffineH`: the big h category over
  `S` and its affine full subcategory, with their covering families and topologies.

## Main results

The projections and elementary API of `AlgebraicGeometry.BigHSite` expose the initial
containment, the site axioms and the combinatorial cofinality of its chosen covering
families.

## Implementation notes

Following Stacks 000J, the ambient category is `AlgebraicGeometry.SchemeBelow`, the full
subcategory of schemes of size below the cutoff; a family there is h covering when its image
under the canonical inclusion is one in the sense of Stacks 0ETS.  As in Stacks 000X the
chosen families are those with index cardinality at most `coveringBound`, and the limit
ordinal records the remaining choice in that construction.  The generated Grothendieck
topology is kept separate from the chosen family-level coverings, so that both the site
axioms and Mathlib's sheaf interface are directly available.  Unlike the big affine ph site,
the affine families here are cut out by the standard h condition of Stacks 0EUY rather than
by finiteness of the index type.

## References

* [Stacks Project, Tag 0ETZ](https://stacks.math.columbia.edu/tag/0ETZ)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A family in a size-bounded full category of schemes is h covering if its image in all
schemes is an h covering. -/
public abbrev IsHCoveringInCutoff {κ : Cardinal.{u}}
    (𝒰 : Covering.{u + 1, u, u + 1} (AlgebraicGeometry.SchemeBelow κ)) : Prop :=
  let 𝒱 := 𝒰.2.map (AlgebraicGeometry.schemeBelowInclusion κ)
  IsHCovering 𝒱.X 𝒱.f

/-- **Stacks 0ETZ.** A big h site consists of an initial set of schemes and initial h
coverings, a sufficiently large cutoff category containing them, and a bounded collection of
h coverings satisfying the site axioms and representing every h covering. -/
@[stacks 0ETZ]
public structure BigHSite where
  /-- The initially chosen set of schemes. -/
  initialSchemes : Set Scheme.{u}
  /-- The initial set is small in the universe in which sizes are measured. -/
  initialSchemes_small : Small.{u} initialSchemes
  /-- The cardinal cutoff defining the underlying category. -/
  cutoff : Cardinal.{u}
  /-- The cutoff is uncountable. -/
  aleph0_lt_cutoff : ℵ₀ < cutoff
  /-- The cutoff is a strong prelimit cardinal. -/
  cutoff_isStrongPrelimit : cutoff.IsStrongPrelimit
  /-- The cutoff has uncountable cofinality. -/
  aleph0_lt_cutoff_cof : ℵ₀ < cutoff.ord.cof
  /-- Every initially chosen scheme is in the cutoff category. -/
  initialSchemes_mem : ∀ X ∈ initialSchemes, X.size < cutoff
  /-- The initially chosen h covering families among the initial schemes. -/
  initialCoverings : Set (Covering (AlgebraicGeometry.SchemeBelow cutoff))
  /-- The initial collection of coverings is small. -/
  initialCoverings_small : Small.{u + 1} initialCoverings
  /-- Every scheme appearing in an initial covering belongs to the initial set. -/
  initialCoverings_supported : ∀ 𝒰 ∈ initialCoverings,
    𝒰.1.1 ∈ initialSchemes ∧ ∀ i, (𝒰.2.X i).1 ∈ initialSchemes
  /-- The cardinal bounding the index types of chosen coverings. -/
  coveringBound : Cardinal.{u + 1}
  /-- The limit ordinal from the set-sized covering construction. -/
  coveringOrdinal : Ordinal.{u + 1}
  /-- The chosen covering ordinal is a successor limit. -/
  coveringOrdinal_isSuccLimit : Order.IsSuccLimit coveringOrdinal
  /-- Every initially chosen family is among the bounded h coverings. -/
  initialCoverings_mem : ∀ 𝒰 ∈ initialCoverings,
    CovBounded (IsHCoveringInCutoff (κ := cutoff)) coveringBound 𝒰
  /-- The bounded h covering families satisfy the site axioms. -/
  coverings_isSite :
    IsSite (CovBounded (IsHCoveringInCutoff (κ := cutoff)) coveringBound)
  /-- Every h covering has a combinatorially equivalent chosen representative. -/
  covering_representative :
    ∀ 𝒰 : Covering (AlgebraicGeometry.SchemeBelow cutoff),
      IsHCoveringInCutoff 𝒰 →
      ∃ 𝒱 : Covering (AlgebraicGeometry.SchemeBelow cutoff),
        CovBounded IsHCoveringInCutoff coveringBound 𝒱 ∧ Covering.CombEquiv 𝒰 𝒱

namespace BigHSite

/-- The stored smallness of the initial schemes is available to typeclass inference. -/
public instance (B : BigHSite.{u}) : Small.{u} B.initialSchemes := B.initialSchemes_small

/-- The stored smallness of the initial coverings is available to typeclass inference. -/
public instance (B : BigHSite.{u}) : Small.{u + 1} B.initialCoverings :=
  B.initialCoverings_small

/-- The underlying category of a big h site. -/
public abbrev Schemes (B : BigHSite.{u}) :=
  AlgebraicGeometry.SchemeBelow B.cutoff

/-- The canonical inclusion of a big h site into all schemes. -/
public abbrev inclusion (B : BigHSite.{u}) : B.Schemes ⥤ Scheme.{u} :=
  AlgebraicGeometry.schemeBelowInclusion B.cutoff

/-- A scheme lies in a big h site precisely when it is below the site's cutoff. -/
public abbrev Contains (B : BigHSite.{u}) (X : Scheme.{u}) : Prop := X.size < B.cutoff

/-- A scheme contained in a big h site, regarded as an object of its category. -/
public abbrev obj (B : BigHSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) : B.Schemes :=
  ⟨X, hX⟩

/-- The chosen covering families of a big h site. -/
public abbrev IsCovering (B : BigHSite.{u}) : Covering B.Schemes → Prop :=
  CovBounded IsHCoveringInCutoff B.coveringBound

/-- The precoverage represented by the chosen family-level h coverings. -/
public def precoverage (B : BigHSite.{u}) : Precoverage B.Schemes where
  coverings X := {R | ∃ 𝒰 : PreZeroHypercover.{u + 1} X,
    R = 𝒰.presieve₀ ∧ B.IsCovering ⟨X, 𝒰⟩}

/-- Membership in the precoverage is witnessed by one of the site's chosen families. -/
public theorem mem_precoverage_iff (B : BigHSite.{u}) {X : B.Schemes} {R : Presieve X} :
    R ∈ B.precoverage X ↔ ∃ 𝒰 : PreZeroHypercover.{u + 1} X,
      R = 𝒰.presieve₀ ∧ B.IsCovering ⟨X, 𝒰⟩ :=
  Iff.rfl

/-- The Grothendieck topology generated by the chosen h coverings. -/
public abbrev topology (B : BigHSite.{u}) : GrothendieckTopology B.Schemes :=
  B.precoverage.toGrothendieck

/-- A chosen covering family is an h covering. -/
public theorem IsCovering.h {B : BigHSite.{u}} {𝒰 : Covering B.Schemes}
    (h𝒰 : B.IsCovering 𝒰) : IsHCoveringInCutoff 𝒰 := h𝒰.1

/-- The index type of a chosen covering is within the site's bound. -/
public theorem IsCovering.mk_le {B : BigHSite.{u}} {𝒰 : Covering B.Schemes}
    (h𝒰 : B.IsCovering 𝒰) : #𝒰.2.I₀ ≤ B.coveringBound := h𝒰.2

/-- Every prescribed initial covering is an h covering. -/
public theorem initialCoverings_h (B : BigHSite.{u}) {𝒰 : Covering B.Schemes}
    (h𝒰 : 𝒰 ∈ B.initialCoverings) : IsHCoveringInCutoff 𝒰 :=
  (B.initialCoverings_mem 𝒰 h𝒰).1

/-- The chosen h covering families satisfy the site axioms. -/
public theorem isSite (B : BigHSite.{u}) : IsSite B.IsCovering := B.coverings_isSite

end BigHSite

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EU1, part (1).** The big h category of `S` is the slice of the chosen big h
category over its object `S`. -/
@[stacks 0EU1 "part (1), category"]
public abbrev BigHOver := Over (B.obj S hS)

namespace BigHOver

/-- Forget the structure morphism to `S`. -/
public abbrev forget : BigHOver B S hS ⥤ B.Schemes :=
  Over.forget (B.obj S hS)

/-- The canonical functor from the big h category over `S` to schemes. -/
public abbrev toScheme : BigHOver B S hS ⥤ Scheme.{u} :=
  forget B S hS ⋙ B.inclusion

/-- **Stacks 0EU1, part (1).** A family in the slice covers precisely when its underlying
family covers in the chosen big h site. -/
@[stacks 0EU1 "part (1), coverings"]
public abbrev IsCovering (E : Covering (BigHOver B S hS)) : Prop :=
  B.IsCovering ⟨(forget B S hS).obj E.1, E.2.map (forget B S hS)⟩

/-- The canonical localization of the big h site's topology at `S`. -/
public abbrev topology : GrothendieckTopology (BigHOver B S hS) :=
  B.topology.over (B.obj S hS)

/-- An object of the big h category over `S` has affine underlying scheme. -/
public abbrev IsAffineOver : ObjectProperty (BigHOver B S hS) :=
  fun X ↦ IsAffine ((toScheme B S hS).obj X)

end BigHOver

/-- **Stacks 0EU1, part (2).** The big affine h category is the full subcategory of affine
objects in the big h category over `S`. -/
@[stacks 0EU1 "part (2), category"]
public abbrev BigAffineH := (BigHOver.IsAffineOver B S hS).FullSubcategory

namespace BigAffineH

/-- The canonical full embedding into the big h category over `S`. -/
public abbrev inclusion : BigAffineH B S hS ⥤ BigHOver B S hS :=
  (BigHOver.IsAffineOver B S hS).ι

/-- The underlying scheme functor of the big affine h category. -/
public abbrev toScheme : BigAffineH B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ BigHOver.toScheme B S hS

/-- The underlying scheme of a big affine h object is affine. -/
public instance isAffine_toScheme_obj (X : BigAffineH B S hS) :
    IsAffine ((toScheme B S hS).obj X) := X.property

/-- A family in the big affine h category is standard h when its image as a family of scheme
morphisms is standard h. -/
public abbrev IsStandardHCovering (E : Covering (BigAffineH B S hS)) : Prop :=
  AlgebraicGeometry.IsStandardHCovering (fun i ↦ (toScheme B S hS).map (E.2.f i))

/-- **Stacks 0EU1, part (2).** An affine family covers exactly when it covers in the big h
site over `S` and is a standard h covering. -/
@[stacks 0EU1 "part (2), coverings"]
public abbrev IsCovering (E : Covering (BigAffineH B S hS)) : Prop :=
  BigHOver.IsCovering B S hS
      ⟨(inclusion B S hS).obj E.1, E.2.map (inclusion B S hS)⟩ ∧
    IsStandardHCovering B S hS E

/-- The precoverage presented by the standard h covering families of affine objects. -/
public def precoverage : Precoverage (BigAffineH B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- Membership in the affine precoverage is characterized by a standard h covering family. -/
public theorem mem_precoverage_iff {X : BigAffineH B S hS} {R : Presieve X} :
    R ∈ precoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩ :=
  Iff.rfl

/-- The topology generated by the standard h covering families of affine objects. -/
public abbrev topology : GrothendieckTopology (BigAffineH B S hS) :=
  (precoverage B S hS).toGrothendieck

end BigAffineH

end AlgebraicGeometry
