module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Big ph sites

A big ph site is a size-bounded full subcategory of schemes together with a chosen,
set-sized system of ph covering families on it.  The system contains prescribed initial
schemes and coverings, satisfies the site axioms, and contains a combinatorial
representative of every ph covering.  For such a site containing a scheme `S`, the big ph
category over `S` is the slice over `S`, and the big affine ph category is its full
subcategory on objects with affine underlying scheme; the finite ph covering families of
the latter again satisfy the site axioms.

## Main definitions

* `AlgebraicGeometry.IsPHCoveringInCutoff`: recognizes ph coverings in a cutoff category.
* `AlgebraicGeometry.BigPHSite`: packages the choices defining a big ph site.
* `AlgebraicGeometry.BigPHOver` and `AlgebraicGeometry.BigAffinePH`: the big ph category
  over `S` and its affine full subcategory, with their covering families and topologies.

## Main results

* `AlgebraicGeometry.BigAffinePH.isSite`: the finite ph covering families of affine objects
  over `S` form a site.

## Implementation notes

Following Stacks 000J, the ambient category is `AlgebraicGeometry.SchemeBelow`, the
full subcategory of schemes of size below the cutoff; a family there is ph covering when
its image under the canonical inclusion is one in the sense of Stacks 0DBG.  As in Stacks
000X the chosen families are those with index cardinality at most `coveringBound`, and the
limit ordinal records the remaining choice in that construction.  The generated
Grothendieck topology is kept separate from the chosen family-level coverings, so that both
the site axioms and Mathlib's sheaf interface are directly available.  Stability of the
affine families under base change needs that a fibre product of affine objects of the
cutoff category is again one, which is checked by comparing it with the fibre product taken
in all schemes.

## References

* [Stacks Project, Tag 0DBJ](https://stacks.math.columbia.edu/tag/0DBJ)
* [Stacks Project, Tag 0DBL](https://stacks.math.columbia.edu/tag/0DBL)
* [Stacks Project, Tag 0DBM](https://stacks.math.columbia.edu/tag/0DBM)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A family in a size-bounded full category of schemes is ph covering if its image in all
schemes is a ph covering. -/
public abbrev IsPHCoveringInCutoff {κ : Cardinal.{u}}
    (𝒰 : Covering.{u + 1, u, u + 1} (AlgebraicGeometry.SchemeBelow κ)) : Prop :=
  let 𝒱 := 𝒰.2.map (AlgebraicGeometry.schemeBelowInclusion κ)
  IsPHCovering 𝒱.X 𝒱.f

/-- **Stacks 0DBJ.** A big ph site consists of an initial set of schemes and initial ph
coverings, a sufficiently large cutoff category containing them, and a bounded collection
of ph coverings satisfying the site axioms and representing every ph covering. -/
@[stacks 0DBJ]
public structure BigPHSite where
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
  /-- The initially chosen ph covering families among the initial schemes. -/
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
  /-- Every initially chosen family is among the bounded ph coverings. -/
  initialCoverings_mem : ∀ 𝒰 ∈ initialCoverings,
    CovBounded (IsPHCoveringInCutoff (κ := cutoff)) coveringBound 𝒰
  /-- The bounded ph covering families satisfy the site axioms. -/
  coverings_isSite :
    IsSite (CovBounded (IsPHCoveringInCutoff (κ := cutoff)) coveringBound)
  /-- Every ph covering has a combinatorially equivalent chosen representative. -/
  covering_representative :
    ∀ 𝒰 : Covering (AlgebraicGeometry.SchemeBelow cutoff),
      IsPHCoveringInCutoff 𝒰 →
      ∃ 𝒱 : Covering (AlgebraicGeometry.SchemeBelow cutoff),
        CovBounded IsPHCoveringInCutoff coveringBound 𝒱 ∧ Covering.CombEquiv 𝒰 𝒱

namespace BigPHSite

/-- The stored smallness of the initial schemes is available to typeclass inference. -/
public instance (B : BigPHSite.{u}) : Small.{u} B.initialSchemes := B.initialSchemes_small

/-- The stored smallness of the initial coverings is available to typeclass inference. -/
public instance (B : BigPHSite.{u}) : Small.{u + 1} B.initialCoverings :=
  B.initialCoverings_small

/-- The underlying category of a big ph site. -/
public abbrev Schemes (B : BigPHSite.{u}) :=
  AlgebraicGeometry.SchemeBelow B.cutoff

/-- The canonical inclusion of a big ph site into all schemes. -/
public abbrev inclusion (B : BigPHSite.{u}) : B.Schemes ⥤ Scheme.{u} :=
  AlgebraicGeometry.schemeBelowInclusion B.cutoff

/-- A scheme lies in a big ph site precisely when it is below the site's cutoff. -/
public abbrev Contains (B : BigPHSite.{u}) (X : Scheme.{u}) : Prop := X.size < B.cutoff

/-- A scheme contained in a big ph site, regarded as an object of its category. -/
public abbrev obj (B : BigPHSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) : B.Schemes :=
  ⟨X, hX⟩

/-- The chosen covering families of a big ph site. -/
public abbrev IsCovering (B : BigPHSite.{u}) : Covering B.Schemes → Prop :=
  CovBounded IsPHCoveringInCutoff B.coveringBound

/-- The precoverage represented by the chosen family-level ph coverings. -/
public def precoverage (B : BigPHSite.{u}) : Precoverage B.Schemes where
  coverings X := {R | ∃ 𝒰 : PreZeroHypercover.{u + 1} X,
    R = 𝒰.presieve₀ ∧ B.IsCovering ⟨X, 𝒰⟩}

/-- Membership in the precoverage is witnessed by one of the site's chosen families. -/
public theorem mem_precoverage_iff (B : BigPHSite.{u}) {X : B.Schemes} {R : Presieve X} :
    R ∈ B.precoverage X ↔ ∃ 𝒰 : PreZeroHypercover.{u + 1} X,
      R = 𝒰.presieve₀ ∧ B.IsCovering ⟨X, 𝒰⟩ :=
  Iff.rfl

/-- The Grothendieck topology generated by the chosen ph coverings. -/
public abbrev topology (B : BigPHSite.{u}) : GrothendieckTopology B.Schemes :=
  B.precoverage.toGrothendieck

/-- A chosen covering family is a ph covering. -/
public theorem IsCovering.ph {B : BigPHSite.{u}} {𝒰 : Covering B.Schemes}
    (h𝒰 : B.IsCovering 𝒰) : IsPHCoveringInCutoff 𝒰 := h𝒰.1

/-- The index type of a chosen covering is within the site's bound. -/
public theorem IsCovering.mk_le {B : BigPHSite.{u}} {𝒰 : Covering B.Schemes}
    (h𝒰 : B.IsCovering 𝒰) : #𝒰.2.I₀ ≤ B.coveringBound := h𝒰.2

/-- The chosen ph covering families satisfy the site axioms. -/
public theorem isSite (B : BigPHSite.{u}) : IsSite B.IsCovering := B.coverings_isSite

end BigPHSite

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DBL, part (1).** The big ph category of `S` is the slice of the chosen big ph
category over its object `S`. -/
@[stacks 0DBL "part (1), category"]
public abbrev BigPHOver := Over (B.obj S hS)

namespace BigPHOver

/-- Forget the structure morphism to `S`. -/
public abbrev forget : BigPHOver B S hS ⥤ B.Schemes :=
  Over.forget (B.obj S hS)

/-- The canonical functor from the big ph category over `S` to schemes. -/
public abbrev toScheme : BigPHOver B S hS ⥤ Scheme.{u} :=
  forget B S hS ⋙ B.inclusion

/-- **Stacks 0DBL, part (1).** A family in the slice covers precisely when its underlying
family covers in the chosen big ph site. -/
@[stacks 0DBL "part (1), coverings"]
public abbrev IsCovering (E : Covering (BigPHOver B S hS)) : Prop :=
  B.IsCovering ⟨(forget B S hS).obj E.1, E.2.map (forget B S hS)⟩

/-- The canonical localization of the big ph site's topology at `S`. -/
public abbrev topology : GrothendieckTopology (BigPHOver B S hS) :=
  B.topology.over (B.obj S hS)

/-- An object of the big ph category over `S` has affine underlying scheme. -/
public abbrev IsAffineOver : ObjectProperty (BigPHOver B S hS) :=
  fun X ↦ IsAffine ((toScheme B S hS).obj X)

end BigPHOver

/-- **Stacks 0DBL, part (2).** The big affine ph category is the full subcategory of affine
objects in the big ph category over `S`. -/
@[stacks 0DBL "part (2), category"]
public abbrev BigAffinePH := (BigPHOver.IsAffineOver B S hS).FullSubcategory

namespace BigAffinePH

/-- The canonical full embedding into the big ph category over `S`. -/
public abbrev inclusion : BigAffinePH B S hS ⥤ BigPHOver B S hS :=
  (BigPHOver.IsAffineOver B S hS).ι

/-- The underlying scheme functor of the big affine ph category. -/
public abbrev toScheme : BigAffinePH B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ BigPHOver.toScheme B S hS

/-- The underlying scheme of a big affine ph object is affine. -/
public instance isAffine_toScheme_obj (X : BigAffinePH B S hS) :
    IsAffine ((toScheme B S hS).obj X) := X.property

/-- **Stacks 0DBL, part (2).** An affine family covers exactly when it is a finite covering
family in the big ph site over `S`. -/
@[stacks 0DBL "part (2), coverings"]
public abbrev IsCovering (E : Covering (BigAffinePH B S hS)) : Prop :=
  BigPHOver.IsCovering B S hS
      ⟨(inclusion B S hS).obj E.1, E.2.map (inclusion B S hS)⟩ ∧
    Finite E.2.I₀

/-- The precoverage presented by finite ph coverings of affine objects. -/
public def precoverage : Precoverage (BigAffinePH B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- Membership in the affine precoverage is characterized by a finite ph family. -/
public theorem mem_precoverage_iff {X : BigAffinePH B S hS} {R : Presieve X} :
    R ∈ precoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩ :=
  Iff.rfl

/-- The topology generated by finite ph coverings of affine objects. -/
public abbrev topology : GrothendieckTopology (BigAffinePH B S hS) :=
  (precoverage B S hS).toGrothendieck

end BigAffinePH

/-- A fibre product of affine objects over an affine base in a size-bounded category of
schemes is affine, compared with the fibre product taken in all schemes. -/
private lemma affine_of_isPullback_below {κ : Cardinal.{u}}
    {P X Y Z : AlgebraicGeometry.SchemeBelow κ} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hp : IsPullback p q f g)
    (hX : IsAffine ((AlgebraicGeometry.schemeBelowInclusion κ).obj X))
    (hY : IsAffine ((AlgebraicGeometry.schemeBelowInclusion κ).obj Y))
    (hZ : IsAffine ((AlgebraicGeometry.schemeBelowInclusion κ).obj Z)) :
    IsAffine ((AlgebraicGeometry.schemeBelowInclusion κ).obj P) := by
  let I := AlgebraicGeometry.schemeBelowInclusion κ
  let P' : AlgebraicGeometry.SchemeBelow κ :=
    ⟨pullback (I.map f) (I.map g),
      Scheme.size_pullback_lt (I.map f) (I.map g) X.property Y.property⟩
  let p' : P' ⟶ X := ObjectProperty.homMk (pullback.fst (I.map f) (I.map g))
  let q' : P' ⟶ Y := ObjectProperty.homMk (pullback.snd (I.map f) (I.map g))
  have hp' : IsPullback p' q' f g := by
    apply IsPullback.of_map_of_faithful (F := I)
    simpa [p', q', P', I, ObjectProperty.homMk] using
      (IsPullback.of_hasPullback (I.map f) (I.map g))
  let e : P ≅ P' := hp.isLimit.conePointUniqueUpToIso hp'.isLimit
  have : IsAffine (I.obj P') :=
    Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (I.map f) (I.map g)
  exact IsAffine.of_isIso (I.map e.hom)

namespace BigAffinePH

/-- **Stacks 0DBM.** Finite ph covering families of affine objects over `S` satisfy the
axioms of a site. -/
@[stacks 0DBM]
public lemma isSite (B : BigPHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (BigAffinePH.IsCovering B S hS) := by
  let G := BigAffinePH.inclusion B S hS ⋙ BigPHOver.forget B S hS
  rcases B.isSite with ⟨hIso, hComp, hBC⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    exact ⟨hIso (G.map f), inferInstance⟩
  · intro E hE F hF h
    change B.IsCovering ⟨G.obj E.1, E.2.map G⟩ ∧ Finite E.2.I₀ at hE
    change (∀ i, B.IsCovering ⟨G.obj (F i).1, (F i).2.map G⟩ ∧
      Finite (F i).2.I₀) at hF
    have hc := hComp ⟨G.obj E.1, E.2.map G⟩ hE.1
      (fun i => ⟨G.obj (F i).1, (F i).2.map G⟩) (fun i => (hF i).1)
      (fun i => congrArg G.obj (h i))
    show B.IsCovering ⟨G.obj E.1,
      (E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))).map G⟩ ∧
      Finite (E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))).I₀
    have : Finite E.2.I₀ := hE.2
    have : ∀ i, Finite (F i).2.I₀ := fun i => (hF i).2
    constructor
    · convert hc using 1
      simp [G, PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward]
    · show Finite (Σ i : E.2.I₀, (F i).2.I₀)
      exact Finite.instSigma
  · intro E hE V g
    let U₀ := (BigAffinePH.inclusion B S hS).obj E.1
    let V₀ := (BigAffinePH.inclusion B S hS).obj V
    let X₀ (i : E.2.I₀) := (BigAffinePH.inclusion B S hS).obj (E.2.X i)
    change B.IsCovering ⟨G.obj E.1, E.2.map G⟩ ∧ Finite E.2.I₀ at hE
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ := hBC
      ⟨G.obj E.1, E.2.map G⟩ hE.1 (G.obj V) (G.map g)
    change E.2.I₀ → B.Schemes at P
    change (i : E.2.I₀) → P i ⟶ G.obj (E.2.X i) at p₁
    change (i : E.2.I₀) → P i ⟶ G.obj V at p₂
    change ∀ i, IsPullback (p₁ i) (p₂ i) (G.map (E.2.f i)) (G.map g) at hpb
    let Q₀ (i : E.2.I₀) : BigPHOver B S hS :=
      Over.mk (p₂ i ≫ V₀.hom)
    have hAff (i : E.2.I₀) : IsAffine (B.inclusion.obj (P i)) :=
      affine_of_isPullback_below (hpb i)
        (BigAffinePH.isAffine_toScheme_obj B S hS (E.2.X i))
        (BigAffinePH.isAffine_toScheme_obj B S hS V)
        (BigAffinePH.isAffine_toScheme_obj B S hS E.1)
    let Q (i : E.2.I₀) : BigAffinePH B S hS := ⟨Q₀ i, hAff i⟩
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk (Over.homMk (X := B.obj S hS) (U := Q₀ i) (V := X₀ i)
        (p₁ i) (by
        show p₁ i ≫ (X₀ i).hom = (Q₀ i).hom
        simpa [G, U₀, V₀, X₀, Q₀, Category.assoc] using
          congrArg (fun t => t ≫ U₀.hom) (hpb i).w))
    let q₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk
        (Over.homMk (X := B.obj S hS) (U := Q₀ i) (V := V₀) (p₂ i) (by simp [Q₀]))
    refine ⟨Q, q₁, q₂, ?_, ?_⟩
    · exact fun i ↦ IsPullback.of_map_of_faithful (F := BigAffinePH.inclusion B S hS)
        (IsPullback.of_map_of_faithful (F := BigPHOver.forget B S hS)
          (by simpa [G, Q, Q₀, q₁, q₂, U₀, V₀, X₀] using hpb i))
    · show B.IsCovering ⟨G.obj V, ⟨E.2.I₀, P, p₂⟩⟩ ∧
        Finite E.2.I₀
      exact ⟨hcov, hE.2⟩

end BigAffinePH

end AlgebraicGeometry
