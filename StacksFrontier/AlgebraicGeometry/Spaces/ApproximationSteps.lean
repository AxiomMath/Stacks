module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Finite presentation, and inverse limits of algebraic spaces with affine transitions

A morphism of algebraic spaces over a scheme `S` is *of finite presentation* when it is
locally of finite presentation, quasi-compact and quasi-separated; it is *of finite
presentation at a point of its source* when it is locally of finite presentation on some
open subspace containing that point. A space of finite presentation over a quasi-compact space
is quasi-compact.

A cofiltered limit of affine schemes is of cardinal size below a cardinal `κ` as soon as
the stages are and the index category has fewer objects than the cofinality of `κ`.
Consequently a cofiltered inverse system of affine objects of the big fppf site of `S`,
indexed by a category small enough for the site's cutoff, has a limit in the site whose
underlying scheme is affine.

For a cofiltered inverse system `D` of presheaves on the big fppf site of `S` and a stage
`i`, the base change of the limit of `D` along a morphism `g` to the stage `D i` is the
inverse limit, over the stages mapping to `i`, of the base changes of those stages along
`g`. When the transition morphisms of `D` are affine, each projection from the limit is
therefore affine.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation`: a space of finite
  presentation over a quasi-compact algebraic space is quasi-compact.
* `AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine_of_le` and
  `AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine`: the size bound for a cofiltered
  limit of affine schemes, from a uniform bound on the stages and from an index below the
  cofinality respectively; `AlgebraicGeometry.Scheme.DiagramBoundedBelow` bundles the first
  hypothesis.
* `AlgebraicGeometry.mk_over_le` and `AlgebraicGeometry.mk_over_lt`: a slice of an index
  category is no larger than the pairs consisting of an object and a morphism to the base,
  hence stays below the cofinality of a cardinal that bounds both.
* `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine_of_bounded` and
  `AlgebraicGeometry.BigFppfOver.isAffine_toScheme_of_isLimit_of_bounded`, with their cases
  `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` and
  `AlgebraicGeometry.BigFppfOver.isAffine_toScheme_of_isLimit`: existence and affineness of
  the limit of a bounded cofiltered inverse system of affine objects of the big fppf site of
  `S`.
* `AlgebraicGeometry.Space.HasBoundedBaseChanges`: the base changes of the later stages of an
  inverse system along the affine points of a stage are bounded below the cutoff, with its two
  sufficient conditions `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_lt_cof` and
  `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE`.
* `AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`: the canonical cone exhibiting
  the base change of the limit of an inverse system as the limit of the base changes at
  the later stages.
* `AlgebraicGeometry.Space.isAffineHom_limitπ`: each projection from the limit of a
  cofiltered inverse system with affine transition morphisms is affine.
* `AlgebraicGeometry.Space.isAffineHom_limitπ_of_isSiteSmall` and
  `AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`: the same, for a
  system small for the site in the sense of `AlgebraicGeometry.Space.IsSiteSmall`, and for one
  whose limits of base changes lie in the site.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 06G5](https://stacks.math.columbia.edu/tag/06G5)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-! ### The size of a limit of affine schemes -/

section AffineDiagram

variable {J : Type u} [Category.{u} J]

/-- **The size of a cofiltered limit of affine schemes, from a uniform bound on the stages.**
Indexed by a category with fewer objects than an infinite cardinal `κ`, a cofiltered limit of
affine schemes all of size at most one cardinal `μ < κ` has size below `κ`. -/
theorem Scheme.size_lt_of_isLimit_of_isAffine_of_le [IsCofiltered J] {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j))
    (hJ : #J < κ) {μ : Cardinal.{u}} (hμ : μ < κ) (hsize : ∀ j, (V.obj j).size ≤ μ)
    {c : Cone V} (hc : IsLimit c) :
    c.pt.size < κ := by
  have hpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hΓ : ∀ j, #Γ(V.obj j, ⊤) ≤ μ := by
    intro j
    have := hV j
    refine le_trans ?_ (hsize j)
    rw [Scheme.size_of_isAffine (V.obj j)]
    exact le_max_right _ _
  have h₁ : #Γ(c.pt, ⊤) ≤ #(Σ j : J, Γ(V.obj j, ⊤)) := by
    refine Cardinal.mk_le_of_surjective (f := fun p : Σ j : J, Γ(V.obj j, ⊤) ↦
      show Γ(c.pt, ⊤) from (c.π.app p.1).appTop p.2) ?_
    intro x
    obtain ⟨j, y, hy⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit V c hc x
    exact ⟨⟨j, y⟩, hy⟩
  have h₂ : #(Σ j : J, Γ(V.obj j, ⊤)) < κ := by
    rw [Cardinal.mk_sigma]
    refine (Cardinal.sum_le_mk_mul_iSup _).trans_lt ?_
    exact Cardinal.mul_lt_of_lt hκ.le hJ ((ciSup_le' hΓ).trans_lt hμ)
  rw [Scheme.size_of_isAffine c.pt]
  exact max_lt hκ (h₁.trans_lt h₂)

/-- The cardinal size of a cofiltered limit of affine schemes of size below `κ`, indexed by
a category with fewer objects than the cofinality of `κ`, is again below `κ`. -/
theorem Scheme.size_lt_of_isLimit_of_isAffine [IsCofiltered J] {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j))
    (hJ : #J < κ.ord.cof) (hsize : ∀ j, (V.obj j).size < κ) {c : Cone V} (hc : IsLimit c) :
    c.pt.size < κ :=
  Scheme.size_lt_of_isLimit_of_isAffine_of_le hκ V hV (hJ.trans_le (Ordinal.cof_ord_le κ))
    (Cardinal.iSup_lt_of_lt_cof_ord hJ hsize)
    (fun j ↦ le_ciSup (Cardinal.bddAbove_range _) j) hc

/-- **A diagram of schemes bounded below `κ`**: one cardinal below `κ` bounds both the number
of objects of the index category and the size of every scheme of the diagram. -/
def Scheme.DiagramBoundedBelow (κ : Cardinal.{u}) (V : J ⥤ Scheme.{u}) : Prop :=
  ∃ μ < κ, #J ≤ μ ∧ ∀ j, (V.obj j).size ≤ μ

/-- A diagram indexed by fewer objects than the cofinality of `κ`, all of whose schemes are of
size below `κ`, is bounded below `κ`. -/
theorem Scheme.diagramBoundedBelow_of_lt_cof {κ : Cardinal.{u}} (V : J ⥤ Scheme.{u})
    (hJ : #J < κ.ord.cof) (hsize : ∀ j, (V.obj j).size < κ) :
    Scheme.DiagramBoundedBelow κ V :=
  ⟨max #J (⨆ j, (V.obj j).size),
    max_lt (hJ.trans_le (Ordinal.cof_ord_le κ)) (Cardinal.iSup_lt_of_lt_cof_ord hJ hsize),
    le_max_left _ _, fun j ↦ le_max_of_le_right (le_ciSup (Cardinal.bddAbove_range _) j)⟩

/-- A bound on the sizes of the schemes of a diagram transports along a natural isomorphism. -/
theorem Scheme.DiagramBoundedBelow.of_iso {κ : Cardinal.{u}} {V V' : J ⥤ Scheme.{u}}
    (h : Scheme.DiagramBoundedBelow κ V) (e : V ≅ V') : Scheme.DiagramBoundedBelow κ V' :=
  let ⟨μ, hμ, hJ, hsize⟩ := h
  ⟨μ, hμ, hJ, fun j ↦ (Scheme.size_congr (e.app j)).symm.le.trans (hsize j)⟩

/-- **The size of a cofiltered limit of a bounded diagram of affine schemes** is below `κ`. -/
theorem Scheme.size_lt_of_isLimit_of_diagramBoundedBelow [IsCofiltered J] {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j))
    (hb : Scheme.DiagramBoundedBelow κ V) {c : Cone V} (hc : IsLimit c) : c.pt.size < κ :=
  let ⟨_, hμ, hJ, hsize⟩ := hb
  Scheme.size_lt_of_isLimit_of_isAffine_of_le hκ V hV (hJ.trans_lt hμ) hμ hsize hc

/-- **The cofinality-free size bound for a cofiltered limit of affine schemes.** If the
index category has fewer than `κ` objects and *one* cardinal `μ < κ` bounds the size of
every stage, the limit again has size below `κ`. -/
theorem Scheme.size_lt_of_isLimit_of_isAffine_of_size_le [IsCofiltered J]
    {κ μ : Cardinal.{u}} (hκ : ℵ₀ < κ) (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j))
    (hJ : #J < κ) (hμ : μ < κ) (hsize : ∀ j, (V.obj j).size ≤ μ)
    {c : Cone V} (hc : IsLimit c) : c.pt.size < κ :=
  Scheme.size_lt_of_isLimit_of_isAffine_of_le hκ V hV hJ hμ hsize hc

end AffineDiagram

/-! ### The size of a slice of the index category -/

section SliceSize

variable {I : Type u} [Category.{u} I]

/-- The objects of a slice of a category are indexed by the pairs consisting of an object
and a morphism from it to the base. -/
theorem mk_over_le (i : I) : #(Over i) ≤ #(Σ j : I, (j ⟶ i)) := by
  refine Cardinal.mk_le_of_injective
    (f := fun A : Over i ↦ (⟨A.left, A.hom⟩ : Σ j : I, (j ⟶ i))) ?_
  intro A A' h
  obtain ⟨a, ⟨u⟩, f⟩ := A
  obtain ⟨a', ⟨u'⟩, f'⟩ := A'
  cases u
  cases u'
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj h
  cases h₁
  have : f = f' := eq_of_heq h₂
  subst this
  rfl

/-- A slice of an index category whose object type and whose morphism types are all smaller
than the cofinality of `κ` is again smaller than that cofinality. -/
theorem mk_over_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ.ord.cof)
    (hI : #I < κ.ord.cof) (hhom : ∀ j j' : I, #(j ⟶ j') < κ.ord.cof) (i : I) :
    #(Over i) < κ.ord.cof := by
  refine (mk_over_le i).trans_lt ?_
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_mk_mul_iSup _).trans_lt ?_
  exact Cardinal.mul_lt_of_lt hκ.le hI
    (Cardinal.iSup_lt_of_lt_cof_ord (by rwa [Ordinal.cof_ord_cof]) fun j ↦ hhom j i)

/-- **The cofinality-free bound for a slice of an index category.** If the index category
has fewer than `κ` objects and *one* cardinal `ν < κ` bounds all of its morphism types,
every slice of it again has fewer than `κ` objects. -/
theorem mk_over_lt_of_mk_hom_le {κ ν : Cardinal.{u}} (hκ : ℵ₀ < κ) (hI : #I < κ)
    (hν : ν < κ) (hhom : ∀ j j' : I, #(j ⟶ j') ≤ ν) (i : I) : #(Over i) < κ := by
  refine (mk_over_le i).trans_lt ?_
  rw [Cardinal.mk_sigma]
  exact (Cardinal.sum_le_mk_mul_iSup _).trans_lt
    (Cardinal.mul_lt_of_lt hκ.le hI ((ciSup_le' fun j ↦ hhom j i).trans_lt hν))

end SliceSize

/-! ### Cofiltered limits of affine objects of the big fppf site -/

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The diagram of schemes underlying a diagram in the big fppf site of `S`. -/
public abbrev underlyingDiagram (V : J ⥤ BigFppfOver B S hS) : J ⥤ Scheme.{u} :=
  (V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion

omit [IsCofiltered J] in
/-- The diagram of schemes underlying a cofiltered diagram of affine objects of the big
fppf site of `S` has a limit. -/
private theorem hasLimit_underlying (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j))) :
    HasLimit (underlyingDiagram V) :=
  have : ∀ j, IsAffine ((underlyingDiagram V).obj j) := hV
  CofilteredLimit.hasLimit_of_isAffine (underlyingDiagram V)

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` has a limit in the
site as soon as the size-bounded subcategory of schemes creates the limit of the underlying
schemes. -/
private theorem hasLimit_of_createsLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hcr : CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion) : HasLimit V := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have : HasLimit (V ⋙ BigFppfOver.forget B S hS) := hasLimit_of_created _ B.inclusion
  exact hasLimit_of_created V (Over.forget (B.obj hS))

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of affine
objects of the big fppf site of `S` as soon as the size-bounded subcategory of schemes creates
the limit of the underlying schemes. -/
private theorem preservesLimit_toScheme_of_createsLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hcr : CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have : HasLimit (V ⋙ BigFppfOver.forget B S hS) := hasLimit_of_created _ B.inclusion
  infer_instance

/-- The underlying scheme of the limit of a cofiltered inverse system of affine objects of the
big fppf site of `S` is affine as soon as the size-bounded subcategory of schemes creates the
limit of the underlying schemes. -/
private theorem isAffine_toScheme_of_isLimit_of_createsLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hcr : CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion)
    {c : Cone V} (hc : IsLimit c) : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  have := preservesLimit_toScheme_of_createsLimit V hV hcr
  have : ∀ j, IsAffine ((V ⋙ BigFppfOver.toScheme B S hS).obj j) := hV
  Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (BigFppfOver.toScheme B S hS) hc)

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the big fppf site of `S` that is bounded
below the site's cutoff. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfBounded (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS)) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have hsize : schemeSizeBelow B.cutoff (limit (underlyingDiagram V)) :=
    Scheme.size_lt_of_isLimit_of_diagramBoundedBelow B.aleph0_lt_cutoff (underlyingDiagram V)
      hV hb (limit.isLimit (underlyingDiagram V))
  Limits.createsLimitFullSubcategoryInclusion _ hsize

omit [IsCofiltered J] in
/-- A diagram of objects of the big fppf site of `S` indexed by fewer objects than the
cofinality of the cutoff is bounded below the cutoff. -/
theorem BigFppfOver.diagramBoundedBelow_of_lt_cof (V : J ⥤ BigFppfOver B S hS)
    (hJ : #J < B.cutoff.ord.cof) :
    Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS) :=
  Scheme.diagramBoundedBelow_of_lt_cof _ hJ fun j ↦ (V.obj j).left.property

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the big fppf site of `S` indexed by fewer
objects than the cofinality of the site's cutoff. -/
@[instance_reducible]
private noncomputable def createsLimitInclusion (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  createsLimitInclusionOfBounded V hV (BigFppfOver.diagramBoundedBelow_of_lt_cof V hJ)

/-- **A bounded cofiltered inverse system of affine objects of the big fppf site of `S` has a
limit in the site.** -/
theorem BigFppfOver.hasLimit_of_isAffine_of_bounded (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS)) :
    HasLimit V :=
  hasLimit_of_createsLimit V hV (createsLimitInclusionOfBounded V hV hb)

/-- A cofiltered inverse system of affine objects of the big fppf site of `S`, indexed by a
category with fewer objects than the cofinality of the site's size cutoff, has a limit in
the site. -/
theorem BigFppfOver.hasLimit_of_isAffine (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) : HasLimit V :=
  BigFppfOver.hasLimit_of_isAffine_of_bounded V hV (BigFppfOver.diagramBoundedBelow_of_lt_cof V hJ)

/-- The underlying scheme functor preserves the limit of a bounded cofiltered inverse system of
affine objects of the big fppf site of `S`. -/
theorem BigFppfOver.preservesLimit_toScheme_of_bounded (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS)) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  preservesLimit_toScheme_of_createsLimit V hV (createsLimitInclusionOfBounded V hV hb)

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of
affine objects of the big fppf site of `S`. -/
theorem BigFppfOver.preservesLimit_toScheme (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  BigFppfOver.preservesLimit_toScheme_of_bounded V hV
    (BigFppfOver.diagramBoundedBelow_of_lt_cof V hJ)

/-- The underlying scheme of the limit of a bounded cofiltered inverse system of affine objects
of the big fppf site of `S` is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit_of_bounded (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS))
    {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  isAffine_toScheme_of_isLimit_of_createsLimit V hV (createsLimitInclusionOfBounded V hV hb) hc

/-- The underlying scheme of the limit of a cofiltered inverse system of affine objects of
the big fppf site of `S` is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  BigFppfOver.isAffine_toScheme_of_isLimit_of_bounded V hV
    (BigFppfOver.diagramBoundedBelow_of_lt_cof V hJ) hc

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the big fppf site of `S`, as soon as
that limit is of size below the site's cutoff. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfSizeBelow (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hsize : ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  Limits.createsLimitFullSubcategoryInclusion _
    (hsize (limit.cone (underlyingDiagram V)) (limit.isLimit (underlyingDiagram V)))

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` whose
underlying limit of schemes has size below the site's cutoff has a limit in the site. -/
private theorem hasLimit_of_isAffine_of_sizeBelow (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hsize : ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt) :
    HasLimit V :=
  hasLimit_of_createsLimit V hV (createsLimitInclusionOfSizeBelow V hV hsize)

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of
affine objects of the big fppf site of `S` whose underlying limit of schemes has size below
the site's cutoff. -/
private theorem preservesLimit_toScheme_of_sizeBelow (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hsize : ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  preservesLimit_toScheme_of_createsLimit V hV (createsLimitInclusionOfSizeBelow V hV hsize)

/-- The underlying scheme of the limit of a cofiltered inverse system of affine objects of
the big fppf site of `S` whose underlying limit of schemes has size below the site's cutoff
is affine. -/
private theorem isAffine_toScheme_of_isLimit_of_sizeBelow (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hsize : ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt)
    {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  isAffine_toScheme_of_isLimit_of_createsLimit V hV (createsLimitInclusionOfSizeBelow V hV hsize) hc

/-- The underlying limit of schemes of a cofiltered inverse system of affine objects of the
big fppf site of `S`, indexed by a category with fewer objects than the cofinality of the
site's size cutoff, has size below that cutoff. -/
private theorem sizeBelow_limit_underlying_of_lt_cof (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) :
    ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt :=
  fun _ hc ↦ Scheme.size_lt_of_isLimit_of_isAffine B.aleph0_lt_cutoff (underlyingDiagram V)
    hV hJ (fun j ↦ (V.obj j).left.property) hc

/-- The underlying limit of schemes of a cofiltered inverse system of affine objects of the
big fppf site of `S`, indexed by a category with fewer than `B.cutoff` objects and with all
stages of size at most one cardinal `μ < B.cutoff`, has size below that cutoff. -/
private theorem sizeBelow_limit_underlying_of_size_le (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hstage : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ) :
    ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt :=
  fun _ hc ↦ Scheme.size_lt_of_isLimit_of_isAffine_of_size_le B.aleph0_lt_cutoff
    (underlyingDiagram V) hV hJ hμ hstage hc

/-- **The cofinality-free existence of the limit in the site.** A cofiltered inverse system
of affine objects of the big fppf site of `S`, indexed by a category with fewer than
`B.cutoff` objects and all of whose stages have size at most one cardinal `μ < B.cutoff`,
has a limit in the site. -/
theorem BigFppfOver.hasLimit_of_isAffine_of_size_le (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hstage : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ) : HasLimit V :=
  hasLimit_of_isAffine_of_sizeBelow V hV
    (sizeBelow_limit_underlying_of_size_le V hV hJ hμ hstage)

/-- **The cofinality-free preservation of the limit by the underlying scheme functor.** The
underlying scheme functor preserves the limit of a cofiltered inverse system of affine objects
of the big fppf site of `S`, indexed by a category with fewer than `B.cutoff` objects and all
of whose stages have size at most one cardinal `μ < B.cutoff`. -/
theorem BigFppfOver.preservesLimit_toScheme_of_size_le (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hstage : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  preservesLimit_toScheme_of_sizeBelow V hV
    (sizeBelow_limit_underlying_of_size_le V hV hJ hμ hstage)

/-- **The cofinality-free affineness of the limit.** The underlying scheme of the limit of a
cofiltered inverse system of affine objects of the big fppf site of `S`, indexed by a category
with fewer than `B.cutoff` objects and all of whose stages have size at most one cardinal
`μ < B.cutoff`, is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit_of_size_le (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hstage : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ)
    {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  isAffine_toScheme_of_isLimit_of_sizeBelow V hV
    (sizeBelow_limit_underlying_of_size_le V hV hJ hμ hstage) hc

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of finite presentation -/

section FinitePresentation

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `f : X ⟶ Y` is of finite presentation and `Y` is a quasi-compact algebraic space, then
`X` is quasi-compact. -/
theorem isQuasiCompactSpace_of_isFinitePresentation (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hf : IsFinitePresentation B S hS f) : IsQuasiCompactSpace B S hS X := by
  obtain ⟨U, q, hc, hs, he⟩ := hf.2.1 Y hY hYqc (𝟙 Y)
  have : IsIso (pullback.snd (𝟙 Y) f) := inferInstance
  let e := asIso (pullback.snd (𝟙 Y) f)
  refine ⟨U, q ≫ e.hom, hc, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.postcomp _ e.hom q hs
  · exact fun U' φ hφ ↦ MorphismProperty.RespectsIso.postcomp _ e.hom (φ ≫ q) (he U' φ hφ)

end FinitePresentation

/-! ### Base change of an inverse limit at a stage -/

section Limits

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- For a cofiltered inverse system `D` of presheaves on the big fppf site of `S`, a stage `i`
and a morphism `g : T ⟶ D i`, the base changes of the stages over `i` along `g` form an inverse
system whose limit is the base change of `limit D` along `g`. The cone is the limit cone of `D`,
restricted to the stages over `i` and base changed along `g`. -/
@[stacks 07SF "part (2)", stacks 07SH "base change of the limit is the limit of the base changes"]
noncomputable def isLimitPullbackLimitOverPost (i : I)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : T ⟶ D.obj i) :
    IsLimit ((Over.forget T).mapCone
      ((Over.pullback g).mapCone ((limit.cone D).overPost i))) := by
  letI : IsConnected (Over i) := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget T)
    (isLimitOfPreserves (Over.pullback g) ((limit.isLimit D).overPost i))

omit [IsCofiltered I] in
/-- An inverse limit of fppf sheaves on the big fppf site of `S` is an fppf sheaf. -/
theorem isSheaf_limit (hD : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.obj i)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (limit D) :=
  ObjectProperty.prop_limit _ D hD

/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic spaces
with affine transition morphisms is affine, provided the limit of the affine base changes
`W` of the stages over `i` exists and has an affine underlying scheme. -/
private theorem isAffineHom_limitπ_of_hasLimit_isAffine
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i : I)
    (hL : ∀ (Z : BigAffineFppf B S hS)
      (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
      (W : Over i ⥤ BigAffineFppf B S hS),
      (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
        (Over.post (X := i) D ⋙ Over.pullback g) ⋙
          Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
      (∀ k : Over i, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((W ⋙ BigAffineFppf.inclusion B S hS).obj k))) →
      HasLimit (W ⋙ BigAffineFppf.inclusion B S hS) ∧
        ∀ {c : Cone (W ⋙ BigAffineFppf.inclusion B S hS)}, IsLimit c →
          IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) :
    IsAffineHom B S hS (limit.π D i) := by
  intro Z g
  set E := (Over.post (X := i) D ⋙ Over.pullback g) ⋙
    Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) with hE
  have hbase := isLimitPullbackLimitOverPost B S hS D i g
  have hess : ∀ k : Over i,
      (BigAffineFppf.inclusion B S hS ⋙ yoneda).essImage (E.obj k) := by
    intro k
    obtain ⟨A, p, q, hpb⟩ := hAffine k.hom Z g
    exact ⟨A, ⟨hpb.isoPullback⟩⟩
  set F := BigAffineFppf.inclusion B S hS ⋙ yoneda with hF
  set W := Functor.essImage.liftFunctor E F hess with hW
  have hiso : W ⋙ F ≅ E := Functor.essImage.liftFunctorCompIso E F hess
  set W' := W ⋙ BigAffineFppf.inclusion B S hS with hW'
  have hWaff : ∀ k : Over i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W'.obj k)) :=
    fun k ↦ (W.obj k).property
  obtain ⟨hlim, hL⟩ := hL Z g W hiso hWaff
  have hLaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (limit W')) := hL (limit.isLimit W')
  have hyoneda : IsLimit ((Cone.postcompose hiso.hom).obj
      (yoneda.mapCone (limit.cone W'))) :=
    (IsLimit.postcomposeHomEquiv hiso (yoneda.mapCone (limit.cone W'))).symm
      (isLimitOfPreserves yoneda (limit.isLimit W'))
  have e : yoneda.obj (limit W') ≅ pullback (limit.π D i) g :=
    hyoneda.conePointUniqueUpToIso hbase
  refine ⟨⟨limit W', hLaff⟩, e.hom ≫ pullback.fst _ _,
    yoneda.preimage (e.hom ≫ pullback.snd _ _), ?_⟩
  exact IsPullback.of_iso_pullback ⟨by rw [Functor.map_preimage]; simp [pullback.condition]⟩
    e rfl (by rw [Functor.map_preimage])


/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic spaces
with affine transition morphisms is affine, provided the index category is small enough for the
site: its object type and all of its morphism types have cardinality below the cofinality of the
site's size cutoff. -/
@[stacks 07SF "part (1)"]
theorem isAffineHom_limitπ (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) : IsAffineHom B S hS (limit.π D i) := by
  refine isAffineHom_limitπ_of_hasLimit_isAffine B S hS D hAffine i fun Z g W _ hWaff ↦ ?_
  have hJ : #(Over i) < B.cutoff.ord.cof := mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i
  exact ⟨BigFppfOver.hasLimit_of_isAffine _ hWaff hJ,
    fun hc ↦ BigFppfOver.isAffine_toScheme_of_isLimit _ hWaff hJ hc⟩

end Limits

/-! ### Bounded base changes -/

/-- **One cardinal bounding every object of the site that maps monomorphically to `Z`.**
This is the bound of `AlgebraicGeometry.Scheme.size_le_of_mono` for the underlying scheme of
`Z`. -/
noncomputable def monoSizeBound (Z : BigFppfOver B S hS) : Cardinal.{u} :=
  max (2 ^ #((BigFppfOver.toScheme B S hS).obj Z : Type u))
    ((BigFppfOver.toScheme B S hS).obj Z).size

/-- The uniform bound of `AlgebraicGeometry.Space.monoSizeBound` lies below the site's size
cutoff. -/
theorem monoSizeBound_lt_cutoff (Z : BigFppfOver B S hS) :
    monoSizeBound B S hS Z < B.cutoff :=
  Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit Z.left.property

/-- An object of the site admitting a monomorphism of represented presheaves into `Z` has
size at most `AlgebraicGeometry.Space.monoSizeBound B S hS Z`. -/
theorem size_le_monoSizeBound_of_mono {W Z : BigFppfOver B S hS}
    (m : yoneda.obj W ⟶ yoneda.obj Z) (hm : Mono m) :
    ((BigFppfOver.toScheme B S hS).obj W).size ≤ monoSizeBound B S hS Z :=
  have h₁ : Mono (yoneda.preimage m) :=
    yoneda.mono_of_mono_map (by rwa [Functor.map_preimage])
  have h₂ : Mono ((BigFppfOver.toScheme B S hS).map (yoneda.preimage m)) :=
    preserves_mono_of_preservesLimit _ _
  Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map (yoneda.preimage m))

/-- Every stage of the inverse system `D` admits a monomorphism to the presheaf represented by
`Z`. -/
def MonoBoundedBy {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Z : BigFppfOver B S hS) : Prop :=
  ∀ i, ∃ m : D.obj i ⟶ yoneda.obj Z, Mono m

/-- An object of the site mapping monomorphically to a stage of a system bounded by `Z` has
size at most `AlgebraicGeometry.Space.monoSizeBound B S hS Z`. -/
theorem size_le_monoSizeBound_of_monoBoundedBy {I : Type u} [Category.{u} I]
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : BigFppfOver B S hS}
    (hb : MonoBoundedBy B S hS D Z) {i : I} {W : BigFppfOver B S hS}
    (m : yoneda.obj W ⟶ D.obj i) (hm : Mono m) :
    ((BigFppfOver.toScheme B S hS).obj W).size ≤ monoSizeBound B S hS Z := by
  obtain ⟨n, hn⟩ := hb i
  exact size_le_monoSizeBound_of_mono B S hS (m ≫ n) (mono_comp m n)

/-- **An inverse system whose base changes along a test morphism are uniformly bounded.** For
every stage `i₀` and every morphism `g : yoneda Z ⟶ D i₀` from an object of the site, one
cardinal below the cutoff bounds the sizes of *all* the objects of the site representing a base
change `D k ×_{D i₀} yoneda Z` of a later stage, `k` ranging over the slice over `i₀`. -/
def BaseChangeSizeBounded {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (i₀ : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i₀),
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧
      ∀ (k : Over i₀) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ D.obj k.left)
        (q : yoneda.obj W ⟶ yoneda.obj Z), IsPullback p q (D.map k.hom) g →
          ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ

/-- An inverse system with monomorphic transition morphisms has uniformly bounded base
changes. -/
theorem baseChangeSizeBounded_of_mono {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) : BaseChangeSizeBounded B S hS D :=
  fun _ Z _ ↦ ⟨monoSizeBound B S hS Z, monoSizeBound_lt_cutoff B S hS Z,
    fun k _ _ q hpq ↦ size_le_monoSizeBound_of_mono B S hS q
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpq (hMono k.hom))⟩

section BoundedBaseChanges

variable {I : Type u} [Category.{u} I]

/-- Two objects of the big fppf site of `S` representing the same fibre product of presheaves
have underlying schemes of the same size. -/
theorem BigFppfOver.size_eq_of_isPullback {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Z} {g : Y ⟶ Z} {W W' : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X}
    {q : yoneda.obj W ⟶ Y} {p' : yoneda.obj W' ⟶ X} {q' : yoneda.obj W' ⟶ Y}
    (h : IsPullback p q f g) (h' : IsPullback p' q' f g) :
    ((BigFppfOver.toScheme B S hS).obj W).size = ((BigFppfOver.toScheme B S hS).obj W').size :=
  Scheme.size_congr ((BigFppfOver.toScheme B S hS).mapIso
    (Yoneda.fullyFaithful.preimageIso (h.isoIsPullback _ _ h')))

variable (i₀ : I) (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The base changes of the later stages of `D` along the affine points of the stage `i₀` are
bounded.** For every affine scheme-valued point `f₀ : U₀ ⟶ D i₀` there is one cardinal below the
site's cutoff bounding the number of stages above `i₀` and the size of every object of the site
representing a base change `D j ×_{D i₀} U₀`. -/
def HasBoundedBaseChanges : Prop :=
  ∀ (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀),
    ∃ μ < B.cutoff, #(Over i₀) ≤ μ ∧
      ∀ (j : Over i₀) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ D.obj j.left)
        (q : yoneda.obj W ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)),
        IsPullback p q (D.map j.hom) f₀ → ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ

/-- **A morphism of presheaves whose base changes to affine objects of the site grow by at most
`ν`.** Every object `W` of the site representing a base change of `f` along a morphism from an
affine object `T` has size at most `max (size T) ν`. -/
def HasBaseChangesOfSizeLE (ν : Cardinal.{u}) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) : Prop :=
  ∀ (T : BigAffineFppf B S hS) (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ G)
    (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F)
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj T),
    IsPullback p (yoneda.map q) f g → ((BigFppfOver.toScheme B S hS).obj W).size ≤
      max ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj T)).size ν

/-- **An affine morphism whose base changes to affine objects are locally of finite type has
base changes of bounded growth**, for every bound `ν`. -/
theorem hasBaseChangesOfSizeLE_of_locallyOfFiniteType (ν : Cardinal.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsAffineHom B S hS f)
    (hft : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    HasBaseChangesOfSizeLE B S hS ν f := by
  intro T g W p q hpq
  obtain ⟨W₀, p₀, q₀, hpb₀⟩ := hf T g
  have hW₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W₀)) := W₀.property
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T)) := T.property
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).mapIso
      (Yoneda.fullyFaithful.preimageIso (hpq.isoIsPullback _ _ hpb₀))).hom
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := hft.property g p q hpq
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q) :=
    isAffineHom_of_isAffine _
  exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    ((BigFppfOver.toScheme B S hS).map q)).trans (le_max_left _ _)

/-- **Bounded base changes from a small index.** If the index category has fewer objects, and
fewer morphisms between any two objects, than the cofinality of the site's cutoff, and the
transition morphisms are affine, then the base changes of the stages along any affine point of
a stage are bounded. -/
theorem hasBoundedBaseChanges_of_lt_cof
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    HasBoundedBaseChanges B S hS i₀ D := by
  intro U₀ f₀
  choose W p q hpb using fun j : Over i₀ ↦ hAffine j.hom U₀ f₀
  have hJ : #(Over i₀) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀
  have hW : ∀ j, ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (W j))).size < B.cutoff := fun j ↦
    ((BigAffineFppf.inclusion B S hS).obj (W j)).left.property
  refine ⟨max #(Over i₀) (⨆ j, ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (W j))).size),
    max_lt (hJ.trans_le (Ordinal.cof_ord_le _)) (Cardinal.iSup_lt_of_lt_cof_ord hJ hW),
    le_max_left _ _, fun j W' p' q' h ↦ ?_⟩
  rw [BigFppfOver.size_eq_of_isPullback B S hS h (hpb j)]
  exact le_max_of_le_right (le_ciSup (Cardinal.bddAbove_range _) j)

/-- **Bounded base changes from transitions of bounded growth.** If the stages above `i₀` are
fewer than the site's cutoff and every transition morphism has base changes to affine objects
growing by at most a fixed `ν` below the cutoff, then the base changes of the stages along any
affine point `U₀` of `i₀` are bounded by `max (#(Over i₀)) (max (size U₀) ν)`. -/
theorem hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE (hOver : #(Over i₀) < B.cutoff)
    {ν : Cardinal.{u}} (hν : ν < B.cutoff)
    (hD : ∀ {i j : I} (f : i ⟶ j), HasBaseChangesOfSizeLE B S hS ν (D.map f)) :
    HasBoundedBaseChanges B S hS i₀ D := fun U₀ f₀ ↦
  ⟨max #(Over i₀) (max ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj U₀)).size ν),
    max_lt hOver (max_lt ((BigAffineFppf.inclusion B S hS).obj U₀).left.property hν),
    le_max_left _ _, fun j W p q h ↦ (hD j.hom U₀ f₀ W p (yoneda.preimage q)
      (by rwa [Functor.map_preimage])).trans (le_max_right _ _)⟩

end BoundedBaseChanges

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry

/-! ### The size of a limit of affine schemes -/

section AffineDiagram

variable {J : Type u} [Category.{u} J]

end AffineDiagram

/-! ### The size of a slice of the index category -/

section SliceSize

variable {I : Type u} [Category.{u} I]

/-- A bound on the morphism types of an index category bounds the morphism types of each of
its slices. -/
theorem mk_over_hom_lt {c : Cardinal.{u}} (hhom : ∀ j j' : I, #(j ⟶ j') < c) (i : I)
    (j k : Over i) : #(j ⟶ k) < c :=
  (Cardinal.mk_le_of_injective (show Function.Injective (fun f : j ⟶ k ↦ f.left) from
    fun _ _ h ↦ Over.OverMorphism.ext h)).trans_lt (hhom j.left k.left)

end SliceSize

/-! ### A cofiltered limit of subobjects of a fixed object -/

namespace CofilteredLimit

/-- **A compatible family of monomorphisms to one object makes a cofiltered limit a subobject
of that object.** If every stage of a cofiltered diagram `V` carries a monomorphism `ρ j` to a
fixed object `T`, compatibly with the transition morphisms, then the composite of any limit
projection with its member of the family is a monomorphism. -/
theorem mono_π_app_comp {C : Type*} [Category C] {J : Type*} [Category J] [IsCofiltered J]
    {V : J ⥤ C} {T : C} (ρ : ∀ j, V.obj j ⟶ T)
    (hρ : ∀ {j k : J} (f : j ⟶ k), V.map f ≫ ρ k = ρ j) (hmono : ∀ j, Mono (ρ j))
    {c : Cone V} (hc : IsLimit c) (j₀ : J) : Mono (c.π.app j₀ ≫ ρ j₀) := by
  have key : ∀ j : J, c.π.app j ≫ ρ j = c.π.app j₀ ≫ ρ j₀ := by
    intro j
    obtain ⟨n, u, v, -⟩ := IsCofilteredOrEmpty.cone_objs (C := J) j j₀
    have h₁ : c.π.app n ≫ ρ n = c.π.app j ≫ ρ j := by
      rw [← hρ u, ← Category.assoc, c.w u]
    have h₂ : c.π.app n ≫ ρ n = c.π.app j₀ ≫ ρ j₀ := by
      rw [← hρ v, ← Category.assoc, c.w v]
    rw [← h₁, h₂]
  refine ⟨fun {_} g h hgh ↦ hc.hom_ext fun j ↦ ?_⟩
  have _ := hmono j
  refine (cancel_mono (ρ j)).1 ?_
  rwa [Category.assoc, Category.assoc, key j]

end CofilteredLimit

/-! ### Cofiltered limits of affine objects of the big fppf site -/

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

omit [IsCofiltered J] in
/-- **The condition under which a cofiltered diagram of affine objects of the big fppf site of
`S` has its limit inside the site.** Either the index category has fewer objects than the
cofinality of the site's size cutoff, or the stages carry a compatible family of monomorphisms
of schemes to one object of the site. -/
def BigFppfOver.IsSiteSmallDiagram (V : J ⥤ BigFppfOver B S hS) : Prop :=
  #J < B.cutoff.ord.cof ∨
    ∃ (T : BigFppfOver B S hS) (ρ : ∀ j, V.obj j ⟶ T),
      (∀ {j k : J} (f : j ⟶ k), V.map f ≫ ρ k = ρ j) ∧
        ∀ j, Mono ((BigFppfOver.toScheme B S hS).map (ρ j))

omit [IsCofiltered J] in
/-- An index category with fewer objects than the cofinality of the site's size cutoff is small
for the site. -/
theorem BigFppfOver.IsSiteSmallDiagram.of_lt_cof {V : J ⥤ BigFppfOver B S hS}
    (hJ : #J < B.cutoff.ord.cof) : BigFppfOver.IsSiteSmallDiagram V :=
  Or.inl hJ

omit [IsCofiltered J] in
/-- A compatible family of monomorphisms of schemes from the stages to one object of the site
makes the diagram small for the site, whatever its index. -/
theorem BigFppfOver.IsSiteSmallDiagram.of_mono {V : J ⥤ BigFppfOver B S hS}
    (T : BigFppfOver B S hS) (ρ : ∀ j, V.obj j ⟶ T)
    (hρ : ∀ {j k : J} (f : j ⟶ k), V.map f ≫ ρ k = ρ j)
    (hmono : ∀ j, Mono ((BigFppfOver.toScheme B S hS).map (ρ j))) :
    BigFppfOver.IsSiteSmallDiagram V :=
  Or.inr ⟨T, ρ, hρ, hmono⟩

omit [IsCofiltered J] in
/-- A compatible family of morphisms from the stages to one object of the site which are
monomorphisms *of presheaves* makes the diagram small for the site. -/
theorem BigFppfOver.IsSiteSmallDiagram.of_mono_map {V : J ⥤ BigFppfOver B S hS}
    (T : BigFppfOver B S hS) (ρ : ∀ j, V.obj j ⟶ T)
    (hρ : ∀ {j k : J} (f : j ⟶ k), V.map f ≫ ρ k = ρ j)
    (hmono : ∀ j, Mono (yoneda.map (ρ j))) : BigFppfOver.IsSiteSmallDiagram V := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  refine .of_mono T ρ hρ (fun j ↦ ?_)
  have _ : Mono (ρ j) := (yoneda (C := BigFppfOver B S hS)).mono_of_mono_map (hmono j)
  exact inferInstance

omit [IsCofiltered J] in
/-- A diagram in the big fppf category over `S` whose image under the Yoneda embedding carries
a compatible family of monomorphisms to a representable presheaf is small for the site. -/
theorem BigFppfOver.IsSiteSmallDiagram.of_mono_yoneda {V : J ⥤ BigFppfOver B S hS}
    {E : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (iso : V ⋙ yoneda ≅ E)
    (T : BigFppfOver B S hS) (ρ : ∀ j, E.obj j ⟶ yoneda.obj T)
    (hρ : ∀ {j k : J} (f : j ⟶ k), E.map f ≫ ρ k = ρ j)
    (hmono : ∀ j, Mono (ρ j)) : BigFppfOver.IsSiteSmallDiagram V := by
  refine .of_mono_map T (fun j ↦ yoneda.preimage (iso.hom.app j ≫ ρ j)) (fun {j k} f ↦ ?_)
    (fun j ↦ ?_)
  · refine (yoneda (C := BigFppfOver B S hS)).map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    have h₁ := iso.hom.naturality f
    simp only [Functor.comp_map] at h₁
    rw [← Category.assoc, h₁, Category.assoc, hρ f]
  · have _ := hmono j
    have _ : IsIso (iso.hom.app j) := inferInstance
    rw [Functor.map_preimage]
    exact mono_comp _ _

omit [IsCofiltered J] in
/-- **Smallness of a diagram for the site survives an endofunctor which preserves
monomorphisms.** -/
theorem BigFppfOver.IsSiteSmallDiagram.comp {V : J ⥤ BigFppfOver B S hS}
    (Φ : BigFppfOver B S hS ⥤ BigFppfOver B S hS) [Φ.PreservesMonomorphisms]
    (hV : BigFppfOver.IsSiteSmallDiagram V) :
    BigFppfOver.IsSiteSmallDiagram (V ⋙ Φ) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  rcases hV with h | ⟨T, ρ, hρ, hmono⟩
  · exact Or.inl h
  refine .of_mono (Φ.obj T) (fun j ↦ Φ.map (ρ j)) (fun {j k} f ↦ ?_) (fun j ↦ ?_)
  · rw [show (V ⋙ Φ).map f = Φ.map (V.map f) from rfl, ← Φ.map_comp, hρ f]
  · have _ : Mono (ρ j) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (hmono j)
    have _ : Mono (Φ.map (ρ j)) := inferInstance
    exact inferInstance

/-- **The condition under which the limit of an inverse system of algebraic spaces is formed
inside the site.** Either the index category is small compared with the cofinality of the site's
size cutoff, its object type and its morphism types both, or the transition morphisms of the
system are monomorphisms. -/
def Space.IsSiteSmall (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type u}
    [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  (#I < B.cutoff.ord.cof ∧ ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) ∨
    ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (D.map f)

/-- An index category smaller than the cofinality of the site's size cutoff, morphism types
included, is small for the site. -/
theorem Space.IsSiteSmall.of_lt_cof {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) : Space.IsSiteSmall B S hS D :=
  Or.inl ⟨hSize, hHomSize⟩

/-- A system with monomorphic transition morphisms is small for the site, whatever its
index. -/
theorem Space.IsSiteSmall.of_mono {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (D.map f)) :
    Space.IsSiteSmall B S hS D :=
  Or.inr hmono

/-- **Smallness for the site survives a functor which preserves monomorphisms.** -/
theorem Space.IsSiteSmall.map {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {S' : Scheme.{u}} {hS' : B.Contains S'} {I : Type u} [Category.{u} I]
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Φ : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S' hS')ᵒᵖ ⥤ Type u))
    [Φ.PreservesMonomorphisms] (hb : Space.IsSiteSmall B S hS D) :
    Space.IsSiteSmall B S' hS' (D ⋙ Φ) := by
  rcases hb with h | hmono
  · exact Or.inl h
  refine .of_mono ?_
  intro i j f
  have _ := hmono f
  exact inferInstanceAs (Mono (Φ.map (D.map f)))

/-- An inverse system indexed by the opposite of a preorder smaller than the cofinality of the
site's size cutoff is small for the site. -/
theorem Space.IsSiteSmall.of_lt_cof_op {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {I : Type u} [Preorder I]
    {D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hSize : #I < B.cutoff.ord.cof) :
    Space.IsSiteSmall B S hS D :=
  .of_lt_cof
    ((Cardinal.mk_congr (Opposite.equivToOpposite (α := I))).symm.trans_lt hSize)
    fun _ _ ↦ (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- The limit of the diagram of schemes underlying a cofiltered diagram of affine objects of
the big fppf site of `S` lies in the site, under either alternative of
`AlgebraicGeometry.BigFppfOver.IsSiteSmallDiagram`. -/
private theorem contains_limit_underlying (V : J ⥤ BigFppfOver B S hS)
    [HasLimit (underlyingDiagram V)]
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) :
    schemeSizeBelow B.cutoff (limit (underlyingDiagram V)) := by
  rcases hJ with hJ | ⟨T, ρ, hρ, hmono⟩
  · exact Scheme.size_lt_of_isLimit_of_isAffine B.aleph0_lt_cutoff (underlyingDiagram V) hV hJ
      (fun j ↦ (V.obj j).left.property) (limit.isLimit (underlyingDiagram V))
  · obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
    have hρ' : ∀ {j k : J} (f : j ⟶ k),
        (underlyingDiagram V).map f ≫ (BigFppfOver.toScheme B S hS).map (ρ k) =
          (BigFppfOver.toScheme B S hS).map (ρ j) := by
      intro j k f
      show (BigFppfOver.toScheme B S hS).map (V.map f) ≫
        (BigFppfOver.toScheme B S hS).map (ρ k) = _
      rw [← Functor.map_comp, hρ f]
    have _ := CofilteredLimit.mono_π_app_comp
      (V := underlyingDiagram V) (fun j ↦ (BigFppfOver.toScheme B S hS).map (ρ j)) hρ' hmono
      (limit.isLimit (underlyingDiagram V)) j₀
    exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      ((limit.cone (underlyingDiagram V)).π.app j₀ ≫ (BigFppfOver.toScheme B S hS).map (ρ j₀))
      T.left.property

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the big fppf site of `S` which is small for
the site. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfIsSiteSmallDiagram (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  Limits.createsLimitFullSubcategoryInclusion _ (contains_limit_underlying V hV hJ)

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` which is small
for the site has a limit in the site. -/
theorem BigFppfOver.hasLimit_of_isAffine_of_isSiteSmallDiagram (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) : HasLimit V :=
  hasLimit_of_createsLimit V hV (createsLimitInclusionOfIsSiteSmallDiagram V hV hJ)

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of
affine objects of the big fppf site of `S` which is small for the site. -/
theorem BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  preservesLimit_toScheme_of_createsLimit V hV (createsLimitInclusionOfIsSiteSmallDiagram V hV hJ)

/-- The underlying scheme of the limit of a cofiltered inverse system of affine objects of
the big fppf site of `S` which is small for the site is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit_of_isSiteSmallDiagram (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  isAffine_toScheme_of_isLimit_of_createsLimit V hV
    (createsLimitInclusionOfIsSiteSmallDiagram V hV hJ) hc

/-! ### Limits of the underlying schemes lying in the site

Section 70.2 of the source (Stacks 07SD) assumes that every ring `A` it considers has `Spec(A)`
isomorphic to an object of the big fppf site. For a cofiltered diagram of affine objects of the
site this says that the limit of the underlying schemes lies in the site. -/

/-- The limit of the underlying schemes of a cofiltered diagram of affine objects of the big
fppf site of `S` lies in the site, at every limit cone. -/
def BigFppfOver.LimitInSite (V : J ⥤ BigFppfOver B S hS) : Prop :=
  ∀ c : Cone (underlyingDiagram V), IsLimit c → schemeSizeBelow B.cutoff c.pt

/-- **A diagram small for the site has the limit of its underlying schemes in the site.** -/
theorem BigFppfOver.IsSiteSmallDiagram.limitInSite {V : J ⥤ BigFppfOver B S hS}
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.IsSiteSmallDiagram V) : BigFppfOver.LimitInSite V := by
  intro c hc
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have h := contains_limit_underlying V hV hJ
  show c.pt.size < B.cutoff
  rwa [show c.pt.size = (limit (underlyingDiagram V)).size from
    Scheme.size_congr (hc.conePointUniqueUpToIso (limit.isLimit (underlyingDiagram V)))]

/-- The size-bounded subcategory of schemes creates the limit of a cofiltered diagram of affine
objects of the big fppf site of `S` whose limit of underlying schemes lies in the site. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfConvention (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  Limits.createsLimitFullSubcategoryInclusion _
    (hL (limit.cone (underlyingDiagram V)) (limit.isLimit (underlyingDiagram V)))

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` whose limit of
underlying schemes lies in the site has a limit in the site. -/
theorem BigFppfOver.hasLimit_of_isAffine_of_limitInSite (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) : HasLimit V :=
  hasLimit_of_createsLimit V hV (createsLimitInclusionOfConvention V hV hL)

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of affine
objects of the big fppf site of `S` whose limit of underlying schemes lies in the site. -/
theorem BigFppfOver.preservesLimit_toScheme_of_limitInSite (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  preservesLimit_toScheme_of_createsLimit V hV (createsLimitInclusionOfConvention V hV hL)

/-- The underlying scheme of the limit of a cofiltered inverse system of affine objects of the
big fppf site of `S` whose limit of underlying schemes lies in the site is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit_of_limitInSite (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
  isAffine_toScheme_of_isLimit_of_createsLimit V hV (createsLimitInclusionOfConvention V hV hL) hc

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of finite presentation -/

section FinitePresentation

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end FinitePresentation

/-! ### Base change of an inverse limit at a stage -/

section Limits

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- For every stage `i`, affine object `Z` of the site and morphism `g : yoneda Z ⟶ D i`, and
every lift `W` through the embedding of the big affine site into presheaves of the diagram of
base changes along `g` of the stages over `i`, the limit of the underlying schemes of `W` lies in
the site. -/
def SiteContainsBaseChangeLimits : Prop :=
  ∀ (i : I) (Z : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
    (W : Over i ⥤ BigAffineFppf B S hS),
    (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
      (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
    BigFppfOver.LimitInSite (W ⋙ BigAffineFppf.inclusion B S hS)

/-- **A system small for the site satisfies
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.** -/
theorem IsSiteSmall.siteContainsBaseChangeLimits (hb : IsSiteSmall B S hS D) :
    SiteContainsBaseChangeLimits B S hS D := by
  intro i Z g W hiso
  refine BigFppfOver.IsSiteSmallDiagram.limitInSite (fun k ↦ (W.obj k).property) ?_
  rcases hb with ⟨hSize, hHomSize⟩ | hmono
  · exact .of_lt_cof (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i)
  refine BigFppfOver.IsSiteSmallDiagram.of_mono_yoneda hiso
    ((BigAffineFppf.inclusion B S hS).obj Z)
    (fun k ↦ ((Over.post (X := i) D ⋙ Over.pullback g).obj k).hom)
    (fun {k l} f ↦ Over.w ((Over.post (X := i) D ⋙ Over.pullback g).map f)) (fun k ↦ ?_)
  have _ : Mono (D.map k.hom) := hmono k.hom
  exact (IsPullback.of_hasPullback (D.map k.hom) g).mono_snd_of_mono

/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic spaces
with affine transition morphisms is affine, provided the system satisfies
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. -/
@[stacks 07SF "part (1)"]
theorem isAffineHom_limitπ_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) : IsAffineHom B S hS (limit.π D i) := by
  refine isAffineHom_limitπ_of_hasLimit_isAffine B S hS D hAffine i fun Z g W hiso hWaff ↦ ?_
  have hL : BigFppfOver.LimitInSite (W ⋙ BigAffineFppf.inclusion B S hS) := hconv i Z g W hiso
  exact ⟨BigFppfOver.hasLimit_of_isAffine_of_limitInSite _ hWaff hL,
    fun hc ↦ BigFppfOver.isAffine_toScheme_of_isLimit_of_limitInSite _ hWaff hL hc⟩

/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic spaces
with affine transition morphisms is affine, provided the system is small for the site in the
sense of `AlgebraicGeometry.Space.IsSiteSmall`. -/
@[stacks 07SF "part (1)", sga "3 XI 4.3" "partial"]
theorem isAffineHom_limitπ_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) : IsAffineHom B S hS (limit.π D i) :=
  isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hAffine i

end Limits

end Space

end AlgebraicGeometry

end
