module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
import all StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Bounded charts and size bounds for the approximation steps

The declarations here restate, under weaker hypotheses or at more general universes, declarations
of `StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps`. Each carries the name of the
declaration it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a
definition), or the `SizeBound` variant of it.

## Main results

* `Scheme.size_lt_of_isLimit_of_isAffine_of_iSup_lt`
* `mk_over_lt_of_mk_lt`
* `iSup_size_underlyingDiagram`
* `BigFppfOver.SizeBound`
* `BigFppfOver.SizeBound.of_lt_cof_ord`
* `BigFppfOver.SizeBound.of_size_le`
* `BigFppfOver.SizeBound.size_le_iSup`
* `Space.ChartsBounded`
* `Space.ChartsBounded.comp`
* `Space.chartsBounded_of_lt_cof_ord`
* `Space.chartsBounded_of_size_le`
* `Space.chartsBounded_of_mk_lt_cof_ord_op`
* `BigFppfOver.hasLimit_of_isAffine_of_sizeBound`
* `BigFppfOver.preservesLimit_toScheme_of_sizeBound`
* `BigFppfOver.isAffine_toScheme_of_isLimit_of_sizeBound`
* `Space.isAffineHom_limitπ_of_chartsBounded`
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry

/-! ### The size of a limit of affine schemes -/

section AffineDiagram

variable {J : Type u} [Category.{u} J]

/-- A sigma type over fewer than `κ` indices, with the cardinalities of the fibres having a
supremum below `κ`, has cardinality below `κ`. -/
private theorem mk_sigma_lt_of_iSup_lt {ι : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hι : #ι < κ) {f : ι → Type u} (h : ⨆ j, #(f j) < κ) : #(Σ j, f j) < κ := by
  rw [Cardinal.mk_sigma]
  exact (Cardinal.sum_le_mk_mul_iSup _).trans_lt (Cardinal.mul_lt_of_lt hκ.le hι h)

/-- The cardinal size of a cofiltered limit of affine schemes is below `κ` as soon as the
index category has fewer objects than `κ` and the sizes of the stages have a supremum below
`κ`.

By Stacks 000P the size of an affine scheme is the cardinality of its ring of global
sections together with `ℵ₀`. The ring of global sections of the limit is the filtered
colimit of those of the stages, hence is covered by them, so its cardinality is at most the
sum over the index category of the cardinalities of the stages; that sum is a product of two
cardinals below `κ`, hence below `κ`.

The two hypotheses are what the sum needs, one for each factor, and together they are weaker
than the single hypothesis `#J < κ.ord.cof`, which implies both:
`AlgebraicGeometry.BigFppfOver.SizeBound.of_lt_cof_ord` bounds the supremum through
`Cardinal.iSup_lt_of_lt_cof_ord`, which needs a bound on the number of stages, whereas a
diagram whose stages are bounded by one cardinal below `κ` has the supremum outright and needs
no bound on their number beyond `#J < κ`. -/
theorem Scheme.size_lt_of_isLimit_of_isAffine_of_iSup_lt [IsCofiltered J] {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j))
    (hJ : #J < κ) (hsize : ⨆ j, (V.obj j).size < κ) {c : Cone V} (hc : IsLimit c) :
    c.pt.size < κ := by
  have hV' : ∀ j, IsAffine (V.obj j) := hV
  have hpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hΓ : ∀ j, #Γ(V.obj j, ⊤) ≤ ⨆ j, (V.obj j).size := by
    intro j
    have := hV j
    refine le_trans ?_ (le_ciSup Cardinal.bddAbove_of_small j)
    rw [Scheme.size_of_isAffine (V.obj j)]
    exact le_max_right _ _
  have h₁ : #Γ(c.pt, ⊤) ≤ #(Σ j : J, Γ(V.obj j, ⊤)) := by
    refine Cardinal.mk_le_of_surjective (f := fun p : Σ j : J, Γ(V.obj j, ⊤) =>
      show Γ(c.pt, ⊤) from (c.π.app p.1).appTop p.2) ?_
    intro x
    obtain ⟨j, y, hy⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit V c hc x
    exact ⟨⟨j, y⟩, hy⟩
  have h₂ : #(Σ j : J, Γ(V.obj j, ⊤)) < κ := by
    exact mk_sigma_lt_of_iSup_lt hκ hJ ((ciSup_le' hΓ).trans_lt hsize)
  rw [Scheme.size_of_isAffine c.pt]
  exact max_lt hκ (h₁.trans_lt h₂)

end AffineDiagram

/-! ### The size of a slice of the index category -/

section SliceSize

variable {I : Type u} [Category.{u} I]

/-- A slice of an index category with countable morphism types and fewer objects than an
uncountable cardinal `κ` is again smaller than `κ`: the slice injects into the pairs
consisting of an object and a morphism from it to the base, and that is a product of `#I`
with a countable supremum.

This is `AlgebraicGeometry.mk_over_lt` with the bound on the objects of the index category
weakened from `#I < κ.ord.cof` to `#I < κ`, which is possible because the conclusion is
weakened in the same way. The morphism hypothesis is the one every call site in this
development discharges, the index categories here being preorders. -/
theorem mk_over_lt_of_mk_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hI : #I < κ)
    (hhom : ∀ j j' : I, #(j ⟶ j') ≤ ℵ₀) (i : I) : #(Over i) < κ := by
  exact (mk_over_le i).trans_lt
    (mk_sigma_lt_of_iSup_lt hκ hI ((ciSup_le' fun j => hhom j i).trans_lt hκ))

end SliceSize

/-! ### Cofiltered limits of affine objects of the big fppf site -/

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

omit [IsCofiltered J] in
/-- The supremum of the sizes of the objects of a diagram in the big fppf site of `S` is the
supremum of the sizes of the objects of the diagram of schemes underlying it. -/
theorem iSup_size_underlyingDiagram (V : J ⥤ BigFppfOver B S hS) :
    ⨆ j, ((underlyingDiagram V).obj j).size
      = ⨆ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size := rfl

/-- **The size bound under which a diagram in the big fppf site of `S` has a limit there:**
the index category has fewer objects than the site's size cutoff, and the sizes of the
objects of the diagram have a supremum below that cutoff.

The limit of the diagram is formed in schemes, where its ring of global sections is covered
by those of the stages; the two conditions bound the two factors of the resulting sum, which
is what `AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine_of_iSup_lt` consumes.

The pair is weaker than the single hypothesis `#J < B.cutoff.ord.cof`, which implies it
through `AlgebraicGeometry.BigFppfOver.SizeBound.of_lt_cof_ord`: the cofinality hypothesis
bounds the supremum of the sizes through `Cardinal.iSup_lt_of_lt_cof_ord`, which needs a bound
on the *number* of objects, whereas a diagram all of whose objects are bounded by one cardinal
below the cutoff has that supremum outright and needs no bound on their number beyond
`#J < B.cutoff`. This is the same trade as the one
`AlgebraicGeometry.BigFppfSite.contains_glueData_glued_of_le_power` makes for gluing data. -/
structure BigFppfOver.SizeBound (V : J ⥤ BigFppfOver B S hS) : Prop where
  /-- The index category has fewer objects than the site's size cutoff. -/
  mk_lt : #J < B.cutoff
  /-- The sizes of the objects of the diagram have a supremum below the cutoff. -/
  iSup_size_lt : ⨆ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size < B.cutoff

namespace BigFppfOver.SizeBound

omit [IsCofiltered J] in
/-- A diagram indexed by a category with fewer objects than the cofinality of the site's size
cutoff is size-bounded. Every object of the site has size below the cutoff, and the
cofinality hypothesis carries that bound to the supremum. -/
theorem of_lt_cof_ord (V : J ⥤ BigFppfOver B S hS) (hJ : #J < B.cutoff.ord.cof) :
    BigFppfOver.SizeBound V where
  mk_lt := hJ.trans_le (Ordinal.cof_ord_le B.cutoff)
  iSup_size_lt :=
    Cardinal.iSup_lt_of_lt_cof_ord hJ fun j => (V.obj j).left.property

omit [IsCofiltered J] in
/-- A diagram whose objects are bounded by one cardinal below the site's size cutoff, indexed
by a category with fewer objects than the cutoff, is size-bounded. This is the half of the
pair that no bound on the number of objects can supply. -/
theorem of_size_le (V : J ⥤ BigFppfOver B S hS) (hJ : #J < B.cutoff)
    {mu : Cardinal.{u}} (hmu : mu < B.cutoff)
    (hV : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ mu) :
    BigFppfOver.SizeBound V where
  mk_lt := hJ
  iSup_size_lt := (ciSup_le' hV).trans_lt hmu

omit [IsCofiltered J] in
/-- Each object of a size-bounded diagram is bounded by the supremum the bound provides. -/
theorem size_le_iSup {V : J ⥤ BigFppfOver B S hS} (_h : BigFppfOver.SizeBound V) (j : J) :
    ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size
      ≤ ⨆ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size :=
  le_ciSup Cardinal.bddAbove_of_small j

end BigFppfOver.SizeBound

/-! ### Bounded charts of an inverse system of algebraic spaces -/

namespace Space

section ChartsBoundedSection

variable {I : Type u} [Category.{u} I]
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (D) in
/-- **The size bound the chart systems of a cofiltered system of algebraic spaces need.** The
index type is smaller than the site's size cutoff, its slices are too, and for every stage and
every affine scheme-valued point of that stage one cardinal below the cutoff bounds every
object of the site representing a base change of that point along a transition morphism into
the stage.

The bound is stated on the base changes themselves rather than on a chosen chart system, which
makes it invariant under reindexing the system
(`AlgebraicGeometry.Space.ChartsBounded.comp`) and under base change
along a morphism to the distinguished stage. What it is *for* is
`AlgebraicGeometry.Space.ChartsBounded.sizeBound`: every chart system of the system is then
size-bounded in the sense of `AlgebraicGeometry.BigFppfOver.SizeBound`, which is what
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge` consumes, and through it what keeps the
limits of the affine charts inside the site.

Two different hypotheses supply this, and the cardinal being allowed to depend on the stage and
on the scheme-valued point is exactly what makes both available:
`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord` from `#I < B.cutoff.ord.cof`, where the
supremum over the stages of the sizes of the base changes stays below the cutoff by
`Cardinal.iSup_lt_of_lt_cof_ord`; and `AlgebraicGeometry.Space.chartsBounded_of_size_le` from
`#I < B.cutoff` together with a cardinal bounding the base changes directly, which asks nothing
of the number of stages. -/
structure ChartsBounded : Prop where
  /-- The index type is smaller than the site's size cutoff. -/
  mk_lt : #I < B.cutoff
  /-- Every slice of the index category is smaller than the site's size cutoff. -/
  mk_over_lt : ∀ i : I, #(Over i) < B.cutoff
  /-- The base changes of an affine scheme-valued point of a stage along the transition
  morphisms into that stage are bounded by a single cardinal below the cutoff. -/
  bound : ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀),
      ∃ mu < B.cutoff, ∀ (j : I) (a : j ⟶ i₀) (W : BigFppfOver B S hS),
        (yoneda.obj W ≅ pullback (D.map a) f₀) →
          ((BigFppfOver.toScheme B S hS).obj W).size ≤ mu

namespace ChartsBounded

variable {B S hS}

/-- Reindexing a system along a functor preserves boundedness of the charts: the transition
morphisms of the reindexed system are transition morphisms of the original one, so the same
cardinals serve. The two conditions on the index category are about the new index category and
are supplied separately. -/
theorem comp {J : Type u} [Category.{u} J] (h : ChartsBounded B S hS D) (F : J ⥤ I)
    (hJ : #J < B.cutoff) (hJover : ∀ j : J, #(Over j) < B.cutoff) :
    ChartsBounded B S hS (F ⋙ D) where
  mk_lt := hJ
  mk_over_lt := hJover
  bound := fun j₀ U₀ f₀ => by
    obtain ⟨mu, hmu, hb⟩ := h.bound (F.obj j₀) U₀ f₀
    exact ⟨mu, hmu, fun j a W e => hb (F.obj j) (F.map a) W e⟩

end ChartsBounded

variable (D) in
/-- A system indexed by a category with fewer objects than the cofinality of the site's size
cutoff, and with morphism types below that cofinality, has bounded charts: the base changes of
a fixed scheme-valued point along the transition morphisms into its stage are indexed by the
stages and their morphisms, so their supremum stays below the cutoff by
`Cardinal.iSup_lt_of_lt_cof_ord`. -/
theorem chartsBounded_of_lt_cof_ord (hI : #I < B.cutoff.ord.cof)
    (hhom : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) : ChartsBounded B S hS D where
  mk_lt := hI.trans_le (Ordinal.cof_ord_le B.cutoff)
  mk_over_lt := fun i =>
    (mk_over_lt B.aleph0_lt_cutoff_cof hI hhom i).trans_le (Ordinal.cof_ord_le B.cutoff)
  bound := fun i₀ U₀ f₀ => by
    classical
    -- the size of a representing object of a base change, by a choice of one where it exists;
    -- the choice is harmless because all representing objects are isomorphic
    set P : Over i₀ → Cardinal.{u} := fun j =>
      if h : ∃ W : BigFppfOver B S hS, Nonempty (yoneda.obj W ≅ pullback (D.map j.hom) f₀)
        then ((BigFppfOver.toScheme B S hS).obj h.choose).size else 0 with hP
    have hPlt : ∀ j, P j < B.cutoff := by
      intro j
      by_cases h : ∃ W : BigFppfOver B S hS, Nonempty (yoneda.obj W ≅ pullback (D.map j.hom) f₀)
      · simp only [hP, dite_eq_left h]
        exact h.choose.left.property
      · simp only [hP, dite_eq_right h]
        exact lt_of_le_of_lt zero_le B.aleph0_lt_cutoff
    refine ⟨⨆ j : Over i₀, P j,
      Cardinal.iSup_lt_of_lt_cof_ord
        (mk_over_lt B.aleph0_lt_cutoff_cof hI hhom i₀) hPlt,
      fun j a W e => ?_⟩
    have h : ∃ W' : BigFppfOver B S hS,
        Nonempty (yoneda.obj W' ≅ pullback (D.map (Over.mk a).hom) f₀) := ⟨W, ⟨e⟩⟩
    have hsz : ((BigFppfOver.toScheme B S hS).obj W).size = P (Over.mk a) := by
      simp only [hP, dite_eq_left h]
      exact Scheme.size_congr ((BigFppfOver.toScheme B S hS).mapIso
        (Yoneda.fullyFaithful.preimageIso (e.trans h.choose_spec.some.symm)))
    rw [hsz]
    exact le_ciSup Cardinal.bddAbove_of_small (Over.mk a)

variable (D) in
/-- A system indexed by a category whose slices are smaller than the site's size cutoff, and
whose base changes of each affine scheme-valued point along the transition morphisms are
bounded by a single cardinal below the cutoff, has bounded charts.

This is the route that asks nothing of the *number* of stages beyond `#I < B.cutoff`. -/
theorem chartsBounded_of_size_le (hI : #I < B.cutoff)
    (hIover : ∀ i : I, #(Over i) < B.cutoff)
    (hC : ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀),
      ∃ mu < B.cutoff, ∀ (j : I) (a : j ⟶ i₀) (W : BigFppfOver B S hS),
        (yoneda.obj W ≅ pullback (D.map a) f₀) →
          ((BigFppfOver.toScheme B S hS).obj W).size ≤ mu) :
    ChartsBounded B S hS D where
  mk_lt := hI
  mk_over_lt := hIover
  bound := hC

end ChartsBoundedSection

section ChartsBoundedPreorder

variable {I : Type u} [Preorder I] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An inverse system indexed by the opposite of a preorder smaller than the cofinality of the
site's size cutoff has bounded charts. The bound on the morphism types that
`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord` also asks for is automatic, the morphisms
of a preorder being subsingletons and `ℵ₀` lying below that cofinality. -/
theorem chartsBounded_of_mk_lt_cof_ord_op
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hI : #I < B.cutoff.ord.cof) :
    ChartsBounded B S hS D :=
  chartsBounded_of_lt_cof_ord B S hS D
    (by rwa [Cardinal.mk_congr
      (show Iᵒᵖ ≃ I from ⟨Opposite.unop, Opposite.op, fun _ ↦ rfl, fun _ ↦ rfl⟩)])
    fun _ _ => (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

end ChartsBoundedPreorder

end Space

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the big fppf site of `S`: that limit
is affine, and Stacks 000P together with 000R (9) bound its size by the site's cutoff. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfSizeBound (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.SizeBound V) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have hsize : schemeSizeBelow B.cutoff (limit (underlyingDiagram V)) :=
    Scheme.size_lt_of_isLimit_of_isAffine_of_iSup_lt B.aleph0_lt_cutoff (underlyingDiagram V) hV
      hJ.mk_lt ((iSup_size_underlyingDiagram V).trans_lt hJ.iSup_size_lt)
      (limit.isLimit (underlyingDiagram V))
  Limits.createsLimitFullSubcategoryInclusion _ hsize

/-- The diagram of a size-bounded cofiltered inverse system of affine objects in the underlying
schemes of the site has a limit there, created by the inclusion of the size-bounded schemes. -/
private theorem hasLimit_forget_of_sizeBound (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.SizeBound V) : HasLimit (V ⋙ BigFppfOver.forget B S hS) :=
  have _hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have _hcr := createsLimitInclusionOfSizeBound V hV hJ
  hasLimit_of_created _ B.inclusion

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` which is
size-bounded has a limit in the site.

The limit is formed in schemes, where it is affine of size below the cutoff, so it is an
object of the size-bounded subcategory, which therefore creates the limit; the slice over
`S` creates it in turn because a cofiltered index category is connected. -/
theorem BigFppfOver.hasLimit_of_isAffine_of_sizeBound (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.SizeBound V) : HasLimit V := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have := hasLimit_forget_of_sizeBound V hV hJ
  exact hasLimit_of_created V (Over.forget (B.obj hS))

/-- The underlying scheme functor preserves the limit of a size-bounded cofiltered inverse
system of affine objects of the big fppf site of `S`. -/
theorem BigFppfOver.preservesLimit_toScheme_of_sizeBound (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.SizeBound V) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have hlim : HasLimit (underlyingDiagram V) := hasLimit_underlying V hV
  have := hasLimit_forget_of_sizeBound V hV hJ
  have := createsLimitInclusionOfSizeBound V hV hJ
  infer_instance

/-- The underlying scheme of the limit of a size-bounded cofiltered inverse system of affine
objects of the big fppf site of `S` is affine. -/
theorem BigFppfOver.isAffine_toScheme_of_isLimit_of_sizeBound (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : BigFppfOver.SizeBound V) {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := by
  have := BigFppfOver.preservesLimit_toScheme_of_sizeBound V hV hJ
  have haff : ∀ j, IsAffine ((V ⋙ BigFppfOver.toScheme B S hS).obj j) := hV
  exact Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (BigFppfOver.toScheme B S hS) hc)

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of finite presentation -/

/-! ### Base change of an inverse limit at a stage -/

section Limits

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 07SF, part (1).** Every projection from the inverse limit of a cofiltered
inverse system of algebraic spaces with affine transition morphisms is affine, provided the
charts of the system are bounded in the sense of
`AlgebraicGeometry.Space.ChartsBounded`.

Fix a stage `i`, an affine object `Z` of the site and a scheme-valued point
`g : yoneda Z ⟶ D i`. By part (2), the base change of `limit.π D i` along `g` is the
inverse limit over the stages `k ⟶ i` of the base changes of `D k` along `g`, and each of
those is represented by an affine object of the site because the transition morphism
`D k ⟶ D i` is affine. Representing objects are unique up to canonical isomorphism, so the
inverse system of base changes lifts through the fully faithful embedding of the big affine
site into presheaves; the lifted system is a cofiltered system of affine objects of the
site indexed by the slice over `i`, hence has a limit in the site whose underlying scheme
is affine. Yoneda preserves limits, so that limit represents the base change. -/
@[sga "3 XI 4.3" "partial"]
theorem isAffineHom_limitπ_of_chartsBounded (hI : ChartsBounded B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) : IsAffineHom B S hS (limit.π D i) := by
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
    fun k => (W.obj k).property
  have hJ : BigFppfOver.SizeBound W' := by
    obtain ⟨mu, hmu, hb⟩ := hI.bound i Z g
    exact .of_size_le _ (hI.mk_over_lt i) hmu
      fun k => hb k.left k.hom (W'.obj k) (hiso.app k)
  have hlim : HasLimit W' := BigFppfOver.hasLimit_of_isAffine_of_sizeBound W' hWaff hJ
  have hLaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (limit W')) :=
    BigFppfOver.isAffine_toScheme_of_isLimit_of_sizeBound W' hWaff hJ (limit.isLimit W')
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

end Limits

end Space

end AlgebraicGeometry

end
