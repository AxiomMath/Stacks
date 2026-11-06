module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The comparison of formal schemes with formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `𝔛` be a formal scheme à la EGA.
Stacks 0AIR compares `𝔛` with the formal algebraic space its functor of points defines. The
remark has five clauses, and this file carries the four of them that concern the open covering
and the embedding; the first, that `h_𝔛` is an fppf sheaf, is
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`, proved for an
arbitrary formal scheme and an arbitrary base in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonSheaf`.

*The open covering.* An open `𝔘` of `𝔛` whose restriction is again a formal scheme gives an
open formal subscheme `𝔛|_𝔘` and a chart `h_{𝔛|_𝔘} ⟶ h_𝔛`. The base change of that chart
along a point `g` of `𝔛` over a test object `T` of the big fppf site is the open subscheme
`g⁻¹(𝔘)` of `T`: a point of `𝔛` whose image lies in `𝔘` factors uniquely through `𝔛|_𝔘`, and
an open subscheme of an object of the site is again one. That identification is
`AlgebraicGeometry.FormalSpace.isPullback_chart`, and clause (4) of the source — that the charts
are representable and open immersions — follows from it with no hypothesis at all.

*The embedding.* Over a terminal base — the source assumes the base is `Spec(ℤ)` — an object of
the big fppf category over `S` is a scheme of the site with its unique structure morphism, so a
transformation of functors of points on the big fppf site of `S` is a transformation on the
schemes of size below the cutoff of the site. Stacks 0AI1 there gives clause (2): the assignment
`𝔛 ↦ h_𝔛` is fully faithful on the formal schemes whose affine chart quotients belong to the
site. Together with clause (5) this is the opening sentence of the source, that formal schemes
form a full subcategory of formal algebraic spaces.

## Main definitions

* `AlgebraicGeometry.openFormalSubscheme` and `AlgebraicGeometry.openFormalSubschemeHom`: the
  open formal subscheme `𝔛|_𝔘` and its open immersion into `𝔛`.
* `AlgebraicGeometry.FormalSpace.openFormalSubschemeSheafHom`: the chart
  `h_{𝔛|_𝔘} ⟶ h_𝔛` of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.chartObject` and `AlgebraicGeometry.FormalSpace.chartHom`: the
  open subscheme `g⁻¹(𝔘)` of a test object and its open immersion, which represent the base
  change of the chart.
* `AlgebraicGeometry.FormalSpace.Space.openImmersionPropertyULift`: being an open immersion, as
  a property of morphisms of algebraic spaces with values one universe up.
* `AlgebraicGeometry.FormalSpace.comparableFormalSchemes`: the formal schemes the comparison
  applies to.

## Main results

* `AlgebraicGeometry.FormalSpace.fullyFaithfulComparableFormalSchemePointsFunctor`:
  **Stacks 0AIR**, the comparison — the formal schemes the remark applies to form a full
  subcategory of the formal algebraic spaces over `S`.
* `AlgebraicGeometry.FormalSpace.fullyFaithfulFormalSchemePointsFppfSheafFunctor`:
  **Stacks 0AIR**, clause (2) — `𝔛 ↦ h_𝔛` is a fully faithful embedding into the fppf sheaves
  on the big fppf site of `S`.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_openFormalSubschemePoints`:
  **Stacks 0AIR**, clause (3) — the charts of an affine open covering have affine formal
  algebraic space functors of points.
* `AlgebraicGeometry.FormalSpace.relative_isOpenImmersion_openFormalSubschemePresheafHom`:
  **Stacks 0AIR**, clause (4) — the charts `h_{𝔛|_𝔘} ⟶ h_𝔛` are representable and open
  immersions, with no hypothesis.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpaceFormalSchemePoints_of_affineCover`:
  **Stacks 0AIR**, clause (5) — `h_𝔛` is a formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_openFormalSubschemeSheafHom`: the
  charts of an open covering are jointly surjective, the third condition of Definition 0AIM.

## Implementation notes

Clause (4) is proved by exhibiting the pullback square by hand rather than by computing the
fibre product of presheaves: the universal property is verified on a general cone, whose lift to
`g⁻¹(𝔘)` is the factorisation of `AlgebraicGeometry.FormalSpace.existsUnique_chartLift` applied
elementwise, with naturality and the two factorisations coming from the uniqueness of that
factorisation and from the chart being a monomorphism.

Clauses (2), (3) and (5) carry the hypotheses the source states: `hterm`, that the base scheme
is terminal, which is the source's "we assume our base scheme is `Spec(ℤ)`"; the size condition
of Stacks 0AI1 at the cutoff of the site, and the set-theoretic condition of Stacks 0AIS on the
functor of points, which together are the source's "modulo set theoretic issues". Clauses (1)
and (4) need none of them.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIR](https://stacks.math.columbia.edu/tag/0AIR)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The image of the inclusion of an open subspace of a locally topologically ringed space is
that open subset. -/
theorem range_ofRestrict_base {X : LTRS.{u}} (V : Opens X) :
    Set.range (X.ofRestrict V).toHom.base = (V : Set X) := by
  simp only [LocallyTopologicallyRingedSpace.ofRestrict_toHom,
    PresheafedSpace.ofRestrict_base]
  exact Subtype.range_val

/-- A morphism into `X.restrict V`, followed by the inclusion, has image inside `V`. -/
private theorem base_comp_ofRestrict_mem {Z X : LTRS.{u}} (V : Opens X) (l : Z ⟶ X.restrict V)
    (z : Z) : (l ≫ X.ofRestrict V).toHom.base z ∈ V := by
  exact (range_ofRestrict_base V).le ⟨l.toHom.base z, rfl⟩

/-- **A morphism into `X` whose image lies in an open `V` factors uniquely through `X|_V`.**
Existence is `AlgebraicGeometry.liftToRestrict`; uniqueness holds because the inclusion of an
open subspace is an open immersion of presheafed spaces, hence a monomorphism. -/
theorem existsUnique_comp_ofRestrict {Z X : LTRS.{u}} (V : Opens X) (g : Z ⟶ X)
    (hg : ∀ z : Z, g.toHom.base z ∈ V) :
    ∃! l : Z ⟶ X.restrict V, l ≫ X.ofRestrict V = g := by
  have hrange : Set.range g.toHom.base ⊆ Set.range (X.ofRestrict V).toHom.base := by
    rw [range_ofRestrict_base]
    exact fun _ ⟨z, hz⟩ => hz ▸ hg z
  refine ⟨liftToRestrict V g hrange, liftToRestrict_comp_ofRestrict V g hrange, fun l hl => ?_⟩
  refine LocallyTopologicallyRingedSpace.Hom.ext' ?_
  have h2 := congrArg LocallyTopologicallyRingedSpace.Hom.toHom hl
  rw [LocallyTopologicallyRingedSpace.comp_toHom] at h2
  exact PresheafedSpace.IsOpenImmersion.lift_uniq (X.ofRestrict V).toHom g.toHom hrange
    l.toHom h2

/-- The open formal subscheme `𝔛|_𝔘` of a formal scheme `𝔛` cut out by an open `𝔘` whose
restriction is again a formal scheme. These are the members `𝔛_i` of the open covering chosen in
Stacks 0AIR. -/
def openFormalSubscheme (X : FormalScheme.{u}) (V : Opens X.obj)
    (hV : IsFormalScheme (X.obj.restrict V)) : FormalScheme.{u} := ⟨X.obj.restrict V, hV⟩

/-- The open immersion `𝔛|_𝔘 ⟶ 𝔛` of formal schemes. -/
def openFormalSubschemeHom (X : FormalScheme.{u}) (V : Opens X.obj)
    (hV : IsFormalScheme (X.obj.restrict V)) : openFormalSubscheme X V hV ⟶ X :=
  ObjectProperty.homMk (X.obj.ofRestrict V)

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FormalScheme.{u})
  (V : Opens X.obj) (T : BigFppfOver B S hS)
  (x : (formalSchemeFppfPresheaf B S hS X).obj (op T))

/-- The open subscheme `g⁻¹(𝔘)` of a test object `T` of the big fppf site cut out by a point
`g` of `𝔛` over `T`. It is the base change of `𝔛|_𝔘` along that point. -/
def chartOpens : ((BigFppfOver.toScheme B S hS).obj T).Opens :=
  Opens.comap x.down.hom.toHom.base.hom V

/-- The open subscheme `g⁻¹(𝔘)` of a test object belongs to the big fppf site: the source of an
open immersion into an object of the site is an object of the site. -/
theorem contains_chartOpens : B.Contains ((chartOpens B S hS X V T x : Scheme.{u})) :=
  B.contains_coe_opens T.left.property (chartOpens B S hS X V T x)

/-- The open subscheme `g⁻¹(𝔘)` as an object of the big fppf category over `S`, with the
structure morphism it inherits from `T`. -/
abbrev chartObject : BigFppfOver B S hS :=
  siteObject B S hS (contains_chartOpens B S hS X V T x)
    ((chartOpens B S hS X V T x).ι ≫ B.inclusion.map T.hom)

/-- The open immersion `g⁻¹(𝔘) ⟶ T` in the big fppf category over `S`. -/
def chartHom : chartObject B S hS X V T x ⟶ T :=
  Over.homMk (ObjectProperty.homMk (chartOpens B S hS X V T x).ι) rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.FormalSpace.chartHom` is the
inclusion of the open subscheme. -/
theorem toScheme_map_chartHom :
    (BigFppfOver.toScheme B S hS).map (chartHom B S hS X V T x) =
      (chartOpens B S hS X V T x).ι := rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.FormalSpace.chartHom` is an open
immersion. -/
instance isOpenImmersion_toScheme_map_chartHom :
    IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (chartHom B S hS X V T x)) := by
  rw [toScheme_map_chartHom]; infer_instance

/-- A morphism `W ⟶ T` of the big fppf site whose image lies in `g⁻¹(𝔘)` factors uniquely
through `g⁻¹(𝔘)`; the factorisation is a morphism over `S` because it is one after composition
with the monomorphism `g⁻¹(𝔘) ⟶ T`. -/
theorem existsUnique_chartLift {W : BigFppfOver B S hS} (a : W ⟶ T)
    (ha : ∀ w, ((BigFppfOver.toScheme B S hS).map a).base w ∈ chartOpens B S hS X V T x) :
    ∃! c : W ⟶ chartObject B S hS X V T x, c ≫ chartHom B S hS X V T x = a := by
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map a).base ⊆
      Set.range ((chartOpens B S hS X V T x).ι).base := by
    rw [Scheme.Opens.range_ι]
    exact fun _ ⟨w, hw⟩ => hw ▸ ha w
  set c0 := IsOpenImmersion.lift ((chartOpens B S hS X V T x).ι)
    ((BigFppfOver.toScheme B S hS).map a) hrange with hc0def
  have hc0 : c0 ≫ (chartOpens B S hS X V T x).ι = (BigFppfOver.toScheme B S hS).map a :=
    IsOpenImmersion.lift_fac _ _ hrange
  have hfaith : Function.Injective
      (fun k : W ⟶ chartObject B S hS X V T x => (BigFppfOver.toScheme B S hS).map k) :=
    fun _ _ h => (BigFppfOver.toScheme B S hS).map_injective h
  refine ⟨Over.homMk (ObjectProperty.homMk c0) ?_, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    show c0 ≫ ((chartOpens B S hS X V T x).ι ≫ B.inclusion.map T.hom) = _
    rw [← Category.assoc, hc0]
    exact congrArg B.inclusion.map (Over.w a)
  · refine Over.OverMorphism.ext ?_
    apply ObjectProperty.hom_ext
    exact hc0
  · intro c hc
    refine hfaith ?_
    refine IsOpenImmersion.lift_uniq ((chartOpens B S hS X V T x).ι)
      ((BigFppfOver.toScheme B S hS).map a) hrange _ ?_
    rw [← toScheme_map_chartHom B S hS X V T x, ← Functor.map_comp, hc]

/-- the unique factorization through the chart -/
def chartLift' {W : BigFppfOver B S hS} (a : W ⟶ T)
    (ha : ∀ w, ((BigFppfOver.toScheme B S hS).map a).base w ∈ chartOpens B S hS X V T x) :
    W ⟶ chartObject B S hS X V T x :=
  (existsUnique_chartLift B S hS X V T x a ha).choose

/-- The chosen factorisation does factor the given morphism. -/
theorem chartLift_comp_chartHom {W : BigFppfOver B S hS} (a : W ⟶ T)
    (ha : ∀ w, ((BigFppfOver.toScheme B S hS).map a).base w ∈ chartOpens B S hS X V T x) :
    chartLift' B S hS X V T x a ha ≫ chartHom B S hS X V T x = a :=
  (existsUnique_chartLift B S hS X V T x a ha).choose_spec.1

/-- The factorisation through `g⁻¹(𝔘)` is unique. -/
theorem eq_chartLift {W : BigFppfOver B S hS} (a : W ⟶ T)
    (ha : ∀ w, ((BigFppfOver.toScheme B S hS).map a).base w ∈ chartOpens B S hS X V T x)
    (c : W ⟶ chartObject B S hS X V T x) (hc : c ≫ chartHom B S hS X V T x = a) :
    c = chartLift' B S hS X V T x a ha :=
  (existsUnique_chartLift B S hS X V T x a ha).choose_spec.2 c hc

/-- **The geometric step.** If the point of `𝔛` that a morphism `a : W ⟶ T` of the site induces
factors through `𝔛|_𝔘`, then the image of `a` lies in `g⁻¹(𝔘)`: the image of the inclusion
`𝔛|_𝔘 ⟶ 𝔛` is `𝔘`. -/
theorem mem_chartOpens_of_lift (hV : IsFormalScheme (X.obj.restrict V))
    {W : BigFppfOver B S hS} (a : W ⟶ T)
    (b : schemeToFormalScheme.obj ((BigFppfOver.toScheme B S hS).obj W) ⟶
      openFormalSubscheme X V hV)
    (hb : b ≫ openFormalSubschemeHom X V hV =
      schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map a) ≫ x.down) :
    ∀ w, ((BigFppfOver.toScheme B S hS).map a).base w ∈ chartOpens B S hS X V T x := by
  intro w
  have hbase := congrArg (fun k => k.hom.toHom.base) hb
  have h2 : (X.obj.ofRestrict V).toHom.base (b.hom.toHom.base w)
      = x.down.hom.toHom.base (((BigFppfOver.toScheme B S hS).map a).base w) :=
    congrFun (congrArg (fun k : _ ⟶ _ => (ConcreteCategory.hom k : _ → _)) hbase) w
  show x.down.hom.toHom.base (((BigFppfOver.toScheme B S hS).map a).base w) ∈ V
  rw [← h2]
  exact base_comp_ofRestrict_mem V b.hom w

section Point

/-- Equal maps of types into a lifted type have equal values, read through `ULift.down`. -/
private theorem down_apply_eq_of_eq {α : Type (u + 1)} {β : Type u} {f g : α ⟶ ULift.{u + 1} β}
    (h : f = g) (a : α) : (f a).down = (g a).down :=
  congrArg ULift.down (ConcreteCategory.congr_hom h a)

variable (hV : IsFormalScheme (X.obj.restrict V))

/-- A point of `g⁻¹(𝔘)` is carried into `𝔘` by the point `g` of `𝔛`, by the definition of
`AlgebraicGeometry.FormalSpace.chartOpens`. -/
theorem mem_chartOpens_apply
    (z : ((BigFppfOver.toScheme B S hS).obj (chartObject B S hS X V T x) : Type u)) :
    ((schemeToFormalScheme.map (chartOpens B S hS X V T x).ι ≫ x.down).hom).toHom.base z ∈ V :=
  z.2

/-- The point of `𝔛|_𝔘` over `g⁻¹(𝔘)` obtained by factoring the restriction of `g` to `g⁻¹(𝔘)`
through the open immersion `𝔛|_𝔘 ⟶ 𝔛`. -/
def chartFormalHom :
    schemeToFormalScheme.obj ((BigFppfOver.toScheme B S hS).obj
      (chartObject B S hS X V T x)) ⟶ openFormalSubscheme X V hV :=
  ObjectProperty.homMk (existsUnique_comp_ofRestrict V
    ((schemeToFormalScheme.map (chartOpens B S hS X V T x).ι ≫ x.down).hom)
    (mem_chartOpens_apply B S hS X V T x)).choose

/-- That point does factor the restriction of `g`. -/
theorem chartFormalHom_comp :
    chartFormalHom B S hS X V T x hV ≫ openFormalSubschemeHom X V hV =
      schemeToFormalScheme.map (chartOpens B S hS X V T x).ι ≫ x.down :=
  ObjectProperty.hom_ext _ (existsUnique_comp_ofRestrict V
    ((schemeToFormalScheme.map (chartOpens B S hS X V T x).ι ≫ x.down).hom)
    (mem_chartOpens_apply B S hS X V T x)).choose_spec.1

/-- Two morphisms of formal schemes into `𝔛|_𝔘` agreeing after the inclusion `𝔛|_𝔘 ⟶ 𝔛` are
equal: that inclusion is a monomorphism. -/
theorem eq_of_comp_openFormalSubschemeHom {Z : FormalScheme.{u}}
    {p q : Z ⟶ openFormalSubscheme X V hV}
    (h : p ≫ openFormalSubschemeHom X V hV = q ≫ openFormalSubschemeHom X V hV) : p = q := by
  have hu := existsUnique_comp_ofRestrict V (p ≫ openFormalSubschemeHom X V hV).hom
    (base_comp_ofRestrict_mem V p.hom)
  apply ObjectProperty.hom_ext
  refine (hu.choose_spec.2 p.hom rfl).trans (hu.choose_spec.2 q.hom ?_).symm
  exact (congrArg (fun k : Z ⟶ X => k.hom) h).symm

/-- The morphism `h_{𝔛|_𝔘} ⟶ h_𝔛` of fppf sheaves on the big fppf site of `S` induced by the
open immersion `𝔛|_𝔘 ⟶ 𝔛`. These are the arrows `h_{𝔛_i} ⟶ h_𝔛` of Stacks 0AIR. -/
def openFormalSubschemeSheafHom :
    formalSchemePointsFppfSheaf B S hS (openFormalSubscheme X V hV) ⟶
      formalSchemePointsFppfSheaf B S hS X :=
  (formalSchemePointsFppfSheafFunctor B S hS).map (openFormalSubschemeHom X V hV)

/-- The same morphism read on the underlying presheaves, which is the form in which the
representability of the arrow is tested. -/
def openFormalSubschemePresheafHom :
    formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV) ⟶
      formalSchemeFppfPresheaf B S hS X :=
  (formalSchemeFppfPresheafFunctor B S hS).map (openFormalSubschemeHom X V hV)

/-- The underlying morphism of presheaves of the chart inclusion of fppf sheaves. -/
theorem openFormalSubschemeSheafHom_hom :
    (openFormalSubschemeSheafHom B S hS X V hV).hom
      = openFormalSubschemePresheafHom B S hS X V hV :=
  hom_map_formalSchemePointsFppfSheafFunctor B S hS (openFormalSubschemeHom X V hV)

/-- The chart inclusion acts on points by composition with the open immersion
`𝔛|_𝔘 ⟶ 𝔛`. -/
theorem app_openFormalSubschemePresheafHom (W : BigFppfOver B S hS)
    (b : (formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV)).obj (op W)) :
    (openFormalSubschemePresheafHom B S hS X V hV).app (op W) b
      = ULift.up (b.down ≫ openFormalSubschemeHom X V hV) := rfl

/-- The chart inclusion is a monomorphism of presheaves: it is injective on points over every
object of the site. -/
theorem mono_openFormalSubschemePresheafHom :
    Mono (openFormalSubschemePresheafHom B S hS X V hV) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun W => ?_
  refine (mono_iff_injective _).2 fun b₁ b₂ h => ?_
  exact ULift.ext (eq_of_comp_openFormalSubschemeHom X V hV (congrArg ULift.down h))

/-- The morphism of presheaves that Yoneda's lemma attaches to a point `g` of `𝔛` over `T`
sends a morphism `a : W ⟶ T` to the point `a ≫ g`. -/
theorem app_uliftYonedaEquiv_symm (W : BigFppfOver B S hS) (a : W ⟶ T) :
    (uliftYonedaEquiv.{u + 1}.symm x).app (op W) (ULift.up a) =
      ULift.up (schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map a) ≫ x.down) := rfl

/-- The point of `AlgebraicGeometry.FormalSpace.chartFormalHom` read as an element of the
presheaf of points of `𝔛|_𝔘` over `g⁻¹(𝔘)`. -/
def chartPoint : (formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV)).obj
    (op (chartObject B S hS X V T x)) :=
  ULift.up (chartFormalHom B S hS X V T x hV)

/-- That element is the point `AlgebraicGeometry.FormalSpace.chartFormalHom`. -/
theorem chartPoint_down :
    (chartPoint B S hS X V T x hV).down = chartFormalHom B S hS X V T x hV := rfl

/-- The square whose corners are `g⁻¹(𝔘)`, `𝔛|_𝔘`, `T` and `𝔛` commutes. -/
theorem chart_square :
    uliftYonedaEquiv.{u + 1}.symm (chartPoint B S hS X V T x hV) ≫
        openFormalSubschemePresheafHom B S hS X V hV
      = (uliftYoneda.{u + 1}).map (chartHom B S hS X V T x) ≫ uliftYonedaEquiv.{u + 1}.symm x := by
  refine uliftYonedaEquiv.{u + 1}.injective ?_
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply,
    uliftYonedaEquiv_uliftYoneda_map, app_openFormalSubschemePresheafHom, chartPoint_down,
    app_uliftYonedaEquiv_symm, toScheme_map_chartHom]
  exact congrArg ULift.up (chartFormalHom_comp B S hS X V T x hV)

section ConeLift

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}

/-- The condition on a cone over the chart inclusion and the point `g`, spelled out on a single
element: the point of `𝔛|_𝔘` it provides factors the point of `𝔛` it provides. -/
theorem cone_app_eq
    (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x)
    (W : (BigFppfOver B S hS)ᵒᵖ) (z : P.obj W) :
    (pfst.app W z).down ≫ openFormalSubschemeHom X V hV =
      schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map (psnd.app W z).down) ≫
        x.down :=
  down_apply_eq_of_eq (NatTrans.congr_app hcond W) z

/-- Consequently the morphism to `T` that a cone provides has image inside `g⁻¹(𝔘)`. -/
theorem cone_mem
    (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x)
    (W : (BigFppfOver B S hS)ᵒᵖ) (z : P.obj W) :
    ∀ w, ((BigFppfOver.toScheme B S hS).map ((psnd.app W z).down)).base w
      ∈ chartOpens B S hS X V T x :=
  mem_chartOpens_of_lift B S hS X V T x hV _ ((pfst.app W z).down)
    (cone_app_eq B S hS X V T x hV pfst psnd hcond W z)

/-- The morphism to `g⁻¹(𝔘)` that a cone over the chart inclusion and the point `g` induces: on
each element it is the factorisation of
`AlgebraicGeometry.FormalSpace.existsUnique_chartLift`. Naturality is the uniqueness of that
factorisation. -/
def coneLift (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x) :
    P ⟶ (uliftYoneda.{u + 1}).obj (chartObject B S hS X V T x) where
  app W := ↾fun z => ULift.up (chartLift' B S hS X V T x ((psnd.app W z).down)
    (cone_mem B S hS X V T x hV pfst psnd hcond W z))
  naturality {W W'} k := by
    ext z
    have hn : ((psnd.app W' (P.map k z)).down) = k.unop ≫ (psnd.app W z).down :=
      congrArg ULift.down (congrFun (congrArg (fun m : P.obj W ⟶ _ =>
        (ConcreteCategory.hom m : _ → _)) (psnd.naturality k)) z)
    refine congrArg ULift.up (eq_chartLift B S hS X V T x _
      (cone_mem B S hS X V T x hV pfst psnd hcond W' (P.map k z))
      (k.unop ≫ chartLift' B S hS X V T x ((psnd.app W z).down)
        (cone_mem B S hS X V T x hV pfst psnd hcond W z)) ?_).symm
    rw [Category.assoc, chartLift_comp_chartHom]
    exact hn.symm

/-- The induced morphism factors the morphism to `T` provided by the cone. -/
theorem coneLift_comp_chartHom
    (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x) :
    coneLift B S hS X V T x hV pfst psnd hcond ≫
        (uliftYoneda.{u + 1}).map (chartHom B S hS X V T x) = psnd := by
  ext W z
  exact congrArg ULift.up (chartLift_comp_chartHom B S hS X V T x ((psnd.app W z).down)
    (cone_mem B S hS X V T x hV pfst psnd hcond W z))

/-- The induced morphism factors the point of `𝔛|_𝔘` provided by the cone; both become the same
morphism after the monomorphism `h_{𝔛|_𝔘} ⟶ h_𝔛`. -/
theorem coneLift_comp_chartPoint
    (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x) :
    coneLift B S hS X V T x hV pfst psnd hcond ≫
        uliftYonedaEquiv.{u + 1}.symm (chartPoint B S hS X V T x hV) = pfst := by
  have := mono_openFormalSubschemePresheafHom B S hS X V hV
  refine (cancel_mono (openFormalSubschemePresheafHom B S hS X V hV)).1 ?_
  rw [Category.assoc, chart_square, ← Category.assoc,
    coneLift_comp_chartHom B S hS X V T x hV pfst psnd hcond]
  exact hcond.symm

/-- The induced morphism is the unique one factoring the morphism to `T` provided by the
cone. -/
theorem eq_coneLift
    (pfst : P ⟶ formalSchemeFppfPresheaf B S hS (openFormalSubscheme X V hV))
    (psnd : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hcond : pfst ≫ openFormalSubschemePresheafHom B S hS X V hV
      = psnd ≫ uliftYonedaEquiv.{u + 1}.symm x)
    (m : P ⟶ (uliftYoneda.{u + 1}).obj (chartObject B S hS X V T x))
    (hm : m ≫ (uliftYoneda.{u + 1}).map (chartHom B S hS X V T x) = psnd) :
    m = coneLift B S hS X V T x hV pfst psnd hcond := by
  ext W z
  refine congrArg ULift.up (eq_chartLift B S hS X V T x _
    (cone_mem B S hS X V T x hV pfst psnd hcond W z) ((m.app W z).down) ?_)
  exact down_apply_eq_of_eq (NatTrans.congr_app hm W) z

end ConeLift

section Representable

/-- **The base change of the chart inclusion along a point of `𝔛` is the open subscheme
`g⁻¹(𝔘)`.** This is the geometric content of clause (4) of Stacks 0AIR: a morphism `W ⟶ T` of
the site together with a point of `𝔛|_𝔘` over `W` lifting `g` is the same thing as a morphism
`W ⟶ g⁻¹(𝔘)`, because a point of `𝔛` whose image lies in `𝔘` factors uniquely through
`𝔛|_𝔘`. -/
theorem isPullback_chart :
    IsPullback (uliftYonedaEquiv.{u + 1}.symm (chartPoint B S hS X V T x hV))
      ((uliftYoneda.{u + 1}).map (chartHom B S hS X V T x))
      (openFormalSubschemePresheafHom B S hS X V hV)
      (uliftYonedaEquiv.{u + 1}.symm x) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (chart_square B S hS X V T x hV)
    (fun s => coneLift B S hS X V T x hV s.fst s.snd s.condition)
    (fun s => coneLift_comp_chartPoint B S hS X V T x hV s.fst s.snd s.condition)
    (fun s => coneLift_comp_chartHom B S hS X V T x hV s.fst s.snd s.condition)
    (fun s m _ h₂ => eq_coneLift B S hS X V T x hV s.fst s.snd s.condition m h₂))

end Representable

end Point

section Clause4

variable (hV : IsFormalScheme (X.obj.restrict V))

/-- **The chart inclusion `h_{𝔛|_𝔘} ⟶ h_𝔛` is representable by objects of the big fppf site**:
its base change along a point of `𝔛` over `T` is the universe-lifted Yoneda presheaf of the
open subscheme `g⁻¹(𝔘)` of `T`. -/
theorem relativelyRepresentable_openFormalSubschemePresheafHom :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (openFormalSubschemePresheafHom B S hS X V hV) := by
  intro T₀ g
  obtain ⟨x₀, rfl⟩ := uliftYonedaEquiv.{u + 1}.symm.surjective g
  exact ⟨chartObject B S hS X V T₀ x₀, chartHom B S hS X V T₀ x₀,
    uliftYonedaEquiv.{u + 1}.symm (chartPoint B S hS X V T₀ x₀ hV),
    isPullback_chart B S hS X V T₀ x₀ hV⟩

/-- **Stacks 0AIR, clause (4).** The morphism `h_{𝔛|_𝔘} ⟶ h_𝔛` of fppf sheaves on the big fppf
site of `S` is representable and an open immersion: it is representable by morphisms of the
site, and every morphism of the site representing a base change of it is an open immersion of
schemes. Nothing is assumed of `𝔛`, of `𝔘` or of the base scheme `S`.

The base change along a point `g` of `𝔛` over `T` is the inclusion of the open subscheme
`g⁻¹(𝔘)` of `T`, which is `AlgebraicGeometry.FormalSpace.isPullback_chart`; any other morphism
of the site representing the same base change differs from it by an isomorphism, the
universe-lifted Yoneda embedding being fully faithful. -/
@[stacks 0AIR "the morphisms h_{𝔛ᵢ} ⟶ h_𝔛 of an open covering are representable and open \
immersions"]
theorem relative_isOpenImmersion_openFormalSubschemePresheafHom :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1}) (openFormalSubschemePresheafHom B S hS X V hV) := by
  refine ⟨relativelyRepresentable_openFormalSubschemePresheafHom B S hS X V hV, ?_⟩
  intro T₀ b g pfst psnd hsq
  obtain ⟨x₀, rfl⟩ := uliftYonedaEquiv.{u + 1}.symm.surjective g
  have h2 := isPullback_chart B S hS X V T₀ x₀ hV
  set e := hsq.isoIsPullback _ _ h2 with hedef
  have hmap : (uliftYoneda.{u + 1}).map ((uliftYoneda.{u + 1}).preimage e.hom) = e.hom :=
    (uliftYoneda.{u + 1}).map_preimage _
  have : IsIso ((uliftYoneda.{u + 1}).map ((uliftYoneda.{u + 1}).preimage e.hom)) := by
    rw [hmap]; infer_instance
  have : IsIso ((uliftYoneda.{u + 1}).preimage e.hom) :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) _
  have hfac : (uliftYoneda.{u + 1}).preimage e.hom ≫ chartHom B S hS X V T₀ x₀ = psnd := by
    refine (uliftYoneda.{u + 1}).map_injective ?_
    rw [Functor.map_comp, hmap]
    exact hsq.isoIsPullback_hom_snd _ _ h2
  show IsOpenImmersion ((BigFppfOver.toScheme B S hS).map psnd)
  rw [← hfac, Functor.map_comp]
  have : IsIso ((BigFppfOver.toScheme B S hS).map
      ((uliftYoneda.{u + 1}).preimage e.hom)) := inferInstance
  infer_instance

/-- Being an open immersion, as a property of morphisms in the category of algebraic spaces over
`S` with values in `Type (u + 1)`. This is `AlgebraicGeometry.Space.IsOpenImmersion`, the open
immersions of Stacks 02YU (1), for the value universe in which the formal algebraic spaces of
Stacks 0AIM live. -/
abbrev Space.openImmersionPropertyULift :
    MorphismProperty (Space.AlgebraicSpacesULift.{u + 1} B S hS) :=
  fun _ _ k => (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).relative
    (uliftYoneda.{u + 1}) k.hom

/-- The chart inclusion is representable by algebraic spaces, being representable by objects of
the site. -/
theorem isRepresentableByAlgebraicSpacesULift_openFormalSubschemePresheafHom :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (openFormalSubschemePresheafHom B S hS X V hV) :=
  Space.isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable _
    (relativelyRepresentable_openFormalSubschemePresheafHom B S hS X V hV)

/-- Clause (4) of Stacks 0AIR in the vocabulary of Definition 0AIM: the chart inclusion is
representable by algebraic spaces and the projection of each of its represented base changes is
an open immersion. -/
theorem hasPropertyULift_openImmersion_openFormalSubschemePresheafHom :
    Space.HasPropertyULift.{u + 1} B S hS (Space.openImmersionPropertyULift B S hS)
      (openFormalSubschemePresheafHom B S hS X V hV)
      (isRepresentableByAlgebraicSpacesULift_openFormalSubschemePresheafHom B S hS X V hV) :=
  fun _ ξ => Space.relative_of_isPullback B S hS
    (IsPullback.of_hasPullback ξ (openFormalSubschemePresheafHom B S hS X V hV))
    (relative_isOpenImmersion_openFormalSubschemePresheafHom B S hS X V hV)

/-- The chart inclusion is representable by étale morphisms of the site: an open immersion of
schemes is étale. -/
theorem relative_etale_openFormalSubschemePresheafHom :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1}) (openFormalSubschemePresheafHom B S hS X V hV) := by
  refine MorphismProperty.relative_monotone (fun _ _ k hk => ?_) _
    (relative_isOpenImmersion_openFormalSubschemePresheafHom B S hS X V hV)
  have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k) := hk
  exact inferInstanceAs (Etale ((BigFppfOver.toScheme B S hS).map k))

/-- The chart inclusion `h_{𝔛|_𝔘} ⟶ h_𝔛` is representable étale, which is the condition
Definition 0AIM imposes on the members of an atlas. -/
theorem isRepresentableEtale_openFormalSubschemeSheafHom :
    IsRepresentableEtale B S hS (openFormalSubschemeSheafHom B S hS X V hV) := by
  rw [IsRepresentableEtale]
  rw [openFormalSubschemeSheafHom_hom]
  exact ⟨isRepresentableByAlgebraicSpacesULift_openFormalSubschemePresheafHom B S hS X V hV,
    fun _ ξ _ _ hφ => Space.relative_comp B S hS hφ (Space.relative_of_isPullback B S hS
      (IsPullback.of_hasPullback ξ (openFormalSubschemePresheafHom B S hS X V hV))
      (relative_etale_openFormalSubschemePresheafHom B S hS X V hV))⟩

end Clause4

section Clause3

variable (hV : IsFormalScheme (X.obj.restrict V))

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- An isomorphism of presheafed spaces between `𝔛|_𝔘` and the formal spectrum of an admissible
topological ring is an isomorphism of formal schemes: a morphism of presheafed spaces between
locally topologically ringed spaces which is an isomorphism has local stalk maps. -/
def openFormalSubschemeIsoSpf (hA : TopologicalRing.IsAdmissible A)
    (e : (X.obj.restrict V).toPresheafedSpace ≅ (spfLTRS A hA.1).toPresheafedSpace) :
    openFormalSubscheme X V hV ≅ spfFormalScheme A hA where
  hom := ObjectProperty.homMk (ltrsIsoOfPresheafedSpaceIso e).hom
  inv := ObjectProperty.homMk (ltrsIsoOfPresheafedSpaceIso e).inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact (ltrsIsoOfPresheafedSpaceIso e).hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact (ltrsIsoOfPresheafedSpaceIso e).inv_hom_id

/-- **Stacks 0AIR, clause (3).** For a member `𝔛|_𝔘` of an affine open covering of `𝔛` — an open
of `𝔛` whose restriction is isomorphic to the formal spectrum of an admissible topological ring
`A` — the functor of points `h_{𝔛|_𝔘}` is an affine formal algebraic space over `S`.

This is Stacks 0AIE,
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSchemePointsFppfSheaf`,
transported along the chart isomorphism, the functor of points being a functor of the formal
scheme. The source's own hypotheses are kept: the base is terminal, as the source assumes it is
`Spec(ℤ)`, and the quotient spectra of `A` and their coproduct belong to the chosen big fppf
site, which is the datum `D` and the condition `hB`. -/
@[stacks 0AIR "the charts h_{𝔛ᵢ} of an affine open covering are affine formal algebraic \
spaces"]
theorem isAffineFormalAlgebraicSpace_openFormalSubschemePoints (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) (hB : D.HasLargeSite)
    (e : (X.obj.restrict V).toPresheafedSpace ≅ (spfLTRS A hA.1).toPresheafedSpace) :
    IsAffineFormalAlgebraicSpace B S hS
      (formalSchemePointsFppfSheaf B S hS (openFormalSubscheme X V hV)) :=
  isAffineFormalAlgebraicSpace_of_iso B S hS
    (((formalSchemePointsFppfSheafFunctor B S hS).mapIso
      (openFormalSubschemeIsoSpf X V hV hA e)).symm)
    (isAffineFormalAlgebraicSpace_formalSchemePointsFppfSheaf hterm hA D hB)

end Clause3

section Clause2

/-- A terminal scheme contained in a big fppf site is terminal in the site's category of
schemes, the inclusion of that category being fully faithful. -/
def isTerminalSiteBase (hterm : IsTerminal S) : IsTerminal (B.obj hS) :=
  IsTerminal.ofUniqueHom (fun Z => ObjectProperty.homMk (hterm.from Z.obj))
    fun _ _ => by apply ObjectProperty.hom_ext; exact hterm.hom_ext _ _

/-- Over a terminal base every scheme of the site is an object of the big fppf category over
`S`, with its unique structure morphism. -/
def terminalSiteObject (hterm : IsTerminal S) (Z : B.Schemes) : BigFppfOver B S hS :=
  Over.mk ((isTerminalSiteBase B S hS hterm).from Z)

/-- Over a terminal base every morphism of the site's schemes is a morphism over `S`. -/
def terminalSiteMap (hterm : IsTerminal S) {Z Z' : B.Schemes} (t : Z ⟶ Z') :
    terminalSiteObject B S hS hterm Z ⟶ terminalSiteObject B S hS hterm Z' :=
  Over.homMk t ((isTerminalSiteBase B S hS hterm).hom_ext _ _)

/-- a transformation of functors of points on the big fppf site over a terminal base, read on
the schemes of size below the cutoff -/
def transferFormalSchemePoints (hterm : IsTerminal S) {X Y : FormalScheme.{u}}
    (φ : formalSchemeFppfPresheaf B S hS X ⟶ formalSchemeFppfPresheaf B S hS Y) :
    (formalSchemeFunctorOfPoints B.cutoff).obj X ⟶
      (formalSchemeFunctorOfPoints B.cutoff).obj Y where
  app Z := ↾fun q =>
    (φ.app (op (terminalSiteObject B S hS hterm Z.unop)) (ULift.up q)).down
  naturality {Z Z'} t := by
    ext q
    exact congrArg ULift.down (congrFun (congrArg (fun k : _ ⟶ _ =>
      (ConcreteCategory.hom k : _ → _))
      (φ.naturality (terminalSiteMap B S hS hterm t.unop).op)) (ULift.up q))

/-- The transferred transformation, read on a point over an object of the big fppf category
presented with an arbitrary structure morphism: over a terminal base that structure morphism is
the unique one. -/
theorem transferFormalSchemePoints_app (hterm : IsTerminal S) {X Y : FormalScheme.{u}}
    (φ : formalSchemeFppfPresheaf B S hS X ⟶ formalSchemeFppfPresheaf B S hS Y)
    (Z : B.Schemes) (b : Z ⟶ B.obj hS) (q : schemeToFormalScheme.obj Z.obj ⟶ X) :
    (transferFormalSchemePoints B S hS hterm φ).app (op Z) q
      = (φ.app (op (Over.mk b)) (ULift.up q)).down := by
  have hb : b = (isTerminalSiteBase B S hS hterm).from Z :=
    (isTerminalSiteBase B S hS hterm).hom_ext _ _
  subst hb
  rfl

/-- **Faithfulness of `𝔛 ↦ h_𝔛` on the big fppf site.** A morphism of formal schemes out of a
formal scheme whose affine chart quotients belong to the big fppf site is determined by the
morphism of fppf sheaves it induces.

Every scheme of the site is a test object of the big fppf category over the terminal base, so
this is the injectivity half of Stacks 0AI1 at the cutoff of the site,
`AlgebraicGeometry.injective_formalSchemeFunctorOfPoints_map`. -/
theorem injective_map_formalSchemePointsFppfSheafFunctor (hterm : IsTerminal S)
    {X Y : FormalScheme.{u}} (hX : IsSizeBoundedFormalScheme B.cutoff X.obj) :
    Function.Injective fun f : X ⟶ Y =>
      (formalSchemePointsFppfSheafFunctor B S hS).map f := by
  intro f g h
  refine injective_formalSchemeFunctorOfPoints_map (κ := B.cutoff) hX ?_
  ext Z q
  have h2 := congrArg (fun k : formalSchemePointsFppfSheaf B S hS X ⟶
    formalSchemePointsFppfSheaf B S hS Y => k.hom) h
  exact down_apply_eq_of_eq
    (NatTrans.congr_app h2 (op (terminalSiteObject B S hS hterm Z.unop))) (ULift.up q)

/-- **Fullness of `𝔛 ↦ h_𝔛` on the big fppf site.** Every morphism `h_𝔛 ⟶ h_𝔜` of fppf sheaves
is induced by a morphism of formal schemes, provided the affine chart quotients of `𝔛` belong
to the big fppf site.

The morphism of sheaves is read on the schemes of the site by
`AlgebraicGeometry.FormalSpace.transferFormalSchemePoints`, where the surjectivity half of
Stacks 0AI1 at the cutoff of the site produces the morphism of formal schemes; that morphism
induces the given transformation because, over a terminal base, an object of the big fppf
category is its underlying scheme with its unique structure morphism. -/
theorem exists_map_eq_formalSchemePointsFppfSheafFunctor (hterm : IsTerminal S)
    {X Y : FormalScheme.{u}} (hX : IsSizeBoundedFormalScheme B.cutoff X.obj)
    (φ : formalSchemePointsFppfSheaf B S hS X ⟶ formalSchemePointsFppfSheaf B S hS Y) :
    ∃ f : X ⟶ Y, (formalSchemePointsFppfSheafFunctor B S hS).map f = φ := by
  obtain ⟨f, hf⟩ := exists_formalSchemeFunctorOfPoints_map_eq hX
    (transferFormalSchemePoints B S hS hterm φ.hom)
  refine ⟨f, Sheaf.hom_ext ?_⟩
  ext Top y
  obtain ⟨T, rfl⟩ : ∃ T' : BigFppfOver B S hS, Top = op T' := ⟨Top.unop, rfl⟩
  exact congrArg ULift.up
    ((ConcreteCategory.congr_hom (NatTrans.congr_app hf (op T.left)) y.down).trans
      (transferFormalSchemePoints_app B S hS hterm φ.hom T.left T.hom y.down))

/-- The formal schemes whose affine chart quotients `Spec (A/I_λ)` have size below `κ`. For
`κ` the cutoff of a big fppf site this is the source's "modulo set theoretic issues" in the
form Stacks 0AI1 leaves it. -/
abbrev sizeBoundedFormalSchemes (κ : Cardinal.{u}) : ObjectProperty FormalScheme.{u} :=
  fun X => IsSizeBoundedFormalScheme κ X.obj

/-- The functor of points, restricted to the formal schemes whose affine chart quotients belong
to the big fppf site. -/
abbrev sizeBoundedFormalSchemePointsFppfSheafFunctor :
    (sizeBoundedFormalSchemes B.cutoff).FullSubcategory ⥤ FppfSheaf B S hS :=
  (sizeBoundedFormalSchemes B.cutoff).ι ⋙ formalSchemePointsFppfSheafFunctor B S hS

/-- **Stacks 0AIR, clause (2).** The assignment `𝔛 ↦ h_𝔛` is a fully faithful embedding of the
category of formal schemes into the category `AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`
of fppf sheaves on the big fppf site of `S` — the category in which formal algebraic spaces over
`S` live, and the one the comparison of Stacks 0AIR is about.

The source's "modulo set theoretic issues" is the restriction of the source category to the
formal schemes whose affine chart quotients belong to the big fppf site, which is the size
condition of Stacks 0AI1 for the site's cutoff, and the source's assumption that the base is
`Spec(ℤ)` is the hypothesis `hterm`. Both halves are Stacks 0AI1 read on the site:
`AlgebraicGeometry.FormalSpace.injective_map_formalSchemePointsFppfSheafFunctor` and
`AlgebraicGeometry.FormalSpace.exists_map_eq_formalSchemePointsFppfSheafFunctor`. -/
@[stacks 0AIR "the assignment 𝔛 ↦ h_𝔛 is a fully faithful embedding of formal schemes into \
the fppf sheaves on the big fppf site of the base"]
def fullyFaithfulFormalSchemePointsFppfSheafFunctor (hterm : IsTerminal S) :
    (sizeBoundedFormalSchemePointsFppfSheafFunctor B S hS).FullyFaithful :=
  haveI : (sizeBoundedFormalSchemePointsFppfSheafFunctor B S hS).Full :=
    ⟨fun {X _} φ => by
      obtain ⟨f, hf⟩ :=
        exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm X.property φ
      exact ⟨ObjectProperty.homMk f, hf⟩⟩
  haveI : (sizeBoundedFormalSchemePointsFppfSheafFunctor B S hS).Faithful :=
    ⟨fun {X _ _ _} h => ObjectProperty.hom_ext _
      (injective_map_formalSchemePointsFppfSheafFunctor B S hS hterm X.property h)⟩
  .ofFullyFaithful _

end Clause2

section Clause5

variable (X : FormalScheme.{u}) {I : Type u} (U : I → Opens X.obj)
  (hU : ∀ i, IsFormalScheme (X.obj.restrict (U i)))

/-- **The charts of an open covering are jointly surjective.** If the opens `𝔘_i` cover `𝔛`,
then the induced morphism `∐ h_{𝔛|_{𝔘_i}} ⟶ h_𝔛` is a surjection of fppf sheaves.

A point `g` of `𝔛` over a test object `T` is covered by the open subschemes `g⁻¹(𝔘_i)` of `T`,
which form a Zariski and hence an fppf covering of `T`
(`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`), and over each of
them `g` factors through the corresponding chart. This is the third condition of
Definition 0AIM. -/
theorem isLocallySurjective_sigmaDesc_openFormalSubschemeSheafHom
    (hcov : ∀ p : X.obj, ∃ i, p ∈ U i) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc (fun i : ULift.{u + 1} I =>
      openFormalSubschemeSheafHom B S hS X (U i.down) (hU i.down))) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 fun T x => ?_
  refine ⟨Sieve.ofArrows (fun i : I => chartObject B S hS X (U i) T x)
    (fun i => chartHom B S hS X (U i) T x), ?_, ?_⟩
  · refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
      (fun i => isOpenImmersion_toScheme_map_chartHom B S hS X (U i) T x) ?_
    intro y
    obtain ⟨i, hi⟩ := hcov (x.down.hom.toHom.base y)
    exact ⟨i, ⟨⟨y, hi⟩, rfl⟩⟩
  · intro W g hg
    obtain ⟨Z, k, g', ⟨i⟩, hfac⟩ := hg
    refine ⟨ULift.up i, ULift.up (schemeToFormalScheme.map
      ((BigFppfOver.toScheme B S hS).map k) ≫ chartFormalHom B S hS X (U i) T x (hU i)), ?_⟩
    refine congrArg ULift.up ?_
    show schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map k) ≫
        (chartFormalHom B S hS X (U i) T x (hU i) ≫ openFormalSubschemeHom X (U i) (hU i))
      = schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map g) ≫ x.down
    have hmap : (BigFppfOver.toScheme B S hS).map g
        = (BigFppfOver.toScheme B S hS).map k ≫ (chartOpens B S hS X (U i) T x).ι := by
      rw [← hfac, Functor.map_comp]
      rfl
    rw [chartFormalHom_comp B S hS X (U i) T x (hU i), hmap, Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- **Stacks 0AIR, clause (5).** The functor of points of a formal scheme à la EGA is a formal
algebraic space over `S`, for a formal scheme admitting an open covering `𝔛 = ⋃ 𝔘_i` whose
charts have affine formal algebraic space functors of points and whose own functor of points
satisfies the set-theoretic condition of Stacks 0AIS.

This is the last sentence of the source's remark. The family `{h_{𝔛|_{𝔘_i}} ⟶ h_𝔛}` is a family
as in Definition 0AIM: the sources are affine formal algebraic spaces, which is the hypothesis
`haff` supplied by
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_openFormalSubschemePoints`; the
arrows are representable open immersions, hence representable étale, which is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_openFormalSubschemeSheafHom`; and the
family is jointly surjective, which is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_openFormalSubschemeSheafHom`. The
conclusion is then Stacks 0AJ1,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`.

The hypothesis `hset` is the source's "modulo set theoretic issues" in the precise form of
Stacks 0AIS, and it is the only thing the source leaves to the reader here. -/
@[stacks 0AIR "the functor of points of a formal scheme with an affine open covering is a \
formal algebraic space"]
theorem isFormalAlgebraicSpaceFormalSchemePoints_of_affineCover
    (hcov : ∀ p : X.obj, ∃ i, p ∈ U i)
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (formalSchemePointsFppfSheaf B S hS (openFormalSubscheme X (U i) (hU i))))
    (hset : SatisfiesSetTheoreticCondition B S hS (formalSchemePointsFppfSheaf B S hS X)) :
    IsFormalAlgebraicSpaceFormalSchemePoints B S hS X :=
  fun _ => isFormalAlgebraicSpace_of_etaleCover B S hS _
    (fun i : ULift.{u + 1} I =>
      formalSchemePointsFppfSheaf B S hS (openFormalSubscheme X (U i.down) (hU i.down)))
    (fun i => openFormalSubschemeSheafHom B S hS X (U i.down) (hU i.down))
    (fun i => isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haff i.down))
    (fun i => isRepresentableEtale_openFormalSubschemeSheafHom B S hS X (U i.down) (hU i.down))
    (isLocallySurjective_sigmaDesc_openFormalSubschemeSheafHom B S hS X U hU hcov) hset

end Clause5

section Comparison

/-- The formal schemes the comparison of Stacks 0AIR applies to: those whose affine chart
quotients belong to the big fppf site and whose functor of points is a formal algebraic space
over `S`. The second condition is supplied by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpaceFormalSchemePoints_of_affineCover`. -/
abbrev comparableFormalSchemes : ObjectProperty FormalScheme.{u} := fun X =>
  IsSizeBoundedFormalScheme B.cutoff X.obj ∧
    IsFormalAlgebraicSpace B S hS (formalSchemePointsFppfSheaf B S hS X)

/-- The formal algebraic spaces over `S`, as a full subcategory of the fppf sheaves on the big
fppf site of `S`. -/
abbrev formalAlgebraicSpaces : ObjectProperty (FppfSheaf B S hS) := fun Z =>
  IsFormalAlgebraicSpace B S hS Z

/-- The assignment `𝔛 ↦ h_𝔛` as a functor from the formal schemes the comparison applies to
into the category of formal algebraic spaces over `S`. -/
abbrev comparableFormalSchemePointsFunctor :
    (comparableFormalSchemes B S hS).FullSubcategory ⥤
      (formalAlgebraicSpaces B S hS).FullSubcategory :=
  ObjectProperty.lift _
    ((comparableFormalSchemes B S hS).ι ⋙ formalSchemePointsFppfSheafFunctor B S hS)
    fun X => X.property.2

/-- **Stacks 0AIR, the comparison.** The category of formal schemes à la EGA is equivalent to a
full subcategory of the category of formal algebraic spaces over `S`: the functor `𝔛 ↦ h_𝔛`
from the formal schemes the comparison applies to into the formal algebraic spaces over `S` is
fully faithful, so it is an equivalence onto the full subcategory on its image.

This is the opening sentence of the source's remark. Its "modulo set theoretic issues" is the
restriction of the source category to
`AlgebraicGeometry.FormalSpace.comparableFormalSchemes`, and the source's assumption that the
base is `Spec(ℤ)` is the hypothesis `hterm`. Full faithfulness is clause (2),
`AlgebraicGeometry.FormalSpace.fullyFaithfulFormalSchemePointsFppfSheafFunctor`, and the
functor lands in formal algebraic spaces by clause (5). -/
@[stacks 0AIR "the category of formal schemes is equivalent to a full subcategory of the \
category of formal algebraic spaces"]
def fullyFaithfulComparableFormalSchemePointsFunctor (hterm : IsTerminal S) :
    (comparableFormalSchemePointsFunctor B S hS).FullyFaithful where
  preimage {X _} φ := ObjectProperty.homMk
    (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm X.property.1 φ.hom).choose
  map_preimage {X _} φ := ObjectProperty.hom_ext _
    (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm X.property.1 φ.hom).choose_spec
  preimage_map {X _} f := by
    apply ObjectProperty.hom_ext
    refine injective_map_formalSchemePointsFppfSheafFunctor B S hS hterm X.property.1 ?_
    exact (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm X.property.1
      ((comparableFormalSchemePointsFunctor B S hS).map f).hom).choose_spec

end Comparison

end FormalSpace

end AlgebraicGeometry

end
