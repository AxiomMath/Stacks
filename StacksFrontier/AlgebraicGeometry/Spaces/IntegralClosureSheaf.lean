module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits

/-!
# The integral closure of the structure sheaf in an algebra on an algebraic space

Let `F` be an algebraic space over `S` and let `A` be a sheaf of commutative `𝒪_F`-algebras on
the small étale site of `F`, in the sense of `AlgebraicGeometry.Space.AlgebraSheaf`.  Stacks
0820 asserts that `A` contains a quasi-coherent `𝒪_F`-subalgebra whose sections over an
*affine* étale chart `U` are the integral closure of `𝒪_F(U)` in `A(U)`.

This file constructs that subalgebra as data.  Its sections over an arbitrary chart are the
*locally integral* sections of `A`, those integral over the structure sheaf on the members of
some étale covering of the chart; the integral sections by themselves do not form a sheaf.
The inclusion into `A` is constructed and shown to be a monomorphism, and the integral
sections over a chart are shown to be sections of the subalgebra.  The two assertions of
Stacks 0820 that this library cannot supply — that over an *affine* chart a locally integral
section is already integral, and quasi-coherence of the subalgebra — are discussed under
Implementation notes; the first is isolated as the hypothesis
`AlgebraicGeometry.Space.AlgebraSheaf.IsIntegralLocalOnAffineCharts` and no statement of the
second is made.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.integralSubringOfHom` is the subring of elements
  integral over a ring homomorphism, and
  `AlgebraicGeometry.Space.AlgebraSheaf.integralSections` is that subring for the
  structure-algebra map of an algebra sheaf over a chart.
* `AlgebraicGeometry.Space.AlgebraSheaf.integralSubfunctor` is the subpresheaf of integral
  sections, and `AlgebraicGeometry.Space.AlgebraSheaf.locallyIntegralSections` is its
  sheafification in the sense of `CategoryTheory.Subfunctor.sheafify`, as a subring of the
  sections of `A` over a chart.
* `AlgebraicGeometry.Space.AlgebraSheaf.integralClosurePresheaf` is the presheaf of locally
  integral sections and `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureSheaf` the
  resulting algebra sheaf, with
  `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureInclusion` its inclusion into `A`.
  These two are the subalgebra named by Stacks 0821 and the inclusion that names it a
  subalgebra, and they carry that tag.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegralLocalOnAffineCharts` is the assertion that
  over an affine étale chart a locally integral section of `A` is integral.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isSheaf_integralClosurePresheaf`: the presheaf of
  locally integral sections is a sheaf of commutative rings.
* `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureInclusion_app_injective` and
  `AlgebraicGeometry.Space.AlgebraSheaf.mono_integralClosureInclusion_right`: the inclusion is
  injective on the sections over every chart, hence a monomorphism of the underlying sheaves
  of commutative rings.
* `AlgebraicGeometry.Space.AlgebraSheaf.range_integralClosureInclusion_app`: the sections of
  the subalgebra over a chart are exactly the locally integral sections of `A`.
* `AlgebraicGeometry.Space.AlgebraSheaf.integralClosure_le_range_integralClosureInclusion_app`:
  every section of `A` integral over the structure sheaf is a section of the subalgebra.  This
  is one of the two inclusions of the sections assertion of Stacks 0820, and it holds over
  every chart and needs no hypothesis.
* `AlgebraicGeometry.Space.AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure`:
  the sections assertion of Stacks 0820 over an affine chart, from
  `IsIntegralLocalOnAffineCharts`.

## Implementation notes

**Why the locally integral sections and not the integral ones.**  The integral sections form a
subpresheaf of rings, `integralSubfunctor` together with `integralSections`, but not a
subsheaf.  For a chart `U` which is an infinite disjoint union of affine charts `U n`, a
section whose restriction to `U n` satisfies a monic equation of degree `n` and of no smaller
degree is integral on each member of the covering `{U n}` and is not integral over `𝒪_F(U)`:
there is no single degree in which to write a monic equation over the product ring.  This is
why Stacks 0820 identifies the sections only over *affine* charts, and it is what forces the
sheafification here.  The shape is in any case forced: two subsheaves of `A` whose sections
over the affine charts are the integral closure agree, the affine charts generating the small
étale topology, so the locally integral sections are the only candidate.

**What is missing, and where it lives.**  Two assertions of Stacks 0820 are not proved here.

The first is that over an affine chart a locally integral section is integral, carried as the
hypothesis `IsIntegralLocalOnAffineCharts`.  Discharging it needs the identification
`A(V) = 𝒪_F(V) ⊗_{𝒪_F(U)} A(U)` for a morphism `V ⟶ U` of affine charts, which is what lets
integrality be descended along the faithfully flat ring map `𝒪_F(U) → ∏ 𝒪_F(V i)` of a finite
affine refinement of a covering.  That identification is
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, and it is *not* available from
`SheafOfModules.IsQuasicoherentOnSite`: as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections` record, passing from that purely local
quasi-coherence predicate to a statement about the sections over one affine chart is Descent,
Proposition 03DX(2), which rests on the vanishing of the higher étale cohomology of a
quasi-coherent module on an affine scheme, Descent, Proposition 03DW.  Neither is available,
which is why `IsCartesianOnAffineCharts` is carried as a hypothesis throughout this part of
the library; the hypothesis here is its counterpart for integrality.

The second is quasi-coherence of the subalgebra.  The source proves it by restricting `A` to
the Zariski site of a chart, forming the integral closure there by Morphisms, Lemma 29.54.1
(Stacks 035F), and identifying the results along étale morphisms of charts by More on
Morphisms, Lemma 37.19.1 (Stacks 081K).  Neither 035F nor 081K is available in this library,
and the first step is again the comparison of Stacks 03DX(2).  No statement of quasi-coherence
is therefore made, and nothing here carries `@[stacks 0820]`: what is constructed is the
subalgebra, and the content of the tag is the two assertions about it.

Stacks 0821 is a different matter, and it is carried here.  That tag introduces no assertion:
it names the subalgebra of Stacks 0820 and fixes the notation `𝒜'` for it, so the construction
is the whole of its content.  Its adjective *quasi-coherent* is one of the two assertions of
0820 and is therefore an unproved property of the object named, not part of what naming it
requires; a consumer that needs quasi-coherence takes it as a hypothesis, as
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` does.

**The sheaf condition.**  `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget'` is the
universe-general form of `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget`: that lemma fixes
the coefficients to `CommRingCat.{u}` for a site whose morphisms live in `Type u`, whereas the
sections of an algebra sheaf live in a universe independent of the schemes.  Only the universe
annotations differ.  Mathlib's `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` does not
apply at all, since it asks the coefficients to have limits of the size of the site.

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
* [Stacks Project, Tag 081K](https://stacks.math.columbia.edu/tag/081K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.Sites

/-- A presheaf of commutative rings whose underlying presheaf of types is a sheaf is a sheaf,
with the universe of the rings of sections unrelated to the universe of the site.

This is `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget` with the universe of the
coefficients freed from the universe of the morphisms of the site; the proof is the same.  The
sheaf condition is a limit over each covering sieve, and the forgetful functor to types
reflects that limit: it exists in types by hypothesis, so it is small, and the forgetful
functor preserves it. -/
theorem isSheaf_commRingCat_of_isSheaf_forget' {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ CommRingCat.{m})
    (h : Presieve.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat.{m})) :
    Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit]
  have h' : Presheaf.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat.{m}) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 h
  rw [Presheaf.isSheaf_iff_isLimit] at h'
  intro X R hR
  obtain ⟨t⟩ := h' R hR
  let D := R.arrows.diagram.op ⋙ P
  have : HasLimit (D ⋙ CategoryTheory.forget CommRingCat.{m}) := ⟨_, t⟩
  have : Small.{m} (D ⋙ CategoryTheory.forget CommRingCat.{m}).sections :=
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have : PreservesLimit D (CategoryTheory.forget CommRingCat.{m}) :=
    preservesLimit_of_preserves_limit_cone (CommRingCat.limitConeIsLimit D)
      (Types.Small.limitConeIsLimit _)
  have : ReflectsLimit D (CategoryTheory.forget CommRingCat.{m}) :=
    reflectsLimit_of_reflectsIsomorphisms D (CategoryTheory.forget CommRingCat.{m})
  exact ⟨isLimitOfReflects (CategoryTheory.forget CommRingCat.{m}) t⟩

end Stacks.Sites

namespace AlgebraicGeometry.Space.AlgebraSheaf

/-! ### Elements integral over a ring homomorphism -/

/-- The elements of `A` integral over a ring homomorphism `f : R →+* A`, as a subring of `A`.
This is `integralClosure` for the algebra structure that `f` defines, forgotten to a subring,
which is the form in which it is a candidate for the sections of a sheaf of rings. -/
def integralSubringOfHom {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) : Subring A :=
  letI := f.toAlgebra
  (integralClosure R A).toSubring

/-- Membership in `integralSubringOfHom f` is integrality over `f`. -/
theorem mem_integralSubringOfHom {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    {x : A} : x ∈ integralSubringOfHom f ↔ f.IsIntegralElem x :=
  let := f.toAlgebra
  Iff.rfl

/-- A value of a ring homomorphism is integral over it: it is a root of `X - C r`. -/
theorem isIntegralElem_apply {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) (r : R) :
    f.IsIntegralElem (f r) :=
  ⟨Polynomial.X - Polynomial.C r, Polynomial.monic_X_sub_C r, by simp⟩

/-- Integrality is carried along a commuting square of ring homomorphisms: if `σ` carries the
coefficient map `f` to the coefficient map `g` through `ρ`, then it carries elements integral
for `f` to elements integral for `g`.  The witnessing monic polynomial is the image of the
given one under `ρ`. -/
theorem isIntegralElem_map {R A R' A' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [CommRing A'] {f : R →+* A} {g : R' →+* A'} (ρ : R →+* R') (σ : A →+* A')
    (hcomm : σ.comp f = g.comp ρ) {x : A} (hx : f.IsIntegralElem x) :
    g.IsIntegralElem (σ x) := by
  obtain ⟨p, hp, hp0⟩ := hx
  refine ⟨p.map ρ, hp.map ρ, ?_⟩
  rw [Polynomial.eval₂_map, ← hcomm, ← Polynomial.hom_eval₂, hp0, map_zero]

/-! ### The subpresheaf of integral sections -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The sections of an algebra sheaf, as a presheaf of types on the small étale site. -/
abbrev sectionsPresheaf (A : AlgebraSheaf.{u, m} B S hS F hF) :
    (SmallEtale B S hS F)ᵒᵖ ⥤ Type m :=
  A.right.obj ⋙ CategoryTheory.forget CommRingCat.{m}

/-- The sections of an algebra sheaf form a sheaf of types.  The forgetful functor from
commutative rings composes with sheaves, so this is the sheaf condition of the underlying
sheaf of rings read in types. -/
theorem isSheaf_sectionsPresheaf (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Presieve.IsSheaf (SmallEtale.topology B S hS F) A.sectionsPresheaf :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (SmallEtale.topology B S hS F)
      (CategoryTheory.forget CommRingCat.{m})).obj A.right).property

/-- The sections of an algebra sheaf over a chart that are integral over the structure sheaf,
as a subring of the sections. -/
def integralSections (A : AlgebraSheaf.{u, m} B S hS F hF) (U : (SmallEtale B S hS F)ᵒᵖ) :
    Subring (A.right.obj.obj U) :=
  integralSubringOfHom (A.algebraMap U)

/-- Membership in the integral sections over a chart is integrality over the structure-algebra
map of that chart. -/
theorem mem_integralSections {A : AlgebraSheaf.{u, m} B S hS F hF}
    {U : (SmallEtale B S hS F)ᵒᵖ} {a : A.right.obj.obj U} :
    a ∈ A.integralSections U ↔ (A.algebraMap U).IsIntegralElem a :=
  mem_integralSubringOfHom _

/-- The restriction of an integral section along a morphism of charts is integral: the monic
equation restricts, because the structure-algebra maps commute with restriction. -/
theorem map_mem_integralSections (A : AlgebraSheaf.{u, m} B S hS F hF)
    {U V : (SmallEtale B S hS F)ᵒᵖ} (i : U ⟶ V) {a : A.right.obj.obj U}
    (ha : a ∈ A.integralSections U) :
    (A.right.obj.map i).hom a ∈ A.integralSections V := by
  refine mem_integralSections.2 (isIntegralElem_map
    (((structureSheaf B S hS F hF).obj.map i).hom) ((A.right.obj.map i).hom) ?_
    (mem_integralSections.1 ha))
  exact RingHom.ext fun r => A.algebraMap_natural i r

/-- The integral sections of an algebra sheaf, as a subpresheaf of its sections.  It is a
subpresheaf of rings but not a subsheaf; see the implementation notes. -/
def integralSubfunctor (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Subfunctor A.sectionsPresheaf where
  obj U := {a : A.sectionsPresheaf.obj U | a ∈ A.integralSections U}
  map i a ha := by
    change (A.right.obj.map i).hom a ∈ A.integralSections _
    exact A.map_mem_integralSections i ha

/-- The sections of `integralSubfunctor` over a chart are the integral sections. -/
theorem mem_integralSubfunctor_obj {A : AlgebraSheaf.{u, m} B S hS F hF}
    {U : (SmallEtale B S hS F)ᵒᵖ} {a : A.right.obj.obj U} :
    a ∈ A.integralSubfunctor.obj U ↔ a ∈ A.integralSections U := Iff.rfl

/-- The sieve attached to a section by the subpresheaf of integral sections consists of the
morphisms of charts along which the section restricts to an integral section. -/
theorem sieveOfSection_integralSubfunctor_apply (A : AlgebraSheaf.{u, m} B S hS F hF)
    {U : (SmallEtale B S hS F)ᵒᵖ} (a : A.right.obj.obj U) {V : SmallEtale B S hS F}
    (i : V ⟶ unop U) :
    (A.integralSubfunctor.sieveOfSection a).arrows i ↔
      (A.right.obj.map i.op).hom a ∈ A.integralSections (op V) :=
  Iff.rfl

/-! ### The locally integral sections -/

/-- The locally integral sections of an algebra sheaf over a chart: the sections that are
integral over the structure sheaf on the members of some étale covering of the chart.  They
form a subring, because two coverings of a chart have a common refinement. -/
def locallyIntegralSections (A : AlgebraSheaf.{u, m} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) : Subring (A.right.obj.obj U) where
  carrier := (A.integralSubfunctor.sheafify (SmallEtale.topology B S hS F)).obj U
  one_mem' := A.integralSubfunctor.le_sheafify _ U (mem_integralSubfunctor_obj.2 (one_mem _))
  zero_mem' := A.integralSubfunctor.le_sheafify _ U (mem_integralSubfunctor_obj.2 (zero_mem _))
  add_mem' {a b} ha hb := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      ((SmallEtale.topology B S hS F).intersection_covering ha hb)
    intro V i hi
    rw [sieveOfSection_integralSubfunctor_apply, map_add]
    exact add_mem ((sieveOfSection_integralSubfunctor_apply A a i).1 hi.1)
      ((sieveOfSection_integralSubfunctor_apply A b i).1 hi.2)
  mul_mem' {a b} ha hb := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      ((SmallEtale.topology B S hS F).intersection_covering ha hb)
    intro V i hi
    rw [sieveOfSection_integralSubfunctor_apply, map_mul]
    exact mul_mem ((sieveOfSection_integralSubfunctor_apply A a i).1 hi.1)
      ((sieveOfSection_integralSubfunctor_apply A b i).1 hi.2)
  neg_mem' {a} ha := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_ ha
    intro V i hi
    rw [sieveOfSection_integralSubfunctor_apply, map_neg]
    exact neg_mem ((sieveOfSection_integralSubfunctor_apply A a i).1 hi)

/-- The locally integral sections over a chart are the sections of the sheafification of the
subpresheaf of integral sections. -/
theorem mem_locallyIntegralSections_iff_mem_sheafify
    {A : AlgebraSheaf.{u, m} B S hS F hF}
    {U : (SmallEtale B S hS F)ᵒᵖ} {a : A.right.obj.obj U} :
    a ∈ A.locallyIntegralSections U ↔
      a ∈ (A.integralSubfunctor.sheafify (SmallEtale.topology B S hS F)).obj U :=
  Iff.rfl

/-- A section is locally integral exactly when the morphisms of charts along which it restricts
to an integral section form a covering sieve. -/
theorem mem_locallyIntegralSections {A : AlgebraSheaf.{u, m} B S hS F hF}
    {U : (SmallEtale B S hS F)ᵒᵖ} {a : A.right.obj.obj U} :
    a ∈ A.locallyIntegralSections U ↔
      A.integralSubfunctor.sieveOfSection a ∈ SmallEtale.topology B S hS F (unop U) :=
  Iff.rfl

/-- An integral section is locally integral, the trivial sieve being a covering sieve. -/
theorem integralSections_le_locallyIntegralSections
    (A : AlgebraSheaf.{u, m} B S hS F hF) (U : (SmallEtale B S hS F)ᵒᵖ) :
    A.integralSections U ≤ A.locallyIntegralSections U :=
  fun _ ha => mem_locallyIntegralSections_iff_mem_sheafify.2
    (A.integralSubfunctor.le_sheafify _ U (mem_integralSubfunctor_obj.2 ha))

/-! ### The integral closure as an algebra sheaf -/

/-- The presheaf of locally integral sections of an algebra sheaf, with the restriction maps
of `A`. -/
def integralClosurePresheaf (A : AlgebraSheaf.{u, m} B S hS F hF) :
    (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{m} where
  obj U := CommRingCat.of (A.locallyIntegralSections U)
  map {U V} i := CommRingCat.ofHom
    (((A.right.obj.map i).hom.comp (A.locallyIntegralSections U).subtype).codRestrict
      (A.locallyIntegralSections V) fun a =>
        mem_locallyIntegralSections_iff_mem_sheafify.2
          ((A.integralSubfunctor.sheafify (SmallEtale.topology B S hS F)).map i
            (mem_locallyIntegralSections_iff_mem_sheafify.1 a.2)))
  map_id U := by
    ext a
    change (A.right.obj.map (𝟙 U)).hom a.1 = a.1
    simp
  map_comp {U V W} i j := by
    ext a
    change (A.right.obj.map (i ≫ j)).hom a.1 =
      (A.right.obj.map j).hom ((A.right.obj.map i).hom a.1)
    simp

/-- The presheaf of locally integral sections is a sheaf of commutative rings: in types it is
the sheafification of the subpresheaf of integral sections inside the sheaf of all sections. -/
theorem isSheaf_integralClosurePresheaf (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F) (integralClosurePresheaf A) := by
  refine Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget' _ _ ?_
  refine Presieve.isSheaf_iso _ (NatIso.ofComponents (fun U => Iso.refl _) ?_)
    (A.integralSubfunctor.sheafify_isSheaf A.isSheaf_sectionsPresheaf)
  intro U V i
  rfl

/-- **The integral closure of the structure sheaf in an algebra sheaf.**  Its sections over a
chart are the locally integral sections of `A`, and the structure-algebra map is the one of
`A`, whose values are integral.

This is the subalgebra of Stacks 0820 as data, which is what Stacks 0821 names; the two
assertions the source makes about it are discussed in the implementation notes. -/
@[stacks 0821 "the integral closure of the structure sheaf in an algebra"]
def integralClosureSheaf (A : AlgebraSheaf.{u, m} B S hS F hF) :
    AlgebraSheaf.{u, m} B S hS F hF where
  right := ⟨integralClosurePresheaf A, isSheaf_integralClosurePresheaf A⟩
  algebraMap U := (A.algebraMap U).codRestrict (A.locallyIntegralSections U)
    fun r => A.integralSections_le_locallyIntegralSections U
      (mem_integralSections.2 (isIntegralElem_apply _ r))
  algebraMap_natural i r := Subtype.ext (A.algebraMap_natural i r)

/-- The inclusion of the integral closure into the algebra, as a morphism of algebra sheaves.
On each chart it is the inclusion of the subring of locally integral sections.  It is what makes
the integral closure a *subalgebra* of `A`, as Stacks 0821 names it. -/
@[stacks 0821 "the inclusion exhibiting the integral closure as a subalgebra"]
def integralClosureInclusion (A : AlgebraSheaf.{u, m} B S hS F hF) :
    integralClosureSheaf A ⟶ A where
  right :=
    { hom :=
        { app := fun U => CommRingCat.ofHom (A.locallyIntegralSections U).subtype
          naturality := fun _ _ _ => rfl } }
  comm _ _ := rfl

/-- The inclusion of the integral closure sends a section to its underlying section of `A`. -/
@[simp]
theorem integralClosureInclusion_right_app_apply (A : AlgebraSheaf.{u, m} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) (a : (integralClosureSheaf A).right.obj.obj U) :
    (integralClosureInclusion A).right.hom.app U a = a.1 :=
  rfl

/-- The inclusion of the integral closure is injective on the sections over every chart. -/
theorem integralClosureInclusion_app_injective (A : AlgebraSheaf.{u, m} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Injective (((integralClosureInclusion A).right.hom.app U).hom) :=
  Subtype.val_injective

/-- The inclusion of the integral closure is a monomorphism of the underlying sheaves of
commutative rings: it is injective on sections, and the embedding of sheaves into presheaves
reflects monomorphisms. -/
instance mono_integralClosureInclusion_right (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Mono (integralClosureInclusion A).right := by
  have : ∀ U : (SmallEtale B S hS F)ᵒᵖ,
      Mono ((integralClosureInclusion A).right.hom.app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (integralClosureInclusion_app_injective A U)
  exact (sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m}).mono_of_mono_map
    (NatTrans.mono_of_mono_app (integralClosureInclusion A).right.hom)

/-- The sections of the integral closure over a chart are exactly the locally integral
sections of the algebra. -/
theorem range_integralClosureInclusion_app (A : AlgebraSheaf.{u, m} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    Set.range (((integralClosureInclusion A).right.hom.app U).hom) =
      (A.locallyIntegralSections U : Set _) :=
  Set.ext fun _ => ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

/-- **One inclusion of the sections assertion of Stacks 0820, over an arbitrary chart.**  Every
section of the algebra integral over the structure sheaf is a section of the integral closure.

The integral closure is the sheafification of the integral sections, so this holds over every
chart and needs no hypothesis.  It is the converse inclusion that is restricted to affine
charts and is not available here. -/
theorem integralClosure_le_range_integralClosureInclusion_app
    (A : AlgebraSheaf.{u, m} B S hS F hF) (U : (SmallEtale B S hS F)ᵒᵖ) :
    letI : Algebra ((structureSheaf B S hS F hF).obj.obj U) (A.right.obj.obj U) :=
      (A.algebraMap U).toAlgebra
    (integralClosure ((structureSheaf B S hS F hF).obj.obj U) (A.right.obj.obj U) : Set _) ⊆
      Set.range (((integralClosureInclusion A).right.hom.app U).hom) := by
  intro a ha
  rw [range_integralClosureInclusion_app A U]
  exact A.integralSections_le_locallyIntegralSections U
    (mem_integralSections.2 ((mem_integralSubringOfHom _).1 ha))

/-! ### The assertion that remains -/

/-- Over an affine étale chart every locally integral section of the algebra is already
integral over the structure sheaf.

This is the input to Stacks 0820 that this library cannot supply; the implementation notes
record what discharging it needs. -/
def IsIntegralLocalOnAffineCharts (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      ∀ a : A.right.obj.obj (op U),
        a ∈ A.locallyIntegralSections (op U) → a ∈ A.integralSections (op U)

/-- **The sections assertion of Stacks 0820 over an affine chart**, from
`IsIntegralLocalOnAffineCharts`.  The sections of the integral closure over an affine étale
chart are the integral closure of the ring of functions on the chart in the sections of the
algebra over it. -/
theorem range_integralClosureInclusion_app_eq_integralClosure
    (A : AlgebraSheaf.{u, m} B S hS F hF) (h : A.IsIntegralLocalOnAffineCharts)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    letI : Algebra ((structureSheaf B S hS F hF).obj.obj (op U))
        (A.right.obj.obj (op U)) := (A.algebraMap (op U)).toAlgebra
    Set.range (((integralClosureInclusion A).right.hom.app (op U)).hom) =
      (integralClosure ((structureSheaf B S hS F hF).obj.obj (op U))
        (A.right.obj.obj (op U)) : Set _) := by
  refine le_antisymm ?_ (integralClosure_le_range_integralClosureInclusion_app A (op U))
  rw [range_integralClosureInclusion_app A (op U)]
  intro a ha
  exact (mem_integralSubringOfHom _).2 (mem_integralSections.1 (h U hU a ha))

end AlgebraicGeometry.Space.AlgebraSheaf

end
