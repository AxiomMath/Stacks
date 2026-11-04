module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimits

/-!
# Arbitrary direct sums of modules cartesian on affine charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  An
`𝒪_F`-module `G` on the small étale site of `F` is *cartesian on affine charts*
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`) when for every morphism `f : V ⟶ U` of
affine étale charts the base change comparison `𝒪_F(V) ⊗_{𝒪_F(U)} G(U) ⟶ G(V)` is bijective.

This file proves that **that criterion is stable under coproducts of arbitrary size**, and draws
the two consequences the direct-sum and colimit clauses of Stacks 03M1 need.  Nothing here is
conditional on a cohomological input: the only geometric fact used is that an affine étale chart
is a quasi-compact object of the site, so that the sections of a coproduct of modules over it are
the direct sum of the sections (Stacks 0935), and the rest is the distributivity of the tensor
product over a direct sum.

What the existing toolkit already has, and what this adds.

*The sections half.*  `Stacks.Sites.coproductSectionsMap` below is the **third** comparison map
in the `Stacks.Sites` namespace for the sections of a coproduct from Stacks 0935, part (2), and
both of the others live in files imported here directly:

* `Stacks.Sites.freeSectionsMap`, with `Stacks.Sites.freeSectionsMap_single`,
  `Stacks.Sites.isIso_freeSectionsMap` and `Stacks.Sites.freeSectionsIso`
  (`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections`), compares `I →₀ R(X)` with the
  sections of Mathlib's `SheafOfModules.free I`, the coproduct of `I` copies of the unit module.
* `Stacks.Sites.familySectionsMap`, with `Stacks.Sites.familySectionsMap_single`,
  `Stacks.Sites.familySectionsMap_apply` and `Stacks.Sites.bijective_familySectionsMap`
  (`StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations`), is the closest prior art for the
  map below: the same comparison read on an abstract colimiting cofan, hence for copies of an
  arbitrary sheaf of modules rather than only of the unit module.

Both of those are **constant** families — `I` copies of one summand — and in both the **index
type is pinned to the universe of the module sections**: `I : Type u` with
`SheafOfModules.{u} R` for the first, `I : Type s` with `SheafOfModules.{s} R` for the second.
`Stacks.Sites.coproductSectionsMap` relaxes precisely those two restrictions: the family
`G : ι → SheafOfModules.{m} R` is **arbitrary**, and its index universe `w` is **free** of the
module universe `m` and of the ring universe `r`.  Each relaxation forces one half of the change
of carrier, from `Finsupp` and a morphism of `ModuleCat` to `DirectSum` and a bare `LinearMap`:
an arbitrary family has a different module of sections at each index, so the domain has to be the
dependent `⨁ i, (G i)(X)` and cannot be `I →₀ E(X)`; and at a free index universe that direct sum
lives in `Type (max w m)`, which `ModuleCat.of` cannot accept without forcing `max w m = m`.

*The cartesian half.*
`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian` proves the criterion for the
coproducts of copies of `𝒪_F` — an arbitrary index type, but a constant family — by identifying
their sections with finitely supported families of regular functions, and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi`
(`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase`) proves it for a *finite*
product of an arbitrary family, carrying the bijectivity of the product of the sections over an
affine chart as a hypothesis.  The statements below need neither an identification of the
summands nor a hypothesis about their sections, and the index type is arbitrary: that is what
Stacks 0935 buys.

## Main definitions

* `Stacks.Sites.coproductSectionsMap`: the comparison map from the direct sum of the sections of
  a family of sheaves of modules over an object of the site to the sections of a coproduct of the
  family, sending the `i`-th summand through the `i`-th coproduct injection.

## Main results

* `Stacks.Sites.bijective_coproductSectionsMap`: **the sections of a coproduct of sheaves of
  modules over a quasi-compact object of the site are the direct sum of the sections.**  This is
  the elementwise form of Stacks 0935, part (2); the site, the ring and the module sections have
  independent universes and so has the index type of the family.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_coproduct` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_coproduct`: **a coproduct of `𝒪_F`-modules
  cartesian on affine charts is cartesian on affine charts**, unconditionally and at a free
  module universe.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_coproduct_of_isCartesian`: a coproduct of
  `𝒪_F`-modules cartesian on affine charts is quasi-coherent, unconditionally.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_coproduct_of_h03DX` and
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX`: **the
  direct-sum clause of Stacks 03M1, on the single hypothesis `h03DX`.**
* `AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX`: **the colimit clause of Stacks
  03M1 with its direct-sum hypothesis traded for the cited input `h03DX`**, so that only the
  cokernel clause and `h03DX` remain as hypotheses.

## Implementation notes

**What the comparison map is, and why it is not packaged as a morphism of `ModuleCat`.**  For
`ι : Type w` and sections in `Type m` the direct sum `⨁ i, (G i)(X)` lives in `Type (max w m)`,
while the sections of the coproduct live in `Type m`.  A `LinearMap` between modules in different
universes is perfectly well formed, so `Stacks.Sites.coproductSectionsMap` is stated as one; it
is `ModuleCat.of`, not the map, that would force `max w m = m`.

For the same reason the proof of `Stacks.Sites.bijective_coproductSectionsMap` cannot build the
inverse by the universal property of the coproduct with the direct sum as the target — that
target is not an object of `AddCommGrpCat.{m}` unless `w ≤ m`.  Both halves are therefore proved
with targets inside `AddCommGrpCat.{m}`:

* injectivity by the *preadditive projections* of the colimit cofan.  For `j : ι` the projection
  is the map out of the coproduct whose `i`-th leg is `DirectSum.component j ∘ DirectSum.lof i`;
  that leg is the Kronecker delta at `i = j` with no transport along a proof of `i = j`, which is
  what keeps the construction free of `eqToHom`.  Composing a projection with the comparison map
  gives the corresponding component of the direct sum, so an element of the kernel has all
  components zero.
* surjectivity by the *quotient* of the sections by the range of the comparison map.  The
  projection to that quotient kills every coproduct injection, hence is zero by the universal
  property, hence the range is everything.

**The hypotheses, and which are inhabited.**  The hypothesis that the summands are cartesian on
affine charts is inhabited: `AlgebraicGeometry.Space.isCartesianOnAffineCharts_unit` and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free` exhibit `𝒪_F` and the free modules, so
a constant family of copies of `𝒪_F` satisfies it.  `h03DX` is the implication
"quasi-coherent ⟹ cartesian on affine charts" of Descent, Proposition 03DX(2), carried in the
spelling

    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)

which `StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent` and
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite` already carry verbatim, so
the same cited input serves these conclusions with no adapter.  Its converse is not a hypothesis:
it is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.

**Universes.**  Everything above the two quasi-coherence statements holds at a free module
universe `m`.  The two statements that conclude quasi-coherence are at `m := u`, because
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` is, and so is the
`h03DX` spelling.  The index type of the family and the shape of the diagram keep their own
independent universes throughout; in particular
`AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX` has the shape universes of the source,
as `AlgebraicGeometry.Space.isQuasicoherent_colimit` does.

**No `@[stacks 03M1]` attribute is claimed, and no clause of Stacks 03M1 is proved outright.**
The unconditional statements assume the summands *cartesian on affine charts*, which is formally
stronger than the quasi-coherence that clause (1) of Stacks 03M1 assumes — the implication from
quasi-coherence is exactly the unavailable `h03DX` — and the two statements that do assume only
quasi-coherence carry `h03DX`.  The colimit statement carries in addition the cokernel clause of
the same tag, as `AlgebraicGeometry.Space.isQuasicoherent_colimit` does.  What changes here is
that the direct-sum clause is no longer an input to the colimit clause.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules DirectSum

universe w w' m r v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The comparison map from the direct sum of the sections of a family `G` of sheaves of
`R`-modules over an object `X` of the site to the sections over `X` of a coproduct `c` of the
family: the `R(X)`-linear map carrying the `i`-th summand through the `i`-th coproduct injection.

It is bijective over a quasi-compact object of the site, by
`Stacks.Sites.bijective_coproductSectionsMap`, but not in general: a coproduct of sheaves of
modules is the sheafification of the objectwise direct sum.

It generalises the two comparison maps of this namespace that precede it, in two independent
respects.  `Stacks.Sites.freeSectionsMap`
(`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections`) does this for Mathlib's
`SheafOfModules.free I`, and `Stacks.Sites.familySectionsMap`
(`StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations`) for an abstract colimiting cofan of
copies of a single sheaf of modules; both are *constant* families, and both pin the index type to
the universe of the module sections.  Here the family is arbitrary and the index universe `w` is
free, and that is what changes the carrier.  Because the family is arbitrary the summands have
different modules of sections, so the domain is the dependent `⨁ i, (G i)(X)` rather than the
`Finsupp` on one module of sections that those two maps use; and because the index universe is
free the direct sum lives in
`Type (max w m)` while the sections live in `Type m`, so this is stated as a `LinearMap` rather
than as a morphism of `ModuleCat`.  See the implementation notes. -/
noncomputable def coproductSectionsMap {ι : Type w} [DecidableEq ι]
    {G : ι → SheafOfModules.{m} R} (c : Cofan G) (X : Cᵒᵖ) :
    (⨁ i, ((G i).val.obj X : Type m)) →ₗ[R.obj.obj X] (c.pt.val.obj X : Type m) :=
  DirectSum.toModule (R.obj.obj X) ι _ (fun i => ((c.inj i).val.app X).hom)

/-- The comparison map sends the `i`-th summand through the `i`-th coproduct injection. -/
theorem coproductSectionsMap_lof {ι : Type w} [DecidableEq ι]
    {G : ι → SheafOfModules.{m} R} (c : Cofan G) (X : Cᵒᵖ) (i : ι) (x : (G i).val.obj X) :
    coproductSectionsMap c X (DirectSum.lof (R.obj.obj X) ι _ i x) =
      ((c.inj i).val.app X).hom x :=
  DirectSum.toModule_lof _ _ _

section

variable {ι : Type w} {G : ι → SheafOfModules.{m} R}

/-- Sections over an object of the site, as a functor to abelian groups: the composite of the
passage to the underlying sheaf of abelian groups with evaluation. -/
private noncomputable abbrev sectionsFunctorAt (W : C) :
    SheafOfModules.{m} R ⥤ AddCommGrpCat.{m} :=
  SheafOfModules.toSheaf.{m} R ⋙ (sheafSections J AddCommGrpCat.{m}).obj (op W)

/-- The cofan of the sections of a coproduct of sheaves of modules over a quasi-compact object of
the site is a colimit cofan of abelian groups.  This is Stacks 0935, part (2), applied to the
given colimit cofan. -/
private noncomputable def isColimitSectionsCofan (c : Cofan G) (hc : IsColimit c)
    (W : C) (hW : J.IsQuasiCompactObject W) :
    IsColimit (Cofan.mk ((sectionsFunctorAt (J := J) (R := R) W).obj c.pt)
      (fun i => (sectionsFunctorAt (J := J) (R := R) W).map (c.inj i))) :=
  haveI := sheafOfModules_sections_preserves_coproducts J R W hW ι
  Cofan.isColimitMapCoconeEquiv (sectionsFunctorAt (J := J) (R := R) W) G c
    (isColimitOfPreserves (sectionsFunctorAt (J := J) (R := R) W) hc)

/-- **The sections of a coproduct of sheaves of modules over a quasi-compact object of the site
are the direct sum of the sections of the summands.**

This is the elementwise form of Stacks 0935, part (2), which gives the same statement as
preservation of coproducts by the sections functor.  Injectivity is proved by the preadditive
projections of the colimit cofan and surjectivity by the quotient of the sections by the range;
neither construction leaves the universe of the sections, which is what the direct sum itself
does.  See the implementation notes. -/
theorem bijective_coproductSectionsMap [DecidableEq ι] (c : Cofan G) (hc : IsColimit c)
    (W : C) (hW : J.IsQuasiCompactObject W) :
    Function.Bijective (coproductSectionsMap c (op W)) := by
  classical
  have hcof := isColimitSectionsCofan c hc W hW
  set A := R.obj.obj (op W) with hA
  set β : ι → Type m := fun i => ((G i).val.obj (op W) : Type m) with hβ
  set p : ∀ j : ι, (sectionsFunctorAt (J := J) (R := R) W).obj c.pt ⟶
      (sectionsFunctorAt (J := J) (R := R) W).obj (G j) := fun j =>
    Cofan.IsColimit.desc hcof (fun i => AddCommGrpCat.ofHom
      (((DirectSum.component A ι β j).comp (DirectSum.lof A ι β i)).toAddMonoidHom)) with hp
  have hpfac : ∀ (j i : ι) (x : β i),
      (p j).hom (((c.inj i).val.app (op W)).hom x) =
        DirectSum.component A ι β j (DirectSum.lof A ι β i x) := by
    intro j i x
    have h := Cofan.IsColimit.fac hcof (fun i => AddCommGrpCat.ofHom
      (((DirectSum.component A ι β j).comp (DirectSum.lof A ι β i)).toAddMonoidHom)) i
    exact ConcreteCategory.congr_hom h x
  have key : ∀ (j : ι) (z : ⨁ i, β i),
      (p j).hom (coproductSectionsMap c (op W) z) = DirectSum.component A ι β j z := by
    intro j z
    induction z using DirectSum.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact map_zero (p j).hom
    | of i x =>
      rw [← DirectSum.lof_eq_of A, coproductSectionsMap_lof]
      exact hpfac j i x
    | add z w hz hw =>
      rw [map_add, map_add, ← hz, ← hw]
      exact map_add (p j).hom _ _
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine DFinsupp.ext fun j => ?_
    have h1 := key j x
    have h2 := key j y
    rw [hxy] at h1
    exact h1.symm.trans h2
  · set H : AddSubgroup (c.pt.val.obj (op W) : Type m) :=
      (coproductSectionsMap c (op W)).toAddMonoidHom.range with hH
    set Q : AddCommGrpCat.{m} := AddCommGrpCat.of ((c.pt.val.obj (op W) : Type m) ⧸ H) with hQ
    set π : (sectionsFunctorAt (J := J) (R := R) W).obj c.pt ⟶ Q :=
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' H) with hπ
    have hzero : π = 0 := by
      refine Cofan.IsColimit.hom_ext hcof π 0 fun i => ?_
      have hi : (Cofan.mk ((sectionsFunctorAt (J := J) (R := R) W).obj c.pt)
          (fun i => (sectionsFunctorAt (J := J) (R := R) W).map (c.inj i))).inj i =
          (sectionsFunctorAt (J := J) (R := R) W).map (c.inj i) := rfl
      rw [hi, comp_zero]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      have hmem : ((c.inj i).val.app (op W)).hom x ∈ H :=
        ⟨DirectSum.lof A ι β i x, coproductSectionsMap_lof c (op W) i x⟩
      show QuotientAddGroup.mk' H (((c.inj i).val.app (op W)).hom x) = 0
      exact (QuotientAddGroup.eq_zero_iff _).2 hmem
    have hy : QuotientAddGroup.mk' H y = 0 :=
      ConcreteCategory.congr_hom hzero y
    exact (QuotientAddGroup.eq_zero_iff _).1 hy

end

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The base change comparison of a coproduct of `𝒪_F`-modules between two affine charts is
bijective as soon as the comparisons of the summands are.**

Both charts being affine makes them quasi-compact objects of the small étale site, so the
sections of the coproduct over each of them are the direct sum of the sections of the summands
(`Stacks.Sites.bijective_coproductSectionsMap`).  Through those identifications the base change
comparison of the coproduct becomes the direct sum of the base change comparisons of the
summands: the tensor product distributes over a direct sum by
`TensorProduct.directSumRight`, and restriction of sections commutes with the coproduct
injections by naturality.  No cohomological input is used. -/
theorem bijective_sectionsBaseChange_coproduct {ι : Type w}
    {G : ι → Modules.{u, m} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hG : ∀ i, Function.Bijective (sectionsBaseChange (G i) f)) :
    Function.Bijective (sectionsBaseChange c.pt f) := by
  classical
  let _ := chartAlgebra (hF := hF) f
  let eU := LinearEquiv.ofBijective (Stacks.Sites.coproductSectionsMap c (op U))
    (Stacks.Sites.bijective_coproductSectionsMap c hc U
      (isQuasiCompactObject_of_isAffine B S hS F U hU))
  let eV := LinearEquiv.ofBijective (Stacks.Sites.coproductSectionsMap c (op V))
    (Stacks.Sites.bijective_coproductSectionsMap c hc V
      (isQuasiCompactObject_of_isAffine B S hS F V hV))
  let t2 := TensorProduct.directSumRight (chartRing B S hS F hF U) (chartRing B S hS F hF V)
    (chartRing B S hS F hF V) (fun i => ((G i).val.obj (op U) : Type m))
  let t3 := DirectSum.lmap (R := chartRing B S hS F hF V)
    (fun i => sectionsBaseChange (G i) f)
  let t1 := LinearEquiv.lTensor (chartRing B S hS F hF V) eU
  have key : ∀ z, sectionsBaseChange c.pt f (t1 z) = eV (t3 (t2 z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b y =>
      induction y using DirectSum.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | of i x =>
        rw [← DirectSum.lof_eq_of (chartRing B S hS F hF U)]
        have h1 : t1 (TensorProduct.tmul _ b
            (DirectSum.lof (chartRing B S hS F hF U) ι _ i x)) =
            TensorProduct.tmul _ b (eU (DirectSum.lof (chartRing B S hS F hF U) ι _ i x)) := rfl
        have h2 : eU (DirectSum.lof (chartRing B S hS F hF U) ι _ i x) =
            ((c.inj i).val.app (op U)).hom x :=
          Stacks.Sites.coproductSectionsMap_lof c (op U) i x
        have h3 : t2 (TensorProduct.tmul _ b
            (DirectSum.lof (chartRing B S hS F hF U) ι _ i x)) =
            DirectSum.lof (chartRing B S hS F hF V) ι _ i (TensorProduct.tmul _ b x) :=
          TensorProduct.directSumRight_tmul_lof (chartRing B S hS F hF U)
            (chartRing B S hS F hF V) (M₁' := chartRing B S hS F hF V)
            (M₂ := fun i => ((G i).val.obj (op U) : Type m)) b i x
        rw [h1, h2, h3, chartBaseChange_tmul, DirectSum.lmap_lof]
        have h4 : eV (DirectSum.lof (chartRing B S hS F hF V) ι _ i
            (sectionsBaseChange (G i) f (TensorProduct.tmul _ b x))) =
            ((c.inj i).val.app (op V)).hom
              (sectionsBaseChange (G i) f (TensorProduct.tmul _ b x)) :=
          Stacks.Sites.coproductSectionsMap_lof c (op V) i _
        rw [h4, chartBaseChange_tmul,
          map_smul ((c.inj i).val.app (op V)).hom b (chartRestrictLinear (G i) f x)]
        exact congrArg (fun z => b • z)
          (PresheafOfModules.naturality_apply (c.inj i).val f.op x).symm
      | add y₁ y₂ h₁ h₂ =>
        simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hbij : Function.Bijective (fun z => eV (t3 (t2 z))) := by
    refine eV.bijective.comp (Function.Bijective.comp ?_ t2.bijective)
    exact ⟨(DirectSum.lmap_injective _).2 fun i => (hG i).1,
      (DirectSum.lmap_surjective _).2 fun i => (hG i).2⟩
  have hfun : ⇑(sectionsBaseChange c.pt f) = (fun z => eV (t3 (t2 z))) ∘ t1.symm := by
    funext y
    have h := key (t1.symm y)
    rw [t1.apply_symm_apply] at h
    exact h
  rw [hfun]
  exact hbij.comp t1.symm.bijective

/-- **A coproduct of `𝒪_F`-modules cartesian on affine charts is cartesian on affine charts**,
unconditionally and at a free module universe.

This is `AlgebraicGeometry.Space.bijective_sectionsBaseChange_coproduct` at every pair of affine
charts.  Unlike `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan`, which is
about the coproducts of copies of `𝒪_F` appearing in a global presentation, the summands here are
an arbitrary family. -/
theorem isCartesianOnAffineCharts_coproduct {ι : Type w}
    {G : ι → Modules.{u, m} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, IsCartesianOnAffineCharts (G i)) :
    IsCartesianOnAffineCharts c.pt := by
  classical
  exact fun U V hU hV f =>
    bijective_sectionsBaseChange_coproduct B S hS F hF c hc f hU hV fun i => hG i U V hU hV f

/-- **A coproduct of `𝒪_F`-modules cartesian on affine charts is quasi-coherent on the small
étale site of the algebraic space**, unconditionally.

This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_coproduct` followed by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, which is where the
module universe `m := u` comes from.

It is *not* the direct-sum clause of Stacks 03M1: that clause assumes the summands only
quasi-coherent, and the passage from quasi-coherence to the base change criterion is the
unavailable implication of Descent, Proposition 03DX(2).  See
`AlgebraicGeometry.Space.isQuasicoherentOnSite_coproduct_of_h03DX`. -/
theorem isQuasicoherentOnSite_coproduct_of_isCartesian {ι : Type w}
    {G : ι → Modules.{u, u} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, IsCartesianOnAffineCharts (G i)) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts c.pt
    (isCartesianOnAffineCharts_coproduct B S hS F hF c hc hG)

/-- **The direct-sum clause of Stacks 03M1, for one coproduct, on the single hypothesis
`h03DX`.**  A coproduct of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the
implication "quasi-coherent ⟹ cartesian on affine charts" of Descent, Proposition 03DX(2).

The route is: each summand is cartesian on affine charts by `h03DX`, hence so is the coproduct
by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_coproduct`, hence the coproduct is
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.
The index type of the family is arbitrary and no refinement of coverings is involved, which is
what the presentation route could not achieve: a Grothendieck topology is closed under binary
intersections only, so infinitely many coverings have no common refinement. -/
theorem isQuasicoherentOnSite_coproduct_of_h03DX
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    {ι : Type w} {G : ι → Modules.{u, u} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_coproduct_of_isCartesian B S hS F hF c hc fun i => h03DX _ (hG i)

/-- **The direct-sum clause of Stacks 03M1 as a closure property of the quasi-coherent modules,
on the single hypothesis `h03DX`.**

This is the shape in which the colimit clause of Stacks 03M1 consumes the direct-sum clause: the
hypothesis `hsum` of `AlgebraicGeometry.Space.isQuasicoherent_colimit`.  An object of the
property is by construction a chosen colimit `colimit F` of a diagram `F : Discrete ι ⥤ _`; it is
identified with the coproduct of the family `fun i ↦ F.obj ⟨i⟩` by
`CategoryTheory.Limits.HasColimit.isoOfNatIso` and
`CategoryTheory.Discrete.natIsoFunctor`, and quasi-coherence transports along that isomorphism. -/
theorem isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    (ι : Type w) [HasColimitsOfShape (Discrete ι) (Modules.{u, u} B S hS F hF)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape (Discrete ι) := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨D, hD⟩
  have h : (∐ fun i => D.obj ⟨i⟩).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_coproduct_of_h03DX B S hS F hF h03DX _
      (coproductIsCoproduct fun i => D.obj ⟨i⟩) fun i => hD ⟨i⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := D))).symm h

/-- **The colimit clause of Stacks 03M1 with its direct-sum hypothesis traded for the cited input
`h03DX`.**  A colimit of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the implication
"quasi-coherent ⟹ cartesian on affine charts" of Descent, Proposition 03DX(2) and the cokernel
clause of Stacks 03M1 itself.

This is `AlgebraicGeometry.Space.isQuasicoherent_colimit` with its hypothesis `hsum` supplied by
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX`.  The
trade is not a gain in strength, and is not claimed as one: that theorem derives `hsum` from
`h03DX`, so the hypotheses here *imply* the hypotheses of
`AlgebraicGeometry.Space.isQuasicoherent_colimit` and this statement is formally **weaker** than
it.  What changes is that the direct-sum clause of Stacks 03M1 is no longer an input to the
colimit clause.  The
shape of the diagram has its objects and its morphisms in independent universes, as in the
source; the module universe is `u` rather than free, because `h03DX` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` are stated there. -/
theorem isQuasicoherent_colimit_of_h03DX {K : Type w} [Category.{w'} K]
    [HasCoproducts.{max w w'} (Modules.{u, u} B S hS F hF)]
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    (hcoker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels)
    (D : K ⥤ Modules.{u, u} B S hS F hF) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (Limits.colimit D).IsQuasicoherentOnSite :=
  isQuasicoherent_colimit B S hS F hF
    (fun I => isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX B S hS F hF h03DX I)
    hcoker D hD

end AlgebraicGeometry.Space

end
