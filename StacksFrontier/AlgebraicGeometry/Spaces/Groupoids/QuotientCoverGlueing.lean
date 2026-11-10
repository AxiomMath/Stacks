module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafFppfOpenImmersion

/-!
# Glueing a quotient sheaf along a covering of its object scheme

Let `j = (t, s) : R ⟶ U ×_S U` be an equivalence relation on an object `U` of the big fppf site
of `S` whose source and target are surjective, flat and locally of finite presentation, and let
`gᵢ : Uᵢ ⟶ U` be a covering family of the site whose members are flat and locally of finite
presentation.  If every restricted quotient `Uᵢ/Rᵢ` is an algebraic space with an atlas bounded
by one infinite cardinal `μ` below the cutoff of the site, and the index type has cardinality at
most `μ`, then `U/R` is an algebraic space.

The three inputs are [Stacks, Tag 02WU], that `Uᵢ/Rᵢ ⟶ U/R` is a representable open immersion;
[Stacks, Tag 02WQ] in the form that bounds the atlas, that the coproduct of the `Uᵢ/Rᵢ` is an
algebraic space; and [Stacks, Tag 02WR], that a sheaf covered by open algebraic subsheaves whose
coproduct is an algebraic space is an algebraic space.  The covering map out of the coproduct is
locally surjective because the chart `h_U ⟶ U/R` is and the family `h_{Uᵢ} ⟶ h_U` is.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_quotientSheaf_of_coveringAtlases`: the glueing step.

## Implementation notes

The index type lives in `Type u` and is bounded by `μ`, not by the cofinality of the cutoff:
the cofinality-free form of [Stacks, Tag 02WR]
(`AlgebraicGeometry.isAlgebraicSpace_of_open_cover`) asks instead that the coproduct be an
algebraic space, and that is what `AlgebraicGeometry.Space.isAlgebraicSpaceAtlasSizeLE_coproduct`
supplies from the bound on the atlases.  This is why the pieces are required to carry a *bounded*
atlas rather than merely to be algebraic spaces.

Local surjectivity of the covering map is deduced from local surjectivity of the chart by
factoring: on the `i`-th summand the composite of the chart of `Uᵢ/Rᵢ` with the covering map is
`h_{gᵢ}` followed by the chart of `U/R`
(`Stacks.Groupoids.quotientChart_comp_restrictQuotientSheafMap`), so the covering map receives a
locally surjective map out of the coproduct of the `h_{Uᵢ}` and is therefore itself locally
surjective.

## References

* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **The glueing step of [Stacks, Tag 04S6] condition (2).**

An equivalence relation on an object of the big fppf site of `S` whose source and target are
surjective, flat and locally of finite presentation, and which restricts along a covering family
of flat, locally finitely presented morphisms to relations whose quotient sheaves are algebraic
spaces with atlases uniformly bounded by an infinite cardinal `μ` below the cutoff, over an
index type of cardinality at most `μ`, has algebraic quotient sheaf. -/
theorem isAlgebraicSpace_quotientSheaf_of_coveringAtlases
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S} {U : BigFppfOver B S hS}
    (j : PreRelation R ((Over.post (X := B.obj hS) B.inclusion).obj U))
    [CategoryTheory.IsEquivalenceRelation j.target j.source]
    (hssurj : Surjective j.source.left) (htsurj : Surjective j.target.left)
    (hsflat : Flat j.source.left) (htflat : Flat j.target.left)
    (hslfp : LocallyOfFinitePresentation j.source.left)
    (htlfp : LocallyOfFinitePresentation j.target.left)
    {I : Type u} (Ui : I → BigFppfOver B S hS) (gi : ∀ i, Ui i ⟶ U)
    (hgflat : ∀ i, Flat ((Over.post (X := B.obj hS) B.inclusion).map (gi i)).left)
    (hglfp : ∀ i, LocallyOfFinitePresentation
      ((Over.post (X := B.obj hS) B.inclusion).map (gi i)).left)
    (hcov : Sieve.ofArrows Ui gi ∈ BigFppfOver.topology B S hS U)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hI : #I ≤ μ)
    (hpieces : ∀ i, Space.IsAlgebraicSpaceAtlasSizeLE B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion)
        (PreRelation.restrict j
          ((Over.post (X := B.obj hS) B.inclusion).map (gi i)))).obj μ) :
    IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) j).obj := by
  classical
  have _ : HasColimitsOfShape (Discrete I)
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) := Sheaf.instHasColimitsOfShape
  have _ : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have _ : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  set Fsh : I → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun i =>
    Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (PreRelation.restrict j ((Over.post (X := B.obj hS) B.inclusion).map (gi i))) with hFsh
  have hGcolim : IsColimit (Cofan.mk (∐ Fsh) (Sigma.ι Fsh)) := coproductIsCoproduct Fsh
  have hGatlas : Space.IsAlgebraicSpaceAtlasSizeLE B S hS (∐ Fsh).obj μ :=
    Space.isAlgebraicSpaceAtlasSizeLE_coproduct B S hS (fun i => (Fsh i).obj) hℵ hμ hI hpieces
      (∐ Fsh) (fun i => Sigma.ι Fsh i) hGcolim
  set gmap : (∐ Fsh) ⟶ Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) j :=
    Sigma.desc fun i => Stacks.Groupoids.restrictQuotientSheafMap
      (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion) j
      ((Over.post (X := B.obj hS) B.inclusion).map (gi i)) with hgmap
  have hfac (i : I) : Sigma.ι Fsh i ≫ gmap =
      Stacks.Groupoids.restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) j
        ((Over.post (X := B.obj hS) B.inclusion).map (gi i)) := by
    rw [hgmap]
    exact Sigma.ι_comp_desc _ i
  have hfach (i : I) : (Sigma.ι Fsh i).hom ≫ gmap.hom =
      (Stacks.Groupoids.restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) j
        ((Over.post (X := B.obj hS) B.inclusion).map (gi i))).hom := by
    rw [← hfac i]
    rfl
  have hopen : ∀ i, Space.IsOpenImmersion B S hS ((Sigma.ι Fsh i).hom ≫ gmap.hom) := by
    intro i
    rw [hfach i]
    exact isOpenImmersion_restrictedQuotientMap B hS j
      ((Over.post (X := B.obj hS) B.inclusion).map (gi i)) hssurj htsurj hsflat htflat hslfp
      htlfp (hgflat i) (hglfp i)
  have hchart : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) U j) :=
    Stacks.Groupoids.isLocallySurjective_quotientChart _ _ U j
  have hcovsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i => yoneda.map (gi i)) :=
    Space.locallySurjective_sigmaDesc_yoneda_map (BigFppfOver.topology B S hS) gi hcov
  set α : (∐ fun i => yoneda.obj (Ui i)) ⟶ (∐ Fsh).obj :=
    Sigma.desc fun i =>
      Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (Ui i)
        (PreRelation.restrict j ((Over.post (X := B.obj hS) B.inclusion).map (gi i))) ≫
        (Sigma.ι Fsh i).hom with hα
  have hαfac : α ≫ gmap.hom = (Sigma.desc fun i => yoneda.map (gi i)) ≫
      Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) U j := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [hα, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc, Category.assoc, hfach i,
      Stacks.Groupoids.quotientChart_comp_restrictQuotientSheafMap _ _ j (gi i)]
  have _ := hcovsurj
  have _ := hchart
  have hcomp : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (α ≫ gmap.hom) := by
    rw [hαfac]
    infer_instance
  have _ := hcomp
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) gmap.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective _ α gmap.hom
  exact isAlgebraicSpace_of_open_cover B S hS
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) j).obj
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) j).property
    I Fsh (fun i => (hpieces i).1) (∐ Fsh) (fun i => Sigma.ι Fsh i) hGcolim gmap.hom hopen hsurj
    hGatlas.1

end AlgebraicGeometry

end
