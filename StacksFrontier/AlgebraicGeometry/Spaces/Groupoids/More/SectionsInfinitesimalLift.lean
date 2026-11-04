module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalDiff
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# The comorphism moved by a linear map, and the morphism of charts it induces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `R₀ = s^{-1}(U₀) ⊆ R` with inclusion `j : R₀ ⟶ R`, and let
`e₀ : U₀ ⟶ R₀` be the unit of the restricted groupoid.
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalDiff.lean` attaches to
two elements of `Γ₀` the `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which they differ.

This file performs the first half of the converse — the existence half of
[Stacks Project, Tag 04D0] in this situation.  Given `δ ∈ Γ₀` and an `𝒪_{U₀}`-linear map `θ`,
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` moves the transported comorphism of `δ` by the
`𝒪_{U₀}`-derivation attached to `θ` by Equation [Stacks Project, Tag 0619] and produces a second
solution

`g = δ^♯ − ι ∘ D ∘ j^♯ : j^{-1}𝒪_R ⟶ (e₀)_*(i^{-1}𝒪_U)`

of the lifting problem whose descended difference from `δ^♯` is `θ` again.  What is proved here
is that `g` **agrees with the transported comorphism of `δ` on every regular function read from
`U` along the source**, which is what makes the chart morphism it induces over an affine chart a
morphism of the big fppf category over `S`, by
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`.

The agreement is the geometry of the source's argument, and it is spent here exactly once.  A
regular function read from `U` along `s` is, on the chart of `R₀`, a value of `j^♯` at a function
read from `U` along `j ≫ s`; the square `j ≫ s = s₀ ≫ i` turns that into a value of
`s₀^♯ : s₀^{-1}𝒪_{U₀} ⟶ 𝒪_{R₀}`; and the derivation attached to `θ` kills those, which is the
field `d_app` of Equation (0619).

## Main definitions

* `infinitesimalSectionLiftData`: **the pair `(δ^♯, g)` of solutions of the lifting problem**,
  `g` being `δ^♯` moved by the derivation attached to `θ`.

## Main results

* `derivationFamilyOfHom_app_source_eq_zero`: **the derivation attached to `θ` kills every
  function read from `U` along the source.**
* `inverseImage_source_comp_infinitesimalSectionLiftData_g_eq`: **the moved solution agrees with
  the transported comorphism of `δ` after `j^{-1}(s^♯)`**, which is the hypothesis under which
  the chart morphism it induces is a morphism over the base.
* `exists_infinitesimalSectionLiftChartSiteHom`: **the morphism of charts attached to the moved
  solution is a morphism of the big fppf category over `S`**, over an affine chart of `U`
  carrying an affine chart diagram over the source.
* `comp_source_eq_of_infinitesimalSectionLiftChartSiteHom`: **that morphism of charts is a
  section of the source**, the first clause of the lifting condition for the sheaf of lifts of
  Equation [Stacks Project, Tag 0CKE].
* `infinitesimalSectionLiftData_g_comp_reduction_eq`: **the moved solution still restricts to
  `e₀ ≫ j` on the thickening**, its reduction being `j^♯` followed by the comorphism of `e₀`,
  and `infinitesimalSectionLiftData_comp_reduction_eq` the same read on the ambient site of `R`
  at the tautological index.
* `comp_restriction_eq_of_infinitesimalSectionLiftChartSiteHom`: **that morphism of charts
  agrees with the unit on the part of the chart lying in `U₀`**, the second clause of the
  lifting condition for the sheaf of lifts of Equation [Stacks Project, Tag 0CKE].
* `mem_infinitesimalSectionsLiftSheaf_of_infinitesimalSectionLiftChartSiteHom`: **both clauses
  together** — the morphism of charts attached to the moved solution is a section of the sheaf
  of lifts over the chart of `U`.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)

/-! ### The derivation attached to a linear map kills the functions read from `U` -/

/-- **The derivation attached to `θ` by Equation [Stacks Project, Tag 0619] kills every regular
function read from `U` along the source.**

A section of `j^{-1}(s^{-1}𝒪_U)` is carried by `j^♯` to a value of
`s₀^♯ : s₀^{-1}𝒪_{U₀} ⟶ 𝒪_{R₀}`: the two readings of the pullback — along `j ≫ s` and along
`s₀ ≫ i` — are identified by the commutative square `j ≫ s = s₀ ≫ i`, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_structureSharpInverseImage_square`.  And the
derivation attached to `θ` kills the values of `s₀^♯`, which is the field `d_app` of
Equation (0619). -/
theorem derivationFamilyOfHom_app_source_eq_zero (θ : InfinitesimalSectionsHom G U₀)
    (V : (Space.SmallEtale C S hS
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).obj
      (inverseImageStructureSheaf C S hS G.source)).obj.obj V)) :
    derivationFamilyOfHom C S hS (preimageProjection C S hS G.source U₀)
        (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀) θ V
      ((structureSharpRingInverseImage C S hS
          (subspaceInclusion C S hS G.arrows
            (preimageSubspace C S hS G.source U₀))).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU C S hS
              (subspaceInclusion C S hS G.arrows
                (preimageSubspace C S hS G.source U₀)))).map
            (structureSharpRingInverseImage C S hS G.source)).hom.app V x)) = 0 := by
  have hval : (structureSharpRingInverseImage C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).hom.app V
      (((inverseImageRingFunctor (smallToposMorphismTypeU C S hS
            (subspaceInclusion C S hS G.arrows
              (preimageSubspace C S hS G.source U₀)))).map
          (structureSharpRingInverseImage C S hS G.source)).hom.app V x) =
      (structureSharpInverseImage C S hS
          (preimageProjection C S hS G.source U₀)).hom.app V
        (((smallEtaleInverseImageRing C S hS
              (preimageProjection C S hS G.source U₀)).map
            (structureSharpInverseImage C S hS
              (subspaceInclusion C S hS G.objects U₀))).hom.app V
          ((smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
            (restrictedArrows_square G U₀)).hom.hom.app V x)) :=
    (congrArg (fun z ↦ (structureSharpRingInverseImage C S hS
          (subspaceInclusion C S hS G.arrows
            (preimageSubspace C S hS G.source U₀))).hom.app V z)
        (app_inverseImage_structureSharpRingInverseImage C S hS
          (subspaceInclusion C S hS G.arrows
            (preimageSubspace C S hS G.source U₀)) G.source V x)).trans
      ((structureSharpRingInverseImage_app C S hS
            (subspaceInclusion C S hS G.arrows
              (preimageSubspace C S hS G.source U₀)) V _).trans
        (app_structureSharpInverseImage_square G U₀ V x).symm)
  rw [hval]
  exact derivationFamilyOfHom_app C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀) θ V _

/-! ### The moved solution of the lifting problem -/

variable (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- **The transported comorphism of `δ` and the one it is moved to by the derivation attached to
`θ`**, as a `Stacks.Sites.LiftDifferenceData` for the quotient map
`j^♯ : j^{-1}𝒪_R ⟶ 𝒪_{R₀}`.  This is `AlgebraicGeometry.Space.liftDifferenceDataOfHom` in the
groupoid situation: its second map is

`g = δ^♯ − ι ∘ D ∘ j^♯ : j^{-1}𝒪_R ⟶ (e₀)_*(i^{-1}𝒪_U)`,

the solution of the lifting problem whose descended difference from `δ^♯` is `θ`. -/
noncomputable def infinitesimalSectionLiftData (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    Stacks.Sites.LiftDifferenceData
      (structureSharpRingInverseImage C S hS
        (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀)))
      (restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
        (restrictedUnit G U₀) hU₀) :=
  liftDifferenceDataOfHom C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (E := restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
      (restrictedUnit G U₀) hU₀)
    (restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
      δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2))
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀ δ.1.1
      (comp_eq_restrictedUnit_comp G U₀ δ.2) x m)
    θ

include hU₀ in
/-- The first map of the pair is the transported comorphism of `δ`. -/
theorem infinitesimalSectionLiftData_f (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    (infinitesimalSectionLiftData G U₀ hU₀ δ θ).f =
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2) := rfl

include hU₀ in
/-- **The moved solution agrees with the transported comorphism of `δ` after `j^{-1}(s^♯)`:**
the two differ by the derivation attached to `θ`, which kills the functions read from `U` along
the source.

This is the hypothesis under which the chart morphism attached to the moved solution is a
morphism over the base. -/
theorem inverseImage_source_comp_infinitesimalSectionLiftData_g_eq
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀) :
    (inverseImageRingFunctor (smallToposMorphismTypeU C S hS
          (subspaceInclusion C S hS G.arrows
            (preimageSubspace C S hS G.source U₀)))).map
          (structureSharpRingInverseImage C S hS G.source) ≫
        (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g =
      (inverseImageRingFunctor (smallToposMorphismTypeU C S hS
          (subspaceInclusion C S hS G.arrows
            (preimageSubspace C S hS G.source U₀)))).map
          (structureSharpRingInverseImage C S hS G.source) ≫
        restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
          δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2) := by
  have := isLocallySurjective_restrictedArrowsSharp G U₀
  exact comp_liftDifferenceDataOfHom_g_eq C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (E := restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
      (restrictedUnit G U₀) hU₀)
    (restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
      δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2))
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀ δ.1.1
      (comp_eq_restrictedUnit_comp G U₀ δ.2) x m)
    θ
    ((inverseImageRingFunctor (smallToposMorphismTypeU C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀)))).map
      (structureSharpRingInverseImage C S hS G.source))
    (derivationFamilyOfHom_app_source_eq_zero G U₀ θ)

/-! ### The morphism of charts attached to the moved solution -/

include hU₀ in
/-- **The morphism of étale scheme charts attached to the moved solution is a morphism of the
big fppf category over `S`.**

Let `V'` be an affine étale scheme chart of `U`, let `m` be an affine étale scheme chart of `R`
above `R ×_U V'` — so that the structure morphism of `m` factors through the affine scheme `V'`,
by the morphism of charts `s` induces — and let `j` be an étale scheme chart of `U` above
`U ×_R m`.  Then the morphism of schemes which the moved solution `g`, carried back to the small
étale site of `R`, induces from the chart `j` to the chart `m` commutes with the structure
morphisms to `S`, and so lifts to the site.

This is `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index` with its hypothesis
discharged by `inverseImage_source_comp_infinitesimalSectionLiftData_g_eq`: the comparison is
made at `V'`, where `AlgebraicGeometry.ext_of_isAffine` applies, and what has to be checked there
is agreement on the regular functions pulled back from `V'`, which are values of `s^♯`. -/
theorem exists_infinitesimalSectionLiftChartSiteHom (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) (V' : Space.SmallEtale C S hS G.objects.1)
    (m : StructuredArrow (op (chartBaseChange C S hS G.source V'))
      (comparisonFunctor C S hS G.arrows).op)
    (jc : StructuredArrow (op (chartBaseChange C S hS δ.1.1 m.right.unop))
      (comparisonFunctor C S hS G.objects).op)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.objects.1).obj V'))] :
    ∃ ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj jc.right.unop ⟶
        (Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop,
      (BigFppfOver.toScheme C S hS).map ψ =
        thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
          (thickeningLiftOfIndex C S hS U₀ δ.1.1
            (restrictedUnit G U₀ ≫
              subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
            (comp_eq_restrictedUnit_comp G U₀ δ.2)
            (liftRestrictedSharpThroughThickening C S hS U₀
              (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
              (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g))
          m.right.unop jc :=
  exists_thickeningLiftChartSiteHom_of_index C S hS U₀ hU₀.1 δ.1.1
    (restrictedUnit G U₀ ≫
      subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
    (comp_eq_restrictedUnit_comp G U₀ δ.2)
    (liftRestrictedSharpThroughThickening C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)
    G.source V' m jc
    fun s ↦ app_liftRestrictedSharpThroughThickening_eq C S hS U₀
      (preimageSubspace C S hS G.source U₀) δ.1.1 (restrictedUnit G U₀)
      (comp_eq_restrictedUnit_comp G U₀ δ.2) G.source
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g
      (inverseImage_source_comp_infinitesimalSectionLiftData_g_eq G U₀ hU₀ δ θ)
      (op m.right.unop) s

/-! ### The chart morphism is a section of the source -/

include hU₀ in
/-- **The morphism of charts attached to the moved solution is a section of the source over the
chart of `U`**, which is the first clause of the lifting condition
`AlgebraicGeometry.Space.IsChartLift` for the sheaf of lifts
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsLiftSheaf`.

By `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq_of_index` the attached morphism of
charts lies over `U` — it agrees with the morphism of charts `δ` induces after the chart morphism
to the affine chart `V'` of `U`, and that chart is affine, so the comparison is
`AlgebraicGeometry.ext_of_isAffine` there.  Composing with the source and using that `δ` is a
section of the source gives the clause. -/
theorem comp_source_eq_of_infinitesimalSectionLiftChartSiteHom
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀)
    (V' : Space.SmallEtale C S hS G.objects.1)
    (m : StructuredArrow (op (chartBaseChange C S hS G.source V'))
      (comparisonFunctor C S hS G.arrows).op)
    (jc : StructuredArrow (op (chartBaseChange C S hS δ.1.1 m.right.unop))
      (comparisonFunctor C S hS G.objects).op)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.objects.1).obj V'))]
    (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj jc.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme C S hS).map ψ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g))
        m.right.unop jc) :
    (yoneda.map ψ ≫ m.right.unop.1.hom) ≫ G.source.hom =
      jc.right.unop.1.hom ≫ (𝟙 G.objects : G.objects ⟶ G.objects).hom := by
  have hsec : δ.1.1.hom ≫ G.source.hom =
      (𝟙 G.objects : G.objects ⟶ G.objects).hom :=
    congrArg (fun n : G.objects ⟶ G.objects ↦ n.hom) δ.1.2
  refine (yoneda_map_comp_chart_hom_comp_eq_of_index C S hS U₀ hU₀.1 δ.1.1
    (restrictedUnit G U₀ ≫
      subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
    (comp_eq_restrictedUnit_comp G U₀ δ.2)
    (liftRestrictedSharpThroughThickening C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)
    G.source V' m jc
    (fun s ↦ app_liftRestrictedSharpThroughThickening_eq C S hS U₀
      (preimageSubspace C S hS G.source U₀) δ.1.1 (restrictedUnit G U₀)
      (comp_eq_restrictedUnit_comp G U₀ δ.2) G.source
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g
      (inverseImage_source_comp_infinitesimalSectionLiftData_g_eq G U₀ hU₀ δ θ)
      (op m.right.unop) s)
    ψ hψ).trans ?_
  rw [hsec]

/-! ### The moved solution still restricts to the unit on `U₀` -/

include hU₀ in
/-- **The moved solution has the same reduction as the transported comorphism of `δ`:** its
composite with the direct image along `e₀` of `i^♯ : i^{-1}𝒪_U ⟶ 𝒪_{U₀}` is `j^♯` followed by the
comorphism of `e₀`.

That is the statement that the moved solution still restricts to `e₀ ≫ j` on the thickening: the
two solutions differ by a map with values in the square-zero ideal `(e₀)_*𝒞_{U₀/U}`, and the
conormal module is exactly the kernel of `i^♯`, so the reduction does not see the difference
(`AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero`).  For the
transported comorphism of `δ` the reduction is computed by
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction_structureSharp`. -/
theorem infinitesimalSectionLiftData_g_comp_reduction_eq (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g ≫
        pullbackRingSheafMap
          (Space.SmallEtale.topology C S hS
            (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
              (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)
          (smallToposMorphismTypeU C S hS (restrictedUnit G U₀)).pushforward
          (structureSharpRingInverseImage C S hS
            (subspaceInclusion C S hS G.objects U₀)) =
      structureSharpRingInverseImage C S hS
          (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀)) ≫
        structureSharp C S hS (restrictedUnit G U₀) := by
  have := isLocallySurjective_restrictedArrowsSharp G U₀
  refine (liftDifferenceDataOfHom_g_comp_eq C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (E := restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
      (restrictedUnit G U₀) hU₀)
    (restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
      δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2))
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀ δ.1.1
      (comp_eq_restrictedUnit_comp G U₀ δ.2) x m)
    θ _
    (app_reduction_restrictedSquareZeroValues_ι_eq_zero C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀)).trans ?_
  exact restrictedSharpThroughThickening_comp_reduction_structureSharp C S hS U₀
    (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) δ.1.1
    (comp_eq_restrictedUnit_comp G U₀ δ.2)

/-! ### The chart morphism restricts to the unit on the thickening -/

include hU₀ in
/-- **The moved solution, read on the ambient site of `R` at the tautological index, has the
comorphism of `i ≫ δ` for its reduction.**

On the site of `R₀` the reduction of the moved solution is `j^♯` followed by the comorphism of
`e₀`, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftData_g_comp_reduction_eq`;
carrying it back to the site of `R` preserves that, by
`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_comp_reduction`, and the transport
to the index `i ≫ δ` preserves it again, by
`AlgebraicGeometry.Space.thickeningLiftOfIndex_comp_reduction`. -/
theorem infinitesimalSectionLiftData_comp_reduction_eq (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g) ≫
        thickeningLiftReduction C S hS U₀ δ.1.1 =
      structureSharp C S hS (subspaceInclusion C S hS G.objects U₀ ≫ δ.1.1) :=
  thickeningLiftOfIndex_comp_reduction C S hS U₀ δ.1.1 _
    (comp_eq_restrictedUnit_comp G U₀ δ.2) _
    (liftRestrictedSharpThroughThickening_comp_reduction C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g
      (infinitesimalSectionLiftData_g_comp_reduction_eq G U₀ hU₀ δ θ))

include hU₀ in
/-- **The morphism of charts attached to the moved solution agrees with the unit on the part of
the chart lying in `U₀`**, which is the second clause of the lifting condition
`AlgebraicGeometry.Space.IsChartLift` for the sheaf of lifts
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsLiftSheaf`.

This is `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_eq_restriction` with its hypothesis
on the reduction discharged by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftData_comp_reduction_eq`,
followed by the fact that `δ` itself agrees with the unit on `U₀`. -/
theorem comp_restriction_eq_of_infinitesimalSectionLiftChartSiteHom
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀)
    (V' : Space.SmallEtale C S hS G.objects.1)
    (m : StructuredArrow (op (chartBaseChange C S hS G.source V'))
      (comparisonFunctor C S hS G.arrows).op)
    (jc : StructuredArrow (op (chartBaseChange C S hS δ.1.1 m.right.unop))
      (comparisonFunctor C S hS G.objects).op)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop))]
    (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj jc.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme C S hS).map ψ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g))
        m.right.unop jc)
    (Ww : BigFppfOver C S hS)
    (k : Ww ⟶ (Space.SmallEtale.toOver C S hS G.objects.1).obj jc.right.unop)
    (t : yoneda.obj Ww ⟶ U₀.1.toFunctor)
    (hkt : yoneda.map k ≫ jc.right.unop.1.hom = t ≫ U₀.1.ι) :
    yoneda.map k ≫ yoneda.map ψ ≫ m.right.unop.1.hom =
      t ≫ (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom := by
  have hres : U₀.1.ι ≫ δ.1.1.hom =
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom :=
    congrArg
      (fun n : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶ G.arrows ↦ n.hom) δ.2
  refine (yoneda_map_comp_chart_hom_eq_restriction C S hS U₀ hU₀.1 δ.1.1 _
    (infinitesimalSectionLiftData_comp_reduction_eq G U₀ hU₀ δ θ)
    m.right.unop jc ψ hψ Ww k t hkt).trans ?_
  rw [hres]

include hU₀ in
/-- **The morphism of charts attached to the moved solution is a section of the sheaf of lifts
over the chart of `U`.**  Both clauses of the lifting condition
`AlgebraicGeometry.Space.IsChartLift` hold for it: it is a section of the source, by
`comp_source_eq_of_infinitesimalSectionLiftChartSiteHom`, and it agrees with the unit on the
part of the chart lying in `U₀`, by `comp_restriction_eq_of_infinitesimalSectionLiftChartSiteHom`.

This is the local half of the existence clause of Equation [Stacks Project, Tag 0CKE]: the
solution of the lifting problem attached to an `𝒪_{U₀}`-linear map `θ` produces, over every
affine chart diagram, a section of the sheaf of lifts
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsLiftSheaf`.  What the
existence clause needs beyond this is that those sections are compatible, so that they glue to a
global section and hence to an element of `Γ₀` by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_infinitesimalSection_of_sections`. -/
theorem mem_infinitesimalSectionsLiftSheaf_of_infinitesimalSectionLiftChartSiteHom
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀)
    (V' : Space.SmallEtale C S hS G.objects.1)
    (m : StructuredArrow (op (chartBaseChange C S hS G.source V'))
      (comparisonFunctor C S hS G.arrows).op)
    (jc : StructuredArrow (op (chartBaseChange C S hS δ.1.1 m.right.unop))
      (comparisonFunctor C S hS G.objects).op)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.objects.1).obj V'))]
    (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj jc.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme C S hS).map ψ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g))
        m.right.unop jc) :
    yonedaEquiv (yoneda.map ψ ≫ m.right.unop.1.hom) ∈
      (infinitesimalSectionsLiftSheaf G U₀).obj (op jc.right.unop) := by
  show Space.IsChartLift C S hS (𝟙 G.objects) G.source
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom jc.right.unop
    (yonedaEquiv.symm (yonedaEquiv (yoneda.map ψ ≫ m.right.unop.1.hom)))
  rw [Equiv.symm_apply_apply]
  exact ⟨comp_source_eq_of_infinitesimalSectionLiftChartSiteHom G U₀ hU₀ δ θ V' m jc ψ hψ,
    fun Ww k t hkt ↦ comp_restriction_eq_of_infinitesimalSectionLiftChartSiteHom G U₀ hU₀ δ θ
      V' m jc ψ hψ Ww k t hkt⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
