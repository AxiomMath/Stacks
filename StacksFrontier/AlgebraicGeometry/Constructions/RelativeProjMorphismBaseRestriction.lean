module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismFromSections

/-!
# `r_{L, ψ}` is compatible with restriction of the base, and is globally unique

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra and `f : X ⟶ S` a morphism of
schemes. Over an affine open `V ⊆ S` the morphism `r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` of
[Stacks, Tag 01O9] is `Stacks.AlgebraicGeometry.RelativeProjFromSections.relativeChart`: the
morphism of [Stacks, Tag 01NK] for the graded ring `𝒜(V)` read into `Proj_S(𝒜)` through the chart
of [Stacks, Tag 01NQ]. That is the morphism half of clause (3) of Tag 01O9, over one affine open
of the base.

The source builds the global `r_{L, ψ}` by imposing clause (3) over every affine open of the base
and glueing. Two things are needed for that, and both are here.

* **The clause (3) prescriptions are consistent.** For affine opens `Z ⊆ V` of `S`, the morphism
  prescribed over `V` restricts, on the part lying over `Z`, to the one prescribed over `Z`. This
  is `resLE_relativeChart`.
* **At most one morphism satisfies them.** Given a family of affine opens of the base and local
  data over each, a morphism on the union of the resulting opens of `X` is determined by its
  restrictions to them. This is `eq_of_homOfLE_eq`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart`: **the morphism of
  clause (3) commutes with restriction of the base to a smaller affine open.** For affine opens
  `Z ≤ V` of `S`, a morphism of schemes `j : T' ⟶ T`, a Tag 01NK datum `ψ` for `𝒜(V)` on `T` and a
  Tag 01NK datum `χ` for `𝒜(Z)` on `T'` with the invertible module `j^*L`, whose restriction along
  `𝒜(V) → 𝒜(Z)` takes the values that `ψ` takes pulled back along `j`, the inclusion
  `U(χ ∘ res) ⟶ U(χ)` followed by `r_{L, χ}` read over `Z` is the restriction of `j` followed by
  `r_{L, ψ}` read over `V`.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.eq_of_homOfLE_eq` and
  `…subsingleton_homOfLE_eq`: **global uniqueness.** There is at most one morphism
  `⨆_i (U(ψ_i) ∩ f^{-1}(V_i)) ⟶ Proj_S(𝒜)` restricting over each member of the cover to the
  clause (3) morphism there.

## The route

`resLE_relativeChart` is the composite of the two functorialities of the Tag 01NK morphism with
the transition property of the charts of the relative homogeneous spectrum.

* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_glued` moves the scheme and the module
  and fixes the graded ring: `j` restricted to `U(ψ ∘ res) ⟶ U(ψ)` followed by `r_{L, ψ}` is
  `r_{j^*L, ψ ∘ res}`, both morphisms into `Proj 𝒜(V)`.
* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projInclusionMap`
  moves the graded ring and fixes the scheme: `U(χ ∘ res) ⟶ U(χ)` followed by `r_{j^*L, χ}` and by
  `Proj 𝒜(Z) ⟶ Proj 𝒜(V)` is `r_{j^*L, χ ∘ res}`.
* `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_transition` turns
  `Proj 𝒜(Z) ⟶ Proj 𝒜(V) ⟶ Proj_S(𝒜)` into the chart over `Z`.

The two functorialities meet because `χ ∘ res` is the datum both of them produce: the first from
`ψ` by pulling its values back along `j`, the second from `χ` by restricting its arguments along
`𝒜(V) → 𝒜(Z)`. The hypothesis `hχ` is exactly that those two agree.

**The module is the literal inverse image.** `resLE_glued` compares a datum for `L` on `T` with a
datum for `(Scheme.Modules.pullback j).obj L` on `T'`, so `χ` is asked for that module on the nose
rather than for one isomorphic to it. The transports of a Tag 01NK datum along an isomorphism of
invertible modules and along a pullback are `…ProjChartFullGraded.GradedSections.congrModule` and
`…GradedSections.pullback`.

## The tag

The global morphism `r_{ℒ,ψ}` is `…RelativeProjInvertibleMorphism.GradedPowerMap.globalMorphism`,
and the whole statement of [Stacks, Tag 01O9] is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.tag01O9`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (coveringOpen_le_preimage resLE_glued)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap coveringOpen_le
  homOfLE_glued_comp_projInclusionMap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u v

namespace Stacks.AlgebraicGeometry.RelativeProjFromSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Restriction of the base to a smaller affine open -/

section BaseRestriction

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A)
  {Z V : S.Opens} (h : Z ≤ V) (hZ : IsAffineOpen Z) (hV : IsAffineOpen V)
  {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections (A.grading V) L)
  (χ : GradedSections (A.grading Z) ((Scheme.Modules.pullback j).obj L))
  (hχ : ∀ (n : ℕ) (a : A.grading V n),
    (comap (A.res h) χ).toFun n a = pullSection j L n (ψ.toFun n a))

include hχ

/-- **Stacks Project, Tag 01O9: the morphism of clause (3) commutes with restriction of the base
to a smaller affine open.**

Let `Z ⊆ V` be affine opens of `S`, let `ψ` be a Tag 01NK datum for the graded ring `𝒜(V)` on a
scheme `T` with invertible module `L`, let `j : T' ⟶ T` be a morphism of schemes, and let `χ` be a
Tag 01NK datum for `𝒜(Z)` on `T'` with the invertible module `j^*L`, whose restriction along
`𝒜(V) → 𝒜(Z)` has for values the values of `ψ` pulled back along `j`. Then

`(U(χ ∘ res) ⟶ U(χ)) ≫ r_{j^*L, χ} ≫ i_Z  =  (j : U(χ ∘ res) ⟶ U(ψ)) ≫ r_{L, ψ} ≫ i_V`,

where `i_V` and `i_Z` are the charts of `Proj_S(𝒜)` of Tag 01NQ.

This is the consistency of the clause (3) prescriptions along a nested pair of affine opens of the
base, and so the step the source's proof performs to glue them. -/
theorem resLE_relativeChart :
    T'.homOfLE (coveringOpen_le (A.res h) χ) ≫ relativeChart rp Z hZ χ
      = j.resLE ψ.coveringOpen (comap (A.res h) χ).coveringOpen
          (coveringOpen_le_preimage j L ψ (comap (A.res h) χ) hχ)
        ≫ relativeChart rp V hV ψ := by
  calc T'.homOfLE (coveringOpen_le (A.res h) χ) ≫ relativeChart rp Z hZ χ
      = (T'.homOfLE (coveringOpen_le (A.res h) χ) ≫ χ.glued
            ≫ projInclusionMap A Z V h hZ hV) ≫ rp.chart V hV := by
        rw [relativeChart, ← rp.chart_transition Z V h hZ hV]
        simp only [Category.assoc]
    _ = (comap (A.res h) χ).glued ≫ rp.chart V hV := by
        rw [homOfLE_glued_comp_projInclusionMap A h hZ hV χ]
    _ = _ := by rw [← resLE_glued j L ψ (comap (A.res h) χ) hχ, relativeChart, Category.assoc]

end BaseRestriction

/-! ### Global uniqueness -/

section Unique

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A) (f : X ⟶ S)
  {ι : Type v} (V : ι → S.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (L : ∀ i, (f ⁻¹ᵁ V i).toScheme.Modules)
  [∀ i, Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V i).toScheme (L i)]
  (ψ : ∀ i, GradedSections (A.grading (V i)) (L i))

/-- **Stacks Project, Tag 01O9: global uniqueness of `r_{L, ψ}`.** Two morphisms
`⨆_i (U(ψ_i) ∩ f^{-1}(V_i)) ⟶ Proj_S(𝒜)` which both restrict, over each member of that cover, to
the clause (3) morphism of the local datum there, are equal.

The members cover their union, so a morphism out of it is determined by its restrictions to them;
this is the uniqueness the source invokes to glue the local pieces, at global scope. -/
theorem eq_of_homOfLE_eq {R R' : (⨆ i, localOpen f V L ψ i).toScheme ⟶ rp.scheme}
    (hR : ∀ i, X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ R = localChart rp f V hV L ψ i)
    (hR' : ∀ i, X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ R' = localChart rp f V hV L ψ i) :
    R = R' :=
  (totalCover f V L ψ).hom_ext _ _ fun i => (hR i).trans (hR' i).symm

/-- **The morphisms satisfying the clause (3) restriction property form a subsingleton**, the
uniqueness of `eq_of_homOfLE_eq` packaged as a `Subsingleton`. -/
theorem subsingleton_homOfLE_eq :
    Subsingleton {R : (⨆ i, localOpen f V L ψ i).toScheme ⟶ rp.scheme //
      ∀ i, X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ R = localChart rp f V hV L ψ i} :=
  ⟨fun R R' => Subtype.ext (eq_of_homOfLE_eq rp f V hV L ψ R.2 R'.2)⟩

end Unique

end Stacks.AlgebraicGeometry.RelativeProjFromSections

end
