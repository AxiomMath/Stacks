module

public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.DegreeSection
public import StacksFrontier.AlgebraicGeometry.TwistRigidityDegreeOne.Basic

/-!
# Tag 01NO's chart comparisons fix the restricted homogeneous sections

Along a chain `W ⊆ W' ⊆ U` of affine opens of the base, the endomorphism of the degree-`k` twist
on the chart of `W` obtained by cancelling Tag 01NO's comparison for `W ⊆ U` against the two
comparisons through the chart of `W'` fixes the homogeneous global section attached to the
restriction to `W` of every homogeneous element over `U`, in every degree.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.resDegreeSection`: the homogeneous global section
  of a degree-`k` element over the larger chart, restricted to the image of the smaller chart, and
  **typed as a section of the restricted twist** — that is, with the comparison's own domain as its
  declared type.

## Main results

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo_val_app_top_of_res`:
  `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo_val_app_top` with the three restricted
  sections given as sections of the three restricted modules, their relation to one section
  upstairs being two separate equations.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.restrictTwistIso_resDegreeSection`: one leg of the
  chain, with both sections encapsulated.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndoChart_val_app_top`: the endomorphism of
  the degree-`k` twist on the chart of `W` obtained by cancelling Tag 01NO's comparison for
  `W ⊆ U` against the two comparisons through the chart of `W'` fixes the homogeneous global
  section of the restriction to `W` of a homogeneous element over `U`.

## Implementation notes

The twists are sheaves of modules over `ProjectiveSpectrum.Proj.structureSheaf` composed with the
forgetful functor, while `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is indexed by the
scheme's own `ringCatSheaf`. The two are definitionally equal, but identifying them underneath
Tag 01NO's comparison applied to a written-out restricted global section is expensive for the
elaborator. The identification is therefore made only in `resDegreeSection`, whose declared type
is the comparison's domain, and in `legPairIso_resDegreeSection`, and the three legs of the
assembly are instances of the one theorem `restrictTwistIso_resDegreeSection`. For the same reason
`legEndo_val_app_top_of_res` takes the restricted sections as explicit arguments, and
`legEndoChart_val_app_top` is stated with `legEndo` written out rather than with `cocycleEndo`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ChartCocycleRigidity

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### The generic chain, with the restricted sections given -/

section Generic

variable {X Y Z : Scheme.{u}} (p₁ : Y ⟶ Z) (p₂ : Z ⟶ X) (p₃ : Y ⟶ X)
  [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion p₃]

/-- **The comparison of the two readings of the restriction along the composite, on a restricted
global section.** If a section of the restriction along `p₃` and one of the restriction along `p₂`
are both restrictions of one global section upstairs, then the first is carried by
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.legPairIso` to the restriction along `p₁` of the
second. All three inclusions of opens are free arguments. -/
public theorem legPairIso_hom_val_app_top (hp : p₁ ≫ p₂ = p₃) {M : X.Modules}
    (j₁ : p₁ ''ᵁ (⊤ : Y.Opens) ⟶ ⊤) (j₂ : p₂ ''ᵁ (⊤ : Z.Opens) ⟶ ⊤)
    (j₃ : p₃ ''ᵁ (⊤ : Y.Opens) ⟶ ⊤) {s : M.val.obj (op ⊤)}
    {r₂ : ((Scheme.Modules.restrictFunctor p₂).obj M).val.obj (op ⊤)}
    {r₃ : ((Scheme.Modules.restrictFunctor p₃).obj M).val.obj (op ⊤)}
    (hr₂ : r₂ = M.val.map j₂.op s) (hr₃ : r₃ = M.val.map j₃.op s) :
    (legPairIso p₁ p₂ p₃ hp M).hom.val.app (op ⊤) r₃ =
      ((Scheme.Modules.restrictFunctor p₂).obj M).val.map j₁.op r₂ := by
  subst hr₂ hr₃
  refine Eq.trans (legPairIso_hom_val_app p₁ p₂ p₃ hp M ⊤
    (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)) _) ?_
  refine Eq.trans (map_comp_val M _ j₃ (homOfLE le_top) s) ?_
  exact ((restrict_val_map p₂ M j₁ (M.val.map j₂.op s)).trans
    (map_comp_val M (p₂.opensFunctor.map j₁) j₂ (homOfLE le_top) s)).symm

/-- **The endomorphism obtained by cancelling the outer comparison against the two inner ones
fixes a global section which all three comparisons produce from given sections of the three
restricted modules.** The three restricted sections `r₁`, `r₂`, `r₃` are given, and their
relation to one global section upstairs enters as the two equations `hpair` and `hmid`. -/
public theorem legEndo_val_app_top_of_res (hp : p₁ ≫ p₂ = p₃)
    {M : X.Modules} {N : Z.Modules} {L : Y.Modules}
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L)
    (j₁ : p₁ ''ᵁ (⊤ : Y.Opens) ⟶ ⊤)
    (r₂ : ((Scheme.Modules.restrictFunctor p₂).obj M).val.obj (op ⊤))
    (r₁ : ((Scheme.Modules.restrictFunctor p₁).obj N).val.obj (op ⊤))
    (r₃ : ((Scheme.Modules.restrictFunctor p₃).obj M).val.obj (op ⊤))
    (t' : N.val.obj (op ⊤)) (t : L.val.obj (op ⊤))
    (h₂ : e₂.hom.val.app (op ⊤) r₂ = t')
    (h₁ : e₁.hom.val.app (op ⊤) r₁ = t)
    (h₃ : e₃.hom.val.app (op ⊤) r₃ = t)
    (hpair : (legPairIso p₁ p₂ p₃ hp M).hom.val.app (op ⊤) r₃ =
      ((Scheme.Modules.restrictFunctor p₂).obj M).val.map j₁.op r₂)
    (hmid : r₁ = N.val.map j₁.op t') :
    (legEndo p₁ p₂ p₃ hp e₂ e₁ e₃).val.app (op ⊤) t = t := by
  have hinv : e₃.inv.val.app (op ⊤) t = r₃ :=
    (congrArg (e₃.inv.val.app (op ⊤)) h₃.symm).trans
      (Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app e₃ (op ⊤) r₃)
  have hstep : e₂.hom.val.app (op (p₁ ''ᵁ (⊤ : Y.Opens)))
      (M.val.map (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)).op
        (e₃.inv.val.app (op ⊤) t)) = N.val.map j₁.op t' := by
    have hA : M.val.map (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)).op
        (e₃.inv.val.app (op ⊤) t) =
        ((Scheme.Modules.restrictFunctor p₂).obj M).val.map j₁.op r₂ :=
      (congrArg (M.val.map (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)).op) hinv).trans
        ((legPairIso_hom_val_app p₁ p₂ p₃ hp M ⊤
          (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)) r₃).symm.trans hpair)
    exact (congrArg (e₂.hom.val.app (op (p₁ ''ᵁ (⊤ : Y.Opens)))) hA).trans
      ((PresheafOfModules.naturality_apply e₂.hom.val j₁.op r₂).trans
        (congrArg (N.val.map j₁.op) h₂))
  refine Eq.trans (legEndo_val_app p₁ p₂ p₃ hp e₂ e₁ e₃ ⊤
    (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)) t) ?_
  exact Eq.trans (congrArg (e₁.hom.val.app (op ⊤)) (hstep.trans hmid.symm)) h₁

end Generic

/-! ### The encapsulated restricted section of one inclusion of affine opens -/

section Legs

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- **The homogeneous global section of a degree-`k` element over the larger chart, restricted to
the image of the smaller chart.** Its declared type is the domain of Tag 01NO's chart-level
comparison read over the whole smaller chart. -/
public def resDegreeSection (k : ℕ) (c : (A.grading U) k) :
    ((Scheme.Modules.restrictFunctor (projInclusionMap A W U h hW hU)).obj
      (twistingSheaf (A.grading U) (k : ℤ))).val.obj (op ⊤) :=
  (twistingSheaf (A.grading U) (k : ℤ) :
      (AlgebraicGeometry.Proj (A.grading U)).Modules).val.map (homOfLE le_top).op
    (degreeSection (A.grading U) k c)

/-- Its defining equation: it is the restriction of the homogeneous global section to the image of
the whole smaller chart. -/
public theorem resDegreeSection_eq (k : ℕ) (c : (A.grading U) k) :
    resDegreeSection A W U h hW hU k c =
      (twistingSheaf (A.grading U) (k : ℤ) :
          (AlgebraicGeometry.Proj (A.grading U)).Modules).val.map (homOfLE le_top).op
        (degreeSection (A.grading U) k c) :=
  rfl

/-- **One leg of the chain.** Tag 01NO's chart-level comparison for an inclusion `W ⊆ U` of affine
opens carries the encapsulated restricted homogeneous global section of a degree-`k` element to the
homogeneous global section of its restriction. -/
public theorem restrictTwistIso_resDegreeSection (k : ℕ) (c : (A.grading U) k) :
    (restrictTwistIso A W U h hW hU (k : ℤ)).hom.val.app (op ⊤)
        (resDegreeSection A W U h hW hU k c) =
      degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩ :=
  restrictTwistIso_degreeSection A W U h hW hU k c (homOfLE le_top)

end Legs

/-! ### The assembly along a chain of three affine opens -/

section Chain

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W W' U : S.Opens) (hWW' : W ≤ W')
  (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
  (hU : IsAffineOpen U)

/-- **Restriction of homogeneous elements along a chain of affine opens composes**, read on the
homogeneous global sections it determines. -/
public theorem degreeSection_res_res (k : ℕ) (c : (A.grading U) k) :
    degreeSection (A.grading W) k
        ⟨A.res hWW' (A.res hW'U c), (A.res hWW').map_mem ((A.res hW'U).map_mem c.2)⟩ =
      degreeSection (A.grading W) k ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩ :=
  congrArg (degreeSection (A.grading W) k) (res_res_subtype A W W' U hWW' hW'U hWU k c)

include hWW' hW'U hWU hW hW' hU

/-- **The two readings of the restriction from the chart of `U` to the chart of `W` agree on the
encapsulated homogeneous global section** — directly, and through the chart of `W'`. -/
public theorem legPairIso_resDegreeSection (k : ℕ) (c : (A.grading U) k) :
    (legPairIso (projInclusionMap A W W' hWW' hW hW')
          (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
          (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
          (twistingSheaf (A.grading U) (k : ℤ))).hom.val.app (op ⊤)
        (resDegreeSection A W U hWU hW hU k c) =
      ((Scheme.Modules.restrictFunctor (projInclusionMap A W' U hW'U hW' hU)).obj
          (twistingSheaf (A.grading U) (k : ℤ))).val.map
        (homOfLE (le_top (a := projInclusionMap A W W' hWW' hW hW' ''ᵁ ⊤))).op
        (resDegreeSection A W' U hW'U hW' hU k c) :=
  legPairIso_hom_val_app_top (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (homOfLE le_top) (homOfLE le_top) (homOfLE le_top)
    (resDegreeSection_eq A W' U hW'U hW' hU k c) (resDegreeSection_eq A W U hWU hW hU k c)

/-- **The assembly: Tag 01NO's comparison for the outer pair, cancelled against the two
comparisons through the middle chart, fixes the homogeneous global section of a restricted
homogeneous element**, in every degree. -/
public theorem legEndoChart_val_app_top (k : ℕ) (c : (A.grading U) k) :
    (legEndo (projInclusionMap A W W' hWW' hW hW')
          (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
          (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
          (restrictTwistIso A W' U hW'U hW' hU (k : ℤ))
          (restrictTwistIso A W W' hWW' hW hW' (k : ℤ))
          (restrictTwistIso A W U hWU hW hU (k : ℤ))).val.app (op ⊤)
        (degreeSection (A.grading W) k ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩) =
      degreeSection (A.grading W) k ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩ :=
  legEndo_val_app_top_of_res (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU (k : ℤ))
    (restrictTwistIso A W W' hWW' hW hW' (k : ℤ))
    (restrictTwistIso A W U hWU hW hU (k : ℤ))
    (homOfLE le_top)
    (resDegreeSection A W' U hW'U hW' hU k c)
    (resDegreeSection A W W' hWW' hW hW' k ⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩)
    (resDegreeSection A W U hWU hW hU k c)
    (degreeSection (A.grading W') k ⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩)
    (degreeSection (A.grading W) k ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩)
    (restrictTwistIso_resDegreeSection A W' U hW'U hW' hU k c)
    ((restrictTwistIso_resDegreeSection A W W' hWW' hW hW' k
        ⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩).trans
      (degreeSection_res_res A W W' U hWW' hW'U hWU k c))
    (restrictTwistIso_resDegreeSection A W U hWU hW hU k c)
    (legPairIso_resDegreeSection A W W' U hWW' hW'U hWU hW hW' hU k c)
    (resDegreeSection_eq A W W' hWW' hW hW' k ⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩)

end Chain

end Stacks.AlgebraicGeometry.ChartCocycleRigidity

end
