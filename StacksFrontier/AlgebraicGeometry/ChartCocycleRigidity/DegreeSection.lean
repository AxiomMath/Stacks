module

public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Basic

/-!
# Tag 01NO's chart-level comparison on the restricted homogeneous global sections

For an inclusion `W ⊆ U` of affine opens of the base of a quasi-coherent graded algebra, Tag 01NO's
chart-level comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` carries
the restricted homogeneous global section of a homogeneous element of degree `k` over `U` to the
homogeneous global section of its restriction to `W`. This is the identity
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection` for the
comparison on the pullback, carried across the factor
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which takes the restriction of a
global section to the open image to the image of that global section under the unit of the
pullback–pushforward adjunction.

For a chain of three open immersions, the endomorphism obtained by cancelling the outer comparison
against the two inner ones fixes a global section which all three comparisons produce from one
global section upstairs.

## Main results

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.pullbackSection_eq`: the component of
  `restrictFunctorIsoPullback` carries the restriction of a global section to the open image to
  the pulled-back global section.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.restrictTwistIso_degreeSection` and
  `isLegDegreeSection`: **Tag 01NO's chart-level comparison fixes the restricted homogeneous
  global sections**, for every inclusion of affine opens of the base and in every degree. The
  second is the first read as the per-leg predicate
  `Stacks.AlgebraicGeometry.ChartCocycleRigidity.IsLegDegreeSection`.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo_val_app_top`: the endomorphism obtained
  by cancelling the outer comparison against the two inner ones fixes a global section which all
  three comparisons produce from one global section upstairs.

## Implementation notes

Every step is stated for variable schemes, morphisms and sheaves of modules, and the concrete
transition morphisms of a relative projective spectrum enter only by substitution into a generic
statement: written out at the instance, the same steps exhaust the elaborator's recursion limit
and time out in the kernel. For the same reason the three sections of `legEndo_val_app_top` are
implicit, determined by its three leg hypotheses, and `legDegree_of_pullbackSection` takes the two
factors of `restrictTwistIso` as an equation of morphisms.

`Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr`, over an arbitrary sheaf of rings,
and `app_val_congr_scheme`, over a scheme with the two modules explicit, are both needed: an
equation of morphisms at one of the two readings of the structure sheaf of a projective spectrum
is read on sections only by a lemma that either leaves that sheaf of rings free or pins it.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection
open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ChartCocycleRigidity

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Crossing the `restrictFunctorIsoPullback` factor -/

universe v w uc vc

/-- **Equal morphisms of sheaves of modules act equally on a section**, over an arbitrary sheaf
of rings on an arbitrary site. -/
public theorem app_val_congr {C : Type uc} [Category.{vc} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{v} R} {a b : M ⟶ N} (hab : a = b)
    (V : Cᵒᵖ) (s : (M.val.obj V : Type v)) : a.val.app V s = b.val.app V s := by
  subst hab; rfl

/-- **The unit of `f^* ⊣ f_*` at an open immersion factors through the unit of restriction**,
followed by the comparison `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
public theorem unit_eq_restrictUnit {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M =
      (Scheme.Modules.restrictAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom :=
  (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M).symm

/-- The component of `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` carries the
restriction of a global section of `M` to the image of the whole source to the image of that
global section under the unit of the pullback–pushforward adjunction. The inclusion of opens is a
free argument. -/
public theorem pullbackSection_eq {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (s : M.val.obj (op ⊤)) (j : f ''ᵁ (⊤ : Y.Opens) ⟶ ⊤) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom.val.app (op ⊤)
        (M.val.map j.op s) = pullbackSection f M s := by
  refine Eq.symm (Eq.trans (comp_val_app_of _ _ (unit_eq_restrictUnit f M) ⊤
    (restrictAdjunction_unit_val_app f M ⊤ s)) ?_)
  refine Eq.trans (pushforward_map_val_app f _ ⊤ _) ?_
  exact congrArg
    (((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom.val.app (op ⊤))
    (map_val_congr M _ j s)

/-- **An isomorphism of sheaves of modules presented as the restriction-to-pullback comparison
followed by a morphism out of the pullback carries a restricted global section to the image of the
pulled-back one.** The two factors are supplied as an equation of morphisms `hφ`. -/
public theorem legDegree_of_pullbackSection {X Y : Scheme.{u}} (p : Y ⟶ X) [IsOpenImmersion p]
    {M : X.Modules} {N : Y.Modules} {φ : (Scheme.Modules.restrictFunctor p).obj M ⟶ N}
    (ψ : (Scheme.Modules.pullback p).obj M ⟶ N)
    (hφ : φ = ((Scheme.Modules.restrictFunctorIsoPullback p).app M).hom ≫ ψ)
    (s : M.val.obj (op ⊤)) {t : N.val.obj (op ⊤)} (j : p ''ᵁ (⊤ : Y.Opens) ⟶ ⊤)
    (ht : ψ.val.app (op ⊤) (pullbackSection p M s) = t) :
    φ.val.app (op ⊤) (M.val.map j.op s) = t :=
  (comp_val_app_of _ ψ hφ ⊤ (pullbackSection_eq p M s j)).trans ht

/-! ### The generic four-step chain -/

/-- **From the whole space to an arbitrary open.** If the comparison carries the restriction of a
global section to the image of the whole source to a global section downstairs, then over every
open it carries the restriction of that same global section to the restriction of the image. -/
public theorem app_of_top {X Y : Scheme.{u}} (p : Y ⟶ X) [IsOpenImmersion p]
    {M : X.Modules} {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor p).obj M ≅ N)
    (s : M.val.obj (op ⊤)) {t : N.val.obj (op ⊤)} (j : p ''ᵁ (⊤ : Y.Opens) ⟶ ⊤)
    (htop : e.hom.val.app (op ⊤) (M.val.map j.op s) = t)
    (T : Y.Opens) (m : p ''ᵁ T ⟶ ⊤) (i : T ⟶ ⊤) :
    e.hom.val.app (op T) (M.val.map m.op s) = N.val.map i.op t := by
  have h1 : ((Scheme.Modules.restrictFunctor p).obj M).val.map i.op (M.val.map j.op s)
      = M.val.map m.op s :=
    (restrict_val_map p M i _).trans (map_comp_val M _ j m s)
  refine Eq.trans (congrArg (e.hom.val.app (op T)) h1.symm) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply e.hom.val i.op (M.val.map j.op s)) ?_
  exact congrArg (N.val.map i.op) htop

/-- **The endomorphism obtained by cancelling the outer comparison against the two inner ones
fixes a global section the three comparisons all produce from one global section upstairs.** -/
public theorem legEndo_val_app_top {X Y Z : Scheme.{u}} (p₁ : Y ⟶ Z) (p₂ : Z ⟶ X) (p₃ : Y ⟶ X)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion p₃] (hp : p₁ ≫ p₂ = p₃)
    {M : X.Modules} {N : Z.Modules} {L : Y.Modules}
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L)
    (j₂ : p₂ ''ᵁ (⊤ : Z.Opens) ⟶ ⊤) (j₁ : p₁ ''ᵁ (⊤ : Y.Opens) ⟶ ⊤)
    (j₃ : p₃ ''ᵁ (⊤ : Y.Opens) ⟶ ⊤)
    {s : M.val.obj (op ⊤)} {t' : N.val.obj (op ⊤)} {t : L.val.obj (op ⊤)}
    (h₂ : e₂.hom.val.app (op ⊤) (M.val.map j₂.op s) = t')
    (h₁ : e₁.hom.val.app (op ⊤) (N.val.map j₁.op t') = t)
    (h₃ : e₃.hom.val.app (op ⊤) (M.val.map j₃.op s) = t) :
    (legEndo p₁ p₂ p₃ hp e₂ e₁ e₃).val.app (op ⊤) t = t := by
  have m : p₂ ''ᵁ (p₁ ''ᵁ (⊤ : Y.Opens)) ⟶ (⊤ : X.Opens) := homOfLE le_top
  have hinv : e₃.inv.val.app (op ⊤) t = M.val.map j₃.op s :=
    (congrArg (e₃.inv.val.app (op ⊤)) h₃.symm).trans
      (Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app e₃ (op ⊤) _)
  refine Eq.trans (legEndo_val_app p₁ p₂ p₃ hp e₂ e₁ e₃ ⊤
    (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)) t) ?_
  refine Eq.trans (congrArg (e₁.hom.val.app (op ⊤)) ?_) h₁
  refine Eq.trans (congrArg (e₂.hom.val.app (op (p₁ ''ᵁ (⊤ : Y.Opens)))) ?_)
    (app_of_top p₂ e₂ s j₂ h₂ (p₁ ''ᵁ (⊤ : Y.Opens)) m j₁)
  exact (congrArg (M.val.map (eqToHom (image_eq_image_image p₁ p₂ p₃ hp ⊤)).op) hinv).trans
    (map_comp_val M _ j₃ m s)

/-! ### The instance: Tag 01NO's chart-level comparison -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- **Tag 01NO's chart-level comparison carries the restricted homogeneous global section of a
homogeneous element to the homogeneous global section of its restriction**, for every inclusion
`W ⊆ U` of affine opens of the base and in every degree. The inclusion of opens is a free
argument, and the twist on the larger chart is read as a sheaf of modules on that chart. -/
public theorem restrictTwistIso_degreeSection (k : ℕ) (c : (A.grading U) k)
    (j : projInclusionMap A W U h hW hU ''ᵁ
      (⊤ : (AlgebraicGeometry.Proj (A.grading W)).Opens) ⟶ ⊤) :
    (restrictTwistIso A W U h hW hU (k : ℤ)).hom.val.app (op ⊤)
        ((twistingSheaf (A.grading U) (k : ℤ) :
            (AlgebraicGeometry.Proj (A.grading U)).Modules).val.map j.op
          (degreeSection (A.grading U) k c)) =
      degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩ :=
  legDegree_of_pullbackSection (projInclusionMap A W U h hW hU)
    (projInclusionTwistIso A W U h hW hU (k : ℤ)).hom rfl
    (degreeSection (A.grading U) k c) j
    ((app_val_congr (projInclusionTwistIso_hom A W U h hW hU (k : ℤ)) (op ⊤)
        (pullbackSection (projInclusionMap A W U h hW hU)
          (twistingSheaf (A.grading U) (k : ℤ)) (degreeSection (A.grading U) k c))).trans
      (projInclusionTwistMap_degreeSection A W U h hW hU k c))

/-- **The same, as the per-leg assertion
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.IsLegDegreeSection`.** -/
public theorem isLegDegreeSection : IsLegDegreeSection A W U h hW hU :=
  fun k c ↦ restrictTwistIso_degreeSection A W U h hW hU k c (homOfLE le_top)

/-- **Equal morphisms of sheaves of modules on a scheme act equally on a section**, with the
scheme and the two modules explicit arguments. -/
public theorem app_val_congr_scheme (X : Scheme.{u}) (M N : X.Modules) {a b : M ⟶ N}
    (hab : a = b) (V : X.Opens) (s : M.val.obj (op V)) :
    a.val.app (op V) s = b.val.app (op V) s := by
  subst hab; rfl

end Stacks.AlgebraicGeometry.ChartCocycleRigidity

end
