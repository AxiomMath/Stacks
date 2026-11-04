module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.GradedRealizationPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafCoproductInt

/-!
# The algebra pullback of an ungraded realisation is the realisation of the degreewise pullback

`Stacks.GradedRealizationPullback.comparison` is the morphism of sheaves of commutative
`𝒪_X`-algebras

`Φ : (algebraPullback g).obj (⨁ₙ 𝒜ₙ) ⟶ ⨁ₙ g^*𝒜ₙ`

for `g : X ⟶ Y` a morphism of schemes and `𝒜` a sheaf of `ℤ`-graded `𝒪_Y`-algebras with
commutative homogeneous multiplication. `Φ` is invertible.

## Main definitions

* `Stacks.GradedRealizationPullback.summandIncl`: the degree-`n` inclusion
  `𝒜ₙ ⟶ ⨁ₘ 𝒜ₘ` of a homogeneous piece into the module underlying the ungraded realisation,
  which is the `n`-th coproduct injection read through the identification of that module with
  the coproduct.
* `Stacks.GradedRealizationPullback.comparisonIso`: **`Φ` as an isomorphism of sheaves of
  commutative `𝒪_X`-algebras.**

## Main results

* `Stacks.GradedRealizationPullback.moduleMap_comparison_pullbackUnit`: the underlying module
  morphism of `Φ`, on the pullback-unit image of a local section of `⨁ₙ 𝒜ₙ`, is `β` on that
  section.
* `Stacks.GradedRealizationPullback.pullback_map_summandIncl_comp`: **the degree-`n` summand
  identity.** The pullback of the degree-`n` inclusion, followed by the two identifications and
  the comparison, is the degree-`n` inclusion on `X`.
* `Stacks.GradedRealizationPullback.coprod_comparison_eq`: the comparison is the canonical
  isomorphism `g^*(∐ₙ 𝒜ₙ) ≅ ∐ₙ g^*𝒜ₙ` under the two identifications.
* `Stacks.GradedRealizationPullback.isIso_moduleMap_comparison` and
  `Stacks.GradedRealizationPullback.isIso_comparison`: **`Φ` is invertible**, as a morphism of
  modules and as a morphism of algebra sheaves.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.RingedSpace

universe u

namespace Stacks.GradedRealizationPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (𝒜 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)

/-! ### The degreewise inclusion into the underlying module -/

section Incl

variable {Z : Scheme.{u}} (ℬ : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)
  (hb : ∀ (i j : ℤ) (W : (Opens ↥Z)ᵒᵖ) (a : (ℬ.piece i).val.obj W) (b : (ℬ.piece j).val.obj W),
    HEq ((ℬ.mul i j).app W a b) ((ℬ.mul j i).app W b a))

/-- **The degree-`n` inclusion of a homogeneous piece into the module underlying the ungraded
realisation**: the `n`-th coproduct injection, read through
`Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule`. On local sections it is
`SheafOfModules.GradedAlgebra.ungradedIncl`. -/
def summandIncl (n : ℤ) :
    ℬ.piece n ⟶ AlgebraSheaf.underlyingModule (gradedAlgebraSheaf Z ℬ hb) :=
  Sigma.ι (fun k : ℤ => ℬ.piece k) n ≫ (gradedCoprodIntIsoUnderlyingModule Z ℬ hb).hom

/-- The degree-`n` inclusion on a local section is the homogeneous section it names. -/
theorem summandIncl_app (W : (Opens ↥Z)ᵒᵖ) (n : ℤ) (x : (ℬ.piece n).val.obj W) :
    PresheafOfModules.Hom.app (summandIncl ℬ hb n).val W x = ℬ.ungradedIncl n x :=
  gradedCoprodIntIsoUnderlyingModule_hom_sigma_ι Z ℬ hb W n x

end Incl

/-! ### The comparison on pullback-unit images -/

section Algebra

variable (hc : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝒜.piece i).val.obj W)
  (b : (𝒜.piece j).val.obj W), HEq ((𝒜.mul i j).app W a b) ((𝒜.mul j i).app W b a))

/-- **The underlying module morphism of `Φ`, on the pullback-unit image of a local section of
`⨁ₙ 𝒜ₙ`, is `β` on that section.** -/
theorem moduleMap_comparison_pullbackUnit (V : Y.Opens)
    (a : (gradedAlgebraSheaf Y 𝒜 hc).right.obj.obj (op V)) :
    ((comparison g 𝒜 hc).right.hom.app (op (g ⁻¹ᵁ V)))
        (PresheafOfModules.Hom.app
          (AlgebraPullbackQcoh.underlyingModulePullbackIso g
            (gradedAlgebraSheaf Y 𝒜 hc)).hom.val (op (g ⁻¹ᵁ V))
          (pullbackUnit g.toLRSHom.toShHom
            (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf Y 𝒜 hc)) (op V) a)) =
      ((pushforwardHom g 𝒜 hc).right.hom.app (op V)) a := by
  refine Eq.trans (congrArg ((comparison g 𝒜 hc).right.hom.app (op (g ⁻¹ᵁ V)))
      (AlgebraPullbackQcoh.comparison_app_moduleUnit_algebraPullbackMap g
        (gradedAlgebraSheaf Y 𝒜 hc) V a)) ?_
  exact comparison_app_unit g 𝒜 hc V a

/-! ### The degree-`n` summand identity -/

/-- **The degree-`n` summand identity.** The pullback of the degree-`n` inclusion into the module
underlying `⨁ₘ 𝒜ₘ`, followed by the identification of the module underlying the algebra pullback
and by the underlying module morphism of `Φ`, is the degree-`n` inclusion into the module
underlying `⨁ₘ g^*𝒜ₘ`. -/
@[reassoc]
theorem pullback_map_summandIncl_comp (n : ℤ) :
    (Scheme.Modules.pullback g).map (summandIncl 𝒜 hc n) ≫
        (AlgebraPullbackQcoh.underlyingModulePullbackIso g
          (gradedAlgebraSheaf Y 𝒜 hc)).hom ≫
        AlgebraPullbackQcoh.moduleMap (comparison g 𝒜 hc) =
      summandIncl (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc) n := by
  refine Stacks.PullbackTensorCoherence.pullback_hom_ext g.toLRSHom.toShHom fun V x => ?_
  refine Eq.trans (show _ = ((comparison g 𝒜 hc).right.hom.app (op (g ⁻¹ᵁ V.unop)))
      (PresheafOfModules.Hom.app
        (AlgebraPullbackQcoh.underlyingModulePullbackIso g
          (gradedAlgebraSheaf Y 𝒜 hc)).hom.val (op (g ⁻¹ᵁ V.unop))
        (PresheafOfModules.Hom.app
          ((Scheme.Modules.pullback g).map (summandIncl 𝒜 hc n)).val (op (g ⁻¹ᵁ V.unop))
          (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) V x))) from rfl) ?_
  refine Eq.trans (congrArg (fun z => ((comparison g 𝒜 hc).right.hom.app (op (g ⁻¹ᵁ V.unop)))
      (PresheafOfModules.Hom.app
        (AlgebraPullbackQcoh.underlyingModulePullbackIso g
          (gradedAlgebraSheaf Y 𝒜 hc)).hom.val (op (g ⁻¹ᵁ V.unop)) z))
      (pullbackUnit_naturality g.toLRSHom.toShHom (summandIncl 𝒜 hc n) V x)) ?_
  refine Eq.trans (moduleMap_comparison_pullbackUnit g 𝒜 hc V.unop
    (PresheafOfModules.Hom.app (summandIncl 𝒜 hc n).val V x)) ?_
  refine Eq.trans (congrArg ((pushforwardHom g 𝒜 hc).right.hom.app V)
    (summandIncl_app 𝒜 hc V n x)) ?_
  refine Eq.trans (pushforwardHom_ungradedIncl g 𝒜 hc V.unop n x) ?_
  exact (summandIncl_app (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc) (op (g ⁻¹ᵁ V.unop)) n
    (pullbackUnit g.toLRSHom.toShHom (𝒜.piece n) V x)).symm

/-! ### The comparison is the canonical coproduct isomorphism -/

/-- **The comparison is the canonical isomorphism `g^*(∐ₙ 𝒜ₙ) ≅ ∐ₙ g^*𝒜ₙ`** under the
identifications of the two underlying modules with coproducts. -/
theorem coprod_comparison_eq :
    (Scheme.Modules.pullback g).map (gradedCoprodIntIsoUnderlyingModule Y 𝒜 hc).hom ≫
        (AlgebraPullbackQcoh.underlyingModulePullbackIso g
          (gradedAlgebraSheaf Y 𝒜 hc)).hom ≫
        AlgebraPullbackQcoh.moduleMap (comparison g 𝒜 hc) ≫
        (gradedCoprodIntIsoUnderlyingModule X (pbGraded g 𝒜)
          (pbGraded_mul_comm g 𝒜 hc)).inv =
      (PreservesCoproduct.iso (Scheme.Modules.pullback g) (fun n : ℤ => 𝒜.piece n)).hom := by
  refine (cancel_epi (PreservesCoproduct.iso (Scheme.Modules.pullback g)
    (fun n : ℤ => 𝒜.piece n)).inv).mp (Sigma.hom_ext _ _ fun n => ?_)
  have h : Sigma.ι (fun k : ℤ => (Scheme.Modules.pullback g).obj (𝒜.piece k)) n ≫
        (PreservesCoproduct.iso (Scheme.Modules.pullback g) fun k : ℤ => 𝒜.piece k).inv =
      (Scheme.Modules.pullback g).map (Sigma.ι (fun k : ℤ => 𝒜.piece k) n) :=
    (Iso.comp_inv_eq _).mpr (IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit
        (Scheme.Modules.pullback g) fun k : ℤ => 𝒜.piece k)
      (colimit.isColimit _) (Discrete.mk n)).symm
  have hR : Sigma.ι (fun k : ℤ => (Scheme.Modules.pullback g).obj (𝒜.piece k)) n ≫
        ((PreservesCoproduct.iso (Scheme.Modules.pullback g) fun k : ℤ => 𝒜.piece k).inv ≫
          (PreservesCoproduct.iso (Scheme.Modules.pullback g) fun k : ℤ => 𝒜.piece k).hom) =
      Sigma.ι (fun k : ℤ => (Scheme.Modules.pullback g).obj (𝒜.piece k)) n :=
    (congrArg (Sigma.ι (fun k : ℤ => (Scheme.Modules.pullback g).obj (𝒜.piece k)) n ≫ ·)
      (Iso.inv_hom_id _)).trans (Category.comp_id _)
  refine Eq.trans ?_ hR.symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Scheme.Modules.pullback g).map_comp
    (Sigma.ι (fun k : ℤ => 𝒜.piece k) n)
    (gradedCoprodIntIsoUnderlyingModule Y 𝒜 hc).hom).symm).trans ?_
  refine (pullback_map_summandIncl_comp_assoc g 𝒜 hc n
    (gradedCoprodIntIsoUnderlyingModule X (pbGraded g 𝒜)
      (pbGraded_mul_comm g 𝒜 hc)).inv).trans ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (Sigma.ι (fun k : ℤ => (pbGraded g 𝒜).piece k) n ≫ ·)
      (Iso.hom_inv_id _)).trans (Category.comp_id _))

/-! ### Invertibility -/

/-- The canonical isomorphism `g^*(∐ₙ 𝒜ₙ) ≅ ∐ₙ g^*𝒜ₙ` conjugated by the pullback of the
coproduct identification on `Y`, the identification of the module underlying the algebra pullback,
and the coproduct identification on `X`. -/
def moduleComparisonIso :
    AlgebraSheaf.underlyingModule ((algebraPullback g).obj (gradedAlgebraSheaf Y 𝒜 hc)) ≅
      AlgebraSheaf.underlyingModule
        (gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc)) :=
  (((Scheme.Modules.pullback g).mapIso (gradedCoprodIntIsoUnderlyingModule Y 𝒜 hc) ≪≫
        AlgebraPullbackQcoh.underlyingModulePullbackIso g (gradedAlgebraSheaf Y 𝒜 hc)).symm ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback g) (fun n : ℤ => 𝒜.piece n)) ≪≫
    gradedCoprodIntIsoUnderlyingModule X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc)

/-- **The underlying module morphism of `Φ` is `moduleComparisonIso`.** -/
theorem moduleMap_comparison_eq :
    AlgebraPullbackQcoh.moduleMap (comparison g 𝒜 hc) = (moduleComparisonIso g 𝒜 hc).hom :=
  (Iso.comp_inv_eq (gradedCoprodIntIsoUnderlyingModule X (pbGraded g 𝒜)
      (pbGraded_mul_comm g 𝒜 hc))).mp
    ((Iso.eq_inv_comp ((Scheme.Modules.pullback g).mapIso
        (gradedCoprodIntIsoUnderlyingModule Y 𝒜 hc) ≪≫
          AlgebraPullbackQcoh.underlyingModulePullbackIso g
            (gradedAlgebraSheaf Y 𝒜 hc))).mpr
      ((Category.assoc _ _ _).trans (coprod_comparison_eq g 𝒜 hc)))

/-- **The underlying module morphism of `Φ` is invertible.** -/
theorem isIso_moduleMap_comparison :
    IsIso (AlgebraPullbackQcoh.moduleMap (comparison g 𝒜 hc)) := by
  rw [moduleMap_comparison_eq g 𝒜 hc]
  exact (moduleComparisonIso g 𝒜 hc).isIso_hom

/-- **`Φ` is invertible**: the algebra pullback of the ungraded realisation of `𝒜` *is* the
ungraded realisation of the degreewise pullback `g^*𝒜`, multiplication and unit included, for an
arbitrary morphism of schemes `g : X ⟶ Y` and an arbitrary sheaf of graded `𝒪_Y`-algebras with
commutative homogeneous multiplication. -/
theorem isIso_comparison : IsIso (comparison g 𝒜 hc) :=
  AlgebraPullbackQcoh.isIso_of_isIso_moduleMap (comparison g 𝒜 hc)
    (isIso_moduleMap_comparison g 𝒜 hc)

/-- **`Φ` as an isomorphism of sheaves of commutative `𝒪_X`-algebras.** -/
def comparisonIso :
    (algebraPullback g).obj (gradedAlgebraSheaf Y 𝒜 hc) ≅
      gradedAlgebraSheaf X (pbGraded g 𝒜) (pbGraded_mul_comm g 𝒜 hc) :=
  haveI := isIso_comparison g 𝒜 hc
  asIso (comparison g 𝒜 hc)

/-- The forward morphism of `comparisonIso` is `Φ`. -/
@[simp] theorem comparisonIso_hom :
    (comparisonIso g 𝒜 hc).hom = comparison g 𝒜 hc := rfl

end Algebra

end Stacks.GradedRealizationPullback

end
