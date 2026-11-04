module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.Coreflective

/-!
# `QCoh(𝒪_𝒳)` is the Serre quotient of `LQCoh^fbc(𝒪_𝒳)` by its parasitic objects (Stacks 07B2)

Let `𝒳` be an algebraic stack. **Stacks 07B2** reads off **Stacks 0778** and **Stacks 0779** that

`QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`,

the category of quasi-coherent modules is the category of locally quasi-coherent modules with the
flat base change property divided by the Serre subcategory of parasitic objects
(**Stacks 02MS**), and stresses that the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` is left
adjoint to the quotient functor.

This file proves both assertions with no hypothesis beyond `𝒳` being an algebraic stack, at
module universe `u`, for the corrected, sheaf-level `LQCoh^fbc`
(`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`; see
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty`). The inputs are
all theorems:

* `LQCoh^fbc(𝒪_𝒳)` is abelian, being closed in `Mod(𝒪_𝒳)` under kernels and cokernels
  (**Stacks 0771** part (2), fppf half) and under finite products, which are coproducts
  (**Stacks 0771** part (5));
* the coherator `Q = AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator` is right adjoint
  to the fully faithful inclusion `i` (**Stacks 0778**,
  `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorAdjunction`);
* `Q` is right exact and kills exactly the parasitic objects (**Stacks 0779** parts (3) and (1)).

A right exact right adjoint of a fully faithful functor is the Serre quotient by its kernel
(`CategoryTheory.Abelian.isLocalization_isoModSerre_of_rightAdjoint`), so `Q` is a localization
functor at the morphisms with parasitic kernel and cokernel, which is the displayed
identification; the adjunction is that of **Stacks 0778** read through it.

The base registrations of 07B2 in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorSerreQuotient.lean` carry the inputs
of 0778 and 0779 as hypotheses, over the presheaf-level `LQCoh^fbc`; they are left untouched.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSerreClass_parasiticLqcohFbc`: the parasitic part of
  `LQCoh^fbc(𝒪_𝒳)` is a Serre subcategory.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocalization_lqcohFbcCoherator`: **Stacks 07B2**, the
  displayed identification.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSerreQuotientEquivalence`: the same as an
  equivalence between Mathlib's Serre quotient and `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSerreQuotientAdjunction`: **Stacks 07B2**, the
  inclusion is left adjoint to the quotient functor.

## References

* [Stacks Project, Tag 07B2](https://stacks.math.columbia.edu/tag/07B2)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`: the parasitic objects (**Stacks 0773**) of
`LQCoh^fbc(𝒪_𝒳)`, as an object property of `LQCoh^fbc(𝒪_𝒳)`. -/
abbrev parasiticLqcohFbc :
    ObjectProperty (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory :=
  fun F => IsParasitic B S hS 𝒳 .fppf F.obj.val

/-- `LQCoh^fbc(𝒪_𝒳)` is closed under finite products in `Mod(𝒪_𝒳)`: a binary product is a
biproduct, hence a binary coproduct, and `LQCoh^fbc(𝒪_𝒳)` is closed under colimits
(**Stacks 0771** part (5),
`AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_lqcohSheafFbcFppfModules`).
With closure under kernels and cokernels (**Stacks 0771** part (2)) this makes `LQCoh^fbc(𝒪_𝒳)`
an abelian category. -/
instance isClosedUnderFiniteProducts_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderFiniteProducts := by
  have : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift.{u} (α := WalkingPair)))
  have : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (fun _ ⟨F, hF⟩ =>
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_of_iso
        ((biprod.isoCoprod _ _).symm.trans
          ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm))
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_coprod _ _ (hF ⟨.left⟩)
          (hF ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- An object of `LQCoh^fbc(𝒪_𝒳)` is parasitic exactly when the coherator kills it
(**Stacks 0779** part (1)). -/
theorem parasiticLqcohFbc_iff_isZero
    (F : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    parasiticLqcohFbc B E h S hS 𝒳 F ↔ IsZero ((lqcohFbcCoherator B E h S hS 𝒳).obj F) :=
  (isZero_coherator_obj_iff_isParasitic B S hS 𝒳 E h F.obj F.property).symm

/-- The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778** is right exact
(**Stacks 0779** part (3)). -/
instance preservesFiniteColimits_lqcohFbcCoherator :
    PreservesFiniteColimits (lqcohFbcCoherator B E h S hS 𝒳) :=
  (preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator
    B S hS 𝒳 E h).2

/-- **`Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` is a Serre subcategory of `LQCoh^fbc(𝒪_𝒳)`**, the
fact **Stacks 07B2** uses when it divides by it: it is the kernel of the right exact coherator
of **Stacks 0778**, by **Stacks 0779** part (1). -/
instance isSerreClass_parasiticLqcohFbc : (parasiticLqcohFbc B E h S hS 𝒳).IsSerreClass :=
  Abelian.isSerreClass_of_rightAdjoint (lqcohFbcCoheratorAdjunction B E h S hS 𝒳)
    (parasiticLqcohFbc_iff_isZero B E h S hS 𝒳)

/-- **Stacks 07B2**, the displayed identification
`QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`: for an algebraic stack `𝒳`, the
coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778** is a localization functor for the
morphisms whose kernel and cokernel are parasitic, i.e. it exhibits `QCoh(𝒪_𝒳)` as the Serre
quotient (**Stacks 02MS**) of `LQCoh^fbc(𝒪_𝒳)` by its parasitic objects. -/
@[stacks 07B2 "the displayed identification QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ \
LQCoh^fbc(𝒪_𝒳): the coherator Q of 0778 is a localization functor for the Serre class of \
parasitic objects"]
theorem isLocalization_lqcohFbcCoherator :
    (lqcohFbcCoherator B E h S hS 𝒳).IsLocalization
      (parasiticLqcohFbc B E h S hS 𝒳).isoModSerre :=
  Abelian.isLocalization_isoModSerre_of_rightAdjoint (lqcohFbcCoheratorAdjunction B E h S hS 𝒳)
    (parasiticLqcohFbc_iff_isZero B E h S hS 𝒳)

/-- **Stacks 07B2**, the displayed identification as an equivalence of categories between the
Serre quotient `LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` (the localization at the
morphisms with parasitic kernel and cokernel) and `QCoh(𝒪_𝒳)`, the one through which the
coherator of **Stacks 0778** factors. -/
@[stacks 07B2 "the displayed identification read as an equivalence of categories between the \
Serre quotient of LQCoh^fbc(𝒪_𝒳) by Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳) and QCoh(𝒪_𝒳)"]
def lqcohFbcSerreQuotientEquivalence :
    (parasiticLqcohFbc B E h S hS 𝒳).isoModSerre.Localization ≌ quasicoherentModules B S hS 𝒳 :=
  letI := isLocalization_lqcohFbcCoherator B E h S hS 𝒳
  Localization.equivalenceFromModel (lqcohFbcCoherator B E h S hS 𝒳)
    (parasiticLqcohFbc B E h S hS 𝒳).isoModSerre

/-- **Stacks 07B2**, the key feature: the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`, read on the
Serre quotient through `lqcohFbcSerreQuotientEquivalence`, is left adjoint to the quotient
functor `LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 07B2 "the key feature: the inclusion i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) is left adjoint \
to the quotient functor LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)"]
def lqcohFbcSerreQuotientAdjunction :
    (lqcohFbcSerreQuotientEquivalence B E h S hS 𝒳).functor ⋙
        quasicoherentToLqcohFbc B E h S hS 𝒳 ⊣
      (parasiticLqcohFbc B E h S hS 𝒳).isoModSerre.Q :=
  letI := isLocalization_lqcohFbcCoherator B E h S hS 𝒳
  Adjunction.ofNatIsoRight
    ((lqcohFbcSerreQuotientEquivalence B E h S hS 𝒳).toAdjunction.comp
      (lqcohFbcCoheratorAdjunction B E h S hS 𝒳))
    (Localization.compEquivalenceFromModelInverseIso (lqcohFbcCoherator B E h S hS 𝒳)
      (parasiticLqcohFbc B E h S hS 𝒳).isoModSerre)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
