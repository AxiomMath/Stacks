module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeSheafRuleWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RightAdjointHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmoothLocalHigherDirectImageCriterionProof
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SchemeStackPushforwardCartesian

/-!
# Stacks 0765: the higher direct images of `LQCoh^fbc` have the flat base change property

**Stacks 0765** applies the criterion of **Stacks 076Z** to the rule `LQCoh^fbc` of the locally
quasi-coherent étale sheaves of modules with the flat base change property. Hypotheses (1), (2)
and (3) of the criterion hold for that rule:

* (1) `AlgebraicGeometry.Stack.isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule`
  (**Stacks 06WM** (2), (3) with **Stacks 0764** (2));
* (2) `isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule`
  (**Stacks 06WL** with **Stacks 0764** (1));
* (3) `AlgebraicGeometry.Stack.isSmoothLocal_locallyQuasicoherentFlatBaseChangeSheafRule`
  (**Stacks 075Y** with **Stacks 0764** (3)).

Hypothesis (4), the affine case, is proved here: in positive degrees the higher direct images
vanish, a locally quasi-coherent module having no higher cohomology over objects lying over affine
schemes; in degree zero the direct image is `ℱ(- ×_Y X)`, which is again locally quasi-coherent
with the flat base change property
(`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafRule_pushforward_schemeStack`).

## Main results

* `preservesHigherDirectImages_locallyQuasicoherentFlatBaseChangeSheafRule`:
  the higher direct images along every quasi-compact quasi-separated 1-morphism of algebraic
  stacks carry `LQCoh^fbc` into itself, in every degree.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_moduleSheafHigherDirectImage`: for a
  quasi-compact quasi-separated 1-morphism `f` of algebraic stacks and a locally quasi-coherent
  étale module `ℱ` with the flat base change property, every `Rⁱf_*ℱ` has the flat base change
  property.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The criterion of Stacks 076Z at the rule `LQCoh^fbc`, from the affine case.**  Hypotheses
(1), (2) and (3) of the criterion hold for `LQCoh^fbc`; given hypothesis (4), the higher direct
images along every quasi-compact quasi-separated 1-morphism of algebraic stacks carry `LQCoh^fbc`
into itself, in every degree. -/
theorem preservesHigherDirectImages_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine
    (haff : StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS)) :
    StackEtaleModuleRule.PreservesHigherDirectImages.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) :=
  smoothLocalHigherDirectImageCriterion_unconditional.{u, t, u} B S hS _
    (isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule.{u, t} B E h S hS)
    (isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule.{u, t} B E h S hS)
    (isSmoothLocal_locallyQuasicoherentFlatBaseChangeSheafRule.{u, t, u} B E h S hS) haff

/-- **Hypothesis (4) of Stacks 076Z for `LQCoh^fbc`, in positive degrees.** For a 1-morphism `f`
between algebraic stacks representable by affine schemes and `i > 0`, the higher direct image
`Rⁱf_*ℱ` of a member `ℱ` of `LQCoh^fbc` is zero, hence a member. -/
theorem preservedBy_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine_of_pos
    (X Y : BigFppfOver B S hS) (hX : IsAffine X.left.1) (hY : IsAffine Y.left.1)
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) (i : ℕ) (hi : 0 < i) :
    StackEtaleModuleRule.PreservedBy B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) f i := by
  intro F hF
  have hz := isZero_moduleSheafHigherDirectImage_schemeStack_of_affine.{u, t} B S hS hX hY f i F
    (fun x hx => isZero_rightDerived_evaluation_of_isLocallyQuasicoherent B E h S hS _
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F hF.1 x hx i hi)
  have := isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule.{u, t} B E h S hS
    (schemeStack.{u, t} B S hS Y)
  exact ObjectProperty.prop_of_isZero
    (P := fun G : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (schemeStack.{u, t} B S hS Y).val.val.p (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)) =>
      locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS (schemeStack.{u, t} B S hS Y).val.val.p
        (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids G.val) hz

/-- **Hypothesis (4) of Stacks 076Z for `LQCoh^fbc`, in degree zero.** For a 1-morphism `f`
between algebraic stacks representable by affine schemes, `R⁰f_*ℱ = f_*ℱ` of a member `ℱ` of
`LQCoh^fbc` is a member. -/
theorem preservedBy_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine_zero
    (X Y : BigFppfOver B S hS) (hX : IsAffine X.left.1) (hY : IsAffine Y.left.1)
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) :
    StackEtaleModuleRule.PreservedBy B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) f 0 := by
  intro F hF
  let := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
  let := hasSheafify_associatedTopology_of_category_succ B S hS
    (schemeStack.{u, t} B S hS Y).val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (schemeStack.{u, t} B S hS Y).val.val.p
  let := isContinuous_rightAdjoint_of_adjunction B S hS (schemeStack.{u, t} B S hS Y).val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
    (etaleTopology B)
  have hN := locallyQuasicoherentFlatBaseChangeSheafRule_pushforward_schemeStack B S hS E h hX hY
    f F hF
  let e := (moduleSheafHigherDirectImageZeroIso.{u, u + 1, u, u + 1, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (schemeStack.{u, t} B S hS Y).val.val.p
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
      (etaleTopology_le_topology B)).app F ≪≫
    (moduleSheafPushforwardIsoOfRightAdjoint B S hS (schemeStack.{u, t} B S hS Y).val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
      (etaleTopology B) (etaleTopology_le_topology B)).app F
  have := isWeakSerre_locallyQuasicoherentFlatBaseChangeSheafRule.{u, t} B E h S hS
    (schemeStack.{u, t} B S hS Y)
  exact ObjectProperty.prop_of_iso
    (fun G : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (schemeStack.{u, t} B S hS Y).val.val.p (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)) =>
      locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS (schemeStack.{u, t} B S hS Y).val.val.p
        (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids G.val) e.symm hN

/-- **Hypothesis (4) of Stacks 076Z for `LQCoh^fbc`.** The higher direct images along a
1-morphism between algebraic stacks representable by affine schemes carry `LQCoh^fbc` into
itself, in every degree. -/
theorem preservesHigherDirectImagesOfAffine_locallyQuasicoherentFlatBaseChangeSheafRule :
    StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) := by
  intro X Y hX hY f i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact preservedBy_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine_zero B E h S hS
      X Y hX hY f
  · exact preservedBy_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine_of_pos B E h S hS
      X Y hX hY f i hi

/-- **The higher direct images along quasi-compact quasi-separated 1-morphisms preserve
`LQCoh^fbc`**: the criterion of Stacks 076Z, all four of its hypotheses discharged. -/
theorem preservesHigherDirectImages_locallyQuasicoherentFlatBaseChangeSheafRule :
    StackEtaleModuleRule.PreservesHigherDirectImages.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) :=
  preservesHigherDirectImages_locallyQuasicoherentFlatBaseChangeSheafRule_of_affine B E h S hS
    (preservesHigherDirectImagesOfAffine_locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS)

/-- Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (Stacks 050U) and quasi-separated
(Stacks 04YW) 1-morphism of algebraic stacks, and let `ℱ` be an étale sheaf of
`𝒪_𝒳`-modules which is locally quasi-coherent (Stacks 06WJ) and has the flat base change property
(Stacks 0762). Then every higher direct image `Rⁱf_*ℱ`, computed in the étale topology, has the
flat base change property.

The flat base change property is the source's, read on sheaves
(`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`); the sheaves of modules have their
sections in `Type (u + 1)`, where the higher direct images of Stacks 06WE live, and the source
`𝒳` is presented strictly, its structure functor written as the functor of `f` followed by that
of `𝒴`. -/
@[stacks 0765 "R^i f_* of a locally quasi-coherent étale module with the flat base change \
  property has the flat base change property, for f quasi-compact and quasi-separated"]
theorem hasFlatBaseChangePropertySheaf_moduleSheafHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hlqc : IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val)
    (hfbc : HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F)
    (i : ℕ) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
        (etaleTopology_le_topology B) i).obj F) :=
  (preservesHigherDirectImages_locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS f hqc hqs i
    F ⟨hlqc, F.isSheaf, fun _ => hfbc⟩).2.2 _

end AlgebraicGeometry.Stack

end
