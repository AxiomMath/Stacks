module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.SchemesOverCoveringFamily

/-!
# The relative Picard functor of a base change (towards Stacks 0D2C)

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` (the
standing data of Stacks 08KB) and `g : Y' ⟶ Y` a morphism of algebraic spaces, with
`X' = X ×_Y Y'`.  The proof of Stacks 0D2C observes that
`Pic_{X'/Y'} = Y' ×_Y Pic_{X/Y}`: read on the test schemes over `Y'`, the relative Picard functor
of `X' ⟶ Y'` is that of `X ⟶ Y`; this is
`AlgebraicGeometry.Space.CoherentSituation.picardFunctorBaseChangeIso`.

## Main results

* `AlgebraicGeometry.Space.SchemesOver.coverPreserving_map`,
  `AlgebraicGeometry.Space.SchemesOver.compatiblePreserving_map`,
  `AlgebraicGeometry.Space.SchemesOver.isContinuous_map` and
  `AlgebraicGeometry.Space.SchemesOver.isCocontinuous_map`: reading a test scheme over `Y'` as
  one over `Y`, along `g`, is continuous and cocontinuous for the fppf topologies.
* `AlgebraicGeometry.Space.CoherentSituation.picardPresheafBaseChangeIso`: the presheaves
  `T ↦ Pic(X'_T)` and `T ↦ Pic(X_T)` agree on the test schemes over `Y'`, through the comparison
  `X'_T ≅ X_T` of `AlgebraicGeometry.Space.CoherentSituation.baseChangeSpaceIso`.
* `AlgebraicGeometry.Space.CoherentSituation.picardFunctorBaseChangeIso`: `Pic_{X'/Y'}` is
  `Pic_{X/Y}` read on the test schemes over `Y'`.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space.SchemesOver

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)

/-- Reading a test scheme over `Y'` as one over `Y` does not change its scheme. -/
theorem map_comp_proj : CostructuredArrow.map g ⋙ proj Y = proj Y' :=
  rfl

/-- **Reading test schemes over `Y'` as test schemes over `Y` preserves covering sieves.** -/
theorem coverPreserving_map :
    CoverPreserving (topology Y') (topology Y) (CostructuredArrow.map g) where
  cover_preserve {U R} hR := by
    refine Functor.mem_restrictedTopology_of_functorPushforward_mem ?_
    rw [← Sieve.functorPushforward_comp]
    exact functorPushforward_mem_of_mem_restrictedTopology hR

/-- **Reading test schemes over `Y'` as test schemes over `Y` is cocontinuous**: a covering sieve
of a test scheme over `Y'`, read over `Y`, pulls back to a covering sieve. -/
instance isCocontinuous_map :
    (CostructuredArrow.map g).IsCocontinuous (topology Y') (topology Y) where
  cover_lift {U} R hR := by
    refine Functor.mem_restrictedTopology_of_functorPushforward_mem
      (GrothendieckTopology.superset_covering _ ?_
        (functorPushforward_mem_of_mem_restrictedTopology (Y := Y) hR))
    rintro V f ⟨W, r, k, hr, rfl⟩
    let W' : SchemesOver Y' := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map r.left ≫ U.hom)
    let r' : W' ⟶ U := CostructuredArrow.homMk' U r.left
    let e : (CostructuredArrow.map g).obj W' ⟶ W := CostructuredArrow.homMk (𝟙 W.left)
      (by simpa [W', Category.assoc] using (CostructuredArrow.w r).symm)
    refine ⟨W', r', k, ?_, rfl⟩
    have : (CostructuredArrow.map g).map r' = e ≫ r :=
      CostructuredArrow.hom_ext _ _ (Category.id_comp _).symm
    change R.arrows ((CostructuredArrow.map g).map r')
    rw [this]
    exact R.downward_closed hr e

/-- **Reading test schemes over `Y'` as test schemes over `Y` preserves compatible families.** -/
theorem compatiblePreserving_map :
    CompatiblePreserving.{w} (topology Y) (CostructuredArrow.map g) where
  compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    have hl : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := congrArg CommaMorphism.left h
    let W' : SchemesOver Y' :=
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := CostructuredArrow.homMk f₁.left rfl
    let g₂' : W' ⟶ Y₂ := CostructuredArrow.homMk f₂.left (by
      rw [← CostructuredArrow.w g₂, ← Category.assoc, ← Functor.map_comp, ← hl, Functor.map_comp,
        Category.assoc, CostructuredArrow.w g₁]
      rfl)
    let e : (CostructuredArrow.map g).obj W' ≅ W := CostructuredArrow.isoMk (Iso.refl _) (by
      simpa [W', Category.assoc] using (CostructuredArrow.w f₁).symm)
    have h₁ : f₁ = e.inv ≫ (CostructuredArrow.map g).map g₁' :=
      CostructuredArrow.hom_ext _ _ (Category.id_comp _).symm
    have h₂ : f₂ = e.inv ≫ (CostructuredArrow.map g).map g₂' :=
      CostructuredArrow.hom_ext _ _ (Category.id_comp _).symm
    have key := hx g₁' g₂' hg₁ hg₂ (CostructuredArrow.hom_ext _ _ hl)
    rw [h₁, h₂, op_comp, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
    exact congrArg (F.obj.map e.inv.op) key

/-- **Reading test schemes over `Y'` as test schemes over `Y` is continuous.** -/
instance isContinuous_map :
    (CostructuredArrow.map g).IsContinuous (topology Y') (topology Y) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_map g) (coverPreserving_map g)

end AlgebraicGeometry.Space.SchemesOver


/-! ### The Picard functor of a base change -/

namespace AlgebraicGeometry.Space.CoherentSituation

open SchemesOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS) {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y)

/-- **The presheaf `T ↦ Pic(X'_T)` of the base change is the presheaf `T ↦ Pic(X_T)` read on the
test schemes over `Y'`**: at a test scheme `T` over `Y'`, pullback along the comparison
`X'_T ≅ X_T` of the two base changes. -/
def picardPresheafBaseChangeIso :
    (D.baseChange g).toPicardSituation.picardPresheaf ≅
      (CostructuredArrow.map g).op ⋙ D.toPicardSituation.picardPresheaf :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun := picardPullback (D.baseChangeSpaceIso g T.unop).inv
      invFun := picardPullback (D.baseChangeSpaceIso g T.unop).hom
      left_inv := fun x ↦ (picardPullback_comp _ _ x).symm.trans
        ((congrArg (fun q ↦ picardPullback q x) (Iso.hom_inv_id _)).trans
          (picardPullback_id (modulePushforwardCoherence B S hS) _ x))
      right_inv := fun x ↦ (picardPullback_comp _ _ x).symm.trans
        ((congrArg (fun q ↦ picardPullback q x) (Iso.inv_hom_id _)).trans
          (picardPullback_id (modulePushforwardCoherence B S hS) _ x)) })
    fun {T T'} h ↦ by
      ext x
      change picardPullback (D.baseChangeSpaceIso g T'.unop).inv
          (picardPullback (baseChangeMap (D.baseChange g).f h.unop) x) =
        picardPullback (baseChangeMap D.f ((CostructuredArrow.map g).map h.unop))
          (picardPullback (D.baseChangeSpaceIso g T.unop).inv x)
      exact (picardPullback_comp _ _ x).symm.trans
        ((congrArg (fun q ↦ picardPullback q x)
          (baseChangeSpaceIso_inv_naturality D g h.unop)).trans
          (picardPullback_comp _ _ x))

/-- **`Pic_{X'/Y'} = Y' ×_Y Pic_{X/Y}`.** The relative Picard functor of the base change
`X' = X ×_Y Y' ⟶ Y'` is the relative Picard functor of `X ⟶ Y` read on the test schemes over
`Y'`. -/
def picardFunctorBaseChangeIso :
    (D.baseChange g).toPicardSituation.picardFunctor ≅
      (CostructuredArrow.map g).op ⋙ D.toPicardSituation.picardFunctor :=
  (sheafToPresheaf (topology Y') (Type (u + 1))).mapIso
    ((presheafToSheaf (topology Y') (Type (u + 1))).mapIso (D.picardPresheafBaseChangeIso g) ≪≫
    ((CostructuredArrow.map g).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (topology Y') (topology D.Y)).app D.toPicardSituation.picardPresheaf)

end AlgebraicGeometry.Space.CoherentSituation

end
