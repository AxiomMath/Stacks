module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableSummandRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit

/-!
# Flatness of the transitions of the simplicial semi-representable ringed site

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`. Remark
0D9W observes that for the structure sheaf `O = a⁻¹O_C` of the total site of the simplicial site
`n ↦ C/K_n`, the morphisms of ringed topoi `f_φ` attached to the simplex maps `φ` are flat. The
reason is that `O` is pulled back along the augmentation, so its restrictions to the components
are related by isomorphisms: the structure map `f_φ⁻¹O_m ⟶ O_n` of `f_φ` is invertible.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isIso_fiberTransitionCommRing`: the structure maps
  of the transitions are isomorphisms.
* `CategoryTheory.SimplicialSemiRepresentable.transitionRingedToposHom_isFlat`: **Remark 0D9W**,
  the transitions `f_φ` are flat.
* `CategoryTheory.SimplicialSemiRepresentable.hasLeftDerivedFunctor_transition`: the derived
  pullbacks `Lf_φ^*` exist.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- The transitions of the underlying sheaf of sets of `a⁻¹O_C` are invertible: `a⁻¹O_C` is the
inverse image of a sheaf along the augmentation, which is cartesian (Stacks 0D7H (1)). -/
theorem isIso_fiberTransition_structureSheaf {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (((situation X.J K).fiberTransition φ).app
      ((sheafCompose (situation X.J K).totalTopology (forget CommRingCat.{u})).obj
        (structureSheaf X K))) := by
  have h := CocontinuousSimplicialSite.Augmentation.isIso_fiberTransition_app_inverseImage
    (augmentation X.J K) φ ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O)
  exact (NatTrans.isIso_app_iff_of_iso ((situation X.J K).fiberTransition φ)
    ((totalInverseImageIso X.J K).app ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O))).mp h

/-- The structure-sheaf transitions `f_φ⁻¹O_m ⟶ O_n` of `a⁻¹O_C` are isomorphisms. -/
theorem isIso_fiberTransitionCommRing {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((situation X.J K).fiberTransitionCommRing (structureSheaf X K) φ) := by
  have h : IsIso ((sheafCompose ((situation X.J K).componentTopology n)
      (forget CommRingCat.{u})).map
        ((situation X.J K).fiberTransitionCommRing (structureSheaf X K) φ)) := by
    rw [SimplicialSiteSituation.fiberTransitionCommRing_forget]
    exact isIso_fiberTransition_structureSheaf X K φ
  exact isIso_of_reflects_iso _
    (sheafCompose ((situation X.J K).componentTopology n) (forget CommRingCat.{u}))

/-- **Remark 0D9W: the transition morphisms `f_φ` are flat** for the structure sheaf
`O = a⁻¹O_C` of the total site of the simplicial site of `K`, their structure maps being
isomorphisms. -/
theorem transitionRingedToposHom_isFlat {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation X.J K).transitionRingedToposHom (structureSheaf X K) φ).IsFlat := by
  refine SheafOfModules.isFlatMapULift_of_isIso _ ?_
  rw [SimplicialSiteSituation.transitionRingedToposHom_fSharpInverseImage]
  exact isIso_fiberTransitionCommRing X K φ

open Stacks.Cohomology.DerivedPushforward in
attribute [local instance] HasDerivedCategory.standard in
/-- The derived pullbacks `Lf_φ^*` exist for `O = a⁻¹O_C`: pullback along a flat `f_φ` is exact,
so degreewise pullback followed by localization inverts quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_transition (m n : SimplexCategory) (φ : m ⟶ n) :
    (pullbackOnHomotopy ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
      φ)).HasLeftDerivedFunctor
      (targetQuasiIso ((situation X.J K).componentRingedTopos (structureSheaf X K) m)) := by
  let f := (situation X.J K).transitionRingedToposHom (structureSheaf X K) φ
  let : PreservesFiniteLimits f.toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 ((situation X.J K).exactFunctor_transitionPullbackModules'
      (structureSheaf X K) φ (transitionRingedToposHom_isFlat X K φ))).1
  let : PreservesFiniteColimits f.toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits f
  have hinv : (targetQuasiIso ((situation X.J K).componentRingedTopos (structureSheaf X K)
      m)).IsInvertedBy (pullbackOnHomotopy.{u, u, u, u, u, u} f) := by
    intro A B s hs
    have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh _ s hs
    exact (NatIso.isIso_map_iff f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh s).mp
      (Functor.map_isIso f.toModulesHom.pullbackModules.mapDerivedCategory
        (DerivedCategory.Qh.map s))
  have := Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hinv
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _
end CategoryTheory.SimplicialSemiRepresentable
