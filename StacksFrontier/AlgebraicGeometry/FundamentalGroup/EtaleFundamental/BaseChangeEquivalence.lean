module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The fundamental group of a morphism along which base change is an equivalence

Let `f : X ⟶ Y` be a morphism of connected schemes such that base change
`FÉt_Y ⥤ FÉt_X` is an equivalence of categories, and let `x` be a geometric point of `X`. Then
the induced continuous homomorphism `π₁(X, x) → π₁(Y, f ∘ x)` of Stacks 0BND is an isomorphism
of topological groups.

## Main definitions

* `AlgebraicGeometry.etaleFundamentalGroupMulEquivOfIsEquivalence` — the induced map on étale
  fundamental groups as an isomorphism of groups.
* `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquivOfIsEquivalence` — the same as an
  isomorphism of topological groups.

## Main results

* `AlgebraicGeometry.bijective_etaleFundamentalGroupMap_of_isEquivalence` — the induced map is
  bijective.
* `AlgebraicGeometry.continuous_etaleFundamentalGroupMulEquivOfIsEquivalence_symm` — its inverse
  is continuous.

## Implementation notes

Only part (2) of Stacks 0BQA is proved here. Part (1), that `f` induces a homeomorphism
`π₀(X) → π₀(Y)`, concerns connected components of spectral spaces; the hypotheses of the tag
(quasi-compact and quasi-separated) are needed for part (1) only, so they do not appear.

## References

* [Stacks Project, Tag 0BQA](https://stacks.math.columbia.edu/tag/0BQA)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]

/-- If base change along `f` is an equivalence on finite étale covers, then whiskering on the left
with base change along `f` is fully faithful. -/
def fullyFaithfulWhiskeringLeftFiniteEtaleBaseChange (f : X ⟶ Y)
    [(finiteEtaleBaseChange f).IsEquivalence] :
    ((Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
      (finiteEtaleBaseChange f)).FullyFaithful :=
  have : ((Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
      (finiteEtaleBaseChange f)).IsEquivalence :=
    (Equivalence.congrLeft (finiteEtaleBaseChange f).asEquivalence).symm.isEquivalence_functor
  .ofFullyFaithful _

/-- If base change along `f` is an equivalence on finite étale covers, the induced homomorphism
of étale fundamental groups is bijective. -/
theorem bijective_etaleFundamentalGroupMap_of_isEquivalence (f : X ⟶ Y)
    (x : GeometricPoint X) [(finiteEtaleBaseChange f).IsEquivalence] :
    Function.Bijective (etaleFundamentalGroupMap f x) :=
  (finiteEtaleFiberProjectionIso f x).conjAut.bijective.comp
    ((fullyFaithfulWhiskeringLeftFiniteEtaleBaseChange f).autMulEquivOfFullyFaithful
      (finiteEtaleFiberFunctor x)).bijective

/-- The isomorphism of étale fundamental groups induced by a morphism along which base change is
an equivalence on finite étale covers. -/
def etaleFundamentalGroupMulEquivOfIsEquivalence (f : X ⟶ Y) (x : GeometricPoint X)
    [(finiteEtaleBaseChange f).IsEquivalence] :
    EtaleFundamentalGroup X x ≃* EtaleFundamentalGroup Y (x.map f) :=
  MulEquiv.ofBijective (etaleFundamentalGroupMap f x).toMonoidHom
    (bijective_etaleFundamentalGroupMap_of_isEquivalence f x)

/-- The isomorphism `etaleFundamentalGroupMulEquivOfIsEquivalence f x` agrees with
`etaleFundamentalGroupMap f x`. -/
@[simp]
theorem etaleFundamentalGroupMulEquivOfIsEquivalence_apply (f : X ⟶ Y) (x : GeometricPoint X)
    [(finiteEtaleBaseChange f).IsEquivalence] (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquivOfIsEquivalence f x σ = etaleFundamentalGroupMap f x σ :=
  rfl

/-- If base change along `f` is an equivalence on finite étale covers, the inverse of the induced
isomorphism of étale fundamental groups is continuous. -/
theorem continuous_etaleFundamentalGroupMulEquivOfIsEquivalence_symm (f : X ⟶ Y)
    (x : GeometricPoint X) [(finiteEtaleBaseChange f).IsEquivalence] :
    Continuous (etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm := by
  refine Stacks.FundamentalGroup.continuous_of_continuous_component
    (finiteEtaleFiberFunctor (x.map f)) (finiteEtaleFiberFunctor x)
    (etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm fun V q ↦ ?_
  let W : FiniteEtaleOver Y := (finiteEtaleBaseChange f).objPreimage V
  let α : (finiteEtaleBaseChange f).obj W ≅ V :=
    (finiteEtaleBaseChange f).objObjPreimageIso V
  -- The component at `V` of the preimage of `σ`, as a continuous function of `σ`.
  have hkey : ∀ σ : EtaleFundamentalGroup Y (x.map f),
      (((etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm σ).asIso.app V).hom q =
        (finiteEtaleFiberFunctor x).map α.hom
          ((finiteEtaleFiberProjectionEquiv f x W).symm ((σ.asIso.app W).hom
            (finiteEtaleFiberProjection f x W
              ((finiteEtaleFiberFunctor x).map α.inv q)))) := by
    intro σ
    have hτσ : etaleFundamentalGroupMap f x
        ((etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm σ) = σ :=
      (etaleFundamentalGroupMulEquivOfIsEquivalence f x).apply_symm_apply σ
    have hqq : (finiteEtaleFiberFunctor x).map α.hom
        ((finiteEtaleFiberFunctor x).map α.inv q) = q := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, α.inv_hom_id,
        CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
    -- the component at the base change of `W`, by the defining property of the induced map
    have hproj := etaleFundamentalGroupMap_finiteEtaleFiberProjection f x W
      ((etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm σ)
      ((finiteEtaleFiberFunctor x).map α.inv q)
    rw [hτσ] at hproj
    have hcomp : ((((etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm σ).asIso.app
          ((finiteEtaleBaseChange f).obj W)).hom)
          ((finiteEtaleFiberFunctor x).map α.inv q) =
        (finiteEtaleFiberProjectionEquiv f x W).symm ((σ.asIso.app W).hom
          (finiteEtaleFiberProjection f x W
            ((finiteEtaleFiberFunctor x).map α.inv q))) := by
      rw [← hproj]
      exact ((finiteEtaleFiberProjectionEquiv f x W).symm_apply_apply _).symm
    -- naturality of the preimage of `σ` along `α`
    have hnat := NatTrans.naturality_apply
      ((etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm σ).asIso.hom α.hom
      ((finiteEtaleFiberFunctor x).map α.inv q)
    rw [hqq] at hnat
    exact hnat.trans (congrArg (fun z ↦ (finiteEtaleFiberFunctor x).map α.hom z) hcomp)
  let _tA : TopologicalSpace (Aut (finiteEtaleFiberFunctor (x.map f))) :=
    Stacks.FundamentalGroup.functorAutomorphismTopology (finiteEtaleFiberFunctor (x.map f))
  let _tW : TopologicalSpace ((finiteEtaleFiberFunctor (x.map f)).obj W) := ⊥
  let _dW : DiscreteTopology ((finiteEtaleFiberFunctor (x.map f)).obj W) := ⟨rfl⟩
  let _tV : TopologicalSpace ((finiteEtaleFiberFunctor x).obj V) := ⊥
  have hinner := Stacks.FundamentalGroup.continuous_componentEmbedding_apply
    (finiteEtaleFiberFunctor (x.map f)) W
    (finiteEtaleFiberProjection f x W ((finiteEtaleFiberFunctor x).map α.inv q))
  have houter : @Continuous ((finiteEtaleFiberFunctor (x.map f)).obj W)
      ((finiteEtaleFiberFunctor x).obj V) _tW _tV
      (fun b ↦ (finiteEtaleFiberFunctor x).map α.hom
        ((finiteEtaleFiberProjectionEquiv f x W).symm b)) :=
    continuous_of_discreteTopology
  exact (houter.comp hinner).congr fun σ ↦ (hkey σ).symm

/-- If base change along `f : X ⟶ Y` is an equivalence on finite étale covers, then `f` identifies
the étale fundamental group of `X` at a geometric point `x` with the étale fundamental group of `Y`
at the image geometric point, as topological groups. -/
@[stacks 0BQA "part (2)", sga "4 XII 6.5" "(ii) b')⇒b'') π₁"]
def etaleFundamentalGroupContinuousMulEquivOfIsEquivalence (f : X ⟶ Y) (x : GeometricPoint X)
    [(finiteEtaleBaseChange f).IsEquivalence] :
    EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup Y (x.map f) where
  toMulEquiv := etaleFundamentalGroupMulEquivOfIsEquivalence f x
  continuous_toFun := (etaleFundamentalGroupMap f x).continuous_toFun
  continuous_invFun := continuous_etaleFundamentalGroupMulEquivOfIsEquivalence_symm f x

end AlgebraicGeometry

end
