module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraiding

/-!
# Affine-chartwise base change for a tensor factor on the right

The isomorphism `L g^*(A ⊗ᴸ A') ≅ L g^*A ⊗ᴸ L g^*A'` for a morphism `g` of algebraic spaces is
compatible with the commutativity constraints of the derived tensor products. Consequently the
condition `AffineChartwiseBaseChange` passes to `K ⊗ᴸ E` as well as to `E ⊗ᴸ K`: the two maps
`L(g')^*(K ⊗ᴸ E) ⟶ K' ⊗ᴸ L(g')^*E` and `L(g')^*(E ⊗ᴸ K) ⟶ L(g')^*E ⊗ᴸ K'` correspond under the
commutativity constraints.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_braiding`: the isomorphism
  `smallEtaleDerivedPullbackTensorIso` is compatible with the commutativity constraints.
* `AlgebraicGeometry.Space.affineChartwiseBaseChange_tensor_right`: `AffineChartwiseBaseChange`
  passes from `K` to `K ⊗ᴸ E`.

## References

* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For `g : X' ⟶ X` and `A, A' ∈ D(𝒪_X)`, the two isomorphisms
`Lg^*(A ⊗^L A') ≅ Lg^*A' ⊗^L Lg^*A` built from `smallEtaleDerivedPullbackTensorIso` and the
commutativity constraints of `⊗^L` agree. -/
theorem smallEtaleDerivedPullbackTensorIso_braiding {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedTensorProduct B S hS X).braiding A A').hom ≫
        (smallEtaleDerivedPullbackTensorIso g).hom.app (A', A) =
      (smallEtaleDerivedPullbackTensorIso g).hom.app (A, A') ≫
        ((smallEtaleDerivedTensorProduct B S hS X').braiding
          ((smallEtaleDerivedModulePullback B S hS g).obj A)
          ((smallEtaleDerivedModulePullback B S hS g).obj A')).hom :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_braiding
    (smallEtaleRingedToposHom B S hS g) (smallEtaleDerivedTensorProduct B S hS X')
    (smallEtaleDerivedTensorProduct B S hS X) A A'

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- For quasi-coherent `E`, `K` on `X`, `K'` on `X'` and `φ : L(g')^*K ⟶ K'`: if
`AffineChartwiseBaseChange` holds for `(K, K', φ)`, it holds for `(K ⊗ᴸ E, K' ⊗ᴸ L(g')^*E)` and
`smallEtaleDerivedPullbackTensorIso` followed by `φ ⊗ᴸ L(g')^*E`. -/
theorem affineChartwiseBaseChange_tensor_right (w : g' ≫ f = f' ≫ g)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ) :
    AffineChartwiseBaseChange B S hS f g f' g' w (((smallEtaleDerivedTensor B S hS X).obj K).obj E)
      (((smallEtaleDerivedTensor B S hS X').obj K').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E))
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (K, E) ≫
        ((smallEtaleDerivedTensor B S hS X').map φ).app
          ((smallEtaleDerivedModulePullback B S hS g').obj E)) := by
  refine AffineChartwiseBaseChange.of_iso f g f' g' w
    ((smallEtaleDerivedTensorProduct B S hS X).braiding E K)
    ((smallEtaleDerivedTensorProduct B S hS X').braiding
      ((smallEtaleDerivedModulePullback B S hS g').obj E) K') _ _ ?_
    (affineChartwiseBaseChange_tensor B S hS f g f' g' w E K hE hK K' hK' φ h)
  exact (Category.assoc _ _ _).trans ((congrArg
      (fun z ↦ (smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫ z)
      ((smallEtaleDerivedTensorProduct B S hS X').braiding_hom_naturality_right
        ((smallEtaleDerivedModulePullback B S hS g').obj E) φ)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((smallEtaleDerivedTensor B S hS X').map
        φ).app ((smallEtaleDerivedModulePullback B S hS g').obj E))
      (smallEtaleDerivedPullbackTensorIso_braiding g' E K).symm).trans (Category.assoc _ _ _))))

end AlgebraicGeometry.Space

end
