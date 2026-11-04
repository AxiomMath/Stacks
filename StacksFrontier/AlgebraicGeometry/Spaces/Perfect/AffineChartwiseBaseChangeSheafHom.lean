module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensorRight
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualExactPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackMonoidal

/-!
# Condition (2) of Stacks 0DKG for the derived internal Hom out of a perfect object

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces, `K`, `K'` with quasi-coherent
cohomology and `φ : L(g')^*K ⟶ K'`. For `E` perfect on `X`, condition (2) of Stacks 0DKG passes
from `(K, K', φ)` to `R𝓗om(E, K)`, `R𝓗om(L(g')^*E, K')` and the map
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, L(g')^*K) ⟶ R𝓗om(L(g')^*E, K')` (Stacks 08JF followed by
`φ`): this is case (2) of Stacks 0DKI read on affine étale quadruples.

The proof reduces to the tensor case. `E^∨ = R𝓗om(E, 𝒪_X)` is a left dual of `E` (Stacks 0FPV),
so `K ⊗^L E^∨ ≅ R𝓗om(E, K)`; derived pullback is monoidal, so `L(g')^*E^∨` is a left dual of
`L(g')^*E` and `K' ⊗^L L(g')^*E^∨ ≅ R𝓗om(L(g')^*E, K')`; under these isomorphisms the map above
is Stacks 07A4 followed by `φ ⊗^L L(g')^*E^∨`.

## Main results

* `AlgebraicGeometry.Space.affineChartwiseBaseChange_sheafHom_of_isPerfect`.

## References

* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

/- This instance would change the elaboration below (universe joins, the small model of
`D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **Condition (2) of Stacks 0DKG passes to the derived internal Hom out of a perfect object**
(Stacks 0DKI (2), on affine étale quadruples). For `E` perfect on `X`, quasi-coherent `K` on `X`
and `K'` on `X'`, and `φ : L(g')^*K ⟶ K'`: if condition (2) of Stacks 0DKG holds for
`(K, K', φ)`, it holds for `R𝓗om(E, K)`, `R𝓗om(L(g')^*E, K')` and the map of Stacks 08JF
followed by `R𝓗om(L(g')^*E, φ)`. -/
theorem affineChartwiseBaseChange_sheafHom_of_isPerfect (w : g' ≫ f = f' ≫ g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ) :
    AffineChartwiseBaseChange B S hS f g f' g' w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
      (((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
      (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
        ((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ) := by
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X))) := smallEtaleDerivedMonoidal X
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X'))) := smallEtaleDerivedMonoidal X'
  let F := smallEtaleDerivedModulePullback B S hS g'
  let Ed := ((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (𝟙_ _)
  let p := smallEtaleDerivedDualExactPairing X E hE
  let p' := @ExactPairing.map _ _ _ _ (smallEtaleDerivedMonoidal X) (smallEtaleDerivedMonoidal X')
    F (smallEtaleDerivedPullbackMonoidal g') E Ed p
  have hEd : QcohDerived B S hS X Ed :=
    qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X _ _ hE
      (derivedStructureSheaf B S hS X.1 X.2).property
  have he := @CategoryTheory.PullbackInternalHom.isIso_exactPairingTensorHomMap _ _
    (smallEtaleDerivedMonoidal X) (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) E Ed p K
  have he' := @CategoryTheory.PullbackInternalHom.isIso_exactPairingTensorHomMap _ _
    (smallEtaleDerivedMonoidal X') (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') (F.obj E) (F.obj Ed) p' K'
  refine AffineChartwiseBaseChange.of_iso f g f' g' w (@asIso _ _ _ _ _ he) (@asIso _ _ _ _ _ he')
    _ _ ?_ (affineChartwiseBaseChange_tensor_right f g f' g' w _ K hEd hK K' hK' φ h)
  have hnat := @CategoryTheory.PullbackInternalHom.exactPairingTensorHomMap_naturality _ _
    (smallEtaleDerivedMonoidal X') (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') (F.obj E) (F.obj Ed) p' _ _ φ
  have hmap := @CategoryTheory.PullbackInternalHom.map_exactPairingTensorHomMap_comp_pullbackHomMap
    _ _ (smallEtaleDerivedMonoidal X) (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) _ _ (smallEtaleDerivedMonoidal X')
    (smallEtaleDerivedSheafHom B S hS X') (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
    F (smallEtaleDerivedPullbackMonoidal g') (smallEtaleDerivedPullbackTensorIso g')
    (fun _ _ => rfl) E Ed K p
  have h08 : smallEtaleDerivedPullbackSheafHomMap g' E K =
      CategoryTheory.PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
        (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g')
        (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') E K := by
    rw [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit]
    unfold CategoryTheory.PullbackInternalHom.pullbackHomMap
    congr 1
  have hmap' : F.map (@CategoryTheory.PullbackInternalHom.exactPairingTensorHomMap _ _
        (smallEtaleDerivedMonoidal X) (smallEtaleDerivedSheafHom B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) E Ed p K) ≫
        smallEtaleDerivedPullbackSheafHomMap g' E K =
      (smallEtaleDerivedPullbackTensorIso g').hom.app (K, Ed) ≫
        @CategoryTheory.PullbackInternalHom.exactPairingTensorHomMap _ _
          (smallEtaleDerivedMonoidal X') (smallEtaleDerivedSheafHom B S hS X')
          (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') (F.obj E) (F.obj Ed) p'
          (F.obj K) := by
    rw [h08]
    exact hmap
  exact (Category.assoc _ _ _).trans ((congrArg
    ((smallEtaleDerivedPullbackTensorIso g').hom.app (K, Ed) ≫ ·) hnat).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((smallEtaleDerivedSheafHom B S hS X').obj
      (op (F.obj E))).map φ) hmap'.symm).trans (Category.assoc _ _ _))))

end AlgebraicGeometry.Space

end
