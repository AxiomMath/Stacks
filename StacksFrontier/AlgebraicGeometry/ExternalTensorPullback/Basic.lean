module

public import StacksFrontier.AlgebraicGeometry.ChartImmersionAssembly.SegrePassage
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible

/-!
# Pullback of an external tensor product along a pair

Pullback of sheaves of modules along a morphism of schemes commutes with the tensor product sheaf
`Stacks.SheafOfModules.Tensor.sheafTensor`. Consequently, for `p : P ⟶ S`, `q : Q ⟶ S` and
morphisms `j : X ⟶ P`, `j' : X ⟶ Q` agreeing over `S`, the pullback of
`AlgebraicGeometry.externalTensorProduct p q F G` along `pullback.lift j j' h` is
`j ^* F ⊗ j' ^* G`. Applied to a Segre embedding with its twist, this gives an immersion into
projective space whose pullback of the hyperplane sheaf is the tensor product of two pullbacks.

## Main definitions

* `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso`: `g ^* (A ⊗ B) ≅ g ^* A ⊗ g ^* B` for a
  morphism of schemes `g`.
* `Stacks.Tag01VSPullbackTensor.pullbackLift_externalTensorProductIso`: the pullback of
  `AlgebraicGeometry.externalTensorProduct p q F G` along `pullback.lift j j' h` is
  `j ^* F ⊗ j' ^* G`.

## Main results

* `Stacks.Tag01VSPullbackTensor.exists_isImmersion_over_twist_of_segreTwist`: assuming
  `Stacks.ChartImmersionAssembly.SegreTwist n m S`, an immersion `j : X ⟶ ℙⁿ_S` and a morphism
  `j' : X ⟶ ℙᵐ_S` over `S` give an immersion `k : X ⟶ ℙ^{nm+n+m}_S` over `S` with
  `k ^* 𝒪(1) ≅ j ^* 𝒪(1) ⊗ j' ^* 𝒪(1)`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion

namespace Stacks.Tag01VSPullbackTensor

universe u

/-! ### Pullback and the tensor product sheaf -/

/-- Pullback of sheaves of modules along a morphism of schemes `g` commutes with the tensor
product sheaf: `g ^* (A ⊗_{𝒪_Y} B) ≅ g ^* A ⊗_{𝒪_X} g ^* B`, by the canonical comparison
`Stacks.RingedSpace.comparison`. -/
def schemePullbackTensorIso {X Y : Scheme.{u}} (g : X ⟶ Y) (A B : Y.Modules) :
    (Scheme.Modules.pullback g).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback g).obj A))).obj (((Scheme.Modules.pullback g).obj B))) :=
  @asIso _ _ _ _ (Stacks.RingedSpace.comparison g.toLRSHom.toShHom A B)
    (Stacks.PullbackTensorIso.isIso_comparison g.toLRSHom.toShHom A B)

/-- Functoriality of the tensor product sheaf in both arguments, as an isomorphism. -/
def tensorSheafMapIso {X : Scheme.{u}} {A A' B B' : X.Modules} (eA : A ≅ A') (eB : B ≅ B') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A')).obj (B')) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).mapIso eA).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A').mapIso eB

/-- Pseudofunctoriality of the module pullback with the composite named by an equation:
`g ^* (h ^* M) ≅ k ^* M` whenever `g ≫ h = k`. -/
def pullbackCompCongrIso {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) {k : X ⟶ Z}
    (hk : g ≫ h = k) (M : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M) ≅
      (Scheme.Modules.pullback k).obj M :=
  (Scheme.Modules.pullbackComp g h).app M ≪≫ (Scheme.Modules.pullbackCongr hk).app M

/-! ### Pullback of an external tensor product -/

/-- **The pullback of an external tensor product along a pair.** For `p : P ⟶ S`, `q : Q ⟶ S` and
morphisms `j : X ⟶ P`, `j' : X ⟶ Q` agreeing over `S`, the pullback of
`AlgebraicGeometry.externalTensorProduct p q F G` along the induced morphism
`X ⟶ P ×_S Q` is `j ^* F ⊗ j' ^* G`. -/
def pullbackLift_externalTensorProductIso {X S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (j : X ⟶ P) (j' : X ⟶ Q) (hcomm : j ≫ p = j' ≫ q) (F : P.Modules) (G : Q.Modules) :
    (Scheme.Modules.pullback (pullback.lift j j' hcomm)).obj (externalTensorProduct p q F G) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback j).obj F))).obj (((Scheme.Modules.pullback j').obj G))) :=
  schemePullbackTensorIso (pullback.lift j j' hcomm) _ _ ≪≫
    tensorSheafMapIso
      (pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.fst p q)
        (pullback.lift_fst j j' hcomm) F)
      (pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.snd p q)
        (pullback.lift_snd j j' hcomm) G)

/-! ### Immersions into projective space with a twist -/

/-- Assume `Stacks.ChartImmersionAssembly.SegreTwist n m S`, taken as the hypothesis `hseg`. Given
an immersion `j : X ⟶ ℙⁿ_S` over `S` and any morphism `j' : X ⟶ ℙᵐ_S` over `S`, there is an
immersion `k : X ⟶ ℙ^{nm+n+m}_S` over `S` whose pullback of the hyperplane sheaf is the tensor
product of the two pullbacks. -/
theorem exists_isImmersion_over_twist_of_segreTwist {X S : Scheme.{u}} {f : X ⟶ S} {n m : ℕ}
    (hseg : Stacks.ChartImmersionAssembly.SegreTwist n m S)
    (j : X ⟶ projectiveSpaceOver n S) (hj : j ≫ ((projectiveSpaceOver n S) ↘ S) = f)
    [IsImmersion j] (j' : X ⟶ projectiveSpaceOver m S)
    (hj' : j' ≫ ((projectiveSpaceOver m S) ↘ S) = f) :
    ∃ k : X ⟶ projectiveSpaceOver (n * m + n + m) S,
      IsImmersion k ∧ k ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) = f ∧
      Nonempty ((Scheme.Modules.pullback k).obj
            (projectiveSpaceTwistingSheaf (n * m + n + m) S) ≅
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf n S)))).obj
                (((Scheme.Modules.pullback j').obj (projectiveSpaceTwistingSheaf m S))))) := by
  obtain ⟨σ, hcl, hover, ⟨e⟩⟩ := hseg
  have hcomm : j ≫ ((projectiveSpaceOver n S) ↘ S) = j' ≫ ((projectiveSpaceOver m S) ↘ S) :=
    hj.trans hj'.symm
  have hpair : IsImmersion (pullback.lift j j' hcomm) := isImmersion_lift j j' hcomm
  have hσ : IsImmersion σ := have := hcl; inferInstance
  refine ⟨pullback.lift j j' hcomm ≫ σ, inferInstance, ?_, ⟨?_⟩⟩
  · rw [Category.assoc, hover, ← Category.assoc, pullback.lift_fst, hj]
  · exact (pullbackCompCongrIso (pullback.lift j j' hcomm) σ rfl _).symm ≪≫
      (Scheme.Modules.pullback (pullback.lift j j' hcomm)).mapIso e ≪≫
      pullbackLift_externalTensorProductIso _ _ j j' hcomm _ _

end Stacks.Tag01VSPullbackTensor

end
