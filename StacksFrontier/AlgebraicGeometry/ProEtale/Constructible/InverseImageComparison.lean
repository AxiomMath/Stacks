module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.AlgebraicGeometry.ProEtale.CoefficientRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeSupplement

/-!
# Inverse images of pro-étale sheaves of modules: restriction and underlying abelian sheaves

Let `Λ` be a ring. Inverse image of sheaves of `Λ`-modules on small pro-étale sites,
`AlgebraicGeometry.ProEtale.proetaleModuleInverseImage`, is compared with two other functors:

* along a weakly étale morphism `j : U ⟶ X` it is restriction along composition with `j`, since
  both are left adjoint to restriction along base change;
* it commutes with passing to underlying abelian sheaves: the forgetful functor of modules
  preserves the colimits computing the left Kan extension and preserves sheafification, being a
  left adjoint.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageIsoRestriction`: the first comparison.
* `AlgebraicGeometry.ProEtale.forget₂ProetaleModuleInverseImageIso`: the second comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous

variable (Λ : Type v) [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint: it is restriction
of scalars along `ℤ ⟶ Λ` followed by the identification of `ℤ`-modules with abelian groups. -/
theorem isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat.{max v w}).IsLeftAdjoint := by
  change (ModuleCat.restrictScalars.{max v w} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{max v w} ℤ) AddCommGrpCat).IsLeftAdjoint
  infer_instance

/-- Passing to underlying abelian sheaves commutes with sheafification on any site. -/
theorem preservesSheafification_forget₂_moduleCat_ofLeftAdjoint {C : Type*} [Category* C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat.{max v w}) :=
  have := isLeftAdjoint_forget₂_moduleCat.{v, w} Λ
  Sheaf.preservesSheafification_of_adjunction J
    (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat.{max v w}))

/-- **Inverse image along a weakly étale morphism is restriction.** For a weakly étale
`j : U ⟶ X`, inverse image of pro-étale sheaves of `Λ`-modules along `j` is restriction along
composition with `j`: both are left adjoint to restriction along base change. -/
def proetaleModuleInverseImageIsoRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    proetaleModuleInverseImage.{u, v, w} j Λ ≅
      (proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
        (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  (proetaleModuleInverseImageAdjunction.{u, v, w} Λ j).leftAdjointUniq
    ((proetalePostcomposeAdjunction j).sheafPushforwardContinuous _ _)

/-- **Inverse image commutes with passing to underlying abelian sheaves.** -/
def forget₂ProetaleModuleInverseImageIso {Z X : Scheme.{u}} (g : Z ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :
    (sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w})).obj
        ((proetaleModuleInverseImage.{u, v, w} g Λ).obj G) ≅
      (Abelian.proetaleInverseImage.{u, max v w} g).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ)
          AddCommGrpCat.{max (u + 1) v w})).obj G) := by
  let bc := Scheme.proetaleBaseChange g
  have := preservesSheafification_forget₂_moduleCat_ofLeftAdjoint.{v, max (u + 1) w} Λ
    (Scheme.ProEt.topology Z)
  have hcolim (W : Z.ProEtᵒᵖ) : PreservesColimitsOfShape (CostructuredArrow bc.op W)
      (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w}) := by
    have : PreservesColimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v w, v, u, u + 1} Λ
    exact @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _ this _ _
  exact (sheafCompose _ _).mapIso ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} Λ g).app
      G) ≪≫
    (bc.sheafPullbackSheafComposeIso (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z) (forget₂ _ AddCommGrpCat.{max (u + 1) v w}) G).symm ≪≫
    ((bc.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v w} (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).leftAdjointUniq
        (Abelian.proetaleInverseImageDirectImageAdj.{u, max v w} g)).app _

end AlgebraicGeometry.ProEtale

end
