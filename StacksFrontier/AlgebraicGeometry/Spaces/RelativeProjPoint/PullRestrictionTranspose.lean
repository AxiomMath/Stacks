module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence

/-!
# The transposed restriction map of a pulled-back graded algebra is the comparison of Stacks 03LU

For morphisms `φ : P' ⟶ P` and `f : P ⟶ X` of algebraic spaces and `f' = φ ≫ f`, the restriction
map `f^*𝒜 ⟶ φ_*(f'^*𝒜)` of pulled-back graded algebras
(`AlgebraicGeometry.Space.gradedPullRestriction`) is, in each degree, adjoint along `φ^* ⊣ φ_*` to
a morphism `φ^*(f^*𝒜_n) ⟶ f'^*𝒜_n`.  This file identifies that morphism: **it is the composition
comparison `φ^* ∘ f^* ≅ (φ ≫ f)^*` of inverse images of Stacks 03LU**
(`AlgebraicGeometry.Space.modulePullbackCompIso`), followed by the transport along `φ ≫ f = f'`.

Both are comparisons of left adjoints induced by comparisons of direct images: the transposed
restriction map by the comparison `AlgebraicGeometry.Space.pushforwardModulesCompAt` of the direct
images of the morphisms of small étale ringed topoi, and the comparison of Stacks 03LU by
`AlgebraicGeometry.Space.modulePushforwardCompIso`, which is the former transported along the
equalities `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`.  The abstract fact
used is that a comparison of left adjoints does not change when the right adjoints are retyped
along equalities of functors
(`CategoryTheory.Adjunction.leftAdjointCompIso_ofNatIsoRight_eqToIso`).

## Main results

* `CategoryTheory.Adjunction.leftAdjointCompIso_ofNatIsoRight_eqToIso`: the abstract fact.
* `AlgebraicGeometry.Space.homEquiv_symm_gradedPullRestrictionApp`: **the transposed restriction
  map is the comparison of Stacks 03LU followed by the transport.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- **A comparison of left adjoints is unchanged by retyping the right adjoints along equalities
of functors**, the comparison of right adjoints being transported along the same equalities. -/
theorem leftAdjointCompIso_ofNatIsoRight_eqToIso {L₁ : C₀ ⥤ C₁} {R₁ R₁' : C₁ ⥤ C₀}
    {L₂ : C₁ ⥤ C₂} {R₂ R₂' : C₂ ⥤ C₁} {L₃ : C₀ ⥤ C₂} {R₃ R₃' : C₂ ⥤ C₀} (a₁ : L₁ ⊣ R₁)
    (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (h₁ : R₁ = R₁') (h₂ : R₂ = R₂') (h₃ : R₃ = R₃')
    (e : R₂ ⋙ R₁ ≅ R₃) :
    leftAdjointCompIso (a₁.ofNatIsoRight (eqToIso h₁)) (a₂.ofNatIsoRight (eqToIso h₂))
        (a₃.ofNatIsoRight (eqToIso h₃)) (Functor.compIsoCongr h₂ h₁ h₃ e) =
      leftAdjointCompIso a₁ a₂ a₃ e := by
  subst h₁ h₂ h₃
  have hr : ∀ {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R), a.ofNatIsoRight (eqToIso rfl) = a :=
    fun a => Adjunction.ext (NatTrans.ext (funext fun X => by simp [Adjunction.ofNatIsoRight]))
  have hr' : ∀ {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (a : L ⊣ R), a.ofNatIsoRight (eqToIso rfl) = a :=
    fun a => Adjunction.ext (NatTrans.ext (funext fun X => by simp [Adjunction.ofNatIsoRight]))
  have hr'' : ∀ {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (a : L ⊣ R), a.ofNatIsoRight (eqToIso rfl) = a :=
    fun a => Adjunction.ext (NatTrans.ext (funext fun X => by simp [Adjunction.ofNatIsoRight]))
  have he : Functor.compIsoCongr (rfl : R₂ = R₂) (rfl : R₁ = R₁) (rfl : R₃ = R₃) e = e :=
    Iso.ext (by simp [Functor.compIsoCongr])
  rw [hr, hr', hr'', he]

/-- `CategoryTheory.Adjunction.homEquiv_symm_unitTranspose` with the transposed unit written
out. -/
theorem homEquiv_symm_homEquiv_symm_unit_comp {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₀ ⥤ C₂}
    {R' : C₂ ⥤ C₀} {LM : C₁ ⥤ C₂} {M : C₂ ⥤ C₁} (a : L ⊣ R) (a' : L' ⊣ R') (aM : LM ⊣ M)
    (e : M ⋙ R ≅ R') (A : C₀) :
    (aM.homEquiv _ _).symm ((a.homEquiv _ _).symm (a'.unit.app A ≫ e.inv.app _)) =
      (leftAdjointCompIso a aM a' e).hom.app A :=
  homEquiv_symm_unitTranspose a a' aM e A

end CategoryTheory.Adjunction

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P P' : AlgebraicSpaces B S hS}

/-- The inverse-image adjunction of Stacks 03LU is the adjunction of the morphism of small étale
ringed topoi with its right adjoint retyped along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`. -/
theorem modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight (f : P ⟶ X) :
    modulePullbackAdjunction B S hS f =
      (etaleModuleAdjunction f).ofNatIsoRight
        (eqToIso (pushforwardModules_eq_modulePushforward B S hS f)) :=
  (Adjunction.ofNatIsoRight_trans _ _ _).symm.trans
    (congrArg (fun i => (etaleModuleAdjunction f).ofNatIsoRight i)
      (pushforwardModulesIsoModulePushforward_eq_eqToIso B S hS f))

/-- **The comparison `φ^* ∘ f^* ≅ (φ ≫ f)^*` of Stacks 03LU is the comparison of left adjoints
induced by the comparison of direct images of the morphisms of small étale ringed topoi.** -/
theorem modulePullbackCompIso_eq_leftAdjointCompIso_etale (φ : P' ⟶ P) (f : P ⟶ X) :
    modulePullbackCompIso B S hS φ f =
      Adjunction.leftAdjointCompIso (etaleModuleAdjunction f) (etaleModuleAdjunction φ)
        (etaleModuleAdjunction (φ ≫ f)) (pushforwardModulesCompAt B S hS φ f) := by
  rw [modulePullbackCompIso_eq_leftAdjointCompIso,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePushforwardCompIso_eq_compIsoCongr]
  exact Adjunction.leftAdjointCompIso_ofNatIsoRight_eqToIso _ _ _ _ _ _ _

/-- The degreewise components of the inverse of the comparison of direct images of sheaves of
graded algebras are those of the comparison of direct images of sheaves of modules. -/
theorem gradedAlgebraPushforwardCompIso_inv_app_app (φ : P' ⟶ P) (f : P ⟶ X)
    (E : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS P')) (n : ℤ) :
    ((gradedAlgebraPushforwardCompIso B S hS φ f).inv.app E).app n =
      (pushforwardModulesCompAt B S hS φ f).inv.app (E.piece n) := by
  refine (cancel_mono ((pushforwardModulesCompAt B S hS φ f).hom.app _)).1 ?_
  refine Eq.trans ?_ (Iso.inv_hom_id_app (pushforwardModulesCompAt B S hS φ f) _).symm
  exact congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n)
    ((gradedAlgebraPushforwardCompIso B S hS φ f).inv_hom_id_app E)

/-- The unit of the graded adjunction of the composite, read through the comparison of direct
images, is degreewise the unit of the module adjunction read through the comparison of direct
images of modules. -/
theorem gradedAdj_unit_comp_gradedAlgebraPushforwardCompIso_inv_app (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    ((gradedAdj (X := smallEtaleRingedTopos B S hS P')
        (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (φ ≫ f))).unit.app A ≫
      (gradedAlgebraPushforwardCompIso B S hS φ f).inv.app
        ((gradedPull (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A)).app n =
      (etaleModuleAdjunction (φ ≫ f)).unit.app (A.piece n) ≫
        (pushforwardModulesCompAt B S hS φ f).inv.app _ :=
  (SheafOfModules.GradedAlgebra.categoryStruct_comp_app _ _ n).trans
    (congrArg₂ (· ≫ ·) (gradedAdj_unit_app_app (φ ≫ f) A n)
      (gradedAlgebraPushforwardCompIso_inv_app_app φ f _ n))

/-- At the composite itself, the restriction map in one degree is the transposed unit of the
module adjunctions. -/
theorem gradedPullRestrictionApp_comp_rfl (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    gradedPullRestrictionApp φ f (φ ≫ f) rfl A n =
      ((etaleModuleAdjunction f).homEquiv (A.piece n)
        ((smallEtaleRingedToposHom B S hS φ).pushforwardModules.obj
          (((gradedPull (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A).piece n))).symm
        ((etaleModuleAdjunction (φ ≫ f)).unit.app (A.piece n) ≫
          (pushforwardModulesCompAt B S hS φ f).inv.app _) := by
  have e1 : gradedPullRestrictionApp φ f (φ ≫ f) rfl A n =
      SheafOfModules.GradedAlgebra.Hom.app (gradedPullRestriction φ f (φ ≫ f) rfl A) n := rfl
  have e2 : SheafOfModules.GradedAlgebra.Hom.app (gradedPullRestriction φ f (φ ≫ f) rfl A) n =
      SheafOfModules.GradedAlgebra.Hom.app (((gradedAdj (X := smallEtaleRingedTopos B S hS P)
        (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).homEquiv _ _).symm
          ((gradedAdj (X := smallEtaleRingedTopos B S hS P')
        (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (φ ≫ f))).unit.app A ≫
      (gradedAlgebraPushforwardCompIso B S hS φ f).inv.app
        ((gradedPull (X := smallEtaleRingedTopos B S hS P')
            (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A))) n :=
    congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n)
      (gradedPullRestriction_comp_rfl φ f A)
  have e3 := gradedAdj_homEquiv_symm_app (B := B) (S := S) (hS := hS) f (E := A)
    (E' := (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).obj ((gradedPull (X := smallEtaleRingedTopos B S hS P')
            (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A))
    ((gradedAdj (X := smallEtaleRingedTopos B S hS P')
        (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (φ ≫ f))).unit.app A ≫
      (gradedAlgebraPushforwardCompIso B S hS φ f).inv.app
        ((gradedPull (X := smallEtaleRingedTopos B S hS P')
            (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A)) n
  have e4 := congrArg ((etaleModuleAdjunction f).homEquiv (A.piece n)
      ((smallEtaleRingedToposHom B S hS φ).pushforwardModules.obj
        (((gradedPull (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS (φ ≫ f))).obj A).piece n))).symm
      (gradedAdj_unit_comp_gradedAlgebraPushforwardCompIso_inv_app φ f A n)
  exact e1.trans (e2.trans (e3.symm.trans e4))

/-- **The transpose of the restriction map of pulled-back graded algebras along `φ^* ⊣ φ_*` is the
composition comparison of Stacks 03LU**, followed by the transport along `φ ≫ f = f'`. -/
theorem homEquiv_symm_gradedPullRestrictionApp (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (n : ℤ) :
    ((etaleModuleAdjunction φ).homEquiv _ _).symm (gradedPullRestrictionApp φ f f' h A n) =
      (modulePullbackCompIso B S hS φ f).hom.app (A.piece n) ≫
        pullbackTransport (A.piece n) h := by
  subst h
  refine (congrArg ((etaleModuleAdjunction φ).homEquiv _ _).symm
    (gradedPullRestrictionApp_comp_rfl φ f A n)).trans ?_
  refine (Adjunction.homEquiv_symm_homEquiv_symm_unit_comp (etaleModuleAdjunction f)
    (etaleModuleAdjunction (φ ≫ f)) (etaleModuleAdjunction φ)
    (pushforwardModulesCompAt B S hS φ f) (A.piece n)).trans ?_
  rw [modulePullbackCompIso_eq_leftAdjointCompIso_etale]
  exact (Category.comp_id _).symm

end AlgebraicGeometry.Space

end
