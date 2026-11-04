module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.CategoryTheory.Adjunction.UnitTransposeCocycle

/-!
# Associativity of the composition comparison of direct images of graded algebras

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces the direct images of sheaves of
graded algebras along the morphisms of small étale ringed topoi of Stacks 03G8 are compared by
`AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso`, `f_* ∘ g_* ≅ (f ≫ g)_*`.  This file
proves that the comparison obeys the associativity cocycle law for three composable morphisms.
It is the coherence from which the associativity of the multiplicative composition comparison of
pullbacks, `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`, follows by the calculus of
mates, since that comparison is the comparison of left adjoints induced by this one.

## Main results

* `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso_hom_app_app`: the degreewise
  components of the comparison are those of the comparison of direct images of sheaves of
  modules at the morphisms of ringed topoi, `AlgebraicGeometry.Space.pushforwardModulesCompAt`.
* `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso_assoc`: **the associativity cocycle
  law**.

## Implementation notes

A morphism of sheaves of graded algebras is determined by its degreewise components, and the
direct image of sheaves of graded algebras acts degreewise as the direct image of sheaves of
modules, so the cocycle law is the cocycle law
`AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc` in each degree.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X Y Z : AlgebraicSpaces B S hS}

/-- The degreewise components of the comparison of direct images of sheaves of graded algebras are
the components of the comparison of direct images of sheaves of modules. -/
theorem gradedAlgebraPushforwardCompIso_hom_app_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    ((gradedAlgebraPushforwardCompIso B S hS f g).hom.app A).app n =
      (pushforwardModulesCompAt B S hS f g).hom.app (A.piece n) :=
  rfl

/-- **Associativity of the comparison of direct images of sheaves of graded algebras**: for three
composable morphisms the two ways of comparing `f_* ∘ g_* ∘ h_*` with `(f ≫ g ≫ h)_*` agree. -/
theorem gradedAlgebraPushforwardCompIso_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (gradedPush (X := smallEtaleRingedTopos B S hS W)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS f))
        (gradedAlgebraPushforwardCompIso B S hS g h) ≪≫
      gradedAlgebraPushforwardCompIso B S hS f (g ≫ h) =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (gradedAlgebraPushforwardCompIso B S hS f g)
        (gradedPush (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS h)) ≪≫
      gradedAlgebraPushforwardCompIso B S hS (f ≫ g) h :=
  Iso.ext (NatTrans.ext (funext fun A => SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (pushforwardModulesCompAt_assoc B S hS f g h (A.piece n)).symm))

/-! ### The restriction maps of the pulled-back algebras -/

variable {B S hS} {P P' P'' : AlgebraicSpaces B S hS}

/-- **The restriction map of pulled-back graded algebras along a morphism over `X`.**  For
`f : P ⟶ X`, `f' : P' ⟶ X` and `φ : P' ⟶ P` with `φ ≫ f = f'`, the morphism
`f^*𝒜 ⟶ φ_*(f'^*𝒜)` adjoint to the unit `𝒜 ⟶ f'_* f'^*𝒜` read through the comparison
`f_* ∘ φ_* ≅ (φ ≫ f)_*` of direct images. -/
noncomputable def gradedPullRestriction (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    (gradedPull (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).obj A ⟶
      (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
        (smallEtaleRingedToposHom B S hS φ)).obj
        ((gradedPull (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS f')).obj A) := by
  subst h
  exact Adjunction.unitTranspose
    (gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS f))
    (gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS (φ ≫ f)))
    _ (gradedAlgebraPushforwardCompIso B S hS φ f) A

/-- **The cocycle law of the restriction maps.**  Restricting along `ψ ≫ φ` is restricting along
`φ` and then along `ψ`, read through the comparison of direct images. -/
theorem gradedPullRestriction_comp (ψ : P'' ⟶ P') (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (f'' : P'' ⟶ X) (h : φ ≫ f = f') (h' : ψ ≫ f' = f'') (h'' : (ψ ≫ φ) ≫ f = f'')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    gradedPullRestriction (ψ ≫ φ) f f'' h'' A ≫
        (gradedAlgebraPushforwardCompIso B S hS ψ φ).inv.app _ =
      gradedPullRestriction φ f f' h A ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
          (smallEtaleRingedToposHom B S hS φ)).map (gradedPullRestriction ψ f' f'' h' A) := by
  subst h h'
  exact Adjunction.unitTranspose_comp _ _ _ _ _ _ _ _ _ _
    (gradedAlgebraPushforwardCompIso_assoc B S hS ψ φ f) A

/-- The unit of the graded adjunction is degreewise the unit of the module adjunction. -/
theorem gradedAdj_unit_app_app {P P' : AlgebraicSpaces B S hS} (φ : P' ⟶ P)
    (E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS P).O)) (n : ℤ) :
    ((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).unit.app E).app n =
      (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.unit.app
        (E.piece n) := rfl

/-- The direct image of a homomorphism of graded algebras is degreewise the direct image of
sheaves of modules. -/
theorem gradedPush_map_app {P P' : AlgebraicSpaces B S hS} (φ : P' ⟶ P)
    {E E' : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS P').O)}
    (g : E ⟶ E') (n : ℤ) :
    ((gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ)).map g).app n =
      (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map (g.app n) := rfl

/-- The transpose along the graded adjunction is degreewise the transpose along the module
adjunction. -/
theorem gradedAdj_homEquiv_symm_app {P P' : AlgebraicSpaces B S hS} (φ : P' ⟶ P)
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS P).O)}
    {E' : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS P').O)}
    (r : E ⟶ (gradedPush (X := smallEtaleRingedTopos B S hS P')
      (Y := smallEtaleRingedTopos B S hS P) (smallEtaleRingedToposHom B S hS φ)).obj E') (n : ℤ) :
    ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.homEquiv
        _ _).symm (r.app n) =
      (((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
        (smallEtaleRingedToposHom B S hS φ)).homEquiv _ _).symm r).app n := by
  let g := ((gradedAdj (X := smallEtaleRingedTopos B S hS P')
    (Y := smallEtaleRingedTopos B S hS P) (smallEtaleRingedToposHom B S hS φ)).homEquiv E E').symm r
  have h₁ : r = (gradedAdj (X := smallEtaleRingedTopos B S hS P')
      (Y := smallEtaleRingedTopos B S hS P) (smallEtaleRingedToposHom B S hS φ)).unit.app E ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
          (smallEtaleRingedToposHom B S hS φ)).map g :=
    (Equiv.apply_symm_apply _ r).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine Eq.trans ?_ ((smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison
    |>.homEquiv_unit (E.piece n) (E'.piece n) (g.app n)).symm
  exact (congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) h₁).trans
    (congrArg₂ (· ≫ ·) (gradedAdj_unit_app_app φ E n) (gradedPush_map_app φ g n))

/-- A component of an isomorphism of sheaves of graded algebras is an isomorphism. -/
instance _root_.SheafOfModules.GradedAlgebra.isIso_hom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A A' : SheafOfModules.GradedAlgebra.{u, u} R} (e : A ≅ A') (n : ℤ) : IsIso (e.hom.app n) :=
  ⟨⟨e.inv.app n, congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) e.hom_inv_id,
    congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) e.inv_hom_id⟩⟩

/-- At the composite itself, the restriction map is the transposed unit. -/
theorem gradedPullRestriction_comp_rfl (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    gradedPullRestriction φ f (φ ≫ f) rfl A = Adjunction.unitTranspose
      (gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f))
      (gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (φ ≫ f)))
      _ (gradedAlgebraPushforwardCompIso B S hS φ f) A := rfl

/-- **The transpose of the restriction map is the comparison of pullbacks**, hence invertible in
every degree. -/
theorem isIso_gradedPullRestriction_transpose_app (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (n : ℤ) :
    IsIso ((((gradedAdj (X := smallEtaleRingedTopos B S hS P')
      (Y := smallEtaleRingedTopos B S hS P) (smallEtaleRingedToposHom B S hS φ)).homEquiv _ _).symm
        (gradedPullRestriction φ f f' h A)).app n) := by
  subst h
  have e := Adjunction.homEquiv_symm_unitTranspose
    (gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS f))
    (gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS (φ ≫ f)))
    (gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
      (smallEtaleRingedToposHom B S hS φ))
    (gradedAlgebraPushforwardCompIso B S hS φ f) A
  rw [← gradedPullRestriction_comp_rfl] at e
  rw [e]
  exact SheafOfModules.GradedAlgebra.isIso_hom_app
    (Iso.app (Adjunction.leftAdjointCompIso _ _ _ (gradedAlgebraPushforwardCompIso B S hS φ f)) A) n

/-- The adjunction between inverse and direct images of sheaves of modules along the morphism of
small étale ringed topoi of a morphism of algebraic spaces. -/
noncomputable abbrev etaleModuleAdjunction (φ : P' ⟶ P) :=
  (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison

/-- The restriction map in one degree, as a morphism of sheaves of modules into the direct image
of the piece. -/
noncomputable def gradedPullRestrictionApp (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (n : ℤ) :
    ((gradedPull (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).obj A).piece n ⟶
      (smallEtaleRingedToposHom B S hS φ).pushforwardModules.obj
        (((gradedPull (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS f')).obj A).piece n) :=
  (gradedPullRestriction φ f f' h A).app n

/-- **The transpose of the restriction map along the module adjunction is invertible in every
degree**: it is the comparison `φ^*(f^*𝒜_n) ⟶ f'^*𝒜_n` of inverse images. -/
theorem isIso_homEquiv_symm_gradedPullRestrictionApp (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (n : ℤ) :
    IsIso (((etaleModuleAdjunction φ).homEquiv _ _).symm (gradedPullRestrictionApp φ f f' h A n)) :=
  (congrArg IsIso (gradedAdj_homEquiv_symm_app φ (gradedPullRestriction φ f f' h A) n)).mpr
    (isIso_gradedPullRestriction_transpose_app φ f f' h A n)

end AlgebraicGeometry.Space
