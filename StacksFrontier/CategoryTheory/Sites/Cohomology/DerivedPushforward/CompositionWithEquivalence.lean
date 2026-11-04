module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The derived direct image of a composite with an equivalence

Let `f` and `g` be composable morphisms of ringed topoi. In general the comparison
`R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` is invertible only under an acyclicity hypothesis
([Stacks, Tag 0D6E]). When one of the two is an equivalence on sheaves of modules no hypothesis
is needed: an exact equivalence of abelian categories induces an equivalence of the derived
categories, and a right derived functor stays one after postcomposition with a left adjoint and
after precomposition with an equivalence.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardCompEquivIso`:
  `R(e ∘ f)_* ≅ Rf_* ⋙ D(e_*)` when `e_*` is an equivalence.
* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardEquivCompIso`:
  `R(h ∘ g)_* ≅ D(g_*) ⋙ Rh_*` when `g_*` is an equivalence.
* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardIsoIdOfSelf`: `Rk_* ≅ 𝟭` for an
  endomorphism `k` of a ringed topos whose direct image is identified with the identity.

## Implementation notes

`D(e_*)` is `CategoryTheory.Functor.mapDerivedCategory`, the functor an exact functor induces on
unbounded derived categories, which for an equivalence `e_*` is an equivalence by
`Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory`. Each isomorphism is
`CategoryTheory.Functor.rightDerivedUnique` or `CategoryTheory.Functor.rightDerivedNatIso`,
once the composite on the right is known to be a right derived functor.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.DerivedPushforward

attribute [local instance] HasDerivedCategory.standard

variable {X X' Y Z : RingedTopos.{u, u, u}}

/-- Existence of the unbounded right derived functor of the degreewise direct image, at the
universes of this file. -/
local instance hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy' {A B : RingedTopos.{u, u, u}}
    (h : RingedToposHom A B) :
    (pushforwardOnHomotopy.{u, u, u, u, u, u} h).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J)) A.O))
        (ComplexShape.up ℤ)) :=
  pushforwardOnHomotopy_hasRightDerivedFunctor h

/-- The quasi-isomorphisms of the unbounded homotopy category of sheaves of modules on `A`. -/
abbrev qis (A : RingedTopos.{u, u, u}) :
    MorphismProperty (HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J)) A.O))
      (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J)) A.O))
    (ComplexShape.up ℤ)

/-- The canonical comparison `pushforwardOnHomotopy h ⟶ Qh ⋙ Rh_*`. -/
abbrev derivedPushforwardUnit' {A B : RingedTopos.{u, u, u}} (h : RingedToposHom A B) :
    pushforwardOnHomotopy.{u, u, u, u, u, u} h ⟶
      DerivedCategory.Qh ⋙ derivedPushforward.{u, u, u, u, u, u} h :=
  (pushforwardOnHomotopy.{u, u, u, u, u, u} h).totalRightDerivedUnit DerivedCategory.Qh (qis A)

section Postcomposition

variable (f : RingedToposHom X Y) (e : RingedToposHom Y Z)
  [(RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e).IsEquivalence]

/-- The degreewise direct image along `e ∘ f`, followed by localization, is the degreewise
direct image along `f` followed by localization and by `D(e_*)`. -/
def pushforwardOnHomotopyCompEquivIso :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} e f) ≅
      pushforwardOnHomotopy.{u, u, u, u, u, u} f ⋙
        (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e).mapDerivedCategory :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (RingedToposHom.pushforwardModulesCompIso f e).symm (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- **`R(e ∘ f)_* ≅ Rf_* ⋙ D(e_*)` when the direct image along `e` is an equivalence of sheaves
of modules.** `D(e_*)` is then an equivalence, hence a left adjoint, so `Rf_* ⋙ D(e_*)` is a
right derived functor of degreewise direct image along `f` followed by `D(e_*)`, which is
isomorphic to degreewise direct image along `e ∘ f`. -/
def derivedPushforwardCompEquivIso :
    derivedPushforward.{u, u, u, u, u, u} (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} e f) ≅
      derivedPushforward.{u, u, u, u, u, u} f ⋙
        (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e).mapDerivedCategory :=
  have := Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory
    (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e)
  Functor.rightDerivedNatIso _ _
    (derivedPushforwardUnit' (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} e f))
    (Functor.whiskerRight (derivedPushforwardUnit' f)
        (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} e).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (qis X) (pushforwardOnHomotopyCompEquivIso f e)

end Postcomposition

section Precomposition

variable (g : RingedToposHom X X') (h : RingedToposHom X' Y)
  [(RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).IsEquivalence]

/-- The degreewise direct image along `h ∘ g` is the degreewise direct image along `g` followed
by the degreewise direct image along `h`, followed by localization. -/
def pushforwardOnHomotopyEquivCompIso :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} h g) ≅
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        pushforwardOnHomotopy.{u, u, u, u, u, u} h :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (RingedToposHom.pushforwardModulesCompIso g h).symm (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- The comparison `pushforwardOnHomotopy (h ∘ g) ⟶ Qh ⋙ (D(g_*) ⋙ Rh_*)`, the unit of `Rh_*`
transported along `K(g_*)` and `D(g_*)`. -/
def derivedPushforwardEquivCompUnit :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} h g) ⟶
      DerivedCategory.Qh ⋙
        (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapDerivedCategory ⋙
        derivedPushforward.{u, u, u, u, u, u} h :=
  ((pushforwardOnHomotopyEquivCompIso g h).hom ≫
      Functor.whiskerLeft _ (derivedPushforwardUnit' h) ≫ (Functor.associator _ _ _).inv) ≫
    Functor.whiskerRight
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapDerivedCategoryFactorsh.inv
      (derivedPushforward.{u, u, u, u, u, u} h) ≫
    (Functor.associator _ _ _).hom

/-- `D(g_*) ⋙ Rh_*` is a right derived functor of degreewise direct image along `h ∘ g`, when
`g_*` is an equivalence: precomposition with the equivalences `K(g_*)` and `D(g_*)` preserves
left Kan extensions along the localizations. -/
theorem isRightDerivedFunctor_mapDerivedCategory_comp_derivedPushforward :
    ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapDerivedCategory ⋙
        derivedPushforward.{u, u, u, u, u, u} h).IsRightDerivedFunctor
      (derivedPushforwardEquivCompUnit g h) (qis X) := by
  have := Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory
    (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g)
  have := Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory
    (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g)
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have : (derivedPushforward.{u, u, u, u, u, u} h).IsLeftKanExtension
      (derivedPushforwardUnit' h) := by
    rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ (qis X')]
    infer_instance
  exact Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence
    (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapDerivedCategoryFactorsh
    (derivedPushforwardUnit' h) (pushforwardOnHomotopyEquivCompIso g h) _ rfl

/-- **`R(h ∘ g)_* ≅ D(g_*) ⋙ Rh_*` when the direct image along `g` is an equivalence of sheaves
of modules.** -/
def derivedPushforwardEquivCompIso :
    derivedPushforward.{u, u, u, u, u, u} (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} h g) ≅
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} g).mapDerivedCategory ⋙
        derivedPushforward.{u, u, u, u, u, u} h :=
  have := isRightDerivedFunctor_mapDerivedCategory_comp_derivedPushforward g h
  Functor.rightDerivedUnique _ _
    (derivedPushforwardUnit' (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} h g))
    (derivedPushforwardEquivCompUnit g h) (qis X)

end Precomposition

section Identity

variable (k : RingedToposHom X X) (ε : 𝟭 X.Topos ≅ k.toToposHom.pushforward)
  (he : X.forgetRing.map k.fSharp = ε.hom.app (X.forgetRing.obj X.O))

/-- The degreewise direct image along `k`, followed by localization, is the localization
functor, when the direct image along `k` is identified with the identity. -/
def pushforwardOnHomotopyIsoOfSelf :
    pushforwardOnHomotopy.{u, u, u, u, u, u} k ≅ DerivedCategory.Qh :=
  Functor.isoWhiskerRight
      { hom := NatTrans.mapHomotopyCategory
          (RingedToposHom.pushforwardModulesIsoId k ε he).inv (ComplexShape.up ℤ)
        inv := NatTrans.mapHomotopyCategory
          (RingedToposHom.pushforwardModulesIsoId k ε he).hom (ComplexShape.up ℤ)
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryIdIso _ _) DerivedCategory.Qh ≪≫
    Functor.leftUnitor _

/-- **`Rk_* ≅ 𝟭` for an endomorphism `k` of a ringed topos whose direct image is identified with
the identity**, compatibly with the structure map. The identity of `D(𝒪)` is a right derived
functor of the localization functor, which is degreewise direct image along `k` followed by
localization. -/
def derivedPushforwardIsoIdOfSelf :
    derivedPushforward.{u, u, u, u, u, u} k ≅ 𝟭 _ :=
  have := Functor.isRightDerivedFunctor_of_inverts (qis X) (𝟭 _)
    (Functor.rightUnitor DerivedCategory.Qh ≪≫ (pushforwardOnHomotopyIsoOfSelf k ε he).symm)
  Functor.rightDerivedUnique _ _ (derivedPushforwardUnit' k)
    (Functor.rightUnitor DerivedCategory.Qh ≪≫ (pushforwardOnHomotopyIsoOfSelf k ε he).symm).inv
    (qis X)

end Identity

end Stacks.Cohomology.DerivedPushforward

end
