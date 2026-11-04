module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantExtensionHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# The derived extension of scalars is left adjoint to the derived global sections

Let `C` be a small category with the chaotic topology, `R` a commutative ring and `B` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. Suppose that
extension of scalars `K ↦ K ⊗_R B` carries quasi-isomorphisms of complexes of `R`-modules to
quasi-isomorphisms of right differential graded `B`-modules. Then it descends to a functor
`F' : D(R) ⥤ D(B, d)` on the derived categories, which is its own left derived functor, and
`F'` is left adjoint to the derived global sections `G' = RΓ : D(B, d) ⥤ D(R)`. This is the
adjunction `Lf^* ⊣ Rf_*` of the proof of Proposition 0GZK.

## Main definitions

* `Stacks.ChaoticSite.derivedExtend`: the functor `F' : D(R) ⥤ D(B, d)` induced by extension of
  scalars.
* `Stacks.ChaoticSite.derivedExtendAdjunction`: **the adjunction `F' ⊣ RΓ`**, obtained from the
  adjunction of homotopy categories by deriving.

## Main results

* `Stacks.ChaoticSite.derivedExtendAdjunction_unit_fac`: the unit of the derived adjunction on
  the class of a complex `K` is the class of the unit `K ⟶ Γ(K ⊗_R B)` followed by the comparison
  map of the derived global sections.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Stacks.PresheafOfModules

universe u

namespace Stacks.ChaoticSite

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]
  (B : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R))

/-- The hypothesis that extension of scalars inverts the quasi-isomorphisms of the homotopy
category of complexes of `R`-modules, after localization. -/
def ExtendInvertsQuasiIso : Prop :=
  (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
    (homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B)

variable {B}

/-- **The derived extension of scalars** `F' : D(R) ⥤ D(B, d)`. -/
def derivedExtend (hB : ExtendInvertsQuasiIso B) :
    DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory.{u, u, u} B :=
  Localization.lift _ hB DerivedCategory.Qh

/-- The derived extension of scalars on the class of a complex. -/
def derivedExtendFac (hB : ExtendInvertsQuasiIso B) :
    DerivedCategory.Qh ⋙ derivedExtend hB ≅ homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B :=
  Localization.fac _ hB DerivedCategory.Qh

/-- The derived extension of scalars is the left derived functor, with respect to the
quasi-isomorphisms, of extension of scalars followed by the localization to `D(B, d)`. -/
instance (hB : ExtendInvertsQuasiIso B) :
    (derivedExtend hB).IsLeftDerivedFunctor (derivedExtendFac hB).hom
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ _

variable (B) in
/-- The comparison map of the derived global sections, with its source written as the global
sections on the homotopy category followed by the localization. -/
def globalUnit : homotopyGlobalSections R B ⋙ DerivedCategory.Qh ⟶
    toDerivedCategory.{u, u, u} B ⋙ derivedGlobalSections R B :=
  derivedGlobalSectionsUnit R B

/-- The derived global sections are the right derived functor of the global sections on the
homotopy category, via `globalUnit`. -/
instance : (derivedGlobalSections R B).IsRightDerivedFunctor (globalUnit B)
    (quasiIsomorphisms.{u, u, u} B) :=
  isRightDerivedFunctor_derivedGlobalSections R B

/-- The composite `RΓ ∘ F'` is the left derived functor of `RΓ` precomposed with extension of
scalars. -/
instance (hB : ExtendInvertsQuasiIso B) :
    (derivedExtend hB ⋙ derivedGlobalSections R B).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (derivedExtendFac hB).hom
        (derivedGlobalSections R B))
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (asIso ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (derivedExtendFac hB).hom
      (derivedGlobalSections R B)))

/-- The composite `F' ∘ RΓ` is the right derived functor of the global sections on the homotopy
category followed by `F'`. -/
instance (hB : ExtendInvertsQuasiIso B) :
    (derivedGlobalSections R B ⋙ derivedExtend hB).IsRightDerivedFunctor
      (Functor.whiskerRight (globalUnit B) (derivedExtend hB) ≫ (Functor.associator _ _ _).hom)
      (quasiIsomorphisms.{u, u, u} B) := by
  refine Functor.isRightDerivedFunctor_of_coresolutions
    (L := toDerivedCategory.{u, u, u} B) (quasiIsomorphisms.{u, u, u} B) _
    (fun Z => IsKInjective Z.as ∧ GradedInjective Z.as)
    (exists_quasiIso_isDGInjective (X := constRingedSite C R) B)
    (fun I hI Y => bijective_toDerivedCategory_map
      (hasKInjectiveResolutions_dg.{u, u, u} (X := constRingedSite C R) B) Y hI.1 hI.2)
    fun I hI => ?_
  have h : IsIso ((globalUnit B).app I) :=
    isIso_derivedGlobalSectionsUnit_app R B (I := I.as) ⟨hI.2, hI.1⟩
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  exact Functor.map_isIso _ _

/-- **The derived extension of scalars is left adjoint to the derived global sections.** -/
def derivedExtendAdjunction (hB : ExtendInvertsQuasiIso B) :
    derivedExtend hB ⊣ derivedGlobalSections R B :=
  (homotopyExtendAdjunction B).derived
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (quasiIsomorphisms.{u, u, u} B) (derivedExtendFac hB).hom (globalUnit B)

/-- **The unit of the derived adjunction on the class of a complex** `K` is the class of the unit
`K ⟶ Γ(K ⊗_R B)` followed by the comparison map of the derived global sections. -/
theorem derivedExtendAdjunction_unit_fac (hB : ExtendInvertsQuasiIso B)
    (K : _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :
    (derivedExtendAdjunction hB).unit.app (DerivedCategory.Qh.obj K) ≫
        (derivedGlobalSections R B).map ((derivedExtendFac hB).hom.app K) =
      DerivedCategory.Qh.map ((homotopyExtendAdjunction B).unit.app K) ≫
        (globalUnit B).app ((homotopyExtend' B).obj K) :=
  Adjunction.derivedη_fac_app (homotopyExtendAdjunction B)
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (derivedExtendFac hB).hom (globalUnit B) K

end Stacks.ChaoticSite

end
