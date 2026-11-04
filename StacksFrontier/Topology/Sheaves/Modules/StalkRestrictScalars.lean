module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Restriction of scalars does not change the stalk of a sheaf of modules

Let `X` be a topological space and `α : O ⟶ O'` a morphism of sheaves of rings on `X`. A sheaf of
`O'`-modules `N` is read as a sheaf of `O`-modules by `SheafOfModules.restrictScalars α`, and this
does not change the underlying sheaf of abelian groups. Consequently the stalk at `x` of
`(restrictScalars α).obj N` is the stalk of `N`, as an `O_x`-module read through the induced map
`O_x ⟶ O'_x` of stalk rings.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsHom` and
  `AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsIso`: the comparison map and
  isomorphism between the stalk of a restriction of scalars and the restriction of scalars of the
  stalk, objectwise.
* `AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`: the same
  isomorphism, as an isomorphism of functors
  `SheafOfModules O' ⥤ ModuleCat O_x`.

## Implementation notes

The comparison map is the identity on underlying abelian groups: `restrictScalars` leaves the
underlying presheaf of abelian groups untouched
(`PresheafOfModules.restrictScalarsCompToPresheaf` is `Iso.refl`), so both stalk modules have the
same carrier. All that has to be said is that the two scalar actions correspond, which is
`SemilinearStalk.restrictScalars_stalk_smul`.

The single universe `u` carries the space, the rings and the module sections together, as
everywhere in the stalk API for sheaves of modules on a space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  {O O' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (α : O ⟶ O') (x : X)

/-- **The comparison map from the stalk of a restriction of scalars to the restriction of scalars
of the stalk.** It is the identity on underlying abelian groups. -/
def stalkFunctorRestrictScalarsHom (N : _root_.SheafOfModules.{u} O') :
    (stalkFunctor O x).obj ((_root_.SheafOfModules.restrictScalars α).obj N) ⟶
      (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap α.hom x).hom).obj ((stalkFunctor O' x).obj N) :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => SemilinearStalk.restrictScalars_stalk_smul α.hom N.val x r m }

/-- On underlying abelian groups the comparison map is the identity. -/
theorem forget₂_map_stalkFunctorRestrictScalarsHom (N : _root_.SheafOfModules.{u} O') :
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
        AddCommGrpCat.{u}).map (stalkFunctorRestrictScalarsHom α x N) = 𝟙 _ := by
  ext m
  rfl

/-- The comparison map `stalkFunctorRestrictScalarsHom` is an isomorphism, since it is the identity
on underlying abelian groups. -/
instance isIso_stalkFunctorRestrictScalarsHom (N : _root_.SheafOfModules.{u} O') :
    IsIso (stalkFunctorRestrictScalarsHom α x N) := by
  rw [← isIso_iff_of_reflects_iso _
      (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
        AddCommGrpCat.{u}), forget₂_map_stalkFunctorRestrictScalarsHom]
  exact IsIso.id _

/-- **The stalk of a restriction of scalars is the restriction of scalars of the stalk.** -/
def stalkFunctorRestrictScalarsIso (N : _root_.SheafOfModules.{u} O') :
    (stalkFunctor O x).obj ((_root_.SheafOfModules.restrictScalars α).obj N) ≅
      (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap α.hom x).hom).obj ((stalkFunctor O' x).obj N) :=
  asIso (stalkFunctorRestrictScalarsHom α x N)

/-- On underlying abelian groups the stalk of a morphism of sheaves of modules does not see a
restriction of scalars. -/
theorem forget₂_map_stalkFunctor_map_restrictScalars_map
    {N N' : _root_.SheafOfModules.{u} O'} (f : N ⟶ N') :
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
          AddCommGrpCat.{u}).map
        ((stalkFunctor O x).map ((_root_.SheafOfModules.restrictScalars α).map f)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf O'.obj).map f.val) := by
  ext m
  rfl

/-- **The stalk of a restriction of scalars is the restriction of scalars of the stalk, naturally
in the sheaf of modules.** -/
def stalkFunctorRestrictScalarsFunctorIso :
    _root_.SheafOfModules.restrictScalars.{u} α ⋙ stalkFunctor O x ≅
      stalkFunctor O' x ⋙
        ModuleCat.restrictScalars.{u} (SemilinearStalk.ringStalkMap α.hom x).hom :=
  NatIso.ofComponents (stalkFunctorRestrictScalarsIso α x) fun {N N'} f => by
    apply (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
      AddCommGrpCat.{u}).map_injective
    simp only [Functor.comp_map, Functor.map_comp, stalkFunctorRestrictScalarsIso, asIso_hom,
      forget₂_map_stalkFunctorRestrictScalarsHom,
      forget₂_map_stalkFunctor_map_restrictScalars_map]
    rfl

end AlgebraicGeometry.SheafOfModules

end
