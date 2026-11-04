module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Injective objects under a change of coefficients

Let `G : A ⥤ D` be a functor which preserves injective objects, for instance the universe lift
`AddCommGrpCat.uliftFunctor` of abelian groups.  This file shows that the universe lift of
abelian groups preserves injective objects, and that an exact, fully faithful functor between
abelian categories which preserves injective objects carries vanishing `Ext` groups to vanishing
`Ext` groups.

The statement that postcomposition with such a `G` preserves injective sheaves on an essentially
small site is `CategoryTheory.sheafCompose_preservesInjectiveObjects`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleCohomologyAbelianComparison.lean`, built on the
small-site case of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleCohomologyFilteredColimits.lean`.

## Main results

* `AddCommGrpCat.uliftFunctor_preservesInjectiveObjects`: the universe lift of abelian groups
  preserves injective objects.
* `CategoryTheory.Functor.ext_eq_zero_of_forall_ext_eq_zero`: an exact, fully faithful functor
  preserving injective objects carries vanishing `Ext` groups to vanishing `Ext` groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

/-- **The universe lift of abelian groups preserves injective objects**: an abelian group is
injective exactly when it is injective as a `ℤ`-module, and the universe lift of modules
preserves injective modules. -/
instance AddCommGrpCat.uliftFunctor_preservesInjectiveObjects :
    AddCommGrpCat.uliftFunctor.{w, u}.PreservesInjectiveObjects where
  injective_obj {M} hM := by
    apply (AddCommGrpCat.injective_as_module_iff _).mp
    have := (AddCommGrpCat.injective_as_module_iff M).mpr hM
    exact (ModuleCat.uliftFunctor.{w, u} ℤ).injective_obj (ModuleCat.of ℤ M)

namespace CategoryTheory

namespace Functor

variable {A : Type*} [Category* A] [Abelian A] {A' : Type*} [Category* A'] [Abelian A']

/-- **Vanishing `Ext` groups are carried along an exact, fully faithful functor preserving
injective objects.**  If `Ext^{n+1}(X, Y)` vanishes then so does `Ext^{n+1}(L X, L Y)`: an
injective resolution of `Y` is carried by `L` to an injective resolution of `L Y`, a cocycle
`L X ⟶ L I^{n+1}` is the image of a cocycle `X ⟶ I^{n+1}` because `L` is fully faithful, and
the coboundary witnessing the vanishing of its class is carried along by `L`. -/
theorem ext_eq_zero_of_forall_ext_eq_zero [HasExt.{w} A] [HasExt.{v} A'] [EnoughInjectives A]
    (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.Full]
    [L.Faithful] [L.PreservesInjectiveObjects] {X Y : A} (n : ℕ)
    (h : ∀ e : Abelian.Ext.{w} X Y (n + 1), e = 0)
    (e : Abelian.Ext.{v} (L.obj X) (L.obj Y) (n + 1)) : e = 0 := by
  let I := injectiveResolution Y
  let I' : InjectiveResolution (L.obj Y) := Stacks.RightDerivedComp.mapOfAcyclic L I
    (fun k hk => L.isZero_rightDerived_of_exact Y k hk)
  obtain ⟨f, hf, rfl⟩ := I'.extMk_surjective e (n + 2) rfl
  obtain ⟨g, rfl⟩ := L.map_surjective (X := X) (Y := I.cocomplex.X (n + 1)) f
  have hg : g ≫ I.cocomplex.d (n + 1) (n + 2) = 0 :=
    L.map_injective (by rwa [L.map_comp, L.map_zero])
  obtain ⟨b, hb⟩ := (I.extMk_eq_zero_iff g (n + 2) rfl hg n rfl).mp (h _)
  rw [I'.extMk_eq_zero_iff _ (n + 2) rfl hf n rfl]
  exact ⟨L.map b, by rw [← hb, L.map_comp]; rfl⟩

end Functor

end CategoryTheory
