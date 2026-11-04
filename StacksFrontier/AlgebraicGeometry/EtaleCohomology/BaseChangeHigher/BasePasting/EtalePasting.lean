module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.AbstractPasting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pasting law for the bounded below derived étale base change comparison

Inverse image of abelian sheaves on a small étale site is exact, so
`Stacks.Cohomology.BaseChange.derived_paste` applies to two commutative squares of schemes
stacked along the base.  This file identifies
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` with the abstract descent, constructs the
composition isomorphisms `(f')⁻¹ ∘ (f'')⁻¹ ≅ (f'' ∘ f')⁻¹` and
`R(f'' ∘ f')⁻¹ ≅ R(f')⁻¹ ⋙ R(f'')⁻¹`, and states the resulting pasting law and its two out of
three consequences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.BaseChange

variable {X' X'' S T Y Y'' : Scheme.{u}}

/-- **The bounded below derived étale base change comparison is the abstract descent of its
underived comparison** along the derived-functor unit of `R(f')⁻¹`, inverse image of abelian
sheaves on the small étale sites being exact. -/
public theorem smallEtaleDerivedBaseChangeAb_eq (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X')
    (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) :
    smallEtaleDerivedBaseChangeAb f' g h e w =
      derived (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        (smallEtalePullbackAb f') (smallEtalePullbackAb e) (smallEtaleBaseChangeAb f' g h e w)
        (exactUnitIso (smallEtalePullbackAb f')) := rfl

/-- **The bounded below derived étale base change comparison at a bounded below complex.** Its
composite with the derived-functor unit of `Rg_*` is the degreewise base change map followed by
the derived-functor units of `Rh_*` and of `Re⁻¹`, read through the comparison identifying
`R(f')⁻¹` with the degreewise inverse image.  This determines the comparison. -/
public theorem smallEtaleDerivedBaseChangeAb_fac_app (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X')
    (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)
    (K : HomotopyCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1})) :
    (smallEtalePullbackAb f').rightDerivedFunctorPlus.map
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlusUnit.app K) ≫
        (smallEtaleDerivedBaseChangeAb f' g h e w).app
          (DerivedCategory.Plus.Qh.obj K) =
      (exactUnitIso (smallEtalePullbackAb f')).inv.app
          ((smallEtalePushforwardAb g).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((mapPlus (smallEtaleBaseChangeAb f' g h e w)).app K) ≫
        (smallEtalePushforwardAb h).rightDerivedFunctorPlusUnit.app
          ((smallEtalePullbackAb e).mapHomotopyCategoryPlus.obj K) ≫
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
          ((smallEtalePullbackAb e).rightDerivedFunctorPlusUnit.app K) := by
  rw [smallEtaleDerivedBaseChangeAb_eq, derived_fac_app, onHomotopy_app]

/-- **The composition isomorphism `R(f'' ∘ f')⁻¹ ≅ R(f')⁻¹ ⋙ R(f'')⁻¹`** for inverse image of
abelian sheaves on the small étale sites: both inverse images are exact, so every object is
acyclic and the canonical comparison of [Stacks, Tag 05T2] is invertible. -/
public def smallEtaleDerivedPullbackCompIso (f' : X' ⟶ S) (f'' : X'' ⟶ X') :
    (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'').rightDerivedFunctorPlus ≅
      (smallEtalePullbackAb f').rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb f'').rightDerivedFunctorPlus :=
  exactDerivedCompIso (smallEtalePullbackAb f') (smallEtalePullbackAb f'')

/-- **The derived-functor unit of the composite inverse image factors through
`smallEtaleDerivedPullbackCompIso`.** -/
public theorem smallEtale_unit_eq_comp_derivedPullbackCompIso_inv (f' : X' ⟶ S)
    (f'' : X'' ⟶ X')
    (M : HomotopyCategory.Plus (Sheaf (smallEtaleTopology S) Ab.{u + 1})) :
    iteratedUnit (smallEtalePullbackAb f') (smallEtalePullbackAb f'') M ≫
        (smallEtaleDerivedPullbackCompIso f' f'').inv.app
          (DerivedCategory.Plus.Qh.obj M) =
      (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'').rightDerivedFunctorPlusUnit.app M :=
  unit_eq_comp_exactDerivedCompIso_inv _ _ M

/-- **The composition isomorphism `(f')⁻¹ ∘ (f'')⁻¹ ≅ (f'' ∘ f')⁻¹`** for inverse image of
abelian sheaves on the small étale sites: the isomorphism of left adjoints attached to the
composition isomorphism `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` of the direct
images. -/
@[sga "4 VII 1.4" "partial"]
public def smallEtalePullbackAbTowerCompIso (f'' : X'' ⟶ X') (f' : X' ⟶ S) :
    smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'' ≅
      smallEtalePullbackAb (f'' ≫ f') :=
  Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb f'')
    (smallEtaleAdjunctionAb (f'' ≫ f')) (smallEtalePushforwardAbCompIso f'' f')

/-- **The composition isomorphism `R(f'' ∘ f')⁻¹ ≅ R(f')⁻¹ ⋙ R(f'')⁻¹`**, in the form a
consumer of the pasting law needs: the underived composition isomorphism of the inverse images,
right derived, followed by the composition isomorphism of the right derived functors. -/
public def smallEtaleDerivedPullbackComp (f'' : X'' ⟶ X') (f' : X' ⟶ S) :
    (smallEtalePullbackAb (f'' ≫ f')).rightDerivedFunctorPlus ≅
      (smallEtalePullbackAb f').rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb f'').rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusNatIso (smallEtalePullbackAbTowerCompIso f'' f').symm ≪≫
    smallEtaleDerivedPullbackCompIso f' f''

/-- **Base functoriality of the bounded below derived étale base change comparison.**  For a
commutative square `h ≫ f' = e ≫ g` of schemes and a second one `h'' ≫ f'' = e'' ≫ h` extending
its base along `f''`, the comparison descended from the pasted underived comparison is the
comparison of the first square carried by `R(f'')⁻¹`, followed by the comparison of the second,
read through the composition isomorphisms of the derived inverse images.  This is
`Stacks.Cohomology.BaseChange.derived_paste` at the four inverse images, which are exact. -/
public theorem smallEtaleDerivedBaseChangeAb_paste (f' : X' ⟶ S) (f'' : X'' ⟶ X') (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h) :
    derived (smallEtalePushforwardAb g) (smallEtalePushforwardAb h'')
        (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'')
        (smallEtalePullbackAb e ⋙ smallEtalePullbackAb e'')
        (pasteTrans (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
          (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
          (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
          (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w'))
        (exactUnitIso (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'')) =
      Functor.whiskerLeft (smallEtalePushforwardAb g).rightDerivedFunctorPlus
          (smallEtaleDerivedPullbackCompIso f' f'').hom ≫
        Functor.whiskerRight (smallEtaleDerivedBaseChangeAb f' g h e w)
            (smallEtalePullbackAb f'').rightDerivedFunctorPlus ≫
          Functor.whiskerLeft (smallEtalePullbackAb e).rightDerivedFunctorPlus
              (smallEtaleDerivedBaseChangeAb f'' h h'' e'' w') ≫
            Functor.whiskerRight (smallEtaleDerivedPullbackCompIso e e'').inv
              (smallEtalePushforwardAb h'').rightDerivedFunctorPlus :=
  derived_paste (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
    (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
    (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
    (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w')

/-- **Two out of three for the bounded below derived étale base change comparison.**  If the
comparisons of the two squares are invertible at the relevant objects, so is the comparison
descended from the pasted underived comparison. -/
public theorem isIso_smallEtaleDerivedBaseChangeAb_paste_app (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (X : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (h₁ : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app X))
    (h₂ : IsIso ((smallEtaleDerivedBaseChangeAb f'' h h'' e'' w').app
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj X))) :
    IsIso ((derived (smallEtalePushforwardAb g) (smallEtalePushforwardAb h'')
      (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'')
      (smallEtalePullbackAb e ⋙ smallEtalePullbackAb e'')
      (pasteTrans (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
        (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
        (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w'))
      (exactUnitIso (smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f''))).app X) :=
  isIso_derived_paste_app (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
    (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
    (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
    (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w') X h₁ h₂

/-- **The degree-`q` descent.**  If the bounded below derived base change comparison of a
commutative square of schemes is invertible at an abelian sheaf placed in degree zero, then the
base change map on higher direct images of [Stacks, Tag 0F02] is invertible at that sheaf in
every degree: the latter is the degree-`q` cohomology of the former, read through two
isomorphisms. -/
public theorem isIso_higherBaseChangeMapAb_app_of_isIso_derived (f' : X' ⟶ S) (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)))
    (q : ℕ) : IsIso ((higherBaseChangeMapAb f' g h e w q).app F) := by
  rw [isIso_higherBaseChangeMapAb_app_iff]
  have := hF
  infer_instance

end Stacks.EtaleCohomology

end
