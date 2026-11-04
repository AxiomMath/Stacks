module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.CategoryTheory.Adjunction.MateTransportedAdjunctions

/-!
# The conjugate of the composite of the compositor and a 2-isomorphism of pullbacks

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi with a 2-isomorphism
`t : g ∘ f ≅ h`.  The identification `g^* ⋙ f^* ≅ h^*` of pullbacks of sheaves of modules built
from the compositor of Stacks 03D6 and the 2-isomorphism `t` is conjugate, across the adjunctions
of Stacks 03D7, to the identification `h_* ≅ f_* ⋙ g_*` of direct images built from the
compositor of direct images and `t`.

## Main results

* `AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_inv_comp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The identification of pullbacks along a composite read through a 2-isomorphism is conjugate
to that of direct images.**  Across the adjunctions of Stacks 03D7, the conjugate of
`(pullbackModulesCompIso f g).inv ≫ t.pullbackModulesIso.hom : g^* ⋙ f^* ⟶ h^*` is
`t.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f g).hom : h_* ⟶ f_* ⋙ g_*`. -/
theorem conjugateEquiv_pullbackModulesCompIso_inv_comp (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) {h : RingedToposHom X Z} (t : TwoIso (g.comp f) h) :
    conjugateEquiv (pullbackAdjPushforwardModules h)
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))
        ((pullbackModulesCompIso f g).inv ≫ t.pullbackModulesIso.hom) =
      t.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f g).hom := by
  rw [← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp f)), TwoIso.pullbackModulesIso,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom, pullbackModulesCompIso,
    Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv]

end AlgebraicGeometry.RingedToposHom
