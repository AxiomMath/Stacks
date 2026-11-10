module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompAssoc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableSquare

/-!
# Coherence of the 2-isomorphisms of ringed topoi on sheaves of modules

A 2-isomorphism `s : f ≅ g` of morphisms of ringed topoi induces isomorphisms `f_* ≅ g_*` and
`f^* ≅ g^*` of the direct images and pullbacks of sheaves of modules
(`AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso` and
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`). This file records how these
isomorphisms behave under the calculus of 2-isomorphisms: they are compatible with vertical
composition, and with whiskering on either side against the composition isomorphisms
`(g ∘ f)_* ≅ g_* ∘ f_*` and `(g ∘ f)^* ≅ f^* ∘ g^*`.

## Main results

* `TwoIso.trans_symm_self`, `TwoIso.symm_trans`: the groupoid identities of 2-isomorphisms.
* `TwoIso.pasteHorizontal`: the 2-isomorphism of the outer rectangle of two horizontally composable
  2-commutative squares.
* `TwoIso.pushforwardModulesIso_trans`, `TwoIso.pullbackModulesIso_trans`: compatibility with
  vertical composition.
* `TwoIso.pullbackModulesCompIso_inv_whiskerRight` and
  `TwoIso.pullbackModulesCompIso_inv_whiskerLeft`: the composition isomorphism of pullbacks is
  natural with respect to a 2-isomorphism in either factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe v u w v' u' w' v'' u'' w'' v₃ u₃ w₃

section Groupoid

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}} {W : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})] [W.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]

/-- A 2-isomorphism followed by its inverse is the identity 2-isomorphism. -/
theorem trans_symm_self {f g : RingedToposHom X Y} (s : TwoIso f g) :
    s.trans s.symm = refl f :=
  TwoIso.ext (Iso.self_symm_id s.e)

/-- The inverse of a vertical composite of 2-isomorphisms is the composite of the inverses in
the opposite order. -/
theorem symm_trans {f g h : RingedToposHom X Y} (s : TwoIso f g) (s' : TwoIso g h) :
    (s.trans s').symm = s'.symm.trans s.symm :=
  TwoIso.ext rfl

end Groupoid

section Paste

universe vA uA wA vA' uA' wA' vA'' uA'' wA'' vB uB wB vB' uB' wB' vB'' uB'' wB''

variable {A : RingedTopos.{vA, uA, wA}} {A' : RingedTopos.{vA', uA', wA'}}
  {A'' : RingedTopos.{vA'', uA'', wA''}} {B : RingedTopos.{vB, uB, wB}}
  {B' : RingedTopos.{vB', uB', wB'}} {B'' : RingedTopos.{vB'', uB'', wB''}}
  [A.J.HasSheafCompose (forget RingCat.{wA})] [A'.J.HasSheafCompose (forget RingCat.{wA'})]
  [A''.J.HasSheafCompose (forget RingCat.{wA''})] [B.J.HasSheafCompose (forget RingCat.{wB})]
  [B'.J.HasSheafCompose (forget RingCat.{wB'})] [B''.J.HasSheafCompose (forget RingCat.{wB''})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [A'.J.HasSheafCompose (forget₂ CommRingCat.{wA'} RingCat.{wA'})]
  [A''.J.HasSheafCompose (forget₂ CommRingCat.{wA''} RingCat.{wA''})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [B''.J.HasSheafCompose (forget₂ CommRingCat.{wB''} RingCat.{wB''})]

/-- Horizontal pasting of two 2-commutative squares of ringed topoi. For squares

```
        g'         g
  A'' ———→ A' ———→ A
   │ f''     │ f'    │ f
   v         v       v
  B'' ———→ B' ———→ B
        h'         h
```

commuting up to `s : h ∘ f' ≅ f ∘ g` and `s' : h' ∘ f'' ≅ f' ∘ g'`, the 2-isomorphism
`(h ∘ h') ∘ f'' ≅ f ∘ (g ∘ g')` exhibiting the outer rectangle as commutative. -/
noncomputable def pasteHorizontal {f : RingedToposHom A B} {f' : RingedToposHom A' B'}
    {f'' : RingedToposHom A'' B''} {g : RingedToposHom A' A} {g' : RingedToposHom A'' A'}
    {h : RingedToposHom B' B} {h' : RingedToposHom B'' B'} (s : TwoIso (h.comp f') (f.comp g))
    (s' : TwoIso (h'.comp f'') (f'.comp g')) :
    TwoIso ((h.comp h').comp f'') (f.comp (g.comp g')) :=
  (associator f'' h' h).symm.trans ((s'.whiskerRight h).trans ((associator g' f' h).trans
    ((s.whiskerLeft g').trans (associator g' g f).symm)))

end Paste

section Modules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- The direct-image isomorphism of a vertical composite of 2-isomorphisms is the composite of
the two direct-image isomorphisms. -/
theorem pushforwardModulesIso_trans {f g h : RingedToposHom X Y} (s : TwoIso f g)
    (s' : TwoIso g h) :
    (s.trans s').pushforwardModulesIso = s.pushforwardModulesIso ≪≫ s'.pushforwardModulesIso := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ hom_ext_moduleSheafFunctor ?_))
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]
  rfl

/-- The direct-image form of the naturality of the composition isomorphism in its first factor:
for `s : f₁ ≅ f₂` and `g`, the inverse of the direct-image isomorphism of `g ∘ s`, read through
the composition isomorphisms, is `g_*` of the inverse of that of `s`. -/
theorem pushforwardModulesIso_whiskerRight_inv {f₁ f₂ : RingedToposHom X Y} (s : TwoIso f₁ f₂)
    (g : RingedToposHom Y Z) :
    (s.whiskerRight g).pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f₁ g).hom =
      (pushforwardModulesCompIso f₂ g).hom ≫
        Functor.whiskerRight s.pushforwardModulesIso.inv (pushforwardModules g) := by
  refine NatTrans.ext (funext fun M ↦ hom_ext_moduleSheafFunctor ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Functor.map_comp]
  rfl

/-- The direct-image form of the naturality of the composition isomorphism in its second factor:
for `f` and `s : g₁ ≅ g₂`, the inverse of the direct-image isomorphism of `s ∘ f`, read through
the composition isomorphisms, is the inverse of that of `s` at `f_*`. -/
theorem pushforwardModulesIso_whiskerLeft_inv (f : RingedToposHom X Y)
    {g₁ g₂ : RingedToposHom Y Z} (s : TwoIso g₁ g₂) :
    (s.whiskerLeft f).pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f g₁).hom =
      (pushforwardModulesCompIso f g₂).hom ≫
        Functor.whiskerLeft (pushforwardModules f) s.pushforwardModulesIso.inv := by
  refine NatTrans.ext (funext fun M ↦ hom_ext_moduleSheafFunctor ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Functor.map_comp]
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The pullback isomorphism of a 2-isomorphism is the left adjoint of the inverse of its
direct-image isomorphism: its conjugate under the pullback-pushforward adjunctions is that
inverse. -/
theorem conjugateEquiv_pullbackModulesIso_hom {f g : RingedToposHom X Y} (s : TwoIso f g) :
    conjugateEquiv (pullbackAdjPushforwardModules g) (pullbackAdjPushforwardModules f)
        s.pullbackModulesIso.hom = s.pushforwardModulesIso.inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The pullback isomorphism of a vertical composite of 2-isomorphisms is the composite of the two
pullback isomorphisms. -/
theorem pullbackModulesIso_trans {f g h : RingedToposHom X Y} (s : TwoIso f g)
    (s' : TwoIso g h) :
    (s.trans s').pullbackModulesIso = s.pullbackModulesIso ≪≫ s'.pullbackModulesIso := by
  refine Iso.ext ((conjugateEquiv (pullbackAdjPushforwardModules h)
    (pullbackAdjPushforwardModules f)).injective ?_)
  rw [Iso.trans_hom, ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules g),
    conjugateEquiv_pullbackModulesIso_hom, conjugateEquiv_pullbackModulesIso_hom,
    conjugateEquiv_pullbackModulesIso_hom, pushforwardModulesIso_trans, Iso.trans_inv]

/-- The composition isomorphism of pullbacks is natural in its first factor. For a
2-isomorphism `s : f₁ ≅ f₂` and a morphism `g`, the square

```
  g^* ⋙ f₁^* ──(g∘f₁)^*-comparison──→ (g ∘ f₁)^*
      │ g^* (s^*)                          │ (g ∘ s)^*
      v                                    v
  g^* ⋙ f₂^* ──(g∘f₂)^*-comparison──→ (g ∘ f₂)^*
```

commutes. -/
theorem pullbackModulesCompIso_inv_whiskerRight {f₁ f₂ : RingedToposHom X Y} (s : TwoIso f₁ f₂)
    (g : RingedToposHom Y Z) :
    (pullbackModulesCompIso f₁ g).inv ≫ (s.whiskerRight g).pullbackModulesIso.hom =
      Functor.whiskerLeft g.toModulesHom.pullbackModules s.pullbackModulesIso.hom ≫
        (pullbackModulesCompIso f₂ g).inv := by
  apply (conjugateEquiv (pullbackAdjPushforwardModules (g.comp f₂))
    ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f₁))).injective
  rw [← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp f₁)),
    ← conjugateEquiv_comp _ ((pullbackAdjPushforwardModules g).comp
      (pullbackAdjPushforwardModules f₂)),
    conjugateEquiv_pullbackModulesIso_hom, conjugateEquiv_pullbackModulesCompIso_inv,
    conjugateEquiv_pullbackModulesCompIso_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_pullbackModulesIso_hom]
  exact pushforwardModulesIso_whiskerRight_inv s g

/-- The composition isomorphism of pullbacks is natural in its second factor. For a
morphism `f` and a 2-isomorphism `s : g₁ ≅ g₂`, the square

```
  g₁^* ⋙ f^* ──(g₁∘f)^*-comparison──→ (g₁ ∘ f)^*
      │ (s^*) f^*                          │ (s ∘ f)^*
      v                                    v
  g₂^* ⋙ f^* ──(g₂∘f)^*-comparison──→ (g₂ ∘ f)^*
```

commutes. -/
theorem pullbackModulesCompIso_inv_whiskerLeft (f : RingedToposHom X Y)
    {g₁ g₂ : RingedToposHom Y Z} (s : TwoIso g₁ g₂) :
    (pullbackModulesCompIso f g₁).inv ≫ (s.whiskerLeft f).pullbackModulesIso.hom =
      Functor.whiskerRight s.pullbackModulesIso.hom f.toModulesHom.pullbackModules ≫
        (pullbackModulesCompIso f g₂).inv := by
  apply (conjugateEquiv (pullbackAdjPushforwardModules (g₂.comp f))
    ((pullbackAdjPushforwardModules g₁).comp (pullbackAdjPushforwardModules f))).injective
  rw [← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g₁.comp f)),
    ← conjugateEquiv_comp _ ((pullbackAdjPushforwardModules g₂).comp
      (pullbackAdjPushforwardModules f)),
    conjugateEquiv_pullbackModulesIso_hom, conjugateEquiv_pullbackModulesCompIso_inv,
    conjugateEquiv_pullbackModulesCompIso_inv, conjugateEquiv_whiskerRight,
    conjugateEquiv_pullbackModulesIso_hom]
  exact pushforwardModulesIso_whiskerLeft_inv f s

end Modules

end AlgebraicGeometry.RingedToposHom.TwoIso

end
