module

public import Mathlib.CategoryTheory.Sites.Continuous
import StacksCore.Tactic.EgaSgaAttribute

/-! # Composing the direct image of a continuous functor

For composable continuous functors `u : C ⥤ D` and `v : D ⥤ E` between sites, Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp` identifies the composite of the two
restriction functors on sheaves with the restriction along `u ⋙ v`, and it does so by
`Iso.refl`: restriction along a composite *is* the composite of the restrictions.

A consumer essentially never meets the composite in that literal form.  What it has is a third
functor `w : C ⥤ E` together with an equation `u ⋙ v = w` -- the componentwise localization
functor of a semi-representable object factors through a relocalization, a transition functor of
a simplicial site composes with an augmentation, and so on -- and that equation is proved rather
than definitional, so no `Iso.refl` typechecks against it.  This file states the comparison in
that form and computes it.

Not to be confused with `CategoryTheory.Functor.sheafPushforwardContinuousCompIsoOfEq`, which
compares the direct images of *two composites* `f ⋙ g` and `f ⋙ h` with a common first factor
along an equation between them.  Here one side of the equation is a single functor, and it is the
direct image along that functor which is being split.

## Main definitions

* `CategoryTheory.Functor.sheafPushforwardContinuousIsoOfCompEq`: for `h : u ⋙ v = w`, the
  isomorphism between restriction along `w` and the composite of the restrictions along `v`
  and `u`.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuousIsoOfCompEq_hom_app_hom` and
  `CategoryTheory.Functor.sheafPushforwardContinuousIsoOfCompEq_inv_app_hom`: the comparison is
  the presheaf-level transport along `h` and nothing else -- the whole content of the
  isomorphism is the equation it is built from.
* `CategoryTheory.Functor.sheafPushforwardContinuousIsoOfCompEq_rfl`: on a definitional
  equation it is the identity, so the comparison adds nothing where nothing is needed.
* `CategoryTheory.Functor.sheafPushforwardContinuousIsoOfCompEq_naturality`: the comparison is
  compatible with the action of restriction on morphisms of sites.
* `CategoryTheory.Functor.sheafPushforwardContinuousNatTrans_whiskerRight`: that action commutes
  with restricting along a further functor.  Mathlib defines the action and states nothing about
  it; its functoriality is
  `CategoryTheory.Functor.sheafPushforwardContinuousNatTrans_comp` and
  `CategoryTheory.Functor.sheafPushforwardContinuousNatTrans_id`, already in the tree.

## Implementation notes

The definition is Mathlib's `sheafPushforwardContinuousComp'` at `eqToIso h`, taken in the
direction that reads "the direct image along a composite is the composite of the direct images".

Both component lemmas go through a `have` naming the comparison outright as
`sheafPushforwardContinuousNatTrans` at the transport, discharged by `Category.comp_id`.  That
detour is what the defeq costs here.  The comparison is a composition with the inverse of
`sheafPushforwardContinuousComp`, which is an identity -- but an identity of
`v.sheafPushforwardContinuous A K L ⋙ u.sheafPushforwardContinuous A J K`, whereas the
transformation it is composed with has `(u ⋙ v).sheafPushforwardContinuous A J L` as its
target.  Those two functors are definitionally but not syntactically equal, so
`Category.comp_id` does not fire as a rewrite; stating it as the type of a `have` hands that one
defeq to the elaborator and leaves a goal which is a single rewrite.
-/

@[expose] public section

open CategoryTheory

universe t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (u : C ⥤ D) (v : D ⥤ E) {w : C ⥤ E} (h : u ⋙ v = w)
  (A : Type u) [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [u.IsContinuous J K] [v.IsContinuous K L] [w.IsContinuous J L]

/-- **The direct image along a composite of continuous functors.**  If `u ⋙ v = w`, restriction
of sheaves along `w` is the composite of restriction along `v` and restriction along `u`.

The composition is presented by an equation of functors rather than by the literal composite,
which is the form in which it arises; `Iso.refl` does not typecheck against a proved equation,
even one both of whose sides are built from the same data. -/
@[ega "0 3.4.3" "more general"]
noncomputable def sheafPushforwardContinuousIsoOfCompEq :
    w.sheafPushforwardContinuous A J L ≅
      v.sheafPushforwardContinuous A K L ⋙ u.sheafPushforwardContinuous A J K :=
  (sheafPushforwardContinuousComp' (eqToIso h) A J K L).symm

/-- A morphism of restriction functors equal to the one induced by `eqToHom e` is the
presheaf-level transport along `e` at each sheaf. -/
private theorem app_hom_eq_whiskerRight_eqToHom {a b : C ⥤ E}
    [a.IsContinuous J L] [b.IsContinuous J L] (e : a = b)
    (φ : b.sheafPushforwardContinuous A J L ⟶ a.sheafPushforwardContinuous A J L)
    (hφ : φ = sheafPushforwardContinuousNatTrans (eqToHom e) A J L) (F : Sheaf L A) :
    ((φ.app F).hom : b.op ⋙ F.obj ⟶ a.op ⋙ F.obj) =
      Functor.whiskerRight (NatTrans.op (eqToHom e)) F.obj := by
  rw [hφ, sheafPushforwardContinuousNatTrans_app_hom]
  rfl

/-- The comparison at a sheaf is the presheaf-level transport along `h`. -/
theorem sheafPushforwardContinuousIsoOfCompEq_hom_app_hom (F : Sheaf L A) :
    (((sheafPushforwardContinuousIsoOfCompEq u v h A J K L).hom.app F).hom :
        w.op ⋙ F.obj ⟶ u.op ⋙ v.op ⋙ F.obj) =
      Functor.whiskerRight (NatTrans.op (eqToHom h)) F.obj := by
  have : (u ⋙ v).IsContinuous J L := isContinuous_comp u v J K L
  exact app_hom_eq_whiskerRight_eqToHom A J L h _ (Category.comp_id _) F

/-- The inverse of the comparison at a sheaf is the presheaf-level transport along `h.symm`. -/
theorem sheafPushforwardContinuousIsoOfCompEq_inv_app_hom (F : Sheaf L A) :
    (((sheafPushforwardContinuousIsoOfCompEq u v h A J K L).inv.app F).hom :
        u.op ⋙ v.op ⋙ F.obj ⟶ w.op ⋙ F.obj) =
      Functor.whiskerRight (NatTrans.op (eqToHom h.symm)) F.obj := by
  have : (u ⋙ v).IsContinuous J L := isContinuous_comp u v J K L
  exact app_hom_eq_whiskerRight_eqToHom A J L h.symm _ (Category.id_comp _) F

/-- On a definitional composition the comparison is the identity. -/
theorem sheafPushforwardContinuousIsoOfCompEq_rfl [(u ⋙ v).IsContinuous J L] :
    sheafPushforwardContinuousIsoOfCompEq u v rfl A J K L = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun F => Sheaf.hom_ext ?_))
  refine Eq.trans (sheafPushforwardContinuousIsoOfCompEq_hom_app_hom u v rfl A J K L F) ?_
  refine NatTrans.ext (funext fun X => ?_)
  change F.obj.map (𝟙 (Opposite.op (v.obj (u.obj X.unop)))) = 𝟙 _
  exact F.obj.map_id _

section NatTrans

variable {u} {v}

/-- Restricting along `v` the transformation induced by `τ : u ⟶ u'` is the transformation
induced by `τ` whiskered with `v`. -/
theorem sheafPushforwardContinuousNatTrans_whiskerRight {u' : C ⥤ D} [u'.IsContinuous J K]
    (τ : u ⟶ u') (v : D ⥤ E) [v.IsContinuous K L] [(u ⋙ v).IsContinuous J L]
    [(u' ⋙ v).IsContinuous J L] :
    Functor.whiskerLeft (v.sheafPushforwardContinuous A K L)
        (sheafPushforwardContinuousNatTrans τ A J K) =
      sheafPushforwardContinuousNatTrans (Functor.whiskerRight τ v) A J L := by
  ext F X
  rfl

end NatTrans

variable {u}

/-- **The comparison is compatible with the action of restriction on morphisms of sites.**  Let
`τ : u ⟶ u'` be a transformation of the first factor and `σ : w ⟶ w'` a transformation of the
composites corresponding to it under the two equations.  Restriction turns both into
transformations of the direct images, contravariantly, and the comparison carries one to the
other. -/
theorem sheafPushforwardContinuousIsoOfCompEq_naturality {u' : C ⥤ D} {w' : C ⥤ E}
    [u'.IsContinuous J K] [w'.IsContinuous J L] (τ : u ⟶ u') (h' : u' ⋙ v = w') (σ : w ⟶ w')
    (hσ : Functor.whiskerRight τ v = eqToHom h ≫ σ ≫ eqToHom h'.symm) :
    (sheafPushforwardContinuousIsoOfCompEq u' v h' A J K L).hom ≫
        Functor.whiskerLeft (v.sheafPushforwardContinuous A K L)
          (sheafPushforwardContinuousNatTrans τ A J K) =
      sheafPushforwardContinuousNatTrans σ A J L ≫
        (sheafPushforwardContinuousIsoOfCompEq u v h A J K L).hom := by
  subst h
  subst h'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hσ
  subst hσ
  rw [sheafPushforwardContinuousNatTrans_whiskerRight,
    sheafPushforwardContinuousIsoOfCompEq_rfl, sheafPushforwardContinuousIsoOfCompEq_rfl,
    Iso.refl_hom, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end CategoryTheory.Functor

end
