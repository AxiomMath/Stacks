module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheafification does not change the sections over an object of a dense subsite

Let `I : D ⥤ C` be the inclusion of a dense subsite which is moreover cocontinuous, and let `P`
be a presheaf on `C` whose restriction `I.op ⋙ P` to `D` is already a sheaf.  Then the canonical
map `P ⟶ P^#` into the sheafification is an isomorphism over every object in the image of `I`.

The reason is that `P ⟶ P^#` is a local isomorphism; restricting a local isomorphism along a
cocontinuous functor keeps it one, and a local isomorphism between sheaves is an isomorphism.

## Main results

* `CategoryTheory.Presheaf.isIso_toSheafify_app_of_isDenseSubsite`.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe w v'' v' v u'' u' u

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {A : Type u''} [Category.{v''} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **Sheafification does not change the sections over an object of a cocontinuous dense
subsite**, as soon as the restriction of the presheaf to that subsite is a sheaf. -/
theorem isIso_toSheafify_app_of_isDenseSubsite (J' : GrothendieckTopology D)
    (J : GrothendieckTopology C) (I : D ⥤ C) [I.IsCocontinuous J' J] [I.IsDenseSubsite J' J]
    [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [J'.HasSheafCompose (CategoryTheory.forget A)]
    (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J' (I.op ⋙ P)) (U : D) :
    IsIso ((toSheafify J P).app (op (I.obj U))) := by
  set q := toSheafify J P
  have _ : Presheaf.IsLocallyInjective J q := (J.W_toSheafify P).isLocallyInjective
  have _ : Presheaf.IsLocallySurjective J q := (J.W_toSheafify P).isLocallySurjective
  let q' : (⟨I.op ⋙ P, hP⟩ : Sheaf J' A) ⟶
      (I.sheafPushforwardContinuous A J' J).obj ((presheafToSheaf J A).obj P) :=
    ⟨I.op.whiskerLeft q⟩
  have _ : IsIso q' := (Sheaf.isLocallyBijective_iff_isIso q').mp
    ⟨Presheaf.isLocallyInjective_whisker J' J I q, Presheaf.isLocallySurjective_whisker J' J I q⟩
  have _ : IsIso q'.hom := inferInstanceAs (IsIso ((sheafToPresheaf J' A).map q'))
  exact inferInstanceAs (IsIso (q'.hom.app (op U)))

end CategoryTheory.Presheaf

end
