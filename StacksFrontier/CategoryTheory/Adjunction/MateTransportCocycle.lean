module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# A system of comparisons of left adjoints conjugated by equivalences, and composition

Let `E : M ≌ N` and `E' : M' ≌ N'` be equivalences, let `a ⊣ A` be an adjunction between `N`
and `N'` and `b ⊣ B` one between `M` and `M'`, and let
`cmp : B ⋙ E.functor ≅ E'.functor ⋙ A` compare the two routes round the square of the two right
adjoints.  Then `a ⋙ E'.inverse` and `E.inverse ⋙ b` are two left adjoints of `E'.functor ⋙ A`
— the second one through `cmp` — so they are compared by
`CategoryTheory.Adjunction.leftAdjointUniq`, and that comparison, corrected by the counit of `E'`
on the left and the unit of `E` on the right, is a comparison of the two routes round the square
of the two *left* adjoints, a morphism `a (E X) ⟶ E' (b X)`.

This file identifies that corrected comparison with the **mate** of `cmp` in the sense of
`CategoryTheory.mateEquiv`, and deduces that a system of such comparisons is compatible with
composition as soon as the system of the `cmp`s is.  The point is that mates compose: Mathlib's
`CategoryTheory.mateEquiv_hcomp` turns the mate of a vertical pasting of two squares into the
horizontal pasting of the mates, and `CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` say what changing the left and the right edge of
a square by a 2-cell does to its mate.  So the cocycle condition for the comparisons of left
adjoints *is* the cocycle condition for the comparisons of right adjoints, read through a
bijection, and no value of any comparison is ever computed.

## Main results

* `Stacks.CategoryTheory.homEquiv_transportedComparison`: **the transpose of the corrected
  comparison** along `a ⊣ A` is the image under `E.functor` of the unit of `b ⊣ B`, followed by
  `cmp`.  This is the characterising equation, and everything else is formal.
* `Stacks.CategoryTheory.transportedComparison_eq_mateEquiv_symm_app` and
  `Stacks.CategoryTheory.transportedComparisonApp_eq_mateEquiv_symm`: the corrected comparison
  is the mate of `cmp`, with the corrected comparison anonymous and named respectively.
* `Stacks.CategoryTheory.transportedComparisonApp`: the corrected comparison, named.
* `Stacks.CategoryTheory.cocycle_app_of_iso`: the cocycle condition for three comparisons of
  right adjoints, as an equation of isomorphisms, read at an object and solved for the two
  composition comparisons.
* `Stacks.CategoryTheory.mateEquiv_symm_cocycle`: **the cocycle condition for the mates**, from
  the cocycle condition for the comparisons of right adjoints together with the two
  identifications of the composition comparisons of the left adjoints as conjugates.
* `Stacks.CategoryTheory.transportedComparison_cocycle`: the same read at an object and with the
  corrected comparisons written out, which is the form a consumer holding three such comparisons
  — one for each of two composable morphisms and one for their composite — uses.

## Implementation notes

The characterising equation is proved by `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`,
which replaces the unit of the first composite adjunction followed by the comparison with the
unit of the second, and then by two naturality squares and one triangle identity of `E`.  No
triangle identity of `E'` is used, and neither counit of the two adjunctions appears.

Every statement is at plain variables: the categories, the functors, the adjunctions and the
comparisons are all parameters, and the two composition comparisons of left adjoints enter only
through the hypotheses that their conjugates are the given comparisons of the right adjoints.  A
consumer therefore supplies existing lemmas and restates nothing; in particular the cocycle
condition is taken in the shape an equation of *isomorphisms* has, which is the shape in which
such a law is usually proved, and `Stacks.CategoryTheory.cocycle_app_of_iso` does the
rearrangement generically.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.CategoryTheory

section OneSquare

variable {M M' N N' : Type*} [Category* M] [Category* M'] [Category* N] [Category* N']
  (E : M ≌ N) (E' : M' ≌ N') {a : N ⥤ N'} {A : N' ⥤ N} (α : a ⊣ A)
  {b : M ⥤ M'} {B : M' ⥤ M} (β : b ⊣ B) (cmp : B ⋙ E.functor ≅ E'.functor ⋙ A)

/-- **The transpose of the comparison of the two routes round the square of left adjoints.**

`a ⋙ E'.inverse` and `E.inverse ⋙ b` are two left adjoints of `E'.functor ⋙ A`, the second one
through `cmp`, hence compared by `CategoryTheory.Adjunction.leftAdjointUniq`; correcting that
comparison by the counit of `E'` on the left and the unit of `E` on the right gives a morphism
`a (E X) ⟶ E' (b X)`, and its transpose along `a ⊣ A` is the image under `E.functor` of the unit
of `b ⊣ B`, followed by the component of `cmp`.

This equation determines the corrected comparison, since the transpose is a bijection. -/
theorem homEquiv_transportedComparison (X : M) :
    α.homEquiv (E.functor.obj X) (E'.functor.obj (b.obj X))
        (E'.counitIso.inv.app (a.obj (E.functor.obj X)) ≫
          E'.functor.map ((Adjunction.leftAdjointUniq (α.comp E'.symm.toAdjunction)
                ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)).hom.app (E.functor.obj X) ≫
            b.map (E.unitIso.inv.app X))) =
      E.functor.map (β.unit.app X) ≫ cmp.hom.app (b.obj X) := by
  have hkey := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (α.comp E'.symm.toAdjunction) ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)
    (x := E.functor.obj X) (b.map (E.unitIso.inv.app X))
  have hβ := β.unit.naturality (E.unitIso.inv.app X)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hβ
  have hL : (α.comp E'.symm.toAdjunction).homEquiv (E.functor.obj X) (b.obj X)
        ((Adjunction.leftAdjointUniq (α.comp E'.symm.toAdjunction)
            ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)).hom.app (E.functor.obj X) ≫
          b.map (E.unitIso.inv.app X)) =
      α.homEquiv (E.functor.obj X) (E'.functor.obj (b.obj X))
        (E'.counitIso.inv.app (a.obj (E.functor.obj X)) ≫
          E'.functor.map ((Adjunction.leftAdjointUniq (α.comp E'.symm.toAdjunction)
                ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)).hom.app (E.functor.obj X) ≫
            b.map (E.unitIso.inv.app X))) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  have hinner : (E.symm.toAdjunction.comp β).homEquiv (E.functor.obj X) (b.obj X)
      (b.map (E.unitIso.inv.app X)) = E.functor.map (β.unit.app X) := by
    rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.assoc]
    show E.counitIso.inv.app (E.functor.obj X) ≫
        E.functor.map (β.unit.app (E.inverse.obj (E.functor.obj X))) ≫
          E.functor.map (B.map (b.map (E.unitIso.inv.app X))) =
      E.functor.map (β.unit.app X)
    rw [← Functor.map_comp, ← hβ, Functor.map_comp, ← Category.assoc]
    simp
  have hR : ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp).homEquiv (E.functor.obj X)
        (b.obj X) (b.map (E.unitIso.inv.app X)) =
      E.functor.map (β.unit.app X) ≫ cmp.hom.app (b.obj X) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, hinner]
  exact hL.symm.trans (hkey.trans hR)

/-- **The comparison of the two routes round the square of left adjoints is the mate of the
comparison of the two routes round the square of right adjoints.**

Both sides have the same transpose along `a ⊣ A`:
`Stacks.CategoryTheory.homEquiv_transportedComparison` for the left-hand side and
`CategoryTheory.unit_mateEquiv_symm` for the right-hand side. -/
theorem transportedComparison_eq_mateEquiv_symm_app (X : M) :
    E'.counitIso.inv.app (a.obj (E.functor.obj X)) ≫
        E'.functor.map ((Adjunction.leftAdjointUniq (α.comp E'.symm.toAdjunction)
              ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)).hom.app (E.functor.obj X) ≫
          b.map (E.unitIso.inv.app X)) =
      ((mateEquiv β α).symm (TwoSquare.mk B E'.functor E.functor A cmp.hom)).natTrans.app X := by
  refine (α.homEquiv (E.functor.obj X) (E'.functor.obj (b.obj X))).injective ?_
  rw [homEquiv_transportedComparison E E' α β cmp X, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm β α (TwoSquare.mk B E'.functor E.functor A cmp.hom) X

/-- **The comparison of the two routes round the square of left adjoints, at an object.**

`a ⋙ E'.inverse` and `E.inverse ⋙ b` are two left adjoints of `E'.functor ⋙ A`, the second one
through `cmp`; this is their comparison, corrected by the counit of `E'` on the left and the unit
of `E` on the right, read at an object.

It is named so that a consumer whose own comparison is this composite pays the identification
once, in a declaration of its own, rather than inside the elaboration of the composition law
below. -/
def transportedComparisonApp (X : M) :
    a.obj (E.functor.obj X) ⟶ E'.functor.obj (b.obj X) :=
  E'.counitIso.inv.app (a.obj (E.functor.obj X)) ≫
    E'.functor.map ((Adjunction.leftAdjointUniq (α.comp E'.symm.toAdjunction)
          ((E.symm.toAdjunction.comp β).ofNatIsoRight cmp)).hom.app (E.functor.obj X) ≫
      b.map (E.unitIso.inv.app X))

/-- `Stacks.CategoryTheory.transportedComparison_eq_mateEquiv_symm_app` for the named
comparison. -/
theorem transportedComparisonApp_eq_mateEquiv_symm (X : M) :
    transportedComparisonApp E E' α β cmp X =
      ((mateEquiv β α).symm (TwoSquare.mk B E'.functor E.functor A cmp.hom)).natTrans.app X :=
  transportedComparison_eq_mateEquiv_symm_app E E' α β cmp X

end OneSquare

section Cocycle

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [Category* M₁] [Category* M₂] [Category* M₃]
  [Category* N₁] [Category* N₂] [Category* N₃]
  {F₁ : M₁ ⥤ N₁} {F₂ : M₂ ⥤ N₂} {F₃ : M₃ ⥤ N₃}
  {ap : N₂ ⥤ N₁} {Ap : N₁ ⥤ N₂} {aq : N₃ ⥤ N₂} {Aq : N₂ ⥤ N₃} {ac : N₃ ⥤ N₁} {Ac : N₁ ⥤ N₃}
  {bp : M₂ ⥤ M₁} {Bp : M₁ ⥤ M₂} {bq : M₃ ⥤ M₂} {Bq : M₂ ⥤ M₃} {bc : M₃ ⥤ M₁} {Bc : M₁ ⥤ M₃}

/-- **A cocycle condition for comparisons of the two routes round three squares, read at an
object and solved for the two composition comparisons of the right adjoints.**

The hypothesis is the equation of isomorphisms in which such a law is proved — the two
comparisons pasted, read through the composition comparison `eA`, against the composition
comparison `eB` followed by the comparison for the composite — and the conclusion is that
equation at an object with `eB` moved to the other side and `eA` inverted. -/
theorem cocycle_app_of_iso {cp : Bp ⋙ F₂ ≅ F₁ ⋙ Ap} {cq : Bq ⋙ F₃ ≅ F₂ ⋙ Aq}
    {cc : Bc ⋙ F₃ ≅ F₁ ⋙ Ac} {eA : Ap ⋙ Aq ≅ Ac} {eB : Bc ≅ Bp ⋙ Bq}
    (hc : Functor.isoWhiskerLeft Bp cq ≪≫ Functor.isoWhiskerRight cp Aq ≪≫
          Functor.isoWhiskerLeft F₁ eA =
        Functor.isoWhiskerRight eB.symm F₃ ≪≫ cc) (Z : M₁) :
    F₃.map (eB.hom.app Z) ≫ cq.hom.app (Bp.obj Z) ≫ Aq.map (cp.hom.app Z) =
      cc.hom.app Z ≫ eA.inv.app (F₁.obj Z) := by
  have hcZ := congr_app (congrArg Iso.hom hc) Z
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.comp_obj] at hcZ
  have h2 : F₃.map (eB.hom.app Z) ≫ cq.hom.app (Bp.obj Z) ≫ Aq.map (cp.hom.app Z) ≫
      eA.hom.app (F₁.obj Z) = cc.hom.app Z := by
    rw [hcZ, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
  rw [← h2]
  simp

variable (αp : ap ⊣ Ap) (αq : aq ⊣ Aq) (αc : ac ⊣ Ac)
  (βp : bp ⊣ Bp) (βq : bq ⊣ Bq) (βc : bc ⊣ Bc)
  (cp : Bp ⋙ F₂ ≅ F₁ ⋙ Ap) (cq : Bq ⋙ F₃ ≅ F₂ ⋙ Aq) (cc : Bc ⋙ F₃ ≅ F₁ ⋙ Ac)
  (eA : Ap ⋙ Aq ≅ Ac) (eB : Bc ≅ Bp ⋙ Bq)
  (κa : aq ⋙ ap ≅ ac) (κb : bq ⋙ bp ≅ bc)

/-- **The cocycle condition for the mates**, from the cocycle condition for the comparisons of
the right adjoints.

Pasting the mate of `cp` below the mate of `cq` and reading the result through the comparison
`κb` of the composite left adjoints on the one side and through the comparison `κa` on the
other, the two agree.  The hypotheses are that the conjugates of `κa` and `κb` are the given
comparisons `eA` and `eB` of the right adjoints — which is what makes `κa` and `κb` *the*
composition comparisons — and the cocycle condition for `cp`, `cq`, `cc`.

Applying the bijection `CategoryTheory.mateEquiv` turns the claim into that condition:
`CategoryTheory.mateEquiv_hcomp` computes the mate of the pasting, and the two mixed vertical
composition laws compute the effect of the two whiskerings. -/
theorem mateEquiv_symm_cocycle
    (hκa : conjugateEquiv αc (αq.comp αp) κa.hom = eA.inv)
    (hκb : conjugateEquiv βc (βq.comp βp) κb.hom = eB.hom)
    (hc : ∀ Z, F₃.map (eB.hom.app Z) ≫ cq.hom.app (Bp.obj Z) ≫ Aq.map (cp.hom.app Z) =
      cc.hom.app Z ≫ eA.inv.app (F₁.obj Z)) :
    TwoSquare.whiskerLeft
        (TwoSquare.vComp ((mateEquiv βq αq).symm (TwoSquare.mk Bq F₂ F₃ Aq cq.hom))
          ((mateEquiv βp αp).symm (TwoSquare.mk Bp F₁ F₂ Ap cp.hom))) κb.hom =
      TwoSquare.whiskerRight
        ((mateEquiv βc αc).symm (TwoSquare.mk Bc F₁ F₃ Ac cc.hom)) κa.hom := by
  refine (mateEquiv βc (αq.comp αp)).injective ?_
  rw [conjugateEquiv_mateEquiv_vcomp βc (βq.comp βp) (αq.comp αp) κb.hom,
    mateEquiv_conjugateEquiv_vcomp βc αc (αq.comp αp) _ κa.hom,
    mateEquiv_hcomp βq αq βp αp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, hκa, hκb]
  refine TwoSquare.ext _ _ fun Z ↦ ?_
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj]
  exact hc Z

/-- **The cocycle condition for three comparisons of the two routes round a square of left
adjoints, at an object.**

This is `Stacks.CategoryTheory.mateEquiv_symm_cocycle` read at an object, with each mate written
out as the comparison of two left adjoints corrected by the counit of one equivalence and the
unit of the other, which is the shape such a comparison is constructed in. -/
theorem transportedComparison_cocycle (E₁ : M₁ ≌ N₁) (E₂ : M₂ ≌ N₂) (E₃ : M₃ ≌ N₃)
    (αp : ap ⊣ Ap) (αq : aq ⊣ Aq) (αc : ac ⊣ Ac)
    (βp : bp ⊣ Bp) (βq : bq ⊣ Bq) (βc : bc ⊣ Bc)
    (cp : Bp ⋙ E₂.functor ≅ E₁.functor ⋙ Ap) (cq : Bq ⋙ E₃.functor ≅ E₂.functor ⋙ Aq)
    (cc : Bc ⋙ E₃.functor ≅ E₁.functor ⋙ Ac)
    (eA : Ap ⋙ Aq ≅ Ac) (eB : Bc ≅ Bp ⋙ Bq) (κa : aq ⋙ ap ≅ ac) (κb : bq ⋙ bp ≅ bc)
    (hκa : conjugateEquiv αc (αq.comp αp) κa.hom = eA.inv)
    (hκb : conjugateEquiv βc (βq.comp βp) κb.hom = eB.hom)
    (hc : ∀ Z, E₃.functor.map (eB.hom.app Z) ≫ cq.hom.app (Bp.obj Z) ≫
        Aq.map (cp.hom.app Z) = cc.hom.app Z ≫ eA.inv.app (E₁.functor.obj Z)) (X : M₃) :
    ap.map (transportedComparisonApp E₃ E₂ αq βq cq X) ≫
        transportedComparisonApp E₂ E₁ αp βp cp (bq.obj X) ≫
          E₁.functor.map (κb.hom.app X) =
      κa.hom.app (E₃.functor.obj X) ≫ transportedComparisonApp E₃ E₁ αc βc cc X := by
  have key := congr_app (mateEquiv_symm_cocycle αp αq αc βp βq βc cp cq cc eA eB κa κb
    hκa hκb hc) X
  rw [transportedComparisonApp_eq_mateEquiv_symm E₃ E₂ αq βq cq X,
    transportedComparisonApp_eq_mateEquiv_symm E₂ E₁ αp βp cp (bq.obj X),
    transportedComparisonApp_eq_mateEquiv_symm E₃ E₁ αc βc cc X]
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc] using key

end Cocycle

end Stacks.CategoryTheory

end
