module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Naturality of the Frobenius descent isomorphism

For a scheme `S` of characteristic `p` and `n ≠ 0`, base change along the `n`-fold absolute
Frobenius `F_S^n` is isomorphic to the identity of the small étale site of `S`, the component at
an étale `U` being the relative Frobenius of `U`; hence every sheaf `M` on `S_étale` is
canonically isomorphic to `(F_S^n)_* M`
(`Stacks.EtaleCohomology.etaleSheafPushforwardComparison`).

This identification commutes with direct images: for a morphism `h : S' ⟶ S` of schemes of
characteristic `p` and a sheaf `M` on `S'_étale`, the direct image along `h` of
`M ≅ (F_{S'}^n)_* M` is `h_* M ≅ (F_S^n)_* h_* M`, up to the identification
`(F_S^n)_* h_* = (h ∘ F_{S'}^n)_* = h_* (F_{S'}^n)_*`. On the sites this is the naturality of
the relative Frobenius against base change.

It also satisfies a composition law: the identification for `F_S^{a + b}` is the one for `F_S^a`
followed by `(F_S^a)_*` of the one for `F_S^b`.

## Main results

* `Stacks.EtaleCohomology.absoluteFrobeniusPowEtaleSiteIso_baseChange`: the site-level
  naturality.
* `Stacks.EtaleCohomology.smallEtalePushforward_map_etaleSheafPushforwardComparison`: the
  naturality for direct images of sheaves, with arbitrary coefficients.
* `Stacks.EtaleCohomology.absoluteFrobeniusPowEtaleSiteIso_add` and
  `Stacks.EtaleCohomology.etaleSheafPushforwardComparison_add`: the composition law.

## References

* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

/-- In a category, `(e₁ ≫ i ≫ j) ≫ p₁ ≫ p₂ = r ≫ p₁ ≫ p₂` given six compatible factorizations
of its pieces. -/
private lemma frobeniusBaseChangeChain {D : Type*} [Category* D]
    {A B C E G H : D} (e₁ : A ⟶ B) (i : B ⟶ C) (j : C ⟶ E) (p₁ : E ⟶ G) (p₂ : G ⟶ H)
    (pm : C ⟶ H) (q₁ : B ⟶ A) (q₂' : A ⟶ H) (fr' : A ⟶ A) (fr : H ⟶ H)
    (r : A ⟶ E) (e₂ : H ⟶ G)
    (ha : j ≫ p₁ ≫ p₂ = pm) (hb : i ≫ pm = q₁ ≫ q₂') (hc : e₁ ≫ q₁ = fr')
    (hd : fr' ≫ q₂' = q₂' ≫ fr) (he : r ≫ p₁ = q₂' ≫ e₂) (hf : e₂ ≫ p₂ = fr) :
    (e₁ ≫ i ≫ j) ≫ p₁ ≫ p₂ = r ≫ p₁ ≫ p₂ := by
  rw [Category.assoc, Category.assoc, ha, hb, ← Category.assoc, hc, hd, ← hf,
    ← Category.assoc, ← he, Category.assoc]

variable {S S' : Scheme.{u}} (h : S' ⟶ S) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
  (hS' : IsInCharacteristic S' p) {n : ℕ} (hn : n ≠ 0) (m : S' ⟶ S)
  (hm' : m = absoluteFrobeniusPow S' p hS' n ≫ h) (hm : m = h ≫ absoluteFrobeniusPow S p hS n)

/-- **Naturality of the relative Frobenius against base change.** For an étale `U` over `S`, the
relative Frobenius of `U ×_S S'`, followed by the comparisons of the base changes along
`F_{S'}^n ≫ h = h ≫ F_S^n`, is the base change along `h` of the relative Frobenius of `U`. -/
lemma absoluteFrobeniusPowEtaleSiteIso_baseChange (U : S.Etale) :
    (absoluteFrobeniusPowEtaleSiteIso S' p hS' hn).hom.app ((smallEtaleBaseChange h).obj U) ≫
        (smallEtaleBaseChangeComp' (absoluteFrobeniusPow S' p hS' n) h m hm').inv.app U ≫
        (smallEtaleBaseChangeComp' h (absoluteFrobeniusPow S p hS n) m hm).hom.app U =
      (smallEtaleBaseChange h).map ((absoluteFrobeniusPowEtaleSiteIso S p hS hn).hom.app U) := by
  have hext : ∀ {A : S'.Etale} {a b : A ⟶ (smallEtaleBaseChange h).obj
      ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS n)).obj U)},
      a.left ≫ pullback.fst ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS n)).obj U).hom h ≫
          pullback.fst U.hom (absoluteFrobeniusPow S p hS n) =
        b.left ≫ pullback.fst ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS n)).obj U).hom h ≫
          pullback.fst U.hom (absoluteFrobeniusPow S p hS n) → a = b :=
    fun {_ a b} hab => smallEtaleBaseChange_hom_ext h (pullback.hom_ext hab
      ((smallEtaleBaseChange_fst_snd h (absoluteFrobeniusPow S p hS n) a).trans
        (smallEtaleBaseChange_fst_snd h (absoluteFrobeniusPow S p hS n) b).symm))
  exact hext <| frobeniusBaseChangeChain _ _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleBaseChangeComp'_fst_fst h (absoluteFrobeniusPow S p hS n) m hm U)
    (smallEtaleBaseChangeComp'_inv_fst (absoluteFrobeniusPow S' p hS' n) h m hm' U)
    (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst S' p hS' hn ((smallEtaleBaseChange h).obj U))
    (absoluteFrobeniusPow_naturality (pullback.fst U.hom h) p _ _ n)
    (smallEtaleBaseChange_map_left_fst h ((absoluteFrobeniusPowEtaleSiteIso S p hS hn).hom.app U))
    (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst S p hS hn U)

/-- Two composites of restriction maps agree when the underlying composites do. -/
private lemma map_op_comp_eq {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {W X Y Z : C} {a : X ⟶ W} {b : Y ⟶ X} {c : Z ⟶ W} {d : Y ⟶ Z} (h : b ≫ a = d ≫ c) :
    F.map a.op ≫ F.map b.op = F.map c.op ≫ F.map d.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]

/-- A composite of three restriction maps is the restriction along the composite. -/
private lemma map_op_comp_comp_eq {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {W X Y Z : C} {a : X ⟶ W} {b : Y ⟶ X} {c : Z ⟶ Y} {d : Z ⟶ W} (h : c ≫ b ≫ a = d) :
    F.map a.op ≫ F.map b.op ≫ F.map c.op = F.map d.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, Category.assoc, h]

/-- If `x.hom ≫ y.inv ≫ z.hom = w.hom` for isomorphisms `x`, `y`, `z`, `w`, then
`y.hom ≫ x.inv = z.hom ≫ w.inv`. -/
private lemma hom_comp_inv_eq_of_triangle {D : Type*} [Category* D] {A B M E : D} (x : A ≅ B)
    (y : M ≅ B) (z : M ≅ E) (w : A ≅ E) (h : x.hom ≫ y.inv ≫ z.hom = w.hom) :
    y.hom ≫ x.inv = z.hom ≫ w.inv := by
  obtain rfl : w = x ≪≫ y.symm ≪≫ z := Iso.ext h.symm
  simp

/-- The site-level naturality, read with the inverses of the two relative Frobenius
identifications. -/
lemma absoluteFrobeniusPowEtaleSiteIso_baseChange_inv (U : S.Etale) :
    (smallEtaleBaseChangeComp' (absoluteFrobeniusPow S' p hS' n) h m hm').hom.app U ≫
        (absoluteFrobeniusPowEtaleSiteIso S' p hS' hn).inv.app ((smallEtaleBaseChange h).obj U) =
      (smallEtaleBaseChangeComp' h (absoluteFrobeniusPow S p hS n) m hm).hom.app U ≫
        (smallEtaleBaseChange h).map ((absoluteFrobeniusPowEtaleSiteIso S p hS hn).inv.app U) :=
  hom_comp_inv_eq_of_triangle ((absoluteFrobeniusPowEtaleSiteIso S' p hS' hn).app _)
    ((smallEtaleBaseChangeComp' (absoluteFrobeniusPow S' p hS' n) h m hm').app U)
    ((smallEtaleBaseChangeComp' h (absoluteFrobeniusPow S p hS n) m hm).app U)
    ((smallEtaleBaseChange h).mapIso ((absoluteFrobeniusPowEtaleSiteIso S p hS hn).app U))
    (absoluteFrobeniusPowEtaleSiteIso_baseChange h p hS hS' hn m hm' hm U)

/-- **The Frobenius descent isomorphism commutes with direct images.** For `h : S' ⟶ S` and a
sheaf `M` on `S'_étale`, the direct image along `h` of `M ≅ (F_{S'}^n)_* M`, followed by
`h_* (F_{S'}^n)_* = (F_{S'}^n ≫ h)_*`, is `h_* M ≅ (F_S^n)_* h_* M` followed by
`(F_S^n)_* h_* = (h ≫ F_S^n)_*`. -/
@[sga "4½ Rapport 1.3"]
theorem smallEtalePushforward_map_etaleSheafPushforwardComparison (A : Type*) [Category* A]
    (M : Sheaf (smallEtaleTopology S') A) :
    (smallEtalePushforward h A).map ((etaleSheafPushforwardComparison S'
          (absoluteFrobeniusPow S' p hS' n) (absoluteFrobeniusPowEtaleSiteIso S' p hS' hn)
          A).hom.app M) ≫
        (smallEtalePushforwardComp' (absoluteFrobeniusPow S' p hS' n) h m hm' A).hom.app M =
      (etaleSheafPushforwardComparison S (absoluteFrobeniusPow S p hS n)
          (absoluteFrobeniusPowEtaleSiteIso S p hS hn) A).hom.app
          ((smallEtalePushforward h A).obj M) ≫
        (smallEtalePushforwardComp' h (absoluteFrobeniusPow S p hS n) m hm A).hom.app M := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  have hU := absoluteFrobeniusPowEtaleSiteIso_baseChange_inv h p hS hS' hn m hm' hm U.unop
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, smallEtalePushforwardComp'_hom_app_hom_app,
    smallEtalePushforwardComp'_hom_app_hom_app, Functor.sheafPushforwardContinuous_map_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app]
  exact map_op_comp_eq M.obj hU

section Composition

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) {a b : ℕ}
  (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)

/-- The `(a + b)`-fold absolute Frobenius is the `b`-fold one followed by the `a`-fold one. -/
lemma absoluteFrobeniusPow_add_eq_comp :
    absoluteFrobeniusPow S p hS (a + b) =
      absoluteFrobeniusPow S p hS b ≫ absoluteFrobeniusPow S p hS a := by
  simp only [absoluteFrobeniusPow, pow_add, End.mul_asHom]

omit hS in
/-- The `a`-fold absolute Frobenius followed by the `b`-fold one is the `(a + b)`-fold one. -/
lemma absoluteFrobeniusPow_comp_eq_add (X : Scheme.{u}) (hX : IsInCharacteristic X p) :
    absoluteFrobeniusPow X p hX a ≫ absoluteFrobeniusPow X p hX b =
      absoluteFrobeniusPow X p hX (a + b) := by
  rw [Nat.add_comm]
  simp only [absoluteFrobeniusPow, pow_add, End.mul_asHom]

/-- In a category, `eab ≫ pab = (ea ≫ eb ≫ i) ≫ pab` given six compatible factorizations of its
pieces. -/
private lemma frobeniusCompositionChain {D : Type*} [Category* D] {A B C E : D}
    (ea : A ⟶ B) (eb : B ⟶ C) (i : C ⟶ E) (pab : E ⟶ A) (qb : C ⟶ B) (qa : B ⟶ A)
    (fa : A ⟶ A) (fb : A ⟶ A) (fb' : B ⟶ B) (fab : A ⟶ A) (eab : A ⟶ E)
    (hi : i ≫ pab = qb ≫ qa) (hb : eb ≫ qb = fb') (hn : fb' ≫ qa = qa ≫ fb)
    (ha : ea ≫ qa = fa) (hc : fa ≫ fb = fab) (hab : eab ≫ pab = fab) :
    eab ≫ pab = (ea ≫ eb ≫ i) ≫ pab := by
  rw [hab, Category.assoc, Category.assoc, hi, ← Category.assoc eb, hb, hn, ← Category.assoc, ha,
    hc]

/-- **Composition law of the relative Frobenius identifications.** For an étale `U` over `S`, the
relative Frobenius of `U` for `F_S^{a + b}` is the one for `F_S^a`, followed by the one for
`F_S^b` of the base change of `U` along `F_S^a`, and the comparison of base changes along
`F_S^b ≫ F_S^a = F_S^{a + b}`. -/
lemma absoluteFrobeniusPowEtaleSiteIso_add (U : S.Etale) :
    (absoluteFrobeniusPowEtaleSiteIso S p hS hab).hom.app U =
      (absoluteFrobeniusPowEtaleSiteIso S p hS ha).hom.app U ≫
        (absoluteFrobeniusPowEtaleSiteIso S p hS hb).hom.app
          ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS a)).obj U) ≫
        (smallEtaleBaseChangeComp' (absoluteFrobeniusPow S p hS b) (absoluteFrobeniusPow S p hS a)
          (absoluteFrobeniusPow S p hS (a + b))
          (absoluteFrobeniusPow_add_eq_comp p hS)).inv.app U := by
  refine smallEtaleBaseChange_hom_ext _ ?_
  exact frobeniusCompositionChain _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleBaseChangeComp'_inv_fst (absoluteFrobeniusPow S p hS b)
      (absoluteFrobeniusPow S p hS a) _ (absoluteFrobeniusPow_add_eq_comp p hS) U)
    (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst S p hS hb
      ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS a)).obj U))
    (absoluteFrobeniusPow_naturality (pullback.fst U.hom (absoluteFrobeniusPow S p hS a)) p _ _ b)
    (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst S p hS ha U)
    (absoluteFrobeniusPow_comp_eq_add p U.left _)
    (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst S p hS hab U)

/-- The composition law, read with the inverses. -/
lemma absoluteFrobeniusPowEtaleSiteIso_add_inv (U : S.Etale) :
    (smallEtaleBaseChangeComp' (absoluteFrobeniusPow S p hS b) (absoluteFrobeniusPow S p hS a)
          (absoluteFrobeniusPow S p hS (a + b)) (absoluteFrobeniusPow_add_eq_comp p hS)).hom.app U ≫
        (absoluteFrobeniusPowEtaleSiteIso S p hS hb).inv.app
          ((smallEtaleBaseChange (absoluteFrobeniusPow S p hS a)).obj U) ≫
        (absoluteFrobeniusPowEtaleSiteIso S p hS ha).inv.app U =
      (absoluteFrobeniusPowEtaleSiteIso S p hS hab).inv.app U := by
  rw [← cancel_mono ((absoluteFrobeniusPowEtaleSiteIso S p hS hab).hom.app U),
    Iso.inv_hom_id_app, absoluteFrobeniusPowEtaleSiteIso_add p hS ha hb hab U]
  simp

/-- **Composition law of the Frobenius descent isomorphisms.** `M ≅ (F_S^{a + b})_* M` is
`M ≅ (F_S^a)_* M`, followed by `(F_S^a)_*` of `M ≅ (F_S^b)_* M` and the identification
`(F_S^a)_* (F_S^b)_* = (F_S^b ≫ F_S^a)_*`. -/
theorem etaleSheafPushforwardComparison_add (A : Type*) [Category* A]
    (M : Sheaf (smallEtaleTopology S) A) :
    (etaleSheafPushforwardComparison S (absoluteFrobeniusPow S p hS a)
          (absoluteFrobeniusPowEtaleSiteIso S p hS ha) A).hom.app M ≫
        (smallEtalePushforward (absoluteFrobeniusPow S p hS a) A).map
          ((etaleSheafPushforwardComparison S (absoluteFrobeniusPow S p hS b)
            (absoluteFrobeniusPowEtaleSiteIso S p hS hb) A).hom.app M) ≫
        (smallEtalePushforwardComp' (absoluteFrobeniusPow S p hS b) (absoluteFrobeniusPow S p hS a)
          (absoluteFrobeniusPow S p hS (a + b)) (absoluteFrobeniusPow_add_eq_comp p hS)
          A).hom.app M =
      (etaleSheafPushforwardComparison S (absoluteFrobeniusPow S p hS (a + b))
          (absoluteFrobeniusPowEtaleSiteIso S p hS hab) A).hom.app M := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  have hU := absoluteFrobeniusPowEtaleSiteIso_add_inv p hS ha hb hab U.unop
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, smallEtalePushforwardComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app]
  exact map_op_comp_comp_eq M.obj hU

end Composition

end Stacks.EtaleCohomology

end
