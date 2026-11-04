module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Transporting the compatibility of a composition isomorphism along a change of underived model

`Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp` compares the composition isomorphisms
of two models of a derived pullback.  Its hypothesis `h₂` is the compatibility of the composition
isomorphism of the *second* model with the comparisons of derived and underived pullback — but
read against the underived pullbacks of the *first* model, through identifications `χ` of the two
underived pullbacks and `κ` of the two localization functors.  That is not the shape in which such
a compatibility is proved: it is proved against the second model's own underived pullbacks.

This file transports the one into the other.  Given the compatibility `h'` in the second model's
own terms and the compatibility `hχ` of the identifications `χ` with the two underived composition
isomorphisms, the transported comparisons
```
t_f = L_f(κ_Y⁻¹) ≫ a_f ≫ Q'_X(χ_f⁻¹) ≫ κ_X
```
satisfy the compatibility against the first model's underived pullbacks.

## Main results

* `Stacks.CategoryTheory.ModelComparison.comp_comm_transported_app`: the hypothesis `h₂` of
  `Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`, from the same statement for the
  second model's own underived pullbacks and the underived compatibility of the identifications.
* `Stacks.CategoryTheory.ModelComparison.comp_comm_transported_factors`: the same, with every
  factor of the conclusion taken as a variable pinned down by its own pointwise hypothesis, so
  that no natural transformation appears in the interface.
* `Stacks.CategoryTheory.ModelComparison.transported_app`: the component of the transported
  comparison, from the whiskered shape it is built in.
* `Stacks.CategoryTheory.ModelComparison.comp_comm_transported`: the first result with the
  transported comparisons and the identifications `Θ` given in that shape instead.

## Why there are four

`Stacks.CategoryTheory.ModelComparison.comp_comm_transported_app` and
`Stacks.CategoryTheory.ModelComparison.comp_comm_transported` state the conclusion with the
transported comparisons as natural transformations, so a consumer whose two readings of the target
category are only definitionally equal has to identify them inside
`CategoryTheory.NatTrans.app`, where the elaborator does not finish.
`Stacks.CategoryTheory.ModelComparison.comp_comm_transported_factors` exists for that consumer:
it takes the four factors of the conclusion as variables, each pinned down by a pointwise
hypothesis the consumer already has, so each identification is paid where the factor is supplied.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.ModelComparison

variable {HX HY HZ H'X H'Y H'Z DX DY DZ D'X D'Y D'Z : Type*}
  [Category HX] [Category HY] [Category HZ] [Category H'X] [Category H'Y] [Category H'Z]
  [Category DX] [Category DY] [Category DZ] [Category D'X] [Category D'Y] [Category D'Z]
  {QX : HX ⥤ DX} {QY : HY ⥤ DY} {QZ : HZ ⥤ DZ}
  {Q'X : H'X ⥤ D'X} {Q'Y : H'Y ⥤ D'Y} {Q'Z : H'Z ⥤ D'Z}
  {JX : HX ⥤ H'X} {JY : HY ⥤ H'Y} {JZ : HZ ⥤ H'Z}
  {EX : DX ⥤ D'X} {EY : DY ⥤ D'Y} {EZ : DZ ⥤ D'Z}
  {pf : HY ⥤ HX} {pg : HZ ⥤ HY} {pc : HZ ⥤ HX}
  {p'f : H'Y ⥤ H'X} {p'g : H'Z ⥤ H'Y} {p'c : H'Z ⥤ H'X}
  {Lf : D'Y ⥤ D'X} {Lg : D'Z ⥤ D'Y} {Lc : D'Z ⥤ D'X}

/-- The inverse form of the compatibility of the identifications of the underived pullbacks with
the two underived composition isomorphisms. -/
theorem inv_app_comp_of_underived_comp
    {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    (hχ : ∀ M : HZ, χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M)
    (M : HZ) :
    e'.hom.app (JZ.obj M) ≫ χc.inv.app M =
      p'f.map (χg.inv.app M) ≫ χf.inv.app (pg.obj M) ≫ JX.map (e.hom.app M) := by
  rw [← cancel_epi (p'f.map (χg.hom.app M)), ← cancel_epi (χf.hom.app (pg.obj M)),
    reassoc_of% (hχ M), ← p'f.map_comp_assoc]
  simp

/-- The transported compatibility, with the comparisons written out. -/
private theorem comp_comm_transported_core
    {κX : JX ⋙ Q'X ≅ QX ⋙ EX} {κY : JY ⋙ Q'Y ≅ QY ⋙ EY} {κZ : JZ ⋙ Q'Z ≅ QZ ⋙ EZ}
    {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c} {C : Lc ≅ Lg ⋙ Lf}
    {af : Q'Y ⋙ Lf ⟶ p'f ⋙ Q'X} {ag : Q'Z ⋙ Lg ⟶ p'g ⋙ Q'Y} {ac : Q'Z ⋙ Lc ⟶ p'c ⋙ Q'X}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    (h' : ∀ N : H'Z, C.inv.app (Q'Z.obj N) ≫ ac.app N =
      Lf.map (ag.app N) ≫ af.app (p'g.obj N) ≫ Q'X.map (e'.hom.app N))
    (hχ : ∀ M : HZ, χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M) (M : HZ) :
    C.inv.app (EZ.obj (QZ.obj M)) ≫ (Lc.map (κZ.inv.app M) ≫ ac.app (JZ.obj M) ≫
      Q'X.map (χc.inv.app M) ≫ κX.hom.app (pc.obj M)) =
    Lf.map (Lg.map (κZ.inv.app M) ≫ ag.app (JZ.obj M) ≫
      Q'Y.map (χg.inv.app M) ≫ κY.hom.app (pg.obj M)) ≫
    (Lf.map (κY.inv.app (pg.obj M)) ≫ af.app (JY.obj (pg.obj M)) ≫
      Q'X.map (χf.inv.app (pg.obj M)) ≫ κX.hom.app (pf.obj (pg.obj M))) ≫
    EX.map (QX.map (e.hom.app M)) := by
  have nC := C.inv.naturality (κZ.inv.app M)
  have naf := af.naturality (χg.inv.app M)
  have nκX := κX.hom.naturality (e.hom.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at nC naf nκX
  rw [← reassoc_of% nC, reassoc_of% (h' (JZ.obj M)), ← Q'X.map_comp_assoc,
    inv_app_comp_of_underived_comp hχ M, Q'X.map_comp, Q'X.map_comp, Category.assoc,
    Category.assoc, nκX, Lf.map_comp, Lf.map_comp, Lf.map_comp]
  simp only [Category.assoc]
  rw [← Lf.map_comp_assoc (κY.hom.app (pg.obj M)) (κY.inv.app (pg.obj M)), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% naf]

/-- **The hypothesis `h₂` of `Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`, from the
compatibility in the second model's own terms.**

`κ` identifies the two localization functors, `χ` the two underived pullbacks, `e` and `e'` are
the underived composition isomorphisms, `C` the derived one of the second model, `a` its
comparisons of derived and underived pullback and `t` the transported comparisons, pinned down by
`htf`, `htg`, `htc`.  Then the compatibility `h'` of `C` with `a` and `e'` gives the compatibility
of `C` with `t` and `e`, as soon as `χ` is compatible with `e` and `e'` (`hχ`). -/
theorem comp_comm_transported_app
    {κX : JX ⋙ Q'X ≅ QX ⋙ EX} {κY : JY ⋙ Q'Y ≅ QY ⋙ EY} {κZ : JZ ⋙ Q'Z ≅ QZ ⋙ EZ}
    {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c} {C : Lc ≅ Lg ⋙ Lf}
    {af : Q'Y ⋙ Lf ⟶ p'f ⋙ Q'X} {ag : Q'Z ⋙ Lg ⟶ p'g ⋙ Q'Y} {ac : Q'Z ⋙ Lc ⟶ p'c ⋙ Q'X}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    {tf : QY ⋙ EY ⋙ Lf ⟶ pf ⋙ QX ⋙ EX} {tg : QZ ⋙ EZ ⋙ Lg ⟶ pg ⋙ QY ⋙ EY}
    {tc : QZ ⋙ EZ ⋙ Lc ⟶ pc ⋙ QX ⋙ EX}
    (htf : ∀ N : HY, tf.app N = Lf.map (κY.inv.app N) ≫ af.app (JY.obj N) ≫
      Q'X.map (χf.inv.app N) ≫ κX.hom.app (pf.obj N))
    (htg : ∀ M : HZ, tg.app M = Lg.map (κZ.inv.app M) ≫ ag.app (JZ.obj M) ≫
      Q'Y.map (χg.inv.app M) ≫ κY.hom.app (pg.obj M))
    (htc : ∀ M : HZ, tc.app M = Lc.map (κZ.inv.app M) ≫ ac.app (JZ.obj M) ≫
      Q'X.map (χc.inv.app M) ≫ κX.hom.app (pc.obj M))
    (h' : ∀ N : H'Z, C.inv.app (Q'Z.obj N) ≫ ac.app N =
      Lf.map (ag.app N) ≫ af.app (p'g.obj N) ≫ Q'X.map (e'.hom.app N))
    (hχ : ∀ M : HZ, χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M)
    (M : HZ) :
    C.inv.app (EZ.obj (QZ.obj M)) ≫ tc.app M =
      Lf.map (tg.app M) ≫ tf.app (pg.obj M) ≫ EX.map (QX.map (e.hom.app M)) := by
  rw [htc M, htf (pg.obj M), htg M]
  exact comp_comm_transported_core h' hχ M

/-- **The hypothesis `h₂` of `Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`, with
every component of the conclusion taken as a variable.**

Each of the four factors of the conclusion is a variable pinned down by its own hypothesis, and no
natural transformation appears in the interface: a consumer supplies its own spelling of each
factor and its own pointwise factorisation of it, so the identification of two definitionally
equal spellings of a category is paid once per factor, where the factor is supplied, and never
inside `CategoryTheory.NatTrans.app` in the conclusion. -/
theorem comp_comm_transported_factors
    {κX : JX ⋙ Q'X ≅ QX ⋙ EX} {κY : JY ⋙ Q'Y ≅ QY ⋙ EY} {κZ : JZ ⋙ Q'Z ≅ QZ ⋙ EZ}
    {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c} {C : Lc ≅ Lg ⋙ Lf}
    {af : Q'Y ⋙ Lf ⟶ p'f ⋙ Q'X} {ag : Q'Z ⋙ Lg ⟶ p'g ⋙ Q'Y} {ac : Q'Z ⋙ Lc ⟶ p'c ⋙ Q'X}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    (M : HZ)
    {s : Lc.obj (EZ.obj (QZ.obj M)) ⟶ EX.obj (QX.obj (pc.obj M))}
    (hs : s = Lc.map (κZ.inv.app M) ≫ ac.app (JZ.obj M) ≫
      Q'X.map (χc.inv.app M) ≫ κX.hom.app (pc.obj M))
    {r : Lg.obj (EZ.obj (QZ.obj M)) ⟶ EY.obj (QY.obj (pg.obj M))}
    (hr : r = Lg.map (κZ.inv.app M) ≫ ag.app (JZ.obj M) ≫
      Q'Y.map (χg.inv.app M) ≫ κY.hom.app (pg.obj M))
    {t : Lf.obj (EY.obj (QY.obj (pg.obj M))) ⟶ EX.obj (QX.obj (pf.obj (pg.obj M)))}
    (ht : t = Lf.map (κY.inv.app (pg.obj M)) ≫ af.app (JY.obj (pg.obj M)) ≫
      Q'X.map (χf.inv.app (pg.obj M)) ≫ κX.hom.app (pf.obj (pg.obj M)))
    {w : EX.obj (QX.obj (pf.obj (pg.obj M))) ⟶ EX.obj (QX.obj (pc.obj M))}
    (hw : w = EX.map (QX.map (e.hom.app M)))
    (h' : ∀ N : H'Z, C.inv.app (Q'Z.obj N) ≫ ac.app N =
      Lf.map (ag.app N) ≫ af.app (p'g.obj N) ≫ Q'X.map (e'.hom.app N))
    (hχ : ∀ M : HZ, χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M) :
    C.inv.app (EZ.obj (QZ.obj M)) ≫ s = Lf.map r ≫ t ≫ w := by
  subst hs hr ht hw
  exact comp_comm_transported_core h' hχ M

/-- **The transported comparison, componentwise.**  `Θf` is the identification of the two
readings of the underived pullback followed by localization, built out of the identification `k`
of the localization functors and the identification `χ` of the underived pullbacks; `tf` is the
comparison of the second model, transported along them.  The associators contribute identities,
so the component of `tf` is the four-fold composite the pointwise statements below are phrased
with. -/
theorem transported_app {kX : QX ⋙ EX ≅ JX ⋙ Q'X} {kY : QY ⋙ EY ≅ JY ⋙ Q'Y}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {af : Q'Y ⋙ Lf ⟶ p'f ⋙ Q'X}
    {Θf : (pf ⋙ QX) ⋙ EX ≅ JY ⋙ p'f ⋙ Q'X}
    (hΘf : Θf = Functor.associator pf QX EX ≪≫ Functor.isoWhiskerLeft pf kX ≪≫
      (Functor.associator pf JX Q'X).symm ≪≫ Functor.isoWhiskerRight χf Q'X ≪≫
      Functor.associator JY p'f Q'X)
    {tf : QY ⋙ EY ⋙ Lf ⟶ pf ⋙ QX ⋙ EX}
    (htf : tf = Functor.whiskerRight kY.hom Lf ≫ Functor.whiskerLeft JY af ≫ Θf.inv)
    (N : HY) :
    tf.app N = Lf.map (kY.hom.app N) ≫ af.app (JY.obj N) ≫
      Q'X.map (χf.inv.app N) ≫ kX.inv.app (pf.obj N) := by
  subst hΘf htf
  simp [Iso.trans_inv]

/-- **The hypothesis `h₂` of `Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`, from the
compatibility in the second model's own terms**, with the transported comparisons `t` and the
identifications `Θ` given in the shape they are built in rather than componentwise.  This is
`Stacks.CategoryTheory.ModelComparison.comp_comm_transported_app` with
`Stacks.CategoryTheory.ModelComparison.transported_app` supplying its pointwise hypotheses. -/
theorem comp_comm_transported
    {kX : QX ⋙ EX ≅ JX ⋙ Q'X} {kY : QY ⋙ EY ≅ JY ⋙ Q'Y} {kZ : QZ ⋙ EZ ≅ JZ ⋙ Q'Z}
    {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c} {C : Lc ≅ Lg ⋙ Lf}
    {af : Q'Y ⋙ Lf ⟶ p'f ⋙ Q'X} {ag : Q'Z ⋙ Lg ⟶ p'g ⋙ Q'Y} {ac : Q'Z ⋙ Lc ⟶ p'c ⋙ Q'X}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    {Θf : (pf ⋙ QX) ⋙ EX ≅ JY ⋙ p'f ⋙ Q'X}
    {Θg : (pg ⋙ QY) ⋙ EY ≅ JZ ⋙ p'g ⋙ Q'Y}
    {Θc : (pc ⋙ QX) ⋙ EX ≅ JZ ⋙ p'c ⋙ Q'X}
    (hΘf : Θf = Functor.associator pf QX EX ≪≫ Functor.isoWhiskerLeft pf kX ≪≫
      (Functor.associator pf JX Q'X).symm ≪≫ Functor.isoWhiskerRight χf Q'X ≪≫
      Functor.associator JY p'f Q'X)
    (hΘg : Θg = Functor.associator pg QY EY ≪≫ Functor.isoWhiskerLeft pg kY ≪≫
      (Functor.associator pg JY Q'Y).symm ≪≫ Functor.isoWhiskerRight χg Q'Y ≪≫
      Functor.associator JZ p'g Q'Y)
    (hΘc : Θc = Functor.associator pc QX EX ≪≫ Functor.isoWhiskerLeft pc kX ≪≫
      (Functor.associator pc JX Q'X).symm ≪≫ Functor.isoWhiskerRight χc Q'X ≪≫
      Functor.associator JZ p'c Q'X)
    {tf : QY ⋙ EY ⋙ Lf ⟶ pf ⋙ QX ⋙ EX} {tg : QZ ⋙ EZ ⋙ Lg ⟶ pg ⋙ QY ⋙ EY}
    {tc : QZ ⋙ EZ ⋙ Lc ⟶ pc ⋙ QX ⋙ EX}
    (htf : tf = Functor.whiskerRight kY.hom Lf ≫ Functor.whiskerLeft JY af ≫ Θf.inv)
    (htg : tg = Functor.whiskerRight kZ.hom Lg ≫ Functor.whiskerLeft JZ ag ≫ Θg.inv)
    (htc : tc = Functor.whiskerRight kZ.hom Lc ≫ Functor.whiskerLeft JZ ac ≫ Θc.inv)
    (h' : ∀ N : H'Z, C.inv.app (Q'Z.obj N) ≫ ac.app N =
      Lf.map (ag.app N) ≫ af.app (p'g.obj N) ≫ Q'X.map (e'.hom.app N))
    (hχ : ∀ M : HZ, χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M)
    (M : HZ) :
    C.inv.app (EZ.obj (QZ.obj M)) ≫ tc.app M =
      Lf.map (tg.app M) ≫ tf.app (pg.obj M) ≫ EX.map (QX.map (e.hom.app M)) :=
  comp_comm_transported_app (κX := kX.symm) (κY := kY.symm) (κZ := kZ.symm)
    (transported_app hΘf htf) (transported_app hΘg htg) (transported_app hΘc htc) h' hχ M

end Stacks.CategoryTheory.ModelComparison

end
