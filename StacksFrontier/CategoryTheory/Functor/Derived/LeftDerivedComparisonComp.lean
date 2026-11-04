module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Composition coherence of comparisons of left derived functors

Let `Φ_X : D_X ⥤ D'_X` be functors between two families of localized categories, `Q_X : K_X ⥤ D_X`
and `Q'_X : K'_X ⥤ D'_X`, compatible with functors `ι_X : K_X ⥤ K'_X`
(`F_X : Q_X ⋙ Φ_X ≅ ι_X ⋙ Q'_X`), and let `L_f`, `L'_f` be left derived functors of two families of
underived pullbacks `p_f`, `p'_f`, with comparisons `α_f`, `β_f`. A transformation
`μ_f : ι_Y ⋙ p'_f ⟶ p_f ⋙ ι_X` of the underived pullbacks induces, by the universal property of
`L_f ⋙ Φ_X`, a comparison `ε_f : Φ_Y ⋙ L'_f ⟶ L_f ⋙ Φ_X`. This file proves that the `ε_f` are
compatible with composition comparisons on both sides (in the shape of Stacks 0D6D) as soon as the
`μ_f` are compatible with the underived ones; and it gives the underived compatibility on
homotopy categories from the one on the categories of complexes' terms.

All statements are about arbitrary categories and functors, so that they can be applied to large
concrete functors without the elaboration of any comparison of their spellings.

## Main results

* `Stacks.LeftDerivedComparisonComp.comparisonCompCompatible_of_characterized`: the composition
  coherence of the comparisons `ε_f`.
* `Stacks.LeftDerivedComparisonComp.invComparisonCompCompatible_of_comparisonCompCompatible`: the
  same for isomorphisms whose inverses are the `ε_f`.
* `Stacks.LeftDerivedComparisonComp.mapHomotopyCategory_underivedCompCompatible`: the underived
  compatibility on homotopy categories, from the one on the categories of terms.

The statements are phrased through the propositions
`Stacks.LeftDerivedComparisonComp.CompCounitCompatible`,
`Stacks.LeftDerivedComparisonComp.UnderivedCompCompatible`,
`Stacks.LeftDerivedComparisonComp.ComparisonCharacterized`,
`Stacks.LeftDerivedComparisonComp.ComparisonCompCompatible` and
`Stacks.LeftDerivedComparisonComp.InvComparisonCompCompatible`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.LeftDerivedComparisonComp

section Props

/-- The comparisons `α` of two derived pullbacks and of the derived pullback along the composite
characterize the composition comparison `c : L_g ⋙ L_f ⟶ L_{fg}` through the underived composition
comparison `κ`: `c ≫ α_{fg} = L_f(α_g) ≫ α_f ≫ Q_X(κ)` at the images of objects. -/
def CompCounitCompatible {KX KY KZ DX DY DZ : Type*} [Category* KX] [Category* KY]
    [Category* KZ] [Category* DX] [Category* DY] [Category* DZ] {QX : KX ⥤ DX} {QY : KY ⥤ DY}
    {QZ : KZ ⥤ DZ} {pf : KY ⥤ KX} {pg : KZ ⥤ KY} {pfg : KZ ⥤ KX} {Lf : DY ⥤ DX}
    {Lg : DZ ⥤ DY} {Lfg : DZ ⥤ DX} (c : Lg ⋙ Lf ⟶ Lfg) (αf : QY ⋙ Lf ⟶ pf ⋙ QX)
    (αg : QZ ⋙ Lg ⟶ pg ⋙ QY) (αfg : QZ ⋙ Lfg ⟶ pfg ⋙ QX) (κ : pg ⋙ pf ⟶ pfg) : Prop :=
  ∀ M, c.app (QZ.obj M) ≫ αfg.app M = Lf.map (αg.app M) ≫ αf.app (pg.obj M) ≫ QX.map (κ.app M)

/-- Transformations `κ_f : ι_Y ⋙ q_f ⟶ m_f ⋙ ι_X` intertwining two families of pullbacks are
compatible with the composition comparisons `cq : q_g ⋙ q_f ⟶ q_{fg}` and
`mc : m_g ⋙ m_f ⟶ m_{fg}`: `cq ≫ κ_{fg} = q_f(κ_g) ≫ κ_f ≫ ι_X(mc)`. -/
def UnderivedCompCompatible {AX AY AZ BX BY BZ : Type*} [Category* AX] [Category* AY]
    [Category* AZ] [Category* BX] [Category* BY] [Category* BZ] {ιX : AX ⥤ BX} {ιY : AY ⥤ BY}
    {ιZ : AZ ⥤ BZ} {qf : BY ⥤ BX} {qg : BZ ⥤ BY} {qfg : BZ ⥤ BX} {mf : AY ⥤ AX}
    {mg : AZ ⥤ AY} {mfg : AZ ⥤ AX} (cq : qg ⋙ qf ⟶ qfg) (κf : ιY ⋙ qf ⟶ mf ⋙ ιX)
    (κg : ιZ ⋙ qg ⟶ mg ⋙ ιY) (κfg : ιZ ⋙ qfg ⟶ mfg ⋙ ιX) (mc : mg ⋙ mf ⟶ mfg) : Prop :=
  ∀ N, cq.app (ιZ.obj N) ≫ κfg.app N = qf.map (κg.app N) ≫ κf.app (mg.obj N) ≫ ιX.map (mc.app N)

/-- A comparison `ε_f : Φ_Y ⋙ L'_f ⟶ L_f ⋙ Φ_X` of two derived pullbacks is characterized
through their comparisons `α_f`, `β_f` by a transformation `μ_f : ι_Y ⋙ p'_f ⟶ p_f ⋙ ι_X` of the
underived ones and the compatibilities `F` of `Φ` with `ι`. -/
def ComparisonCharacterized {KX KY DX DY K'X K'Y D'X D'Y : Type*} [Category* KX]
    [Category* KY] [Category* DX] [Category* DY] [Category* K'X] [Category* K'Y] [Category* D'X]
    [Category* D'Y] {QX : KX ⥤ DX} {QY : KY ⥤ DY} {Q'X : K'X ⥤ D'X} {Q'Y : K'Y ⥤ D'Y}
    {ΦX : DX ⥤ D'X} {ΦY : DY ⥤ D'Y} {ιX : KX ⥤ K'X} {ιY : KY ⥤ K'Y} {pf : KY ⥤ KX}
    {Lf : DY ⥤ DX} {p'f : K'Y ⥤ K'X} {L'f : D'Y ⥤ D'X} (FX : QX ⋙ ΦX ≅ ιX ⋙ Q'X)
    (FY : QY ⋙ ΦY ≅ ιY ⋙ Q'Y) (αf : QY ⋙ Lf ⟶ pf ⋙ QX) (βf : Q'Y ⋙ L'f ⟶ p'f ⋙ Q'X)
    (μf : ιY ⋙ p'f ⟶ pf ⋙ ιX) (εf : ΦY ⋙ L'f ⟶ Lf ⋙ ΦX) : Prop :=
  ∀ M, εf.app (QY.obj M) ≫ ((Functor.associator QY Lf ΦX).inv ≫ Functor.whiskerRight αf ΦX).app M =
    L'f.map (FY.hom.app M) ≫ βf.app (ιY.obj M) ≫ Q'X.map (μf.app M) ≫ FX.inv.app (pf.obj M)

/-- Comparisons `ε_f : Φ_Y ⋙ L'_f ⟶ L_f ⋙ Φ_X` are compatible with composition comparisons
`c : L_g ⋙ L_f ⟶ L_{fg}` and `c' : L'_g ⋙ L'_f ⟶ L'_{fg}`:
`c' ≫ ε_{fg} = L'_f(ε_g) ≫ ε_f ≫ Φ_X(c)`. -/
def ComparisonCompCompatible {DX DY DZ D'X D'Y D'Z : Type*} [Category* DX] [Category* DY]
    [Category* DZ] [Category* D'X] [Category* D'Y] [Category* D'Z] {ΦX : DX ⥤ D'X}
    {ΦY : DY ⥤ D'Y} {ΦZ : DZ ⥤ D'Z} {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lfg : DZ ⥤ DX}
    {L'f : D'Y ⥤ D'X} {L'g : D'Z ⥤ D'Y} {L'fg : D'Z ⥤ D'X} (c' : L'g ⋙ L'f ⟶ L'fg)
    (εf : ΦY ⋙ L'f ⟶ Lf ⋙ ΦX) (εg : ΦZ ⋙ L'g ⟶ Lg ⋙ ΦY) (εfg : ΦZ ⋙ L'fg ⟶ Lfg ⋙ ΦX)
    (c : Lg ⋙ Lf ⟶ Lfg) : Prop :=
  ∀ K, c'.app (ΦZ.obj K) ≫ εfg.app K = L'f.map (εg.app K) ≫ εf.app (Lg.obj K) ≫ ΦX.map (c.app K)

/-- Isomorphisms `E_f : L_f ⋙ Φ_X ≅ Φ_Y ⋙ L'_f` are compatible with composition isomorphisms
`e : L_{fg} ≅ L_g ⋙ L_f` and `e' : L'_{fg} ≅ L'_g ⋙ L'_f`:
`E_{fg} ≫ e' = Φ_X(e) ≫ E_f ≫ L'_f(E_g)`, the shape of the composition coherence of Stacks 0D6D. -/
def InvComparisonCompCompatible {DX DY DZ D'X D'Y D'Z : Type*} [Category* DX] [Category* DY]
    [Category* DZ] [Category* D'X] [Category* D'Y] [Category* D'Z] {ΦX : DX ⥤ D'X}
    {ΦY : DY ⥤ D'Y} {ΦZ : DZ ⥤ D'Z} {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lfg : DZ ⥤ DX}
    {L'f : D'Y ⥤ D'X} {L'g : D'Z ⥤ D'Y} {L'fg : D'Z ⥤ D'X} (Ef : Lf ⋙ ΦX ≅ ΦY ⋙ L'f)
    (Eg : Lg ⋙ ΦY ≅ ΦZ ⋙ L'g) (Efg : Lfg ⋙ ΦX ≅ ΦZ ⋙ L'fg) (e : Lfg ≅ Lg ⋙ Lf)
    (e' : L'fg ≅ L'g ⋙ L'f) : Prop :=
  ∀ K, Efg.hom.app K ≫ e'.hom.app (ΦZ.obj K) =
    ΦX.map (e.hom.app K) ≫ Ef.hom.app (Lg.obj K) ≫ L'f.map (Eg.hom.app K)

end Props

section Derived

variable {KX KY KZ DX DY DZ K'X K'Y K'Z D'X D'Y D'Z : Type*}
  [Category* KX] [Category* KY] [Category* KZ] [Category* DX] [Category* DY] [Category* DZ]
  [Category* K'X] [Category* K'Y] [Category* K'Z] [Category* D'X] [Category* D'Y] [Category* D'Z]
  {QX : KX ⥤ DX} {QY : KY ⥤ DY} {QZ : KZ ⥤ DZ}
  {Q'X : K'X ⥤ D'X} {Q'Y : K'Y ⥤ D'Y} {Q'Z : K'Z ⥤ D'Z}
  {ΦX : DX ⥤ D'X} {ΦY : DY ⥤ D'Y} {ΦZ : DZ ⥤ D'Z}
  {ιX : KX ⥤ K'X} {ιY : KY ⥤ K'Y} {ιZ : KZ ⥤ K'Z}
  {pf : KY ⥤ KX} {pg : KZ ⥤ KY} {pfg : KZ ⥤ KX}
  {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lfg : DZ ⥤ DX}
  {p'f : K'Y ⥤ K'X} {p'g : K'Z ⥤ K'Y} {p'fg : K'Z ⥤ K'X}
  {L'f : D'Y ⥤ D'X} {L'g : D'Z ⥤ D'Y} {L'fg : D'Z ⥤ D'X}

/-- **The comparisons of two families of left derived functors are compatible with the
composition comparisons.** In the notation of the module docstring, let `c : L_g ⋙ L_f ⟶ L_{fg}`
and `c' : L'_g ⋙ L'_f ⟶ L'_{fg}` be characterized through the comparisons by the underived
composition comparisons `κ` and `κ'`, let the `μ` be compatible with `κ` and `κ'`, and let each
`ε` be characterized by `μ` through the comparisons and `F`. Then
`c' ∘ ε_{fg} = L'_f(ε_g) ∘ ε_f ∘ Φ_X(c)` at every object, `L_{fg} ⋙ Φ_X` being a left derived
functor. -/
theorem comparisonCompCompatible_of_characterized
    (FX : QX ⋙ ΦX ≅ ιX ⋙ Q'X) (FY : QY ⋙ ΦY ≅ ιY ⋙ Q'Y) (FZ : QZ ⋙ ΦZ ≅ ιZ ⋙ Q'Z)
    (αf : QY ⋙ Lf ⟶ pf ⋙ QX) (αg : QZ ⋙ Lg ⟶ pg ⋙ QY) (αfg : QZ ⋙ Lfg ⟶ pfg ⋙ QX)
    (κ : pg ⋙ pf ⟶ pfg) (c : Lg ⋙ Lf ⟶ Lfg) (hc : CompCounitCompatible c αf αg αfg κ)
    (βf : Q'Y ⋙ L'f ⟶ p'f ⋙ Q'X) (βg : Q'Z ⋙ L'g ⟶ p'g ⋙ Q'Y) (βfg : Q'Z ⋙ L'fg ⟶ p'fg ⋙ Q'X)
    (κ' : p'g ⋙ p'f ⟶ p'fg) (c' : L'g ⋙ L'f ⟶ L'fg) (hc' : CompCounitCompatible c' βf βg βfg κ')
    (μf : ιY ⋙ p'f ⟶ pf ⋙ ιX) (μg : ιZ ⋙ p'g ⟶ pg ⋙ ιY) (μfg : ιZ ⋙ p'fg ⟶ pfg ⋙ ιX)
    (hμ : UnderivedCompCompatible κ' μf μg μfg κ)
    (εf : ΦY ⋙ L'f ⟶ Lf ⋙ ΦX) (εg : ΦZ ⋙ L'g ⟶ Lg ⋙ ΦY) (εfg : ΦZ ⋙ L'fg ⟶ Lfg ⋙ ΦX)
    (hεf : ComparisonCharacterized FX FY αf βf μf εf)
    (hεg : ComparisonCharacterized FY FZ αg βg μg εg)
    (hεfg : ComparisonCharacterized FX FZ αfg βfg μfg εfg)
    (W : MorphismProperty KZ) [QZ.IsLocalization W]
    (hL : (Lfg ⋙ ΦX).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight αfg ΦX) W) :
    ComparisonCompCompatible c' εf εg εfg c := by
  intro K
  unfold CompCounitCompatible at hc hc'
  unfold UnderivedCompCompatible at hμ
  unfold ComparisonCharacterized at hεf hεg hεfg
  have h := Functor.leftDerived_ext (Lfg ⋙ ΦX)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight αfg ΦX) W (ΦZ ⋙ L'g ⋙ L'f)
    (Functor.whiskerLeft ΦZ c' ≫ εfg)
    ((Functor.associator ΦZ L'g L'f).inv ≫ Functor.whiskerRight εg L'f ≫
      (Functor.associator Lg ΦY L'f).hom ≫ Functor.whiskerLeft Lg εf ≫
      (Functor.associator Lg Lf ΦX).inv ≫ Functor.whiskerRight c ΦX) (by
    ext M
    simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.id_comp] at hεf hεg hεfg
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    have n1 := εf.naturality (αg.app M)
    have n2 := FX.inv.naturality (κ.app M)
    have n3 := βf.naturality (μg.app M)
    have n4 := c'.naturality (FZ.hom.app M)
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4
    conv_lhs => rw [hεfg, ← reassoc_of% n4, reassoc_of% (hc' (ιZ.obj M)), ← Q'X.map_comp_assoc, hμ]
    conv_rhs => rw [← ΦX.map_comp, hc, ΦX.map_comp, ΦX.map_comp, ← reassoc_of% n1,
      ← L'f.map_comp_assoc (εg.app (QZ.obj M)), hεg, reassoc_of% (hεf (pg.obj M)), ← n2]
    simp only [Functor.map_comp, Category.assoc]
    rw [← L'f.map_comp_assoc (FY.inv.app (pg.obj M)), Iso.inv_hom_id_app, L'f.map_id,
      Category.id_comp, reassoc_of% n3])
  have := NatTrans.congr_app h K
  simpa only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc] using this

/-- **The inverse comparisons are compatible with the composition isomorphisms**: if
isomorphisms `E_f : L_f ⋙ Φ_X ≅ Φ_Y ⋙ L'_f` have inverses compatible with the inverses of
composition isomorphisms `e` and `e'` (`ComparisonCompCompatible`), then the `E_f` are compatible
with `e` and `e'`. -/
theorem invComparisonCompCompatible_of_comparisonCompCompatible
    (Ef : Lf ⋙ ΦX ≅ ΦY ⋙ L'f) (Eg : Lg ⋙ ΦY ≅ ΦZ ⋙ L'g) (Efg : Lfg ⋙ ΦX ≅ ΦZ ⋙ L'fg)
    (e : Lfg ≅ Lg ⋙ Lf) (e' : L'fg ≅ L'g ⋙ L'f)
    (h : ComparisonCompCompatible e'.inv Ef.inv Eg.inv Efg.inv e.inv) :
    InvComparisonCompCompatible Ef Eg Efg e e' := by
  intro K
  rw [← cancel_epi (e'.inv.app (ΦZ.obj K) ≫ Efg.inv.app K)]
  conv_rhs => rw [h K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← ΦX.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  rw [← L'f.map_comp, Iso.inv_hom_id_app]
  exact (L'f.map_id _).symm

end Derived

section Homotopy

variable {AX AY AZ BX BY BZ : Type*}
  [Category* AX] [Category* AY] [Category* AZ] [Category* BX] [Category* BY] [Category* BZ]
  [Preadditive AX] [Preadditive AY] [Preadditive AZ]
  [Preadditive BX] [Preadditive BY] [Preadditive BZ]
  {ιX : AX ⥤ BX} {ιY : AY ⥤ BY} {ιZ : AZ ⥤ BZ} [ιX.Additive] [ιY.Additive] [ιZ.Additive]
  {qf : BY ⥤ BX} {qg : BZ ⥤ BY} {qfg : BZ ⥤ BX} [qf.Additive] [qg.Additive] [qfg.Additive]
  {mf : AY ⥤ AX} {mg : AZ ⥤ AY} {mfg : AZ ⥤ AX}
  {tf : AY ⥤ AX} {tg : AZ ⥤ AY} {tfg : AZ ⥤ AX} [tf.Additive] [tg.Additive] [tfg.Additive]

omit [Preadditive AX] [Preadditive AY] [Preadditive AZ] [Preadditive BX] [Preadditive BY]
  [Preadditive BZ] [ιX.Additive] [ιY.Additive] [ιZ.Additive] [qf.Additive] [qg.Additive]
  [qfg.Additive] [tf.Additive] [tg.Additive] [tfg.Additive] in
/-- **Transport along equalities of the underived pullbacks.** Isomorphisms
`j_f : ι_Y ⋙ q_f ≅ t_f ⋙ ι_X` which are transformations `κ_f : ι_Y ⋙ q_f ⟶ m_f ⋙ ι_X` followed by
the transport along equalities `t_f = m_f`, are compatible with a composition comparison `ct`
transported from `mc` as soon as the `κ_f` are compatible with `mc`. -/
theorem underivedCompCompatible_of_eq (hf : tf = mf) (hg : tg = mg) (hfg : tfg = mfg)
    (κf : ιY ⋙ qf ⟶ mf ⋙ ιX) (κg : ιZ ⋙ qg ⟶ mg ⋙ ιY) (κfg : ιZ ⋙ qfg ⟶ mfg ⋙ ιX)
    (jf : ιY ⋙ qf ≅ tf ⋙ ιX) (jg : ιZ ⋙ qg ≅ tg ⋙ ιY) (jfg : ιZ ⋙ qfg ≅ tfg ⋙ ιX)
    (hjf : jf.hom = κf ≫ Functor.whiskerRight (eqToHom hf.symm) ιX)
    (hjg : jg.hom = κg ≫ Functor.whiskerRight (eqToHom hg.symm) ιY)
    (hjfg : jfg.hom = κfg ≫ Functor.whiskerRight (eqToHom hfg.symm) ιX)
    (cq : qg ⋙ qf ≅ qfg) (cq' : qg ⋙ qf ≅ qfg) (hcq : cq = cq')
    (mc : mg ⋙ mf ≅ mfg) (ct : tfg ≅ tg ⋙ tf)
    (hct : ct = eqToIso hfg ≪≫ mc.symm ≪≫ eqToIso (by rw [hf, hg]))
    (key : UnderivedCompCompatible cq'.hom κf κg κfg mc.hom) :
    UnderivedCompCompatible cq.hom jf.hom jg.hom jfg.hom ct.inv := by
  subst hf hg hfg hcq hct
  intro N
  have key := key N
  rw [hjf, hjg, hjfg]
  simp only [eqToHom_refl, Functor.whiskerRight_id', Category.comp_id, Iso.trans_inv,
    eqToIso_refl, Iso.refl_inv, Iso.symm_inv, Category.id_comp, key]

omit [ιX.Additive] [ιY.Additive] [ιZ.Additive] [qf.Additive] [qg.Additive] [qfg.Additive]
  [tf.Additive] [tg.Additive] [tfg.Additive] in
private theorem mapHomotopyCategoryCompIso_hom_app_quotient_obj' {A B C : Type*} [Category* A]
    [Category* B] [Category* C] [Preadditive A] [Preadditive B] [Preadditive C] {F : A ⥤ B}
    {G : B ⥤ C} {H : A ⥤ C} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (c : ComplexShape ℤ) (K : HomologicalComplex A c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient C c).map ((Functor.mapHomologicalComplexCompIso e c).hom.app K) :=
  rfl

omit [ιX.Additive] [ιY.Additive] [ιZ.Additive] [qf.Additive] [qg.Additive] [qfg.Additive]
  [tf.Additive] [tg.Additive] [tfg.Additive] in
private theorem mapHomotopyCategoryCompIso_inv_app_quotient_obj' {A B C : Type*} [Category* A]
    [Category* B] [Category* C] [Preadditive A] [Preadditive B] [Preadditive C] {F : A ⥤ B}
    {G : B ⥤ C} {H : A ⥤ C} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (c : ComplexShape ℤ) (K : HomologicalComplex A c) :
    (Functor.mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient C c).map ((Functor.mapHomologicalComplexCompIso e c).inv.app K) :=
  rfl

omit [ιX.Additive] [ιY.Additive] [ιZ.Additive] [qf.Additive] [qg.Additive] [qfg.Additive]
  [tf.Additive] [tg.Additive] [tfg.Additive] in
private theorem mapHomotopyCategoryIso_inv_app_quotient_obj' {A B : Type*} [Category* A]
    [Category* B] [Preadditive A] [Preadditive B] {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ℤ) (K : HomologicalComplex A c) :
    (Stacks.Homology.mapHomotopyCategoryIso e c).inv.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient B c).map ((NatTrans.mapHomologicalComplex e.inv c).app K) :=
  rfl

omit [ιX.Additive] [ιY.Additive] [ιZ.Additive] [qf.Additive] [qg.Additive] [qfg.Additive]
  [tf.Additive] [tg.Additive] [tfg.Additive] in
private theorem mapHomotopyCategory_obj_quotient_obj' {A B : Type*} [Category* A]
    [Category* B] [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (c : ComplexShape ℤ) (K : HomologicalComplex A c) :
    (F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient B c).obj ((F.mapHomologicalComplex c).obj K) :=
  rfl

/-- `mapHomotopyCategory_underivedCompCompatible` at the image of a complex. -/
private theorem mapHomotopyCategory_underivedCompCompatible_quotient (c : ComplexShape ℤ)
    (hf : tf = mf) (hg : tg = mg) (hfg : tfg = mfg)
    (κf : ιY ⋙ qf ⟶ mf ⋙ ιX) (κg : ιZ ⋙ qg ⟶ mg ⋙ ιY) (κfg : ιZ ⋙ qfg ⟶ mfg ⋙ ιX)
    (jf : ιY ⋙ qf ≅ tf ⋙ ιX) (jg : ιZ ⋙ qg ≅ tg ⋙ ιY) (jfg : ιZ ⋙ qfg ≅ tfg ⋙ ιX)
    (hjf : jf.hom = κf ≫ Functor.whiskerRight (eqToHom hf.symm) ιX)
    (hjg : jg.hom = κg ≫ Functor.whiskerRight (eqToHom hg.symm) ιY)
    (hjfg : jfg.hom = κfg ≫ Functor.whiskerRight (eqToHom hfg.symm) ιX)
    (cq : qg ⋙ qf ≅ qfg) (cq' : qg ⋙ qf ≅ qfg) (hcq : cq = cq')
    (mc : mg ⋙ mf ≅ mfg) (ct : tfg ≅ tg ⋙ tf)
    (hct : ct = eqToIso hfg ≪≫ mc.symm ≪≫ eqToIso (by rw [hf, hg]))
    (key : UnderivedCompCompatible cq'.hom κf κg κfg mc.hom)
    (cqh : qg.mapHomotopyCategory c ⋙ qf.mapHomotopyCategory c ≅ qfg.mapHomotopyCategory c)
    (hcqh : cqh = Functor.mapHomotopyCategoryCompIso cq c)
    (K : HomologicalComplex AZ c) :
    cqh.hom.app
          ((ιZ.mapHomotopyCategory c).obj ((HomotopyCategory.quotient AZ c).obj K)) ≫
        (Functor.mapHomotopyCategoryCompIso jfg c ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (tfg ⋙ ιX)) c).symm).hom.app
            ((HomotopyCategory.quotient AZ c).obj K) =
      (qf.mapHomotopyCategory c).map ((Functor.mapHomotopyCategoryCompIso jg c ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (tg ⋙ ιY)) c).symm).hom.app
            ((HomotopyCategory.quotient AZ c).obj K)) ≫
        (Functor.mapHomotopyCategoryCompIso jf c ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (tf ⋙ ιX)) c).symm).hom.app
            ((tg.mapHomotopyCategory c).obj ((HomotopyCategory.quotient AZ c).obj K)) ≫
        (ιX.mapHomotopyCategory c).map ((Stacks.Homology.mapHomotopyCategoryIso ct c ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (tg ⋙ tf)) c).symm).inv.app
            ((HomotopyCategory.quotient AZ c).obj K)) := by
  have hN := underivedCompCompatible_of_eq hf hg hfg κf κg κfg jf jg jfg hjf hjg hjfg cq cq' hcq
    mc ct hct key
  subst hcqh
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    mapHomotopyCategory_obj_quotient_obj', mapHomotopyCategoryCompIso_hom_app_quotient_obj',
    mapHomotopyCategoryCompIso_inv_app_quotient_obj', mapHomotopyCategoryIso_inv_app_quotient_obj',
    Functor.mapHomotopyCategory_map, Functor.comp_obj]
  simp only [← Functor.map_comp]
  congr 1
  ext n
  have h2 : cq.hom.app (ιZ.obj (K.X n)) ≫ jfg.hom.app (K.X n) ≫ 𝟙 _ =
      qf.map (jg.hom.app (K.X n) ≫ 𝟙 _) ≫ (jf.hom.app (tg.obj (K.X n)) ≫ 𝟙 _) ≫
        ιX.map (𝟙 _ ≫ ct.inv.app (K.X n)) := by
    simp only [Category.comp_id, Category.id_comp, hN (K.X n)]
  exact h2

/-- **The underived compatibility on homotopy categories.** In the situation of
`underivedCompCompatible_of_eq` (isomorphisms `j` of additive functors, written through
transformations `κ` and equalities `t = m`), the isomorphisms induced by the `j` on homotopy
categories (as in `CategoryTheory.Functor.mapHomotopyCategoryCompIso`) are compatible with the
composition comparisons induced by `cq` (in any presentation `cqh`) and `ct`. -/
theorem mapHomotopyCategory_underivedCompCompatible (c : ComplexShape ℤ)
    (hf : tf = mf) (hg : tg = mg) (hfg : tfg = mfg)
    (κf : ιY ⋙ qf ⟶ mf ⋙ ιX) (κg : ιZ ⋙ qg ⟶ mg ⋙ ιY) (κfg : ιZ ⋙ qfg ⟶ mfg ⋙ ιX)
    (jf : ιY ⋙ qf ≅ tf ⋙ ιX) (jg : ιZ ⋙ qg ≅ tg ⋙ ιY) (jfg : ιZ ⋙ qfg ≅ tfg ⋙ ιX)
    (hjf : jf.hom = κf ≫ Functor.whiskerRight (eqToHom hf.symm) ιX)
    (hjg : jg.hom = κg ≫ Functor.whiskerRight (eqToHom hg.symm) ιY)
    (hjfg : jfg.hom = κfg ≫ Functor.whiskerRight (eqToHom hfg.symm) ιX)
    (cq : qg ⋙ qf ≅ qfg) (cq' : qg ⋙ qf ≅ qfg) (hcq : cq = cq')
    (mc : mg ⋙ mf ≅ mfg) (ct : tfg ≅ tg ⋙ tf)
    (hct : ct = eqToIso hfg ≪≫ mc.symm ≪≫ eqToIso (by rw [hf, hg]))
    (key : UnderivedCompCompatible cq'.hom κf κg κfg mc.hom)
    (cqh : qg.mapHomotopyCategory c ⋙ qf.mapHomotopyCategory c ≅ qfg.mapHomotopyCategory c)
    (hcqh : cqh = Functor.mapHomotopyCategoryCompIso cq c) :
    UnderivedCompCompatible cqh.hom
      (Functor.mapHomotopyCategoryCompIso jf c ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (tf ⋙ ιX)) c).symm).hom
      (Functor.mapHomotopyCategoryCompIso jg c ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (tg ⋙ ιY)) c).symm).hom
      (Functor.mapHomotopyCategoryCompIso jfg c ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (tfg ⋙ ιX)) c).symm).hom
      (Stacks.Homology.mapHomotopyCategoryIso ct c ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (tg ⋙ tf)) c).symm).inv :=
  fun M => mapHomotopyCategory_underivedCompCompatible_quotient c hf hg hfg κf κg κfg jf jg jfg
    hjf hjg hjfg cq cq' hcq mc ct hct key cqh hcqh M.as

end Homotopy

end Stacks.LeftDerivedComparisonComp

end
