module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates commute with comparisons from models

Consider two squares of categories of the same shape: a *model* square, of categories `H_•`,
and a square of categories `C_•` receiving functors `Q_• : H_• ⥤ C_•` from the model square.
In each square there are two horizontal left adjoints `E ⊣ Lu`, `E' ⊣ Lu'`, and two vertical
functors `Lt'`, `Lt`, together with a 2-cell `σ : Lu ⋙ Lt' ⟶ Lt ⋙ Lu'`, and the mate
`β : Lt' ⋙ E' ⟶ E ⋙ Lt` of `σ`.  The typical example is a square of derived categories, modelled
on a square of homotopy categories by the localization functors, the vertical functors of the
first being left derived functors of those of the second.

Suppose that the functors of the two squares are compared by natural transformations
`c : Q ⋙ L ⟶ h ⋙ Q`, invertible for the right adjoint `Lu'`, and by natural isomorphisms
`e : Q ⋙ E ≅ hE ⋙ Q` for the left adjoints; that the units of the adjunctions are compatible with
these comparisons; and that the 2-cells `σ` and `hσ` are compatible with them.  Then the mates
`β` and `hβ` are compatible with them too: `CategoryTheory.Adjunction.mateEquiv_symm_app_comp`.

The statement is pure adjunction calculus; it is what reduces a base change map of derived
functors, evaluated at an object coming from the model, to the base change map of the model.

## Main results

* `CategoryTheory.Adjunction.mateEquiv_symm_app_comp`: the compatibility of the two mates with
  the comparisons.
* `CategoryTheory.Adjunction.mateEquiv_symm_app_comp_of_eq`: the same, for natural
  transformations given together with equations identifying them with the two mates.
* `CategoryTheory.Iso.hom_inv_app_comp_eq_of_comparisons`: the compatibility hypothesis on the
  2-cells, for a 2-cell `α ≫ β⁻¹` built from two identifications `α`, `β` of composites with a
  third functor, from the compatibilities of `α` and `β`.

## Implementation notes

The variants taking natural transformations and equations let a consumer whose mates, 2-cells or
adjunctions are named definitions discharge the identifications by `rfl` once, at the level of
natural transformations, and receive a statement mentioning its definitions rather than their
unfolded bodies.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {CU : Type u₁} {CT' : Type u₂} {CT : Type u₃} {CZ : Type u₄}
  [Category.{v₁} CU] [Category.{v₂} CT'] [Category.{v₃} CT] [Category.{v₄} CZ]
  {HU : Type u₅} {HT' : Type u₆} {HT : Type u₇} {HZ : Type u₈}
  [Category.{v₅} HU] [Category.{v₆} HT'] [Category.{v₇} HT] [Category.{v₈} HZ]
  {QU : HU ⥤ CU} {QT' : HT' ⥤ CT'} {QT : HT ⥤ CT} {QZ : HZ ⥤ CZ}
  {Lt' : CU ⥤ CT'} {Lt : CZ ⥤ CT} {Lu : CZ ⥤ CU} {Lu' : CT ⥤ CT'}
  {E : CU ⥤ CZ} {E' : CT' ⥤ CT} (adj : E ⊣ Lu) (adj' : E' ⊣ Lu')
  {ht' : HU ⥤ HT'} {ht : HZ ⥤ HT} {hu : HZ ⥤ HU} {hu' : HT ⥤ HT'}
  {hE : HU ⥤ HZ} {hE' : HT' ⥤ HT} (hadj : hE ⊣ hu) (hadj' : hE' ⊣ hu')
  (ct' : QU ⋙ Lt' ⟶ ht' ⋙ QT') (ct : QZ ⋙ Lt ⟶ ht ⋙ QT) (cu : QZ ⋙ Lu ⟶ hu ⋙ QU)
  (cu' : QT ⋙ Lu' ⟶ hu' ⋙ QT') [IsIso cu']
  (e : QU ⋙ E ≅ hE ⋙ QZ) (e' : QT' ⋙ E' ≅ hE' ⋙ QT)
  (σ : Lu ⋙ Lt' ⟶ Lt ⋙ Lu') (hσ : hu ⋙ ht' ⟶ ht ⋙ hu')

/-- Solve `a ≫ b ≫ c = d` for `a ≫ b` when `c` is invertible. -/
private theorem comp_comp_eq_comp_inv {X Y Z W : CU} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W}
    [IsIso c] {d : X ⟶ W} (h : a ≫ b ≫ c = d) : a ≫ b = d ≫ inv c := by
  rw [← h]
  simp

/-- **Mates commute with comparisons from models.**  If the units of `E ⊣ Lu` and `E' ⊣ Lu'`
read through the comparisons are the units of the model adjunctions (`hunit`, `hunit'`), and the
2-cell `σ` read through the comparisons is the model 2-cell `hσ` (`hS`), then the mate of `σ`
read through the comparisons is the mate of `hσ`. -/
theorem mateEquiv_symm_app_comp
    (hunit : ∀ M : HU, adj.unit.app (QU.obj M) ≫ Lu.map (e.hom.app M) ≫ cu.app (hE.obj M) =
      QU.map (hadj.unit.app M))
    (hunit' : ∀ M : HT', adj'.unit.app (QT'.obj M) ≫ Lu'.map (e'.hom.app M) ≫
      cu'.app (hE'.obj M) = QT'.map (hadj'.unit.app M))
    (hS : ∀ N : HZ, σ.app (QZ.obj N) ≫ Lu'.map (ct.app N) ≫ cu'.app (ht.obj N) =
      Lt'.map (cu.app N) ≫ ct'.app (hu.obj N) ≫ QT'.map (hσ.app N))
    (M : HU) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ σ)).natTrans.app (QU.obj M) ≫
        Lt.map (e.hom.app M) ≫ ct.app (hE.obj M) =
      E'.map (ct'.app M) ≫ e'.hom.app (ht'.obj M) ≫
        QT.map (((mateEquiv hadj hadj').symm (TwoSquare.mk _ _ _ _ hσ)).natTrans.app M) := by
  set β := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ σ)).natTrans with hβdef
  set hβ := ((mateEquiv hadj hadj').symm (TwoSquare.mk _ _ _ _ hσ)).natTrans with hhβdef
  apply (adj'.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp]
  -- the two mates, transposed
  have h₁ : Lt'.map (adj.unit.app (QU.obj M)) ≫ σ.app (E.obj (QU.obj M)) =
      adj'.unit.app (Lt'.obj (QU.obj M)) ≫ Lu'.map (β.app (QU.obj M)) :=
    unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ σ) (QU.obj M)
  have h₂ : ht'.map (hadj.unit.app M) ≫ hσ.app (hE.obj M) =
      hadj'.unit.app (ht'.obj M) ≫ hu'.map (hβ.app M) :=
    unit_mateEquiv_symm hadj hadj' (TwoSquare.mk _ _ _ _ hσ) M
  rw [← reassoc_of% h₁]
  -- naturality of `σ` along `e`
  have hnat : Lt'.map (Lu.map (e.hom.app M)) ≫ σ.app (QZ.obj (hE.obj M)) =
      σ.app (E.obj (QU.obj M)) ≫ Lu'.map (Lt.map (e.hom.app M)) :=
    σ.naturality (e.hom.app M)
  rw [← reassoc_of% hnat]
  -- the compatibility of `σ`, solved for `σ ≫ Lu'.map ct`
  rw [comp_comp_eq_comp_inv (hS (hE.obj M)), assoc, assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, assoc, hunit M]
  have hct : Lt'.map (QU.map (hadj.unit.app M)) ≫ ct'.app (hu.obj (hE.obj M)) =
      ct'.app M ≫ QT'.map (ht'.map (hadj.unit.app M)) :=
    ct'.naturality (hadj.unit.app M)
  rw [reassoc_of% hct]
  -- the right-hand side
  have hu₁ : adj'.unit.app (Lt'.obj (QU.obj M)) ≫ Lu'.map (E'.map (ct'.app M)) =
      ct'.app M ≫ adj'.unit.app (QT'.obj (ht'.obj M)) :=
    (adj'.unit.naturality (ct'.app M)).symm
  rw [reassoc_of% hu₁]
  congr 1
  have hcu : Lu'.map (QT.map (hβ.app M)) ≫ cu'.app (hE.obj M |> ht.obj) =
      cu'.app (hE'.obj (ht'.obj M)) ≫ QT'.map (hu'.map (hβ.app M)) :=
    cu'.naturality (hβ.app M)
  have hcu' : inv (cu'.app (hE'.obj (ht'.obj M))) ≫ Lu'.map (QT.map (hβ.app M)) =
      QT'.map (hu'.map (hβ.app M)) ≫ inv (cu'.app (ht.obj (hE.obj M))) := by
    rw [IsIso.inv_comp_eq, ← reassoc_of% hcu, IsIso.hom_inv_id, comp_id]
  rw [reassoc_of% (comp_comp_eq_comp_inv (hunit' (ht'.obj M))), hcu', ← Functor.map_comp_assoc,
    h₂, Functor.map_comp, assoc]

/-- `CategoryTheory.Adjunction.mateEquiv_symm_app_comp` for natural transformations `β` and `hβ`
given together with equations identifying them with the two mates. -/
theorem mateEquiv_symm_app_comp_of_eq
    (β : Lt' ⋙ E' ⟶ E ⋙ Lt) (hβ : β = ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ σ)).natTrans)
    (βh : ht' ⋙ hE' ⟶ hE ⋙ ht)
    (hβh : βh = ((mateEquiv hadj hadj').symm (TwoSquare.mk _ _ _ _ hσ)).natTrans)
    (hunit : ∀ M : HU, adj.unit.app (QU.obj M) ≫ Lu.map (e.hom.app M) ≫ cu.app (hE.obj M) =
      QU.map (hadj.unit.app M))
    (hunit' : ∀ M : HT', adj'.unit.app (QT'.obj M) ≫ Lu'.map (e'.hom.app M) ≫
      cu'.app (hE'.obj M) = QT'.map (hadj'.unit.app M))
    (hS : ∀ N : HZ, σ.app (QZ.obj N) ≫ Lu'.map (ct.app N) ≫ cu'.app (ht.obj N) =
      Lt'.map (cu.app N) ≫ ct'.app (hu.obj N) ≫ QT'.map (hσ.app N))
    (M : HU) :
    β.app (QU.obj M) ≫ Lt.map (e.hom.app M) ≫ ct.app (hE.obj M) =
      E'.map (ct'.app M) ≫ e'.hom.app (ht'.obj M) ≫ QT.map (βh.app M) := by
  subst hβ hβh
  exact mateEquiv_symm_app_comp adj adj' hadj hadj' ct' ct cu cu' e e' σ hσ hunit hunit' hS M

end CategoryTheory.Adjunction

namespace CategoryTheory.Iso

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {CZ : Type u₁} {CU : Type u₂} {CT : Type u₃} {CT' : Type u₄}
  [Category.{v₁} CZ] [Category.{v₂} CU] [Category.{v₃} CT] [Category.{v₄} CT']
  {HZ : Type u₅} {HU : Type u₆} {HT : Type u₇} {HT' : Type u₈}
  [Category.{v₅} HZ] [Category.{v₆} HU] [Category.{v₇} HT] [Category.{v₈} HT']

/-- **The 2-cell of a square built from two factorisations, read through comparisons.**  Let
`α : Lu ⋙ Lt' ≅ Lk` and `β : Lt ⋙ Lu' ≅ Lk` identify the two composites around a square with a
third functor, and let `φ₁`, `φ₂` be the corresponding identifications in a model.  If `α` and `β`
read through comparisons `c` are `φ₁` and `φ₂` (`h₁`, `h₂`), then the 2-cell `α ≫ β⁻¹` read
through the comparisons is `φ₁ ≫ φ₂⁻¹`. -/
theorem hom_inv_app_comp_eq_of_comparisons {QZ : HZ ⥤ CZ} {QU : HU ⥤ CU} {QT : HT ⥤ CT}
    {QT' : HT' ⥤ CT'} {Lu : CZ ⥤ CU} {Lt' : CU ⥤ CT'} {Lt : CZ ⥤ CT} {Lu' : CT ⥤ CT'}
    {Lk : CZ ⥤ CT'} {hu : HZ ⥤ HU} {ht' : HU ⥤ HT'} {ht : HZ ⥤ HT} {hu' : HT ⥤ HT'}
    {hk : HZ ⥤ HT'} (α : Lu ⋙ Lt' ≅ Lk) (β : Lt ⋙ Lu' ≅ Lk)
    (cu : QZ ⋙ Lu ⟶ hu ⋙ QU) (ct' : QU ⋙ Lt' ⟶ ht' ⋙ QT') (ct : QZ ⋙ Lt ⟶ ht ⋙ QT)
    (cu' : QT ⋙ Lu' ⟶ hu' ⋙ QT') (ck : QZ ⋙ Lk ⟶ hk ⋙ QT')
    (φ₁ : hu ⋙ ht' ≅ hk) (φ₂ : ht ⋙ hu' ≅ hk) (N : HZ)
    (h₁ : α.hom.app (QZ.obj N) ≫ ck.app N =
      Lt'.map (cu.app N) ≫ ct'.app (hu.obj N) ≫ QT'.map (φ₁.hom.app N))
    (h₂ : β.hom.app (QZ.obj N) ≫ ck.app N =
      Lu'.map (ct.app N) ≫ cu'.app (ht.obj N) ≫ QT'.map (φ₂.hom.app N)) :
    (α.hom.app (QZ.obj N) ≫ β.inv.app (QZ.obj N)) ≫ Lu'.map (ct.app N) ≫ cu'.app (ht.obj N) =
      Lt'.map (cu.app N) ≫ ct'.app (hu.obj N) ≫ QT'.map ((φ₁.hom ≫ φ₂.inv).app N) := by
  have h₂' : β.inv.app (QZ.obj N) ≫ Lu'.map (ct.app N) ≫ cu'.app (ht.obj N) =
      ck.app N ≫ QT'.map (φ₂.inv.app N) := by
    rw [← cancel_epi (β.hom.app (QZ.obj N)), hom_inv_id_app_assoc, reassoc_of% h₂,
      ← Functor.map_comp, hom_inv_id_app]
    simp
  rw [assoc, h₂', reassoc_of% h₁, NatTrans.comp_app, Functor.map_comp]

end CategoryTheory.Iso
