module

public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomContravariant
public import StacksCore.Tactic.StacksAttribute

/-!
# The internal hom of sheaves of sets: `Mor(F × G, H) = Mor(F, SheafHom(G, H))`

Let `(C, J)` be a site (small, as all sites of the Stacks Project are: the coverings form a set
and contain every identity, so the objects form a set) and let `F`, `G`, `H` be sheaves of sets
on it. Stacks 0BWQ asserts a canonical bijection
`Mor_{Sh(C)}(F × G, H) = Mor_{Sh(C)}(F, SheafHom(G, H))`, functorial in all three entries, where
`SheafHom(G, H)` is the sheaf `U ↦ Mor_{Sh(C/U)}(G|_{C/U}, H|_{C/U})`, which is Mathlib's
`CategoryTheory.sheafHom G H`.

## Main results

* `CategoryTheory.SheafHomAdj.sheafHomPrecomp`: for `g : G' ⟶ G`, the map
  `SheafHom(G, H) ⟶ SheafHom(G', H)` precomposing a section `G|_{C/U} ⟶ H|_{C/U}` with the
  restriction of `g`.
* `CategoryTheory.SheafHomAdj.prodHomEquivSheafHom`: the bijection
  `(F ⨯ G ⟶ H) ≃ (F ⟶ sheafHom G H)`, the hom-equivalence of the adjunction
  `- × G ⊣ SheafHom(G, -)` (`prodFlipSheafHomAdjunction`).
* `CategoryTheory.SheafHomAdj.prodHomEquivSheafHom_symm_hom_app`: the inverse is the source's
  formula `(s, t) ↦ ψ(s)(t)`.
* `CategoryTheory.SheafHomAdj.prodHomEquivSheafHom_naturality_left`, `..._naturality_middle`,
  `..._naturality_right`: naturality in `F`, in `G` (contravariantly, through
  `sheafHomPrecomp`) and in `H` (through postcomposition, `sheafHomMap`).
* `CategoryTheory.SheafHomAdj.prodHomEquivSheafHom_natural`: the three naturality statements
  together; this and the bijection carry the tag 0BWQ.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory.SheafHomAdj

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- `SheafHom(-, H)` on a morphism `g : G' ⟶ G` of the source: a section
`φ : G|_{C/V} ⟶ H|_{C/V}` of `SheafHom(G, H)` over `V` is sent to `g|_{C/V} ≫ φ`. -/
def sheafHomPrecomp {G' G : Sheaf J (Type u)} (g : G' ⟶ G) (H : Sheaf J (Type u)) :
    sheafHom G H ⟶ sheafHom G' H :=
  ⟨{ app := fun V => ↾fun φ => (J.overPullback (Type u) V.unop).map g ≫ φ
     naturality := by intro V V' f; ext φ; rfl }⟩

/-- `sheafHomPrecomp g H` acts on sections by precomposition with the restriction of `g`. -/
@[simp] lemma sheafHomPrecomp_hom_app {G' G : Sheaf J (Type u)} (g : G' ⟶ G)
    (H : Sheaf J (Type u)) {V : Cᵒᵖ} (φ : (sheafHom G H).obj.obj V) :
    (sheafHomPrecomp g H).hom.app V φ = (J.overPullback (Type u) V.unop).map g ≫ φ := rfl

/-- Elementwise form of an equation `m ≫ p = q` of morphisms of sheaves of sets. -/
private lemma hom_app_comp_eq {P Q R : Sheaf J (Type u)} {m : P ⟶ Q} {p : Q ⟶ R} {q : P ⟶ R}
    (h : m ≫ p = q) {V : Cᵒᵖ} (z : P.obj.obj V) :
    p.hom.app V (m.hom.app V z) = q.hom.app V z := by
  rw [← h]
  rfl

/-- **Stacks 0BWQ, the bijection.** For sheaves of sets `F`, `G`, `H` on a site, maps
`F × G ⟶ H` are in canonical bijection with maps `F ⟶ SheafHom(G, H)`, where `SheafHom(G, H)` is
Mathlib's `sheafHom G H`, the sheaf `U ↦ Mor_{Sh(C/U)}(G|_{C/U}, H|_{C/U})`. It is the
hom-equivalence of the adjunction `- × G ⊣ SheafHom(G, -)`; the inverse is the source's formula
`(s, t) ↦ ψ(s)(t)` (`prodHomEquivSheafHom_symm_hom_app`), and the bijection is natural in all
three entries (`prodHomEquivSheafHom_natural`). -/
@[stacks 0BWQ]
def prodHomEquivSheafHom (F G H : Sheaf J (Type u)) :
    (F ⨯ G ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (prodFlipSheafHomAdjunction G).homEquiv F H

/-- The inverse of `prodHomEquivSheafHom` is the source's formula: `ψ : F ⟶ SheafHom(G, H)` gives
the map `F × G ⟶ H` sending `(s, t)` over `V` to `ψ(s)(t)`, the value of
`ψ(s) : G|_{C/V} ⟶ H|_{C/V}` at the tautological object `V/V` on `t`. -/
lemma prodHomEquivSheafHom_symm_hom_app {F G H : Sheaf J (Type u)} (ψ : F ⟶ sheafHom G H)
    {V : Cᵒᵖ} (z : (F ⨯ G).obj.obj V) :
    ((prodHomEquivSheafHom F G H).symm ψ).hom.app V z
      = (Sheaf.homEquiv (ψ.hom.app V ((prod.fst : F ⨯ G ⟶ F).hom.app V z))).app
          (op (Over.mk (𝟙 V.unop))) ((prod.snd : F ⨯ G ⟶ G).hom.app V z) := by
  have key : (prodHomEquivSheafHom F G H).symm ψ
      = (prod.braiding G F).inv ≫ ((prodSheafHomAdjunction G).homEquiv F H).symm ψ := by
    unfold prodHomEquivSheafHom prodFlipSheafHomAdjunction
    exact Adjunction.homEquiv_ofNatIsoLeft_symm_apply (adj := prodSheafHomAdjunction G)
      (X := F) (Y := H) (f := ψ) ..
  have hadj : (prodSheafHomAdjunction G).homEquiv F H = prodSheafHomEquiv' G H F := by
    change (Adjunction.mkOfHomEquiv _).homEquiv F H = _
    rw [Adjunction.mkOfHomEquiv_homEquiv]
  rw [key, hadj]
  change ((prodSheafHomEquiv' G H F).symm ψ).hom.app V ((prod.braiding G F).inv.hom.app V z) = _
  refine (prodSheafHomEquiv'_symm_app G ψ ((prod.braiding G F).inv.hom.app V z)).trans ?_
  rw [hom_app_comp_eq (show (prod.braiding G F).inv ≫ prod.snd = prod.fst by simp [prod.braiding]),
    hom_app_comp_eq (show (prod.braiding G F).inv ≫ prod.fst = prod.snd by simp [prod.braiding])]
  rfl

/-- `prodHomEquivSheafHom` is natural in `F`. -/
lemma prodHomEquivSheafHom_naturality_left {F' F G H : Sheaf J (Type u)} (f : F' ⟶ F)
    (φ : F ⨯ G ⟶ H) :
    prodHomEquivSheafHom F' G H (prod.map f (𝟙 G) ≫ φ) = f ≫ prodHomEquivSheafHom F G H φ :=
  (prodFlipSheafHomAdjunction G).homEquiv_naturality_left f φ

/-- `prodHomEquivSheafHom` is natural in `H`, `SheafHom(G, -)` acting by postcomposition. -/
lemma prodHomEquivSheafHom_naturality_right {F G H H' : Sheaf J (Type u)} (h : H ⟶ H')
    (φ : F ⨯ G ⟶ H) :
    prodHomEquivSheafHom F G H' (φ ≫ h) = prodHomEquivSheafHom F G H φ ≫ sheafHomMap G h :=
  (prodFlipSheafHomAdjunction G).homEquiv_naturality_right φ h

/-- `prodHomEquivSheafHom` is natural in `G`, contravariantly: `SheafHom(-, H)` acts on
`g : G' ⟶ G` by precomposition with the restriction of `g` (`sheafHomPrecomp`). -/
lemma prodHomEquivSheafHom_naturality_middle {F G' G H : Sheaf J (Type u)} (g : G' ⟶ G)
    (φ : F ⨯ G ⟶ H) :
    prodHomEquivSheafHom F G' H (prod.map (𝟙 F) g ≫ φ)
      = prodHomEquivSheafHom F G H φ ≫ sheafHomPrecomp g H := by
  rw [← Equiv.eq_symm_apply]
  conv_lhs => rw [← (prodHomEquivSheafHom F G H).symm_apply_apply φ]
  generalize prodHomEquivSheafHom F G H φ = ψ
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  ext z
  change ((prodHomEquivSheafHom F G H).symm ψ).hom.app V ((prod.map (𝟙 F) g).hom.app V z)
    = ((prodHomEquivSheafHom F G' H).symm (ψ ≫ sheafHomPrecomp g H)).hom.app V z
  rw [prodHomEquivSheafHom_symm_hom_app, prodHomEquivSheafHom_symm_hom_app,
    hom_app_comp_eq (prod.map_fst (𝟙 F) g), hom_app_comp_eq (prod.map_snd (𝟙 F) g),
    Category.comp_id]
  rfl

/-- **Stacks 0BWQ, functoriality.** The bijection `prodHomEquivSheafHom` is functorial in all
three entries: in `F` (precomposition with `f × G`), in `G` (precomposition with `F × g` on the
left, `SheafHom(g, H)` on the right) and in `H` (postcomposition, `SheafHom(G, h)` on the
right). -/
@[stacks 0BWQ]
theorem prodHomEquivSheafHom_natural :
    (∀ {F' F G H : Sheaf J (Type u)} (f : F' ⟶ F) (φ : F ⨯ G ⟶ H),
      prodHomEquivSheafHom F' G H (prod.map f (𝟙 G) ≫ φ) = f ≫ prodHomEquivSheafHom F G H φ) ∧
    (∀ {F G' G H : Sheaf J (Type u)} (g : G' ⟶ G) (φ : F ⨯ G ⟶ H),
      prodHomEquivSheafHom F G' H (prod.map (𝟙 F) g ≫ φ)
        = prodHomEquivSheafHom F G H φ ≫ sheafHomPrecomp g H) ∧
    (∀ {F G H H' : Sheaf J (Type u)} (h : H ⟶ H') (φ : F ⨯ G ⟶ H),
      prodHomEquivSheafHom F G H' (φ ≫ h) = prodHomEquivSheafHom F G H φ ≫ sheafHomMap G h) :=
  ⟨prodHomEquivSheafHom_naturality_left, prodHomEquivSheafHom_naturality_middle,
    prodHomEquivSheafHom_naturality_right⟩

end CategoryTheory.SheafHomAdj

end
