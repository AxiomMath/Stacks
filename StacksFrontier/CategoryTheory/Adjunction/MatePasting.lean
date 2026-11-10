module

public import StacksFrontier.CategoryTheory.Adjunction.MatePaste

/-!
# Vertical and horizontal pasting of mates, as identities of natural transformations

Consider squares of categories whose horizontal functors are adjunctions `L ⊣ R` and whose
vertical functors are arbitrary, and a "base change" 2-cell `G ⋙ L' ⟶ L ⋙ H` defined as the
inverse mate of a 2-cell `R ⋙ G ⟶ H ⋙ R'` between the right adjoints.  This file records the two
pasting laws for such 2-cells, stated as identities of natural transformations whose shape is
that of the pasting operations used for base change maps:

* in the vertical direction, two squares stacked along a vertical functor, with the composite
  vertical functors identified with given functors;
* in the horizontal direction, two squares placed side by side, with the composite left adjoints
  identified with given left adjoints, compatibly (through `CategoryTheory.conjugateEquiv`) with
  given identifications of the composite right adjoints.

In each case the hypothesis is the corresponding pasting identity for the 2-cells between right
adjoints.  The file also records two cancellations in an arbitrary category, which reduce such a
pasting identity to three instances of an associativity pentagon.

## Main results

* `Stacks.CategoryTheory.MatePasting.pasteV_eq_of_mateEquiv_symm`: vertical pasting.
* `Stacks.CategoryTheory.MatePasting.pasteH_eq_of_mateEquiv_symm`: horizontal pasting.
* `Stacks.CategoryTheory.MatePasting.comp_eq_of_pentagons_v` and
  `Stacks.CategoryTheory.MatePasting.comp_eq_of_pentagons_h`: the cancellations.

## Implementation notes

Everything is stated over abstract functors, so that applying the results to concrete functors
(sheaf pushforwards and pullbacks, say) produces proof terms that are single applications.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.MatePasting

section Algebra

variable {E E' E'' : Type*} [Category* E] [Category* E'] [Category* E'']

/-- **A cancellation of three pentagons, vertical form.**  Given commuting squares
`a ≫ s = p ≫ q`, `Φ i ≫ s = c ≫ t` and `e ≫ k = j ≫ t` with `i`, `j`, `k` isomorphisms, the
composite `a ≫ Φ i⁻¹ ≫ c ≫ j⁻¹ ≫ e` is `p ≫ q ≫ k⁻¹`. -/
theorem comp_eq_of_pentagons_v (Φ : E' ⥤ E) {O₁ O₄ O₅ O₆ O₇ O₈ : E} {P₂ P₃ : E'}
    (a : O₁ ⟶ Φ.obj P₂) (i : P₃ ≅ P₂) (c : Φ.obj P₃ ⟶ O₄) (j : O₅ ≅ O₄) (e : O₅ ⟶ O₆)
    (p : O₁ ⟶ O₇) (q : O₇ ⟶ O₈) (k : O₆ ≅ O₈) (s : Φ.obj P₂ ⟶ O₈) (t : O₄ ⟶ O₈)
    (h₁ : a ≫ s = p ≫ q) (h₂ : Φ.map i.hom ≫ s = c ≫ t) (h₃ : e ≫ k.hom = j.hom ≫ t) :
    a ≫ Φ.map i.inv ≫ c ≫ j.inv ≫ e = p ≫ q ≫ k.inv := by
  rw [← cancel_mono k.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₃, Iso.inv_hom_id_assoc, ← h₂, Iso.inv_hom_id_map_assoc, h₁]

/-- **A cancellation of three pentagons, horizontal form.**  Given commuting squares
`Φ i ≫ p = b ≫ t`, `d ≫ s = j ≫ t` and `Ψ l ≫ s = k ≫ n` with `i`, `j`, `l`, `n` isomorphisms,
the composite `Φ i⁻¹ ≫ b ≫ j⁻¹ ≫ d ≫ Ψ l⁻¹ ≫ k` is `p ≫ n⁻¹`. -/
theorem comp_eq_of_pentagons_h (Φ : E' ⥤ E) (Ψ : E'' ⥤ E) {O₃ O₄ O₇ O₈ : E}
    {P₁ P₂ : E'} {Q₅ Q₆ : E''} (i : P₂ ≅ P₁) (b : Φ.obj P₂ ⟶ O₃) (j : O₄ ≅ O₃)
    (d : O₄ ⟶ Ψ.obj Q₅) (l : Q₆ ≅ Q₅) (k : Ψ.obj Q₆ ⟶ O₇) (p : Φ.obj P₁ ⟶ O₈) (n : O₇ ≅ O₈)
    (s : Ψ.obj Q₅ ⟶ O₈) (t : O₃ ⟶ O₈) (hA : Φ.map i.hom ≫ p = b ≫ t) (hB : d ≫ s = j.hom ≫ t)
    (hC : Ψ.map l.hom ≫ s = k ≫ n.hom) :
    Φ.map i.inv ≫ b ≫ j.inv ≫ d ≫ Ψ.map l.inv ≫ k = p ≫ n.inv := by
  rw [← cancel_mono n.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hC, Iso.inv_hom_id_map_assoc, hB, Iso.inv_hom_id_assoc, ← hA, Iso.inv_hom_id_map_assoc]

end Algebra

section Vertical

variable {CX CY CZ CX' CY' CZ' : Type*} [Category* CX] [Category* CY] [Category* CZ]
  [Category* CX'] [Category* CY'] [Category* CZ']
  {fS : CX ⥤ CY} {gS : CY ⥤ CZ} {fgS : CX ⥤ CZ}
  {f'S : CX' ⥤ CY'} {g'S : CY' ⥤ CZ'} {f'g'S : CX' ⥤ CZ'}
  {cS : CX' ⥤ CX} {bS : CY' ⥤ CY} {aS : CZ' ⥤ CZ}
  {cI : CX ⥤ CX'} {bI : CY ⥤ CY'} {aI : CZ ⥤ CZ'}

/-- **Vertical pasting of mates.**  Let `β₁`, `β₂` and `β` be the inverse mates of 2-cells
`γ₁ : c_* f_* ⟶ f'_* b_*`, `γ₂ : b_* g_* ⟶ g'_* a_*` and `γ : c_* (gf)_* ⟶ (g'f')_* a_*` between
right adjoints, the first two pasting vertically to the third through `μ : f_* g_* ≅ (gf)_*`
and `μ' : f'_* g'_* ≅ (g'f')_*`.  Then `β` precomposed with `μ` is the vertical pasting of
`β₁` and `β₂` followed by `μ'`. -/
theorem pasteV_eq_of_mateEquiv_symm (adjc : cI ⊣ cS) (adjb : bI ⊣ bS) (adja : aI ⊣ aS)
    (μ : fS ⋙ gS ≅ fgS) (μ' : f'S ⋙ g'S ≅ f'g'S)
    (γ₁ : TwoSquare cS f'S fS bS) (γ₂ : TwoSquare bS g'S gS aS) (γ : TwoSquare cS f'g'S fgS aS)
    (β₁ : fS ⋙ bI ⟶ cI ⋙ f'S) (β₂ : gS ⋙ aI ⟶ bI ⋙ g'S) (β : fgS ⋙ aI ⟶ cI ⋙ f'g'S)
    (hβ₁ : β₁ = (mateEquiv adjc adjb).symm γ₁) (hβ₂ : β₂ = (mateEquiv adjb adja).symm γ₂)
    (hβ : β = (mateEquiv adjc adja).symm γ)
    (h : ∀ F, gS.map (γ₁.app F) ≫ γ₂.app (f'S.obj F) ≫ aS.map (μ'.hom.app F) =
      μ.hom.app (cS.obj F) ≫ γ.app F) :
    Functor.whiskerRight μ.hom aI ≫ β =
      ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft fS β₂ ≫
          (Functor.associator _ _ _).inv ≫ Functor.whiskerRight β₁ g'S ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft cI μ'.hom := by
  subst hβ₁ hβ₂ hβ
  ext F
  simpa using mateEquiv_symm_paste_app adjc adjb adja μ μ' γ₁ γ₂ γ h F

end Vertical

section Horizontal

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B'']
  {G : A ⥤ B} {H : A' ⥤ B'} {K : A'' ⥤ B''}
  {L₁ : A ⥤ A'} {R₁ : A' ⥤ A} {L₂ : B ⥤ B'} {R₂ : B' ⥤ B}
  {L₃ : A' ⥤ A''} {R₃ : A'' ⥤ A'} {L₄ : B' ⥤ B''} {R₄ : B'' ⥤ B'}
  {L₅ : A ⥤ A''} {R₅ : A'' ⥤ A} {L₆ : B ⥤ B''} {R₆ : B'' ⥤ B}

/-- **Horizontal pasting of mates.**  Let `β₁ : G L₂ ⟶ L₁ H`, `β₂ : H L₄ ⟶ L₃ K` and
`β : G L₆ ⟶ L₅ K` be the inverse mates of 2-cells `γ₁`, `γ₂`, `γ` between right adjoints, and let
`eL : L₁ ⋙ L₃ ≅ L₅`, `eL' : L₂ ⋙ L₄ ≅ L₆` be identifications of the composite left adjoints
conjugate to identifications `dR`, `dR'` of the composite right adjoints.  If `γ₂` and `γ₁`
paste to `γ` through `dR` and `dR'`, then `β` is the horizontal pasting of `β₁` and `β₂`
through `eL'` and `eL`. -/
theorem pasteH_eq_of_mateEquiv_symm (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅) (adj₆ : L₆ ⊣ R₆) (eL : L₁ ⋙ L₃ ≅ L₅)
    (eL' : L₂ ⋙ L₄ ≅ L₆) (dR : R₃ ⋙ R₁ ≅ R₅) (dR' : R₄ ⋙ R₂ ≅ R₆)
    (hL : conjugateEquiv adj₅ (adj₁.comp adj₃) eL.hom = dR.inv)
    (hL' : conjugateEquiv adj₆ (adj₂.comp adj₄) eL'.hom = dR'.inv)
    (γ₁ : TwoSquare R₁ H G R₂) (γ₂ : TwoSquare R₃ K H R₄) (γ : TwoSquare R₅ K G R₆)
    (β₁ : G ⋙ L₂ ⟶ L₁ ⋙ H) (β₂ : H ⋙ L₄ ⟶ L₃ ⋙ K) (β : G ⋙ L₆ ⟶ L₅ ⋙ K)
    (hβ₁ : β₁ = (mateEquiv adj₁ adj₂).symm γ₁) (hβ₂ : β₂ = (mateEquiv adj₃ adj₄).symm γ₂)
    (hβ : β = (mateEquiv adj₅ adj₆).symm γ)
    (h : ∀ F, G.map (dR.inv.app F) ≫ γ₁.app (R₃.obj F) ≫ R₂.map (γ₂.app F) ≫
      dR'.hom.app (K.obj F) = γ.app F) :
    Functor.whiskerLeft G eL'.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight β₁ L₄ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L₁ β₂ ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight eL.hom K = β := by
  subst hβ₁ hβ₂ hβ
  have hL'' : conjugateEquiv (adj₂.comp adj₄) adj₆ eL'.inv = dR'.hom := by
    have h₀ := conjugateEquiv_comp adj₆ (adj₂.comp adj₄) adj₆ eL'.hom eL'.inv
    rw [Iso.inv_hom_id, conjugateEquiv_id, hL'] at h₀
    exact (Iso.inv_comp_eq_id _).1 h₀
  apply (mateEquiv adj₅ adj₆).injective
  rw [Equiv.apply_symm_apply]
  have e : (Functor.whiskerLeft G eL'.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((mateEquiv adj₁ adj₂).symm γ₁) L₄ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L₁ ((mateEquiv adj₃ adj₄).symm γ₂) ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eL.hom K :
        TwoSquare G L₅ L₆ K) =
      ((((mateEquiv adj₁ adj₂).symm γ₁).vComp ((mateEquiv adj₃ adj₄).symm γ₂)).whiskerRight
        eL'.inv).whiskerLeft eL.hom := by
    ext F
    simp [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  rw [e, conjugateEquiv_mateEquiv_vcomp adj₅ (adj₁.comp adj₃) adj₆,
    mateEquiv_conjugateEquiv_vcomp (adj₁.comp adj₃) (adj₂.comp adj₄) adj₆, mateEquiv_hcomp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, hL, hL'']
  ext F
  simpa [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using h F

end Horizontal

end Stacks.CategoryTheory.MatePasting

end
