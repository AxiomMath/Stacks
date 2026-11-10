module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting base change maps and their restrictions to subfunctors

Consider two squares on top of each other
```
X' --c--> X
|f'       |f
v         v
Y' --b--> Y
|g'       |g
v         v
Z' --a--> Z
```
of "spaces" whose direct images `f_*`, `c_*`, ... are functors and whose inverse images
`c⁻¹ ⊣ c_*`, `b⁻¹ ⊣ b_*`, `a⁻¹ ⊣ a_*` along the horizontal arrows are left adjoints. The base
change map `b⁻¹ f_* ⟶ f'_* c⁻¹` of a square is the mate of a 2-cell `c_* f_* ⟶ f'_* b_*`. This
file records, in this abstract setting, the two formal steps of Stacks, Remark 0F77 (2).

## Main results

* `CategoryTheory.mateEquiv_symm_paste_app`: if the 2-cells of the two squares paste vertically
  to the 2-cell of the rectangle, through comparisons `μ : f_* g_* ≅ (gf)_*` and
  `μ' : f'_* g'_* ≅ (g'f')_*` of the direct image along a composite with the composite of the
  direct images, then the base change maps paste horizontally through the same comparisons.
  This is Sites, Remark 0F6X, read through the comparisons `μ` and `μ'`.
* `CategoryTheory.subfunctor_baseChange_paste_app`: subfunctors of the direct images whose
  composition and base change maps are restrictions of those of the direct images inherit the
  pasting identity; this is the diagram of Remark 0F77 (2).

## References

* [Stacks Project, Tag 0F6X](https://stacks.math.columbia.edu/tag/0F6X)
* [Stacks Project, Tag 0F77](https://stacks.math.columbia.edu/tag/0F77)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

open CategoryTheory.Functor TwoSquare

section Paste

variable {CX CY CZ CX' CY' CZ' : Type*} [Category* CX] [Category* CY] [Category* CZ]
  [Category* CX'] [Category* CY'] [Category* CZ']
  {fS : CX ⥤ CY} {gS : CY ⥤ CZ} {fgS : CX ⥤ CZ}
  {f'S : CX' ⥤ CY'} {g'S : CY' ⥤ CZ'} {f'g'S : CX' ⥤ CZ'}
  {cS : CX' ⥤ CX} {bS : CY' ⥤ CY} {aS : CZ' ⥤ CZ}
  {cI : CX ⥤ CX'} {bI : CY ⥤ CY'} {aI : CZ ⥤ CZ'}

/-- **Pasting of base change maps** (Sites, Remark 0F6X). Let `γ₁`, `γ₂` and `γ` be 2-cells
`c_* f_* ⟶ f'_* b_*`, `b_* g_* ⟶ g'_* a_*` and `c_* (gf)_* ⟶ (g'f')_* a_*` between direct
images, the first two pasting vertically to the third through the comparisons
`μ : f_* g_* ≅ (gf)_*` and `μ' : f'_* g'_* ≅ (g'f')_*`. Then their mates, the base change maps
`b⁻¹ f_* ⟶ f'_* c⁻¹`, `a⁻¹ g_* ⟶ g'_* b⁻¹` and `a⁻¹ (gf)_* ⟶ (g'f')_* c⁻¹`, paste horizontally
through the same comparisons. -/
theorem mateEquiv_symm_paste_app (adjc : cI ⊣ cS) (adjb : bI ⊣ bS) (adja : aI ⊣ aS)
    (μ : fS ⋙ gS ≅ fgS) (μ' : f'S ⋙ g'S ≅ f'g'S)
    (γ₁ : TwoSquare cS f'S fS bS) (γ₂ : TwoSquare bS g'S gS aS)
    (γ : TwoSquare cS f'g'S fgS aS)
    (h : ∀ F, gS.map (γ₁.app F) ≫ γ₂.app (f'S.obj F) ≫ aS.map (μ'.hom.app F) =
      μ.hom.app (cS.obj F) ≫ γ.app F) (F : CX) :
    aI.map (μ.hom.app F) ≫ ((mateEquiv adjc adja).symm γ).app F =
      ((mateEquiv adjb adja).symm γ₂).app (fS.obj F) ≫
        g'S.map (((mateEquiv adjc adjb).symm γ₁).app F) ≫ μ'.hom.app (cI.obj F) := by
  set β₁ := (mateEquiv adjc adjb).symm γ₁
  set β₂ := (mateEquiv adjb adja).symm γ₂
  set β := (mateEquiv adjc adja).symm γ
  let δ : TwoSquare (fS ⋙ gS) cI aI (f'S ⋙ g'S) :=
    (β.whiskerTop μ.hom).whiskerBottom μ'.inv
  have hwhisker : mateEquiv adjc adja δ = (γ.whiskerRight μ.hom).whiskerLeft μ'.inv := by
    have hγ : γ = mateEquiv adjc adja β := ((mateEquiv adjc adja).apply_symm_apply γ).symm
    rw [hγ]
    refine NatTrans.ext (funext fun d => ?_)
    simp [δ, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, mateEquiv]
  have hpaste : mateEquiv adjc adja (β₁ ≫ₕ β₂) = γ₁ ≫ᵥ γ₂ := by
    rw [mateEquiv_vcomp adjc adjb adja]
    simp only [β₁, β₂, Equiv.apply_symm_apply]
  have hδ : δ = β₁ ≫ₕ β₂ := by
    apply (mateEquiv adjc adja).injective
    rw [hpaste, hwhisker]
    refine NatTrans.ext (funext fun d => ?_)
    have hd := h d
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
      associator_inv_app, associator_hom_app, Category.id_comp, Category.comp_id] at hd ⊢
    rw [← hd]
    simp [← Functor.map_comp]
  have hF := congrArg (fun α : TwoSquare (fS ⋙ gS) cI aI (f'S ⋙ g'S) => α.app F) hδ
  simp only [δ, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    associator_inv_app, associator_hom_app, Category.id_comp, Category.comp_id] at hF
  rw [← reassoc_of% hF]
  simp

variable {fB : CX ⥤ CY} {gB : CY ⥤ CZ} {fgB : CX ⥤ CZ}
  {f'B : CX' ⥤ CY'} {g'B : CY' ⥤ CZ'} {f'g'B : CX' ⥤ CZ'}

/-- **The compatibility of Remark 0F77 (2), for subfunctors.** Let `f_! ⊂ f_*`, `g_! ⊂ g_*`,
`(gf)_! ⊂ (gf)_*`, and similarly for the primed functors, be subfunctors of direct images
(given by monomorphisms `ι`), with composition maps `κ : g_! f_! ⟶ (gf)_!` and `κ'` and base
change maps `ε₁ : b⁻¹ f_! ⟶ f'_! c⁻¹`, `ε₂ : a⁻¹ g_! ⟶ g'_! b⁻¹`, `ε : a⁻¹ (gf)_! ⟶ (g'f')_! c⁻¹`
each of which is the restriction of the corresponding map `μ`, `μ'`, `β₁`, `β₂`, `β` between
direct images. If the base change maps of direct images paste horizontally
(`CategoryTheory.mateEquiv_symm_paste_app`), then so do the restricted ones. Only the
components at the objects involved are used, so `κ`, `κ'`, `ε₁`, `ε₂` and `ε` are families of
morphisms rather than natural transformations. -/
theorem subfunctor_baseChange_paste_app
    (μ : fS ⋙ gS ≅ fgS) (μ' : f'S ⋙ g'S ≅ f'g'S)
    (β₁ : TwoSquare fS cI bI f'S) (β₂ : TwoSquare gS bI aI g'S) (β : TwoSquare fgS cI aI f'g'S)
    (hβ : ∀ F, aI.map (μ.hom.app F) ≫ β.app F =
      β₂.app (fS.obj F) ≫ g'S.map (β₁.app F) ≫ μ'.hom.app (cI.obj F))
    (ιf : fB ⟶ fS) (ιg : gB ⟶ gS) (ιfg : fgB ⟶ fgS)
    (ιf' : f'B ⟶ f'S) (ιg' : g'B ⟶ g'S) (ιf'g' : f'g'B ⟶ f'g'S)
    [∀ F, Mono (ιf'g'.app F)]
    (κ : ∀ F, gB.obj (fB.obj F) ⟶ fgB.obj F) (κ' : ∀ F, g'B.obj (f'B.obj F) ⟶ f'g'B.obj F)
    (hκ : ∀ F, κ F ≫ ιfg.app F = ιg.app (fB.obj F) ≫ gS.map (ιf.app F) ≫ μ.hom.app F)
    (hκ' : ∀ F, κ' F ≫ ιf'g'.app F =
      ιg'.app (f'B.obj F) ≫ g'S.map (ιf'.app F) ≫ μ'.hom.app F)
    (ε₁ : ∀ F, bI.obj (fB.obj F) ⟶ f'B.obj (cI.obj F))
    (ε₂ : ∀ F, aI.obj (gB.obj F) ⟶ g'B.obj (bI.obj F))
    (ε : ∀ F, aI.obj (fgB.obj F) ⟶ f'g'B.obj (cI.obj F))
    (hε₁ : ∀ F, ε₁ F ≫ ιf'.app (cI.obj F) = bI.map (ιf.app F) ≫ β₁.app F)
    (hε₂ : ∀ F, ε₂ F ≫ ιg'.app (bI.obj F) = aI.map (ιg.app F) ≫ β₂.app F)
    (hε : ∀ F, ε F ≫ ιf'g'.app (cI.obj F) = aI.map (ιfg.app F) ≫ β.app F) (F : CX) :
    aI.map (κ F) ≫ ε F = ε₂ (fB.obj F) ≫ g'B.map (ε₁ F) ≫ κ' (cI.obj F) := by
  rw [← cancel_mono (ιf'g'.app (cI.obj F))]
  simp only [Category.assoc, hε, hκ']
  rw [← Functor.map_comp_assoc, hκ]
  simp only [Functor.map_comp, Category.assoc, hβ]
  have hn := β₂.naturality (ιf.app F)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← reassoc_of% (hε₂ (fB.obj F)), ← g'S.map_comp_assoc, ← hε₁]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (ε₂ (fB.obj F) ≫ ·) (ιg'.naturality_assoc (ε₁ F) _).symm

end Paste

end CategoryTheory
