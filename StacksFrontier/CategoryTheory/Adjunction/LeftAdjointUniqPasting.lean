module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.MatePaste

/-!
# Pasting comparisons of left adjoints obtained by uniqueness

Consider two squares of categories placed side by side,

```
      F         F'        F''
  A ----→ B   A' ----→ B'   A'' ----→ B''
```

with "horizontal" functors `G₁ : B ⥤ B'`, `G₂ : B' ⥤ B''`, `H₁ : A ⥤ A'`, `H₂ : A' ⥤ A''` and
composites `G : B ⥤ B''`, `H : A ⥤ A''` identified with `G₁ ⋙ G₂` and `H₁ ⋙ H₂`, in which every
functor is a left adjoint. A comparison `F ⋙ G₁ ⟶ H₁ ⋙ F'` of left adjoints obtained by
`CategoryTheory.Adjunction.leftAdjointUniq` from a comparison of the right adjoints is
determined by that comparison, its conjugate. This file proves that the horizontal pasting of
two such comparisons is again the comparison obtained by uniqueness, as soon as the comparisons
of right adjoints paste.

It also records, in the same abstract setting, the formal steps of the compatibility of the
inclusion `j_! ⟶ j_*` of extension by zero into direct image with base change: the inclusion is
transposed to the identity under the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, and a comparison of
left adjoints obtained by uniqueness is detected on units.

## Main results

* `Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv` and
  `Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_hom`: the
  conjugates of a comparison obtained by uniqueness.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_associator_inv`: the conjugate of
  the inverse associator of three composable left adjoints.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.pasteH_leftAdjointUniq_inv`: the horizontal
  pasting of two comparisons obtained by uniqueness.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.twoSquare_eq_mateEquiv_symm`: the base change
  2-square as a mate along the horizontal adjunctions.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.unit_comp_map_comp_counit`: the canonical map
  from the left to the right adjoint of an adjoint triple is transposed to the identity.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.map_comp_baseChange_eq`: the inclusion of the
  left adjoint of an adjoint triple into the right adjoint commutes with base change.
* `Stacks.CategoryTheory.LeftAdjointUniqPasting.comp_eq_of_hom_ext`: a diagram chase identifying
  two composites in a single category through a chain of commuting squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.CategoryTheory.LeftAdjointUniqPasting

section Conjugate

variable {C D : Type*} [Category* C] [Category* D] {L L' : C ⥤ D} {R R' : D ⥤ C}

/-- The conjugate of the inverse of the comparison of two left adjoints obtained by uniqueness
from an isomorphism `E` of right adjoints is `E.inv`. -/
theorem conjugateEquiv_leftAdjointUniq_inv (a : L ⊣ R) (b : L' ⊣ R') (E : R' ≅ R) :
    conjugateEquiv a b (Adjunction.leftAdjointUniq a (b.ofNatIsoRight E)).inv = E.inv := by
  ext X
  simp only [Adjunction.leftAdjointUniq, Adjunction.ofNatIsoRight, Iso.symm_inv,
    conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom, conjugateEquiv_apply_app,
    conjugateEquiv_symm_apply_app, NatTrans.id_app, map_id, NatTrans.comp_app, comp_obj, id_obj,
    whiskerRight_app, Category.id_comp, map_comp, Category.assoc, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components_assoc]
  rw [← E.inv.naturality, ← Category.assoc, Adjunction.right_triangle_components,
    Category.id_comp]

/-- The conjugate of the comparison of two left adjoints obtained by uniqueness from an
isomorphism `E` of right adjoints is `E.hom`. -/
theorem conjugateEquiv_leftAdjointUniq_hom (a : L ⊣ R) (b : L' ⊣ R') (E : R' ≅ R) :
    conjugateEquiv b a (Adjunction.leftAdjointUniq a (b.ofNatIsoRight E)).hom = E.hom := by
  have h := conjugateEquiv_comm a b (Iso.hom_inv_id (Adjunction.leftAdjointUniq a
    (b.ofNatIsoRight E)))
  rw [conjugateEquiv_leftAdjointUniq_inv, Iso.inv_comp_eq, Category.comp_id] at h
  exact h

end Conjugate

section Associator

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B} {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}

/-- The conjugate of the inverse associator of three composable left adjoints is the inverse
associator of their right adjoints. -/
theorem conjugateEquiv_associator_inv (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (associator _ _ _).inv = (associator _ _ _).inv := by
  ext X
  simp only [comp_obj, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc, ← map_comp, associator_inv_app, map_id,
    Adjunction.comp_counit_app, Category.id_comp]
  simp

end Associator

section Horizontal

variable {A A' A'' B B' B'' : Type*} [Category* A] [Category* A'] [Category* A'']
  [Category* B] [Category* B'] [Category* B'']
  {F : A ⥤ B} {F' : A' ⥤ B'} {F'' : A'' ⥤ B''} {RF : B ⥤ A} {RF' : B' ⥤ A'} {RF'' : B'' ⥤ A''}
  {G₁ : B ⥤ B'} {G₂ : B' ⥤ B''} {G : B ⥤ B''} {RG₁ : B' ⥤ B} {RG₂ : B'' ⥤ B'} {RG : B'' ⥤ B}
  {H₁ : A ⥤ A'} {H₂ : A' ⥤ A''} {H : A ⥤ A''} {RH₁ : A' ⥤ A} {RH₂ : A'' ⥤ A'} {RH : A'' ⥤ A}
  (adjF : F ⊣ RF) (adjF' : F' ⊣ RF') (adjF'' : F'' ⊣ RF'')
  (adjG₁ : G₁ ⊣ RG₁) (adjG₂ : G₂ ⊣ RG₂) (adjG : G ⊣ RG)
  (adjH₁ : H₁ ⊣ RH₁) (adjH₂ : H₂ ⊣ RH₂) (adjH : H ⊣ RH)

/-- **Horizontal pasting of comparisons of left adjoints obtained by uniqueness.** If the
comparisons `e₁`, `e₂` and `e` of right adjoints paste, through comparisons `dG`, `dH` of right
adjoints conjugate to `eG` and `eH`, then the horizontal pasting of the comparisons
`F ⋙ G₁ ⟶ H₁ ⋙ F'` and `F' ⋙ G₂ ⟶ H₂ ⋙ F''` of left adjoints obtained from `e₁` and `e₂` is
the comparison `F ⋙ G ⟶ H ⋙ F''` obtained from `e`. -/
theorem pasteH_leftAdjointUniq_inv
    (e₁ : RG₁ ⋙ RF ≅ RF' ⋙ RH₁) (e₂ : RG₂ ⋙ RF' ≅ RF'' ⋙ RH₂) (e : RG ⋙ RF ≅ RF'' ⋙ RH)
    (eG : G₁ ⋙ G₂ ≅ G) (eH : H₁ ⋙ H₂ ≅ H) (dG : RG₂ ⋙ RG₁ ≅ RG) (dH : RH₂ ⋙ RH₁ ≅ RH)
    (hG : conjugateEquiv (adjG₁.comp adjG₂) adjG eG.inv = dG.hom)
    (hH : conjugateEquiv adjH (adjH₁.comp adjH₂) eH.hom = dH.inv)
    (he : e.inv = whiskerLeft RF'' dH.inv ≫ (associator _ _ _).inv ≫
      whiskerRight e₂.inv RH₁ ≫ (associator _ _ _).hom ≫ whiskerLeft RG₂ e₁.inv ≫
      (associator _ _ _).inv ≫ whiskerRight dG.hom RF) :
    whiskerLeft F eG.inv ≫ (associator _ _ _).inv ≫
        whiskerRight (Adjunction.leftAdjointUniq (adjH₁.comp adjF')
          ((adjF.comp adjG₁).ofNatIsoRight e₁)).inv G₂ ≫ (associator _ _ _).hom ≫
        whiskerLeft H₁ (Adjunction.leftAdjointUniq (adjH₂.comp adjF'')
          ((adjF'.comp adjG₂).ofNatIsoRight e₂)).inv ≫ (associator _ _ _).inv ≫
        whiskerRight eH.hom F'' =
      (Adjunction.leftAdjointUniq (adjH.comp adjF'') ((adjF.comp adjG).ofNatIsoRight e)).inv := by
  apply (conjugateEquiv (adjH.comp adjF'') (adjF.comp adjG)).injective
  rw [conjugateEquiv_leftAdjointUniq_inv, he,
    ← conjugateEquiv_comp _ (adjF.comp (adjG₁.comp adjG₂)),
    ← conjugateEquiv_comp _ ((adjF.comp adjG₁).comp adjG₂),
    ← conjugateEquiv_comp _ ((adjH₁.comp adjF').comp adjG₂),
    ← conjugateEquiv_comp _ (adjH₁.comp (adjF'.comp adjG₂)),
    ← conjugateEquiv_comp _ (adjH₁.comp (adjH₂.comp adjF'')),
    ← conjugateEquiv_comp _ ((adjH₁.comp adjH₂).comp adjF''),
    conjugateEquiv_whiskerRight, hH, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_leftAdjointUniq_inv,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_leftAdjointUniq_inv, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, hG]
  simp only [Category.assoc]

end Horizontal

section Mate

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'} {Lg : A ⥤ A'} {Rg : A' ⥤ A}
  {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'} {Rc : B' ⥤ A}

/-- **The base change map as a mate along the horizontal adjunctions.** If the two comparisons
of composite left adjoints are conjugate to comparisons `df`, `dg` of composite right adjoints,
then the base change map `Stacks.CategoryTheory.BaseChange.twoSquare`, the mate along the
vertical adjunctions, is the mate along the horizontal adjunctions of `df ≫ dg⁻¹`. -/
theorem twoSquare_eq_mateEquiv_symm (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg)
    (adjg' : Lg' ⊣ Rg') (adjc : Lc ⊣ Rc) (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (dg : Rf' ⋙ Rg ≅ Rc) (df : Rg' ⋙ Rf ≅ Rc)
    (hg : conjugateEquiv adjc (adjg.comp adjf') eg.hom = dg.inv)
    (hf : conjugateEquiv (adjf.comp adjg') adjc ef.inv = df.hom) :
    Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef =
      (mateEquiv adjg' adjg).symm (TwoSquare.mk _ _ _ _ (df.hom ≫ dg.inv)) := by
  refine (Equiv.eq_symm_apply _).2 ?_
  refine (iterated_mateEquiv_conjugateEquiv adjf adjf' adjg adjg' _).trans ?_
  change conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') (eg.hom ≫ ef.inv) = df.hom ≫ dg.inv
  rw [← conjugateEquiv_comp _ adjc, hf, hg]

end Mate

section ExtensionByZero

variable {CX CXb CX' CXb' : Type*} [Category* CX] [Category* CXb] [Category* CX']
  [Category* CXb']
  {jS : CX ⥤ CXb} {jR : CXb ⥤ CX} {jP : CX ⥤ CXb}
  {jS' : CX' ⥤ CXb'} {jR' : CXb' ⥤ CX'} {jP' : CX' ⥤ CXb'}
  {φI : CXb ⥤ CXb'} {φP : CXb' ⥤ CXb} {gI : CX ⥤ CX'} {gP : CX' ⥤ CX}
  (s : jS ⊣ jR) (t : jR ⊣ jP) (s' : jS' ⊣ jR') (t' : jR' ⊣ jP') (a : φI ⊣ φP) (b : gI ⊣ gP)

/-- For an adjoint triple `jS ⊣ jR ⊣ jP` whose first unit is invertible, the canonical map
`jS ⟶ jP` (the unit of `jR ⊣ jP` followed by `jP` of the inverse of the unit of `jS ⊣ jR`) is
transposed, under both adjunctions, to the identity. -/
theorem unit_comp_map_comp_counit (F : CX) [IsIso (s.unit.app F)] :
    s.unit.app F ≫ jR.map (t.unit.app (jS.obj F) ≫ jP.map (inv (s.unit.app F))) ≫
      t.counit.app F = 𝟙 F := by
  have h1 := t.counit_naturality (inv (s.unit.app F))
  have h2 := t.left_triangle_components (jS.obj F)
  simp only [Functor.id_obj, Functor.comp_obj] at h1
  rw [Functor.map_comp, Category.assoc, h1, ← Category.assoc (jR.map _), h2, Category.id_comp,
    IsIso.hom_inv_id]
  rfl

/-- **Compatibility of the inclusion of extension by zero into direct image with base change**,
abstractly. Let `jS ⊣ jR ⊣ jP` and `jS' ⊣ jR' ⊣ jP'` be adjoint triples with maps `ε : jS ⟶ jP`,
`ε' : jS' ⟶ jP'` transposed to the identity, let `φI ⊣ φP` and `gI ⊣ gP` be adjunctions, and let
`e : φP ⋙ jR ≅ jR' ⋙ gP` identify the composite right adjoints. Let `β : jP ⋙ φI ⟶ gI ⋙ jP'` be
a base change map described on units by a comparison `γ : gP ⋙ jP ⟶ jP' ⋙ φP`. If `γ`, `e` and
the counits of `jR ⊣ jP`, `jR' ⊣ jP'` are compatible, then `φI ε` followed by `β` is the
comparison `jS ⋙ φI ⟶ gI ⋙ jS'` obtained from `e` followed by `ε'`. -/
theorem map_comp_baseChange_eq (e : φP ⋙ jR ≅ jR' ⋙ gP) (ε : jS ⟶ jP) (ε' : jS' ⟶ jP')
    (hε : ∀ F, s.unit.app F ≫ jR.map (ε.app F) ≫ t.counit.app F = 𝟙 F)
    (hε' : ∀ G, s'.unit.app G ≫ jR'.map (ε'.app G) ≫ t'.counit.app G = 𝟙 G)
    [∀ G, IsIso (s'.unit.app G)]
    (γ : gP ⋙ jP ⟶ jP' ⋙ φP) (β : jP ⋙ φI ⟶ gI ⋙ jP')
    (hβ : ∀ F, a.unit.app (jP.obj F) ≫ φP.map (β.app F) =
      jP.map (b.unit.app F) ≫ γ.app (gI.obj F))
    (hsec : ∀ G, jR.map (γ.app G) ≫ e.hom.app (jP'.obj G) ≫ gP.map (t'.counit.app G) =
      t.counit.app (gP.obj G))
    (F : CX) :
    φI.map (ε.app F) ≫ β.app F =
      (Adjunction.leftAdjointUniq (b.comp s') ((s.comp a).ofNatIsoRight e)).inv.app F ≫
        ε'.app (gI.obj F) := by
  set iso := Adjunction.leftAdjointUniq (b.comp s') ((s.comp a).ofNatIsoRight e)
  rw [← cancel_epi (iso.hom.app F), Iso.hom_inv_id_app_assoc]
  apply (t'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    ← cancel_epi (s'.unit.app (gI.obj F)), hε']
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit]
  have hiso := Adjunction.unit_leftAdjointUniq_hom_app (b.comp s')
    ((s.comp a).ofNatIsoRight e) F
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_map,
    Category.assoc] at hiso
  have he1 := e.hom.naturality (φI.map (ε.app F))
  have he2 := e.hom.naturality (β.app F)
  simp only [Functor.comp_map] at he1 he2
  have ha := a.unit_naturality (ε.app F)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hiso, ← reassoc_of% he1, ← reassoc_of% he2, ← jR.map_comp_assoc (a.unit.app _),
    ha, jR.map_comp_assoc, ← jR.map_comp_assoc (a.unit.app (jP.obj F)), hβ, jR.map_comp_assoc,
    hsec, t.counit_naturality]
  have h3 := reassoc_of% (hε F)
  exact h3 (b.unit.app F)

end ExtensionByZero

section Assembly

variable {D : Type*} [Category* D] {A A₂ B B₂ C C₂ E E₂ M T : D}

/-- A diagram chase in a single category: a map `θφ ≫ βp ≫ i₁` out of `A` is identified with
`i₂ ≫ θ'` by testing against a morphism `e₁'` that separates maps out of `E`, through a chain
of commuting squares. -/
theorem comp_eq_of_hom_ext (θφ : A ⟶ B) (βp : B ⟶ C) (i₁ : C ⟶ M) (i₂ : A ⟶ E) (i₂' : E ⟶ A)
    (θ' : E ⟶ M) (e₁' : M ⟶ T) (ε₂' : E ⟶ E₂) (n : T ⟶ E₂) (n' : E₂ ⟶ T)
    (e₁φ : C ⟶ C₂) (b₁ : C₂ ⟶ T) (pe₁ : B ⟶ B₂) (βp' : B₂ ⟶ C₂) (e₂φ : A ⟶ A₂)
    (m : B₂ ⟶ A₂) (m' : A₂ ⟶ B₂) (β₂ : A₂ ⟶ E₂)
    (hext : ∀ x y : E ⟶ M, x ≫ e₁' = y ≫ e₁' → x = y)
    (hi : i₂' ≫ i₂ = 𝟙 E) (hi' : i₂ ≫ i₂' = 𝟙 A)
    (hθ' : θ' ≫ e₁' = ε₂' ≫ n') (hA₁ : i₁ ≫ e₁' = e₁φ ≫ b₁) (hnat : βp ≫ e₁φ = pe₁ ≫ βp')
    (hθ : θφ ≫ pe₁ = e₂φ ≫ m') (hB : m ≫ β₂ = βp' ≫ b₁ ≫ n) (hm : m' ≫ m = 𝟙 A₂)
    (hn : n ≫ n' = 𝟙 T) (hA₂ : e₂φ ≫ β₂ = i₂ ≫ ε₂') :
    θφ ≫ βp ≫ i₁ = i₂ ≫ θ' := by
  have key : i₂' ≫ θφ ≫ βp ≫ i₁ = θ' := by
    apply hext
    have hB' : m' ≫ m ≫ β₂ ≫ n' = m' ≫ βp' ≫ b₁ ≫ n ≫ n' := by
      rw [reassoc_of% hB]
    rw [reassoc_of% hm, hn, Category.comp_id] at hB'
    rw [hθ', Category.assoc, Category.assoc, Category.assoc, hA₁, reassoc_of% hnat,
      reassoc_of% hθ, ← hB', reassoc_of% hA₂, reassoc_of% hi]
  rw [← key, reassoc_of% hi']

end Assembly

end Stacks.CategoryTheory.LeftAdjointUniqPasting
