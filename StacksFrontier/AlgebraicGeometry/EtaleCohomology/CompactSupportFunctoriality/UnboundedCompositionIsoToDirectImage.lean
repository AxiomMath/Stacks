module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedCompositionToDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0H6X], compatibility (1), on `D(X_étale, Λ)`

For separated morphisms of finite type `f : X ⟶ Y` and `g : Y ⟶ Z` of quasi-compact and
quasi-separated schemes and a torsion ring `Λ`, the map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X] on
`D(X_étale, Λ)` (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedToDirectImage`) is
compatible with the isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) and the composition isomorphism
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*`: compatibility (1) of the remark, whose proof the source omits.

Through the compactifications of the proof of [Stacks, Tag 0F7J] this is the compatibility of
the open immersion case of [Stacks, Tag 0F7B] with `Rj_! ⟶ Rj_*`
(`etaleModuleExtensionByZeroDirectImageUnboundedIso_hom_comp_toDirectImage`), of `Rj_! ⟶ Rj_*`
with composition of open immersions
(`etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_comp`), and the coherence of the
composition isomorphisms of unbounded derived direct images; it is transported to arbitrary
compactifications by the independence of the map of the compactification.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso_hom_comp_toDirectImage`: for the
  compactifications of the proof of [Stacks, Tag 0F7J].
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_comp_toDirectImage`:
  **[Stacks, Tag 0H6X] (1) on `D(X_étale, Λ)`.**

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/-! ### Abstract rearrangements -/

section Algebra

variable {C : Type*} [Category* C]

/-- Two factorizations through a common isomorphism, inverted, stated on isomorphisms. -/
private theorem iso_chain_right {a b c d e f : C} (z : a ≅ b) (x₁ : a ≅ c) (y₁ : c ≅ d)
    (w₁ : b ≅ d) (x₂ : a ≅ e) (y₂ : e ≅ f) (w₂ : b ≅ f)
    (hA : x₁.hom ≫ y₁.hom = z.hom ≫ w₁.hom) (hB : x₂.hom ≫ y₂.hom = z.hom ≫ w₂.hom) :
    w₁.inv ≫ w₂.hom ≫ y₂.inv ≫ x₂.inv = y₁.inv ≫ x₁.inv := by
  have hz : z.inv = w₂.hom ≫ y₂.inv ≫ x₂.inv := by
    rw [← cancel_epi z.hom, Iso.hom_inv_id, ← reassoc_of% hB]
    simp
  have h₁ : y₁.inv ≫ x₁.inv = w₁.inv ≫ z.inv := by
    rw [← cancel_epi y₁.hom, Iso.hom_inv_id_assoc, ← cancel_epi x₁.hom, Iso.hom_inv_id,
      reassoc_of% hA]
    simp
  rw [h₁, hz]

/-- Two factorizations out of a common isomorphism, stated on isomorphisms. -/
private theorem iso_chain_left {a b c d e f : C} (z : a ≅ b) (q : b ≅ c) (p : a ≅ d)
    (r : d ≅ c) (s : b ≅ e) (t : a ≅ f) (u : f ≅ e)
    (hA : z.hom ≫ q.hom = p.hom ≫ r.hom) (hB : z.hom ≫ s.hom = t.hom ≫ u.hom) :
    r.hom ≫ q.inv ≫ s.hom ≫ u.inv ≫ t.inv = p.inv := by
  have h₁ : r.hom ≫ q.inv = p.inv ≫ z.hom := by
    rw [← cancel_epi p.hom, Iso.hom_inv_id_assoc, ← reassoc_of% hA]
    simp
  rw [reassoc_of% h₁, reassoc_of% hB]
  simp

/-- The chase behind `derivedLowerShriekUnboundedRestrictBase_comp_toDirectImage`, stated on
variables. -/
private theorem inner_chain {e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃ e₁₄ : C}
    (β : e₀ ⟶ e₁) (eiR : e₁ ⟶ e₂) (rI : e₂ ⟶ e₃) (ri : e₃ ⟶ e₄) (εU : e₄ ⟶ e₅) (lfi : e₅ ⟶ e₆)
    (eiτ : e₂ ⟶ e₇) (rI' : e₇ ⟶ e₄) (eiW : e₁ ⟶ e₇) (εiR : e₁ ⟶ e₈) (RiW : e₈ ⟶ e₅)
    (fbε : e₀ ⟶ e₉) (lbinvE : e₉ ⟶ e₁₀) (lfiE : e₁₀ ⟶ e₈) (rr₁ : e₈ ⟶ e₁₂) (rr₂ : e₁₂ ⟶ e₅)
    (Rhε : e₁₀ ⟶ e₁₁) (lfiR : e₁₁ ⟶ e₁₂) (fbRb : e₉ ⟶ e₁₃) (lbinvR : e₁₃ ⟶ e₁₁)
    (fbZ : e₀ ⟶ e₁₃) (fbL : e₁₃ ⟶ e₁₄) (labf : e₁₄ ⟶ e₆)
    (hf2 : rI ≫ ri = eiτ ≫ rI') (hf12 : eiR ≫ eiτ = eiW) (hf3 : eiW ≫ rI' ≫ εU = εiR ≫ RiW)
    (hC : β ≫ εiR = fbε ≫ lbinvE ≫ lfiE) (hRiW : RiW = rr₁ ≫ rr₂)
    (hf5 : lfiE ≫ rr₁ = Rhε ≫ lfiR) (hf6 : lbinvE ≫ Rhε = fbRb ≫ lbinvR)
    (hf7 : fbε ≫ fbRb = fbZ) (hLI : lbinvR ≫ lfiR ≫ rr₂ ≫ lfi = fbL ≫ labf) :
    β ≫ eiR ≫ rI ≫ ri ≫ εU ≫ lfi = fbZ ≫ fbL ≫ labf := by
  rw [reassoc_of% hf2, reassoc_of% hf12, reassoc_of% hf3, reassoc_of% hC, hRiW, Category.assoc,
    reassoc_of% hf5, reassoc_of% hf6, reassoc_of% hf7, hLI]

/-- Moving an inverse across, stated on variables. -/
private theorem comp_hom_of_comp_inv {a b c d : C} (x : a ⟶ b) (y : b ⟶ c) (l : d ≅ c)
    (z : a ⟶ d) (h : x ≫ y ≫ l.inv = z) : x ≫ y = z ≫ l.hom := by
  rw [← h]
  simp

/-- The assembly of `derivedLowerShriekUnboundedCompOverIso_hom_comp_toDirectImage`, stated on
variables. -/
private theorem final_chain {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    (F' : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (H : D₀ ⥤ D₂) {x₀ x₁ x₂ : D₀} {y₁ y₂ y₃ y₄ y₅ y₆ : D₁}
    {w v : D₂} (e₁ : x₀ ⟶ x₁) (Zab : x₁ ⟶ x₂) (εab : x₀ ⟶ x₂) (e₂X : H.obj x₁ ⟶ G.obj (F'.obj x₁))
    (e₂R : H.obj x₂ ⟶ G.obj (F'.obj x₂)) (β : F'.obj x₁ ⟶ y₁) (eiR : y₁ ⟶ y₂) (rI : y₂ ⟶ y₃)
    (ri : y₃ ⟶ y₄) (εU : y₄ ⟶ y₅) (lfi : y₅ ⟶ y₆) (lfiHom : y₆ ⟶ y₅) (labf : F'.obj x₂ ⟶ y₆)
    (lig : G.obj y₅ ⟶ w) (lfg : w ⟶ v) (labfg : H.obj x₂ ⟶ v)
    {x₃ x₄ : D₀} (Z₁ : x₁ ⟶ x₃) (Z₂ : x₃ ⟶ x₄) (Z₃ : x₄ ⟶ x₂) (hZ : Zab = Z₁ ≫ Z₂ ≫ Z₃)
    (hinner : β ≫ eiR ≫ rI ≫ ri ≫ εU ≫ lfi = F'.map (Z₁ ≫ Z₂) ≫ F'.map Z₃ ≫ labf)
    (hlfi : lfi ≫ lfiHom = 𝟙 y₅)
    (hE : εab = e₁ ≫ Z₁ ≫ Z₂ ≫ Z₃) (he₂ : H.map Zab ≫ e₂R = e₂X ≫ G.map (F'.map Zab))
    (hLI : e₂R ≫ G.map labf ≫ G.map lfiHom ≫ lig ≫ lfg = labfg) :
    ((H.map e₁ ≫ e₂X) ≫ G.map β ≫ G.map eiR ≫ G.map rI) ≫ G.map ri ≫ G.map εU ≫ lig ≫ lfg =
      H.map εab ≫ labfg := by
  simp only [Category.assoc]
  have hi : β ≫ eiR ≫ rI ≫ ri ≫ εU = F'.map Zab ≫ labf ≫ lfiHom := by
    have hF : F'.map Zab = F'.map (Z₁ ≫ Z₂) ≫ F'.map Z₃ := by
      rw [hZ, ← F'.map_comp, Category.assoc]
    rw [hF, Category.assoc, ← reassoc_of% hinner, hlfi, Category.comp_id]
  have hG : G.map β ≫ G.map eiR ≫ G.map rI ≫ G.map ri ≫ G.map εU ≫ lig ≫ lfg =
      G.map (F'.map Zab) ≫ G.map labf ≫ G.map lfiHom ≫ lig ≫ lfg := by
    simp only [← G.map_comp_assoc]
    rw [hi]
  rw [hG, ← reassoc_of% he₂, hLI, hE, ← hZ, H.map_comp, Category.assoc]

end Algebra

attribute [local instance] HasDerivedCategory.standard

/-! ### Coherence of the unbounded Leray isomorphisms -/

section Leray

variable (Λ : Type r) [Ring Λ]

/-- **Two decompositions of a direct image along a cartesian square**: for `ab = a ≫ b`,
`f = a ≫ f'` and `h = b ≫ f̄ = f' ≫ i`, the two ways of taking `R(ab ≫ f̄)_* = R(f ≫ i)_*` apart
into `Ra_*`, `Rb_*` and `Rf̄_*`, or into `Ra_*`, `Rf'_*` and `Ri_*`, agree. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_square {X U T Y W : Scheme.{u}}
    (a : X ⟶ U) (b : U ⟶ T) (f' : U ⟶ Y) (fb : T ⟶ W) (i : Y ⟶ W) (f : X ⟶ Y) (ab : X ⟶ T)
    (h : U ⟶ W) (fi : X ⟶ W) (hab : ab = a ≫ b) (hf : f = a ≫ f') (hb : h = b ≫ fb)
    (hf' : h = f' ≫ i) (h₁ : fi = ab ≫ fb) (h₂ : fi = a ≫ h) (h₃ : fi = f ≫ i)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ b fb h hb).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a).obj K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f' i h hf').hom.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ i).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a f' f hf).inv.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f i fi h₃).inv.app K =
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ fb).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a b ab hab).inv.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fb fi h₁).inv.app K :=
  iso_chain_right ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a h fi h₂).app K)
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fb fi h₁).app K)
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ fb).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a b ab hab).app K))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ b fb h hb).app
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a).obj K))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f i fi h₃).app K)
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ i).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a f' f hf).app K))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f' i h hf').app
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a).obj K))
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ a b fb ab hab h hb fi h₁ h₂ K)
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ a f' i f hf h hf' fi h₃ h₂ K)

/-- **Two decompositions of a direct image along a composite**: for `fi = ab ≫ f̄ = f ≫ i` and
`fg = ab ≫ (f̄ ≫ ḡ) = f ≫ g` with `g = i ≫ ḡ`, taking `R(fg)_*` apart through `R(ab)_*`,
`Rf̄_*`, `Rḡ_*` or through `Rf_*`, `Ri_*`, `Rḡ_*` agrees. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_triangle {X T Y W Z : Scheme.{u}}
    (ab : X ⟶ T) (fb : T ⟶ W) (gb : W ⟶ Z) (f : X ⟶ Y) (i : Y ⟶ W) (g : Y ⟶ Z) (fi : X ⟶ W)
    (fgb : T ⟶ Z) (fg : X ⟶ Z) (h₁ : fi = ab ≫ fb) (hfgb : fgb = fb ≫ gb) (h₂ : fg = fi ≫ gb)
    (h₃ : fg = ab ≫ fgb) (hfi : fi = f ≫ i) (hg : g = i ≫ gb) (h₄ : fg = f ≫ g)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ fb gb fgb hfgb).hom.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ ab).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ gb).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fb fi h₁).inv.app K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ gb).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f i fi hfi).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ i gb g hg).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg h₄).inv.app K =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fgb fg h₃).inv.app K :=
  iso_chain_left ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ fi gb fg h₂).app K)
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ gb).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fb fi h₁).app K))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ ab fgb fg h₃).app K)
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ fb gb fgb hfgb).app
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ ab).obj K))
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ gb).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f i fi hfi).app K))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg h₄).app K)
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ i gb g hg).app
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K))
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ ab fb gb fi h₁ fgb hfgb fg h₂ h₃ K)
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ f i gb fi hfi g hg fg h₂ h₄ K)

end Leray

/-! ### Compatibility (1) through the compactifications of the proof of [Stacks, Tag 0F7J] -/

section Composition

attribute [local instance high] CompactificationOf.etale_restrictBaseι

variable (Λ : Type) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z : Scheme.{u}}
  {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- The map `Rp_! ⟶ Rp_*` of a compactification, componentwise. -/
private theorem derivedLowerShriekUnboundedToDirectImage_app_eq {A B : Scheme.{u}} (p : A ⟶ B)
    (j : CompactificationOf (Over.mk p)) (M : DerivedCategory (EtaleModules.{u, 0} Λ A)) :
    (derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ p j).app M =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).map
        ((etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, 0} Λ j.immersion).app M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ j.immersion j.toBase p
        (CompactificationOf.immersion_toBase j).symm).inv.app M := rfl

include hΛ in
/-- **The map `Rf_! ⟶ Rf_*` against the open immersion case of [Stacks, Tag 0F7B]**, for the
compactifications of the proof of [Stacks, Tag 0F7J]: `Rf̄_* b_! a_! ≅ i_! Rf'_* a_!` followed by
`i_!` of `Rf_! ⟶ Rf_*`, by `i_! ⟶ Ri_*` and by `Ri_* Rf_* ≅ R(f ≫ i)_*` is `Rf̄_*` of
`b_! a_! ⟶ b_! Ra_* ⟶ Rb_* Ra_* ≅ R(a ≫ b)_*` followed by `Rf̄_* R(a ≫ b)_* ≅ R(f ≫ i)_*`. -/
theorem derivedLowerShriekUnboundedRestrictBase_comp_toDirectImage [CompactSpace jg.space]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
        (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K) ≫
      (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).inv.app K)) ≫
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K)) ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion).map
        ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K) ≫
      (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, 0} Λ jg.immersion).app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f jg.immersion (f ≫ jg.immersion)
        rfl).inv.app K =
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBaseι jg jX)).mapDerivedCategory.map
            ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
              (CompactificationOf.restrictBase jg jX).immersion).app K) ≫
          (etaleModuleExtensionByZeroToDirectImageUnbounded Λ
            (CompactificationOf.restrictBaseι jg jX)).app
            ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion).obj K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) rfl).inv.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
        jX.toBase (f ≫ jg.immersion)
        (CompactificationOf.immersion_toBase
          (CompactificationOf.overBar jg jX)).symm).inv.app K := by
  have hf : f = (CompactificationOf.restrictBase jg jX).immersion ≫
      (CompactificationOf.restrictBase jg jX).toBase :=
    (CompactificationOf.immersion_toBase (CompactificationOf.restrictBase jg jX)).symm
  have sq := IsPullback.of_hasPullback jX.toBase jg.immersion
  have hsq : (CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion =
      CompactificationOf.restrictBaseι jg jX ≫ jX.toBase := sq.w.symm
  -- the map `Rf_! ⟶ Rf_*` of the induced compactification, componentwise
  have hτ := derivedLowerShriekUnboundedToDirectImage_app_eq Λ f
    (CompactificationOf.restrictBase jg jX) K
  have hf2 := ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion).inv.naturality
    ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
      (CompactificationOf.restrictBase jg jX)).app K)).symm
  have hf12 : (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).inv.app K)) ≫
      (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
        ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K) =
      (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
            (CompactificationOf.restrictBase jg jX).immersion).app K) ≫
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBase jg jX).toBase f hf).inv.app K) := by
    rw [hτ, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    rfl
  have hf3 := (etaleModuleExtensionByZeroToDirectImageUnbounded Λ jg.immersion).naturality
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
            (CompactificationOf.restrictBase jg jX).immersion).app K) ≫
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBase jg jX).toBase f hf).inv.app K)
  have hC₀ : (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
        sq).hom.app ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K) ≫
      (etaleModuleExtensionByZeroToDirectImageUnbounded Λ jg.immersion).app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).toBase).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).toBase jg.immersion
        ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) rfl).inv.app
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
        ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
          (CompactificationOf.restrictBaseι jg jX)).app
          ((etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.restrictBaseι jg jX) jX.toBase
        ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) hsq).inv.app
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K) :=
    NatTrans.congr_app
      (etaleModuleExtensionByZeroDirectImageUnboundedIso_hom_comp_toDirectImage Λ hΛ jX.toBase
        jg.immersion (CompactificationOf.restrictBaseι jg jX)
        (CompactificationOf.restrictBase jg jX).toBase sq) _
  have hC := comp_hom_of_comp_inv _ _ (((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).toBase jg.immersion
        ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) rfl).app
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K))) _ hC₀
  have hf5 := ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
    (CompactificationOf.restrictBase jg jX).toBase jg.immersion
    ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) rfl).hom.naturality
    ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
      (CompactificationOf.restrictBase jg jX).immersion).app K)).symm
  have hf6 := ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
    (CompactificationOf.restrictBaseι jg jX) jX.toBase
    ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) hsq).inv.naturality
    ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
      (CompactificationOf.restrictBase jg jX).immersion).app K)).symm
  have hf7 := (Functor.map_comp _ _ _).symm.trans (congrArg
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
    ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
      (CompactificationOf.restrictBaseι jg jX)).naturality
      ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
        (CompactificationOf.restrictBase jg jX).immersion).app K)).symm)
  have hLI := etaleModuleDerivedDirectImageUnboundedLerayIso_square Λ
    (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
    (CompactificationOf.restrictBase jg jX).toBase jX.toBase jg.immersion f
    ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
    ((CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion) (f ≫ jg.immersion) rfl hf hsq
    rfl (CompactificationOf.immersion_toBase (CompactificationOf.overBar jg jX)).symm
    ((congrArg (· ≫ jg.immersion) hf).trans (Category.assoc _ _ _)) rfl K
  exact inner_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf2 hf12 hf3
    (hC.trans (Category.assoc _ _ _))
    (Functor.map_comp _ _ _) hf5 hf6 hf7 hLI

include hΛ in
/-- **[Stacks, Tag 0H6X] (1) for the compactifications of the proof of [Stacks, Tag 0F7J]**, on
`D(X_étale, Λ)` for a torsion ring `Λ`: the isomorphism
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of `derivedLowerShriekUnboundedCompOverIso`, followed by `Rg_!` of
`Rf_! ⟶ Rf_*`, by `Rg_! ⟶ Rg_*` at `Rf_*` and by `Rg_* Rf_* ≅ R(g ∘ f)_*`, is the map
`R(g ∘ f)_! ⟶ R(g ∘ f)_*`. -/
theorem derivedLowerShriekUnboundedCompOverIso_hom_comp_toDirectImage [CompactSpace jg.space]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
          ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
            (CompactificationOf.restrictBase jg jX)).app K) ≫
        (derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ g jg).app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f g (f ≫ g) rfl).inv.app K =
      (derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ (f ≫ g)
        (CompactificationOf.compOver jg jX)).app K := by
  have hco := NatTrans.congr_app (show (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom =
      (Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) ≪≫
          Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX))).hom
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jX.toBase ≫ jg.toBase)) ≫
        Functor.whiskerLeft ((etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory ⋙
            (etaleModuleExtensionByZero.{u, 0} Λ
              (CompactificationOf.restrictBaseι jg jX)).mapDerivedCategory)
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase
            (jX.toBase ≫ jg.toBase) rfl).hom) ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory
          (Functor.whiskerRight (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase
            jg.immersion (CompactificationOf.restrictBaseι jg jX)
            (CompactificationOf.restrictBase jg jX).toBase
            (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom
            (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase)) ≫
        Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).inv
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).toBase ⋙
            (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory) ⋙
            etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase) ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion ⋙
            etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).toBase)
          (Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
            jg.immersion).inv
            (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase)) from rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map] at hco
  have hg : g = jg.immersion ≫ jg.toBase := (CompactificationOf.immersion_toBase jg).symm
  have hE : (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, 0} Λ
        ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX)).app K =
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) ≪≫
          Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX))).hom.app K ≫
        (etaleModuleExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBaseι jg jX)).mapDerivedCategory.map
          ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
            (CompactificationOf.restrictBase jg jX).immersion).app K) ≫
        (etaleModuleExtensionByZeroToDirectImageUnbounded Λ
          (CompactificationOf.restrictBaseι jg jX)).app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) rfl).inv.app K :=
    NatTrans.congr_app (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_comp Λ
      (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)) K
  have he₂ := ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl).hom.naturality
      ((etaleModuleExtensionByZero.{u, 0} Λ
        (CompactificationOf.restrictBaseι jg jX)).mapDerivedCategory.map
          ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ
            (CompactificationOf.restrictBase jg jX).immersion).app K) ≫
        (etaleModuleExtensionByZeroToDirectImageUnbounded Λ
          (CompactificationOf.restrictBaseι jg jX)).app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) rfl).inv.app K))
  have hLI := etaleModuleDerivedDirectImageUnboundedLerayIso_triangle Λ
    ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
    jX.toBase jg.toBase f jg.immersion g (f ≫ jg.immersion) (jX.toBase ≫ jg.toBase) (f ≫ g)
    (CompactificationOf.immersion_toBase (CompactificationOf.overBar jg jX)).symm rfl
    ((congrArg (f ≫ ·) hg).trans (Category.assoc _ _ _).symm)
    ((CompactificationOf.immersion_toBase (CompactificationOf.compOver jg jX)).symm) rfl hg rfl K
  rw [hco, derivedLowerShriekUnboundedToDirectImage_app_eq Λ g jg,
    derivedLowerShriekUnboundedToDirectImage_app_eq Λ (f ≫ g) (CompactificationOf.compOver jg jX)]
  simp only [Category.assoc]
  have key := final_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jX.toBase ≫ jg.toBase))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (derivedLowerShriekUnboundedRestrictBase_comp_toDirectImage Λ hΛ jg jX K)
    (Iso.inv_hom_id_app _ _) hE he₂ hLI
  have r1 : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
        (CompactificationOf.compOver jg jX).toBase).map
      ((etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, 0} Λ
        (CompactificationOf.compOver jg jX).immersion).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.compOver jg jX).immersion (CompactificationOf.compOver jg jX).toBase
        (f ≫ g)
        (CompactificationOf.immersion_toBase (CompactificationOf.compOver jg jX)).symm).inv.app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jX.toBase ≫ jg.toBase)).map
      ((etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, 0} Λ
        ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX)).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
        (jX.toBase ≫ jg.toBase) (f ≫ g)
        (CompactificationOf.immersion_toBase
          (CompactificationOf.compOver jg jX)).symm).inv.app K := rfl
  have p1 : (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
      ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
        (CompactificationOf.restrictBase jg jX)).app K) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion).map
          ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f
            (CompactificationOf.restrictBase jg jX)).app K)) := rfl
  rw [p1]
  refine Eq.trans ?_ (key.trans r1.symm)
  congr 1
  exact (Category.assoc _ _ _).symm

end Composition

section CompatibilityOne

variable (Λ : Type) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f]
  [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- **[Stacks, Tag 0H6X], compatibility (1), on `D(X_étale, Λ)`** for a torsion ring `Λ`: the map
`Rf_! ⟶ Rf_*` is compatible with the isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) and the composition isomorphism
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` of Cohomology on Sites, Tag 0D6E, for arbitrary compactifications
`jf`, `jg`, `j` of `f`, `g` and `g ∘ f`: for `K` in `D(X_étale, Λ)`,
`R(g ∘ f)_! K ≅ Rg_! Rf_! K ⟶ Rg_! Rf_* K ⟶ Rg_* Rf_* K ≅ R(g ∘ f)_* K` is the map
`R(g ∘ f)_! K ⟶ R(g ∘ f)_* K`. -/
@[stacks 0H6X "(1), on D(X_étale, Λ), Λ torsion"]
theorem derivedLowerShriekUnboundedCompIso_hom_comp_toDirectImage
    (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
    (j : CompactificationOf (Over.mk (f ≫ g))) (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
          ((derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ f jf).app K) ≫
        (derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ g jg).app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f g (f ≫ g) rfl).inv.app K =
      (derivedLowerShriekUnboundedToDirectImage.{u, 0} Λ (f ≫ g) j).app K := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : UniversallyClosed jg.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact jg.toBase := instQuasiCompactOfUniversallyClosed jg.toBase
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  have hiso := NatTrans.congr_app (show (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom =
      (derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
          (CompactificationOf.compOver jg jX) Λ hΛ).hom ≫
        (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom ≫
        Functor.whiskerRight (derivedLowerShriekUnboundedCompactificationIsoUniv f
          (CompactificationOf.restrictBase jg jX) jf Λ hΛ).hom
          (derivedLowerShriekUnbounded.{u, 0} g jg Λ) from rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hiso
  have i₁ := NatTrans.congr_app
    (derivedLowerShriekUnboundedCompactificationIsoUniv_hom_comp_toDirectImage Λ (f ≫ g) j
      (CompactificationOf.compOver jg jX) hΛ) K
  have i₂ := NatTrans.congr_app
    (derivedLowerShriekUnboundedCompactificationIsoUniv_hom_comp_toDirectImage Λ f
      (CompactificationOf.restrictBase jg jX) jf hΛ) K
  simp only [NatTrans.comp_app] at i₁ i₂
  have hc := derivedLowerShriekUnboundedCompOverIso_hom_comp_toDirectImage Λ hΛ jg jX K
  rw [hiso, Category.assoc, Category.assoc, ← Functor.map_comp_assoc, i₂, hc, i₁]

end CompatibilityOne

end Stacks.EtaleCohomology

end
