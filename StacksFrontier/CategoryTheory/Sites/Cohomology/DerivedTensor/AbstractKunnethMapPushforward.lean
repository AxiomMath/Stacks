module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMap

/-!
# Naturality of the Künneth map along a direct image in the second factor

Consider a proper factor `f : Y ⟶ S`, a morphism `g : X ⟶ S`, a morphism `j : U ⟶ X` with
`g' = j ≫ g`, and the two squares
```
W₁ --q₁--> X        W₂ --q₂--> U
|p₁        |g       |p₂        |g'
Y  --f---> S        Y  --f---> S
```
together with `h : W₂ ⟶ W₁`, `h ≫ p₁ = p₂` and `h ≫ q₁ = q₂ ≫ j`. In the abstract setting of
`Stacks.Cohomology.AbstractKunnethMap` (inverse images, their right adjoints, tensor products and
comparisons of the inverse images with them) this file proves that **the Künneth map of the second
square at `(E, K)` is the Künneth map of the first square at `(E, j_*K)`**, followed by the direct
image of the canonical map `p₁^*E ⊗ q₁^*j_*K ⟶ h_*(p₂^*E ⊗ q₂^*K)` of
`Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap`, through the identifications
`g_*j_* ≅ g'_*` and `c₁_*h_* ≅ c₂_*` of the composite direct images
(`kunnethMap_comp_tensorBaseChangeMap`).

The hypotheses are the compatibilities of the comparisons with composition: the comparison `μ₂`
for `c₂` is the composite of `μ₁` and of `μ_h` along `c₁^* ⋙ h^* ≅ c₂^*` (the composition law of
[Stacks, Tag 07A4]), and the identifications of composite inverse images around the squares are
compatible (the cocycle condition of [Stacks, Tag 0D6D]).

## References

* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

open KunnethMapOnRingedTopoi

variable {DS DY DX DU DW₁ DW₂ : Type*} [Category* DS] [Category* DY] [Category* DX] [Category* DU]
  [Category* DW₁] [Category* DW₂]
  (TS : DS × DS ⥤ DS) (TW₁ : DW₁ × DW₁ ⥤ DW₁) (TW₂ : DW₂ × DW₂ ⥤ DW₂)
  {fPull : DS ⥤ DY} {fPush : DY ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DX} {gPush : DX ⥤ DS} (adjg : gPull ⊣ gPush)
  {g'Pull : DS ⥤ DU} {g'Push : DU ⥤ DS} (adjg' : g'Pull ⊣ g'Push)
  {jPull : DX ⥤ DU} {jPush : DU ⥤ DX} (adjj : jPull ⊣ jPush)
  {c₁Pull : DS ⥤ DW₁} {c₁Push : DW₁ ⥤ DS} (adjc₁ : c₁Pull ⊣ c₁Push)
  {c₂Pull : DS ⥤ DW₂} {c₂Push : DW₂ ⥤ DS} (adjc₂ : c₂Pull ⊣ c₂Push)
  {hPull : DW₁ ⥤ DW₂} {hPush : DW₂ ⥤ DW₁} (adjh : hPull ⊣ hPush)
  (p₁Pull : DY ⥤ DW₁) (q₁Pull : DX ⥤ DW₁) (p₂Pull : DY ⥤ DW₂) (q₂Pull : DU ⥤ DW₂)
  (μ₁ : TS ⋙ c₁Pull ⟶ c₁Pull.prod c₁Pull ⋙ TW₁) (μ₂ : TS ⋙ c₂Pull ⟶ c₂Pull.prod c₂Pull ⋙ TW₂)
  (μh : TW₁ ⋙ hPull ⟶ hPull.prod hPull ⋙ TW₂)
  (ep₁ : fPull ⋙ p₁Pull ≅ c₁Pull) (eq₁ : gPull ⋙ q₁Pull ≅ c₁Pull)
  (ep₂ : fPull ⋙ p₂Pull ≅ c₂Pull) (eq₂ : g'Pull ⋙ q₂Pull ≅ c₂Pull)
  (α : p₁Pull ⋙ hPull ≅ p₂Pull) (β : q₁Pull ⋙ hPull ≅ jPull ⋙ q₂Pull)
  (γ : c₁Pull ⋙ hPull ≅ c₂Pull) (δ : gPull ⋙ jPull ≅ g'Pull)

/-- The identification `g_* ∘ j_* ≅ g'_*` of the composite direct images, conjugate to
`δ : g^* ⋙ j^* ≅ g'^*`. -/
abbrev conjugatePushforwardIso : jPush ⋙ gPush ≅ g'Push :=
  conjugateIsoEquiv (adjg.comp adjj) adjg' δ.symm

/-- **Naturality of the Künneth map along a direct image in the second factor.** The Künneth map
of the first square at `(E, j_*K)`, followed by the direct image of the canonical map
`p₁^*E ⊗ q₁^*j_*K ⟶ h_*(p₂^*E ⊗ q₂^*K)` (the base change map of the square `(h, q₂, q₁, j)` in the
second factor, then the projection map of `h`, then `α`) and by `c₁_*h_* ≅ c₂_*`, is
`g_*j_* ≅ g'_*` in the second factor followed by the Künneth map of the second square at `(E, K)`.
The hypotheses are the composition law of the comparisons with `⊗` (`hμ`) and the compatibility
of the identifications of composite inverse images around the two squares (`hp`, `hq`). -/
theorem kunnethMap_comp_tensorBaseChangeMap
    (hμ : ∀ M N : DS, γ.inv.app (TS.obj (M, N)) ≫ hPull.map (μ₁.app (M, N)) ≫
      μh.app (c₁Pull.obj M, c₁Pull.obj N) =
        μ₂.app (M, N) ≫ TW₂.map (γ.inv.app M ×ₘ γ.inv.app N))
    (hp : ∀ M : DS, γ.inv.app M ≫ hPull.map (ep₁.inv.app M) ≫ α.hom.app (fPull.obj M) =
      ep₂.inv.app M)
    (hq : ∀ M : DS, γ.inv.app M ≫ hPull.map (eq₁.inv.app M) ≫ β.hom.app (gPull.obj M) =
      eq₂.inv.app M ≫ q₂Pull.map (δ.inv.app M))
    (E : DY) (K : DU) :
    kunnethMap TS TW₁ adjf adjg adjc₁ p₁Pull q₁Pull μ₁ ep₁ eq₁ E (jPush.obj K) ≫
        c₁Push.map (tensorBaseChangeMap adjj adjh q₁Pull q₂Pull β TW₁ TW₂ μh (p₁Pull.obj E) K ≫
          hPush.map (TW₂.map (α.hom.app E ×ₘ 𝟙 _))) ≫
        (conjugatePushforwardIso adjc₁ adjc₂ adjh γ).hom.app _ =
      TS.map (𝟙 _ ×ₘ (conjugatePushforwardIso adjg adjg' adjj δ).hom.app K) ≫
        kunnethMap TS TW₂ adjf adjg' adjc₂ p₂Pull q₂Pull μ₂ ep₂ eq₂ E K := by
  have hL : ∀ {A : DS} {Z : DW₂} (x : A ⟶ c₁Push.obj (hPush.obj Z)),
      (adjc₂.homEquiv _ _).symm (x ≫ (conjugatePushforwardIso adjc₁ adjc₂ adjh γ).hom.app Z) =
        γ.inv.app A ≫ hPull.map ((adjc₁.homEquiv _ _).symm x) ≫ adjh.counit.app Z := by
    intro A Z x
    have h1 := conjugateEquiv_counit (adjc₁.comp adjh) adjc₂ γ.symm.hom Z
    have h2 := γ.inv.naturality x
    simp only [Functor.comp_map, Iso.symm_hom] at h1 h2
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, conjugatePushforwardIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom, h1]
    simp only [Functor.comp_obj] at h2 ⊢
    rw [reassoc_of% h2, Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  have h₁ : γ.inv.app (fPush.obj E) ≫ hPull.map (ep₁.inv.app (fPush.obj E) ≫
      p₁Pull.map (adjf.counit.app E)) ≫ α.hom.app E =
      ep₂.inv.app (fPush.obj E) ≫ p₂Pull.map (adjf.counit.app E) := by
    have n := α.hom.naturality (adjf.counit.app E)
    simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n
    rw [Functor.map_comp, Category.assoc, n, ← reassoc_of% (hp (fPush.obj E))]
  have h₂ : γ.inv.app (gPush.obj (jPush.obj K)) ≫ hPull.map (eq₁.inv.app (gPush.obj (jPush.obj K)) ≫
      q₁Pull.map (adjg.counit.app (jPush.obj K))) ≫ β.hom.app (jPush.obj K) ≫
        q₂Pull.map (adjj.counit.app K) =
      c₂Pull.map ((conjugatePushforwardIso adjg adjg' adjj δ).hom.app K) ≫
        eq₂.inv.app (g'Push.obj K) ≫ q₂Pull.map (adjg'.counit.app K) := by
    have n₁ := β.hom.naturality (adjg.counit.app (jPush.obj K))
    have n₂ := eq₂.inv.naturality ((conjugatePushforwardIso adjg adjg' adjj δ).hom.app K)
    have hc := conjugateEquiv_counit (adjg.comp adjj) adjg' δ.symm.hom K
    simp only [Functor.comp_map, Iso.symm_hom, Functor.comp_obj, Functor.id_obj] at n₁ n₂ hc
    rw [Functor.map_comp, Category.assoc, reassoc_of% n₁, reassoc_of% (hq _), reassoc_of% n₂,
      ← q₂Pull.map_comp, ← q₂Pull.map_comp, ← q₂Pull.map_comp]
    congr 2
    simp only [conjugatePushforwardIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom, hc,
      Adjunction.comp_counit_app]
  apply (adjc₂.homEquiv _ _).symm.injective
  rw [← Category.assoc, hL, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [kunnethMap, adjunctionCupProductOfMaps, Equiv.symm_apply_apply,
    pullbackPushforwardCounit]
  rw [tensorBaseChangeMap_eq_adjunctionCupProductOfMaps]
  have key : ∀ {A B : DW₁} {Z : DW₂} (u : A ⟶ B) (y : B ⟶ hPush.obj Z),
      hPull.map (u ≫ y) ≫ adjh.counit.app Z = hPull.map u ≫ (adjh.homEquiv _ _).symm y := by
    intro A B Z u y
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [key, Adjunction.homEquiv_naturality_right_symm]
  simp only [adjunctionCupProductOfMaps, Equiv.symm_apply_apply]
  have nμh := μh.naturality ((ep₁.inv.app (fPush.obj E) ≫ p₁Pull.map (adjf.counit.app E)) ×ₘ
    (eq₁.inv.app (gPush.obj (jPush.obj K)) ≫ q₁Pull.map (adjg.counit.app (jPush.obj K))))
  have nμ₂ := μ₂.naturality (𝟙 (fPush.obj E) ×ₘ
    (conjugatePushforwardIso adjg adjg' adjj δ).hom.app K)
  simp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at nμh nμ₂
  rw [reassoc_of% nμ₂, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% nμh, ← Category.assoc (γ.inv.app _), ← Category.assoc (γ.inv.app _ ≫ _),
    Category.assoc (γ.inv.app _), hμ]
  simp only [← TW₂.map_comp, prod_comp, Category.assoc, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [h₁, ← h₂]
  exact congrArg (fun t ↦ _ ≫ TW₂.map (_ ×ₘ t)) (by simp)

end Stacks.Cohomology.AbstractKunnethMap
