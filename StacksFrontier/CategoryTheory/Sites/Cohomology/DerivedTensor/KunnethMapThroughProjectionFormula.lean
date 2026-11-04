module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMap

/-!
# The Künneth map through the projection formula and base change

For a square
```
W --q--> Y
|        |
p        g
↓        ↓
X --f--> S
```
with diagonal `c`, adjunctions `f^* ⊣ f_*`, `g^* ⊣ g_*`, `p^* ⊣ p_*`, `c^* ⊣ c_*`, tensor
products `⊗_S`, `⊗_X`, `⊗_W` and comparisons `μ_f`, `μ_p`, `μ_c` of the inverse images with them,
the Künneth map `f_*E ⊗_S g_*K ⟶ c_*(p^*E ⊗_W q^*K)` of
`Stacks.Cohomology.AbstractKunnethMap.kunnethMap` can be built in a second way, which is the one
the proof of [Stacks, Tag 0F1P] uses:

`f_*E ⊗ g_*K ⟶ f_*(E ⊗ f^*g_*K) ⟶ f_*p_*(p^*E ⊗ q^*K) ≅ c_*(p^*E ⊗ q^*K)`,

the projection formula map of `f`, then `f_*` of the canonical map of [Stacks, Tag 0F1J] and
[Stacks, Tag 0F1N], then the composition of direct images. This file proves that the two agree as
soon as the comparison for `c` is the composite of the comparisons for `f` and `p` along
`f^* ⋙ p^* ≅ c^*`, which is the composition law of [Stacks, Tag 07A4].

## Main results

* `Stacks.Cohomology.AbstractKunnethMap.kunnethMap_eq_projection_tensorBaseChangeMap` — the
  Künneth map is the projection formula map, followed by the direct image of the canonical map of
  Tags 0F1J and 0F1N and by the composition of direct images.

## References

* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

variable {DW DX DY DS : Type*} [Category* DW] [Category* DX] [Category* DY] [Category* DS]
  (TS : DS × DS ⥤ DS) (TX : DX × DX ⥤ DX) (TW : DW × DW ⥤ DW)
  {fPull : DS ⥤ DX} {fPush : DX ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DY} {gPush : DY ⥤ DS} (adjg : gPull ⊣ gPush)
  {pPull : DX ⥤ DW} {pPush : DW ⥤ DX} (adjp : pPull ⊣ pPush)
  {cPull : DS ⥤ DW} {cPush : DW ⥤ DS} (adjc : cPull ⊣ cPush)
  (qPull : DY ⥤ DW)
  (μf : TS ⋙ fPull ⟶ fPull.prod fPull ⋙ TX) (μp : TX ⋙ pPull ⟶ pPull.prod pPull ⋙ TW)
  (μc : TS ⋙ cPull ⟶ cPull.prod cPull ⋙ TW)
  (ep : fPull ⋙ pPull ≅ cPull) (eq : gPull ⋙ qPull ≅ cPull)
  (β : fPull ⋙ pPull ≅ gPull ⋙ qPull)

/-- The composite of the transposes along `p^* ⊣ p_*` and `f^* ⊣ f_*`, read across the
composition of direct images, is the transpose along `c^* ⊣ c_*`. -/
private theorem homEquiv_symm_comp_conjugate {A : DS} {Z : DW} (x : A ⟶ fPush.obj (pPush.obj Z)) :
    (adjc.homEquiv _ _).symm (x ≫ (conjugateIsoEquiv (adjf.comp adjp) adjc ep.symm).hom.app Z) =
      ep.inv.app A ≫ pPull.map (fPull.map x ≫ adjf.counit.app (pPush.obj Z)) ≫
        adjp.counit.app Z := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h := conjugateEquiv_counit (adjf.comp adjp) adjc ep.symm.hom Z
  change cPull.map ((conjugateIsoEquiv (adjf.comp adjp) adjc ep.symm).hom.app Z) ≫
    adjc.counit.app Z = _ at h
  rw [h, Adjunction.comp_counit_app]
  have hn := ep.inv.naturality x
  dsimp at hn ⊢
  rw [reassoc_of% hn, Functor.map_comp, Category.assoc]

/-- The transpose along `p^* ⊣ p_*` of the canonical map of Tags 0F1J and 0F1N. -/
private theorem map_tensorBaseChangeMap_comp_counit (E : DX) (K : DY) :
    pPull.map (tensorBaseChangeMap adjg adjp fPull qPull β TX TW μp E K) ≫
        adjp.counit.app (TW.obj (pPull.obj E, qPull.obj K)) =
      μp.app (E, fPull.obj (gPush.obj K)) ≫
        TW.map (𝟙 (pPull.obj E) ×ₘ (β.hom.app (gPush.obj K) ≫ qPull.map (adjg.counit.app K))) := by
  rw [tensorBaseChangeMap_eq_adjunctionCupProductOfMaps]
  have h := (adjp.homEquiv _ _).symm_apply_apply (μp.app (E, fPull.obj (gPush.obj K)) ≫
    TW.map (𝟙 (pPull.obj E) ×ₘ (β.hom.app (gPush.obj K) ≫ qPull.map (adjg.counit.app K))))
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- **The Künneth map through the projection formula and base change.** If the comparison `μ_c`
of `c^*` with the tensor products is the comparison `μ_f` followed by `μ_p`, read along
`f^* ⋙ p^* ≅ c^*` (the composition law of [Stacks, Tag 07A4], `hμ`), and `β` is the isomorphism
`f^* ⋙ p^* ≅ c^* ≅ g^* ⋙ q^*` (`hβ`), then the Künneth map `f_*E ⊗ g_*K ⟶ c_*(p^*E ⊗ q^*K)` is
the projection formula map `f_*E ⊗ g_*K ⟶ f_*(E ⊗ f^*g_*K)`, followed by `f_*` of the canonical
map `E ⊗ f^*g_*K ⟶ p_*(p^*E ⊗ q^*K)` of Tags 0F1J and 0F1N and by the composition
`f_*p_* ≅ c_*` of direct images. -/
theorem kunnethMap_eq_projection_tensorBaseChangeMap
    (hβ : ∀ M : DS, β.hom.app M = ep.hom.app M ≫ eq.inv.app M)
    (hμ : ∀ M N : DS, ep.hom.app (TS.obj (M, N)) ≫ μc.app (M, N) =
      pPull.map (μf.app (M, N)) ≫ μp.app (fPull.obj M, fPull.obj N) ≫
        TW.map (ep.hom.app M ×ₘ ep.hom.app N))
    (E : DX) (K : DY) :
    kunnethMap TS TW adjf adjg adjc pPull qPull μc ep eq E K =
      adjunctionTensorMap adjf TS TX μf E (gPush.obj K) ≫
        fPush.map (tensorBaseChangeMap adjg adjp fPull qPull β TX TW μp E K) ≫
          (conjugateIsoEquiv (adjf.comp adjp) adjc ep.symm).hom.app _ := by
  apply (adjc.homEquiv _ _).symm.injective
  conv_rhs => rw [← Category.assoc]
  have hx : fPull.map (adjunctionTensorMap adjf TS TX μf E (gPush.obj K) ≫
      fPush.map (tensorBaseChangeMap adjg adjp fPull qPull β TX TW μp E K)) ≫
        adjf.counit.app (pPush.obj (TW.obj (pPull.obj E, qPull.obj K))) =
      (μf.app (fPush.obj E, gPush.obj K) ≫
        TX.map (adjf.counit.app E ×ₘ 𝟙 (fPull.obj (gPush.obj K)))) ≫
        tensorBaseChangeMap adjg adjp fPull qPull β TX TW μp E K := by
    have hn := adjf.counit.naturality (tensorBaseChangeMap adjg adjp fPull qPull β TX TW μp E K)
    dsimp at hn
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
      map_adjunctionTensorMap_comp_counit]
  rw [homEquiv_symm_comp_conjugate, hx]
  simp only [Functor.map_comp, Category.assoc]
  rw [map_tensorBaseChangeMap_comp_counit]
  -- the inverse form of the composition law
  have hμ' : ep.inv.app (TS.obj (fPush.obj E, gPush.obj K)) ≫
      pPull.map (μf.app (fPush.obj E, gPush.obj K)) ≫
        μp.app (fPull.obj (fPush.obj E), fPull.obj (gPush.obj K)) =
      μc.app (fPush.obj E, gPush.obj K) ≫
        TW.map (ep.inv.app (fPush.obj E) ×ₘ ep.inv.app (gPush.obj K)) := by
    rw [← cancel_epi (ep.hom.app (TS.obj (fPush.obj E, gPush.obj K))), Iso.hom_inv_id_app_assoc,
      reassoc_of% (hμ (fPush.obj E) (gPush.obj K)), ← TW.map_comp]
    simp
  have hnat := μp.naturality (adjf.counit.app E ×ₘ 𝟙 (fPull.obj (gPush.obj K)))
  dsimp at hnat
  simp only [kunnethMap, KunnethMapOnRingedTopoi.adjunctionCupProductOfMaps,
    Equiv.symm_apply_apply, pullbackPushforwardCounit]
  rw [reassoc_of% hnat, reassoc_of% hμ', ← TW.map_comp, ← TW.map_comp]
  congr 2
  refine Prod.ext ?_ ?_
  · simp
  · simp [hβ]

end Stacks.Cohomology.AbstractKunnethMap

end
