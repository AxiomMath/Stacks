module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMapPushforward
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionMapAlongEquivalences

/-!
# The Künneth map through the projection formula of the second factor

For a square
```
W --q--> X
|        |
p        g
↓        ↓
Y --f--> S
```
with diagonal `c`, adjunctions `f^* ⊣ f_*`, `g^* ⊣ g_*`, `q^* ⊣ q_*`, `c^* ⊣ c_*`, tensor
products `⊗_S`, `⊗_X`, `⊗_W` and comparisons `μ_g`, `μ_q`, `μ_c` of the inverse images with them,
the Künneth map `f_*E ⊗_S g_*K ⟶ c_*(p^*E ⊗_W q^*K)` of
`Stacks.Cohomology.AbstractKunnethMap.kunnethMap` is the composite which the proof of
[Stacks, Tag 0F14] runs through:

`f_*E ⊗ g_*K ⟶ g_*(g^*f_*E ⊗ K) ⟶ g_*(q_*p^*E ⊗ K) ⟶ g_*q_*(p^*E ⊗ q^*K) ≅ c_*(p^*E ⊗ q^*K)`,

the projection map of `g`, the base change map `g^*f_* ⟶ q_*p^*` in the first factor, the
projection formula map of `q`, and the composition of direct images
(`kunnethMap_eq_projectionMap_comp`). It is the mirror image of
`Stacks.Cohomology.AbstractKunnethMap.kunnethMap_eq_projection_tensorBaseChangeMap`, which runs
through the first factor.

The second half of the file is the argument of the last paragraph of the proof of
[Stacks, Tag 0F1H] in this abstract setting. For an open immersion `j : U ⟶ X` and the two
squares of `Y ×_S X` and `Y ×_S U` over `S`, with `h : Y ×_S U ⟶ Y ×_S X`, the Künneth map of the
second square, read through the identifications transported from the first square along `h`
(`transportedPullbackIsoFirst`, `transportedPullbackIsoSecond`), is invertible as soon as the
projection maps, the base change map of the first square and the base change map of the square
`(h, q₂, q₁, j)` are; and then, by the naturality of the Künneth map along `j`
(`kunnethMap_comp_tensorBaseChangeMap`), the direct image to `S` of `p₁^*E ⊗ β`, `β` the base
change map `q₁^*j_* ⟶ h_*q₂^*`, is invertible
(`isIso_map_tensor_baseChangeMap_of_kunneth`).

## Main results

* `kunnethMap_eq_projectionMap_comp` — the Künneth map through the projection map of `g`.
* `isIso_kunnethMap_of_isIso_projectionMap` — its invertibility from that of the three factors.
* `baseChangeMap_transported_app` — the base change map of the transported data is the base
  change map of the first square followed by the base change map of `(h, q₂, q₁, j)`.
* `isIso_map_tensor_baseChangeMap_of_kunneth` — the Künneth step of [Stacks, Tag 0F1H].

## References

* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

open KunnethMapOnRingedTopoi

/-! ### The Künneth map through the second factor -/

section SecondFactor

variable {DW DX DY DS : Type*} [Category* DW] [Category* DX] [Category* DY] [Category* DS]
  (TS : DS × DS ⥤ DS) (TX : DX × DX ⥤ DX) (TW : DW × DW ⥤ DW)
  {fPull : DS ⥤ DY} {fPush : DY ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DX} {gPush : DX ⥤ DS} (adjg : gPull ⊣ gPush)
  {qPull : DX ⥤ DW} {qPush : DW ⥤ DX} (adjq : qPull ⊣ qPush)
  {cPull : DS ⥤ DW} {cPush : DW ⥤ DS} (adjc : cPull ⊣ cPush)
  (pPull : DY ⥤ DW)
  (μg : TS ⋙ gPull ⟶ gPull.prod gPull ⋙ TX) (μq : TX ⋙ qPull ⟶ qPull.prod qPull ⋙ TW)
  (μc : TS ⋙ cPull ⟶ cPull.prod cPull ⋙ TW)
  (ep : fPull ⋙ pPull ≅ cPull) (eq : gPull ⋙ qPull ≅ cPull)

/-- A bifunctor carries a pair of invertible morphisms to an invertible morphism. -/
private theorem isIso_map_prod {C D : Type*} [Category* C] [Category* D] (F : C × C ⥤ D)
    {X Y X' Y' : C} (u : X ⟶ Y) (v : X' ⟶ Y') [IsIso u] [IsIso v] : IsIso (F.map (u ×ₘ v)) := by
  have : IsIso (u ×ₘ v) := (isIso_prod_iff (C := C) (D := C)).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The transpose along `c^* ⊣ c_*` of a map followed by the composition `g_*q_* ≅ c_*` of direct
images is the transposes along `g^* ⊣ g_*` and `q^* ⊣ q_*`, read through `g^* ⋙ q^* ≅ c^*`. -/
theorem homEquiv_symm_comp_conjugateIsoEquiv_hom_app {A : DS} {Z : DW}
    (x : A ⟶ gPush.obj (qPush.obj Z)) :
    (adjc.homEquiv _ _).symm (x ≫ (conjugateIsoEquiv (adjg.comp adjq) adjc eq.symm).hom.app Z) =
      eq.inv.app A ≫ qPull.map (gPull.map x ≫ adjg.counit.app (qPush.obj Z)) ≫
        adjq.counit.app Z := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h := conjugateEquiv_counit (adjg.comp adjq) adjc eq.symm.hom Z
  change cPull.map ((conjugateIsoEquiv (adjg.comp adjq) adjc eq.symm).hom.app Z) ≫
    adjc.counit.app Z = _ at h
  rw [h, Adjunction.comp_counit_app]
  have hn := eq.inv.naturality x
  dsimp at hn ⊢
  rw [reassoc_of% hn, Functor.map_comp, Category.assoc]

/-- **The Künneth map through the projection formula of the second factor.** If the comparison
`μ_c` of `c^*` with the tensor products is `μ_g` followed by `μ_q`, read along
`g^* ⋙ q^* ≅ c^*` (the composition law of [Stacks, Tag 07A4]), then the Künneth map
`f_*E ⊗ g_*K ⟶ c_*(p^*E ⊗ q^*K)` is the projection map `f_*E ⊗ g_*K ⟶ g_*(g^*f_*E ⊗ K)` of `g`,
followed by `g_*` of the base change map `g^*f_*E ⟶ q_*p^*E` in the first factor and of the
projection formula map `q_*p^*E ⊗ K ⟶ q_*(p^*E ⊗ q^*K)` of `q`, and by the composition
`g_*q_* ≅ c_*` of direct images. -/
theorem kunnethMap_eq_projectionMap_comp
    (hμ : ∀ M N : DS, eq.hom.app (TS.obj (M, N)) ≫ μc.app (M, N) =
      qPull.map (μg.app (M, N)) ≫ μq.app (gPull.obj M, gPull.obj N) ≫
        TW.map (eq.hom.app M ×ₘ eq.hom.app N))
    (E : DY) (K : DX) :
    kunnethMap TS TW adjf adjg adjc pPull qPull μc ep eq E K =
      projectionMap TS TX adjg μg (fPush.obj E) K ≫
        gPush.map (TX.map ((baseChangeMap adjf adjq gPull pPull (eq ≪≫ ep.symm)).app E ×ₘ 𝟙 K) ≫
          adjunctionTensorMap adjq TX TW μq (pPull.obj E) K) ≫
        (conjugateIsoEquiv (adjg.comp adjq) adjc eq.symm).hom.app _ := by
  apply (adjc.homEquiv _ _).symm.injective
  rw [← Category.assoc, homEquiv_symm_comp_conjugateIsoEquiv_hom_app adjg adjq adjc eq]
  -- the transpose of the projection map of `g`
  have hπ : gPull.map (projectionMap TS TX adjg μg (fPush.obj E) K) ≫
      adjg.counit.app (TX.obj (gPull.obj (fPush.obj E), K)) =
      μg.app (fPush.obj E, gPush.obj K) ≫ TX.map (𝟙 _ ×ₘ adjg.counit.app K) := by
    have h := (adjg.homEquiv _ _).symm_apply_apply (μg.app (fPush.obj E, gPush.obj K) ≫
      TX.map (𝟙 _ ×ₘ adjg.counit.app K))
    rw [Adjunction.homEquiv_counit] at h
    exact h
  have hn := adjg.counit.naturality (TX.map ((baseChangeMap adjf adjq gPull pPull
    (eq ≪≫ ep.symm)).app E ×ₘ 𝟙 K) ≫ adjunctionTensorMap adjq TX TW μq (pPull.obj E) K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [Functor.map_comp gPull, Category.assoc, hn, reassoc_of% hπ,
    ← TX.map_comp_assoc, prod_comp,
    Category.id_comp, Category.comp_id]
  -- the composition law, in inverse form
  have hμ' : eq.inv.app (TS.obj (fPush.obj E, gPush.obj K)) ≫
      qPull.map (μg.app (fPush.obj E, gPush.obj K)) ≫
        μq.app (gPull.obj (fPush.obj E), gPull.obj (gPush.obj K)) =
      μc.app (fPush.obj E, gPush.obj K) ≫
        TW.map (eq.inv.app (fPush.obj E) ×ₘ eq.inv.app (gPush.obj K)) := by
    rw [← cancel_epi (eq.hom.app (TS.obj (fPush.obj E, gPush.obj K))), Iso.hom_inv_id_app_assoc,
      reassoc_of% (hμ (fPush.obj E) (gPush.obj K)), ← TW.map_comp]
    simp
  have hnat := μq.naturality ((baseChangeMap adjf adjq gPull pPull (eq ≪≫ ep.symm)).app E ×ₘ
    adjg.counit.app K)
  simp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at hnat
  have hbc := baseChangeMap_counit adjf adjq gPull pPull (eq ≪≫ ep.symm) E
  simp only [Functor.map_comp, Category.assoc, map_adjunctionTensorMap_comp_counit]
  rw [reassoc_of% hnat, ← Category.assoc (eq.inv.app _), ← Category.assoc (eq.inv.app _ ≫ _),
    Category.assoc (eq.inv.app _), hμ']
  simp only [kunnethMap, adjunctionCupProductOfMaps, Equiv.symm_apply_apply,
    pullbackPushforwardCounit, Category.assoc, ← TW.map_comp, prod_comp]
  congr 2
  refine Prod.ext ?_ ?_
  · simp only
    rw [hbc]
    simp
  · simp

/-- **The Künneth map is invertible once its three factors through the second factor are**: the
projection map of `g`, the base change map `g^*f_* ⟶ q_*p^*` at `E`, and the projection formula
map of `q`. -/
theorem isIso_kunnethMap_of_isIso_projectionMap
    (hμ : ∀ M N : DS, eq.hom.app (TS.obj (M, N)) ≫ μc.app (M, N) =
      qPull.map (μg.app (M, N)) ≫ μq.app (gPull.obj M, gPull.obj N) ≫
        TW.map (eq.hom.app M ×ₘ eq.hom.app N))
    (E : DY) (K : DX) (h₁ : IsIso (projectionMap TS TX adjg μg (fPush.obj E) K))
    (h₂ : IsIso ((baseChangeMap adjf adjq gPull pPull (eq ≪≫ ep.symm)).app E))
    (h₃ : IsIso (adjunctionTensorMap adjq TX TW μq (pPull.obj E) K)) :
    IsIso (kunnethMap TS TW adjf adjg adjc pPull qPull μc ep eq E K) := by
  rw [kunnethMap_eq_projectionMap_comp TS TX TW adjf adjg adjq adjc pPull μg μq μc ep eq hμ]
  have := isIso_map_prod TX ((baseChangeMap adjf adjq gPull pPull (eq ≪≫ ep.symm)).app E) (𝟙 K)
  infer_instance

end SecondFactor

/-! ### The data of the second square transported from the first along `h` -/

section Transport

variable {DS DY DX DU DW₁ DW₂ : Type*} [Category* DS] [Category* DY] [Category* DX] [Category* DU]
  [Category* DW₁] [Category* DW₂]
  (TS : DS × DS ⥤ DS) (TX : DX × DX ⥤ DX) (TU : DU × DU ⥤ DU) (TW₁ : DW₁ × DW₁ ⥤ DW₁)
  (TW₂ : DW₂ × DW₂ ⥤ DW₂)
  {fPull : DS ⥤ DY} {fPush : DY ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DX} {gPush : DX ⥤ DS} (adjg : gPull ⊣ gPush)
  {g'Pull : DS ⥤ DU} {g'Push : DU ⥤ DS} (adjg' : g'Pull ⊣ g'Push)
  {jPull : DX ⥤ DU} {jPush : DU ⥤ DX} (adjj : jPull ⊣ jPush)
  {c₁Pull : DS ⥤ DW₁} {c₁Push : DW₁ ⥤ DS} (adjc₁ : c₁Pull ⊣ c₁Push)
  {hPull : DW₁ ⥤ DW₂} {hPush : DW₂ ⥤ DW₁} (adjh : hPull ⊣ hPush)
  {q₁Pull : DX ⥤ DW₁} {q₁Push : DW₁ ⥤ DX} (adjq₁ : q₁Pull ⊣ q₁Push)
  {q₂Pull : DU ⥤ DW₂} {q₂Push : DW₂ ⥤ DU} (adjq₂ : q₂Pull ⊣ q₂Push)
  (p₁Pull : DY ⥤ DW₁) (p₂Pull : DY ⥤ DW₂)
  (μ₁ : TS ⋙ c₁Pull ⟶ c₁Pull.prod c₁Pull ⋙ TW₁) (μh : TW₁ ⋙ hPull ⟶ hPull.prod hPull ⋙ TW₂)
  (ep₁ : fPull ⋙ p₁Pull ≅ c₁Pull) (eq₁ : gPull ⋙ q₁Pull ≅ c₁Pull)
  (α : p₁Pull ⋙ hPull ≅ p₂Pull) (β : q₁Pull ⋙ hPull ≅ jPull ⋙ q₂Pull)
  (δ : gPull ⋙ jPull ≅ g'Pull)

/-- The identification `f^* ⋙ p₂^* ≅ c₁^* ⋙ h^*` transported from `f^* ⋙ p₁^* ≅ c₁^*` along
`α : p₁^* ⋙ h^* ≅ p₂^*`. -/
def transportedPullbackIsoFirst : fPull ⋙ p₂Pull ≅ c₁Pull ⋙ hPull :=
  Functor.isoWhiskerLeft fPull α.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ep₁ hPull

/-- The identification `g'^* ⋙ q₂^* ≅ c₁^* ⋙ h^*` transported from `g^* ⋙ q₁^* ≅ c₁^*` along
`δ : g^* ⋙ j^* ≅ g'^*` and `β : q₁^* ⋙ h^* ≅ j^* ⋙ q₂^*`. -/
def transportedPullbackIsoSecond : g'Pull ⋙ q₂Pull ≅ c₁Pull ⋙ hPull :=
  Functor.isoWhiskerRight δ.symm q₂Pull ≪≫ Functor.associator gPull jPull q₂Pull ≪≫
    Functor.isoWhiskerLeft gPull β.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eq₁ hPull

/-- The component of `transportedPullbackIsoFirst` at `M` is `α⁻¹` at `f^* M`, then `h^*` applied
to `ep₁` at `M`. -/
@[simp]
theorem transportedPullbackIsoFirst_hom_app (M : DS) :
    (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α).hom.app M =
      α.inv.app (fPull.obj M) ≫ hPull.map (ep₁.hom.app M) := by
  simp [transportedPullbackIsoFirst]

/-- The component of the inverse of `transportedPullbackIsoFirst` at `M` is `h^*` applied to
`ep₁⁻¹` at `M`, then `α` at `f^* M`. -/
@[simp]
theorem transportedPullbackIsoFirst_inv_app (M : DS) :
    (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α).inv.app M =
      hPull.map (ep₁.inv.app M) ≫ α.hom.app (fPull.obj M) := by
  simp [transportedPullbackIsoFirst]

/-- The component of `transportedPullbackIsoSecond` at `M` is `q₂^*` applied to `δ⁻¹` at `M`,
then `β⁻¹` at `g^* M`, then `h^*` applied to `eq₁` at `M`. -/
@[simp]
theorem transportedPullbackIsoSecond_hom_app (M : DS) :
    (transportedPullbackIsoSecond eq₁ β δ).hom.app M =
      q₂Pull.map (δ.inv.app M) ≫ β.inv.app (gPull.obj M) ≫ hPull.map (eq₁.hom.app M) := by
  simp [transportedPullbackIsoSecond]

/-- The component of the inverse of `transportedPullbackIsoSecond` at `M` is `h^*` applied to
`eq₁⁻¹` at `M`, then `β` at `g^* M`, then `q₂^*` applied to `δ` at `M`. -/
@[simp]
theorem transportedPullbackIsoSecond_inv_app (M : DS) :
    (transportedPullbackIsoSecond eq₁ β δ).inv.app M =
      hPull.map (eq₁.inv.app M) ≫ β.hom.app (gPull.obj M) ≫ q₂Pull.map (δ.hom.app M) := by
  simp [transportedPullbackIsoSecond]

/-- **The base change map of the transported data is a pasting.** The base change map
`g'^*f_* ⟶ q₂_*p₂^*` of the identification `g'^* ⋙ q₂^* ≅ f^* ⋙ p₂^*` transported from the first
square is `δ`, then `j^*` of the base change map `g^*f_* ⟶ q₁_*p₁^*` of the first square, then
the base change map `j^*q₁_* ⟶ q₂_*h^*` of `β`, then `α`. -/
theorem baseChangeMap_transported_app (E : DY) :
    (baseChangeMap adjf adjq₂ g'Pull p₂Pull
        (transportedPullbackIsoSecond eq₁ β δ ≪≫
          (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α).symm)).app E =
      δ.inv.app (fPush.obj E) ≫
        jPull.map ((baseChangeMap adjf adjq₁ gPull p₁Pull (eq₁ ≪≫ ep₁.symm)).app E) ≫
        (baseChangeMap adjq₁ adjq₂ jPull hPull β.symm).app (p₁Pull.obj E) ≫
        q₂Push.map (α.hom.app E) := by
  apply (adjq₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [baseChangeMap_counit]
  simp only [Functor.map_comp, Category.assoc]
  have nα := adjq₂.counit.naturality (α.hom.app E)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at nα
  rw [nα, reassoc_of% (baseChangeMap_counit adjq₁ adjq₂ jPull hPull β.symm (p₁Pull.obj E))]
  have nβ := β.inv.naturality ((baseChangeMap adjf adjq₁ gPull p₁Pull (eq₁ ≪≫ ep₁.symm)).app E)
  simp only [Functor.comp_map] at nβ
  rw [Iso.symm_hom, reassoc_of% nβ, ← hPull.map_comp_assoc,
    baseChangeMap_counit adjf adjq₁ gPull p₁Pull (eq₁ ≪≫ ep₁.symm) E]
  have nα' := α.hom.naturality (adjf.counit.app E)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nα'
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, transportedPullbackIsoSecond_hom_app,
    transportedPullbackIsoFirst_inv_app, Functor.map_comp, Category.assoc]
  rw [nα']

variable (μg : TS ⋙ gPull ⟶ gPull.prod gPull ⋙ TX) (μg' : TS ⋙ g'Pull ⟶ g'Pull.prod g'Pull ⋙ TU)
  (μj : TX ⋙ jPull ⟶ jPull.prod jPull ⋙ TU) (μq₁ : TX ⋙ q₁Pull ⟶ q₁Pull.prod q₁Pull ⋙ TW₁)
  (μq₂ : TU ⋙ q₂Pull ⟶ q₂Pull.prod q₂Pull ⋙ TW₂)

/-- **The composition law of [Stacks, Tag 07A4] for the transported identification**
`g'^* ⋙ q₂^* ≅ c₁^* ⋙ h^*`, from the composition laws of its three pieces: `eq₁` (`hμ₁`), the
identification `β` around the square `(h, q₂, q₁, j)` (`hμβ`) and `δ : g^* ⋙ j^* ≅ g'^*`
(`hμδ`). -/
theorem tensorCompat_transportedPullbackIsoSecond
    (hμ₁ : TensorCompat (compTensor μg μq₁) μ₁ eq₁.hom)
    (hμβ : TensorCompat (compTensor μq₁ μh) (compTensor μj μq₂) β.hom)
    (hμδ : TensorCompat (compTensor μg μj) μg' δ.hom) :
    TensorCompat (compTensor μg' μq₂) (compTensor μ₁ μh)
      (transportedPullbackIsoSecond eq₁ β δ).hom := by
  intro M N
  have hβ' := (TensorCompat.symm hμβ) (gPull.obj M) (gPull.obj N)
  have hδ' := (TensorCompat.symm hμδ) M N
  have h₁ := hμ₁ M N
  simp only [compTensor_app, Category.assoc] at hβ' hδ' h₁
  simp only [transportedPullbackIsoSecond_hom_app, compTensor_app, Category.assoc]
  rw [← hPull.map_comp_assoc (eq₁.hom.app _), h₁]
  have nh := μh.naturality (eq₁.hom.app M ×ₘ eq₁.hom.app N)
  have nβ := β.inv.naturality (μg.app (M, N))
  have nq := μq₂.naturality (δ.inv.app M ×ₘ δ.inv.app N)
  simp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at nh nβ nq
  simp only [Functor.map_comp, Category.assoc]
  rw [nh, ← reassoc_of% nβ, reassoc_of% hβ', ← q₂Pull.map_comp_assoc, ← q₂Pull.map_comp_assoc,
    Category.assoc, hδ', q₂Pull.map_comp_assoc, reassoc_of% nq]
  simp only [← TW₂.map_comp, prod_comp]

end Transport

/-! ### The Künneth step of Tag 0F1H -/

section OpenImmersion

variable {DS DY DX DU DW₁ DW₂ : Type*} [Category* DS] [Category* DY] [Category* DX] [Category* DU]
  [Category* DW₁] [Category* DW₂]
  (TS : DS × DS ⥤ DS) (TX : DX × DX ⥤ DX) (TU : DU × DU ⥤ DU) (TW₁ : DW₁ × DW₁ ⥤ DW₁)
  (TW₂ : DW₂ × DW₂ ⥤ DW₂)
  {fPull : DS ⥤ DY} {fPush : DY ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DX} {gPush : DX ⥤ DS} (adjg : gPull ⊣ gPush)
  {g'Pull : DS ⥤ DU} {g'Push : DU ⥤ DS} (adjg' : g'Pull ⊣ g'Push)
  {jPull : DX ⥤ DU} {jPush : DU ⥤ DX} (adjj : jPull ⊣ jPush)
  {c₁Pull : DS ⥤ DW₁} {c₁Push : DW₁ ⥤ DS} (adjc₁ : c₁Pull ⊣ c₁Push)
  {hPull : DW₁ ⥤ DW₂} {hPush : DW₂ ⥤ DW₁} (adjh : hPull ⊣ hPush)
  {q₁Pull : DX ⥤ DW₁} {q₁Push : DW₁ ⥤ DX} (adjq₁ : q₁Pull ⊣ q₁Push)
  {q₂Pull : DU ⥤ DW₂} {q₂Push : DW₂ ⥤ DU} (adjq₂ : q₂Pull ⊣ q₂Push)
  (p₁Pull : DY ⥤ DW₁) (p₂Pull : DY ⥤ DW₂)
  (μ₁ : TS ⋙ c₁Pull ⟶ c₁Pull.prod c₁Pull ⋙ TW₁) (μh : TW₁ ⋙ hPull ⟶ hPull.prod hPull ⋙ TW₂)
  (μg : TS ⋙ gPull ⟶ gPull.prod gPull ⋙ TX) (μg' : TS ⋙ g'Pull ⟶ g'Pull.prod g'Pull ⋙ TU)
  (μj : TX ⋙ jPull ⟶ jPull.prod jPull ⋙ TU) (μq₁ : TX ⋙ q₁Pull ⟶ q₁Pull.prod q₁Pull ⋙ TW₁)
  (μq₂ : TU ⋙ q₂Pull ⟶ q₂Pull.prod q₂Pull ⋙ TW₂)
  (ep₁ : fPull ⋙ p₁Pull ≅ c₁Pull) (eq₁ : gPull ⋙ q₁Pull ≅ c₁Pull)
  (α : p₁Pull ⋙ hPull ≅ p₂Pull) (β : q₁Pull ⋙ hPull ≅ jPull ⋙ q₂Pull)
  (δ : gPull ⋙ jPull ≅ g'Pull)

include adjc₁ α in
/-- **The Künneth step of [Stacks, Tag 0F1H].** In the situation of
`kunnethMap_comp_tensorBaseChangeMap` (`f : Y ⟶ S`, `g : X ⟶ S`, `j : U ⟶ X`, `g' = j ≫ g`,
the squares of `W₁ = Y ×_S X` and `W₂ = Y ×_S U`, and `h : W₂ ⟶ W₁`), let the comparisons with the
tensor products satisfy the composition laws of [Stacks, Tag 07A4] around `eq₁`, `β` and `δ`.
Suppose that at `E ∈ D(Y)` and `K ∈ D(U)`

* the projection maps of `g` at `(f_*E, j_*K)` and of `g'` at `(f_*E, K)` are invertible (the
  projection formula to a separably closed point);
* the base change map `g^*f_*E ⟶ q₁_*p₁^*E` of the first square is invertible (proper base change
  for `f`), and so is the base change map `j^*q₁_* ⟶ q₂_*h^*` of `β^{-1}` at `p₁^*E` (both are
  given as transformations `bc`, `bcj` equal to the base change maps, so that a model may supply
  its own spelling of them);
* the projection formula maps of `q₁` at `(p₁^*E, j_*K)` and of `q₂` at `(p₂^*E, K)` are
  invertible ([Stacks, Tag 0F0G] for the base changes of the proper `f`);
* the projection map of `h` at `(p₁^*E, q₂^*K)` is invertible (for instance `p₁^*E` is the unit).

Then the direct image to `S` of `p₁^*E ⊗ β_K`, `β_K : q₁^*j_*K ⟶ h_*q₂^*K` the base change map of
`β`, is invertible: both Künneth maps are, and they differ by it. -/
theorem isIso_map_tensor_baseChangeMap_of_kunneth
    (hμ₁ : TensorCompat (compTensor μg μq₁) μ₁ eq₁.hom)
    (hμβ : TensorCompat (compTensor μq₁ μh) (compTensor μj μq₂) β.hom)
    (hμδ : TensorCompat (compTensor μg μj) μg' δ.hom)
    (E : DY) (K : DU)
    (hπg : IsIso (projectionMap TS TX adjg μg (fPush.obj E) (jPush.obj K)))
    (hπg' : IsIso (projectionMap TS TU adjg' μg' (fPush.obj E) K))
    (bc : fPush ⋙ gPull ⟶ p₁Pull ⋙ q₁Push)
    (hbceq : bc = baseChangeMap adjf adjq₁ gPull p₁Pull (eq₁ ≪≫ ep₁.symm))
    (hbc : IsIso (bc.app E)) (bcj : q₁Push ⋙ jPull ⟶ hPull ⋙ q₂Push)
    (hbcjeq : bcj = baseChangeMap adjq₁ adjq₂ jPull hPull β.symm)
    (hbcj : IsIso (bcj.app (p₁Pull.obj E)))
    (hq₁ : IsIso (adjunctionTensorMap adjq₁ TX TW₁ μq₁ (p₁Pull.obj E) (jPush.obj K)))
    (hq₂ : IsIso (adjunctionTensorMap adjq₂ TU TW₂ μq₂ (p₂Pull.obj E) K))
    (hh : IsIso (projectionMap TW₁ TW₂ adjh μh (p₁Pull.obj E) (q₂Pull.obj K))) :
    IsIso (c₁Push.map (TW₁.map (𝟙 (p₁Pull.obj E) ×ₘ
      (baseChangeMap adjj adjh q₁Pull q₂Pull β).app K))) := by
  subst hbceq hbcjeq
  -- the Künneth map of the first square is invertible
  have hκ₁ := isIso_kunnethMap_of_isIso_projectionMap TS TX TW₁ adjf adjg adjq₁ adjc₁ p₁Pull μg μq₁
    μ₁ ep₁ eq₁ (fun M N => by simpa using hμ₁ M N) E (jPush.obj K) hπg hbc hq₁
  -- the Künneth map of the second square, with the transported data, is invertible
  have hbc₂ : IsIso ((baseChangeMap adjf adjq₂ g'Pull p₂Pull
      (transportedPullbackIsoSecond eq₁ β δ ≪≫
        (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α).symm)).app E) := by
    rw [baseChangeMap_transported_app (adjq₁ := adjq₁)]
    infer_instance
  have hκ₂ := isIso_kunnethMap_of_isIso_projectionMap TS TU TW₂ adjf adjg' adjq₂ (adjc₁.comp adjh)
    p₂Pull μg' μq₂ (compTensor μ₁ μh)
    (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α) (transportedPullbackIsoSecond eq₁ β δ)
    (fun M N => by
      simpa using tensorCompat_transportedPullbackIsoSecond TS TX TU TW₁ TW₂ μ₁ μh eq₁ β δ
        μg μg' μj μq₁ μq₂ hμ₁ hμβ hμδ M N) E K hπg' hbc₂ hq₂
  -- the naturality of the Künneth map along `j`
  have hnat := kunnethMap_comp_tensorBaseChangeMap TS TW₁ TW₂ adjf adjg adjg' adjj adjc₁
    (adjc₁.comp adjh) adjh p₁Pull q₁Pull p₂Pull q₂Pull μ₁
    (compTensor μ₁ μh) μh ep₁ eq₁
    (transportedPullbackIsoFirst p₁Pull p₂Pull ep₁ α) (transportedPullbackIsoSecond eq₁ β δ) α β
    (Iso.refl _) δ (fun M N => by simp)
    (fun M => by simp)
    (fun M => by simp [← Functor.map_comp]) E K
  have hX : IsIso (c₁Push.map (tensorBaseChangeMap adjj adjh q₁Pull q₂Pull β TW₁ TW₂ μh
      (p₁Pull.obj E) K ≫ hPush.map (TW₂.map (α.hom.app E ×ₘ 𝟙 _)))) := by
    have h₀ : IsIso (kunnethMap TS TW₁ adjf adjg adjc₁ p₁Pull q₁Pull μ₁ ep₁ eq₁ E (jPush.obj K) ≫
        c₁Push.map (tensorBaseChangeMap adjj adjh q₁Pull q₂Pull β TW₁ TW₂ μh (p₁Pull.obj E) K ≫
          hPush.map (TW₂.map (α.hom.app E ×ₘ 𝟙 _))) ≫
        (conjugatePushforwardIso adjc₁ (adjc₁.comp adjh) adjh (Iso.refl _)).hom.app _) := by
      rw [hnat]
      have := isIso_map_prod TS (𝟙 (fPush.obj E))
        ((conjugatePushforwardIso adjg adjg' adjj δ).hom.app K)
      infer_instance
    have h₁ : IsIso (c₁Push.map (tensorBaseChangeMap adjj adjh q₁Pull q₂Pull β TW₁ TW₂ μh
        (p₁Pull.obj E) K ≫ hPush.map (TW₂.map (α.hom.app E ×ₘ 𝟙 _))) ≫
        (conjugatePushforwardIso adjc₁ (adjc₁.comp adjh) adjh (Iso.refl _)).hom.app _) :=
      IsIso.of_isIso_comp_left
        (kunnethMap TS TW₁ adjf adjg adjc₁ p₁Pull q₁Pull μ₁ ep₁ eq₁ E (jPush.obj K)) _
    exact IsIso.of_isIso_comp_right _
      ((conjugatePushforwardIso adjc₁ (adjc₁.comp adjh) adjh (Iso.refl _)).hom.app _)
  have hα := isIso_map_prod TW₂ (α.hom.app E) (𝟙 (q₂Pull.obj K))
  simp only [tensorBaseChangeMap, Category.assoc, Functor.map_comp] at hX
  exact IsIso.of_isIso_comp_right _ (c₁Push.map (projectionMap TW₁ TW₂ adjh μh _ _) ≫
    c₁Push.map (hPush.map (TW₂.map (α.hom.app E ×ₘ 𝟙 _))))

end OpenImmersion

end Stacks.Cohomology.AbstractKunnethMap

end
