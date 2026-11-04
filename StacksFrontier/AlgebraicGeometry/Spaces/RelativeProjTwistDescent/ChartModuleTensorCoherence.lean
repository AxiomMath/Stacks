module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorNaturality
public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackTensorTransportCoherence

/-!
# The tensor identification of Stacks 03DX (2) on a representable is monoidal

For quasi-coherent modules `M`, `N` on the scheme underlying an object `U` of the big fppf site,
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` identifies the module attached
to `M ⊗ N` on the small étale site of `yoneda.obj U` with the tensor product of the attached
modules, and `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` identifies the module
attached to `𝒪_U` with `𝒪_{yoneda U}`. These identifications are compatible with the associators
and the braidings: on the scheme those of the tensor product sheaf of Tag 01CA, on `yoneda.obj U`
those of the monoidal structure `AlgebraicGeometry.Space.modulesMonoidalCategory` of `𝒪`-modules.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentAssociator` and
  `AlgebraicGeometry.Space.quasicoherentBraiding`: the associator and the braiding of the tensor
  product sheaf of Tag 01CA, between quasi-coherent tensor products
  `AlgebraicGeometry.Space.quasicoherentTensorObj` on the scheme underlying `U`.

## Main results

* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_associativity`: the tensor
  identification of Stacks 03DX (2) is compatible with the associators.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_braiding`: it is compatible
  with the braidings.
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_associativity`,
  `pullbackTensorIsoTransport_comp_braiding`, `pullbackTensorIsoTransport_comp_leftUnitality`
  and `pullbackTensorIsoTransport_comp_rightUnitality`: the same for any composite of two
  comparisons of Stacks 03EL read through identifications of pullbacks, at ringed topoi of
  independent universes, read through `Stacks.SheafOfModules.monoidalCategory` on the target.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

/-! ### A composite of two comparisons, read through a conjugation on the target -/

section Abstract

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [mD : MonoidalCategory D]
  (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ D) {T₂ : C₂ → C₂ → C₂} {T₃ : D → D → D}
  (tD : ∀ a b : D, a ⊗ b ≅ T₃ a b)
  (δ₂ : ∀ a b : C₂, G₂.obj (T₂ a b) ≅ T₃ (G₂.obj a) (G₂.obj b))
  (w₂l : ∀ (a : C₂) {b b' : C₂}, (b ⟶ b') → (T₂ a b ⟶ T₂ a b'))
  (w₂r : ∀ {a a' : C₂}, (a ⟶ a') → ∀ b : C₂, (T₂ a b ⟶ T₂ a' b))
  (w₃l : ∀ (a : D) {b b' : D}, (b ⟶ b') → (T₃ a b ⟶ T₃ a b'))
  (w₃r : ∀ {a a' : D}, (a ⟶ a') → ∀ b : D, (T₃ a b ⟶ T₃ a' b))

/-- The composite of comparisons of `G₁` with the comparison `δ₂` of `G₂`, read through the
conjugation `tD` on the target, is compatible with the associators. -/
private theorem comp_conj_associativity
    (hw₃l : ∀ (a : D) {b b' : D} (g : b ⟶ b'), w₃l a g = (tD a b).inv ≫ (a ◁ g) ≫ (tD a b').hom)
    (hw₃r : ∀ {a a' : D} (g : a ⟶ a') (b : D), w₃r g b = (tD a b).inv ≫ (g ▷ b) ≫ (tD a' b).hom)
    (hR : ∀ (a : C₂) {b b' : C₂} (g : b ⟶ b'),
      G₂.map (w₂l a g) ≫ (δ₂ a b').hom = (δ₂ a b).hom ≫ w₃l (G₂.obj a) (G₂.map g))
    (hL : ∀ {a a' : C₂} (g : a ⟶ a') (b : C₂),
      G₂.map (w₂r g b) ≫ (δ₂ a' b).hom = (δ₂ a b).hom ≫ w₃r (G₂.map g) (G₂.obj b))
    {M N K MN NK MN_K M_NK : C₁} (a₁ : MN_K ⟶ M_NK)
    (dMN : G₁.obj MN ≅ T₂ (G₁.obj M) (G₁.obj N)) (dNK : G₁.obj NK ≅ T₂ (G₁.obj N) (G₁.obj K))
    (dMN_K : G₁.obj MN_K ≅ T₂ (G₁.obj MN) (G₁.obj K))
    (dM_NK : G₁.obj M_NK ≅ T₂ (G₁.obj M) (G₁.obj NK))
    (a₂ : T₂ (T₂ (G₁.obj M) (G₁.obj N)) (G₁.obj K) ⟶ T₂ (G₁.obj M) (T₂ (G₁.obj N) (G₁.obj K)))
    (h₁ : G₁.map a₁ ≫ dM_NK.hom ≫ w₂l (G₁.obj M) dNK.hom =
      dMN_K.hom ≫ w₂r dMN.hom (G₁.obj K) ≫ a₂)
    (a₃ : T₃ (T₃ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))) (G₂.obj (G₁.obj K)) ⟶
      T₃ (G₂.obj (G₁.obj M)) (T₃ (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K))))
    (ha₃ : a₃ = ((tD (T₃ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))) (G₂.obj (G₁.obj K))).inv ≫
      ((tD (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))).inv ⊗ₘ 𝟙 (G₂.obj (G₁.obj K)))) ≫
      ((α_ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K))).hom ≫
      ((𝟙 (G₂.obj (G₁.obj M)) ⊗ₘ (tD (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K))).hom) ≫
      (tD (G₂.obj (G₁.obj M)) (T₃ (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K)))).hom)))
    (h₂ : G₂.map a₂ ≫ (δ₂ (G₁.obj M) (T₂ (G₁.obj N) (G₁.obj K))).hom ≫
        w₃l (G₂.obj (G₁.obj M)) (δ₂ (G₁.obj N) (G₁.obj K)).hom =
      (δ₂ (T₂ (G₁.obj M) (G₁.obj N)) (G₁.obj K)).hom ≫
        w₃r (δ₂ (G₁.obj M) (G₁.obj N)).hom (G₂.obj (G₁.obj K)) ≫ a₃)
    (μMN : G₂.obj (G₁.obj MN) ≅ G₂.obj (G₁.obj M) ⊗ G₂.obj (G₁.obj N))
    (hμMN : μMN = G₂.mapIso dMN ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (μNK : G₂.obj (G₁.obj NK) ≅ G₂.obj (G₁.obj N) ⊗ G₂.obj (G₁.obj K))
    (hμNK : μNK = G₂.mapIso dNK ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (μMN_K : G₂.obj (G₁.obj MN_K) ≅ G₂.obj (G₁.obj MN) ⊗ G₂.obj (G₁.obj K))
    (hμMN_K : μMN_K = G₂.mapIso dMN_K ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (μM_NK : G₂.obj (G₁.obj M_NK) ≅ G₂.obj (G₁.obj M) ⊗ G₂.obj (G₁.obj NK))
    (hμM_NK : μM_NK = G₂.mapIso dM_NK ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (e₀ : G₂.obj (G₁.obj MN_K) ⟶ G₂.obj (G₁.obj M_NK)) (he₀ : e₀ = G₂.map (G₁.map a₁)) :
    e₀ ≫ μM_NK.hom ≫ (G₂.obj (G₁.obj M) ◁ μNK.hom) =
      μMN_K.hom ≫ (μMN.hom ▷ G₂.obj (G₁.obj K)) ≫
        (α_ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K))).hom := by
  have key : G₂.map (G₁.map a₁) ≫ G₂.map dM_NK.hom ≫ (δ₂ _ _).hom ≫
      w₃l _ (G₂.map dNK.hom) ≫ w₃l _ (δ₂ (G₁.obj N) (G₁.obj K)).hom =
      G₂.map dMN_K.hom ≫ (δ₂ _ _).hom ≫ w₃r (G₂.map dMN.hom) _ ≫
        w₃r (δ₂ (G₁.obj M) (G₁.obj N)).hom _ ≫ a₃ := by
    calc _ = G₂.map (G₁.map a₁ ≫ dM_NK.hom ≫ w₂l (G₁.obj M) dNK.hom) ≫
          (δ₂ (G₁.obj M) (T₂ (G₁.obj N) (G₁.obj K))).hom ≫
          w₃l (G₂.obj (G₁.obj M)) (δ₂ (G₁.obj N) (G₁.obj K)).hom := by
          rw [← reassoc_of% (hR (G₁.obj M) dNK.hom)]
          simp only [Functor.map_comp, Category.assoc]
      _ = G₂.map (dMN_K.hom ≫ w₂r dMN.hom (G₁.obj K) ≫ a₂) ≫
          (δ₂ (G₁.obj M) (T₂ (G₁.obj N) (G₁.obj K))).hom ≫
          w₃l (G₂.obj (G₁.obj M)) (δ₂ (G₁.obj N) (G₁.obj K)).hom := by rw [h₁]
      _ = _ := by
          simp only [Functor.map_comp, Category.assoc]
          rw [h₂, reassoc_of% (hL dMN.hom (G₁.obj K))]
  subst hμMN hμNK hμMN_K hμM_NK ha₃ he₀
  simp only [hw₃l, hw₃r] at key
  rw [← cancel_mono ((G₂.obj (G₁.obj M) ◁ (tD (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K))).hom) ≫
    (tD (G₂.obj (G₁.obj M)) (T₃ (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj K)))).hom)]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_inv_hom_assoc, MonoidalCategory.whiskerLeft_inv_hom,
    tensorHom_id, id_tensorHom, Category.comp_id] using key

/-- The composite of comparisons of `G₁` with the comparison `δ₂` of `G₂`, read through the
conjugation `tD` on the target, is compatible with the braidings. -/
private theorem comp_conj_braiding [bD : BraidedCategory D] {M N MN NM : C₁} (b₁ : MN ⟶ NM)
    (dMN : G₁.obj MN ≅ T₂ (G₁.obj M) (G₁.obj N)) (dNM : G₁.obj NM ≅ T₂ (G₁.obj N) (G₁.obj M))
    (b₂ : T₂ (G₁.obj M) (G₁.obj N) ⟶ T₂ (G₁.obj N) (G₁.obj M))
    (h₁ : G₁.map b₁ ≫ dNM.hom = dMN.hom ≫ b₂)
    (b₃ : T₃ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N)) ⟶ T₃ (G₂.obj (G₁.obj N)) (G₂.obj (G₁.obj M)))
    (hb₃ : b₃ = (tD _ _).inv ≫ (β_ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))).hom ≫ (tD _ _).hom)
    (h₂ : G₂.map b₂ ≫ (δ₂ (G₁.obj N) (G₁.obj M)).hom = (δ₂ (G₁.obj M) (G₁.obj N)).hom ≫ b₃)
    (μMN : G₂.obj (G₁.obj MN) ≅ G₂.obj (G₁.obj M) ⊗ G₂.obj (G₁.obj N))
    (hμMN : μMN = G₂.mapIso dMN ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (μNM : G₂.obj (G₁.obj NM) ≅ G₂.obj (G₁.obj N) ⊗ G₂.obj (G₁.obj M))
    (hμNM : μNM = G₂.mapIso dNM ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (e₀ : G₂.obj (G₁.obj MN) ⟶ G₂.obj (G₁.obj NM)) (he₀ : e₀ = G₂.map (G₁.map b₁)) :
    e₀ ≫ μNM.hom = μMN.hom ≫ (β_ (G₂.obj (G₁.obj M)) (G₂.obj (G₁.obj N))).hom := by
  subst hμMN hμNM he₀ hb₃
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← G₂.map_comp_assoc, h₁, G₂.map_comp_assoc, reassoc_of% h₂]
  simp

/-- The composite of the comparison `dOM` of `G₁` with the comparison `δ₂` of `G₂`, read through
the conjugation `tD` on the target, is compatible with the left unitors, the units being matched by
`ε`. -/
private theorem comp_conj_leftUnitality
    (hw₃r : ∀ {a a' : D} (g : a ⟶ a') (b : D), w₃r g b = (tD a b).inv ≫ (g ▷ b) ≫ (tD a' b).hom)
    {M OM u₁ : C₁} {u₂ : C₂} (l₁ : OM ⟶ M)
    (dOM : G₁.obj OM ≅ T₂ (G₁.obj u₁) (G₁.obj M)) (e₁ : G₁.obj u₁ ⟶ u₂)
    (l₂ : T₂ u₂ (G₁.obj M) ⟶ G₁.obj M) (h₁ : G₁.map l₁ = dOM.hom ≫ w₂r e₁ (G₁.obj M) ≫ l₂)
    (hL : G₂.map (w₂r e₁ (G₁.obj M)) ≫ (δ₂ u₂ (G₁.obj M)).hom =
      (δ₂ (G₁.obj u₁) (G₁.obj M)).hom ≫ w₃r (G₂.map e₁) (G₂.obj (G₁.obj M)))
    (e₂ : G₂.obj u₂ ⟶ 𝟙_ D) (l₃ : T₃ (𝟙_ D) (G₂.obj (G₁.obj M)) ⟶ G₂.obj (G₁.obj M))
    (hl₃ : l₃ = (tD _ _).inv ≫ (λ_ (G₂.obj (G₁.obj M))).hom)
    (h₂ : G₂.map l₂ = (δ₂ u₂ (G₁.obj M)).hom ≫ w₃r e₂ (G₂.obj (G₁.obj M)) ≫ l₃)
    (μ : G₂.obj (G₁.obj OM) ≅ G₂.obj (G₁.obj u₁) ⊗ G₂.obj (G₁.obj M))
    (hμ : μ = G₂.mapIso dOM ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (ε : G₂.obj (G₁.obj u₁) ⟶ 𝟙_ D) (hε : ε = G₂.map e₁ ≫ e₂)
    (e₀ : G₂.obj (G₁.obj OM) ⟶ G₂.obj (G₁.obj M)) (he₀ : e₀ = G₂.map (G₁.map l₁)) :
    e₀ = μ.hom ≫ (ε ▷ G₂.obj (G₁.obj M)) ≫ (λ_ (G₂.obj (G₁.obj M))).hom := by
  subst hμ hε he₀ hl₃
  rw [h₁, G₂.map_comp, G₂.map_comp, h₂, reassoc_of% hL, hw₃r, hw₃r]
  simp

/-- The composite of the comparison `dMO` of `G₁` with the comparison `δ₂` of `G₂`, read through
the conjugation `tD` on the target, is compatible with the right unitors, the units being matched
by `ε`. -/
private theorem comp_conj_rightUnitality
    (hw₃l : ∀ (a : D) {b b' : D} (g : b ⟶ b'), w₃l a g = (tD a b).inv ≫ (a ◁ g) ≫ (tD a b').hom)
    {M MO u₁ : C₁} {u₂ : C₂} (r₁ : MO ⟶ M)
    (dMO : G₁.obj MO ≅ T₂ (G₁.obj M) (G₁.obj u₁)) (e₁ : G₁.obj u₁ ⟶ u₂)
    (r₂ : T₂ (G₁.obj M) u₂ ⟶ G₁.obj M) (h₁ : G₁.map r₁ = dMO.hom ≫ w₂l (G₁.obj M) e₁ ≫ r₂)
    (hR : G₂.map (w₂l (G₁.obj M) e₁) ≫ (δ₂ (G₁.obj M) u₂).hom =
      (δ₂ (G₁.obj M) (G₁.obj u₁)).hom ≫ w₃l (G₂.obj (G₁.obj M)) (G₂.map e₁))
    (e₂ : G₂.obj u₂ ⟶ 𝟙_ D) (r₃ : T₃ (G₂.obj (G₁.obj M)) (𝟙_ D) ⟶ G₂.obj (G₁.obj M))
    (hr₃ : r₃ = (tD _ _).inv ≫ (ρ_ (G₂.obj (G₁.obj M))).hom)
    (h₂ : G₂.map r₂ = (δ₂ (G₁.obj M) u₂).hom ≫ w₃l (G₂.obj (G₁.obj M)) e₂ ≫ r₃)
    (μ : G₂.obj (G₁.obj MO) ≅ G₂.obj (G₁.obj M) ⊗ G₂.obj (G₁.obj u₁))
    (hμ : μ = G₂.mapIso dMO ≪≫ δ₂ _ _ ≪≫ (tD _ _).symm)
    (ε : G₂.obj (G₁.obj u₁) ⟶ 𝟙_ D) (hε : ε = G₂.map e₁ ≫ e₂)
    (e₀ : G₂.obj (G₁.obj MO) ⟶ G₂.obj (G₁.obj M)) (he₀ : e₀ = G₂.map (G₁.map r₁)) :
    e₀ = μ.hom ≫ (G₂.obj (G₁.obj M) ◁ ε) ≫ (ρ_ (G₂.obj (G₁.obj M))).hom := by
  subst hμ hε he₀ hr₃
  rw [h₁, G₂.map_comp, G₂.map_comp, h₂, reassoc_of% hR, hw₃l, hw₃l]
  simp

end Abstract

/-! ### Two comparisons of Stacks 03EL read through identifications, composed -/

namespace Stacks.SheafOfModules

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] Strict.monoidalUnderlyingRingSheaf Strict.braidedUnderlyingRingSheaf

variable {X₁ : AlgebraicGeometry.RingedTopos.{v₁, u₁, w₁}}
    {X₂ : AlgebraicGeometry.RingedTopos.{v₂, u₂, w₂}}
    {X₃ : AlgebraicGeometry.RingedTopos.{v₃, u₃, w₃}}
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X₁.J.HasSheafCompose (forget RingCat.{w₁})] [X₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget RingCat.{w₃})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [X₃.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasWeakSheafify X₃.J AddCommGrpCat.{w₃}] [X₃.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  (f₁ : Stacks.Sheaves.RingedToposModules.RingedToposHom X₂ X₁)
  {L₁ : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O) ⥤
    _root_.SheafOfModules.{w₂} (Tensor.ringSheaf X₂.O)}
  (α₁ : f₁.pullbackModules ≅ L₁)
  (f₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X₃ X₂)
  {L₂ : _root_.SheafOfModules.{w₂} (Tensor.ringSheaf X₂.O) ⥤
    _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O)}
  (α₂ : f₂.pullbackModules ≅ L₂)

/-- Two comparisons of Stacks 03EL read through identifications of pullbacks, composed and read
through the monoidal structure `Stacks.SheafOfModules.monoidalCategory` on the target, are
compatible with the associators: those of the strict structure of Tag 01CA on the source, of
`Stacks.SheafOfModules.monoidalCategory` on the target. The composites are given as `μ`, each
identified with `L₂(δ₁) ≫ δ₂ ≫ t⁻¹` by an equation. -/
theorem pullbackTensorIsoTransport_comp_associativity
    (M N K : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O))
    (μMN : L₂.obj (L₁.obj (M ⊗ N)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
      (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N)))
    (hμMN : μMN = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ M N) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj M) (L₁.obj N) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (μNK : L₂.obj (L₁.obj (N ⊗ K)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
      (L₂.obj (L₁.obj N)) (L₂.obj (L₁.obj K)))
    (hμNK : μNK = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ N K) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj N) (L₁.obj K) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (μMN_K : L₂.obj (L₁.obj ((M ⊗ N) ⊗ K)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
      (L₂.obj (L₁.obj (M ⊗ N))) (L₂.obj (L₁.obj K)))
    (hμMN_K : μMN_K = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ (M ⊗ N) K) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj (M ⊗ N)) (L₁.obj K) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (μM_NK : L₂.obj (L₁.obj (M ⊗ (N ⊗ K))) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
      (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj (N ⊗ K))))
    (hμM_NK : μM_NK = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ M (N ⊗ K)) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj M) (L₁.obj (N ⊗ K)) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (e₀ : L₂.obj (L₁.obj ((M ⊗ N) ⊗ K)) ⟶ L₂.obj (L₁.obj (M ⊗ (N ⊗ K))))
    (he₀ : e₀ = L₂.map (L₁.map (α_ M N K).hom)) :
    e₀ ≫ μM_NK.hom ≫ MonoidalCategoryStruct.whiskerLeft
        (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        (L₂.obj (L₁.obj M)) μNK.hom =
      μMN_K.hom ≫ MonoidalCategoryStruct.whiskerRight
        (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        μMN.hom (L₂.obj (L₁.obj K)) ≫
      (MonoidalCategoryStruct.associator
        (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N)) (L₂.obj (L₁.obj K))).hom :=
  comp_conj_associativity (D := _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O))
    (mD := monoidalCategory X₃.O.obj
      (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)) L₁ L₂
    (T₂ := fun a b => a ⊗ b) (T₃ := fun a b => a ⊗ b)
    (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
    (fun a b => pullbackTensorIsoTransport f₂ α₂ a b)
    (fun a {_ _} g => a ◁ g) (fun {_ _} g b => g ▷ b)
    (fun a {_ _} g => a ◁ g) (fun {_ _} g b => g ▷ b)
    (fun _ {_ _} _ => rfl) (fun {_ _} _ _ => rfl)
    (pullbackTensorIsoTransport_whiskerLeft_naturality f₂ α₂)
    (pullbackTensorIsoTransport_whiskerRight_naturality f₂ α₂)
    (α_ M N K).hom (pullbackTensorIsoTransport f₁ α₁ M N) (pullbackTensorIsoTransport f₁ α₁ N K)
    (pullbackTensorIsoTransport f₁ α₁ (M ⊗ N) K) (pullbackTensorIsoTransport f₁ α₁ M (N ⊗ K))
    (α_ (L₁.obj M) (L₁.obj N) (L₁.obj K)).hom
    (pullbackTensorIsoTransport_associativity f₁ α₁ M N K)
    (α_ (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N)) (L₂.obj (L₁.obj K))).hom rfl
    (pullbackTensorIsoTransport_associativity f₂ α₂ (L₁.obj M) (L₁.obj N) (L₁.obj K))
    μMN hμMN μNK hμNK μMN_K hμMN_K μM_NK hμM_NK e₀ he₀

/-- Two comparisons of Stacks 03EL read through identifications of pullbacks, composed and read
through `Stacks.SheafOfModules.monoidalCategory` on the target, are compatible with the
braidings. -/
theorem pullbackTensorIsoTransport_comp_braiding
    (M N : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O))
    (μMN : L₂.obj (L₁.obj (M ⊗ N)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf
          X₃.O)).toMonoidalCategoryStruct) (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N)))
    (hμMN : μMN = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ M N) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj M) (L₁.obj N) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (μNM : L₂.obj (L₁.obj (N ⊗ M)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf
          X₃.O)).toMonoidalCategoryStruct) (L₂.obj (L₁.obj N)) (L₂.obj (L₁.obj M)))
    (hμNM : μNM = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ N M) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj N) (L₁.obj M) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (e₀ : L₂.obj (L₁.obj (M ⊗ N)) ⟶ L₂.obj (L₁.obj (N ⊗ M)))
    (he₀ : e₀ = L₂.map (L₁.map (β_ M N).hom)) :
    e₀ ≫ μNM.hom = μMN.hom ≫ (BraidedCategory.braiding (self := braidedCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
      (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N))).hom :=
  comp_conj_braiding (D := _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O))
    (mD := monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
    (bD := braidedCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)) L₁ L₂
    (T₂ := fun a b => a ⊗ b) (T₃ := fun a b => a ⊗ b)
    (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
    (fun a b => pullbackTensorIsoTransport f₂ α₂ a b)
    (β_ M N).hom (pullbackTensorIsoTransport f₁ α₁ M N) (pullbackTensorIsoTransport f₁ α₁ N M)
    (β_ (L₁.obj M) (L₁.obj N)).hom (pullbackTensorIsoTransport_braiding f₁ α₁ M N)
    (β_ (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj N))).hom rfl
    (pullbackTensorIsoTransport_braiding f₂ α₂ (L₁.obj M) (L₁.obj N))
    μMN hμMN μNM hμNM e₀ he₀

/-- Two comparisons of Stacks 03EL read through identifications of pullbacks, composed and read
through `Stacks.SheafOfModules.monoidalCategory` on the target, are compatible with the left
unitors, the units being matched by the composite `ε` of the two identifications
`Stacks.SheafOfModules.pullbackUnitIsoTransport`. -/
theorem pullbackTensorIsoTransport_comp_leftUnitality
    (M : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O))
    (μ : L₂.obj (L₁.obj (𝟙_ _ ⊗ M)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf
          X₃.O)).toMonoidalCategoryStruct) (L₂.obj (L₁.obj (𝟙_ _))) (L₂.obj (L₁.obj M)))
    (hμ : μ = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ (𝟙_ _) M) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj (𝟙_ _)) (L₁.obj M) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (ε : L₂.obj (L₁.obj (𝟙_ _)) ⟶ _root_.SheafOfModules.unit (Tensor.ringSheaf X₃.O))
    (hε : ε = L₂.map (pullbackUnitIsoTransport f₁ α₁).hom ≫ (pullbackUnitIsoTransport f₂ α₂).hom)
    (e₀ : L₂.obj (L₁.obj (𝟙_ _ ⊗ M)) ⟶ L₂.obj (L₁.obj M))
    (he₀ : e₀ = L₂.map (L₁.map (λ_ M).hom)) :
    e₀ = μ.hom ≫ MonoidalCategoryStruct.whiskerRight (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct) ε
        (L₂.obj (L₁.obj M)) ≫
      (MonoidalCategoryStruct.leftUnitor (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        (L₂.obj (L₁.obj M))).hom :=
  comp_conj_leftUnitality (D := _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O))
    (mD := monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)) L₁ L₂
    (T₂ := fun a b => a ⊗ b) (T₃ := fun a b => a ⊗ b)
    (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
    (fun a b => pullbackTensorIsoTransport f₂ α₂ a b)
    (fun {_ _} g b => g ▷ b) (fun {_ _} g b => g ▷ b) (fun {_ _} _ _ => rfl)
    (λ_ M).hom (pullbackTensorIsoTransport f₁ α₁ (𝟙_ _) M) (pullbackUnitIsoTransport f₁ α₁).hom
    (λ_ (L₁.obj M)).hom (pullbackTensorIsoTransport_leftUnitality f₁ α₁ M)
    (pullbackTensorIsoTransport_whiskerRight_naturality f₂ α₂ (pullbackUnitIsoTransport f₁ α₁).hom
      (L₁.obj M))
    (pullbackUnitIsoTransport f₂ α₂).hom (λ_ (L₂.obj (L₁.obj M))).hom rfl
    (pullbackTensorIsoTransport_leftUnitality f₂ α₂ (L₁.obj M)) μ hμ ε hε e₀ he₀

/-- Two comparisons of Stacks 03EL read through identifications of pullbacks, composed and read
through `Stacks.SheafOfModules.monoidalCategory` on the target, are compatible with the right
unitors, the units being matched by the composite `ε` of the two identifications
`Stacks.SheafOfModules.pullbackUnitIsoTransport`. -/
theorem pullbackTensorIsoTransport_comp_rightUnitality
    (M : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O))
    (μ : L₂.obj (L₁.obj (M ⊗ 𝟙_ _)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf
          X₃.O)).toMonoidalCategoryStruct) (L₂.obj (L₁.obj M)) (L₂.obj (L₁.obj (𝟙_ _))))
    (hμ : μ = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ M (𝟙_ _)) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj M) (L₁.obj (𝟙_ _)) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (ε : L₂.obj (L₁.obj (𝟙_ _)) ⟶ _root_.SheafOfModules.unit (Tensor.ringSheaf X₃.O))
    (hε : ε = L₂.map (pullbackUnitIsoTransport f₁ α₁).hom ≫ (pullbackUnitIsoTransport f₂ α₂).hom)
    (e₀ : L₂.obj (L₁.obj (M ⊗ 𝟙_ _)) ⟶ L₂.obj (L₁.obj M))
    (he₀ : e₀ = L₂.map (L₁.map (ρ_ M).hom)) :
    e₀ = μ.hom ≫ MonoidalCategoryStruct.whiskerLeft (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        (L₂.obj (L₁.obj M)) ε ≫
      (MonoidalCategoryStruct.rightUnitor (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct)
        (L₂.obj (L₁.obj M))).hom :=
  comp_conj_rightUnitality (D := _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O))
    (mD := monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)) L₁ L₂
    (T₂ := fun a b => a ⊗ b) (T₃ := fun a b => a ⊗ b)
    (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O))
    (fun a b => pullbackTensorIsoTransport f₂ α₂ a b)
    (fun a {_ _} g => a ◁ g) (fun a {_ _} g => a ◁ g) (fun _ {_ _} _ => rfl)
    (ρ_ M).hom (pullbackTensorIsoTransport f₁ α₁ M (𝟙_ _)) (pullbackUnitIsoTransport f₁ α₁).hom
    (ρ_ (L₁.obj M)).hom (pullbackTensorIsoTransport_rightUnitality f₁ α₁ M)
    (pullbackTensorIsoTransport_whiskerLeft_naturality f₂ α₂ (L₁.obj M)
      (pullbackUnitIsoTransport f₁ α₁).hom)
    (pullbackUnitIsoTransport f₂ α₂).hom (ρ_ (L₂.obj (L₁.obj M))).hom rfl
    (pullbackTensorIsoTransport_rightUnitality f₂ α₂ (L₁.obj M)) μ hμ ε hε e₀ he₀

end Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The associator of the tensor product sheaf of Tag 01CA, between quasi-coherent tensor
products on the scheme underlying `U`. -/
abbrev quasicoherentAssociator
    (M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentTensorObj B S hS U (quasicoherentTensorObj B S hS U M N) K ≅
      quasicoherentTensorObj B S hS U M (quasicoherentTensorObj B S hS U N K) :=
  ObjectProperty.isoMk _ (MonoidalCategoryStruct.associator (self :=
      ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf ((BigFppfOver.toScheme B S hS).obj
          U).zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct)) M.obj N.obj K.obj)

section Irreducible

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.SheafOfModules.pullbackTensorIso

/-- The tensor identification of Stacks 03DX (2) on a representable is compatible with the
associators: for quasi-coherent modules `M`, `N`, `K` on the scheme underlying `U`, the two ways
of identifying `((M ⊗ N) ⊗ K)_{yoneda U}` with `M_{yoneda U} ⊗ (N_{yoneda U} ⊗ K_{yoneda U})`
agree. -/
theorem representedQuasicoherentSchemeTensorIso_associativity
    (M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
        (quasicoherentAssociator B S hS U M N K).hom).hom ≫
      (representedQuasicoherentSchemeTensorIso B S hS U M
        (quasicoherentTensorObj B S hS U N K)).hom ≫
      MonoidalCategoryStruct.whiskerLeft (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        (representedQuasicoherentSchemeTensorIso B S hS U N K).hom =
    (representedQuasicoherentSchemeTensorIso B S hS U
        (quasicoherentTensorObj B S hS U M N) K).hom ≫
      MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (representedQuasicoherentSchemeTensorIso B S hS U M N).hom
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj ≫
      (MonoidalCategoryStruct.associator (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj).hom := by
  refine Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_associativity
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (Stacks.SheafOfModules.reindexRingedToposModulesHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    M.obj N.obj K.obj _ ?_ _ ?_ _ ?_ _ ?_ _ ?_
  all_goals first
    | exact representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS U _
    | exact representedQuasicoherentSchemeTensorIso_eq B S hS U _ _

/-- The braiding of the tensor product sheaf of Tag 01CA, between quasi-coherent tensor products
on the scheme underlying `U`. -/
abbrev quasicoherentBraiding (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentTensorObj B S hS U M N ≅ quasicoherentTensorObj B S hS U N M :=
  ObjectProperty.isoMk _ (BraidedCategory.braiding (self :=
      (Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)) M.obj N.obj)

/-- The tensor identification of Stacks 03DX (2) on a representable is compatible with the
braidings. -/
theorem representedQuasicoherentSchemeTensorIso_braiding (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
        (quasicoherentBraiding B S hS U M N).hom).hom ≫
      (representedQuasicoherentSchemeTensorIso B S hS U N M).hom =
    (representedQuasicoherentSchemeTensorIso B S hS U M N).hom ≫
      (BraidedCategory.braiding (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom := by
  refine Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_braiding
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (Stacks.SheafOfModules.reindexRingedToposModulesHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    M.obj N.obj _ ?_ _ ?_ _ ?_
  all_goals first
    | exact representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS U _
    | exact representedQuasicoherentSchemeTensorIso_eq B S hS U _ _

end Irreducible

end AlgebraicGeometry.Space

end
