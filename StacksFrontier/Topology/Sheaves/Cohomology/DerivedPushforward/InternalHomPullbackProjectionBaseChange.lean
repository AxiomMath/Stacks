module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The projection map of a functor with a left adjoint: converse criterion and base change

Let `P : D₁ ⥤ D₂` carry the data of the transpose construction of Tag 08I3 (internal homs,
tensor products, tensor–hom bijections and a monoidality comparison `m`) and let `L ⊣ P`. The
projection maps `π(W, A) : L(W ⊗ P A) ⟶ L W ⊗ A`
(`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.projectionMap`) control the comparison
`P H(A, B) ⟶ H(P A, P B)`: by
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_homComparison_of_isIso_projectionMap`
the comparison at `A` is invertible for every `B` as soon as `π(W, A)` is for every `W`. This file
proves the converse, and the compatibility of the projection maps with base change.

For the base change, consider a square of categories

```
DT' <--Pu'-- DT
 ^            ^
 |Pt'         |Pt
DU  <--Pu--- DZ
```

whose horizontal functors have left adjoints `Lu ⊣ Pu`, `Lu' ⊣ Pu'`, with an identification
`σ : Pu ⋙ Pt' ≅ Pt ⋙ Pu'`, its mate `β : Pt' ⋙ Lu' ⟶ Lu ⋙ Pt` (the base change map), and
bifunctors on the four corners with comparisons along the four functors which are compatible
around the square. Then `Pt` carries the projection map of `Pu` at `(W, A)` to the projection map
of `Pu'` at `(Pt' W, Pt A)`, read through `β` and the comparisons. So if `β` is invertible, the
projection maps of `Pu'` being invertible forces those of `Pu` to become invertible after `Pt`.

## Main definitions

* `IsMateOf`: the base change map is the mate of the identification of the two composites.

## Main results

* `isIso_projectionMap_of_isIso_homComparison`: the projection maps at `A` are invertible as soon
  as the comparisons at `A` are.
* `unit_comp_map_eq_of_eq_mate`: the unit identity of a base change map given by the mate formula.
* `projectionMap_baseChange`: `Pt` carries the projection map of `Pu` at `(W, A)` to the
  projection map of `Pu'` at `(Pt' W, Pt A)`, read through `β` and the comparisons.
* `isIso_map_projectionMap_of_baseChange` and
  `isIso_map_projectionMap_of_baseChange_of_tensorComparisonCompatible`: if `β` and the projection
  map of `Pu'` are invertible, then `Pt` carries the projection map of `Pu` to an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

section Converse

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)
  {L : D₂ ⥤ D₁} (adj : L ⊣ P)

/-- **The projection maps out of an object at which the comparison is invertible are
invertible.** If `P H(A, B) ⟶ H(P A, P B)` is invertible for every `B`, then
`L(W ⊗ P A) ⟶ L W ⊗ A` is invertible for every `W`. -/
theorem isIso_projectionMap_of_isIso_homComparison
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A : D₁) (hc : ∀ B : D₁, IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)) (W : D₂) :
    IsIso (projectionMap P T₁ T₂ m adj W A) := by
  refine isIso_of_coyoneda_map_bijective _ fun B => ?_
  have hf : (fun k : T₁.obj (L.obj W, A) ⟶ B => projectionMap P T₁ T₂ m adj W A ≫ k) =
      (adj.homEquiv _ _).symm ∘ (e₂ W (P.obj A) (P.obj B)) ∘
        (fun g => g ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) ∘
          (adj.homEquiv W ((H₁.obj (op A)).obj B)) ∘ (e₁ (L.obj W) A B).symm := by
    funext k
    simp only [Function.comp_apply]
    rw [homEquiv_symm_e₂_comp_homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m adj hnat₁ hnat₂ A B W,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [hf]
  have := hc B
  refine (adj.homEquiv _ _).symm.bijective.comp ((e₂ _ _ _).bijective.comp
    (Function.Bijective.comp ?_ ((adj.homEquiv _ _).bijective.comp (e₁ _ _ _).symm.bijective)))
  exact ⟨fun g g' h => (cancel_mono _).1 h,
    fun g => ⟨g ≫ inv (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B), by simp⟩⟩

end Converse

section BaseChange

variable {DZ DU DT DT' : Type*} {cZ : Category DZ} {cU : Category DU} {cT : Category DT}
  {cT' : Category DT'}
  {Pu : DZ ⥤ DU} {Lu : DU ⥤ DZ} (adju : Lu ⊣ Pu)
  {Pu' : DT ⥤ DT'} {Lu' : DT' ⥤ DT} (adju' : Lu' ⊣ Pu')
  (Pt : DZ ⥤ DT) (Pt' : DU ⥤ DT') (σ : Pu ⋙ Pt' ≅ Pt ⋙ Pu')
  (TZ : DZ × DZ ⥤ DZ) (TU : DU × DU ⥤ DU) (TT : DT × DT ⥤ DT) (TT' : DT' × DT' ⥤ DT')
  (mu : TZ ⋙ Pu ≅ Pu.prod Pu ⋙ TU) (mu' : TT ⋙ Pu' ≅ Pu'.prod Pu' ⋙ TT')
  (mt : TZ ⋙ Pt ≅ Pt.prod Pt ⋙ TT) (mt' : TU ⋙ Pt' ≅ Pt'.prod Pt' ⋙ TT')
  (β : Pt' ⋙ Lu' ⟶ Lu ⋙ Pt)

/-- **`β` is the mate of `σ`**: at every `W` it is `Lu'(Pt'(η_W) ≫ σ) ≫ ε'`, the transpose
under `Lu' ⊣ Pu'` of the unit of `Lu ⊣ Pu` followed by `σ`. -/
def IsMateOf : Prop :=
  ∀ W : DU, β.app W = Lu'.map (Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W)) ≫
    adju'.counit.app (Pt.obj (Lu.obj W))

/-- **The unit identity of a mate.** If `β` is given at `W` by the mate formula
`Lu'(Pt'(η_W) ≫ σ) ≫ ε'`, then `η' ≫ Pu'(β_W) = Pt'(η_W) ≫ σ`. -/
theorem unit_comp_map_eq_of_eq_mate (hβ : IsMateOf adju adju' Pt Pt' σ β) (W : DU) :
    adju'.unit.app (Pt'.obj W) ≫ Pu'.map (β.app W) =
      Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W) := by
  have h := (adju'.homEquiv _ _).apply_symm_apply
    (Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W))
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  rwa [hβ W]

/-- The compatibility of the four comparisons around the square, solved for the comparison
along `Pu` read backwards. -/
theorem map_inv_comp_square_comp_map
    (hsq : ∀ M N : DZ, Pt'.map (mu.hom.app (M, N)) ≫ mt'.hom.app (Pu.obj M, Pu.obj N) ≫
        TT'.map (σ.hom.app M ×ₘ σ.hom.app N) =
      σ.hom.app (TZ.obj (M, N)) ≫ Pu'.map (mt.hom.app (M, N)) ≫
        mu'.hom.app (Pt.obj M, Pt.obj N))
    (M N : DZ) :
    Pt'.map (mu.inv.app (M, N)) ≫ σ.hom.app (TZ.obj (M, N)) ≫ Pu'.map (mt.hom.app (M, N)) =
      mt'.hom.app (Pu.obj M, Pu.obj N) ≫ TT'.map (σ.hom.app M ×ₘ σ.hom.app N) ≫
        mu'.inv.app (Pt.obj M, Pt.obj N) := by
  rw [← cancel_epi (Pt'.map (mu.hom.app (M, N))), ← Pt'.map_comp_assoc, Iso.hom_inv_id_app,
    Pt'.map_id, Category.id_comp, reassoc_of% (hsq M N)]
  simp

/-- Composing the images of two product morphisms under a bifunctor. -/
@[reassoc]
theorem map_prod_comp_map_prod {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {a a' a'' : C} {b b' b'' : D} (f : a ⟶ a') (f' : a' ⟶ a'') (g : b ⟶ b')
    (g' : b' ⟶ b'') : F.map (f ×ₘ g) ≫ F.map (f' ×ₘ g') = F.map ((f ≫ f') ×ₘ (g ≫ g')) := by
  rw [← F.map_comp]
  rfl

/-- **The projection map commutes with base change.** For a square with left adjoints `Lu ⊣ Pu`,
`Lu' ⊣ Pu'`, an identification `σ : Pu ⋙ Pt' ≅ Pt ⋙ Pu'` with mate `β` (hypothesis `hβ`) and
comparisons of bifunctors compatible around the square (hypothesis `hsq`), the image under `Pt`
of the projection map of `Pu` at `(W, A)` is the projection map of `Pu'` at `(Pt' W, Pt A)`:

`β ≫ Pt(π(W, A)) ≫ mt = Lu'(mt' ≫ (1 ⊗ σ)) ≫ π'(Pt' W, Pt A) ≫ (β ⊗ 1)`. -/
theorem projectionMap_baseChange
    (hβ : ∀ W : DU, adju'.unit.app (Pt'.obj W) ≫ Pu'.map (β.app W) =
      Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W))
    (hsq : ∀ M N : DZ, Pt'.map (mu.hom.app (M, N)) ≫ mt'.hom.app (Pu.obj M, Pu.obj N) ≫
        TT'.map (σ.hom.app M ×ₘ σ.hom.app N) =
      σ.hom.app (TZ.obj (M, N)) ≫ Pu'.map (mt.hom.app (M, N)) ≫
        mu'.hom.app (Pt.obj M, Pt.obj N))
    (W : DU) (A : DZ) :
    β.app (TU.obj (W, Pu.obj A)) ≫ Pt.map (projectionMap Pu TZ TU mu adju W A) ≫
        mt.hom.app (Lu.obj W, A) =
      Lu'.map (mt'.hom.app (W, Pu.obj A) ≫ TT'.map (𝟙 (Pt'.obj W) ×ₘ σ.hom.app A)) ≫
        projectionMap Pu' TT TT' mu' adju' (Pt'.obj W) (Pt.obj A) ≫
          TT.map (β.app W ×ₘ 𝟙 (Pt.obj A)) := by
  apply (adju'.homEquiv _ _).injective
  have hσ := σ.hom.naturality (projectionMap Pu TZ TU mu adju W A)
  dsimp only [Functor.comp_map] at hσ
  have hl : adju'.homEquiv _ _ (β.app (TU.obj (W, Pu.obj A)) ≫
      Pt.map (projectionMap Pu TZ TU mu adju W A) ≫ mt.hom.app (Lu.obj W, A)) =
      Pt'.map (TU.map (adju.unit.app W ×ₘ 𝟙 (Pu.obj A))) ≫
        mt'.hom.app (Pu.obj (Lu.obj W), Pu.obj A) ≫
          TT'.map (σ.hom.app (Lu.obj W) ×ₘ σ.hom.app A) ≫
            mu'.inv.app (Pt.obj (Lu.obj W), Pt.obj A) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
      reassoc_of% (hβ (TU.obj (W, Pu.obj A))), ← reassoc_of% hσ, ← Pt'.map_comp_assoc,
      unit_comp_map_projectionMap, Pt'.map_comp, Category.assoc,
      map_inv_comp_square_comp_map Pt Pt' σ TZ TU TT TT' mu mu' mt mt' hsq]
  have hn := mu'.inv.naturality (β.app W ×ₘ 𝟙 (Pt.obj A))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [Pu'.map_id] at hn
  have hr : adju'.homEquiv _ _
      (Lu'.map (mt'.hom.app (W, Pu.obj A) ≫ TT'.map (𝟙 (Pt'.obj W) ×ₘ σ.hom.app A)) ≫
        projectionMap Pu' TT TT' mu' adju' (Pt'.obj W) (Pt.obj A) ≫
          TT.map (β.app W ×ₘ 𝟙 (Pt.obj A))) =
      mt'.hom.app (W, Pu.obj A) ≫
        TT'.map ((Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W)) ×ₘ σ.hom.app A) ≫
          mu'.inv.app (Pt.obj (Lu.obj W), Pt.obj A) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_unit]
    dsimp only [Functor.comp_obj]
    rw [unit_comp_map_projectionMap]
    simp only [Category.assoc]
    dsimp only [Functor.comp_obj] at hn
    rw [← hn, map_prod_comp_map_prod_assoc, map_prod_comp_map_prod_assoc]
    simp only [Category.id_comp, Category.comp_id]
    rw [hβ W]
  refine hl.trans (Eq.trans ?_ hr.symm)
  have hm := mt'.hom.naturality (adju.unit.app W ×ₘ 𝟙 (Pu.obj A))
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  rw [Pt'.map_id] at hm
  rw [reassoc_of% hm, map_prod_comp_map_prod_assoc]
  simp only [Category.id_comp]

/-- **Invertibility of the projection map after base change.** Under the hypotheses of
`projectionMap_baseChange`, if the base change map `β` is invertible at `W` and at `W ⊗ Pu A`,
and the projection map of `Pu'` at `(Pt' W, Pt A)` is invertible, then `Pt` carries the
projection map of `Pu` at `(W, A)` to an isomorphism. -/
theorem isIso_map_projectionMap_of_baseChange
    (hβ : ∀ W : DU, adju'.unit.app (Pt'.obj W) ≫ Pu'.map (β.app W) =
      Pt'.map (adju.unit.app W) ≫ σ.hom.app (Lu.obj W))
    (hsq : ∀ M N : DZ, Pt'.map (mu.hom.app (M, N)) ≫ mt'.hom.app (Pu.obj M, Pu.obj N) ≫
        TT'.map (σ.hom.app M ×ₘ σ.hom.app N) =
      σ.hom.app (TZ.obj (M, N)) ≫ Pu'.map (mt.hom.app (M, N)) ≫
        mu'.hom.app (Pt.obj M, Pt.obj N))
    (W : DU) (A : DZ) [IsIso (β.app W)] [IsIso (β.app (TU.obj (W, Pu.obj A)))]
    [IsIso (projectionMap Pu' TT TT' mu' adju' (Pt'.obj W) (Pt.obj A))] :
    IsIso (Pt.map (projectionMap Pu TZ TU mu adju W A)) := by
  have h := projectionMap_baseChange adju adju' Pt Pt' σ TZ TU TT TT' mu mu' mt mt' β hβ hsq W A
  have : IsIso (𝟙 (Pt'.obj W) ×ₘ σ.hom.app A) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (β.app W ×ₘ 𝟙 (Pt.obj A)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (β.app (TU.obj (W, Pu.obj A)) ≫ Pt.map (projectionMap Pu TZ TU mu adju W A) ≫
      mt.hom.app (Lu.obj W, A)) := by
    rw [h]; infer_instance
  have : IsIso (Pt.map (projectionMap Pu TZ TU mu adju W A) ≫ mt.hom.app (Lu.obj W, A)) :=
    IsIso.of_isIso_comp_left (β.app (TU.obj (W, Pu.obj A))) _
  exact IsIso.of_isIso_comp_right _ (mt.hom.app (Lu.obj W, A))

/-- **Invertibility of the projection map after base change, with the identification of the
two composites around the square given through a common composite.** As
`isIso_map_projectionMap_of_baseChange`, with `σ` equal to the comparison
`Stacks.AffineProjectionFormula.squareCompositeIso eg ef` of two identifications `eg`, `ef` with a
functor `Φ`, and the compatibility of the four comparisons stated in the form
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` at `eg` and `ef`. -/
theorem isIso_map_projectionMap_of_baseChange_of_tensorComparisonCompatible
    {Φ : DZ ⥤ DT'} (eg : Pu ⋙ Pt' ≅ Φ) (ef : Pt ⋙ Pu' ≅ Φ)
    (e : σ = Stacks.AffineProjectionFormula.squareCompositeIso eg ef)
    (hβ : IsMateOf adju adju' Pt Pt' σ β)
    (hsq : ∀ M N : DZ, Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef TZ TU TT TT'
      mt.hom mt'.hom mu.hom mu'.hom M N)
    (W : DU) (A : DZ) (hβW : IsIso (β.app W)) (hβT : IsIso (β.app (TU.obj (W, Pu.obj A))))
    (hπ : IsIso (projectionMap Pu' TT TT' mu' adju' (Pt'.obj W) (Pt.obj A))) :
    IsIso (Pt.map (projectionMap Pu TZ TU mu adju W A)) := by
  refine isIso_map_projectionMap_of_baseChange adju adju' Pt Pt' σ TZ TU TT TT' mu mu' mt mt' β
    (unit_comp_map_eq_of_eq_mate adju adju' Pt Pt' σ β hβ) (fun M N => ?_) W A
  subst e
  exact hsq M N

end BaseChange

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

end
