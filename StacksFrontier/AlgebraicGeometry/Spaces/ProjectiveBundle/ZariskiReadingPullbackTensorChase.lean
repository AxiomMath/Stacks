module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Monoidality of a base change read through restrictions

Two categorical pastes for the monoidality of the base change of the Zariski reading.  The first
reads a base change `P` of two readings `R ≅ Ei ⋙ r`, `R' ≅ Ei' ⋙ r'` through a comparison `c` of
the restrictions and a comparison `μ` of the `Ei`, and shows that `P` is monoidal for the tensor
comparisons of the readings once `c` and `μ` are.  The second shows that the mate of a monoidal
square of left adjoints through two equivalences is monoidal.

## Main results

* `CategoryTheory.Functor.tensor_baseChange_of_restriction`.
* `CategoryTheory.Functor.mate_tensor_of_counit`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

section TensorChase

variable {𝒩 𝒩' Et Et' 𝒵 𝒵' : Type*} [Category 𝒩] [Category 𝒩'] [Category Et] [Category Et']
  [Category 𝒵] [Category 𝒵']
  (T𝒩 : 𝒩 ⥤ 𝒩 ⥤ 𝒩) (T𝒩' : 𝒩' ⥤ 𝒩' ⥤ 𝒩') (TE : Et ⥤ Et ⥤ Et) (TE' : Et' ⥤ Et' ⥤ Et')
  (T𝒵 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (T𝒵' : 𝒵' ⥤ 𝒵' ⥤ 𝒵')
  {Ei : 𝒩 ⥤ Et} {Ei' : 𝒩' ⥤ Et'} {r : Et ⥤ 𝒵} {r' : Et' ⥤ 𝒵'} {R : 𝒩 ⥤ 𝒵} {R' : 𝒩' ⥤ 𝒵'}
  {τs : 𝒵 ⥤ 𝒵'} {gs : Et ⥤ Et'} {φs : 𝒩 ⥤ 𝒩'}
  (ι : ∀ X : 𝒩, r.obj (Ei.obj X) ≅ R.obj X) (ι' : ∀ X : 𝒩', r'.obj (Ei'.obj X) ≅ R'.obj X)

/-- Two successive whiskered maps of a bifunctor compose to the whiskered composite. -/
private theorem map_app_comp_map_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒞 ⥤ 𝒟)
    {A A' A'' X Y W : 𝒞} (f : A ⟶ A') (f' : A' ⟶ A'') (g : X ⟶ Y) (g' : Y ⟶ W) :
    (F.map f).app X ≫ (F.obj A').map g ≫ (F.map f').app Y ≫ (F.obj A'').map g' =
      (F.map (f ≫ f')).app X ≫ (F.obj A'').map (g ≫ g') := by
  simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

/-- **Monoidality of a base change read through two restrictions.**  A base change `P` of readings
`R ≅ Ei ⋙ r`, `R' ≅ Ei' ⋙ r'`, described through a comparison `c` of the restrictions and a
comparison `μ` of the `Ei`, is monoidal for the tensor comparisons `Z, Z'` of the readings as
soon as `c` is monoidal (`hZP`) and `μ` is (`hstar`). -/
theorem Functor.tensor_baseChange_of_restriction
    (hι' : ∀ {X Y : 𝒩'} (f : X ⟶ Y), r'.map (Ei'.map f) ≫ (ι' Y).hom = (ι' X).hom ≫ R'.map f)
    (N M : 𝒩)
    (P : ∀ X : 𝒩, τs.obj (R.obj X) ⟶ R'.obj (φs.obj X))
    (μ : ∀ X : 𝒩, gs.obj (Ei.obj X) ⟶ Ei'.obj (φs.obj X))
    (cN : τs.obj (r.obj (Ei.obj N)) ⟶ r'.obj (gs.obj (Ei.obj N)))
    (cM : τs.obj (r.obj (Ei.obj M)) ⟶ r'.obj (gs.obj (Ei.obj M)))
    (cNM : τs.obj (r.obj (Ei.obj ((T𝒩.obj N).obj M))) ⟶
      r'.obj (gs.obj (Ei.obj ((T𝒩.obj N).obj M))))
    (cT : τs.obj (r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))) ⟶
      r'.obj (gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))))
    (hFN : τs.map ((ι N).hom) ≫ P N = cN ≫ r'.map (μ N) ≫ (ι' (φs.obj N)).hom)
    (hFM : τs.map ((ι M).hom) ≫ P M = cM ≫ r'.map (μ M) ≫ (ι' (φs.obj M)).hom)
    (hFNM : τs.map ((ι ((T𝒩.obj N).obj M)).hom) ≫ P ((T𝒩.obj N).obj M) =
      cNM ≫ r'.map (μ ((T𝒩.obj N).obj M)) ≫ (ι' (φs.obj ((T𝒩.obj N).obj M))).hom)
    (J : Ei.obj ((T𝒩.obj N).obj M) ⟶ (TE.obj (Ei.obj N)).obj (Ei.obj M))
    (K : r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (T𝒵.obj (r.obj (Ei.obj N))).obj (r.obj (Ei.obj M)))
    (Z : R.obj ((T𝒩.obj N).obj M) ⟶ (T𝒵.obj (R.obj N)).obj (R.obj M))
    (hZ : Z = (ι _).inv ≫ r.map J ≫ K ≫
      ((T𝒵.map ((ι N).hom)).app _ ≫ (T𝒵.obj (R.obj N)).map ((ι M).hom)))
    (cφ : φs.obj ((T𝒩.obj N).obj M) ⟶ (T𝒩'.obj (φs.obj N)).obj (φs.obj M))
    (J' : Ei'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M)))
    (K' : ∀ A B : Et', r'.obj ((TE'.obj A).obj B) ⟶ (T𝒵'.obj (r'.obj A)).obj (r'.obj B))
    (hK' : ∀ {A A' B B' : Et'} (f : A ⟶ A') (g : B ⟶ B'),
      r'.map ((TE'.map f).app B ≫ (TE'.obj A').map g) ≫ K' A' B' =
        K' A B ≫ ((T𝒵'.map (r'.map f)).app _ ≫ (T𝒵'.obj (r'.obj A')).map (r'.map g)))
    (Z' : R'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (T𝒵'.obj (R'.obj (φs.obj N))).obj (R'.obj (φs.obj M)))
    (hZ' : Z' = (ι' _).inv ≫ r'.map J' ≫ K' _ _ ≫
      ((T𝒵'.map ((ι' (φs.obj N)).hom)).app _ ≫
        (T𝒵'.obj (R'.obj (φs.obj N))).map ((ι' (φs.obj M)).hom)))
    (I : ∀ X Y : 𝒵, τs.obj ((T𝒵.obj X).obj Y) ⟶ (T𝒵'.obj (τs.obj X)).obj (τs.obj Y))
    (hI : ∀ {X X' Y Y' : 𝒵} (f : X ⟶ X') (g : Y ⟶ Y'),
      τs.map ((T𝒵.map f).app Y ≫ (T𝒵.obj X').map g) ≫ I X' Y' =
        I X Y ≫ ((T𝒵'.map (τs.map f)).app _ ≫ (T𝒵'.obj (τs.obj X')).map (τs.map g)))
    (bc : gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M)))
    (hZP : τs.map K ≫ I _ _ ≫ ((T𝒵'.map cN).app _ ≫ (T𝒵'.obj _).map cM) =
      cT ≫ r'.map bc ≫ K' _ _)
    (hc : τs.map (r.map J) ≫ cT = cNM ≫ r'.map (gs.map J))
    (hstar : gs.map J ≫ bc ≫ ((TE'.map (μ N)).app _ ≫ (TE'.obj _).map (μ M)) =
      μ ((T𝒩.obj N).obj M) ≫ Ei'.map cφ ≫ J') :
    τs.map Z ≫ I (R.obj N) (R.obj M) ≫
        ((T𝒵'.map (P N)).app _ ≫ (T𝒵'.obj (R'.obj (φs.obj N))).map (P M)) =
      P ((T𝒩.obj N).obj M) ≫ R'.map cφ ≫ Z' := by
  have eP : ∀ (X : 𝒩) (c' : τs.obj (r.obj (Ei.obj X)) ⟶ r'.obj (gs.obj (Ei.obj X)))
      (_ : τs.map ((ι X).hom) ≫ P X = c' ≫ r'.map (μ X) ≫ (ι' (φs.obj X)).hom),
      P X = τs.map ((ι X).inv) ≫ c' ≫ r'.map (μ X) ≫ (ι' (φs.obj X)).hom := by
    intro X c' h
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  have e1 : ((T𝒵'.map (τs.map ((ι N).hom))).app _ ≫
      (T𝒵'.obj (τs.obj (R.obj N))).map (τs.map ((ι M).hom))) ≫
      ((T𝒵'.map (P N)).app _ ≫ (T𝒵'.obj (R'.obj (φs.obj N))).map (P M)) =
      ((T𝒵'.map cN).app _ ≫ (T𝒵'.obj _).map cM) ≫
        ((T𝒵'.map (r'.map (μ N))).app _ ≫ (T𝒵'.obj _).map (r'.map (μ M))) ≫
        ((T𝒵'.map ((ι' (φs.obj N)).hom)).app _ ≫
          (T𝒵'.obj (R'.obj (φs.obj N))).map ((ι' (φs.obj M)).hom)) := by
    simp only [Category.assoc]
    rw [map_app_comp_map_comp, hFN, hFM, ← map_app_comp_map_comp,
      ← map_app_comp_map_comp]
  have e2 := hK' (μ N) (μ M)
  have e3 : (ι' (φs.obj ((T𝒩.obj N).obj M))).hom ≫ R'.map cφ ≫ (ι' _).inv =
      r'.map (Ei'.map cφ) := by
    rw [← Category.assoc, ← hι', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hZ, hZ', eP _ _ hFNM]
  have hI2 := hI ((ι N).hom) ((ι M).hom)
  have hs := congrArg r'.map hstar
  simp only [Functor.map_comp, Category.assoc] at hI2 e1 hZP e2 e3 hc hs ⊢
  rw [reassoc_of% hI2, e1, reassoc_of% hZP, ← reassoc_of% e2, reassoc_of% hc,
    reassoc_of% e3, reassoc_of% hs]

end TensorChase

section MateTensor

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {gs : 𝒵 ⥤ 𝒴₁} {φs : 𝒴₂ ⥤ 𝒳} (F : 𝒵 ⥤ 𝒴₂) (G : 𝒴₂ ⥤ 𝒵) (F' : 𝒴₁ ⥤ 𝒳) (G' : 𝒳 ⥤ 𝒴₁)
  [F'.Faithful] (ε : ∀ X, F.obj (G.obj X) ⟶ X) (ε' : ∀ X, F'.obj (G'.obj X) ⟶ X) [∀ X, IsIso (ε' X)]
  (θ : ∀ A : 𝒵, F'.obj (gs.obj A) ⟶ φs.obj (F.obj A))
  (T𝒵 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (T₁ : 𝒴₁ ⥤ 𝒴₁ ⥤ 𝒴₁) (T₂ : 𝒴₂ ⥤ 𝒴₂ ⥤ 𝒴₂) (T𝒳 : 𝒳 ⥤ 𝒳 ⥤ 𝒳)

/-- **The mate of a monoidal square through two equivalences is monoidal.**  Let `μ_X` be maps
`gs (E⁻¹ X) ⟶ E'⁻¹ (φs X)` transposed along `E'` to `θ` followed by `φs` of the counit, `L, L'`
comparisons of `E, E'` with tensor products, `J, J'` the corresponding comparisons of the
inverses (transposed to the counit), `cφ` a natural comparison of `φs` with tensor products and
`bc` a comparison of `gs`, with `θ` monoidal (`hRS`).  Then `μ` is monoidal. -/
theorem Functor.mate_tensor_of_counit
    (hε' : ∀ {X Y : 𝒳} (f : X ⟶ Y), F'.map (G'.map f) ≫ ε' Y = ε' X ≫ f) (N M : 𝒴₂)
    (μ : ∀ X : 𝒴₂, gs.obj (G.obj X) ⟶ G'.obj (φs.obj X))
    (hμ : ∀ X, F'.map (μ X) ≫ ε' (φs.obj X) =
      θ (G.obj X) ≫ φs.map (ε X))
    (L : F.obj ((T𝒵.obj (G.obj N)).obj (G.obj M)) ⟶
      (T₂.obj (F.obj (G.obj N))).obj (F.obj (G.obj M)))
    (J : G.obj ((T₂.obj N).obj M) ⟶ (T𝒵.obj (G.obj N)).obj (G.obj M))
    (hJ : F.map J ≫ L ≫ ((T₂.map (ε N)).app _ ≫
      (T₂.obj N).map (ε M)) = ε ((T₂.obj N).obj M))
    (L' : ∀ A B : 𝒴₁, F'.obj ((T₁.obj A).obj B) ⟶
      (T𝒳.obj (F'.obj A)).obj (F'.obj B))
    (hL' : ∀ {A A' B B' : 𝒴₁} (f : A ⟶ A') (g : B ⟶ B'),
      F'.map ((T₁.map f).app B ≫ (T₁.obj A').map g) ≫ L' A' B' =
        L' A B ≫ ((T𝒳.map (F'.map f)).app _ ≫
          (T𝒳.obj (F'.obj A')).map (F'.map g)))
    (hL'i : IsIso (L' (G'.obj (φs.obj N)) (G'.obj (φs.obj M))))
    (J' : G'.obj ((T𝒳.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (T₁.obj (G'.obj (φs.obj N))).obj (G'.obj (φs.obj M)))
    (hJ' : F'.map J' ≫ L' _ _ ≫ ((T𝒳.map (ε' (φs.obj N))).app _ ≫
      (T𝒳.obj (φs.obj N)).map (ε' (φs.obj M))) =
        ε' ((T𝒳.obj (φs.obj N)).obj (φs.obj M)))
    (cφ : ∀ X Y : 𝒴₂, φs.obj ((T₂.obj X).obj Y) ⟶ (T𝒳.obj (φs.obj X)).obj (φs.obj Y))
    (hcφ : ∀ {X X' Y Y' : 𝒴₂} (f : X ⟶ X') (g : Y ⟶ Y'),
      φs.map ((T₂.map f).app Y ≫ (T₂.obj X').map g) ≫ cφ X' Y' =
        cφ X Y ≫ ((T𝒳.map (φs.map f)).app _ ≫ (T𝒳.obj (φs.obj X')).map (φs.map g)))
    (bc : gs.obj ((T𝒵.obj (G.obj N)).obj (G.obj M)) ⟶
      (T₁.obj (gs.obj (G.obj N))).obj (gs.obj (G.obj M)))
    (hRS : F'.map bc ≫ L' _ _ ≫ ((T𝒳.map (θ (G.obj N))).app _ ≫
      (T𝒳.obj _).map (θ (G.obj M))) =
        θ _ ≫ φs.map L ≫ cφ _ _)
    (hθ : F'.map (gs.map J) ≫ θ _ = θ _ ≫ φs.map (F.map J)) :
    gs.map J ≫ bc ≫ ((T₁.map (μ N)).app _ ≫ (T₁.obj _).map (μ M)) =
      μ ((T₂.obj N).obj M) ≫ G'.map (cφ N M) ≫ J' := by
  have := hL'i
  apply F'.map_injective
  rw [← cancel_mono (L' _ _ ≫ ((T𝒳.map (ε' (φs.obj N))).app _ ≫
      (T𝒳.obj (φs.obj N)).map (ε' (φs.obj M))))]
  have hn := hε' (cφ N M)
  have hc2 := hcφ (ε N) (ε M)
  have hL2 := hL' (μ N) (μ M)
  have hRHS : F'.map (μ ((T₂.obj N).obj M) ≫ G'.map (cφ N M) ≫ J') ≫
      L' _ _ ≫ ((T𝒳.map (ε' (φs.obj N))).app _ ≫
        (T𝒳.obj (φs.obj N)).map (ε' (φs.obj M))) =
      θ _ ≫ φs.map (ε ((T₂.obj N).obj M)) ≫ cφ N M := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hJ', hn, ← Category.assoc, hμ, Category.assoc]
  have hLHS : F'.map (gs.map J ≫ bc ≫ ((T₁.map (μ N)).app _ ≫ (T₁.obj _).map (μ M))) ≫
      L' _ _ ≫ ((T𝒳.map (ε' (φs.obj N))).app _ ≫
        (T𝒳.obj (φs.obj N)).map (ε' (φs.obj M))) =
      θ _ ≫ φs.map (F.map J ≫ L ≫ ((T₂.map (ε N)).app _ ≫
        (T₂.obj N).map (ε M))) ≫ cφ N M := by
    simp only [Functor.map_comp, Category.assoc] at hL2 hRS hc2 ⊢
    rw [reassoc_of% hL2, map_app_comp_map_comp, hμ, hμ, ← map_app_comp_map_comp,
      reassoc_of% hRS, ← hc2, reassoc_of% hθ]
  rw [hLHS, hRHS, hJ]

end MateTensor

end CategoryTheory
