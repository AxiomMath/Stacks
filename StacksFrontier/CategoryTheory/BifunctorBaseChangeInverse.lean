module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.NatIso

/-!
# Base change of tensor products and of tensor inverses, for bifunctors

Let `ρ : 𝒳 ⥤ 𝒞₀`, `ρ' : 𝒳 ⥤ 𝒞₁` and `P : 𝒞₀ ⥤ 𝒞₁` be functors, the three categories carrying
tensor bifunctors `⊗`, and let `c : ρ' ≅ ρ ⋙ P` be a natural identification.  Suppose `ρ`, `ρ'`
and `P` are compatible with the tensor products through comparisons `μ`, `μ'`, `κ`, and that `c`
is monoidal at a pair `(A, B)`:

`c_{A ⊗ B} ≫ P(μ_{A,B}) ≫ κ = μ'_{A,B} ≫ (c_A ⊗ c_B)`.

This file records the two formal consequences used for the conormal source `Ker(q) ⊗ ℒ^{⊗ -1}`
of Stacks 0B3V and 0B4I.

* A tensor product of two identifications, each compatible with `c` and with given base-change
  isomorphisms, is compatible with `c` and with the tensor product of the base-change
  isomorphisms (`CategoryTheory.Functor.bifunctor_baseChange_tensor`).
* **The base change of a tensor inverse is forced by the evaluation.**  Let `e : Λ ⊗ L ≅ 𝟙` be a
  trivialisation, `i : ρΛ ≅ Λ₀` and `i' : ρ'Λ ≅ Λ₁` identifications with tensor inverses
  characterised by the pairings `ρΛ ⊗ ρL ≅ ρ(Λ ⊗ L) ≅ ρ 𝟙 ≅ 𝟙`, and `b : PΛ₀ ≅ Λ₁` a base-change
  isomorphism characterised by the pullback of the evaluation.  If `c` is monoidal at `(Λ, L)`
  and compatible with the identifications of the units, then
  `c_Λ ≫ P(i) ≫ b = i'` (`CategoryTheory.Functor.bifunctor_baseChange_inverse`).  Nothing is
  unfolded: the identity is the uniqueness of a tensor inverse with a prescribed evaluation.

## Main results

* `CategoryTheory.Functor.bifunctor_map_app_comp_obj_map`: functoriality of a bifunctor in both
  variables at once.
* `CategoryTheory.Functor.bifunctor_baseChange_tensor`.
* `CategoryTheory.Functor.bifunctor_tensor_paste`: a monoidality square pasted with two
  naturality squares, and `CategoryTheory.Functor.bifunctor_tensor_paste_of_map`, the same with
  the image of `m` under the middle functor given as a morphism.
* `CategoryTheory.Functor.bifunctor_baseChange_inverse`, and
  `CategoryTheory.Functor.bifunctor_baseChange_inverse_iso` for identifications given as
  isomorphisms.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {𝒳 𝒞₀ 𝒞₁ : Type*} [Category 𝒳] [Category 𝒞₀] [Category 𝒞₁]

/-- **A bifunctor is functorial in both variables at once.** -/
theorem bifunctor_map_app_comp_obj_map (F : 𝒞₁ ⥤ 𝒞₁ ⥤ 𝒞₁) {A A' A'' B B' B'' : 𝒞₁}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    ((F.map f).app B ≫ (F.obj A').map g) ≫ ((F.map f').app B' ≫ (F.obj A'').map g') =
      (F.map (f ≫ f')).app B ≫ (F.obj A'').map (g ≫ g') := by
  simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

variable (Fx : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (F₀ : 𝒞₀ ⥤ 𝒞₀ ⥤ 𝒞₀) (F₁ : 𝒞₁ ⥤ 𝒞₁ ⥤ 𝒞₁)
  (ρ : 𝒳 ⥤ 𝒞₀) (ρ' : 𝒳 ⥤ 𝒞₁) (P : 𝒞₀ ⥤ 𝒞₁)

/-- **Base change of a tensor product of two identifications.**  If `c` is monoidal at `(A, B)`
and the identifications `k : ρA ≅ A₀`, `i : ρB ≅ B₀` are compatible with `c` and with base-change
isomorphisms `kb`, `ib`, then the tensor product `μ ≫ (k ⊗ i)` is compatible with `c` and with
`κ ≫ (kb ⊗ ib)`. -/
theorem bifunctor_baseChange_tensor (A B : 𝒳) {A₀ B₀ : 𝒞₀} {A₁ B₁ : 𝒞₁}
    (cA : ρ'.obj A ⟶ P.obj (ρ.obj A)) (cB : ρ'.obj B ⟶ P.obj (ρ.obj B))
    (cAB : ρ'.obj ((Fx.obj A).obj B) ⟶ P.obj (ρ.obj ((Fx.obj A).obj B)))
    (μ : ρ.obj ((Fx.obj A).obj B) ⟶ (F₀.obj (ρ.obj A)).obj (ρ.obj B))
    (μ' : ρ'.obj ((Fx.obj A).obj B) ⟶ (F₁.obj (ρ'.obj A)).obj (ρ'.obj B))
    (κ : ∀ X Y : 𝒞₀, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y))
    (hκ : ∀ {X X' Y Y' : 𝒞₀} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map ((F₀.map f).app Y ≫ (F₀.obj X').map g) ≫ κ X' Y' =
        κ X Y ≫ ((F₁.map (P.map f)).app (P.obj Y) ≫ (F₁.obj (P.obj X')).map (P.map g)))
    (hT : cAB ≫ P.map μ ≫ κ (ρ.obj A) (ρ.obj B) =
      μ' ≫ ((F₁.map cA).app (ρ'.obj B) ≫ (F₁.obj (P.obj (ρ.obj A))).map cB))
    (k : ρ.obj A ⟶ A₀) (i : ρ.obj B ⟶ B₀) (k' : ρ'.obj A ⟶ A₁) (i' : ρ'.obj B ⟶ B₁)
    (kb : P.obj A₀ ⟶ A₁) (ib : P.obj B₀ ⟶ B₁)
    (hk : cA ≫ P.map k ≫ kb = k') (hi : cB ≫ P.map i ≫ ib = i') :
    cAB ≫ P.map (μ ≫ ((F₀.map k).app (ρ.obj B) ≫ (F₀.obj A₀).map i)) ≫
        κ A₀ B₀ ≫ ((F₁.map kb).app (P.obj B₀) ≫ (F₁.obj A₁).map ib) =
      μ' ≫ ((F₁.map k').app (ρ'.obj B) ≫ (F₁.obj A₁).map i') := by
  rw [P.map_comp, Category.assoc, reassoc_of% (hκ k i), reassoc_of% hT, ← hk, ← hi]
  congr 1
  rw [← bifunctor_map_app_comp_obj_map, ← bifunctor_map_app_comp_obj_map]
  simp only [Category.assoc]

/-- **The base change of a tensor inverse is forced by the evaluation.**

Let `e : Λ ⊗ L ≅ 𝟙` on `𝒳`, `u : ρ𝟙 ≅ 𝟙₀`, `u' : ρ'𝟙 ≅ 𝟙₁`, `ν : P 𝟙₀ ⟶ 𝟙₁`, and let
`i : ρΛ ⟶ Λ₀`, `i' : ρ'Λ ⟶ Λ₁` be characterised by `(i ⊗ 1) ≫ ev₀ = μ⁻¹ ≫ ρ(e) ≫ u` and
`(i' ⊗ 1) ≫ ev₁ = μ'⁻¹ ≫ ρ'(e) ≫ u'`, and `b : PΛ₀ ⟶ Λ₁` by
`κ ≫ (b ⊗ c_L⁻¹) ≫ ev₁ = P(ev₀) ≫ ν`.  If `c` is monoidal at `(Λ, L)`, compatible with the
identifications of the units, and maps into `Λ₁` are determined by their tensor product with
`ρ'L` followed by `ev₁`, then `c_Λ ≫ P(i) ≫ b = i'`. -/
theorem bifunctor_baseChange_inverse
    (Λ L : 𝒳) {Λ₀ : 𝒞₀} {Λ₁ : 𝒞₁} (Ux : 𝒳) (U₀ : 𝒞₀) (U₁ : 𝒞₁)
    (cΛ : ρ'.obj Λ ⟶ P.obj (ρ.obj Λ)) (cL : ρ'.obj L ≅ P.obj (ρ.obj L))
    (cΛL : ρ'.obj ((Fx.obj Λ).obj L) ⟶ P.obj (ρ.obj ((Fx.obj Λ).obj L)))
    (cU : ρ'.obj Ux ⟶ P.obj (ρ.obj Ux))
    (μ : ρ.obj ((Fx.obj Λ).obj L) ≅ (F₀.obj (ρ.obj Λ)).obj (ρ.obj L))
    (μ' : ρ'.obj ((Fx.obj Λ).obj L) ≅ (F₁.obj (ρ'.obj Λ)).obj (ρ'.obj L))
    (κ : ∀ X Y : 𝒞₀, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y))
    (hκ : ∀ {X X' Y Y' : 𝒞₀} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map ((F₀.map f).app Y ≫ (F₀.obj X').map g) ≫ κ X' Y' =
        κ X Y ≫ ((F₁.map (P.map f)).app (P.obj Y) ≫ (F₁.obj (P.obj X')).map (P.map g)))
    (hT : cΛL ≫ P.map μ.hom ≫ κ (ρ.obj Λ) (ρ.obj L) =
      μ'.hom ≫ ((F₁.map cΛ).app (ρ'.obj L) ≫ (F₁.obj (P.obj (ρ.obj Λ))).map cL.hom))
    (e : (Fx.obj Λ).obj L ⟶ Ux) (hc : ρ'.map e ≫ cU = cΛL ≫ P.map (ρ.map e)) (u : ρ.obj Ux ⟶ U₀)
    (u' : ρ'.obj Ux ⟶ U₁) (ν : P.obj U₀ ⟶ U₁)
    (hU : cU ≫ P.map u ≫ ν = u')
    (i : ρ.obj Λ ⟶ Λ₀) (i' : ρ'.obj Λ ⟶ Λ₁) (b : P.obj Λ₀ ⟶ Λ₁)
    (ev₀ : (F₀.obj Λ₀).obj (ρ.obj L) ⟶ U₀) (ev₁ : (F₁.obj Λ₁).obj (ρ'.obj L) ⟶ U₁)
    (hi : (F₀.map i).app (ρ.obj L) ≫ ev₀ = μ.inv ≫ ρ.map e ≫ u)
    (hi' : (F₁.map i').app (ρ'.obj L) ≫ ev₁ = μ'.inv ≫ ρ'.map e ≫ u')
    (hb : κ Λ₀ (ρ.obj L) ≫ ((F₁.map b).app (P.obj (ρ.obj L)) ≫ (F₁.obj Λ₁).map cL.inv) ≫
      ev₁ = P.map ev₀ ≫ ν)
    (huniq : ∀ α β : ρ'.obj Λ ⟶ Λ₁,
      (F₁.map α).app (ρ'.obj L) ≫ ev₁ = (F₁.map β).app (ρ'.obj L) ≫ ev₁ → α = β) :
    cΛ ≫ P.map i ≫ b = i' := by
  refine huniq _ _ ?_
  rw [hi']
  -- `(α ⊗ 1) = (c_Λ ⊗ c_L) ≫ (P i ⊗ 1) ≫ (b ⊗ c_L⁻¹)`
  have hsplit : (F₁.map (cΛ ≫ P.map i ≫ b)).app (ρ'.obj L) =
      ((F₁.map cΛ).app (ρ'.obj L) ≫ (F₁.obj (P.obj (ρ.obj Λ))).map cL.hom) ≫
        ((F₁.map (P.map i)).app (P.obj (ρ.obj L)) ≫ (F₁.obj (P.obj Λ₀)).map (P.map (𝟙 _))) ≫
        ((F₁.map b).app (P.obj (ρ.obj L)) ≫ (F₁.obj Λ₁).map cL.inv) := by
    rw [bifunctor_map_app_comp_obj_map, bifunctor_map_app_comp_obj_map]
    simp
  rw [hsplit]
  calc _ = μ'.inv ≫ (cΛL ≫ P.map μ.hom ≫ κ (ρ.obj Λ) (ρ.obj L)) ≫
        ((F₁.map (P.map i)).app (P.obj (ρ.obj L)) ≫
          (F₁.obj (P.obj Λ₀)).map (P.map (𝟙 _))) ≫
        ((F₁.map b).app (P.obj (ρ.obj L)) ≫ (F₁.obj Λ₁).map cL.inv) ≫ ev₁ := by
          rw [hT]; simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = μ'.inv ≫ cΛL ≫
        P.map (μ.hom ≫ (F₀.map i).app (ρ.obj L) ≫ ev₀) ≫ ν := by
          simp only [Category.assoc] at hb ⊢
          rw [← reassoc_of% (hκ i (𝟙 (ρ.obj L))), hb]
          simp only [Functor.map_id, Category.comp_id, Functor.map_comp, Category.assoc]
    _ = μ'.inv ≫ ρ'.map e ≫ u' := by
          rw [hi, Iso.hom_inv_id_assoc, P.map_comp, ← hU, Category.assoc, reassoc_of% hc]

/-- **The base change of a tensor inverse is forced by the evaluation**, for identifications
given as isomorphisms with evaluations stated between isomorphisms
(`CategoryTheory.Functor.bifunctor_baseChange_inverse`): if `c` is monoidal at `(Λ, L)`,
compatible with the identifications of the units, and maps into `Λ₁` are determined by their
tensor product with `ρ'L` followed by `ev₁`, then `c_Λ ≪≫ P(i) ≪≫ b = i'`. -/
theorem bifunctor_baseChange_inverse_iso
    (Λ L : 𝒳) {Λ₀ : 𝒞₀} {Λ₁ : 𝒞₁} (Ux : 𝒳) (U₀ : 𝒞₀) (U₁ : 𝒞₁)
    (cΛ : ρ'.obj Λ ≅ P.obj (ρ.obj Λ)) (cL : ρ'.obj L ≅ P.obj (ρ.obj L))
    (cΛL : ρ'.obj ((Fx.obj Λ).obj L) ⟶ P.obj (ρ.obj ((Fx.obj Λ).obj L)))
    (cU : ρ'.obj Ux ⟶ P.obj (ρ.obj Ux))
    (μ : ρ.obj ((Fx.obj Λ).obj L) ≅ (F₀.obj (ρ.obj Λ)).obj (ρ.obj L))
    (μ' : ρ'.obj ((Fx.obj Λ).obj L) ≅ (F₁.obj (ρ'.obj Λ)).obj (ρ'.obj L))
    (κ : ∀ X Y : 𝒞₀, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y))
    (hκ : ∀ {X X' Y Y' : 𝒞₀} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map ((F₀.map f).app Y ≫ (F₀.obj X').map g) ≫ κ X' Y' =
        κ X Y ≫ ((F₁.map (P.map f)).app (P.obj Y) ≫ (F₁.obj (P.obj X')).map (P.map g)))
    (hT : cΛL ≫ P.map μ.hom ≫ κ (ρ.obj Λ) (ρ.obj L) =
      μ'.hom ≫ ((F₁.map cΛ.hom).app (ρ'.obj L) ≫ (F₁.obj (P.obj (ρ.obj Λ))).map cL.hom))
    (e : (Fx.obj Λ).obj L ≅ Ux) (hc : ρ'.map e.hom ≫ cU = cΛL ≫ P.map (ρ.map e.hom))
    (u : ρ.obj Ux ≅ U₀) (u' : ρ'.obj Ux ≅ U₁) (ν : P.obj U₀ ⟶ U₁)
    (hU : cU ≫ P.map u.hom ≫ ν = u'.hom)
    (i : ρ.obj Λ ≅ Λ₀) (i' : ρ'.obj Λ ≅ Λ₁) (b : P.obj Λ₀ ≅ Λ₁)
    (ev₀ : (F₀.obj Λ₀).obj (ρ.obj L) ≅ U₀) (ev₁ : (F₁.obj Λ₁).obj (ρ'.obj L) ≅ U₁)
    (hi : (F₀.mapIso i).app (ρ.obj L) ≪≫ ev₀ = μ.symm ≪≫ ρ.mapIso e ≪≫ u)
    (hi' : (F₁.mapIso i').app (ρ'.obj L) ≪≫ ev₁ = μ'.symm ≪≫ ρ'.mapIso e ≪≫ u')
    (hb : κ Λ₀ (ρ.obj L) ≫ ((F₁.map b.hom).app (P.obj (ρ.obj L)) ≫
      (F₁.obj Λ₁).map cL.inv) ≫ ev₁.hom = P.map ev₀.hom ≫ ν)
    (huniq : ∀ α β : ρ'.obj Λ ⟶ Λ₁,
      (F₁.map α).app (ρ'.obj L) ≫ ev₁.hom = (F₁.map β).app (ρ'.obj L) ≫ ev₁.hom → α = β) :
    cΛ ≪≫ P.mapIso i ≪≫ b = i' := by
  have hi₀ : (F₀.map i.hom).app (ρ.obj L) ≫ ev₀.hom = μ.inv ≫ ρ.map e.hom ≫ u.hom := by
    simpa using congrArg Iso.hom hi
  have hi₁ : (F₁.map i'.hom).app (ρ'.obj L) ≫ ev₁.hom = μ'.inv ≫ ρ'.map e.hom ≫ u'.hom := by
    simpa using congrArg Iso.hom hi'
  exact Iso.ext (bifunctor_baseChange_inverse Fx F₀ F₁ ρ ρ' P Λ L Ux U₀ U₁ cΛ.hom cL cΛL cU μ μ'
    κ hκ hT e.hom hc u.hom u'.hom ν hU i.hom i'.hom b.hom ev₀.hom ev₁.hom hi₀ hi₁ hb huniq)

/-- The core of the pasting lemmas below, in terms of the images of the morphisms involved. -/
private theorem bifunctor_tensor_paste_aux {ℬ : Type*} [Category ℬ] (F : ℬ ⥤ ℬ ⥤ ℬ)
    {A B C X X' Q E E' Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ} {pm : A ⟶ B} {pZ : B ⟶ C}
    {κ : C ⟶ (F.obj Y₁).obj Y₂} {a : Y₁ ⟶ W₁} {b : Y₂ ⟶ W₂} {a' : W₁ ⟶ V₁} {b' : W₂ ⟶ V₂}
    {θ' : B ⟶ X'} {θ : A ⟶ X} {rg : X ⟶ X'} {rφ : X' ⟶ E} {Z' : E ⟶ (F.obj W₁).obj W₂}
    {rc : X ⟶ Q} {rm' : Q ⟶ E'} {rd : E ⟶ E'} {Z'' : E' ⟶ (F.obj V₁).obj V₂}
    (t : pZ ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = θ' ≫ rφ ≫ Z')
    (n : pm ≫ θ' = θ ≫ rg) (hc : rc ≫ rm' = rg ≫ rφ ≫ rd)
    (n' : rd ≫ Z'' = Z' ≫ ((F.map a').app W₂ ≫ (F.obj V₁).map b')) :
    (pm ≫ pZ) ≫ κ ≫ ((F.map (a ≫ a')).app Y₂ ≫ (F.obj V₁).map (b ≫ b')) =
      θ ≫ rc ≫ rm' ≫ Z'' := by
  rw [← bifunctor_map_app_comp_obj_map]
  simp only [Category.assoc]
  rw [reassoc_of% t, ← Category.assoc, n, reassoc_of% hc]
  simp only [Category.assoc, n']

/-- **Pasting a monoidality square with two naturality squares**, the shape of the monoidality of
the identification of two point readings: if `P(Z) ≫ κ ≫ (a ⊗ b) = θ' ≫ R'(m_φ) ≫ Z'`,
`P(R(m)) ≫ θ' = θ ≫ R'(G(m))`, `c ≫ m' = G(m) ≫ m_φ ≫ d` and `R'(d) ≫ Z'' = Z' ≫ (a' ⊗ b')`,
then `P(R(m) ≫ Z) ≫ κ ≫ ((a ≫ a') ⊗ (b ≫ b')) = θ ≫ R'(c) ≫ R'(m') ≫ Z''`. -/
theorem bifunctor_tensor_paste {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ) (G : 𝒟 ⥤ 𝒜) (F : ℬ ⥤ ℬ ⥤ ℬ)
    {D D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ} {E' E'' Ex : 𝒜}
    (m : D ⟶ D') (Z : R.obj D' ⟶ C') (κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂) (a : Y₁ ⟶ W₁)
    (b : Y₂ ⟶ W₂) (θ' : P.obj (R.obj D') ⟶ R'.obj (G.obj D')) (mφ : G.obj D' ⟶ E')
    (Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂) (θ : P.obj (R.obj D) ⟶ R'.obj (G.obj D))
    (c : G.obj D ⟶ Ex) (m' : Ex ⟶ E'') (d : E' ⟶ E'') (a' : W₁ ⟶ V₁) (b' : W₂ ⟶ V₂)
    (Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂)
    (t : P.map Z ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = θ' ≫ R'.map mφ ≫ Z')
    (n : P.map (R.map m) ≫ θ' = θ ≫ R'.map (G.map m))
    (hc : c ≫ m' = G.map m ≫ mφ ≫ d)
    (n' : R'.map d ≫ Z'' = Z' ≫ ((F.map a').app W₂ ≫ (F.obj V₁).map b')) :
    P.map (R.map m ≫ Z) ≫ κ ≫ ((F.map (a ≫ a')).app Y₂ ≫ (F.obj V₁).map (b ≫ b')) =
      θ ≫ R'.map c ≫ R'.map m' ≫ Z'' := by
  rw [P.map_comp]
  exact bifunctor_tensor_paste_aux F t n (by simp only [← Functor.map_comp, hc]) n'

/-- `CategoryTheory.Functor.bifunctor_tensor_paste` with the image `gm` of `m` under the middle
functor given as a morphism, read off the naturality square `n`. -/
theorem bifunctor_tensor_paste_of_map {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ) (F : ℬ ⥤ ℬ ⥤ ℬ)
    {D D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ} {GD GD' E' E'' Ex : 𝒜}
    (m : D ⟶ D') (Z : R.obj D' ⟶ C') (κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂) (a : Y₁ ⟶ W₁)
    (b : Y₂ ⟶ W₂) (θ' : P.obj (R.obj D') ⟶ R'.obj GD') (gm : GD ⟶ GD') (mφ : GD' ⟶ E')
    (Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂) (θ : P.obj (R.obj D) ⟶ R'.obj GD)
    (c : GD ⟶ Ex) (m' : Ex ⟶ E'') (d : E' ⟶ E'') (a' : W₁ ⟶ V₁) (b' : W₂ ⟶ V₂)
    (Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂)
    (t : P.map Z ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = θ' ≫ R'.map mφ ≫ Z')
    (n : P.map (R.map m) ≫ θ' = θ ≫ R'.map gm)
    (hc : c ≫ m' = gm ≫ mφ ≫ d)
    (n' : R'.map d ≫ Z'' = Z' ≫ ((F.map a').app W₂ ≫ (F.obj V₁).map b')) :
    P.map (R.map m ≫ Z) ≫ κ ≫ ((F.map (a ≫ a')).app Y₂ ≫ (F.obj V₁).map (b ≫ b')) =
      θ ≫ R'.map c ≫ R'.map m' ≫ Z'' := by
  rw [P.map_comp]
  exact bifunctor_tensor_paste_aux F t n (by simp only [← Functor.map_comp, hc]) n'

/-- The paste of `CategoryTheory.Functor.bifunctor_tensor_paste_of_map`, with the middle square
`hc` given after applying `R'`. -/
theorem bifunctor_tensor_paste_of_map_map {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ) (F : ℬ ⥤ ℬ ⥤ ℬ)
    {D D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ} {GD GD' E' E'' Ex : 𝒜}
    (m : D ⟶ D') (Z : R.obj D' ⟶ C') (κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂) (a : Y₁ ⟶ W₁)
    (b : Y₂ ⟶ W₂) (θ' : P.obj (R.obj D') ⟶ R'.obj GD') (gm : GD ⟶ GD') (mφ : GD' ⟶ E')
    (Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂) (θ : P.obj (R.obj D) ⟶ R'.obj GD)
    (c : GD ⟶ Ex) (m' : Ex ⟶ E'') (d : E' ⟶ E'') (a' : W₁ ⟶ V₁) (b' : W₂ ⟶ V₂)
    (Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂)
    (t : P.map Z ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = θ' ≫ R'.map mφ ≫ Z')
    (n : P.map (R.map m) ≫ θ' = θ ≫ R'.map gm)
    (hc : R'.map c ≫ R'.map m' = R'.map gm ≫ R'.map mφ ≫ R'.map d)
    (n' : R'.map d ≫ Z'' = Z' ≫ ((F.map a').app W₂ ≫ (F.obj V₁).map b')) :
    P.map (R.map m ≫ Z) ≫ κ ≫ ((F.map (a ≫ a')).app Y₂ ≫ (F.obj V₁).map (b ≫ b')) =
      θ ≫ R'.map c ≫ R'.map m' ≫ Z'' := by
  rw [P.map_comp]
  exact bifunctor_tensor_paste_aux F t n hc n'

end CategoryTheory.Functor

end
