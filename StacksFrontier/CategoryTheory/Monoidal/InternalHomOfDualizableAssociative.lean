module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable

/-!
# Internal Homs out of a dualizable object along an associative tensor comparison

`StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable` shows that a *monoidal* functor
`P : C ⥤ D` carries an internal Hom out of a dualizable object `K` to an internal Hom out of
`P K`. This file proves the same conclusion under weaker hypotheses on `P`: a natural
isomorphism `m : P(A ⊗ B) ≅ P A ⊗ P B` compatible with the associativity constraints, and an
arbitrary isomorphism `P 𝟙 ≅ 𝟙`, with no compatibility of the two with the unit constraints.

The point is that the unit compatibility is not needed for the conclusion. Read through `m` and
`P 𝟙 ≅ 𝟙`, the coevaluation and evaluation of `K ⊣ K'` give maps
`η' : 𝟙 ⟶ P K ⊗ P K'` and `ε' : P K' ⊗ P K ⟶ 𝟙` whose two zigzag composites need not be
identities, but are isomorphisms (by the associativity of `m` they are `P` of the zigzag
identities of `K ⊣ K'` conjugated by isomorphisms). And an object `X` carrying `η`, `ε` with
invertible zigzag composites already represents `T ⊗ X ⟶ L` by `T ⟶ L ⊗ Y`
(`CategoryTheory.MonoidalCategory.tensorHomBijective_of_isIso_zigzag`): the two composites of
the transposition maps are composition with the two zigzags.

This is used for the comparison `g⁻¹ RHom(K, M) ⟶ RHom(g⁻¹K, g⁻¹M)` of Stacks 08JF, whose
tensor comparison is that of Stacks 07A4, known to be compatible with the associativity
constraints but not, in this development, with the unit constraints.

## Main results

* `CategoryTheory.MonoidalCategory.tensorHomBijective_of_isIso_zigzag`: `η`, `ε` with invertible
  zigzag composites make `L ⊗ Y` an internal Hom out of `X`.
* `CategoryTheory.MonoidalCategory.tensorHomBijective_map_of_associative`: an associative tensor
  comparison carries an internal Hom out of a dualizable object to an internal Hom.
* `CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map_of_associative`: the
  comparison morphism with internal Homs out of a dualizable object is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

section Zigzag

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- The transposition `T ⊗ X ⟶ L` to `T ⟶ L ⊗ Y` along `η : 𝟙 ⟶ X ⊗ Y`, followed by the
transposition back along `ε : Y ⊗ X ⟶ 𝟙`, is composition with the second zigzag. -/
theorem zigzag_transpose_transpose {X Y : D} (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    {L T : D} (g : T ⟶ L ⊗ Y) :
    (ρ_ T).inv ≫ T ◁ η ≫ (α_ T X Y).inv ≫
        (g ▷ X ≫ (α_ L Y X).hom ≫ L ◁ ε ≫ (ρ_ L).hom) ▷ Y =
      g ≫ L ◁ ((ρ_ Y).inv ≫ Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom) := by
  have h₁ : (ρ_ T).inv ≫ T ◁ η ≫ (α_ T X Y).inv ≫ (g ▷ X) ▷ Y =
      g ≫ (ρ_ (L ⊗ Y)).inv ≫ (L ⊗ Y) ◁ η ≫ (α_ (L ⊗ Y) X Y).inv := by
    rw [← associator_inv_naturality_left, whisker_exchange_assoc,
      ← rightUnitor_inv_naturality_assoc]
  simp only [comp_whiskerRight, ← Category.assoc] at h₁ ⊢
  rw [h₁]
  simp only [Category.assoc]
  congr 1
  monoidal

/-- The transposition `T ⟶ L ⊗ Y` to `T ⊗ X ⟶ L` along `ε : Y ⊗ X ⟶ 𝟙`, after the
transposition along `η : 𝟙 ⟶ X ⊗ Y`, is precomposition with the first zigzag. -/
theorem zigzag_transpose_transpose' {X Y : D} (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    {L T : D} (f : T ⊗ X ⟶ L) :
    ((ρ_ T).inv ≫ T ◁ η ≫ (α_ T X Y).inv ≫ f ▷ Y) ▷ X ≫ (α_ L Y X).hom ≫ L ◁ ε ≫
        (ρ_ L).hom =
      T ◁ ((λ_ X).inv ≫ η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom) ≫ f := by
  have h₁ : (f ▷ Y) ▷ X ≫ (α_ L Y X).hom ≫ L ◁ ε ≫ (ρ_ L).hom =
      (α_ (T ⊗ X) Y X).hom ≫ (T ⊗ X) ◁ ε ≫ (ρ_ (T ⊗ X)).hom ≫ f := by
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [comp_whiskerRight, Category.assoc]
  rw [h₁]
  simp only [← Category.assoc]
  congr 1
  monoidal

/-- **An object with a pairing whose zigzags are invertible represents maps out of a tensor
product.** If `η : 𝟙 ⟶ X ⊗ Y` and `ε : Y ⊗ X ⟶ 𝟙` have invertible zigzag composites (they need
not be identities), then for every `L` the object `L ⊗ Y`, with the evaluation built from `ε`,
is an internal Hom from `X` to `L`. -/
theorem tensorHomBijective_of_isIso_zigzag {X Y : D} (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    (h₁ : IsIso ((λ_ X).inv ≫ η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom))
    (h₂ : IsIso ((ρ_ Y).inv ≫ Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom)) (L T : D) :
    Function.Bijective fun g : T ⟶ L ⊗ Y => g ▷ X ≫ (α_ L Y X).hom ≫ L ◁ ε ≫ (ρ_ L).hom := by
  refine ⟨fun g₁ g₂ hg => ?_, fun f => ?_⟩
  · have hg' := congrArg (fun f => (ρ_ T).inv ≫ T ◁ η ≫ (α_ T X Y).inv ≫ f ▷ Y) hg
    simp only [zigzag_transpose_transpose] at hg'
    exact (cancel_mono _).1 hg'
  · refine ⟨(ρ_ T).inv ≫ T ◁ η ≫ (α_ T X Y).inv ≫
      (inv (T ◁ ((λ_ X).inv ≫ η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom)) ≫ f) ▷ Y, ?_⟩
    dsimp only
    rw [zigzag_transpose_transpose', IsIso.hom_inv_id_assoc]

end Zigzag

section Functor

variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D]
  [MonoidalCategory D] (P : C ⥤ D) (m : ∀ A B : C, P.obj (A ⊗ B) ≅ P.obj A ⊗ P.obj B)
  (hl : ∀ {A A' : C} (f : A ⟶ A') (B : C),
    P.map (f ▷ B) ≫ (m A' B).hom = (m A B).hom ≫ P.map f ▷ P.obj B)
  (hr : ∀ (A : C) {B B' : C} (g : B ⟶ B'),
    P.map (A ◁ g) ≫ (m A B').hom = (m A B).hom ≫ P.obj A ◁ P.map g)
  (ha : ∀ A B E : C, (m (A ⊗ B) E).hom ≫ (m A B).hom ▷ P.obj E ≫ (α_ _ _ _).hom =
    P.map (α_ A B E).hom ≫ (m A (B ⊗ E)).hom ≫ P.obj A ◁ (m B E).hom)

include ha in
/-- The associativity law of the comparison, solved for the middle three factors. -/
theorem associative_hom_comp_whiskerLeft_inv (A B E : C) :
    (m A B).hom ▷ P.obj E ≫ (α_ _ _ _).hom ≫ P.obj A ◁ (m B E).inv =
      (m (A ⊗ B) E).inv ≫ P.map (α_ A B E).hom ≫ (m A (B ⊗ E)).hom := by
  rw [← cancel_epi (m (A ⊗ B) E).hom, ← cancel_mono (P.obj A ◁ (m B E).hom)]
  simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact ha A B E

include ha in
/-- The inverse form of `associative_hom_comp_whiskerLeft_inv`. -/
theorem associative_whiskerLeft_hom_comp_inv (A B E : C) :
    P.obj A ◁ (m B E).hom ≫ (α_ _ _ _).inv ≫ (m A B).inv ▷ P.obj E =
      (m A (B ⊗ E)).inv ≫ P.map (α_ A B E).inv ≫ (m (A ⊗ B) E).hom := by
  rw [← cancel_epi (m A (B ⊗ E)).hom, ← cancel_mono ((m A B).hom ▷ P.obj E)]
  simp only [Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight,
    Category.comp_id, Iso.hom_inv_id_assoc]
  have h := ha A B E
  rw [← cancel_epi (P.map (α_ A B E).inv), ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [← cancel_mono (α_ _ _ _).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Category.assoc, h]

variable (ν : P.obj (𝟙_ C) ≅ 𝟙_ D) (K K' : C) [ExactPairing K K']

/-- The coevaluation of `K ⊣ K'` read through `m` and `ν`. -/
abbrev mapCoevaluation : 𝟙_ D ⟶ P.obj K ⊗ P.obj K' :=
  ν.inv ≫ P.map (η_ K K') ≫ (m K K').hom

/-- The evaluation of `K ⊣ K'` read through `m` and `ν`. -/
abbrev mapEvaluation : P.obj K' ⊗ P.obj K ⟶ 𝟙_ D :=
  (m K' K).inv ≫ P.map (ε_ K K') ≫ ν.hom

include hl hr ha in
/-- The first zigzag of the mapped pairing is invertible. -/
theorem isIso_mapZigzag₁ :
    IsIso ((λ_ (P.obj K)).inv ≫ mapCoevaluation P m ν K K' ▷ P.obj K ≫
      (α_ (P.obj K) (P.obj K') (P.obj K)).hom ≫ P.obj K ◁ mapEvaluation P m ν K K' ≫
        (ρ_ (P.obj K)).hom) := by
  have key : (λ_ (P.obj K)).inv ≫ mapCoevaluation P m ν K K' ▷ P.obj K ≫
      (α_ (P.obj K) (P.obj K') (P.obj K)).hom ≫ P.obj K ◁ mapEvaluation P m ν K K' ≫
        (ρ_ (P.obj K)).hom =
      (λ_ (P.obj K)).inv ≫ ν.inv ▷ P.obj K ≫ (m (𝟙_ C) K).inv ≫
        P.map ((λ_ K).hom ≫ (ρ_ K).inv) ≫ (m K (𝟙_ C)).hom ≫ P.obj K ◁ ν.hom ≫
          (ρ_ (P.obj K)).hom := by
    simp only [mapCoevaluation, mapEvaluation, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [reassoc_of% (associative_hom_comp_whiskerLeft_inv P m ha K K' K)]
    have e₁ : P.map (η_ K K') ▷ P.obj K ≫ (m (K ⊗ K') K).inv =
        (m (𝟙_ C) K).inv ≫ P.map (η_ K K' ▷ K) :=
      (CommSq.vert_inv ⟨hl (η_ K K') K⟩).w
    have e₂ : (m K (K' ⊗ K)).hom ≫ P.obj K ◁ P.map (ε_ K K') =
        P.map (K ◁ ε_ K K') ≫ (m K (𝟙_ C)).hom := (hr K (ε_ K K')).symm
    have hz : η_ K K' ▷ K ≫ (α_ K K' K).hom ≫ K ◁ ε_ K K' = (λ_ K).hom ≫ (ρ_ K).inv := by simp
    rw [reassoc_of% e₁, reassoc_of% e₂, ← hz]
    simp only [Functor.map_comp, Category.assoc]
  rw [key]
  infer_instance

include hl hr ha in
/-- The second zigzag of the mapped pairing is invertible. -/
theorem isIso_mapZigzag₂ :
    IsIso ((ρ_ (P.obj K')).inv ≫ P.obj K' ◁ mapCoevaluation P m ν K K' ≫
      (α_ (P.obj K') (P.obj K) (P.obj K')).inv ≫ mapEvaluation P m ν K K' ▷ P.obj K' ≫
        (λ_ (P.obj K')).hom) := by
  have key : (ρ_ (P.obj K')).inv ≫ P.obj K' ◁ mapCoevaluation P m ν K K' ≫
      (α_ (P.obj K') (P.obj K) (P.obj K')).inv ≫ mapEvaluation P m ν K K' ▷ P.obj K' ≫
        (λ_ (P.obj K')).hom =
      (ρ_ (P.obj K')).inv ≫ P.obj K' ◁ ν.inv ≫ (m K' (𝟙_ C)).inv ≫
        P.map ((ρ_ K').hom ≫ (λ_ K').inv) ≫ (m (𝟙_ C) K').hom ≫ ν.hom ▷ P.obj K' ≫
          (λ_ (P.obj K')).hom := by
    simp only [mapCoevaluation, mapEvaluation, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [reassoc_of% (associative_whiskerLeft_hom_comp_inv P m ha K' K K')]
    have e₁ : P.obj K' ◁ P.map (η_ K K') ≫ (m K' (K ⊗ K')).inv =
        (m K' (𝟙_ C)).inv ≫ P.map (K' ◁ η_ K K') :=
      (CommSq.vert_inv ⟨hr K' (η_ K K')⟩).w
    have e₂ : (m (K' ⊗ K) K').hom ≫ P.map (ε_ K K') ▷ P.obj K' =
        P.map (ε_ K K' ▷ K') ≫ (m (𝟙_ C) K').hom := (hl (ε_ K K') K').symm
    have hz : K' ◁ η_ K K' ≫ (α_ K' K K').inv ≫ ε_ K K' ▷ K' = (ρ_ K').hom ≫ (λ_ K').inv := by
      simp
    rw [reassoc_of% e₁, reassoc_of% e₂, ← hz]
    simp only [Functor.map_comp, Category.assoc]
  rw [key]
  infer_instance

include hl hr ha ν K' in
/-- **An associative tensor comparison carries an internal Hom out of a dualizable object to an
internal Hom.** Let `P : C ⥤ D` carry a natural isomorphism `m : P(A ⊗ B) ≅ P A ⊗ P B`
compatible with the associativity constraints, and let `ν : P 𝟙 ≅ 𝟙` be any isomorphism. If
`K ⊣ K'` is an exact pairing in `C` and `e : I ⊗ K ⟶ L` is the evaluation of an internal Hom,
then `m⁻¹ ≫ P e : P I ⊗ P K ⟶ P L` is the evaluation of an internal Hom in `D`. -/
theorem tensorHomBijective_map_of_associative {L I : C} {e : I ⊗ K ⟶ L}
    (h : ∀ T : C, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e) (T : D) :
    Function.Bijective fun g : T ⟶ P.obj I => g ▷ P.obj K ≫ (m I K).inv ≫ P.map e := by
  obtain ⟨θ, hθe⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective e _ h
    (tensorHomBijective_pairingEvaluation K K' L)
  have hstd := tensorHomBijective_of_isIso_zigzag (mapCoevaluation P m ν K K')
    (mapEvaluation P m ν K K') (isIso_mapZigzag₁ P m hl hr ha ν K K')
    (isIso_mapZigzag₂ P m hl hr ha ν K K') (P.obj L) T
  let σ : P.obj I ≅ P.obj L ⊗ P.obj K' := P.mapIso θ ≪≫ m L K'
  let a : P.obj L ≅ P.obj L := (ρ_ (P.obj L)).symm ≪≫ whiskerLeftIso (P.obj L) ν.symm ≪≫
    (m L (𝟙_ C)).symm ≪≫ P.mapIso (ρ_ L)
  have key : σ.hom ▷ P.obj K ≫ ((α_ (P.obj L) (P.obj K') (P.obj K)).hom ≫
      P.obj L ◁ mapEvaluation P m ν K K' ≫ (ρ_ (P.obj L)).hom) ≫ a.hom =
      (m I K).inv ≫ P.map e := by
    rw [← hθe]
    simp only [σ, a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, whiskerLeftIso_hom,
      mapEvaluation, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, pairingEvaluation, Functor.map_comp]
    rw [reassoc_of% (associative_hom_comp_whiskerLeft_inv P m ha L K' K)]
    have e₁ : (m L (K' ⊗ K)).hom ≫ P.obj L ◁ P.map (ε_ K K') ≫ (m L (𝟙_ C)).inv =
        P.map (L ◁ ε_ K K') := by
      rw [← reassoc_of% (hr L (ε_ K K')), Iso.hom_inv_id, Category.comp_id]
    have e₂ : P.map θ.hom ▷ P.obj K ≫ (m (L ⊗ K') K).inv = (m I K).inv ≫ P.map (θ.hom ▷ K) :=
      (CommSq.vert_inv ⟨hl θ.hom K⟩).w
    rw [reassoc_of% e₁, reassoc_of% e₂]
  have hfun : (fun g : T ⟶ P.obj I => g ▷ P.obj K ≫ (m I K).inv ≫ P.map e) =
      (fun f => f ≫ a.hom) ∘
        (fun g : T ⟶ P.obj L ⊗ P.obj K' => g ▷ P.obj K ≫ (α_ (P.obj L) (P.obj K') (P.obj K)).hom ≫
          P.obj L ◁ mapEvaluation P m ν K K' ≫ (ρ_ (P.obj L)).hom) ∘
        (fun g => g ≫ σ.hom) := by
    funext g
    simp only [Function.comp_apply, comp_whiskerRight, Category.assoc, ← key]
  rw [hfun]
  refine Function.Bijective.comp ⟨fun x y hxy => ?_, fun f => ⟨f ≫ a.inv, by simp⟩⟩
    (Function.Bijective.comp hstd ⟨fun x y hxy => ?_, fun f => ⟨f ≫ σ.inv, by simp⟩⟩)
  · simpa using congrArg (· ≫ a.inv) hxy
  · simpa using congrArg (· ≫ σ.inv) hxy

end Functor

end CategoryTheory.MonoidalCategory

end
