module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutChartTriples
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct

/-!
# Base change and transport of triples, and the comparison of two charts over `X`

For a 1-morphism `P : 𝒞/Y ⥤ 𝒳` and `k : X ⟶ Y`, a triple for `Over.map k ⋙ P` over `T` is a
triple for `P` whose first morphism factors through `k`; so if `F` represents the 2-fibre product
of `P` and `f₀`, the sections of the fibre product of presheaves `F ×_{h_Y} h_X` are the triples
for `Over.map k ⋙ P` (`AlgebraicGeometry.Stack.ThickeningPushout.fibreProductTripEquiv`). A
vertical isomorphism `P₁ ≅ P₂` of 1-morphisms out of `𝒞/X` transports triples. Together they give,
in the situation of Stacks 07WN, the isomorphism `V ×_Y X ≅ Q ×_{X'} X` between the base changes
to `X` of the algebraic spaces representing `Y ×_𝒵 W` and `X' ×_𝒵 W`
(`AlgebraicGeometry.Stack.ThickeningPushout.chartComparison`).

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack.ThickeningPushout

universe v₁ u₁ u₂ v₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}
  (hp : p.IsFiberedInGroupoids) {U₀ : 𝒞} {f₀ : Over U₀ ⥤ 𝒳} (hf₀ : f₀ ⋙ p = Over.forget U₀)


/-! ### Morphisms of slices between objects of the form `Over.mk t` -/

omit hp hf₀ in
/-- A functor carries a composite of two morphisms `Over.homMk` to the morphism `Over.homMk` of
the composite. -/
@[reassoc]
lemma map_homMk_comp {A : 𝒞} (P : Over A ⥤ 𝒳) {T₁ T₂ T₃ : 𝒞} {t₁ : T₁ ⟶ A} {t₂ : T₂ ⟶ A}
    {t₃ : T₃ ⟶ A} (g₁ : T₁ ⟶ T₂) (g₂ : T₂ ⟶ T₃) (g₃ : T₁ ⟶ T₃) (w₁ : g₁ ≫ t₂ = t₁)
    (w₂ : g₂ ≫ t₃ = t₂) (w₃ : g₃ ≫ t₃ = t₁) (h : g₁ ≫ g₂ = g₃) :
    P.map (Over.homMk g₁ w₁ : Over.mk t₁ ⟶ Over.mk t₂) ≫
        P.map (Over.homMk g₂ w₂ : Over.mk t₂ ⟶ Over.mk t₃) =
      P.map (Over.homMk g₃ w₃ : Over.mk t₁ ⟶ Over.mk t₃) := by
  rw [← P.map_comp]
  congr 1
  exact Over.OverMorphism.ext (by simpa using h)

omit hp hf₀ in
/-- A functor carries `Over.homMk (𝟙 T)` between equal objects to the identity. -/
@[simp]
lemma map_homMk_id {A : 𝒞} (P : Over A ⥤ 𝒳) {T : 𝒞} (t : T ⟶ A) (w : 𝟙 T ≫ t = t) :
    P.map (Over.homMk (𝟙 T) w : Over.mk t ⟶ Over.mk t) = 𝟙 _ := by
  rw [show (Over.homMk (𝟙 T) w : Over.mk t ⟶ Over.mk t) = 𝟙 _ from
    Over.OverMorphism.ext rfl, P.map_id]

omit hp hf₀ in
/-- A functor carries `Over.homMk (𝟙 T)` to an isomorphism. -/
instance isIso_map_homMk_id {A : 𝒞} (P : Over A ⥤ 𝒳) {T : 𝒞} {t t' : T ⟶ A}
    (w : 𝟙 T ≫ t' = t) : IsIso (P.map (Over.homMk (𝟙 T) w : Over.mk t ⟶ Over.mk t')) :=
  ⟨P.map (Over.homMk (𝟙 T) (by simp [← w]) : Over.mk t' ⟶ Over.mk t),
    by rw [map_homMk_comp P _ _ (𝟙 T) w _ (by simp [← w]) (by simp), map_homMk_id]; rfl,
    by rw [map_homMk_comp P _ _ (𝟙 T) _ w (by simp) (by simp), map_homMk_id]⟩

omit hp hf₀ in
/-- A functor carries the composite of `Over.homMk (𝟙 T) : Over.mk t ⟶ Over.mk t'` and
`Over.homMk (𝟙 T) : Over.mk t' ⟶ Over.mk t` to the identity. -/
@[reassoc (attr := simp)]
lemma map_homMk_id_comp_map_homMk_id {A : 𝒞} (P : Over A ⥤ 𝒳) {T : 𝒞} {t t' : T ⟶ A}
    (w : 𝟙 T ≫ t' = t) (w' : 𝟙 T ≫ t = t') :
    P.map (Over.homMk (𝟙 T) w : Over.mk t ⟶ Over.mk t') ≫
      P.map (Over.homMk (𝟙 T) w' : Over.mk t' ⟶ Over.mk t) = 𝟙 _ := by
  rw [map_homMk_comp P _ _ (𝟙 T) w w' (by simp [← w]) (by simp), map_homMk_id]

omit hp hf₀ in
/-- The inverse of the image of `Over.homMk (𝟙 T) : Over.mk t ⟶ Over.mk t'` is the image of
`Over.homMk (𝟙 T) : Over.mk t' ⟶ Over.mk t`. -/
lemma inv_map_homMk_id {A : 𝒞} (P : Over A ⥤ 𝒳) {T : 𝒞} {t t' : T ⟶ A}
    (w : 𝟙 T ≫ t' = t) (w' : 𝟙 T ≫ t = t') :
    inv (P.map (Over.homMk (𝟙 T) w : Over.mk t ⟶ Over.mk t')) =
      P.map (Over.homMk (𝟙 T) w' : Over.mk t' ⟶ Over.mk t) := by
  rw [IsIso.inv_eq_of_hom_inv_id]
  rw [map_homMk_comp P _ _ (𝟙 T) w w' (by simp [← w]) (by simp), map_homMk_id]

/-! ### Base change of triples -/

section MapBase

variable {X Y : 𝒞} (k : X ⟶ Y) {P : Over Y ⥤ 𝒳}

/-- A triple for `Over.map k ⋙ P`, read as a triple for `P`. -/
def Trip.mapBase {T : 𝒞} (τ : Trip p f₀ (Over.map k ⋙ P) T) : Trip p f₀ P T :=
  ⟨τ.1 ≫ k, τ.2.1, τ.2.2.1, τ.2.2.2⟩

/-- The first morphism of `τ.mapBase k` is the composite of the first morphism of `τ` with `k`. -/
@[simp] lemma Trip.mapBase_fst {T : 𝒞} (τ : Trip p f₀ (Over.map k ⋙ P) T) :
    (τ.mapBase k).1 = τ.1 ≫ k := rfl

/-- The second morphism of `τ.mapBase k` is the second morphism of `τ`. -/
@[simp] lemma Trip.mapBase_snd_fst {T : 𝒞} (τ : Trip p f₀ (Over.map k ⋙ P) T) :
    (τ.mapBase k).2.1 = τ.2.1 := rfl

variable (hP : P ⋙ p = Over.forget Y) {F : 𝒞ᵒᵖ ⥤ Type v₁}
  (e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget U₀) p P f₀)
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-- Naming the base change of a triple is compatible with restriction. -/
lemma tripSection_mapBase_restrict {T T' : 𝒞} (g : T' ⟶ T)
    (τ : Trip p f₀ (Over.map k ⋙ P) T) :
    tripSection e ((τ.restrict hp hf₀ (by rw [Functor.assoc, hP]; rfl) g).mapBase k) =
      F.map g.op (tripSection e (τ.mapBase k)) :=
  tripSection_eq_map_of_hom e g (τ.mapBase k) _ (Category.assoc _ _ _).symm rfl
    (Trip.restrictHom_fac hp hf₀ (by rw [Functor.assoc, hP]; rfl) g τ).symm

end MapBase

/-! ### Transport of triples along the comparison of points -/

section Transfer

variable (c : p.ChoiceOfPullbacks) {X X' Y : 𝒞} (f : X ⟶ Y) (i : X ⟶ X') (y : p.Fiber Y)
  (x' : p.Fiber X') (α : c.obj f y ≅ c.obj i x')

/-- The comparison of points at `h : T ⟶ X`, as a morphism between the values at `h ≫ f` and
`h ≫ i`. -/
noncomputable abbrev θ {T : 𝒞} (h : T ⟶ X) :
    (TwoYoneda.liftFunctor p hp Y y).obj (Over.mk (h ≫ f)) ⟶
      (TwoYoneda.liftFunctor p hp X' x').obj (Over.mk (h ≫ i)) :=
  pointCompHom p hp c f i y x' α (Over.mk h)

/-- The comparison of points `θ` at `h : T ⟶ X` lies over `𝟙 T`. -/
lemma isHomLift_θ {T : 𝒞} (h : T ⟶ X) : p.IsHomLift (𝟙 T) (θ hp c f i y x' α h) :=
  isHomLift_pointCompHom p hp c f i y x' α (Over.mk h)

/-- The inverse of the comparison of points `θ` at `h : T ⟶ X` lies over `𝟙 T`. -/
lemma isHomLift_inv_θ {T : 𝒞} (h : T ⟶ X) : p.IsHomLift (𝟙 T) (inv (θ hp c f i y x' α h)) :=
  have := isHomLift_θ hp c f i y x' α h
  IsHomLift.lift_id_inv_isIso p T (θ hp c f i y x' α h)

/-- **Naturality of the comparison of points.** For `g : T' ⟶ T` and `h : T ⟶ X`, the
comparison `θ` commutes with the maps induced by `g`. -/
@[reassoc]
lemma θ_naturality {T T' : 𝒞} (g : T' ⟶ T) (h : T ⟶ X) :
    θ hp c f i y x' α (g ≫ h) ≫ (TwoYoneda.liftFunctor p hp X' x').map
        (Over.homMk g (Category.assoc _ _ _).symm :
          Over.mk ((g ≫ h) ≫ i) ⟶ Over.mk (h ≫ i)) =
      (TwoYoneda.liftFunctor p hp Y y).map
        (Over.homMk g (Category.assoc _ _ _).symm :
          Over.mk ((g ≫ h) ≫ f) ⟶ Over.mk (h ≫ f)) ≫ θ hp c f i y x' α h :=
  pointCompHom_naturality p hp c f i y x' α
    (Over.homMk g rfl : Over.mk (g ≫ h) ⟶ Over.mk h)

variable {U₀ : 𝒞} {f₀ : Over U₀ ⥤ 𝒳}

/-- The image of `Over.homMk (𝟙 T)` under `TwoYoneda.liftFunctor p hp A w` lies over `𝟙 T`. -/
lemma isHomLift_liftFunctor_homMk_id {A T : 𝒞} (w : p.Fiber A) {t t' : T ⟶ A}
    (ht : 𝟙 T ≫ t' = t) :
    p.IsHomLift (𝟙 T) ((TwoYoneda.liftFunctor p hp A w).map
      (Over.homMk (𝟙 T) ht : Over.mk t ⟶ Over.mk t')) :=
  have : (Over.forget A).IsHomLift (𝟙 T) (Over.homMk (𝟙 T) ht : Over.mk t ⟶ Over.mk t') :=
    IsHomLift.of_fac' _ (𝟙 T) _ rfl rfl (by simp)
  isHomLift_map_of_comp_eq (TwoYoneda.liftFunctor_w p hp A w) (𝟙 T) _

/-- The transport of a triple for `y` whose first morphism is `h ≫ f` to a triple for `x'`
with first morphism `h ≫ i`. -/
noncomputable def transfer {T : 𝒞} (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T)
    (h : T ⟶ X) (hτ : τ.1 = h ≫ f) : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') T :=
  Trip.mk' hp (h ≫ i) τ.2.1
    (inv (θ hp c f i y x' α h) ≫ (TwoYoneda.liftFunctor p hp Y y).map
      (Over.homMk (𝟙 T) (by simp [hτ]) : Over.mk (h ≫ f) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom)
    (have := isHomLift_inv_θ hp c f i y x' α h
     have := isHomLift_liftFunctor_homMk_id hp y (t := h ≫ f) (t' := τ.1) (by simp [hτ])
     have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
     inferInstance)

/-- The transport of a triple for `x'` whose first morphism is `h ≫ i` back to a triple for `y`
with first morphism `h ≫ f`. -/
noncomputable def transferInv {T : 𝒞} (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') T)
    (h : T ⟶ X) (hτ : τ.1 = h ≫ i) : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T :=
  Trip.mk' hp (h ≫ f) τ.2.1
    (θ hp c f i y x' α h ≫ (TwoYoneda.liftFunctor p hp X' x').map
      (Over.homMk (𝟙 T) (by simp [hτ]) : Over.mk (h ≫ i) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom)
    (have := isHomLift_θ hp c f i y x' α h
     have := isHomLift_liftFunctor_homMk_id hp x' (t := h ≫ i) (t' := τ.1) (by simp [hτ])
     have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
     inferInstance)

end Transfer

section TransferSections

variable (c : p.ChoiceOfPullbacks) {X X' Y : 𝒞} (f : X ⟶ Y) (i : X ⟶ X') (y : p.Fiber Y)
  (x' : p.Fiber X') (α : c.obj f y ≅ c.obj i x')
  {FY FX' : 𝒞ᵒᵖ ⥤ Type v₁}
  (eY : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget U₀) p
      (TwoYoneda.liftFunctor p hp Y y) f₀)
    (presheafOfCategories (FY ⋙ typeToCat)).p)
  (eX' : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget X') (Over.forget U₀) p
      (TwoYoneda.liftFunctor p hp X' x') f₀)
    (presheafOfCategories (FX' ⋙ typeToCat)).p)

/-- Transporting there and back names the same section. -/
lemma tripSection_transferInv_transfer {T : 𝒞}
    (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T) (h : T ⟶ X) (hτ : τ.1 = h ≫ f) :
    tripSection eY (transferInv hp c f i y x' α (transfer hp c f i y x' α τ h hτ) h rfl) =
      tripSection eY τ := by
  refine tripSection_eq_of_hom eY τ _ hτ rfl ?_
  show _ = (θ hp c f i y x' α h ≫ (TwoYoneda.liftFunctor p hp X' x').map
      (Over.homMk (𝟙 T) (by simp) : Over.mk (h ≫ i) ⟶ Over.mk (h ≫ i)) ≫
      inv (θ hp c f i y x' α h) ≫ (TwoYoneda.liftFunctor p hp Y y).map
      (Over.homMk (𝟙 T) (by simp [hτ]) : Over.mk (h ≫ f) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom) ≫
    f₀.map (Over.homMk (𝟙 T) (by simp) : Over.mk τ.2.1 ⟶ Over.mk τ.2.1)
  simp only [Over.mk_hom, map_homMk_id, Category.id_comp, Category.comp_id,
    IsIso.hom_inv_id_assoc]
  rfl

/-- Transporting back and there names the same section. -/
lemma tripSection_transfer_transferInv {T : 𝒞}
    (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') T) (h : T ⟶ X) (hτ : τ.1 = h ≫ i) :
    tripSection eX' (transfer hp c f i y x' α (transferInv hp c f i y x' α τ h hτ) h rfl) =
      tripSection eX' τ := by
  refine tripSection_eq_of_hom eX' τ _ hτ rfl ?_
  show _ = (inv (θ hp c f i y x' α h) ≫ (TwoYoneda.liftFunctor p hp Y y).map
      (Over.homMk (𝟙 T) (by simp) : Over.mk (h ≫ f) ⟶ Over.mk (h ≫ f)) ≫
      θ hp c f i y x' α h ≫ (TwoYoneda.liftFunctor p hp X' x').map
      (Over.homMk (𝟙 T) (by simp [hτ]) : Over.mk (h ≫ i) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom) ≫
    f₀.map (Over.homMk (𝟙 T) (by simp) : Over.mk τ.2.1 ⟶ Over.mk τ.2.1)
  simp only [Over.mk_hom, map_homMk_id, Category.id_comp, Category.comp_id,
    IsIso.inv_hom_id_assoc]
  rfl

/-- **Transport of triples commutes with restriction.** -/
lemma tripSection_transfer_restrict {T T' : 𝒞} (g : T' ⟶ T)
    (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T) (h : T ⟶ X) (hτ : τ.1 = h ≫ f) :
    tripSection eX' (transfer hp c f i y x' α
        (τ.restrict hp hf₀ (TwoYoneda.liftFunctor_w p hp Y y) g) (g ≫ h)
        (by simp [hτ])) =
      FX'.map g.op (tripSection eX' (transfer hp c f i y x' α τ h hτ)) := by
  refine tripSection_eq_map_of_hom eX' g _ _ (Category.assoc _ _ _).symm rfl ?_
  have e1 := Trip.restrictHom_fac hp hf₀ (TwoYoneda.liftFunctor_w p hp Y y) g τ
  have e2 : (TwoYoneda.liftFunctor p hp Y y).map
        (Over.homMk (𝟙 T') (by simp [hτ]) : Over.mk ((g ≫ h) ≫ f) ⟶ Over.mk (g ≫ τ.1)) ≫
        (TwoYoneda.liftFunctor p hp Y y).map
          (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) =
      (TwoYoneda.liftFunctor p hp Y y).map
        (Over.homMk g (Category.assoc _ _ _).symm :
          Over.mk ((g ≫ h) ≫ f) ⟶ Over.mk (h ≫ f)) ≫
        (TwoYoneda.liftFunctor p hp Y y).map
          (Over.homMk (𝟙 T) (by simp [hτ]) : Over.mk (h ≫ f) ⟶ Over.mk τ.1) := by
    rw [map_homMk_comp _ _ _ g _ _ (by simp [hτ]) (by simp),
      map_homMk_comp _ _ _ g _ _ (by simp [hτ]) (by simp)]
  have e3 : (TwoYoneda.liftFunctor p hp X' x').map
        (Over.homMk g (Category.assoc _ _ _).symm :
          Over.mk ((g ≫ h) ≫ i) ⟶ Over.mk (h ≫ i)) ≫ inv (θ hp c f i y x' α h) =
      inv (θ hp c f i y x' α (g ≫ h)) ≫ (TwoYoneda.liftFunctor p hp Y y).map
        (Over.homMk g (Category.assoc _ _ _).symm :
          Over.mk ((g ≫ h) ≫ f) ⟶ Over.mk (h ≫ f)) := by
    rw [IsIso.eq_inv_comp, θ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  dsimp only [transfer, Trip.mk', Trip.restrict]
  simp only [asIso_hom, Category.assoc]
  rw [e1, reassoc_of% e2, reassoc_of% e3]

end TransferSections

/-! ### The comparison of the two base changes to `X` -/

section Comparison

variable (c : p.ChoiceOfPullbacks) {X X' Y : 𝒞} (f : X ⟶ Y) (i : X ⟶ X') (y : p.Fiber Y)
  (x' : p.Fiber X') (α : c.obj f y ≅ c.obj i x')
  {FY FX' : 𝒞ᵒᵖ ⥤ Type v₁}
  (eY : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget U₀) p
      (TwoYoneda.liftFunctor p hp Y y) f₀)
    (presheafOfCategories (FY ⋙ typeToCat)).p)
  (eX' : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget X') (Over.forget U₀) p
      (TwoYoneda.liftFunctor p hp X' x') f₀)
    (presheafOfCategories (FX' ⋙ typeToCat)).p)
  (ρY : FY ⟶ yoneda.obj Y) (ρX' : FX' ⟶ yoneda.obj X')
  (hρY : ∀ {T : 𝒞} (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T),
    ρY.app (op T) (tripSection eY τ) = τ.1)
  (hρX' : ∀ {T : 𝒞} (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') T),
    ρX'.app (op T) (tripSection eX' τ) = τ.1)

omit hf₀ in
/-- Equal triples have equal transports. -/
lemma transfer_congr {T : 𝒞} {τ₁ τ₂ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T} (h : T ⟶ X)
    (h₁ : τ₁.1 = h ≫ f) (h₂ : τ₂.1 = h ≫ f) (e : τ₁ = τ₂) :
    transfer hp c f i y x' α τ₁ h h₁ = transfer hp c f i y x' α τ₂ h h₂ := by
  subst e; rfl

omit hf₀ in
/-- Equal triples have equal inverse transports. -/
lemma transferInv_congr {T : 𝒞} {τ₁ τ₂ : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') T}
    (h : T ⟶ X) (h₁ : τ₁.1 = h ≫ i) (h₂ : τ₂.1 = h ≫ i) (e : τ₁ = τ₂) :
    transferInv hp c f i y x' α τ₁ h h₁ = transferInv hp c f i y x' α τ₂ h h₂ := by
  subst e; rfl

omit hf₀ in
include hρY in
/-- The first morphism of the triple naming a section `σ` of `FY` is the image of `σ` under
`ρY`. -/
lemma tripEquiv_symm_fst {T : 𝒞} (σ : FY.obj (op T)) :
    ((tripEquiv eY T).symm σ).1 = ρY.app (op T) σ := by
  conv_rhs => rw [← (tripEquiv eY T).apply_symm_apply σ]
  rw [tripEquiv_apply, hρY]

/-- The comparison on sections. -/
noncomputable def chartComparisonApp (T : 𝒞) :
    (Presheaf.fibreProduct ρY (yoneda.map f)).obj (op T) →
      (Presheaf.fibreProduct ρX' (yoneda.map i)).obj (op T) := fun x =>
  ⟨(tripSection eX' (transfer hp c f i y x' α ((tripEquiv eY T).symm x.1.1) x.1.2
      (by rw [tripEquiv_symm_fst hp y eY ρY hρY]; exact x.2)), x.1.2), by
    change ρX'.app (op T) _ = x.1.2 ≫ i
    rw [hρX']; rfl⟩

/-- The inverse comparison on sections. -/
noncomputable def chartComparisonInvApp (T : 𝒞) :
    (Presheaf.fibreProduct ρX' (yoneda.map i)).obj (op T) →
      (Presheaf.fibreProduct ρY (yoneda.map f)).obj (op T) := fun x =>
  ⟨(tripSection eY (transferInv hp c f i y x' α ((tripEquiv eX' T).symm x.1.1) x.1.2
      (by rw [tripEquiv_symm_fst hp x' eX' ρX' hρX']; exact x.2)), x.1.2), by
    change ρY.app (op T) _ = x.1.2 ≫ f
    rw [hρY]; rfl⟩

/-- `chartComparisonInvApp` is a left inverse of `chartComparisonApp`. -/
lemma chartComparisonInvApp_app (T : 𝒞) (x : (Presheaf.fibreProduct ρY (yoneda.map f)).obj (op T)) :
    chartComparisonInvApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T
      (chartComparisonApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T x) = x := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  show tripSection eY (transferInv hp c f i y x' α ((tripEquiv eX' T).symm (tripSection eX'
    (transfer hp c f i y x' α ((tripEquiv eY T).symm x.1.1) x.1.2 _))) x.1.2 _) = x.1.1
  refine (congrArg (tripSection eY) (transferInv_congr hp c f i y x' α x.1.2 _ rfl
    ((tripEquiv eX' T).symm_apply_apply _))).trans ?_
  refine (tripSection_transferInv_transfer hp c f i y x' α eY _ _ _).trans ?_
  exact (tripEquiv eY T).apply_symm_apply _

/-- `chartComparisonInvApp` is a right inverse of `chartComparisonApp`. -/
lemma chartComparisonApp_invApp (T : 𝒞)
    (x : (Presheaf.fibreProduct ρX' (yoneda.map i)).obj (op T)) :
    chartComparisonApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T
      (chartComparisonInvApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T x) = x := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  show tripSection eX' (transfer hp c f i y x' α ((tripEquiv eY T).symm (tripSection eY
    (transferInv hp c f i y x' α ((tripEquiv eX' T).symm x.1.1) x.1.2 _))) x.1.2 _) = x.1.1
  refine (congrArg (tripSection eX') (transfer_congr hp c f i y x' α x.1.2 _ rfl
    ((tripEquiv eY T).symm_apply_apply _))).trans ?_
  refine (tripSection_transfer_transferInv hp c f i y x' α eX' _ _ _).trans ?_
  exact (tripEquiv eX' T).apply_symm_apply _

include hf₀ in
/-- `chartComparisonApp` is natural with respect to restriction along `g : T' ⟶ T`. -/
lemma chartComparisonApp_naturality {T T' : 𝒞} (g : T' ⟶ T)
    (x : (Presheaf.fibreProduct ρY (yoneda.map f)).obj (op T)) :
    chartComparisonApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T'
        ((Presheaf.fibreProduct ρY (yoneda.map f)).map g.op x) =
      (Presheaf.fibreProduct ρX' (yoneda.map i)).map g.op
        (chartComparisonApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T x) := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  set τ := (tripEquiv eY T).symm x.1.1 with hτ
  have hx : x.1.1 = tripSection eY τ := ((tripEquiv eY T).apply_symm_apply _).symm
  have key : (tripEquiv eY T').symm (FY.map g.op x.1.1) =
      τ.restrict hp hf₀ (TwoYoneda.liftFunctor_w p hp Y y) g := by
    rw [Equiv.symm_apply_eq, tripEquiv_apply, hx, map_tripSection]
  show tripSection eX' (transfer hp c f i y x' α ((tripEquiv eY T').symm (FY.map g.op x.1.1))
    (g ≫ x.1.2) _) = FX'.map g.op (tripSection eX' (transfer hp c f i y x' α τ x.1.2 _))
  have hτ' : τ.1 = x.1.2 ≫ f := by rw [tripEquiv_symm_fst hp y eY ρY hρY]; exact x.2
  refine (congrArg (tripSection eX') (transfer_congr hp c f i y x' α (g ≫ x.1.2) _
    (by simp [hτ']) key)).trans ?_
  exact tripSection_transfer_restrict hp hf₀ c f i y x' α eX' g τ x.1.2 hτ'

/-- **The comparison `V ×_Y X ≅ Q ×_{X'} X`** of the base changes to `X` of the presheaves
representing the 2-fibre products of the points `y` and `x'` with `f₀`, induced by the
isomorphism `α : f^* y ≅ i^* x'`. It commutes with the projections to `h_X`. -/
noncomputable def chartComparison :
    Presheaf.fibreProduct ρY (yoneda.map f) ≅ Presheaf.fibreProduct ρX' (yoneda.map i) :=
  NatIso.ofComponents
    (fun T => {
      hom := ↾(chartComparisonApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T.unop)
      inv := ↾(chartComparisonInvApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' T.unop)
      hom_inv_id := by
        ext x
        exact chartComparisonInvApp_app hp c f i y x' α eY eX' ρY ρX' hρY hρX' _ x
      inv_hom_id := by
        ext x
        exact chartComparisonApp_invApp hp c f i y x' α eY eX' ρY ρX' hρY hρX' _ x })
    (fun {T T'} g => by
      ext x
      exact chartComparisonApp_naturality hp hf₀ c f i y x' α eY eX' ρY ρX' hρY hρX' g.unop x)

/-- The comparison `chartComparison` commutes with the projections to `h_X`. -/
lemma chartComparison_hom_snd :
    (chartComparison hp hf₀ c f i y x' α eY eX' ρY ρX' hρY hρX').hom ≫
        Presheaf.fibreProductSnd ρX' (yoneda.map i) =
      Presheaf.fibreProductSnd ρY (yoneda.map f) := by
  ext T x
  rfl

/-- The comparison carries a section named by a triple to the section named by its transport. -/
lemma chartComparison_hom_app_fst {T : 𝒞} (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) T)
    (h : T ⟶ X) (hτ : τ.1 = h ≫ f) :
    ((chartComparison hp hf₀ c f i y x' α eY eX' ρY ρX' hρY hρX').hom.app (op T)
      ⟨(tripSection eY τ, h), by rw [hρY]; exact hτ⟩).1.1 =
      tripSection eX' (transfer hp c f i y x' α τ h hτ) := by
  show tripSection eX' (transfer hp c f i y x' α ((tripEquiv eY T).symm (tripSection eY τ)) h _)
    = _
  exact congrArg (tripSection eX')
    (transfer_congr hp c f i y x' α h _ hτ ((tripEquiv eY T).symm_apply_apply τ))

end Comparison

/-! ### The compatibility over `X` of two charts related by transport -/

section Glue

variable (c : p.ChoiceOfPullbacks) {X X' Y : 𝒞} (f : X ⟶ Y) (i : X ⟶ X') (y : p.Fiber Y)
  (x' : p.Fiber X') (α : c.obj f y ≅ c.obj i x')

/-- Inverting the restricted comparison of a triple and mapping `g` under the point gives the image
of `g` under `f₀` followed by the inverse of the comparison. -/
private theorem inv_restrictHom_comp_map_homMk {A T T' : 𝒞} {P : Over A ⥤ 𝒳}
    (hP : P ⋙ p = Over.forget A) (τ : Trip p f₀ P T) (g : T' ⟶ T) :
    inv (τ.restrict hp hf₀ hP g).2.2.1.hom ≫
        P.map (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) =
      f₀.map (Over.homMk g rfl : Over.mk (g ≫ τ.2.1) ⟶ Over.mk τ.2.1) ≫ inv τ.2.2.1.hom := by
  rw [IsIso.inv_comp_eq, Trip.restrict_iso_hom, Trip.restrictHom_fac_assoc hp hf₀ hP,
    IsIso.hom_inv_id, Category.comp_id]

/-- The inverse of the comparison of a triple, followed by the cartesian map of the point, lies
over the first morphism of the triple. -/
private theorem isHomLift_inv_comp_liftπ {A T : 𝒞} (w : p.Fiber A)
    (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp A w) T) :
    p.IsHomLift τ.1 (inv τ.2.2.1.hom ≫ liftπ p hp w (Over.mk τ.1)) :=
  have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
  have := IsHomLift.lift_id_inv_isIso p T τ.2.2.1.hom
  have : p.IsHomLift τ.1 (liftπ p hp w (Over.mk τ.1)) :=
    (isStronglyCartesian_liftπ p hp w (Over.mk τ.1)).toIsHomLift
  IsHomLift.comp_lift_id_left' p T _ τ.1 _

include hf₀ in
/-- **The local preimage morphisms over a pair of charts related by transport.** Let `τ` be a
triple for `y` over `V₁` and `τ'` a triple for `x'` over `U'₁`, and let `g : U₁ ⟶ V₁`,
`k : U₁ ⟶ U'₁`, `r : U₁ ⟶ X` be such that the restriction of `τ'` along `k` is related by a
vertical compatibility to the transport along `r` of the restriction of `τ` along `g`. Then the
images under `f₀` of the second morphisms of the triples map to `y` and `x'`, and over `U₁` the
two composites to `x'` — through `α` and through `k` — agree. -/
theorem exists_glueMorphisms {V₁ U'₁ U₁ : 𝒞}
    (τ : Trip p f₀ (TwoYoneda.liftFunctor p hp Y y) V₁)
    (τ' : Trip p f₀ (TwoYoneda.liftFunctor p hp X' x') U'₁)
    (g : U₁ ⟶ V₁) (k : U₁ ⟶ U'₁) (r : U₁ ⟶ X) (hcond : g ≫ τ.1 = r ≫ f)
    (hc₁ : r ≫ i = k ≫ τ'.1) (hc₂ : g ≫ τ.2.1 = k ≫ τ'.2.1)
    (hc₃ : (TwoYoneda.liftFunctor p hp X' x').map (Over.homMk (𝟙 U₁) (by simp [hc₁]) :
        Over.mk (k ≫ τ'.1) ⟶ Over.mk (r ≫ i)) ≫
        (transfer hp c f i y x' α (τ.restrict hp hf₀ (TwoYoneda.liftFunctor_w p hp Y y) g) r
          hcond).2.2.1.hom =
      (τ'.restrict hp hf₀ (TwoYoneda.liftFunctor_w p hp X' x') k).2.2.1.hom ≫
        f₀.map (Over.homMk (𝟙 U₁) (by simp [hc₂]) : Over.mk (k ≫ τ'.2.1) ⟶ Over.mk (g ≫ τ.2.1)))
    (σ₁ : V₁ ⟶ U₀) (σ' : U'₁ ⟶ U₀) (hσ₁ : σ₁ = τ.2.1) (hσ' : σ' = τ'.2.1) :
    ∃ (ψY : f₀.obj (Over.mk σ₁) ⟶ y.1) (ψX : f₀.obj (Over.mk σ') ⟶ x'.1)
      (lam : f₀.obj (Over.mk (g ≫ σ₁)) ⟶ (c.obj f y).1),
      p.IsHomLift τ.1 ψY ∧ p.IsHomLift τ'.1 ψX ∧ p.IsHomLift r lam ∧
      lam ≫ c.map f y = f₀.map (Over.homMk g rfl : Over.mk (g ≫ σ₁) ⟶ Over.mk σ₁) ≫ ψY ∧
      lam ≫ α.hom.1 ≫ c.map i x' =
        f₀.map (Over.homMk k (by simp [hσ₁, hσ', hc₂]) : Over.mk (g ≫ σ₁) ⟶ Over.mk σ') ≫ ψX := by
  subst hσ₁ hσ'
  have hPy := TwoYoneda.liftFunctor_w p hp Y y
  have hPx := TwoYoneda.liftFunctor_w p hp X' x'
  let Rg := (τ.restrict hp hf₀ hPy g).2.2.1.hom
  let Rk := (τ'.restrict hp hf₀ hPx k).2.2.1.hom
  let Tt := (transfer hp c f i y x' α (τ.restrict hp hf₀ hPy g) r hcond).2.2.1.hom
  let L : (TwoYoneda.liftFunctor p hp Y y).obj (Over.mk (r ≫ f)) ⟶
      (TwoYoneda.liftFunctor p hp Y y).obj (Over.mk (g ≫ τ.1)) :=
    (TwoYoneda.liftFunctor p hp Y y).map (Over.homMk (𝟙 U₁) (by simp [hcond]))
  have hTe : Tt = inv (θ hp c f i y x' α r) ≫ L ≫ Rg := rfl
  have e3 : inv Rg ≫ _ = _ := inv_restrictHom_comp_map_homMk hp hf₀ hPy τ g
  have e3' : inv Rk ≫ _ = _ := inv_restrictHom_comp_map_homMk hp hf₀ hPx τ' k
  have e1 : inv L ≫ liftπ p hp y (Over.mk (r ≫ f)) = liftπ p hp y (Over.mk (g ≫ τ.1)) := by
    rw [IsIso.inv_comp_eq]
    exact (liftFunctor_map_liftπ p hp y _).symm
  have hRg1 : p.IsHomLift (𝟙 U₁) Rg := (τ.restrict hp hf₀ hPy g).2.2.2
  have hL1 : p.IsHomLift (𝟙 U₁) L := isHomLift_liftFunctor_homMk_id hp y _
  have hpf := isHomLift_pointFactor p hp c f y (Over.mk r)
  refine ⟨inv τ.2.2.1.hom ≫ liftπ p hp y (Over.mk τ.1),
    inv τ'.2.2.1.hom ≫ liftπ p hp x' (Over.mk τ'.1),
    inv Rg ≫ inv L ≫ pointFactor p hp c f y (Over.mk r), ?_, ?_, ?_, ?_, ?_⟩
  · exact isHomLift_inv_comp_liftπ hp y τ
  · exact isHomLift_inv_comp_liftπ hp x' τ'
  · have := IsHomLift.lift_id_inv_isIso p U₁ Rg
    have := IsHomLift.lift_id_inv_isIso p U₁ L
    have : p.IsHomLift r (pointFactor p hp c f y (Over.mk r)) := hpf
    have : p.IsHomLift r (inv L ≫ pointFactor p hp c f y (Over.mk r)) :=
      IsHomLift.comp_lift_id_left' p U₁ _ r _
    exact IsHomLift.comp_lift_id_left' p U₁ _ r _
  · simp only [Category.assoc]
    rw [pointFactor_fac]
    show inv Rg ≫ inv L ≫ liftπ p hp y (Over.mk (r ≫ f)) = _
    rw [e1, ← liftFunctor_map_liftπ p hp y (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1),
      reassoc_of% e3]
  · have key : inv Rk ≫ (TwoYoneda.liftFunctor p hp X' x').map (Over.homMk (𝟙 U₁)
        (by simp [hc₁]) : Over.mk (k ≫ τ'.1) ⟶ Over.mk (r ≫ i)) =
        f₀.map (Over.homMk (𝟙 U₁) (by simp [hc₂]) :
          Over.mk (k ≫ τ'.2.1) ⟶ Over.mk (g ≫ τ.2.1)) ≫ inv Rg ≫ inv L ≫
          θ hp c f i y x' α r := by
      rw [IsIso.inv_comp_eq]
      have h2 : (τ'.restrict hp hf₀ hPx k).2.2.1.hom ≫
          f₀.map (Over.homMk (𝟙 U₁) (by simp [hc₂]) :
            Over.mk (k ≫ τ'.2.1) ⟶ Over.mk (g ≫ τ.2.1)) =
          (TwoYoneda.liftFunctor p hp X' x').map (Over.homMk (𝟙 U₁) (by simp [hc₁]) :
            Over.mk (k ≫ τ'.1) ⟶ Over.mk (r ≫ i)) ≫ inv (θ hp c f i y x' α r) ≫ L ≫ Rg :=
        hc₃.symm
      refine Eq.symm ?_
      show (τ'.restrict hp hf₀ hPx k).2.2.1.hom ≫ _ ≫ _ = _
      rw [reassoc_of% h2, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id]
      exact Category.comp_id _
    have hLHS : (inv Rg ≫ inv L ≫ pointFactor p hp c f y (Over.mk r)) ≫ α.hom.1 ≫
        c.map i x' = inv Rg ≫ inv L ≫ θ hp c f i y x' α r ≫
          liftπ p hp x' (Over.mk (r ≫ i)) := by
      simp only [Category.assoc]
      congr 2
      exact (pointCompHom_fac p hp c f i y x' α (Over.mk r)).symm
    rw [hLHS, ← map_homMk_comp_assoc f₀ (𝟙 U₁) k k (by simp [hc₂]) rfl (by simp [hc₂])
      (by simp), reassoc_of% e3'.symm, liftFunctor_map_liftπ,
      ← liftFunctor_map_liftπ p hp x' (Over.homMk (𝟙 U₁) (by simp [hc₁]) :
        Over.mk (k ≫ τ'.1) ⟶ Over.mk (r ≫ i)), reassoc_of% key,
      map_homMk_id_comp_map_homMk_id_assoc]

end Glue

end AlgebraicGeometry.Stack.ThickeningPushout

end
