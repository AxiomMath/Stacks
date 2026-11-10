module

public import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapBaseChange

/-!
# The projection and comparison maps of a composite

Let `F₁ : A ⥤ B` and `F₂ : B ⥤ C` be oplax monoidal functors with right adjoints `G₁`, `G₂`, and
let `G₁ ⊣ a₁`, `G₂ ⊣ a₂`. The projection map (`CategoryTheory.Adjunction.projectionMap`) of the
composite adjunction `F₁ ⋙ F₂ ⊣ G₂ ⋙ G₁` is the projection map of `F₁ ⊣ G₁` followed by `G₁` of
that of `F₂ ⊣ G₂`, and the comparison map (`CategoryTheory.Adjunction.comparisonMap`, the
two-variable form of Equation 48.8.0.1) of the composite is the comparison map of `F₂` at
`(F₁ K, a₁ L)` followed by `a₂` of the comparison map of `F₁` at `(K, L)`. This is the
categorical content of [Stacks, Tag 0B6R], in two variables.

## Main results

* `CategoryTheory.Adjunction.projectionMap_comp`: the projection map of a composite adjunction.
* `CategoryTheory.Adjunction.comparisonMap_comp`: the comparison map of a composite adjunction.
* `Stacks.CategoryTheory.BaseChange.isIso_map_comparisonMap_comp_iff`: in a base change square
  along which `α` is invertible at the relevant objects and the comparison maps of the base change
  are invertible, `Lg'` inverts the comparison map of a composite `F₀ ⋙ Lf` exactly when `a' ∘ Lg`
  inverts that of `F₀`; this is how [Stacks, Tag 0B6R] and [Stacks, Tag 0B6P] combine in the proof
  of [Stacks, Tag 0B6T].
* `CategoryTheory.Adjunction.projectionMap_of_iso`,
  `CategoryTheory.Adjunction.comparisonMap_of_iso`: the projection and comparison maps depend on
  the adjunctions only up to isomorphism: isomorphisms `F ≅ F'` (of oplax monoidal functors),
  `G ≅ G'` and `a ≅ a'` compatible with the counits conjugate them. This is what carries the
  composite statement to a third adjunction `F ⊣ G` with `F ≅ F₁ ⋙ F₂`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Comp

variable {A B C : Type*} [Category A] [Category B] [Category C] [MonoidalCategory A]
  [MonoidalCategory B] [MonoidalCategory C] {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C}
  {G₂ : C ⥤ B} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) [F₁.OplaxMonoidal] [F₂.OplaxMonoidal]

/-- **The projection map of a composite adjunction** is the projection map of `F₁ ⊣ G₁` at
`(K, G₂ M)` followed by `G₁` of the projection map of `F₂ ⊣ G₂` at `(F₁ K, M)`. -/
lemma projectionMap_comp (K : A) (M : C) :
    (adj₁.comp adj₂).projectionMap K M =
      adj₁.projectionMap K (G₂.obj M) ≫ G₁.map (adj₂.projectionMap (F₁.obj K) M) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit (adj₁.comp adj₂)
  have n₁ : F₁.map (G₁.map (adj₂.projectionMap (F₁.obj K) M)) ≫
      adj₁.counit.app (G₂.obj (F₂.obj (F₁.obj K) ⊗ M)) =
      adj₁.counit.app (F₁.obj K ⊗ G₂.obj M) ≫ adj₂.projectionMap (F₁.obj K) M :=
    adj₁.counit.naturality _
  have m₁ := map_projectionMap_comp_counit adj₁ K (G₂.obj M)
  have m₂ := map_projectionMap_comp_counit adj₂ (F₁.obj K) M
  have d : F₂.map (F₁.obj K ◁ adj₁.counit.app (G₂.obj M)) ≫ δ F₂ (F₁.obj K) (G₂.obj M) =
      δ F₂ (F₁.obj K) (F₁.obj (G₁.obj (G₂.obj M))) ≫
        F₂.obj (F₁.obj K) ◁ F₂.map (adj₁.counit.app (G₂.obj M)) :=
    (δ_natural_right F₂ _ _).symm
  rw [map_projectionMap_comp_counit]
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc, Functor.OplaxMonoidal.comp_δ, MonoidalCategory.whiskerLeft_comp]
  rw [← F₂.map_comp_assoc (F₁.map (G₁.map _)), n₁, F₂.map_comp_assoc, m₂,
    ← F₂.map_comp_assoc, m₁, F₂.map_comp_assoc, reassoc_of% d]

variable [∀ (K : A) (M : B), IsIso (adj₁.projectionMap K M)]
  [∀ (K : B) (M : C), IsIso (adj₂.projectionMap K M)]
  {a₁ : A ⥤ B} {a₂ : B ⥤ C} (b₁ : G₁ ⊣ a₁) (b₂ : G₂ ⊣ a₂)

/-- The projection map of a composite of adjunctions with invertible projection maps is
invertible. -/
instance (K : A) (M : C) : IsIso ((adj₁.comp adj₂).projectionMap K M) := by
  rw [projectionMap_comp]; infer_instance

/-- The inverse projection map is natural in the second variable. -/
private theorem map_whiskerLeft_comp_inv_projectionMap_aux (K : A) {M M' : B} (g : M ⟶ M') :
    G₁.map (F₁.obj K ◁ g) ≫ inv (adj₁.projectionMap K M') =
      inv (adj₁.projectionMap K M) ≫ K ◁ G₁.map g := by
  rw [IsIso.comp_inv_eq, Category.assoc, adj₁.whiskerLeft_projectionMap, IsIso.inv_hom_id_assoc]

/-- **The comparison map of a composite** ([Stacks, Tag 0B6R] in two variables): the comparison
map of `(F₂ ⊣ G₂, G₂ ⊣ a₂)` at `(F₁ K, a₁ L)` followed by `a₂` of the comparison map of
`(F₁ ⊣ G₁, G₁ ⊣ a₁)` at `(K, L)`. -/
lemma comparisonMap_comp (K L : A) :
    (adj₁.comp adj₂).comparisonMap (b₂.comp b₁) K L =
      adj₂.comparisonMap b₂ (F₁.obj K) (a₁.obj L) ≫ a₂.map (adj₁.comparisonMap b₁ K L) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit (b₂.comp b₁)
  have n : G₂.map (a₂.map (adj₁.comparisonMap b₁ K L)) ≫ b₂.counit.app (a₁.obj (K ⊗ L)) =
      b₂.counit.app (F₁.obj K ⊗ a₁.obj L) ≫ adj₁.comparisonMap b₁ K L :=
    b₂.counit.naturality _
  have m₂ := map_comparisonMap_comp_counit adj₂ b₂ (F₁.obj K) (a₁.obj L)
  have m₁ := map_comparisonMap_comp_counit adj₁ b₁ K L
  have w := map_whiskerLeft_comp_inv_projectionMap_aux adj₁ K (b₂.counit.app (a₁.obj L))
  rw [map_comparisonMap_comp_counit]
  simp only [projectionMap_comp, IsIso.inv_comp, ← Functor.map_inv]
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [← G₁.map_comp_assoc (G₂.map (a₂.map _)), n, G₁.map_comp_assoc, m₁,
    ← G₁.map_comp_assoc, m₂, G₁.map_comp_assoc, reassoc_of% w]

end Comp

section Invariance

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F F' : C ⥤ D} {G G' : D ⥤ C} [F.OplaxMonoidal] [F'.OplaxMonoidal]
  (adj : F ⊣ G) (adj' : F' ⊣ G') (e : F ≅ F') (i : G ≅ G')
  (he : ∀ K N : C, δ F K N ≫ (e.hom.app K ⊗ₘ e.hom.app N) = e.hom.app (K ⊗ N) ≫ δ F' K N)
  (hi : ∀ M : D, F'.map (i.hom.app M) ≫ adj'.counit.app M = e.inv.app (G.obj M) ≫ adj.counit.app M)

include he hi in
/-- **Invariance of the projection map** under isomorphisms `F ≅ F'` of oplax monoidal functors
and `G ≅ G'` compatible with the counits. -/
lemma projectionMap_of_iso (K : C) (M : D) :
    adj'.projectionMap K M =
      K ◁ i.inv.app M ≫ adj.projectionMap K M ≫ i.hom.app (F.obj K ⊗ M) ≫
        G'.map (e.hom.app K ▷ M) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj'
  have n₁ : F'.map (G'.map (e.hom.app K ▷ M)) ≫ adj'.counit.app (F'.obj K ⊗ M) =
      adj'.counit.app (F.obj K ⊗ M) ≫ e.hom.app K ▷ M := adj'.counit.naturality _
  have n₂ : e.inv.app (K ⊗ G.obj M) ≫ F.map (adj.projectionMap K M) =
      F'.map (adj.projectionMap K M) ≫ e.inv.app (G.obj (F.obj K ⊗ M)) :=
    (e.inv.naturality _).symm
  have h₁ : e.inv.app (K ⊗ G.obj M) ≫ δ F K (G.obj M) =
      δ F' K (G.obj M) ≫ (e.inv.app K ⊗ₘ e.inv.app (G.obj M)) := by
    rw [← cancel_epi (e.hom.app (K ⊗ G.obj M)), Iso.hom_inv_id_app_assoc, ← reassoc_of% (he _ _),
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id, Category.comp_id]
  have h₂ : (e.inv.app K ⊗ₘ e.inv.app (G.obj M)) ≫ F.obj K ◁ adj.counit.app M ≫
      e.hom.app K ▷ M = F'.obj K ◁ (e.inv.app (G.obj M) ≫ adj.counit.app M) := by
    rw [MonoidalCategory.tensorHom_def', Category.assoc, ← whisker_exchange_assoc]
    simp only [Functor.id_obj]
    rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id_app, MonoidalCategory.id_whiskerRight,
      Category.comp_id, ← MonoidalCategory.whiskerLeft_comp]
  have h₃ : F'.map (K ◁ i.inv.app M) ≫ δ F' K (G.obj M) =
      δ F' K (G'.obj M) ≫ F'.obj K ◁ F'.map (i.inv.app M) := (δ_natural_right F' _ _).symm
  have h₄ : F'.map (i.inv.app M) ≫ e.inv.app (G.obj M) ≫ adj.counit.app M =
      adj'.counit.app M := by
    rw [← hi, ← F'.map_comp_assoc, Iso.inv_hom_id_app, F'.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hi' := hi (F.obj K ⊗ M)
  rw [n₁, reassoc_of% hi', ← reassoc_of% n₂, map_projectionMap_comp_counit_assoc, reassoc_of% h₁,
    h₂, reassoc_of% h₃, ← MonoidalCategory.whiskerLeft_comp, h₄, map_projectionMap_comp_counit]

variable [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
  [∀ (K : C) (M : D), IsIso (adj'.projectionMap K M)]
  {a a' : C ⥤ D} (b : G ⊣ a) (b' : G' ⊣ a') (j : a ≅ a')
  (hj : ∀ L : C, G'.map (j.hom.app L) ≫ b'.counit.app L = i.inv.app (a.obj L) ≫ b.counit.app L)

include he hi hj in
/-- **Invariance of the comparison map** under isomorphisms `F ≅ F'` of oplax monoidal functors,
`G ≅ G'` and `a ≅ a'` compatible with the counits. -/
lemma comparisonMap_of_iso (K L : C) :
    adj'.comparisonMap b' K L =
      (e.inv.app K ⊗ₘ j.inv.app L) ≫ adj.comparisonMap b K L ≫ j.hom.app (K ⊗ L) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit b'
  have hπ := projectionMap_of_iso adj adj' e i he hi K (a'.obj L)
  have n₁ : G'.map (j.hom.app (K ⊗ L)) ≫ b'.counit.app (K ⊗ L) =
      i.inv.app (a.obj (K ⊗ L)) ≫ b.counit.app (K ⊗ L) := hj _
  have n₂ : G'.map (adj.comparisonMap b K L) ≫ i.inv.app (a.obj (K ⊗ L)) =
      i.inv.app (F.obj K ⊗ a.obj L) ≫ G.map (adj.comparisonMap b K L) :=
    i.inv.naturality _
  have n₃ : G'.map (e.inv.app K ⊗ₘ j.inv.app L) ≫ i.inv.app (F.obj K ⊗ a.obj L) =
      i.inv.app (F'.obj K ⊗ a'.obj L) ≫ G.map (e.inv.app K ⊗ₘ j.inv.app L) :=
    i.inv.naturality _
  rw [map_comparisonMap_comp_counit]
  simp only [Functor.map_comp, Category.assoc]
  have p₁ := map_whiskerLeft_comp_inv_projectionMap_aux adj K (j.inv.app L)
  have p₂ : G.map (e.hom.app K ▷ a'.obj L) ≫ G.map (e.inv.app K ⊗ₘ j.inv.app L) =
      G.map (F.obj K ◁ j.inv.app L) := by
    rw [← G.map_comp, MonoidalCategory.tensorHom_def, ← MonoidalCategory.comp_whiskerRight_assoc,
      Iso.hom_inv_id_app, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have p₃ : i.hom.app (F.obj K ⊗ a'.obj L) ≫ G'.map (e.hom.app K ▷ a'.obj L) ≫
      i.inv.app (F'.obj K ⊗ a'.obj L) = G.map (e.hom.app K ▷ a'.obj L) := by
    rw [i.inv.naturality, Iso.hom_inv_id_app_assoc]
  have hε : i.inv.app (a'.obj L) ≫ G.map (j.inv.app L) ≫ b.counit.app L = b'.counit.app L := by
    rw [← i.inv.naturality_assoc, ← hj, ← G'.map_comp_assoc, Iso.inv_hom_id_app, G'.map_id,
      Category.id_comp]
  rw [n₁, reassoc_of% n₂, reassoc_of% n₃, map_comparisonMap_comp_counit, IsIso.inv_comp_eq, hπ]
  simp only [Category.assoc]
  rw [reassoc_of% p₃, reassoc_of% p₂, reassoc_of% p₁, IsIso.hom_inv_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, hε]

omit [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
  [∀ (K : C) (M : D), IsIso (adj'.projectionMap K M)] in
include he in
/-- **Invertibility of the comparison map does not depend on the adjunctions**: for an
isomorphism `F ≅ F'` of oplax monoidal functors, any adjunctions `F ⊣ G`, `F' ⊣ G'`, `G ⊣ a`,
`G' ⊣ a'` and any functor `H`, `H` inverts the comparison map of `(F' ⊣ G', G' ⊣ a')` at `(K, L)`
exactly when it inverts that of `(F ⊣ G, G ⊣ a)` at `(K, L)`, conjugated by the comparisons of
the right adjoints. -/
lemma isIso_map_comparisonMap_iff_of_iso [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
    [∀ (K : C) (M : D), IsIso (adj'.projectionMap K M)] {a a' : C ⥤ D} (b : G ⊣ a) (b' : G' ⊣ a')
    {E : Type*} [Category E] (H : D ⥤ E) (K L : C) :
    IsIso (H.map (adj'.comparisonMap b' K L)) ↔
      IsIso (H.map (adj.comparisonMap b K L ≫
        (Adjunction.rightAdjointUniq (b.ofNatIsoLeft
          (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj')) b').hom.app (K ⊗ L))) := by
  set i := Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj'
  set j := Adjunction.rightAdjointUniq (b.ofNatIsoLeft i) b'
  have hi : ∀ M : D, F'.map (i.hom.app M) ≫ adj'.counit.app M =
      e.inv.app (G.obj M) ≫ adj.counit.app M := fun M => by
    rw [Adjunction.rightAdjointUniq_hom_app_counit]; rfl
  have hj : ∀ L : C, G'.map (j.hom.app L) ≫ b'.counit.app L =
      i.inv.app (a.obj L) ≫ b.counit.app L := fun L => by
    rw [Adjunction.rightAdjointUniq_hom_app_counit]; rfl
  rw [comparisonMap_of_iso adj adj' e i he hi b b' j hj K L, H.map_comp, isIso_comp_left_iff]

omit [F'.OplaxMonoidal] [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] in
/-- **The comparison map is invertible when the pushforward is an equivalence**: then the unit
and the counit of `G ⊣ a` are invertible. -/
lemma isIso_comparisonMap_of_isEquivalence [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
    [G.IsEquivalence] {a : C ⥤ D} (b : G ⊣ a) (K L : C) :
    IsIso (adj.comparisonMap b K L) := by
  rw [comparisonMap, Adjunction.homEquiv_unit]
  infer_instance

end Invariance

section Assoc

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]
  [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] {a : C ⥤ D} (b : G ⊣ a)

/-- The inverse projection map is natural in the second variable. -/
@[reassoc]
lemma map_whiskerLeft_comp_inv_projectionMap (K : C) {M M' : D} (g : M ⟶ M') :
    G.map (F.obj K ◁ g) ≫ inv (adj.projectionMap K M') =
      inv (adj.projectionMap K M) ≫ K ◁ G.map g :=
  map_whiskerLeft_comp_inv_projectionMap_aux adj K g

/-- **The comparison map is compatible with the associators**: the oplax structure of `F` at
`(M, N)` whiskered by `a L`, the associator and the comparison maps at `(N, L)` and `(M, N ⊗ L)`
compose to the comparison map at `(M ⊗ N, L)` followed by `a` of the associator. -/
lemma comparisonMap_assoc (M N L : C) :
    δ F M N ▷ a.obj L ≫ (α_ (F.obj M) (F.obj N) (a.obj L)).hom ≫
        F.obj M ◁ adj.comparisonMap b N L ≫ adj.comparisonMap b M (N ⊗ L) =
      adj.comparisonMap b (M ⊗ N) L ≫ a.map (α_ M N L).hom := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit b
  have hp := adj.projectionMap_assoc N M (a.obj L)
  have hp' : G.map (δ F M N ▷ a.obj L) ≫ G.map (α_ (F.obj M) (F.obj N) (a.obj L)).hom ≫
      inv (adj.projectionMap M (F.obj N ⊗ a.obj L)) ≫ M ◁ inv (adj.projectionMap N (a.obj L)) =
      inv (adj.projectionMap (M ⊗ N) (a.obj L)) ≫ (α_ M N (G.obj (a.obj L))).hom := by
    rw [← cancel_epi (adj.projectionMap (M ⊗ N) (a.obj L)), IsIso.hom_inv_id_assoc]
    have hp'' : adj.projectionMap (M ⊗ N) (a.obj L) ≫ G.map (δ F M N ▷ a.obj L) =
        (α_ M N (G.obj (a.obj L))).hom ≫ M ◁ adj.projectionMap N (a.obj L) ≫
          adj.projectionMap M (F.obj N ⊗ a.obj L) ≫
            G.map (α_ (F.obj M) (F.obj N) (a.obj L)).inv := by
      rw [hp, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hp'', ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
      IsIso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp, IsIso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  have hc : G.map (a.map (α_ M N L).hom) ≫ b.counit.app (M ⊗ N ⊗ L) =
      b.counit.app ((M ⊗ N) ⊗ L) ≫ (α_ M N L).hom := b.counit.naturality _
  simp only [Functor.map_comp, Category.assoc]
  rw [map_comparisonMap_comp_counit, hc, map_comparisonMap_comp_counit_assoc,
    map_whiskerLeft_comp_inv_projectionMap_assoc, ← MonoidalCategory.whiskerLeft_comp,
    map_comparisonMap_comp_counit, MonoidalCategory.whiskerLeft_comp, reassoc_of% hp',
    MonoidalCategory.associator_naturality_right]

/-- **The one-variable comparison map is compatible with the associators**: with
`μ K = cmp (K, 𝟙) ≫ a ρ_K`, the map `μ (M ⊗ N)` is the oplax structure of `F` at `(M, N)`,
the associator, `F M` tensored with `μ N`, and the comparison map at `(M, N)`. -/
lemma comparisonMap_unit_assoc (M N : C) :
    adj.comparisonMap b (M ⊗ N) (𝟙_ C) ≫ a.map (ρ_ (M ⊗ N)).hom =
      δ F M N ▷ a.obj (𝟙_ C) ≫ (α_ (F.obj M) (F.obj N) (a.obj (𝟙_ C))).hom ≫
        F.obj M ◁ (adj.comparisonMap b N (𝟙_ C) ≫ a.map (ρ_ N).hom) ≫
          adj.comparisonMap b M N := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [comparisonMap_naturality_right, reassoc_of% (comparisonMap_assoc adj b M N (𝟙_ C)),
    ← a.map_comp, MonoidalCategory.rightUnitor_tensor_hom]

end Assoc

section CompUnit

variable {A B C : Type*} [Category A] [Category B] [Category C] [MonoidalCategory A]
  [MonoidalCategory B] [MonoidalCategory C] {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C}
  {G₂ : C ⥤ B} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) [F₁.OplaxMonoidal] [F₂.OplaxMonoidal]
  [∀ (K : A) (M : B), IsIso (adj₁.projectionMap K M)]
  [∀ (K : B) (M : C), IsIso (adj₂.projectionMap K M)]
  {a₁ : A ⥤ B} {a₂ : B ⥤ C} (b₁ : G₁ ⊣ a₁) (b₂ : G₂ ⊣ a₂)
  {F : A ⥤ C} {G : C ⥤ A} [F.OplaxMonoidal] (adj : F ⊣ G)
  [∀ (K : A) (M : C), IsIso (adj.projectionMap K M)] {c : A ⥤ C} (bc : G ⊣ c)
  (e : F₁ ⋙ F₂ ≅ F) (i : G₂ ⋙ G₁ ≅ G) (j : a₁ ⋙ a₂ ≅ c)
  (he : ∀ K N : A, δ (F₁ ⋙ F₂) K N ≫ (e.hom.app K ⊗ₘ e.hom.app N) =
    e.hom.app (K ⊗ N) ≫ δ F K N)
  (hi : ∀ M : C, F.map (i.hom.app M) ≫ adj.counit.app M =
    e.inv.app ((G₂ ⋙ G₁).obj M) ≫ (adj₁.comp adj₂).counit.app M)
  (hj : ∀ L : A, G.map (j.hom.app L) ≫ bc.counit.app L =
    i.inv.app ((a₁ ⋙ a₂).obj L) ≫ (b₂.comp b₁).counit.app L)

include he hi hj in
/-- **[Stacks, Tag 0B6R] over abstract monoidal adjunctions.** For `F ⊣ G` identified with the
composite of `F₁ ⊣ G₁` and `F₂ ⊣ G₂` (through `F ≅ F₁ ⋙ F₂`, `G ≅ G₂ ⋙ G₁` and `c ≅ a₁ ⋙ a₂`
compatible with the counits) and the one-variable comparison maps
`μ K = cmp (K, 𝟙) ≫ a ρ_K`, the composite
`F₂(F₁K ⊗ a₁𝟙) ⊗ a₂𝟙 ⟶ a₂(F₁K ⊗ a₁𝟙) ⟶ a₂(a₁K) = c K` of `μ₂` and `a₂ μ₁` is the
identification `F₂(F₁K ⊗ a₁𝟙) ⊗ a₂𝟙 ≅ F K ⊗ (F₂(a₁𝟙) ⊗ a₂𝟙)` followed by `F K` tensored with
`μ₂(a₁𝟙)` (landing in `a₂(a₁𝟙) = c 𝟙`) and `μ K`. -/
lemma comparisonMap_unit_comp {UA : A} {UB : B} (hA : 𝟙_ A = UA) (hB : 𝟙_ B = UB) (K : A) :
    (adj₂.comparisonMap b₂ (F₁.obj K ⊗ a₁.obj UA) UB ≫
        a₂.map ((F₁.obj K ⊗ a₁.obj UA) ◁ eqToHom hB.symm ≫
          (ρ_ (F₁.obj K ⊗ a₁.obj UA)).hom)) ≫
      a₂.map (adj₁.comparisonMap b₁ K UA ≫ a₁.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom)) ≫
        j.hom.app K =
    (δ F₂ (F₁.obj K) (a₁.obj UA) ▷ a₂.obj UB ≫
        (α_ (F₂.obj (F₁.obj K)) (F₂.obj (a₁.obj UA)) (a₂.obj UB)).hom ≫
        e.hom.app K ▷ _) ≫
      F.obj K ◁ ((adj₂.comparisonMap b₂ (a₁.obj UA) UB ≫
        a₂.map (a₁.obj UA ◁ eqToHom hB.symm ≫ (ρ_ (a₁.obj UA)).hom)) ≫ j.hom.app UA) ≫
      adj.comparisonMap bc K UA ≫ c.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom) := by
  subst hA hB
  simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hc := comparisonMap_of_iso (adj₁.comp adj₂) adj e i he hi (b₂.comp b₁) bc j hj K (𝟙_ A)
  have hcomp := comparisonMap_comp adj₁ adj₂ b₁ b₂ K (𝟙_ A)
  have hn : j.hom.app (K ⊗ 𝟙_ A) ≫ c.map (ρ_ K).hom =
      a₂.map (a₁.map (ρ_ K).hom) ≫ j.hom.app K := (j.hom.naturality _).symm
  have hw : e.hom.app K ▷ a₂.obj (a₁.obj (𝟙_ A)) ≫ F.obj K ◁ j.hom.app (𝟙_ A) ≫
      (e.inv.app K ⊗ₘ j.inv.app (𝟙_ A)) = 𝟙 _ := by
    rw [MonoidalCategory.tensorHom_def, whisker_exchange_assoc]
    simp
  rw [comparisonMap_unit_assoc adj₂ b₂ (F₁.obj K) (a₁.obj (𝟙_ A)), hc, hcomp]
  simp only [Category.assoc, Functor.map_comp, MonoidalCategory.whiskerLeft_comp]
  rw [hn, ← whisker_exchange_assoc, ← whisker_exchange_assoc, reassoc_of% hw]
  rfl

end CompUnit

end CategoryTheory.Adjunction

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {R : Type*} {S : Type*} {T : Type*} {S' : Type*} {T' : Type*} [Category R]
  [Category S] [Category T] [Category S'] [Category T'] [MonoidalCategory R]
  [MonoidalCategory S] [MonoidalCategory T] [MonoidalCategory S'] [MonoidalCategory T']
  {F₀ : R ⥤ S} {G₀ : S ⥤ R} {a₀ : R ⥤ S}
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Rg : S' ⥤ S} {Lg' : T ⥤ T'} {Rg' : T' ⥤ T} {Lc : S ⥤ T'}
  [F₀.OplaxMonoidal] [Lf.OplaxMonoidal] [Lf'.OplaxMonoidal] [Lg.OplaxMonoidal]
  [Lg'.OplaxMonoidal]
  (adj₀ : F₀ ⊣ G₀) (b₀ : G₀ ⊣ a₀)
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (hsq : ∀ K N : S, Lf'.map (δ Lg K N) ≫ δ Lf' (Lg.obj K) (Lg.obj N) ≫
      ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ Lg'.map (δ Lf K N) ≫
      δ Lg' (Lf.obj K) (Lf.obj N))
  {a : S ⥤ T} {a' : S' ⥤ T'} (adja : Rf ⊣ a) (adja' : Rf' ⊣ a')
  [∀ (K : R) (M : S), IsIso (adj₀.projectionMap K M)]
  [∀ (K : S) (M : T), IsIso (adjf.projectionMap K M)]
  [∀ (K : S') (M : T'), IsIso (adjf'.projectionMap K M)]
  [IsIso (twoSquare adjf adjf' eg ef)]

include hsq in
/-- **Invertibility of the comparison map of a composite under base change.** In a base change
square along which `α` is invertible at `a₀ L` and at `a₀ (K ⊗ L)`, whose oplax structure of `Lg`
is invertible and whose base change has invertible comparison maps, `Lg'` inverts the comparison
map of the composite adjunction `F₀ ⋙ Lf ⊣ Rf ⋙ G₀` at `(K, L)` exactly when `a' ∘ Lg` inverts
the comparison map of `F₀ ⊣ G₀` at `(K, L)`. -/
theorem isIso_map_comparisonMap_comp_iff [∀ K N : S, IsIso (δ Lg K N)]
    [∀ M N : T, IsIso (δ Lg' M N)]
    [∀ (A : S') (B : S'), IsIso (adjf'.comparisonMap adja' A B)] (K L : R)
    [IsIso ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app
      (a₀.obj L))]
    [IsIso ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app
      (a₀.obj (K ⊗ L)))] :
    IsIso (Lg'.map ((adj₀.comp adjf).comparisonMap (adja.comp b₀) K L)) ↔
      IsIso (a'.map (Lg.map (adj₀.comparisonMap b₀ K L))) := by
  set α := rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja'
  set E := F₀.obj K
  set M := a₀.obj L
  have hbc := comparisonMap_baseChange adjf adjf' adjg adjg' eg ef hsq adja adja' E M
  have hn : Lg'.map (a.map (adj₀.comparisonMap b₀ K L)) ≫ α.app (a₀.obj (K ⊗ L)) =
      α.app (E ⊗ M) ≫ a'.map (Lg.map (adj₀.comparisonMap b₀ K L)) :=
    α.naturality _
  have key : Lg'.map ((adj₀.comp adjf).comparisonMap (adja.comp b₀) K L) ≫
      α.app (a₀.obj (K ⊗ L)) =
      (δ Lg' (Lf.obj E) (a.obj M) ≫ ((squareCompositeIso eg ef).inv.app E ⊗ₘ α.app M) ≫
        adjf'.comparisonMap adja' (Lg.obj E) (Lg.obj M)) ≫
          a'.map (inv (δ Lg E M) ≫ Lg.map (adj₀.comparisonMap b₀ K L)) := by
    rw [Adjunction.comparisonMap_comp, Functor.map_comp, Category.assoc, hn, ← hbc]
    simp only [Category.assoc, Functor.map_comp, Functor.map_inv, IsIso.hom_inv_id_assoc]
    rfl
  rw [← isIso_comp_right_iff _ (α.app (a₀.obj (K ⊗ L))), key, isIso_comp_left_iff,
    Functor.map_comp, isIso_comp_left_iff]

end Stacks.CategoryTheory.BaseChange

end
