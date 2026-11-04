module

public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapBaseChange
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomDual
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap

/-!
# Testing the comparison map against a dualizable object

Let `F : C ⥤ D` be a strong monoidal functor with right adjoint `G`, whose projection maps
`K ⊗ G M ⟶ G (F K ⊗ M)` are invertible, and let `a` be a right adjoint of `G`. For an exact
pairing `(P, P')` in `D` the functor `W = G((a -) ⊗ P')` is right adjoint to `- ⊗ G P`, and
morphisms `P ⟶ F J ⊗ a K` are global sections of `J ⊗ W K`. Under these identifications
postcomposition with the comparison map `F J ⊗ a K ⟶ a (J ⊗ K)` becomes postcomposition with
the tensor–hom diagonal `J ⊗ W K ⟶ W (J ⊗ K)` of the adjunction `(- ⊗ G P) ⊣ W`. This is the
formal part of the proof of part (3) of [Stacks, Tag 0AA8].

## Main definitions

* `CategoryTheory.Adjunction.tensorRightDiagonal` — the diagonal `J ⊗ W K ⟶ W (J ⊗ K)` of an
  adjunction `(- ⊗ Q) ⊣ W`, the adjoint transpose of `J ⊗ (W K ⊗ Q) ⟶ J ⊗ K`.
* `CategoryTheory.Adjunction.dualTestAdjunction` — the adjunction `(- ⊗ G P) ⊣ G((a -) ⊗ P')`.

## Main results

* `CategoryTheory.Adjunction.bijective_comp_comparisonMap_iff` — postcomposition with the
  comparison map is bijective on morphisms out of `P` if and only if postcomposition with the
  diagonal of `dualTestAdjunction` is bijective on global sections.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

namespace Adjunction

/-! ### The diagonal of an adjunction `(- ⊗ Q) ⊣ W` -/

section Diagonal

variable {Q : C} {W : C ⥤ C} (adjQ : tensorRight Q ⊣ W)

/-- **The tensor–hom diagonal** `J ⊗ W K ⟶ W (J ⊗ K)` of an adjunction `(- ⊗ Q) ⊣ W`: the
adjoint transpose of the associator followed by `J` tensored with the counit at `K`. -/
def tensorRightDiagonal (J K : C) : J ⊗ W.obj K ⟶ W.obj (J ⊗ K) :=
  adjQ.homEquiv _ _ ((α_ J (W.obj K) Q).hom ≫ J ◁ adjQ.counit.app K)

/-- The defining equation of the diagonal. -/
@[reassoc]
lemma tensorRightDiagonal_whiskerRight_comp_counit (J K : C) :
    adjQ.tensorRightDiagonal J K ▷ Q ≫ adjQ.counit.app (J ⊗ K) =
      (α_ J (W.obj K) Q).hom ≫ J ◁ adjQ.counit.app K := by
  have h := (adjQ.homEquiv _ _).symm_apply_apply
    ((α_ J (W.obj K) Q).hom ≫ J ◁ adjQ.counit.app K)
  rwa [Adjunction.homEquiv_counit] at h

/-- A morphism into `W (J ⊗ K)` with the defining property of the diagonal is the diagonal. -/
lemma eq_tensorRightDiagonal {J K : C} (θ : J ⊗ W.obj K ⟶ W.obj (J ⊗ K))
    (h : θ ▷ Q ≫ adjQ.counit.app (J ⊗ K) = (α_ J (W.obj K) Q).hom ≫ J ◁ adjQ.counit.app K) :
    θ = adjQ.tensorRightDiagonal J K := by
  apply (adjQ.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact h.trans (adjQ.tensorRightDiagonal_whiskerRight_comp_counit J K).symm

end Diagonal

/-! ### The dual test adjunction -/

section DualTest

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal]
  [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] {a : C ⥤ D} (adj₂ : G ⊣ a)
  (P P' : D) [ExactPairing P P']

/-- The projection maps at `P`, as an isomorphism `- ⊗ G P ≅ G (F (-) ⊗ P)`. -/
def projectionRightIso : tensorRight (G.obj P) ≅ (F ⋙ tensorRight P) ⋙ G :=
  NatIso.ofComponents (fun K => asIso (adj.projectionMap K P))
    (fun f => adj.projectionMap_whiskerRight f P)

/-- The component of `projectionRightIso` at `K` is the projection map `K ⊗ G P ⟶ G (F K ⊗ P)`. -/
@[simp]
lemma projectionRightIso_hom_app (K : C) :
    (adj.projectionRightIso P).hom.app K = adj.projectionMap K P :=
  rfl

/-- **The adjunction `(- ⊗ G P) ⊣ G ((a -) ⊗ P')`** for an exact pairing `(P, P')`: the
composite of `F ⊣ G`, `(- ⊗ P) ⊣ (- ⊗ P')` and `G ⊣ a`, transported along the projection
maps. -/
def dualTestAdjunction : tensorRight (G.obj P) ⊣ a ⋙ tensorRight P' ⋙ G :=
  ((adj.comp (tensorRightAdjunction P P')).comp adj₂).ofNatIsoLeft
    (adj.projectionRightIso P).symm

/-- The counit of `dualTestAdjunction` at `K` is the projection map, followed by `G` applied to
the counit of `F ⊣ G` and the evaluation of the pairing `(P, P')`, followed by the counit of
`G ⊣ a`. -/
lemma dualTestAdjunction_counit_app (K : C) :
    (adj.dualTestAdjunction adj₂ P P').counit.app K =
      adj.projectionMap (G.obj (a.obj K ⊗ P')) P ≫
        G.map (adj.counit.app (a.obj K ⊗ P') ▷ P ≫ (α_ (a.obj K) P' P).hom ≫
          a.obj K ◁ ε_ P P' ≫ (ρ_ (a.obj K)).hom) ≫ adj₂.counit.app K := by
  simp [dualTestAdjunction, tensorRightAdjunction_counit_app]

/-- The composite `J ⊗ G (a K ⊗ P') ⟶ G (F J ⊗ (a K ⊗ P')) ⟶ G (a (J ⊗ K) ⊗ P')` of the
projection map and the comparison map tensored with `P'`. -/
def dualTestComparison (J K : C) :
    J ⊗ G.obj (a.obj K ⊗ P') ⟶ G.obj (a.obj (J ⊗ K) ⊗ P') :=
  adj.projectionMap J (a.obj K ⊗ P') ≫
    G.map ((α_ (F.obj J) (a.obj K) P').inv ≫ adj.comparisonMap adj₂ J K ▷ P')

/-- The adjoint transpose of `dualTestComparison` under `F ⊣ G`. -/
@[reassoc]
lemma map_dualTestComparison_comp_counit (J K : C) :
    F.map (adj.dualTestComparison adj₂ P' J K) ≫ adj.counit.app (a.obj (J ⊗ K) ⊗ P') =
      δ F J (G.obj (a.obj K ⊗ P')) ≫ F.obj J ◁ adj.counit.app (a.obj K ⊗ P') ≫
        (α_ (F.obj J) (a.obj K) P').inv ≫ adj.comparisonMap adj₂ J K ▷ P' := by
  have hc := adj.counit.naturality
    ((α_ (F.obj J) (a.obj K) P').inv ≫ adj.comparisonMap adj₂ J K ▷ P')
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc
  rw [dualTestComparison, F.map_comp, assoc, hc, map_projectionMap_comp_counit_assoc]

/-- The comparison map commutes with the evaluation of the pairing `(P, P')`. -/
@[reassoc]
lemma whiskerRight_whiskerRight_comp_evaluation {X Y : D} (h : X ⟶ Y) :
    (h ▷ P') ▷ P ≫ (α_ Y P' P).hom ≫ Y ◁ ε_ P P' ≫ (ρ_ Y).hom =
      (α_ X P' P).hom ≫ X ◁ ε_ P P' ≫ (ρ_ X).hom ≫ h := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- For `c : F M ⟶ L ⊗ P'`, tensoring `δ F J M ≫ F J ◁ c` with `P` and evaluating the pairing
`(P, P')` agrees with tensoring `δ F J M` with `P` and evaluating after `c` in the second
factor. -/
lemma dualTest_coherence (J : C) (M : C) (L : D) (c : F.obj M ⟶ L ⊗ P') :
    ((δ F J M ≫ F.obj J ◁ c ≫ (α_ (F.obj J) L P').inv) ▷ P ≫
        (α_ (F.obj J ⊗ L) P' P).hom ≫ (F.obj J ⊗ L) ◁ ε_ P P' ≫ (ρ_ (F.obj J ⊗ L)).hom) =
      δ F J M ▷ P ≫ (α_ (F.obj J) (F.obj M) P).hom ≫
        F.obj J ◁ (c ▷ P ≫ (α_ L P' P).hom ≫ L ◁ ε_ P P' ≫ (ρ_ L).hom) := by
  simp only [comp_whiskerRight, assoc, MonoidalCategory.whiskerLeft_comp]
  congr 1
  monoidal

/-- **The composite of the projection map and the comparison map is the diagonal** of
`dualTestAdjunction`. -/
theorem dualTestComparison_eq (J K : C) :
    adj.dualTestComparison adj₂ P' J K =
      (adj.dualTestAdjunction adj₂ P P').tensorRightDiagonal J K := by
  refine (adj.dualTestAdjunction adj₂ P P').eq_tensorRightDiagonal _ ?_
  rw [dualTestAdjunction_counit_app, dualTestAdjunction_counit_app]
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj]
  rw [adj.projectionMap_whiskerRight_assoc, ← G.map_comp_assoc, ← comp_whiskerRight_assoc,
    map_dualTestComparison_comp_counit]
  simp only [comp_whiskerRight, assoc]
  rw [whiskerRight_whiskerRight_comp_evaluation]
  set M := G.obj (a.obj K ⊗ P')
  set c := adj.counit.app (a.obj K ⊗ P')
  set Ψ := c ▷ P ≫ (α_ (a.obj K) P' P).hom ≫ a.obj K ◁ ε_ P P' ≫ (ρ_ (a.obj K)).hom
  have hΦ := congrArg G.map (dualTest_coherence P P' J M (a.obj K) c)
  simp only [G.map_comp, comp_whiskerRight, assoc] at hΦ
  simp only [G.map_comp, assoc]
  rw [map_comparisonMap_comp_counit, reassoc_of% hΦ]
  have h₂ : G.map (F.obj J ◁ Ψ) ≫ inv (adj.projectionMap J (a.obj K)) =
      inv (adj.projectionMap J (F.obj M ⊗ P)) ≫ J ◁ G.map Ψ := by
    rw [IsIso.comp_inv_eq, assoc, adj.whiskerLeft_projectionMap, IsIso.inv_hom_id_assoc]
  have h₃ : adj.projectionMap (J ⊗ M) P ≫ G.map (δ F J M ▷ P) =
      (α_ J M (G.obj P)).hom ≫ J ◁ adj.projectionMap M P ≫ adj.projectionMap J (F.obj M ⊗ P) ≫
        G.map (α_ (F.obj J) (F.obj M) P).inv := by
    rw [adj.projectionMap_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h₃, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, id_comp, reassoc_of% h₂,
    IsIso.hom_inv_id_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp]
  rfl

/-- **Morphisms out of `P` are global sections of `G (- ⊗ P')`**: the bijection
`(P ⟶ Z) ≃ (𝟙_C ⟶ G (Z ⊗ P'))` of the exact pairing `(P, P')` and the adjunction `F ⊣ G`. -/
def homEquivDualTest (Z : D) : (P ⟶ Z) ≃ (𝟙_ C ⟶ G.obj (Z ⊗ P')) :=
  ((Iso.homCongr (λ_ P) (Iso.refl Z)).symm.trans (tensorRightHomEquiv (𝟙_ D) P P' Z)).trans
    ((Iso.homCongr (Functor.Monoidal.εIso F) (Iso.refl _)).trans (adj.homEquiv _ _))

omit [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] in
/-- `homEquivDualTest` is natural in the target. -/
lemma homEquivDualTest_comp {Z₁ Z₂ : D} (u : P ⟶ Z₁) (φ : Z₁ ⟶ Z₂) :
    adj.homEquivDualTest P P' Z₂ (u ≫ φ) = adj.homEquivDualTest P P' Z₁ u ≫ G.map (φ ▷ P') := by
  simp only [homEquivDualTest, Equiv.trans_apply, Iso.homCongr_symm, Iso.refl_symm,
    Iso.homCongr_apply, Iso.refl_hom, comp_id, Iso.symm_inv, assoc,
    ← tensorRightHomEquiv_naturality, ← Adjunction.homEquiv_naturality_right]

/-- Bijectivity transfers along bijections intertwining two maps. -/
lemma _root_.Function.bijective_iff_of_equiv {α β α' β' : Sort*} (e₁ : α ≃ α') (e₂ : β ≃ β')
    (f : α → β) (g : α' → β') (h : ∀ x, e₂ (f x) = g (e₁ x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hg : g = e₂ ∘ f ∘ e₁.symm := funext fun x => by simp [h]
  rw [hg, Equiv.comp_bijective, Equiv.bijective_comp]

/-- **Testing the comparison map against a dualizable object.** Postcomposition with the
comparison map `F J ⊗ a K ⟶ a (J ⊗ K)` is bijective on morphisms out of `P` if and only if
postcomposition with the diagonal `J ⊗ W K ⟶ W (J ⊗ K)` of the adjunction
`(- ⊗ G P) ⊣ W = G ((a -) ⊗ P')` is bijective on global sections. -/
theorem bijective_comp_comparisonMap_iff (J K : C) :
    Function.Bijective (fun u : P ⟶ F.obj J ⊗ a.obj K => u ≫ adj.comparisonMap adj₂ J K) ↔
      Function.Bijective (fun v : 𝟙_ C ⟶ J ⊗ G.obj (a.obj K ⊗ P') =>
        v ≫ (adj.dualTestAdjunction adj₂ P P').tensorRightDiagonal J K) := by
  rw [Function.bijective_iff_of_equiv (adj.homEquivDualTest P P' _) (adj.homEquivDualTest P P' _)
    _ (fun v => v ≫ G.map (adj.comparisonMap adj₂ J K ▷ P'))
    (fun u => adj.homEquivDualTest_comp P P' u _)]
  let i := asIso (adj.projectionMap J (a.obj K ⊗ P')) ≪≫ G.mapIso (α_ (F.obj J) (a.obj K) P').symm
  refine (Function.bijective_iff_of_equiv (Iso.homCongr (Iso.refl _) i) (Equiv.refl _)
    (fun v : 𝟙_ C ⟶ J ⊗ G.obj (a.obj K ⊗ P') =>
      v ≫ (adj.dualTestAdjunction adj₂ P P').tensorRightDiagonal J K)
    (fun w => w ≫ G.map (adj.comparisonMap adj₂ J K ▷ P')) fun v => ?_).symm
  rw [← dualTestComparison_eq, dualTestComparison]
  simp [i]

end DualTest

end Adjunction

end CategoryTheory

end
