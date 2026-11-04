module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapDualTest

/-!
# The tensor–hom diagonal at an object approximated by dualizable ones

Let `C` be a pretriangulated monoidal category and let `(- ⊗ Q) ⊣ W`. The diagonal
`J ⊗ W K ⟶ W (J ⊗ K)` (`CategoryTheory.Adjunction.tensorRightDiagonal`) is invertible when `Q`
is dualizable. Suppose instead that `Q` is approximated by dualizable objects: for every `N`
there is a distinguished triangle `Q' ⟶ Q ⟶ C'' ⟶ Q'[1]` with `Q'` dualizable and `C''` in
cohomological degrees `≤ -N`, for a pair of cohomological-degree predicates `LE`, `GE` with the
usual orthogonality and compatibility with the tensor product. Then, for `K` bounded below and
`J` of Tor amplitude bounded below, postcomposition with the diagonal is bijective on global
sections `𝟙 ⟶ J ⊗ W K`.

This is the argument of [Stacks, Tag 0ATK] for a pseudo-coherent `Q` (approximated by perfect
complexes), a bounded below `K` and a `J` of finite Tor dimension, made at the level of an
abstract adjunction: the diagonal at `Q` and at `Q'` are compared through the mate
`W ⟶ W'` of `Q' ⟶ Q`, whose cone is concentrated in high degrees.

## Main results

* `CategoryTheory.Adjunction.tensorRightDiagonal_comp_tensorRightMate` — naturality of the
  diagonal in `Q`.
* `CategoryTheory.Adjunction.tensorRightDiagonal_tensorRightAdjunction` — for an exact pairing
  the diagonal is the associator.
* `CategoryTheory.Adjunction.bijective_comp_tensorRightDiagonal_of_approximation` — the
  bijectivity statement.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory Pretriangulated

/-! ### Two exactness consequences in a pretriangulated category -/

namespace Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a distinguished triangle `A ⟶ B ⟶ Z ⟶ A[1]`, postcomposition with `A ⟶ B` is bijective on
morphisms out of `U` when `U` receives no nonzero morphism into `Z` or `Z[-1]`. -/
theorem bijective_comp_mor₁_of_distTriang {T : Triangle C} (hT : T ∈ distTriang C) {U : C}
    (h₁ : ∀ z : U ⟶ T.obj₃, z = 0) (h₂ : ∀ z : U ⟶ T.obj₃⟦(-1 : ℤ)⟧, z = 0) :
    Function.Bijective (fun x : U ⟶ T.obj₁ => x ≫ T.mor₁) := by
  refine ⟨fun x x' hxx' => ?_, fun y => ?_⟩
  · have h0 : (x - x') ≫ T.mor₁ = 0 := by
      simp only [Preadditive.sub_comp]
      exact sub_eq_zero.mpr hxx'
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang _ hT)
      (x - x' : U ⟶ T.invRotate.obj₂) h0
    have hz : x - x' = 0 := hg.trans (by rw [h₂ g]; exact Limits.zero_comp)
    exact sub_eq_zero.mp hz
  · obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ hT y (h₁ _)
    exact ⟨x, hx.symm⟩

/-- In a distinguished triangle `A ⟶ B ⟶ Z ⟶ A[1]`, `U` receives no nonzero morphism into `Z`
as soon as postcomposition with `A ⟶ B` is surjective on morphisms out of `U` and postcomposition
with `A[1] ⟶ B[1]` is injective on them. -/
theorem eq_zero_of_distTriang {T : Triangle C} (hT : T ∈ distTriang C) {U : C}
    (hsurj : ∀ y : U ⟶ T.obj₂, ∃ x : U ⟶ T.obj₁, x ≫ T.mor₁ = y)
    (hinj : ∀ t : U ⟶ T.obj₁⟦(1 : ℤ)⟧, t ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 → t = 0) (z : U ⟶ T.obj₃) :
    z = 0 := by
  have h₁ : z ≫ T.mor₃ = 0 :=
    hinj _ (by rw [assoc, comp_distTriang_mor_zero₃₁ _ hT, comp_zero])
  obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₃ _ hT z h₁
  obtain ⟨x, rfl⟩ := hsurj y
  rw [assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero]

omit [HasZeroObject C] [Pretriangulated C] in
/-- Injectivity of postcomposition with `f[1]` on morphisms out of `U` follows from injectivity
of postcomposition with `f` on morphisms out of `U[-1]`. -/
theorem eq_zero_of_comp_shift_eq_zero {A B U : C} (f : A ⟶ B)
    (h : ∀ s : U⟦(-1 : ℤ)⟧ ⟶ A, s ≫ f = 0 → s = 0) (t : U ⟶ A⟦(1 : ℤ)⟧)
    (ht : t ≫ f⟦(1 : ℤ)⟧' = 0) : t = 0 := by
  let e : (U⟦(-1 : ℤ)⟧ : C)⟦(1 : ℤ)⟧ ≅ U :=
    (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by simp)).app U
  obtain ⟨s, hs⟩ : ∃ s : (U⟦(-1 : ℤ)⟧ : C) ⟶ A, s⟦(1 : ℤ)⟧' = e.hom ≫ t :=
    ⟨(shiftFunctor C (1 : ℤ)).preimage _, (shiftFunctor C (1 : ℤ)).map_preimage _⟩
  have hsf : s ≫ f = 0 := by
    refine (shiftFunctor C (1 : ℤ)).map_injective ?_
    rw [Functor.map_comp, hs, assoc, ht, comp_zero, Functor.map_zero]
  have h0 : e.hom ≫ t = 0 := by rw [← hs, h s hsf, Functor.map_zero]
  rw [← cancel_epi e.hom, h0, comp_zero]

end Pretriangulated

namespace Adjunction

variable {C : Type*} [Category C] [MonoidalCategory C]

/-! ### The mate of a morphism `Q' ⟶ Q` -/

section Mate

variable {Q Q' : C} {W W' : C ⥤ C} (adjQ : tensorRight Q ⊣ W) (adjQ' : tensorRight Q' ⊣ W')
  (u : Q' ⟶ Q)

/-- The morphism `W K ⟶ W' K` induced by `u : Q' ⟶ Q`: the adjoint transpose of
`W K ⊗ Q' ⟶ W K ⊗ Q ⟶ K`. -/
def tensorRightMate (K : C) : W.obj K ⟶ W'.obj K :=
  adjQ'.homEquiv _ _ (W.obj K ◁ u ≫ adjQ.counit.app K)

/-- The adjoint transpose of `tensorRightMate adjQ adjQ' u K` is `W K ◁ u ≫ adjQ.counit.app K`:
whiskering the mate by `Q'` and composing with the counit of `adjQ'` gives
`W K ⊗ Q' ⟶ W K ⊗ Q ⟶ K`. -/
@[reassoc]
lemma tensorRightMate_whiskerRight_comp_counit (K : C) :
    tensorRightMate adjQ adjQ' u K ▷ Q' ≫ adjQ'.counit.app K =
      W.obj K ◁ u ≫ adjQ.counit.app K := by
  have h := (adjQ'.homEquiv _ _).symm_apply_apply (W.obj K ◁ u ≫ adjQ.counit.app K)
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- Postcomposition with the mate is precomposition with `T ◁ u` on adjoint transposes. -/
lemma homEquiv_symm_comp_tensorRightMate {T K : C} (x : T ⟶ W.obj K) :
    (adjQ'.homEquiv _ _).symm (x ≫ tensorRightMate adjQ adjQ' u K) =
      T ◁ u ≫ (adjQ.homEquiv _ _).symm x := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  dsimp only [Functor.flip_obj_map, curriedTensor_map_app]
  rw [comp_whiskerRight, assoc, tensorRightMate_whiskerRight_comp_counit,
    whisker_exchange_assoc]

/-- **The diagonal is natural in `Q`.** -/
lemma tensorRightDiagonal_comp_tensorRightMate (J K : C) :
    adjQ.tensorRightDiagonal J K ≫ tensorRightMate adjQ adjQ' u (J ⊗ K) =
      J ◁ tensorRightMate adjQ adjQ' u K ≫ adjQ'.tensorRightDiagonal J K := by
  apply (adjQ'.homEquiv _ _).symm.injective
  rw [homEquiv_symm_comp_tensorRightMate, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.flip_obj_map, curriedTensor_map_app]
  rw [tensorRightDiagonal_whiskerRight_comp_counit, comp_whiskerRight, assoc,
    tensorRightDiagonal_whiskerRight_comp_counit, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp, tensorRightMate_whiskerRight_comp_counit,
    MonoidalCategory.whiskerLeft_comp, associator_naturality_right_assoc]

end Mate

/-- **For an exact pairing the diagonal is the associator.** -/
lemma tensorRightDiagonal_tensorRightAdjunction (Q Q'' : C) [ExactPairing Q Q''] (J K : C) :
    (tensorRightAdjunction Q Q'').tensorRightDiagonal J K = (α_ J K Q'').inv := by
  refine ((tensorRightAdjunction Q Q'').eq_tensorRightDiagonal _ ?_).symm
  dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Functor.flip_obj_obj,
    curriedTensor_obj_obj]
  rw [tensorRightAdjunction_counit_app, tensorRightAdjunction_counit_app]
  monoidal

/-! ### Approximation by dualizable objects -/

section Approximation

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ X : C, (tensorRight X).PreservesZeroMorphisms]

/-- **The diagonal at an object approximated by dualizable ones.** Let `(- ⊗ Q) ⊣ W`, and let
`LE`, `GE` be predicates on `C` indexed by `ℤ`, read as "concentrated in degrees `≤ p`" and
"`≥ q`", stable under the shift as `[-1]` shifts degrees up, with `LE p ⊗ LE q ⊆ LE (p + q)`,
`𝟙 ∈ LE 0`, `Hom(LE p, GE q) = 0` for `p < q`, and `GE q` detected by orthogonality to
`LE (q - 1)`. Suppose tensoring on the left carries distinguished triangles to distinguished
triangles, and that for every `N` there is a distinguished triangle `Q' ⟶ Q ⟶ C'' ⟶ Q'[1]` with
`Q'` dualizable and `C'' ∈ LE (-N)`. Then for `K ∈ GE b` and `J` with `J ⊗ GE m ⊆ GE (m + a)`,
postcomposition with the diagonal `J ⊗ W K ⟶ W (J ⊗ K)` is bijective on morphisms out of `𝟙`. -/
theorem bijective_comp_tensorRightDiagonal_of_approximation {Q : C} {W : C ⥤ C}
    (adjQ : tensorRight Q ⊣ W) (LE GE : ℤ → C → Prop)
    (hLEshift : ∀ (p : ℤ) (X : C), LE p X → LE (p + 1) (X⟦(-1 : ℤ)⟧))
    (hLEtensor : ∀ (p q : ℤ) (X Y : C), LE p X → LE q Y → LE (p + q) (X ⊗ Y))
    (hLEunit : LE 0 (𝟙_ C))
    (hGEshift : ∀ (m : ℤ) (X : C), GE m X → GE (m + 1) (X⟦(-1 : ℤ)⟧))
    (horth : ∀ (p q : ℤ) (X Y : C), p < q → LE p X → GE q Y → ∀ f : X ⟶ Y, f = 0)
    (hdetect : ∀ (m : ℤ) (Z : C), (∀ T : C, LE (m - 1) T → ∀ f : T ⟶ Z, f = 0) → GE m Z)
    (htensor : ∀ (T : C) (Tr : Triangle C), Tr ∈ distTriang C →
      ∃ w : T ⊗ Tr.obj₃ ⟶ (T ⊗ Tr.obj₁)⟦(1 : ℤ)⟧,
        Triangle.mk (T ◁ Tr.mor₁) (T ◁ Tr.mor₂) w ∈ distTriang C)
    (happrox : ∀ N : ℤ, ∃ (Q' Q'' C'' : C) (_ : ExactPairing Q' Q'') (u : Q' ⟶ Q) (v : Q ⟶ C'')
      (w : C'' ⟶ Q'⟦(1 : ℤ)⟧), Triangle.mk u v w ∈ distTriang C ∧ LE (-N) C'')
    (J K : C) (a b : ℤ) (hJ : ∀ (m : ℤ) (X : C), GE m X → GE (m + a) (J ⊗ X)) (hK : GE b K) :
    Function.Bijective (fun φ : 𝟙_ C ⟶ J ⊗ W.obj K => φ ≫ adjQ.tensorRightDiagonal J K) := by
  obtain ⟨Q', Q'', C'', hP, u, v, w, hT, hC⟩ := happrox (2 - a - b)
  let adj' := tensorRightAdjunction Q' Q''
  let r := tensorRightMate adjQ adj' u
  -- the cone of the mate at an object of `GE c` lies in `GE (c + N - 1)`
  have hcone : ∀ (c : ℤ) (L : C), GE c L → ∀ (Z : C) (g : (tensorRight Q'').obj L ⟶ Z)
      (h : Z ⟶ (W.obj L)⟦(1 : ℤ)⟧), Triangle.mk (r L) g h ∈ distTriang C →
      GE (c + (2 - a - b) - 1) Z := by
    intro c L hL Z g h hZ
    refine hdetect _ Z fun T hT' z => Pretriangulated.eq_zero_of_distTriang hZ ?_ ?_ z
    · intro y
      obtain ⟨w₁, hw₁⟩ := htensor T _ hT
      obtain ⟨g'', hg''⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hw₁)
        (((adj'.homEquiv _ _).symm y : T ⊗ Q' ⟶ L))
        (horth _ c _ L (by omega) (hLEshift _ _ (hLEtensor _ _ T C'' hT' hC)) hL _)
      let g₀ : T ⊗ Q ⟶ L := g''
      refine ⟨adjQ.homEquiv _ _ g₀, (adj'.homEquiv _ _).symm.injective ?_⟩
      change (adj'.homEquiv _ _).symm (adjQ.homEquiv _ _ g₀ ≫ tensorRightMate adjQ adj' u L) = _
      rw [homEquiv_symm_comp_tensorRightMate, Equiv.symm_apply_apply]
      exact hg''.symm
    · refine Pretriangulated.eq_zero_of_comp_shift_eq_zero (r L) fun s hs => ?_
      have hs' : T⟦(-1 : ℤ)⟧ ◁ u ≫ (adjQ.homEquiv _ _).symm s = 0 := by
        rw [← homEquiv_symm_comp_tensorRightMate]
        show (adj'.homEquiv _ _).symm (s ≫ r L) = 0
        rw [hs, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
      obtain ⟨w₁, hw₁⟩ := htensor (T⟦(-1 : ℤ)⟧) _ hT
      obtain ⟨g'', hg''⟩ := Triangle.yoneda_exact₂ _ hw₁ _ hs'
      have hg0 : g'' = 0 :=
        horth _ c _ L (by omega) (hLEtensor _ _ _ C'' (hLEshift _ T hT') hC) hL _
      rw [hg0, comp_zero] at hg''
      apply (adjQ.homEquiv _ _).symm.injective
      rw [hg'', Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  obtain ⟨Z₁, g₁, h₁, hZ₁⟩ := distinguished_cocone_triangle (r K)
  obtain ⟨Z₂, g₂, h₂, hZ₂⟩ := distinguished_cocone_triangle (r (J ⊗ K))
  have hGE₁ := hJ _ _ (hcone b K hK Z₁ g₁ h₁ hZ₁)
  have hGE₂ := hcone (b + a) (J ⊗ K) (hJ b K hK) Z₂ g₂ h₂ hZ₂
  obtain ⟨w₁, hw₁⟩ := htensor J _ hZ₁
  have hbij : ∀ (Tr : Triangle C), Tr ∈ distTriang C → ∀ m : ℤ, 0 < m → GE m Tr.obj₃ →
      Function.Bijective (fun x : 𝟙_ C ⟶ Tr.obj₁ => x ≫ Tr.mor₁) := fun Tr hTr m hm hGE =>
    Pretriangulated.bijective_comp_mor₁_of_distTriang hTr
      (fun z => horth 0 m _ _ hm hLEunit hGE z)
      (fun z => horth 0 (m + 1) _ _ (by omega) hLEunit (hGEshift _ _ hGE) z)
  have hb₁ := hbij _ hw₁ _ (by omega) hGE₁
  have hb₂ := hbij _ hZ₂ _ (by omega) hGE₂
  have hdiag : IsIso (adj'.tensorRightDiagonal J K) := by
    rw [tensorRightDiagonal_tensorRightAdjunction]
    infer_instance
  have hcomp : (fun φ : 𝟙_ C ⟶ J ⊗ (tensorRight Q'').obj K => φ ≫ adj'.tensorRightDiagonal J K) ∘
      (fun φ : 𝟙_ C ⟶ J ⊗ W.obj K => φ ≫ J ◁ r K) =
      (fun φ : 𝟙_ C ⟶ W.obj (J ⊗ K) => φ ≫ r (J ⊗ K)) ∘
      (fun φ : 𝟙_ C ⟶ J ⊗ W.obj K => φ ≫ adjQ.tensorRightDiagonal J K) := by
    funext φ
    simp only [Function.comp_apply, assoc, r, tensorRightDiagonal_comp_tensorRightMate]
  have hiso : Function.Bijective
      (fun φ : 𝟙_ C ⟶ J ⊗ (tensorRight Q'').obj K => φ ≫ adj'.tensorRightDiagonal J K) :=
    ⟨fun x y hxy => (cancel_mono (adj'.tensorRightDiagonal J K)).1 hxy,
      fun y => ⟨y ≫ inv (adj'.tensorRightDiagonal J K), by simp⟩⟩
  have h : Function.Bijective
      ((fun φ : 𝟙_ C ⟶ J ⊗ (tensorRight Q'').obj K => φ ≫ adj'.tensorRightDiagonal J K) ∘
        (fun φ : 𝟙_ C ⟶ J ⊗ W.obj K => φ ≫ J ◁ r K)) := hiso.comp hb₁
  rw [hcomp] at h
  exact (Function.Bijective.of_comp_iff' hb₂ _).mp h

end Approximation

end Adjunction

end CategoryTheory

end
