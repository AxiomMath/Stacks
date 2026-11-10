module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentInterface

/-!
# Transporting the 0DLA shape along a comparison of pullback assignments

Let `pull`, `comp` and `pull'`, `comp'` be two contravariant assignments of functors
`D b ⥤ D a`, `D' b ⥤ D' a` on a category `A`, each with a composition comparison. Let
`Φ a : D a ⥤ D' a` be functors and, for the morphisms `f` of a class `P`, let
`ε_f : pull f ⋙ Φ a ≅ Φ b ⋙ pull' f` be isomorphisms compatible with the composition
comparisons. If `Φ` is bijective on morphisms between objects satisfying `Q`, commutes with the
shifts, carries `Q` to `Q'`, and its essential image descends along `P`, then the shape of Stacks
0DLA (`CategoryTheory.HypercoverDerivedDescent`) for `pull'` gives it for `pull`, provided that
the augmentation, the faces and the last vertices of the hypercoverings in question lie in `P` and
that `Q` is stable under pullback along `P` and under shifts.

This is the formal part of the transfer of Stacks 0DLA from the spaces-étale sites to the small
étale sites (`AlgebraicGeometry.Space.SmallEtaleHypercoverDescentOfSpacesEtale`). Nothing here is
registered.

## Main definitions and results

* `CategoryTheory.HypercoverComparisonCompCompatible`: the compatibility of the `ε` with the
  composition comparisons, in the shape of the last clause of
  `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.
* `CategoryTheory.HypercoverComparisonCompCompatible.edgeRestrict` and
  `CategoryTheory.HypercoverComparisonCompCompatible.isHypercoverDescentCocycle`: the transport
  of the restrictions of a gluing map and of the cocycle condition.
* `CategoryTheory.hypercoverDerivedDescent_of_comparison`: the transfer.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

/-- A functor bijective on the four hom-sets between and on two objects lifts every isomorphism
between their images. -/
theorem Functor.exists_iso_map_hom_of_bijective {C : Type u₄} [Category.{v₄} C]
    {C' : Type u₅} [Category.{v₅} C'] (F : C ⥤ C') {X Y : C}
    (hXY : Function.Bijective (fun g : X ⟶ Y => F.map g))
    (hYX : Function.Bijective (fun g : Y ⟶ X => F.map g))
    (hXX : Function.Bijective (fun g : X ⟶ X => F.map g))
    (hYY : Function.Bijective (fun g : Y ⟶ Y => F.map g)) (φ : F.obj X ≅ F.obj Y) :
    ∃ e : X ≅ Y, F.map e.hom = φ.hom := by
  obtain ⟨a, ha⟩ := hXY.2 φ.hom
  obtain ⟨b, hb⟩ := hYX.2 φ.inv
  refine ⟨⟨a, b, hXX.1 ?_, hYY.1 ?_⟩, ha⟩
  · simp [ha, hb]
  · simp [ha, hb]

/-- Negative self-extensions vanish on an object isomorphic to the image `F X` of an object `X`
without negative self-extensions, when `F` commutes with the shift `⟦t⟧` at `X` and is surjective
on `X ⟶ X⟦t⟧`. -/
theorem Functor.subsingleton_hom_shift_of_surjective {C : Type u₄} [Category.{v₄} C]
    {C' : Type u₅} [Category.{v₅} C'] [HasShift C ℤ] [HasShift C' ℤ] (F : C ⥤ C') {X : C}
    {X' : C'} (t : ℤ) (e : X' ≅ F.obj X) (σ : F.obj (X⟦t⟧) ≅ (F.obj X)⟦t⟧)
    (hF : Function.Surjective (fun g : X ⟶ X⟦t⟧ => F.map g)) (hX : Subsingleton (X ⟶ X⟦t⟧)) :
    Subsingleton (X' ⟶ X'⟦t⟧) := by
  have := hF.subsingleton
  exact (e.homCongr ((shiftFunctor C' t).mapIso e ≪≫ σ.symm)).injective.subsingleton

section Triangle

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
  (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)

/-- Along the composite itself, the triangle `CategoryTheory.hypercoverPullTriangle` is the
composition comparison. -/
theorem hypercoverPullTriangle_rfl {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    hypercoverPullTriangle pull comp (rfl : f ≫ g = f ≫ g) = comp f g := by
  simp only [hypercoverPullTriangle, eqToIso_refl, Iso.refl_trans]

end Triangle

section Comparison

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
  (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
  {D' : A → Type u₃} [∀ a, Category.{v₃} (D' a)]
  (pull' : ∀ {a b : A}, (a ⟶ b) → (D' b ⥤ D' a))
  (comp' : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull' (f ≫ g) ≅ pull' g ⋙ pull' f)
  (P : MorphismProperty A) (Φ : ∀ a, D a ⥤ D' a)
  (ε : ∀ {a b : A} (f : a ⟶ b), P f → (pull f ⋙ Φ a ≅ Φ b ⋙ pull' f))

/-- **The comparisons `ε` are compatible with the composition comparisons**: for `f`, `g` and
`f ≫ g` in `P`, the comparison for `f ≫ g` followed by `comp'` is `Φ` of `comp`, then the
comparison for `f`, then `pull' f` of the comparison for `g`. This is the shape of the last clause
of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`. -/
def HypercoverComparisonCompCompatible : Prop :=
  ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (hf : P f) (hg : P g) (hfg : P (f ≫ g)) (K : D c),
    (ε (f ≫ g) hfg).hom.app K ≫ (comp' f g).hom.app ((Φ c).obj K) =
      (Φ a).map ((comp f g).hom.app K) ≫ (ε f hf).hom.app ((pull g).obj K) ≫
        (pull' f).map ((ε g hg).hom.app K)

variable {pull comp pull' comp' P Φ ε}

/-- The compatibility of the comparisons with the composition comparisons, along a morphism
`k` only equal to a composite `f ≫ g`. -/
theorem HypercoverComparisonCompCompatible.pullTriangle_hom_app
    (h : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε) {a b c : A}
    {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) (hf : P f) (hg : P g) (hk' : P k)
    (K : D c) :
    (ε k hk').hom.app K ≫ (hypercoverPullTriangle pull' comp' hk).hom.app ((Φ c).obj K) =
      (Φ a).map ((hypercoverPullTriangle pull comp hk).hom.app K) ≫
        (ε f hf).hom.app ((pull g).obj K) ≫ (pull' f).map ((ε g hg).hom.app K) := by
  subst hk
  rw [hypercoverPullTriangle_rfl, hypercoverPullTriangle_rfl]
  exact h f g hf hg hk' K

/-- The inverse form of
`CategoryTheory.HypercoverComparisonCompCompatible.pullTriangle_hom_app`. -/
theorem HypercoverComparisonCompCompatible.pullTriangle_inv_app
    (h : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε) {a b c : A}
    {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) (hf : P f) (hg : P g) (hk' : P k)
    (K : D c) :
    (Φ a).map ((hypercoverPullTriangle pull comp hk).inv.app K) =
      (ε f hf).hom.app ((pull g).obj K) ≫ (pull' f).map ((ε g hg).hom.app K) ≫
        (hypercoverPullTriangle pull' comp' hk).inv.app ((Φ c).obj K) ≫
          (ε k hk').inv.app K := by
  rw [← cancel_epi ((Φ a).map ((hypercoverPullTriangle pull comp hk).hom.app K)),
    ← reassoc_of% (h.pullTriangle_hom_app hk hf hg hk' K)]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Iso.hom_inv_id_app_assoc,
    Functor.comp_obj]

/-- **The restriction of a transported gluing map**: the restriction along `e` of
`ε_s⁻¹ ≫ Φ(α) ≫ ε_t` is `ε_v⁻¹ ≫ Φ(α|_e) ≫ ε_w`. -/
theorem HypercoverComparisonCompCompatible.edgeRestrict
    (h : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε) {U₀ U₁ Z : A}
    {s t : U₁ ⟶ U₀} (hs : P s) (ht : P t) {K₀ : D U₀} (α : (pull s).obj K₀ ⟶ (pull t).obj K₀)
    (e : Z ⟶ U₁) (he : P e) {v w : Z ⟶ U₀} (hv : e ≫ s = v) (hw : e ≫ t = w) (hv' : P v)
    (hw' : P w) :
    hypercoverEdgeRestrict pull' comp'
        ((ε s hs).inv.app K₀ ≫ (Φ U₁).map α ≫ (ε t ht).hom.app K₀) e hv hw =
      (ε v hv').inv.app K₀ ≫ (Φ Z).map (hypercoverEdgeRestrict pull comp α e hv hw) ≫
        (ε w hw').hom.app K₀ := by
  have h1 := h.pullTriangle_hom_app hv he hs hv' K₀
  have h2 := h.pullTriangle_inv_app hw he ht hw' K₀
  have hn := (ε e he).hom.naturality α
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← cancel_epi ((ε v hv').hom.app K₀)]
  simp only [hypercoverEdgeRestrict, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp, h2]
  rw [reassoc_of% h1, reassoc_of% hn]
  simp

/-- **The cocycle condition is transported by the comparisons**: if `α` satisfies the cocycle
condition for `pull`, then `ε_s⁻¹ ≫ Φ(α) ≫ ε_t` satisfies it for `pull'`. -/
theorem HypercoverComparisonCompCompatible.isHypercoverDescentCocycle
    (h : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε)
    [P.IsStableUnderComposition] {U₀ U₁ U₂ : A} {s t : U₁ ⟶ U₀} {e₀₁ e₁₂ e₀₂ : U₂ ⟶ U₁}
    (hs : P s) (ht : P t) (h₀₁ : P e₀₁) (h₁₂ : P e₁₂) (h₀₂ : P e₀₂) {K₀ : D U₀}
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀)
    (hα : IsHypercoverDescentCocycle pull comp s t e₀₁ e₁₂ e₀₂ α) :
    IsHypercoverDescentCocycle pull' comp' s t e₀₁ e₁₂ e₀₂
      (((ε s hs).app K₀).symm ≪≫ (Φ U₁).mapIso α ≪≫ (ε t ht).app K₀) := by
  intro v₀ v₁ v₂ hv₀ hv₁ hv₁' hv₂ hv₀' hv₂'
  have p₀ : P v₀ := hv₀ ▸ P.comp_mem _ _ h₀₁ hs
  have p₁ : P v₁ := hv₁ ▸ P.comp_mem _ _ h₀₁ ht
  have p₂ : P v₂ := hv₂ ▸ P.comp_mem _ _ h₁₂ ht
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom]
  rw [h.edgeRestrict hs ht α.hom e₀₁ h₀₁ hv₀ hv₁ p₀ p₁,
    h.edgeRestrict hs ht α.hom e₁₂ h₁₂ hv₁' hv₂ p₁ p₂,
    h.edgeRestrict hs ht α.hom e₀₂ h₀₂ hv₀' hv₂' p₀ p₂, ← hα v₀ v₁ v₂ hv₀ hv₁ hv₁' hv₂ hv₀' hv₂']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]

/-- **The compatibility of the output is pulled back through the comparisons**: if
`β' : a₀'^*K' ≅ Φ(K₀)` is compatible with the transported gluing map, `γ : Φ(K) ≅ K'`, and
`β : a₀^*K ≅ K₀` is a preimage of `ε ≫ a₀'^*γ ≫ β'` under `Φ`, then `β` is compatible with `α`
as soon as `Φ` is injective on `s^*K₀ ⟶ t^*K₀`. -/
theorem HypercoverComparisonCompCompatible.isHypercoverDescentCompatible
    (h : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε)
    [P.IsStableUnderComposition] {X U₀ U₁ : A} {a₀ : U₀ ⟶ X} {s t : U₁ ⟶ U₀} (ha₀ : P a₀)
    (hs : P s) (ht : P t) {K₀ : D U₀} (α : (pull s).obj K₀ ≅ (pull t).obj K₀) (K : D X)
    (K' : D' X) (γ : (Φ X).obj K ≅ K') (β' : (pull' a₀).obj K' ≅ (Φ U₀).obj K₀)
    (hc' : IsHypercoverDescentCompatible pull' comp' a₀ s t
      (((ε s hs).app K₀).symm ≪≫ (Φ U₁).mapIso α ≪≫ (ε t ht).app K₀) K' β')
    (β : (pull a₀).obj K ≅ K₀)
    (hβ : (Φ U₀).map β.hom = (ε a₀ ha₀).hom.app K ≫ (pull' a₀).map γ.hom ≫ β'.hom)
    (hinj : Function.Injective (fun g : (pull s).obj K₀ ⟶ (pull t).obj K₀ => (Φ U₁).map g)) :
    IsHypercoverDescentCompatible pull comp a₀ s t α K β := by
  intro a₁ hs₁ ht₁
  have ha₁ : P a₁ := hs₁ ▸ P.comp_mem _ _ hs ha₀
  have hβ' : (Φ U₀).map β.inv = β'.inv ≫ (pull' a₀).map γ.inv ≫ (ε a₀ ha₀).inv.app K := by
    rw [← cancel_epi ((Φ U₀).map β.hom), ← Functor.map_comp, β.hom_inv_id, Functor.map_id, hβ]
    simp
  apply hinj
  change (Φ U₁).map (_ ≫ _ ≫ _ ≫ _) = (Φ U₁).map α.hom
  have hαΦ : (Φ U₁).map α.hom = (ε s hs).hom.app K₀ ≫
      (((ε s hs).app K₀).symm ≪≫ (Φ U₁).mapIso α ≪≫ (ε t ht).app K₀).hom ≫
        (ε t ht).inv.app K₀ := by
    simp
  rw [hαΦ, ← hc' a₁ hs₁ ht₁]
  have ns := NatIso.naturality_2 (ε s hs) β.inv
  have nt := NatIso.naturality_2 (ε t ht) β.hom
  have ns' := (hypercoverPullTriangle pull' comp' hs₁).inv.naturality γ.inv
  have nt' := (hypercoverPullTriangle pull' comp' ht₁).hom.naturality γ.hom
  simp only [Functor.comp_map, Functor.comp_obj] at ns nt ns' nt'
  have ts := h.pullTriangle_inv_app hs₁ hs ha₀ ha₁ K
  have tt := h.pullTriangle_hom_app ht₁ ht ha₀ ha₁ K
  have tt' : (Φ U₁).map ((hypercoverPullTriangle pull comp ht₁).hom.app K) =
      (ε a₁ ha₁).hom.app K ≫ (hypercoverPullTriangle pull' comp' ht₁).hom.app ((Φ X).obj K) ≫
        (pull' t).map ((ε a₀ ha₀).inv.app K) ≫ (ε t ht).inv.app ((pull a₀).obj K) := by
    rw [reassoc_of% tt, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, ← ns, ← nt, hβ', hβ, ts, tt']
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.comp_obj]
  rw [← (pull' s).map_comp_assoc ((ε a₀ ha₀).inv.app K) ((ε a₀ ha₀).hom.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    ← (pull' t).map_comp_assoc ((ε a₀ ha₀).inv.app K) ((ε a₀ ha₀).hom.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, reassoc_of% ns', ← reassoc_of% nt',
    ← (pull' a₁).map_comp_assoc γ.inv γ.hom, γ.inv_hom_id, Functor.map_id, Category.id_comp]

variable [∀ a, HasShift (D a) ℤ] [∀ a, HasShift (D' a) ℤ]

variable (pull comp pull' comp' P Φ ε) in
/-- **The transfer of Stacks 0DLA along a comparison.** Let `Φ` and `ε` be as in
`CategoryTheory.HypercoverComparisonCompCompatible`, with

1. `Φ a` bijective on morphisms between objects satisfying `Q`;
2. `Φ a (K⟦i⟧) ≅ (Φ a K)⟦i⟧`;
3. `Φ a` carrying `Q` to `Q'`;
4. the essential image of `Φ` descending along `P`;
5. the `ε` compatible with the composition comparisons.

Suppose that `Q` is stable under the pullbacks along `P` and under the shifts, that every
augmented simplicial object in `H` lies in `H'`, and that its augmentation in degree zero, its
faces and its last vertices `τⁿₙ` lie in `P`. Then the shape of Stacks 0DLA for `pull'`, `H'`,
`Q'` gives it for `pull`, `H`, `Q`.

The proof transports `K₀`, `α` and the cocycle condition through `ε` and `Φ`, the negative
self-extensions through clauses 1 and 2, applies the hypothesis, and pulls the output back
through clauses 4 and 1. -/
theorem hypercoverDerivedDescent_of_comparison [P.IsStableUnderComposition]
    (H H' : SimplicialObject.Augmented A → Prop) (Q : ∀ a : A, D a → Prop)
    (Q' : ∀ a : A, D' a → Prop) (h' : HypercoverDerivedDescent pull' comp' H' Q')
    (h1 : ∀ (a : A) (K E : D a), Q a K → Q a E →
      Function.Bijective (fun g : K ⟶ E => (Φ a).map g))
    (h2 : ∀ (a : A) (K : D a) (i : ℤ), Nonempty ((Φ a).obj (K⟦i⟧) ≅ ((Φ a).obj K)⟦i⟧))
    (h3 : ∀ (a : A) (K : D a), Q a K → Q' a ((Φ a).obj K))
    (h4 : ∀ {X Y : A} (f : Y ⟶ X), P f → ∀ L : D' X, Q' X L → ∀ K' : D Y, Q Y K' →
      Nonempty ((Φ Y).obj K' ≅ (pull' f).obj L) → ∃ K : D X, Q X K ∧ Nonempty ((Φ X).obj K ≅ L))
    (h5 : HypercoverComparisonCompCompatible pull comp pull' comp' P Φ ε)
    (hQpull : ∀ {a b : A} (f : a ⟶ b), P f → ∀ K : D b, Q b K → Q a ((pull f).obj K))
    (hQshift : ∀ (a : A) (K : D a) (i : ℤ), Q a K → Q a (K⟦i⟧))
    (hH : ∀ U, H U → H' U)
    (hP₀ : ∀ U, H U → P (U.hom.app (op (SimplexCategory.mk 0))))
    (hPδ : ∀ U, H U → ∀ (n : ℕ) (i : Fin (n + 2)), P (U.left.δ i))
    (hPτ : ∀ U, H U → ∀ n : ℕ, P (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk n) (Fin.last n)).op)) :
    HypercoverDerivedDescent pull comp H Q := by
  intro U hU K₀ α hα hK₀ hExt
  have hs : P (U.left.δ (1 : Fin 2)) := hPδ U hU 0 1
  have ht : P (U.left.δ (0 : Fin 2)) := hPδ U hU 0 0
  have ha₀ := hP₀ U hU
  have hα' := h5.isHypercoverDescentCocycle hs ht (hPδ U hU 1 (2 : Fin 3))
    (hPδ U hU 1 (0 : Fin 3)) (hPδ U hU 1 (1 : Fin 3)) α hα
  have hExt' : ∀ (n : ℕ) (t : ℤ), t < 0 →
      Subsingleton ((pull' (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) (Fin.last n)).op)).obj ((Φ _).obj K₀) ⟶
        ((pull' (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) (Fin.last n)).op)).obj ((Φ _).obj K₀))⟦t⟧) := by
    intro n t htn
    have hτ := hPτ U hU n
    have hQn := hQpull _ hτ K₀ hK₀
    exact (Φ _).subsingleton_hom_shift_of_surjective t ((ε _ hτ).app K₀).symm
      (h2 _ _ t).some (h1 _ _ _ hQn (hQshift _ _ t hQn)).2 (hExt n t htn)
  obtain ⟨K', β', hK', hc'⟩ := h' U (hH U hU) ((Φ _).obj K₀) _ hα' (h3 _ _ hK₀) hExt'
  obtain ⟨K, hK, ⟨γ⟩⟩ := h4 _ ha₀ K' hK' K₀ hK₀ ⟨β'.symm⟩
  have hQa := hQpull _ ha₀ K hK
  obtain ⟨β, hβ⟩ := (Φ _).exists_iso_map_hom_of_bijective (h1 _ _ _ hQa hK₀) (h1 _ _ _ hK₀ hQa)
    (h1 _ _ _ hQa hQa) (h1 _ _ _ hK₀ hK₀) ((ε _ ha₀).app K ≪≫ (pull' _).mapIso γ ≪≫ β')
  exact ⟨K, β, hK, h5.isHypercoverDescentCompatible ha₀ hs ht α K K' γ β' hc' β hβ
    (h1 _ _ _ (hQpull _ hs _ hK₀) (hQpull _ ht _ hK₀)).1⟩

end Comparison

end CategoryTheory
