module

public import StacksFrontier.Homology.DerivedComplete.TriangulatedReflection

/-!
# Functors killing invertible objects invert the derived completion map

Let `𝒟` be an `A`-linear pretriangulated category with countable products, `I ⊆ A` a finitely
generated ideal, and `Φ : 𝒟 ⥤ ℰ` a triangulated functor which kills every object on which some
element of `I` acts invertibly. Then `Φ` inverts the derived completion map `K ⟶ K^∧` of every
object `K`.

## Main results

* `DerivedCompletionReflection.isIso_map_unit_of_kills`: a triangulated functor killing every
  object on which some element of `I` acts invertibly inverts the derived completion map `K ⟶ K^∧`.
* `DerivedCompletionReflection.isDerivedComplete_obj₃_of_distTriang`: the cone of a map of
  derived complete objects is derived complete.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCompletionReflection

variable {A : Type*} [CommRing A] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [Linear A 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear A] [HasProductsOfShape ℕ 𝒟]
  {ℰ : Type*} [Category ℰ] [Preadditive ℰ] [HasZeroObject ℰ] [HasShift ℰ ℤ]
  [∀ n : ℤ, (shiftFunctor ℰ n).Additive] [Pretriangulated ℰ]
  (Φ : 𝒟 ⥤ ℰ) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- A triangulated functor killing every object on which `f` acts invertibly inverts the map
`coneπ K f`. -/
theorem isIso_map_coneπ (K : 𝒟) (f : A)
    (hΦ : ∀ N : 𝒟, IsIso (f • 𝟙 N) → IsZero (Φ.obj N)) : IsIso (Φ.map (coneπ K f)) :=
  (Triangle.isZero₁_iff_isIso₂ _ (Φ.map_distinguished _ (cone_distinguished K f))).1
    (hΦ _ (isIso_smul_fiber K f))

/-- If `Φ` kills every object on which some member of the list `l` acts invertibly, then there is
a map `η : K ⟶ R` with `R` derived complete at every member of `l`, through which every map from
`K` to an object derived complete at every member of `l` factors uniquely, such that `Φ.map η` is
an isomorphism. -/
theorem exists_reflection_list_kill (l : List A) (K : 𝒟)
    (hΦ : ∀ a ∈ l, ∀ N : 𝒟, IsIso (a • 𝟙 N) → IsZero (Φ.obj N)) :
    ∃ (R : 𝒟) (η : K ⟶ R), (∀ a ∈ l, IsDerivedCompleteAt R a) ∧
      (∀ M : 𝒟, (∀ a ∈ l, IsDerivedCompleteAt M a) →
        Function.Bijective fun g : R ⟶ M => η ≫ g) ∧ IsIso (Φ.map η) := by
  induction l with
  | nil =>
    exact ⟨K, 𝟙 K, by simp, fun M _ ↦ ⟨fun g h e ↦ by simpa using e,
      fun g ↦ ⟨g, Category.id_comp g⟩⟩, inferInstance⟩
  | cons a l ih =>
    obtain ⟨R, η, hR, huniv, hiso⟩ := ih fun b hb ↦ hΦ b (List.mem_cons_of_mem a hb)
    refine ⟨coneObj R a, η ≫ coneπ R a, ?_, ?_, ?_⟩
    · exact List.forall_mem_cons.2 ⟨isDerivedCompleteAt_coneObj R a,
        fun c hc ↦ isDerivedCompleteAt_coneObj_of_isDerivedCompleteAt R a (hR c hc)⟩
    · intro M hM
      simpa only [Function.comp_def, Category.assoc] using
        (huniv M fun c hc ↦ hM c (List.mem_cons_of_mem a hc)).comp
          (bijective_precomp_coneπ R a (hM a List.mem_cons_self))
    · have := isIso_map_coneπ Φ R a (hΦ a List.mem_cons_self)
      rw [Φ.map_comp]
      infer_instance

/-- **A triangulated functor killing the objects on which some element of `I` acts invertibly
inverts the derived completion map** `K ⟶ K^∧`, for a finitely generated ideal `I` and any left
adjoint `L` of the inclusion of the derived `I`-complete objects. -/
theorem isIso_map_unit_of_kills (I : Ideal A) (hI : I.FG)
    {L : 𝒟 ⥤ ObjectProperty.FullSubcategory (IsDerivedComplete I : ObjectProperty 𝒟)}
    (adj : L ⊣ ObjectProperty.ι _) (K : 𝒟)
    (hΦ : ∀ a ∈ I, ∀ N : 𝒟, IsIso (a • 𝟙 N) → IsZero (Φ.obj N)) :
    IsIso (Φ.map (adj.unit.app K)) := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨R, η, hR, huniv, hiso⟩ := exists_reflection_list_kill Φ s.toList K
    fun a ha ↦ hΦ a (Ideal.subset_span (by simpa using ha))
  have hRc : IsDerivedComplete (Ideal.span (s : Set A)) R :=
    (isDerivedComplete_span_iff _ R).2 fun a ha ↦ hR a (by simpa using ha)
  obtain ⟨φ, hφ⟩ := (huniv (L.obj K).obj fun a ha ↦
    ((isDerivedComplete_span_iff _ _).1 (L.obj K).property) a (by simpa using ha)).2
      (adj.unit.app K)
  replace hφ : η ≫ φ = adj.unit.app K := hφ
  let ψ : L.obj K ⟶ ⟨R, hRc⟩ := (adj.homEquiv K ⟨R, hRc⟩).symm η
  have hψ : adj.unit.app K ≫ ψ.hom = η :=
    (adj.homEquiv_unit K _ ψ).symm.trans (Equiv.apply_symm_apply _ η)
  have h1 : φ ≫ ψ.hom = 𝟙 R := (huniv R hR).1 (by
    show η ≫ φ ≫ ψ.hom = η ≫ 𝟙 R
    rw [← Category.assoc, hφ, hψ, Category.comp_id])
  have h2 : ψ.hom ≫ φ = 𝟙 _ := by
    have := (adj.homEquiv K (L.obj K)).injective (a₁ := ψ ≫ ObjectProperty.homMk φ) (a₂ := 𝟙 _)
      (by rw [adj.homEquiv_unit, adj.homEquiv_unit]; simp [← Category.assoc, hψ, hφ])
    exact congrArg (fun t ↦ t.hom) this
  have : IsIso φ := ⟨ψ.hom, h1, h2⟩
  rw [← hφ, Φ.map_comp]
  infer_instance

omit [HasProductsOfShape ℕ 𝒟] in
/-- In a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `X` and `Y` derived complete at `f`,
`Z` is derived complete at `f`. -/
theorem isDerivedCompleteAt_obj₃_of_distTriang [HasProductsOfShape ℕ 𝒟] {X Y Z : 𝒟} {a : X ⟶ Y}
    {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧} (h : Triangle.mk a b c ∈ distTriang 𝒟) {f : A}
    (hX : IsDerivedCompleteAt X f) (hY : IsDerivedCompleteAt Y f) : IsDerivedCompleteAt Z f := by
  rw [isDerivedCompleteAt_iff_forall_eq_zero]
  intro N _ g
  have hgc : g ≫ c = 0 := by
    have := isIso_smul_shift (A := A) (N := N) (f := f) (-1 : ℤ)
    apply (shiftFunctor 𝒟 (-1 : ℤ)).map_injective
    rw [Functor.map_zero,
      ← cancel_mono ((shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).hom.app X), zero_comp]
    exact (isDerivedCompleteAt_iff_forall_eq_zero X f).1 hX (N⟦(-1 : ℤ)⟧) _
  obtain ⟨v, hv⟩ := coyoneda_exact₃' h g hgc
  rw [hv, (isDerivedCompleteAt_iff_forall_eq_zero Y f).1 hY N v, zero_comp]

omit [HasProductsOfShape ℕ 𝒟] in
/-- The cone of a map of derived complete objects is derived complete. -/
theorem isDerivedComplete_obj₃_of_distTriang [HasProductsOfShape ℕ 𝒟] {X Y Z : 𝒟} {a : X ⟶ Y}
    {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧} (h : Triangle.mk a b c ∈ distTriang 𝒟) {I : Ideal A}
    (hX : IsDerivedComplete I X) (hY : IsDerivedComplete I Y) : IsDerivedComplete I Z :=
  fun f hf ↦ isDerivedCompleteAt_obj₃_of_distTriang h (hX f hf) (hY f hf)

end DerivedCompletionReflection
