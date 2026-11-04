module

public import StacksFrontier.Homology.DerivedComplete.DerivedLimitReflection

/-!
# The derived completion functor from reflections onto derived complete objects

Let `D` be an `A`-linear pre-triangulated category with countable products and `I` an ideal of
`A`. Suppose given, functorially in `K ∈ D`, a tower `T(K)` of derived complete objects with
compatible maps `K → T(K)ₙ`, such that for every derived limit `L` of `T(K)` the induced map
`η : K → L` is a reflection onto the derived complete objects: every map from `K` to a derived
complete object factors uniquely through `η`. Then `K ↦ R lim T(K)` is the left adjoint to the
inclusion of the derived complete objects, with unit `η` and with projections to the tower that
are natural in `K`; and `K` is derived complete exactly when `K` itself, with its maps to the
tower, is a derived limit of `T(K)`.

Every tower has a derived limit, its projections fitting into a Milnor triangle, and the maps
from `K` lift to it; the reflection property then makes the construction a functor.

## Main results

* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_comp_eq`: compatible maps to a
  tower lift to its derived limit.
* `DerivedComplete.exists_leftAdjoint_isDerivedLimitWithProjections`: the left adjoint.
* `DerivedComplete.isDerivedComplete_iff_isDerivedLimitWithProjections`: completeness as being
  the derived limit of the tower.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open NoetherianAdicCompletion

namespace NoetherianAdicCompletion

variable {D : Type*} [Category D] [Preadditive D] [HasProductsOfShape ℕ D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Compatible maps to a tower lift to its derived limit.** -/
theorem IsDerivedLimitWithProjections.exists_comp_eq {T : ℕᵒᵖ ⥤ D} {L : D}
    {π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩} (hL : IsDerivedLimitWithProjections T L π) {K : D}
    (red : (Functor.const ℕᵒᵖ).obj K ⟶ T) :
    ∃ η : K ⟶ L, ∀ n : ℕ, η ≫ π n = red.app ⟨n⟩ := by
  obtain ⟨δ, hδ⟩ := hL
  obtain ⟨η, hη⟩ := Triangle.coyoneda_exact₂ _ hδ (Pi.lift fun n : ℕ ↦ red.app ⟨n⟩) (by
    dsimp
    ext n
    have := red.naturality (homOfLE (Nat.le_succ n)).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    simp [Preadditive.comp_sub, this])
  refine ⟨η, fun n ↦ ?_⟩
  simpa using congrArg (· ≫ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n) hη.symm

/-- A tower has a derived limit through which compatible maps from any `K` factor. -/
private theorem exists_isDerivedLimitWithProjections_exists_comp_eq (T : ℕᵒᵖ ⥤ D) (K : D)
    (red : (Functor.const ℕᵒᵖ).obj K ⟶ T) :
    ∃ (L : D) (π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩), IsDerivedLimitWithProjections T L π ∧
      ∃ η : K ⟶ L, ∀ n : ℕ, η ≫ π n = red.app ⟨n⟩ := by
  obtain ⟨L, h⟩ := exists_isDerivedLimit T
  obtain ⟨π, hL⟩ := exists_isDerivedLimitWithProjections h
  exact ⟨L, π, hL, hL.exists_comp_eq red⟩

end NoetherianAdicCompletion

namespace DerivedComplete

variable {A : Type*} [CommRing A]
  {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasProductsOfShape ℕ D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear A] [Pretriangulated D]

/-- **The left adjoint to the inclusion of the derived complete objects, from reflections.**
Let `T(K)` be towers of derived complete objects, functorial in `K`, with natural maps
`red : K → T(K)`, such that every derived limit of `T(K)` receives from `K` a reflection onto
the derived complete objects. Then the inclusion of the derived complete objects has a left
adjoint sending `K` to a derived limit of `T(K)`, whose projections are natural in `K` and
composed with the unit give `red`. -/
theorem exists_leftAdjoint_isDerivedLimitWithProjections (I : Ideal A)
    (T : D ⥤ ℕᵒᵖ ⥤ D) (red : Functor.const ℕᵒᵖ ⟶ T)
    (hT : ∀ (K : D) (n : ℕ), IsDerivedComplete I ((T.obj K).obj ⟨n⟩))
    (hrefl : ∀ (K L : D) (π : ∀ n : ℕ, L ⟶ (T.obj K).obj ⟨n⟩),
      IsDerivedLimitWithProjections (T.obj K) L π → ∀ η : K ⟶ L,
        (∀ n : ℕ, η ≫ π n = (red.app K).app ⟨n⟩) →
          ∀ E : D, IsDerivedComplete I E → Function.Bijective fun ψ : L ⟶ E ↦ η ≫ ψ) :
    let P : ObjectProperty D := fun K ↦ IsDerivedComplete I K
    ∃ (Lf : D ⥤ P.FullSubcategory) (adj : Lf ⊣ P.ι)
      (π : ∀ n : ℕ, Lf ⋙ P.ι ⟶ T ⋙ (evaluation ℕᵒᵖ D).obj ⟨n⟩),
      (∀ K : D, IsDerivedLimitWithProjections (T.obj K) ((Lf ⋙ P.ι).obj K)
        fun n ↦ (π n).app K) ∧
      ∀ (K : D) (n : ℕ), adj.unit.app K ≫ (π n).app K = (red.app K).app ⟨n⟩ := by
  intro P
  choose L π hL η hη using fun K : D ↦
    exists_isDerivedLimitWithProjections_exists_comp_eq (T.obj K) K (red.app K)
  have hLc : ∀ K, IsDerivedComplete I (L K) := fun K ↦
    isDerivedComplete_of_isDerivedLimitWithProjections I (hT K) (hL K)
  let e : ∀ (K : D) (E : P.FullSubcategory), ((⟨L K, hLc K⟩ : P.FullSubcategory) ⟶ E) ≃
      (K ⟶ P.ι.obj E) := fun K E ↦
    Equiv.ofBijective (fun ψ ↦ η K ≫ ψ.hom)
      ((hrefl K (L K) (π K) (hL K) (η K) (hη K) E.obj E.property).comp
        ⟨fun a b h ↦ by ext1; exact h, fun φ ↦ ⟨⟨φ⟩, rfl⟩⟩)
  have he : ∀ (K : D) (E E' : P.FullSubcategory) (g : E ⟶ E') (h : _ ⟶ E),
      e K E' (h ≫ g) = e K E h ≫ P.ι.map g := fun K E E' g h ↦ by
    simp [e]
  let Lf := Adjunction.leftAdjointOfEquiv e he
  let adj : Lf ⊣ P.ι := Adjunction.adjunctionOfEquivLeft e he
  have hunit : ∀ K, adj.unit.app K = η K := fun K ↦ by
    simp only [adj, Adjunction.adjunctionOfEquivLeft, e, Adjunction.mkOfHomEquiv_unit_app,
      Equiv.ofBijective_apply, ObjectProperty.FullSubcategory.id_hom]
    exact Category.comp_id _
  have hmap : ∀ {K K' : D} (g : K ⟶ K'), η K ≫ (Lf.map g).hom = g ≫ η K' := fun {K K'} g ↦ by
    have h : e K (Lf.obj K') (Lf.map g) = g ≫ e K' (Lf.obj K') (𝟙 _) :=
      (e K _).apply_symm_apply _
    simpa [e] using h
  let πn : ∀ n : ℕ, Lf ⋙ P.ι ⟶ T ⋙ (evaluation ℕᵒᵖ D).obj ⟨n⟩ := fun n ↦
    { app := fun K ↦ π K n
      naturality := fun K K' g ↦ by
        apply (hrefl K (L K) (π K) (hL K) (η K) (hη K) _ (hT K' n)).1
        have hred := congrArg (fun φ ↦ φ.app ⟨n⟩) (red.naturality g)
        simp only [Functor.const_obj_obj, NatTrans.comp_app, Functor.const_map_app] at hred
        dsimp
        rw [reassoc_of% (hmap g), hη K', reassoc_of% (hη K n)]
        exact hred }
  refine ⟨Lf, adj, πn, hL, fun K n ↦ ?_⟩
  rw [hunit]
  exact hη K n

/-- **Derived completeness as being the derived limit of the tower.** Under the hypotheses of
`exists_leftAdjoint_isDerivedLimitWithProjections`, an object `K` is derived complete exactly
when `K`, with the maps `red`, is a derived limit of `T(K)`. -/
theorem isDerivedComplete_iff_isDerivedLimitWithProjections (I : Ideal A)
    (T : D ⥤ ℕᵒᵖ ⥤ D) (red : Functor.const ℕᵒᵖ ⟶ T)
    (hT : ∀ (K : D) (n : ℕ), IsDerivedComplete I ((T.obj K).obj ⟨n⟩))
    (hrefl : ∀ (K L : D) (π : ∀ n : ℕ, L ⟶ (T.obj K).obj ⟨n⟩),
      IsDerivedLimitWithProjections (T.obj K) L π → ∀ η : K ⟶ L,
        (∀ n : ℕ, η ≫ π n = (red.app K).app ⟨n⟩) →
          ∀ E : D, IsDerivedComplete I E → Function.Bijective fun ψ : L ⟶ E ↦ η ≫ ψ)
    (K : D) :
    IsDerivedComplete I K ↔
      IsDerivedLimitWithProjections (T.obj K) K fun n ↦ (red.app K).app ⟨n⟩ := by
  refine ⟨fun hK ↦ ?_, fun h ↦
    isDerivedComplete_of_isDerivedLimitWithProjections I (hT K) h⟩
  obtain ⟨L, π, hL, η, hη⟩ :=
    exists_isDerivedLimitWithProjections_exists_comp_eq (T.obj K) K (red.app K)
  have hb := hrefl K L π hL η hη
  obtain ⟨ψ, hψ⟩ := (hb K hK).2 (𝟙 K)
  have hψ' : ψ ≫ η = 𝟙 L :=
    (hb L (isDerivedComplete_of_isDerivedLimitWithProjections I (hT K) hL)).1
      (by simp [reassoc_of% hψ])
  simpa [hη] using hL.ofIso (⟨η, ψ, hψ, hψ'⟩ : K ≅ L).symm

end DerivedComplete
