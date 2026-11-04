module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjectionsFunctor
public import StacksFrontier.Homology.DerivedComplete.ConstantTowerDerivedLimit
public import StacksFrontier.Homology.DerivedComplete.LeftOrthogonal
public import StacksFrontier.Homology.DerivedComplete.PretriangulatedTwoOfThree

/-!
# Derived limits of reductions as reflections onto derived complete objects

Let `A` be a commutative ring, `I = (f₁, …, f_r)` a finitely generated ideal and `D` an
`A`-linear pre-triangulated category with countable products. Let `K` be an object of `D`,
`(Tₙ)` a tower of derived complete objects with compatible maps `red : K ⟶ Tₙ`, and `L` a
derived limit of `(Tₙ)` with projections `πₙ`, together with a map `η : K ⟶ L` such that
`η ≫ πₙ = redₙ`.

Suppose given an exact functor `Φ : D ⥤ D` which commutes with countable products, and such that
every object `X` has iterated cones of `f₁, …, f_r` ending at `Φ X`; for instance `Φ` is the
tensor product with the Koszul complex on `f₁, …, f_r`. If the tower `Φ Tₙ` is pro-isomorphic,
through `Φ redₙ`, to the constant tower `Φ K`, then `η` is a reflection of `K` onto the derived
complete objects: `L` is derived complete and every map from `K` to a derived complete object
factors uniquely through `η`.

Indeed `Φ L` is a derived limit of the tower `Φ Tₙ`, so `Φ η` is an isomorphism, and the cone
of `η` is sent by `Φ` to zero. Its iterated cones of the `fᵢ` vanish, so it has no nonzero map
to a shift of a derived complete object, and `η` induces a bijection on maps into such objects.

## Main results

* `DerivedComplete.isDerivedComplete_of_isDerivedLimitWithProjections`: a derived limit of
  derived complete objects is derived complete.
* `DerivedComplete.bijective_comp_of_isIso_of_isLeftOrthogonalShifts`: a map whose cone has no
  nonzero map to the shifts of `E` induces a bijection on maps into `E`.
* `DerivedComplete.isDerivedComplete_and_bijective_of_derivedLimit`: the reflection criterion.

## References

* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open NoetherianAdicCompletion

namespace DerivedComplete

variable {A : Type*} [CommRing A]
  {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasProductsOfShape ℕ D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear A] [Pretriangulated D]

/-- **A derived limit of derived complete objects is derived complete.** -/
theorem isDerivedComplete_of_isDerivedLimitWithProjections (I : Ideal A) {T : ℕᵒᵖ ⥤ D}
    (hT : ∀ n : ℕ, IsDerivedComplete I (T.obj ⟨n⟩)) {L : D} {π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩}
    (hL : IsDerivedLimitWithProjections T L π) : IsDerivedComplete I L := by
  obtain ⟨δ, hδ⟩ := hL
  intro f hf
  exact isDerivedCompleteAt_of_distTriang_of_pretriangulated hδ
    (isDerivedCompleteAt_pi fun n ↦ hT n f hf)
    (isDerivedCompleteAt_pi fun n ↦ hT n f hf)

omit [HasProductsOfShape ℕ D] in
/-- **Maps out of a cone that is left orthogonal to `E`.** If `K ⟶ L ⟶ C ⟶ K⟦1⟧` is a
distinguished triangle and no shift of `C` maps nontrivially to `E`, then precomposition with
`K ⟶ L` is a bijection from maps `L ⟶ E` to maps `K ⟶ E`. -/
theorem bijective_comp_of_distTriang_of_isLeftOrthogonalShifts {E : D}
    {T : Triangle D} (hT : T ∈ distTriang D) (hC : IsLeftOrthogonalShifts E T.obj₃) :
    Function.Bijective fun ψ : T.obj₂ ⟶ E ↦ T.mor₁ ≫ ψ := by
  have h₀ : ∀ χ : T.obj₃ ⟶ E, χ = 0 := fun χ ↦ by
    have := hC 0 ((shiftFunctorZero D ℤ).hom.app T.obj₃ ≫ χ)
    rw [← cancel_epi ((shiftFunctorZero D ℤ).hom.app T.obj₃), this, comp_zero]
  refine ⟨fun ψ₁ ψ₂ hψ ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨χ, hχ⟩ := Triangle.yoneda_exact₂ T hT (ψ₁ - ψ₂)
      (by simpa [Preadditive.comp_sub, sub_eq_zero] using hψ)
    rw [hχ, h₀ χ, comp_zero]
  · obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang T hT) g (by
      dsimp [Triangle.invRotate]
      rw [Preadditive.neg_comp]
      exact neg_eq_zero.mpr (hC (-1) _))
    exact ⟨ψ, hψ.symm⟩

variable [∀ n : ℤ, (shiftFunctor D n).Linear A]

/-- **The reflection criterion.** Let `T` be a tower of objects derived complete along
`I = (f₁, …, f_r)`, `red` compatible maps from `K`, `L` a derived limit of `T` with projections
`π`, and `η : K ⟶ L` with `η ≫ πₙ = redₙ`. Let `Φ` be an exact functor commuting with countable
products such that every object `X` has iterated cones of the `fᵢ` ending at `Φ X`, and such that
`Φ redₙ` makes `Φ Tₙ` pro-isomorphic to the constant tower `Φ K`. Then `L` is derived complete
and every map from `K` to a derived complete object factors uniquely through `η`. -/
theorem isDerivedComplete_and_bijective_of_derivedLimit {r : ℕ} (f : Fin r → A)
    (I : Ideal A) (hI : I = Ideal.span (Set.range f))
    (Φ : D ⥤ D) [Φ.Additive] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) Φ]
    (hΦ : ∀ X : D, ∃ (M : Fin (r + 1) → D) (v : ∀ i : Fin r, M i.castSucc ⟶ M i.succ)
      (w : ∀ i : Fin r, M i.succ ⟶ (M i.castSucc)⟦(1 : ℤ)⟧),
      (∀ i, Triangle.mk (f i • 𝟙 (M i.castSucc)) (v i) (w i) ∈ distTriang D) ∧
        Nonempty (M 0 ≅ X) ∧ Nonempty (M (Fin.last r) ≅ Φ.obj X))
    {K : D} {T : ℕᵒᵖ ⥤ D} (red : (Functor.const ℕᵒᵖ).obj K ⟶ T)
    (hT : ∀ n : ℕ, IsDerivedComplete I (T.obj ⟨n⟩))
    (hpro : HasEventualInverses ((Functor.constComp ℕᵒᵖ K Φ).inv ≫ Functor.whiskerRight red Φ))
    {L : D} {π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩} (hL : IsDerivedLimitWithProjections T L π)
    (η : K ⟶ L) (hη : ∀ n : ℕ, η ≫ π n = red.app ⟨n⟩) :
    IsDerivedComplete I L ∧
      ∀ E : D, IsDerivedComplete I E → Function.Bijective fun ψ : L ⟶ E ↦ η ≫ ψ := by
  refine ⟨isDerivedComplete_of_isDerivedLimitWithProjections I hT hL, fun E hE ↦ ?_⟩
  have hΦη : IsIso (Φ.map η) :=
    isIso_of_comp_eq_of_hasEventualInverses_const _ hpro (hL.map Φ) (Φ.map η) (fun n ↦ by
      simp [← Functor.map_comp, hη])
  obtain ⟨Z, v, w, hT₀⟩ := distinguished_cocone_triangle η
  have hZ : IsZero (Φ.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ (Φ.map_distinguished _ hT₀)).2 hΦη
  obtain ⟨M, v', w', hM, ⟨e₀⟩, ⟨e⟩⟩ := hΦ Z
  have hE' : ∀ i, IsDerivedCompleteAt E (f i) := fun i ↦
    hE (f i) (hI ▸ Ideal.subset_span ⟨i, rfl⟩)
  have hlast : IsLeftOrthogonalShifts E (M (Fin.last r)) := fun k φ ↦
    ((shiftFunctor D k).map_isZero (hZ.of_iso e)).eq_of_src _ _
  have h₀ := isLeftOrthogonalShifts_of_coneChain f hE' M v' w' hM hlast
  have hC : IsLeftOrthogonalShifts E Z := fun k φ ↦ by
    have := h₀ k ((shiftFunctor D k).map e₀.hom ≫ φ)
    rw [← cancel_epi ((shiftFunctor D k).map e₀.hom), this, comp_zero]
  exact bijective_comp_of_distTriang_of_isLeftOrthogonalShifts hT₀ hC

end DerivedComplete

end
