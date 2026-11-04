module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FilteredCharSeries

/-!
# Multiplicativity of the characteristic series along a short exact sequence of complexes

Let `0 → N → M → Q → 0` be a short exact sequence of cochain complexes of modules over a
commutative ring `R`, with `N` and `Q` perfect, and let `φ` be an endomorphism of the sequence.
Then

`det(1 - φ T | M) = det(1 - φ T | N) · det(1 - φ T | Q)`

in `R⟦T⟧ˣ`. This is the determinant analogue of
`CategoryTheory.FilteredDerived.perfectDerivedTrace_X₂_eq_add`, and the proof is the same: the
two-step filtration `M ⊇ N ⊇ 0` with its bounded filtered finite projective representative
`CategoryTheory.FilteredDerived.repFilteredPerfectData`, and the multiplicativity of the
characteristic series along a filtration,
`CategoryTheory.FilteredDerived.perfectDerivedCharSeries_forgetDF_eq_prod_grDF`.

## Main results

* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries_congr`: the characteristic series is
  invariant under conjugation by an isomorphism, for any model of the derived category.
* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries_eq_one_of_isZero`: the characteristic
  series of an endomorphism of a zero object is `1`.
* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries_X₂_eq_mul`: multiplicativity along a
  short exact sequence.

## Implementation notes

The two-step filtered representative and the comparison isomorphisms
`CategoryTheory.FilteredDerived.liftDFQIsoApp` are defined in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace` for the model
`HasDerivedCategory.standard` of the derived category, so the results from the second section on
are stated in that model too; the instance is made local exactly as in that file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace CategoryTheory.FilteredDerived

/-! ### Invariance under conjugation -/

section Conj

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **The characteristic series is invariant under conjugation.** If `e : K ≅ K'` intertwines
`f` and `f'`, then `det(1 - f T | K) = det(1 - f' T | K')`. -/
theorem perfectDerivedCharSeries_congr {K K' : DerivedCategory (ModuleCat.{v} R)}
    (hK : StacksDraft.Perfect.IsPerfect K) (hK' : StacksDraft.Perfect.IsPerfect K') (e : K ≅ K')
    (f : K ⟶ K) (f' : K' ⟶ K') (h : f ≫ e.hom = e.hom ≫ f') :
    perfectDerivedCharSeries R K hK f = perfectDerivedCharSeries R K' hK' f' := by
  have hP := perfectRep_spec R K hK
  have := isKProjective_of_finiteProjectiveComplex R hP
  obtain ⟨g, hg⟩ := exists_map_eq_of_isKProjective (perfectRep R K hK) (perfectRep R K hK)
    ((perfectRepIso R K hK).hom ≫ f ≫ (perfectRepIso R K hK).inv)
  rw [perfectDerivedCharSeries_eq_alternatingCharSeries R K hK f _ hP (perfectRepIso R K hK) g hg,
    perfectDerivedCharSeries_eq_alternatingCharSeries R K' hK' f' _ hP
      (perfectRepIso R K hK ≪≫ e) g]
  rw [hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← reassoc_of% h]
  simp

/-- The characteristic series of an endomorphism of a zero object is `1`. -/
theorem perfectDerivedCharSeries_eq_one_of_isZero {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : StacksDraft.Perfect.IsPerfect K) (hz : IsZero K) (f : K ⟶ K) :
    perfectDerivedCharSeries R K hK f = 1 := by
  have hP : finiteProjectiveComplex R (Stacks.EtaleCohomology.zeroCochainComplex.{u, v} R) :=
    Stacks.EtaleCohomology.zeroCochainComplex_finiteProjective.{u, v} R
  have hQ : IsZero (DerivedCategory.Q.obj
      (Stacks.EtaleCohomology.zeroCochainComplex.{u, v} R)) :=
    Functor.map_isZero _ (Stacks.EtaleCohomology.zeroCochainComplex_isZero.{u, v} R)
  rw [perfectDerivedCharSeries_eq_alternatingCharSeries R K hK f _ hP (hQ.iso hz) 0
    (hQ.eq_of_src _ _)]
  unfold alternatingCharSeries
  refine (finprod_congr fun i => ?_).trans finprod_one
  rw [charUnitAt_eq_one_of_isZero R _ hP i _
    (Stacks.EtaleCohomology.zeroCochainComplex_isZero_X.{u, v} R i), inv_one, ite_self]

end Conj

attribute [local instance] HasDerivedCategory.standard

/-! ### Multiplicativity along a short exact sequence -/

section Multiplicativity

open CochainComplex Stacks.EtaleCohomology

variable {R : Type u} [CommRing R]

/-- The characteristic series of the image under `G : DF ⥤ D` of an endomorphism `Qh(x)` of
`Qh(X)` is the characteristic series of `y` on `Q(Y)`, for an isomorphism `G(X) ≅ Y`
intertwining `G(x)` and `y`. -/
lemma perfectDerivedCharSeries_liftDF_eq
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    {X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ} (x : X ⟶ X)
    {Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (y : Y ⟶ Y)
    (e : (G.mapHomologicalComplex _).obj X ≅ Y)
    (he : (G.mapHomologicalComplex _).map x ≫ e.hom = e.hom ≫ y)
    (hX : StacksDraft.Perfect.IsPerfect ((FilteredDerivedCategory.liftDF G hG).obj
      (FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj X))))
    (hY : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y)) :
    perfectDerivedCharSeries R _ hX ((FilteredDerivedCategory.liftDF G hG).map
        (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x))) =
      perfectDerivedCharSeries R _ hY (DerivedCategory.Q.map y) :=
  perfectDerivedCharSeries_congr R hX hY _ _ _ (liftDF_map_comm G hG x y e he)

/-- **Multiplicativity along a two-step filtration, abstractly.** Let `F` be a filtered perfect
complex whose underlying object is `Qh(X)` for a complex of finite filtered modules `X`, and `x`
an endomorphism of `X`. Given identifications of the underlying complex of `X` and of its graded
pieces in indices `1` and `0` with complexes `Y₂`, `Y₁`, `Y₀` intertwining `x` with `y₂`, `y₁`,
`y₀`, and vanishing of the other graded pieces, `det(y₂) = det(y₁) · det(y₀)`. -/
lemma perfectDerivedCharSeries_eq_mul_of_twoStep
    {X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ}
    (F : FilteredPerfectData.{u, v} R)
    (hF : F.obj = FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj X))
    (x : X ⟶ X) {Y₂ Y₁ Y₀ : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (y₂ : Y₂ ⟶ Y₂) (y₁ : Y₁ ⟶ Y₁) (y₀ : Y₀ ⟶ Y₀)
    (e₂ : (FiniteFilteredObject.forget.mapHomologicalComplex _).obj X ≅ Y₂)
    (he₂ : (FiniteFilteredObject.forget.mapHomologicalComplex _).map x ≫ e₂.hom = e₂.hom ≫ y₂)
    (e₁ : ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).obj X ≅ Y₁)
    (he₁ : ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).map x ≫ e₁.hom = e₁.hom ≫ y₁)
    (e₀ : ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).obj X ≅ Y₀)
    (he₀ : ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).map x ≫ e₀.hom = e₀.hom ≫ y₀)
    (hz : ∀ p : ℤ, p ≠ 0 → p ≠ 1 →
      IsZero (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj X))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₂))
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₁))
    (h₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₀)) :
    perfectDerivedCharSeries R _ h₂ (DerivedCategory.Q.map y₂) =
      perfectDerivedCharSeries R _ h₁ (DerivedCategory.Q.map y₁) *
        perfectDerivedCharSeries R _ h₀ (DerivedCategory.Q.map y₀) := by
  obtain ⟨obj, representative, bounded, finiteProjective, iso⟩ := F
  subst hF
  let F : FilteredPerfectData.{u, v} R := ⟨_, representative, bounded, finiteProjective, iso⟩
  let f : F.obj ⟶ F.obj :=
    FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x)
  have key := perfectDerivedCharSeries_forgetDF_eq_prod_grDF R F f
  have hL := perfectDerivedCharSeries_liftDF_eq.{u, v} FiniteFilteredObject.forget
    FilteredDerivedCategory.forget_inverts x y₂ e₂ he₂ (F.isPerfect_forgetDF R) h₂
  have k1 := perfectDerivedCharSeries_liftDF_eq.{u, v} (FiniteFilteredObject.grP 1)
    (FilteredDerivedCategory.grP_inverts 1) x y₁ e₁ he₁ (F.isPerfect_grDF R 1) h₁
  have k0 := perfectDerivedCharSeries_liftDF_eq.{u, v} (FiniteFilteredObject.grP 0)
    (FilteredDerivedCategory.grP_inverts 0) x y₀ e₀ he₀ (F.isPerfect_grDF R 0) h₀
  have kz : ∀ p : ℤ, p ≠ 0 → p ≠ 1 → perfectDerivedCharSeries R _ (F.isPerfect_grDF R p)
      ((CochainComplex.FilteredDerivedCategory.grDF p).map f) = 1 := fun p hp0 hp1 =>
    perfectDerivedCharSeries_eq_one_of_isZero R _
      ((DerivedCategory.Q.map_isZero (hz p hp0 hp1)).of_iso
        (liftDFQIsoApp.{u, v} R (FiniteFilteredObject.grP p)
          (FilteredDerivedCategory.grP_inverts p) X)) _
  rw [← hL, key, finprod_eq_prod_of_mulSupport_subset (s := {0, 1}),
    Finset.prod_pair (by norm_num), ← k1, ← k0, mul_comm]
  intro p hp
  by_contra hmem
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hmem
  exact hp (kz p hmem.1 hmem.2)

variable {S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ)}

/-- **Multiplicativity of the characteristic series along a short exact sequence.** For a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes of `R`-modules whose terms are perfect and an
endomorphism `φ` of it, `det(1 - φ T | X₂) = det(1 - φ T | X₁) · det(1 - φ T | X₃)`. -/
theorem perfectDerivedCharSeries_X₂_eq_mul (hS : S.ShortExact) (φ : S ⟶ S)
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₁))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₂))
    (h₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₃)) :
    perfectDerivedCharSeries R _ h₂ (DerivedCategory.Q.map φ.τ₂) =
      perfectDerivedCharSeries R _ h₁ (DerivedCategory.Q.map φ.τ₁) *
        perfectDerivedCharSeries R _ h₃ (DerivedCategory.Q.map φ.τ₃) := by
  have : ∀ n, Mono (S.f.f n) := fun n =>
    (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).mono_f
  obtain ⟨P₁, hP₁, p₁, hp₁⟩ := exists_finiteProjective_quasiIso h₁
  obtain ⟨P₃, hP₃, q₃, hq₃⟩ := exists_finiteProjective_quasiIso h₃
  have := isKProjective_of_finiteProjectiveComplex R hP₃
  have : ∀ n, Projective (P₃.X n) := fun n => by
    have := (hP₃.2 n).1
    infer_instance
  exact perfectDerivedCharSeries_eq_mul_of_twoStep.{u, v}
    (repFilteredPerfectData hS hP₁ hP₃ p₁ q₃) rfl
    (twoStepComplexMap φ) φ.τ₂ φ.τ₁ φ.τ₃
    (twoStepComplexForgetIso S) (twoStepComplexForgetIso_hom_naturality S φ)
    (twoStepComplexGrOneIso S) (twoStepComplexGrOneIso_hom_naturality S φ)
    (twoStepComplexGrZeroIso S hS) (twoStepComplexGrZeroIso_hom_naturality S hS hS φ)
    (fun _ hp0 hp1 => isZero_twoStepComplex_grP S hp0 hp1) h₂ h₁ h₃

end Multiplicativity

end CategoryTheory.FilteredDerived
