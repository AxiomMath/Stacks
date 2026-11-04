module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# When the homology comparison of a left exact functor is invertible

Let `F : A ⥤ B` be an additive left exact functor of abelian categories and `K` a cochain
complex of `A`. The comparison `H^q(F K) ⟶ F(H^q K)` of `homologyComparison` is invertible exactly
when `F` carries the cokernel presentation `K^{q-1} ⟶ Z^q K ⟶ H^q K ⟶ 0` of the cohomology of `K`
to a cokernel presentation, that is, when the short complex

`F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)`

is exact and its second map is an epimorphism. At the derived level, the edge morphism of an
unbounded right derived functor of `F` is invertible at a K-injective complex only if the
comparison of that complex is invertible.

## Main definitions

* `cyclesHomologyShortComplex`: the short complex `F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)`.

## Main results

* `isIso_homologyComparison_iff`: the comparison is invertible if and only if that short complex
  is exact with epimorphic second map.
* `isIso_homologyComparison_of_isIso_derivedHomologyComparison_app`: the edge morphism of a right
  derived functor of `F` is invertible at a K-injective complex only if the comparison of that
  complex is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vB uB

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

section Complexes

/-- The short complex `F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)`: the functor `F` applied to the
cokernel presentation of the cohomology of `K` in degree `q` by its cycles. -/
def cyclesHomologyShortComplex (K : CochainComplex A ℤ) (q : ℤ) : ShortComplex B :=
  ShortComplex.mk (F.map (K.toCycles (q - 1) q)) (F.map (K.homologyπ q))
    (by rw [← F.map_comp, K.toCycles_comp_homologyπ, F.map_zero])

/-- The cycles comparison is compatible with the maps from the previous term of the complex. -/
@[reassoc]
lemma toCycles_comp_cyclesComparison (K : CochainComplex A ℤ) (q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles (q - 1) q ≫
        cyclesComparison F K q =
      F.map (K.toCycles (q - 1) q) := by
  have := mono_map_iCycles F K q
  apply (cancel_mono (F.map (K.iCycles q))).1
  rw [Category.assoc, cyclesComparison_comp_map_iCycles, ← F.map_comp, K.toCycles_i]
  exact ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles_i (q - 1) q

/-- The cokernel presentation `(F K)^{q-1} ⟶ Z^q(F K) ⟶ H^q(F K)` of the cohomology of `F K`. -/
abbrev cyclesHomologyShortComplexOfMap (K : CochainComplex A ℤ) (q : ℤ) : ShortComplex B :=
  ShortComplex.mk (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles (q - 1) q)
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q)
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles_comp_homologyπ (q - 1) q)

/-- The map from the cokernel presentation of `H^q(F K)` to `cyclesHomologyShortComplex F K q`
given by the identity, the cycles comparison and the homology comparison. -/
def cyclesHomologyShortComplexHom (K : CochainComplex A ℤ) (q : ℤ) :
    cyclesHomologyShortComplexOfMap F K q ⟶ cyclesHomologyShortComplex F K q where
  τ₁ := 𝟙 (F.obj (K.X (q - 1)))
  τ₂ := cyclesComparison F K q
  τ₃ := homologyComparison F K q
  comm₁₂ := (Category.id_comp _).trans (toCycles_comp_cyclesComparison F K q).symm
  comm₂₃ := (homologyπ_comp_homologyComparison F K q).symm

omit [PreservesFiniteLimits F] in
/-- The cokernel presentation of `H^q(F K)` is exact with epimorphic second map. -/
lemma exact_and_epi_cyclesHomologyShortComplexOfMap (K : CochainComplex A ℤ) (q : ℤ) :
    (cyclesHomologyShortComplexOfMap F K q).Exact ∧
      Epi (cyclesHomologyShortComplexOfMap F K q).g :=
  (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).2
    ⟨((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyIsCokernel (q - 1) q
      (by simp)⟩

/-- If the homology comparison is invertible, then `F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)` is exact
and its second map is an epimorphism. -/
lemma exact_and_epi_of_isIso_homologyComparison (K : CochainComplex A ℤ) (q : ℤ)
    [IsIso (homologyComparison F K q)] :
    (cyclesHomologyShortComplex F K q).Exact ∧ Epi (cyclesHomologyShortComplex F K q).g := by
  have : IsIso (cyclesHomologyShortComplexHom F K q) := by
    rw [ShortComplex.isIso_iff]
    exact ⟨inferInstanceAs (IsIso (𝟙 _)), isIso_cyclesComparison F K q,
      inferInstanceAs (IsIso (homologyComparison F K q))⟩
  let e := asIso (cyclesHomologyShortComplexHom F K q)
  obtain ⟨hex, hepi⟩ := exact_and_epi_cyclesHomologyShortComplexOfMap F K q
  refine ⟨(ShortComplex.exact_iff_of_iso e).1 hex, ?_⟩
  have hfac : (cyclesHomologyShortComplex F K q).g =
      e.inv.τ₂ ≫ (cyclesHomologyShortComplexOfMap F K q).g ≫ e.hom.τ₃ := by
    symm
    rw [← Category.assoc, e.inv.comm₂₃, Category.assoc, ← ShortComplex.comp_τ₃, e.inv_hom_id,
      ShortComplex.id_τ₃, Category.comp_id]
  rw [hfac]
  infer_instance

/-- If `F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)` is exact and its second map is an epimorphism, then
the homology comparison is invertible. -/
lemma isIso_homologyComparison_of_exact_of_epi (K : CochainComplex A ℤ) (q : ℤ)
    (hex : (cyclesHomologyShortComplex F K q).Exact)
    (hepi : Epi (cyclesHomologyShortComplex F K q).g) :
    IsIso (homologyComparison F K q) := by
  obtain ⟨c, hc₁, hc₂⟩ := (isIso_cyclesComparison F K q).out
  let X := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hT := hex.gIsCokernel
  have hw : F.map (K.toCycles (q - 1) q) ≫ c ≫ X.homologyπ q = 0 := by
    rw [← toCycles_comp_cyclesComparison_assoc, reassoc_of% hc₁]
    exact X.toCycles_comp_homologyπ (q - 1) q
  let j : F.obj (K.homology q) ⟶ X.homology q :=
    hT.desc (CokernelCofork.ofπ (c ≫ X.homologyπ q) hw)
  have hj : F.map (K.homologyπ q) ≫ j = c ≫ X.homologyπ q :=
    hT.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  refine ⟨j, ?_, ?_⟩
  · apply (cancel_epi (X.homologyπ q)).1
    rw [homologyπ_comp_homologyComparison_assoc, hj, reassoc_of% hc₁, Category.comp_id]
  · have : Epi (F.map (K.homologyπ q)) := hepi
    apply (cancel_epi (F.map (K.homologyπ q))).1
    rw [reassoc_of% hj, homologyπ_comp_homologyComparison, reassoc_of% hc₂, Category.comp_id]

/-- **The homology comparison is invertible if and only if `F` preserves the cokernel
presentation of the cohomology**: `H^q(F K) ⟶ F(H^q K)` is an isomorphism exactly when
`F(K^{q-1}) ⟶ F(Z^q K) ⟶ F(H^q K)` is exact with epimorphic second map. -/
theorem isIso_homologyComparison_iff (K : CochainComplex A ℤ) (q : ℤ) :
    IsIso (homologyComparison F K q) ↔
      (cyclesHomologyShortComplex F K q).Exact ∧ Epi (cyclesHomologyShortComplex F K q).g :=
  ⟨fun _ => exact_and_epi_of_isIso_homologyComparison F K q,
    fun h => isIso_homologyComparison_of_exact_of_epi F K q h.1 h.2⟩

end Complexes

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B]

/-- The homology comparison of a complex is invertible as soon as its transport to the derived
level is. -/
lemma isIso_homologyComparison_of_isIso_homotopyHomologyComparisonToDerived_app
    (K : CochainComplex A ℤ) (q : ℤ)
    (h : IsIso ((homotopyHomologyComparisonToDerived F q).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) :
    IsIso (homologyComparison F K q) := by
  have h₁ : IsIso ((homologyComparisonOnHomotopy F q).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
    rw [homotopyHomologyComparisonToDerived] at h
    simp only [NatTrans.comp_app] at h
    exact (isIso_comp_right_iff _ _).1 ((isIso_comp_left_iff _ _).1 h)
  rw [homologyComparisonOnHomotopy, Localization.liftNatTrans_app] at h₁
  simp only [NatTrans.comp_app, Category.assoc] at h₁
  have h₂ := (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 h₁)
  have i₁ : IsIso ((Functor.isoWhiskerRight
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q) F).inv.app K) :=
    ((Functor.isoWhiskerRight
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q) F).app K).isIso_inv
  have i₂ : IsIso ((Localization.Lifting.iso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)).inv.app K) :=
    ((Localization.Lifting.iso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)).app K).isIso_inv
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (IsIso.comp_isIso' i₁ i₂) h₂

/-- **The edge morphism is invertible at a K-injective complex only if the homology comparison
of that complex is.** -/
lemma isIso_homologyComparison_of_isIso_derivedHomologyComparison_app
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ)
    (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (h : IsIso ((derivedHomologyComparison F R α hA q).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    IsIso (homologyComparison F I q) := by
  have hα : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      (D := DerivedCategory A) (L := DerivedCategory.Qh) R α I hI
  refine isIso_homologyComparison_of_isIso_homotopyHomologyComparisonToDerived_app F I q ?_
  rw [← derivedHomologyComparison_fac_app F R α hA q]
  infer_instance

end Derived

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
