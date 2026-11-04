module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DegreewiseInvertedMap
public import StacksFrontier.Homology.DerivedComplete.AdicCompletionUnitSingle
public import StacksFrontier.RingTheory.Cech.AdicQuotientKernel
public import StacksFrontier.RingTheory.Cech.TermTensorFlat
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CechCompletedLocalCohomology

/-!
# The Čech completion comparison is a derived `I`-adic completion unit

Let `I` and `J` be ideals of a Noetherian ring `A`, let `g` be a finite generating family of `J`
and let `M` be a finite `A`-module.  The comparison map

`Dualizing.cechCompletionComparison : RΓ_{V(J)}(M) ⟶ lim_n C^•(g; M/IⁿM)`

is the image in `D(A)` of a map of complexes, assembled from the quotient maps `M ⟶ M/IⁿM`.
This file proves that it has the universal property of the derived `I`-adic completion unit:
composing with it is a bijection onto the maps out of `RΓ_{V(J)}(M)` into every derived
`I`-complete object.

## Main results

* `Stacks.Algebraization.bijective_comp_of_isIso_adicCompletionFunctor_map`: a morphism
  inverted by derived completion has the universal property of the completion unit.
* `Dualizing.isIso_adicCompletionFunctor_map_Q_map_cechCompletionComplexMap`: derived completion
  inverts the map of complexes `C^•(g; M) ⟶ lim_n C^•(g; M/IⁿM)`.
* `Dualizing.bijective_cechCompletionComparison_comp`: the comparison is a derived `I`-adic
  completion unit.
* `Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`: the
  canonical projections present `RΓ_{V(J)}(M)^∧` as a derived limit of the tower
  `n ↦ RΓ_{V(J)}(M/IⁿM)`.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale

universe u

namespace Stacks.Algebraization

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

variable {A : Type u} [CommRing A]

/-- **A morphism inverted by derived completion is a derived completion unit.** If derived
completion inverts `w : X ⟶ Y`, then composing with `w` is a bijection from the maps `Y ⟶ E` to
the maps `X ⟶ E` for every derived `I`-complete `E`. -/
theorem bijective_comp_of_isIso_adicCompletionFunctor_map (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (w : X ⟶ Y)
    (hw : IsIso ((adicCompletionFunctor A I hI).map w))
    (E : DerivedCategory (ModuleCat.{u} A)) (hE : IsDerivedComplete I E) :
    Function.Bijective (fun h : Y ⟶ E ↦ w ≫ h) := by
  set Λ := adicCompletionFunctor A I hI with hΛ
  set η := adicCompletionUnit A I hI with hη
  have hα : Function.Bijective (fun k : Λ.obj Y ⟶ E ↦ η.app Y ≫ k) :=
    completionUnit_comp_bijective I hI Y E hE
  have hβ : Function.Bijective (fun k : Λ.obj X ⟶ E ↦ η.app X ≫ k) :=
    completionUnit_comp_bijective I hI X E hE
  have hγ : Function.Bijective (fun k : Λ.obj Y ⟶ E ↦ Λ.map w ≫ k) := by
    refine ⟨fun k l hkl ↦ (cancel_epi (Λ.map w)).1 hkl, fun k ↦ ⟨inv (Λ.map w) ≫ k, ?_⟩⟩
    show Λ.map w ≫ inv (Λ.map w) ≫ k = k
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hnat : (fun h : Y ⟶ E ↦ w ≫ h) ∘ (fun k : Λ.obj Y ⟶ E ↦ η.app Y ≫ k) =
      (fun k : Λ.obj X ⟶ E ↦ η.app X ≫ k) ∘ (fun k : Λ.obj Y ⟶ E ↦ Λ.map w ≫ k) := by
    funext k
    show w ≫ η.app Y ≫ k = η.app X ≫ Λ.map w ≫ k
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun t : X ⟶ Λ.obj Y ↦ t ≫ k) (η.naturality w)
  refine (Function.Bijective.of_comp_iff _ hα).1 ?_
  rw [hnat]
  exact hβ.comp hγ

/-- A functor `Φ` on the derived category commuting with the shifts inverts the image of `u` under
the single functor in degree `i` as soon as it inverts its image under the single functor in
degree zero. -/
theorem isIso_adicCompletionFunctor_map_singleFunctor_map_of_zero {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] {D : Type*} [Category* D] [HasZeroObject D]
    [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (Φ : DerivedCategory C ⥤ D) [Φ.CommShift ℤ] (i : ℤ) {X Y : C} (u : X ⟶ Y)
    (h : IsIso (Φ.map ((DerivedCategory.singleFunctor C 0).map u))) :
    IsIso (Φ.map ((DerivedCategory.singleFunctor C i).map u)) := by
  have e : DerivedCategory.singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) (-i) ≅
      DerivedCategory.singleFunctor C i :=
    (DerivedCategory.singleFunctors C).shiftIso (-i) i 0 (by omega)
  have e₂ : (DerivedCategory.singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) (-i)) ⋙ Φ ≅
      (DerivedCategory.singleFunctor C 0 ⋙ Φ) ⋙ shiftFunctor D (-i) :=
    Functor.isoWhiskerLeft _ (Φ.commShiftIso (-i))
  have h₁ : IsIso (((DerivedCategory.singleFunctor C 0 ⋙ Φ) ⋙
      shiftFunctor D (-i)).map u) := by
    have h' : IsIso ((DerivedCategory.singleFunctor C 0 ⋙ Φ).map u) := h
    exact inferInstanceAs
      (IsIso ((shiftFunctor D (-i)).map ((DerivedCategory.singleFunctor C 0 ⋙ Φ).map u)))
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight e Φ) u).1
    ((NatIso.isIso_map_iff e₂ u).2 h₁)

end Stacks.Algebraization

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

variable (A : Type u) [CommRing A]

/-- A degree in which every term of a tower of complexes vanishes is a degree in which the
termwise inverse limit vanishes. -/
theorem isZero_limit_X (F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (h : ∀ n : ℕᵒᵖ, IsZero ((F.obj n).X i)) : IsZero ((limit F).X i) := by
  have hz : IsZero (limit (F ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) :=
    (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun j ↦ (h j).eq_of_tgt _ _)
  exact hz.of_iso (preservesLimitIso (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) F)

/-- If `ker f = J • ⊤`, then `ker (a ≫ f ≫ b) = J • ⊤` for isomorphisms `a` and `b`. -/
theorem ker_comp_comp_of_isIso {X X' Y Y' : ModuleCat.{u} A} (a : X ⟶ X') [IsIso a]
    (f : X' ⟶ Y') (b : Y' ⟶ Y) [IsIso b] (J : Ideal A)
    (hf : LinearMap.ker f.hom = J • (⊤ : Submodule A X')) :
    LinearMap.ker (a ≫ f ≫ b).hom = J • (⊤ : Submodule A X) := by
  have hb : Function.Injective b.hom := (ModuleCat.mono_iff_injective b).1 inferInstance
  have ha : Function.Injective a.hom := (ModuleCat.mono_iff_injective a).1 inferInstance
  have hasurj : Function.Surjective a.hom := (ModuleCat.epi_iff_surjective a).1 inferInstance
  have hmap : Submodule.map a.hom (J • (⊤ : Submodule A X)) = J • (⊤ : Submodule A X') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hasurj]
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · simp only [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply] at hx
    have h0 : f.hom (a.hom x) = 0 := hb (by rw [hx, map_zero])
    have hmem : a.hom x ∈ J • (⊤ : Submodule A X') := hf ▸ LinearMap.mem_ker.2 h0
    rw [← hmap] at hmem
    obtain ⟨y, hy, hxy⟩ := hmem
    rwa [← ha hxy]
  · simp only [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    have hmem : a.hom x ∈ J • (⊤ : Submodule A X') := hmap ▸ Submodule.mem_map_of_mem hx
    rw [← hf, LinearMap.mem_ker] at hmem
    rw [hmem, map_zero]

/-- **Degreewise, the Čech complex of the quotient map `M ⟶ M/IⁿM` has kernel `Iⁿ` times the
term.** -/
theorem ker_extendedCechFunctor_map_adicQuotientProjection_f (I : Ideal A) {r : ℕ}
    (g : Fin r → A) (M : ModuleCat.{u} A) (n p : ℕ) :
    LinearMap.ker (((Stacks.LocalCohomology.extendedCechFunctor g).map
        (adicQuotientProjection A I M n)).f (p : ℤ)).hom =
      I ^ n • (⊤ : Submodule A
        (((Stacks.LocalCohomology.extendedCechFunctor g).obj M).X (p : ℤ))) := by
  have hfp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
  rw [show ((Stacks.LocalCohomology.extendedCechFunctor g).map
      (adicQuotientProjection A I M n)).f (p : ℤ) =
      (HomologicalComplex.extendXIso (Cech.cechComplex g (M : Type u))
          ComplexShape.embeddingUpNat hfp).hom ≫
        (Stacks.LocalCohomology.cechComplexMap g (adicQuotientProjection A I M n)).f p ≫
        (HomologicalComplex.extendXIso
            (Cech.cechComplex g ((adicQuotientModuleSystem A I M).obj (op n) : Type u))
            ComplexShape.embeddingUpNat hfp).inv from
    HomologicalComplex.extendMap_f _ _ hfp]
  refine ker_comp_comp_of_isIso A
    (HomologicalComplex.extendXIso (Cech.cechComplex g (M : Type u))
      ComplexShape.embeddingUpNat hfp).hom
    ((Stacks.LocalCohomology.cechComplexMap g (adicQuotientProjection A I M n)).f p)
    (HomologicalComplex.extendXIso
      (Cech.cechComplex g ((adicQuotientModuleSystem A I M).obj (op n) : Type u))
      ComplexShape.embeddingUpNat hfp).inv (I ^ n) ?_
  exact Stacks.LocalCohomology.ker_cechTermMap_mkQ g M (I ^ n) p

/-- Derived completion inverts the image under the degree-zero single functor of the degree-`p`
component, `p ≥ 0`, of the map of complexes `C^•(g; M) ⟶ lim_n C^•(g; M/IⁿM)`. -/
theorem isIso_adicCompletionFunctor_map_single_cechCompletionComplexMap_f
    [IsNoetherianRing A] (I : Ideal A) {r : ℕ} (g : Fin r → A) (M : ModuleCat.{u} A)
    [Module.Finite A (M : Type u)] (p : ℕ) :
    IsIso ((Stacks.Algebraization.adicCompletionFunctor A I I.fg_of_isNoetherianRing).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        ((cechCompletionComplexMap A I g M).f (p : ℤ)))) := by
  have hfp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
  have hI : I.FG := I.fg_of_isNoetherianRing
  set F := cechAdicQuotientSystem A I g M with hF
  set E := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) (p : ℤ) with hE
  set c : ∀ n : ℕ, ((Stacks.LocalCohomology.extendedCechFunctor g).obj M).X (p : ℤ) ⟶
      (F ⋙ E).obj (op n) := fun n ↦
    ((Stacks.LocalCohomology.extendedCechFunctor g).map
      (adicQuotientProjection A I M n)).f (p : ℤ) with hc0
  have hc : ∀ (m n : ℕ) (h : m ≤ n), c n ≫ (F ⋙ E).map (homOfLE h).op = c m := by
    intro m n h
    have e2 : (Stacks.LocalCohomology.extendedCechFunctor g).map
          (adicQuotientProjection A I M n) ≫
        (Stacks.LocalCohomology.extendedCechFunctor g).map
          ((adicQuotientModuleSystem A I M).map (homOfLE h).op) =
        (Stacks.LocalCohomology.extendedCechFunctor g).map
          (adicQuotientProjection A I M m) := by
      rw [← Functor.map_comp, adicQuotientProjection_comp_map A I M h]
    have e3 := HomologicalComplex.congr_hom e2 (p : ℤ)
    rwa [HomologicalComplex.comp_f] at e3
  have hsurj : ∀ n : ℕ, Function.Surjective (c n).hom := fun n ↦
    surjective_extendedCechFunctor_map_f g (adicQuotientProjection A I M n)
      (Submodule.mkQ_surjective _) (p : ℤ)
  have hker : ∀ n : ℕ, LinearMap.ker (c n).hom = I ^ n •
      (⊤ : Submodule A (((Stacks.LocalCohomology.extendedCechFunctor g).obj M).X (p : ℤ))) :=
    fun n ↦ ker_extendedCechFunctor_map_adicQuotientProjection_f A I g M n p
  set Qc := E.mapCone (limit.cone F) with hQc0
  have hQc : IsLimit Qc := isLimitOfPreserves E (limit.isLimit F)
  have hu : ∀ n : ℕ, (cechCompletionComplexMap A I g M).f (p : ℤ) ≫ Qc.π.app (op n) = c n := by
    intro n
    have e := HomologicalComplex.congr_hom (cechCompletionComplexMap_comp_π A I g M n) (p : ℤ)
    rwa [HomologicalComplex.comp_f] at e
  let : IsAdicComplete I (AdicCompletion I (Cech.cechTerm g (M : Type u) p)) :=
    AdicCompletion.isAdicComplete hI
  obtain ⟨e0⟩ :=
    Stacks.LocalCohomology.nonempty_iso_adicCompletionFunctor_single_cechTerm I hI g
      (M : Type u) p
  have hiso : Nonempty
      ((Stacks.Algebraization.adicCompletionFunctor A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (((Stacks.LocalCohomology.extendedCechFunctor g).obj M).X (p : ℤ))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (AdicCompletion I (Cech.cechTerm g (M : Type u) p)))) :=
    ⟨(Stacks.Algebraization.adicCompletionFunctor A I hI).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
          (HomologicalComplex.extendXIso (Cech.cechComplex g (M : Type u))
            ComplexShape.embeddingUpNat hfp)) ≪≫ e0⟩
  exact Stacks.Algebraization.isIso_adicCompletionFunctor_map_single_map_of_adicTower I hI _
    (F ⋙ E) c hc hsurj hker Qc hQc _ hu _ hiso

/-- **Derived completion inverts the map of complexes `C^•(g; M) ⟶ lim_n C^•(g; M/IⁿM)`.** -/
theorem isIso_adicCompletionFunctor_map_Q_map_cechCompletionComplexMap
    [IsNoetherianRing A] (I : Ideal A) {r : ℕ} (g : Fin r → A) (M : ModuleCat.{u} A)
    [Module.Finite A (M : Type u)] :
    IsIso ((Stacks.Algebraization.adicCompletionFunctor A I I.fg_of_isNoetherianRing).map
      (DerivedCategory.Q.map (cechCompletionComplexMap A I g M))) := by
  have hI : I.FG := I.fg_of_isNoetherianRing
  set Φ := Stacks.Algebraization.adicCompletionFunctor A I hI with hΦ
  let adj := Stacks.Algebraization.adicCompletionAdjunction A I hI
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (Dualizing.derivedCompletion.{u, u} A I hI).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have hzeroK : ∀ i : ℤ, i < 0 ∨ (r : ℤ) + 1 ≤ i →
      IsZero (((Stacks.LocalCohomology.extendedCechFunctor g).obj M).X i) := fun i hi ↦
    Stacks.LocalCohomology.isZero_extendedCechComplex_X g M i hi
  have hzeroL : ∀ i : ℤ, i < 0 ∨ (r : ℤ) + 1 ≤ i →
      IsZero ((limit (cechAdicQuotientSystem A I g M)).X i) := fun i hi ↦
    isZero_limit_X A _ i fun n ↦
      Stacks.LocalCohomology.isZero_extendedCechComplex_X g _ i hi
  have hfin : ∀ P : ℤ → Prop, (∀ i : ℤ, i < 0 ∨ (r : ℤ) + 1 ≤ i → P i) → {i | ¬ P i}.Finite :=
    fun P hP ↦ (Set.finite_Icc (0 : ℤ) (r : ℤ)).subset fun i hi ↦ by
      by_contra hcon
      exact hi (hP i (by simp only [Set.mem_Icc, not_and_or, not_le] at hcon; omega))
  have hK := hfin _ hzeroK
  have hL := hfin _ hzeroL
  refine Stacks.DerivedCategory.BoundedInduction.isIso_map_Q_map_of_isIso_map_singleFunctor_map
    Φ (cechCompletionComplexMap A I g M) hK hL fun i ↦ ?_
  by_cases hi : 0 ≤ i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
    exact Stacks.Algebraization.isIso_adicCompletionFunctor_map_singleFunctor_map_of_zero Φ _ _
      (isIso_adicCompletionFunctor_map_single_cechCompletionComplexMap_f A I g M p)
  · refine IsZero.isIso (Functor.map_isZero _ (Functor.map_isZero _ (hzeroK i (Or.inl ?_))))
      (Functor.map_isZero _ (Functor.map_isZero _ (hzeroL i (Or.inl ?_)))) _ <;> omega

/-- **The Čech completion comparison is a derived `I`-adic completion unit.** Composing with
`Dualizing.cechCompletionComparison` is a bijection from the maps out of `lim_n C^•(g; M/IⁿM)`
onto the maps out of `RΓ_{V(J)}(M)`, for every derived `I`-complete target. -/
theorem bijective_cechCompletionComparison_comp [IsNoetherianRing A]
    (I J : Ideal A) (hJ : J.FG) {r : ℕ} (g : Fin r → A) (hg : Ideal.span (Set.range g) = J)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)] :
    ∀ E : DerivedCategory (ModuleCat.{u} A), IsDerivedComplete I E →
      Function.Bijective (fun h : cechCompletedLocalCohomology A I g M ⟶ E ↦
        cechCompletionComparison A I J hJ g hg M ≫ h) := by
  intro E hE
  refine Stacks.Algebraization.bijective_comp_of_isIso_adicCompletionFunctor_map
    I I.fg_of_isNoetherianRing _ ?_ E hE
  rw [cechCompletionComparison, Functor.map_comp]
  have h₂ := isIso_adicCompletionFunctor_map_Q_map_cechCompletionComplexMap A I g M
  infer_instance

/-- **The canonical projections present `RΓ_{V(J)}(M)^∧` as a derived limit of the tower
`n ↦ RΓ_{V(J)}(M/IⁿM)`**: part (1) of [Stacks, Tag 0EEW]. -/
theorem isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite
    [IsNoetherianRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A)
    [Module.Finite A (M : Type u)] :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) (completedLocalCohomology A I J hI hJ M)
      (completedLocalCohomologyProjection A I J hI hJ M) := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  change Ideal.span (Set.range g) = J at hg
  exact isDerivedLimitWithProjections_completedLocalCohomologyProjection A I J hI hJ M
    (cechCompletedLocalCohomology A I g M) (cechCompletedProjection A I J hJ g hg M)
    (isDerivedLimitWithProjections_cechCompletedProjection A I J hJ g hg M)
    (cechCompletionComparison A I J hJ g hg M)
    (cechCompletionComparison_comp_cechCompletedProjection A I J hJ g hg M)
    (bijective_cechCompletionComparison_comp A I J hJ g hg M)

end Dualizing

end
