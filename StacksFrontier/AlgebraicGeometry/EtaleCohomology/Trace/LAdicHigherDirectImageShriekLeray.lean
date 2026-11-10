module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiltrationWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveSheafBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence

/-!
# The Leray weight implication for `Rʳ g_! G`

Let `g : U ⟶ W` be separated of finite type over a finite field `k`, `G` an ℓ-adic sheaf on `U`,
and `Rʳ g_! G` the ℓ-adic sheaves of `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`.
If the eigenvalues of the geometric Frobenius on every `H^p_c(W_k̄, Rʳ g_! G ⊗ ℚ_ℓ)` have weights
`≤ b + r + p`, then those on `Hⁱ_c(U_k̄, G ⊗ ℚ_ℓ)` have weights `≤ b + i`: this is the Leray step
of the reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3).

The proof runs on the levels `G'ₘ` of the flat model of `G`. The comparison
`RΓ_c(U_k̄, G'ₘ) ≅ RΓ_c(W_k̄, C G'ₘ)` with `C G'ₘ` a complex computing `Rg_! G'ₘ`
(`Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`, Tags 0F7J and 0F7L) carries the
Frobenius of `U` to that of `W`. The canonical truncations of `C G'ₘ` give exact sequences of
towers `H^{i-n}_c(W_k̄, Rⁿ g_! G'ₘ) → Hⁱ_c(W_k̄, τ_{≥ n} C G'ₘ) → Hⁱ_c(W_k̄, τ_{≥ n+1} C G'ₘ)`
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTruncation`), and descending
induction on `n` propagates the bound through the rational limits; the first terms are the towers
of `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyNormMixedOfWeightLE_higherDirectImageShriek_iff`.

## Main results

* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLim_of_descending`: weights along
  a descending filtration of towers.
* `Stacks.EtaleCohomology.LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily`.

## Implementation notes

`compactSupportFrobeniusFunctor` and `derivedLowerShriek` live in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u v

namespace Stacks.EtaleCohomology

/-! ### Weights along a descending filtration of towers -/

section Towers

variable {ℓ : ℕ} [Fact ℓ.Prime] [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])]

/-- The rational limit of a levelwise zero tower is zero. -/
theorem isZero_rationalLim_of_isZero (A : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (hA : ∀ m, IsZero (A.obj m)) : IsZero ((rationalLim (ℓ := ℓ)).obj A) := by
  have h : IsZero (lim.obj A) := by
    rw [IsZero.iff_id_eq_zero]
    exact limit.hom_ext (fun m => (hA m).eq_of_tgt _ _)
  exact (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_isZero h

/-- The middle of an exact sequence of vector spaces with finite dimensional ends is finite
dimensional. -/
theorem finiteDimensional_of_function_exact {K M N P : Type*} [Field K] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module K M] [Module K N] [Module K P]
    [FiniteDimensional K M] [FiniteDimensional K P] {f : M →ₗ[K] N} {g : N →ₗ[K] P}
    (h : Function.Exact f g) : FiniteDimensional K N := by
  have h' : Function.Exact f g.rangeRestrict := by
    intro y
    rw [← h y]
    exact ⟨congrArg Subtype.val, fun hy => Subtype.ext hy⟩
  exact Module.Finite.of_exact h' g.surjective_rangeRestrict

/-- One step of the descending induction: weights pass from the ends of an exact sequence of
towers, the first levelwise finite, to its middle. -/
theorem isCharpolyNormMixedOfWeightLE_rationalLim_step {A B C : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (α : A ⟶ B) (β : B ⟶ C) (hex : ∀ m, Function.Exact (α.app m) (β.app m))
    (hfin : ∀ m, Finite (A.obj m)) (φA : A ⟶ A) (φB : B ⟶ B) (φC : C ⟶ C)
    (hα : φA ≫ α = α ≫ φB) (hβ : φB ≫ β = β ≫ φC)
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj C)] {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hA : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φA).hom)
    (hC : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φC).hom) :
    ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj B),
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φB).hom := by
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj B) :=
    finiteDimensional_of_function_exact (exact_rationalLimMap_of_finite α β hex hfin)
  exact ⟨inferInstance, isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact α β hex hfin φA φB
    φC hα hβ hA hC⟩

/-- **Weights along a descending filtration of towers.** Let `T n` and `G n` (`n : ℤ`) be towers
of `ℤ_ℓ`-modules with endomorphisms, and maps `G n → T n → T (n+1)` exact at every level and
equivariant. Suppose `T n` vanishes for `n > i`, and for `n ≥ 0` every `G n` is levelwise finite,
with finite dimensional rational limit whose characteristic roots have absolute values
`q ^ (w / 2)` with `w ≤ b`. Then for every `n ≥ 0` the rational limit of `T n` is finite
dimensional with the same bound. -/
theorem isCharpolyNormMixedOfWeightLE_rationalLim_of_descending
    (T G : ℤ → (ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])) (a : ∀ n, G n ⟶ T n) (c : ∀ n, T n ⟶ T (n + 1))
    (hex : ∀ n m, Function.Exact ((a n).app m) ((c n).app m))
    (i : ℤ) (hzero : ∀ n, i < n → ∀ m, IsZero ((T n).obj m))
    (hfin : ∀ n, 0 ≤ n → ∀ m, Finite ((G n).obj m))
    (φT : ∀ n, T n ⟶ T n) (φG : ∀ n, G n ⟶ G n)
    (ha : ∀ n, φG n ≫ a n = a n ≫ φT n) (hc : ∀ n, φT n ≫ c n = c n ≫ φT (n + 1))
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hG : ∀ n, 0 ≤ n → ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (G n)),
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φG n)).hom)
    (n : ℤ) (hn : 0 ≤ n) :
    ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (T n)),
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φT n)).hom := by
  have hz : ∀ n, i < n → ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (T n)),
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φT n)).hom := by
    intro n hn
    have : Subsingleton ((rationalLim (ℓ := ℓ)).obj (T n)) :=
      ModuleCat.subsingleton_of_isZero (isZero_rationalLim_of_isZero (ℓ := ℓ) _ (hzero n hn))
    exact ⟨inferInstance, isCharpolyNormMixedOfWeightLE_of_subsingleton _⟩
  suffices H : ∀ k : ℕ, ∀ n, i + 1 - k ≤ n → 0 ≤ n →
      ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (T n)),
        IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φT n)).hom from
    H (i + 1 - n).toNat n (by omega) hn
  intro k
  induction k with
  | zero => exact fun n h _ => hz n (by omega)
  | succ k ih =>
    intro n h hn
    by_cases h' : i + 1 - k ≤ n
    · exact ih n h' hn
    · obtain ⟨_, hT⟩ := ih (n + 1) (by omega) (by omega)
      obtain ⟨_, hGn⟩ := hG n hn
      exact isCharpolyNormMixedOfWeightLE_rationalLim_step (a n) (c n) (hex n) (hfin n hn)
        (φG n) (φT n) (φT (n + 1)) (ha n) (hc n) hGn hT

end Towers

/-- Weights of the rational limits of two towers isomorphic compatibly with endomorphisms agree. -/
theorem isCharpolyNormMixedOfWeightLE_rationalLim_iff_of_iso {ℓ : ℕ} [Fact ℓ.Prime]
    [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{u + 1} ℤ_[ℓ])] {A A' : ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ]}
    (e : A ≅ A') (φ : A ⟶ A) (φ' : A' ⟶ A') (h : φ ≫ e.hom = e.hom ≫ φ')
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A')] {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φ).hom ↔
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φ').hom :=
  isCharpolyNormMixedOfWeightLE_iff_of_iso ((rationalLim (ℓ := ℓ)).mapIso e) _ _ (by
    rw [Functor.mapIso_hom, ← Functor.map_comp, h, Functor.map_comp])

/-! ### The complex computing `Rg_!` -/

section LerayComplex

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} (g : U ⟶ W)
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
    CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))

/-- **`Hⁿ(C K) ≅ Rⁿ g_! K`** for a complex functor `C` computing `Rg_!`. -/
def lerayComplexHomologyIso
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) (n : ℤ) :
    C ⋙ CochainComplex.Plus.ι _ ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n ≅
      (IsLPowerTorsion ℓ U.1).ι ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg n :=
  Functor.isoWhiskerLeft C (Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
      (DerivedCategory.homologyFunctorFactors _ n).symm) ≪≫
    (Functor.associator C DerivedCategory.Plus.Q
      (DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} ℤ_[ℓ] W.1) n)).symm ≪≫
    Functor.isoWhiskerRight ψ (DerivedCategory.Plus.homologyFunctor _ n)

/-- **`C K` has no cohomology in negative degrees**, as `Rg_! K` for a sheaf `K`. -/
theorem isGE_lerayComplex (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg)
    (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) : (C.obj K).obj.IsGE 0 := by
  have h0 : ((DerivedCategory.Plus.Q).obj ((singlePlus (EtaleModules.{u, 0} ℤ_[ℓ]
      (B.inclusion.obj U))).obj K.obj)).IsGE 0 := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      K.obj)).IsGE 0
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  rw [← DerivedCategory.isGE_Q_obj_iff]
  exact (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).2
    (@DerivedCategory.Plus.TStructure.t.isGE_of_iso _ _ _ _ _ _ _ _ _ (ψ.app K).symm 0
      (@isGE_derivedLowerShriek_obj _ _ _ _ (B.inclusion.map g) jg _ 0 h0))

end LerayComplex

/-! ### The Leray weight implication -/

section Leray

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The levels of the flat model of `G`, as ℓ-power torsion sheaves. -/
abbrev LAdicSheaf.flatModelTorsionTower (G : LAdicSheaf B U ℓ) :
    ℕᵒᵖ ⥤ (IsLPowerTorsion ℓ U.1).FullSubcategory :=
  ObjectProperty.lift _ (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G))
    (fun m => ⟨m.unop + 1, LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop⟩)

/-- `Rⁿ g_! G'ₘ` along the levels of the flat model, from a complex functor computing `Rg_!`. -/
def LAdicSheaf.lerayGradedTowerIso (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) (n i : ℤ) :
    (LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙ compactSupportGradedHomology ℤ_[ℓ] fW jW kbar n i ≅
      LAdicSheaf.lowerShriekTower B ℓ g jg G n ⋙
        compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar (-n + i) :=
  Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
      (compactSupportGradedHomologyIso ℤ_[ℓ] fW jW kbar n i (-n + i) rfl) ≪≫
    Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G)
      (Functor.isoWhiskerRight (lerayComplexHomologyIso B ℓ g jg C ψ n)
        (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar (-n + i)))

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] in
/-- The isomorphism `LAdicSheaf.lerayGradedTowerIso` intertwines the Frobenius on the compactly
supported cohomology of the graded pieces of `C G'ₘ` with the Frobenius on
`H^{i-n}_c(W_k̄, Rⁿ g_! G'ₘ)`. -/
theorem LAdicSheaf.lerayGradedTowerIso_hom_frobenius (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) (n i : ℤ) :
    Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
        (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
          (CochainComplex.Plus.gradedFunctor n) i) ≫
      (LAdicSheaf.lerayGradedTowerIso g jg fW jW kbar G C ψ n i).hom =
    (LAdicSheaf.lerayGradedTowerIso g jg fW jW kbar G C ψ n i).hom ≫
      Functor.whiskerLeft (LAdicSheaf.lowerShriekTower B ℓ g jg G n)
        (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard (-n + i)) := by
  have h₁ := congrArg (Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C))
    (compactSupportGradedHomologyIso_hom_frobenius ℤ_[ℓ] fW jW kbar p q hcard n i (-n + i) rfl)
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at h₁
  have h₂ : Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
        (Functor.whiskerLeft (CochainComplex.Plus.ι (EtaleModules.{u, 0} ℤ_[ℓ] W.1) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n)
          (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
            ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} ℤ_[ℓ] W.1)).functor 0)
            (-n + i))) ≫
      (Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G)
        (Functor.isoWhiskerRight (lerayComplexHomologyIso B ℓ g jg C ψ n)
          (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar (-n + i)))).hom =
      (Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G)
        (Functor.isoWhiskerRight (lerayComplexHomologyIso B ℓ g jg C ψ n)
          (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar (-n + i)))).hom ≫
        Functor.whiskerLeft (LAdicSheaf.lowerShriekTower B ℓ g jg G n)
          (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard (-n + i)) :=
    NatTrans.ext (funext fun m => ((compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard
      (-n + i)).naturality ((lerayComplexHomologyIso B ℓ g jg C ψ n).hom.app
        ((LAdicSheaf.flatModelTorsionTower G).obj m))).symm)
  change _ ≫ ((Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
      (compactSupportGradedHomologyIso ℤ_[ℓ] fW jW kbar n i (-n + i) rfl)).hom ≫ _) =
    ((Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
      (compactSupportGradedHomologyIso ℤ_[ℓ] fW jW kbar n i (-n + i) rfl)).hom ≫ _) ≫ _
  rw [Functor.isoWhiskerLeft_hom, reassoc_of% h₁, Category.assoc]
  exact congrArg _ h₂

omit [Fintype k] [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] in
/-- The graded pieces `H^{i-r}_c(W_k̄, Rʳ g_! G'ₘ)` of the Leray tower are finite. -/
theorem LAdicSheaf.finite_lerayGradedTower (hT : LowerShriekConstructibilityInput B)
    (hfinT : ∀ F : EtaleModules.{u, 0} ℤ_[ℓ] W.1,
      IsBigSiteConstructibleEtaleModule.{u, 0} B W ℤ_[ℓ] F → IsLPowerTorsion ℓ W.1 F →
        ∀ a, Finite ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar a).obj F))
    (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) (r : ℕ) (i : ℤ)
    (m : ℕᵒᵖ) :
    Finite (((LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙
      compactSupportGradedHomology ℤ_[ℓ] fW jW kbar r i).obj m) := by
  have hf := hfinT _ (hT (B.inclusion.map g) jg ℤ_[ℓ] _
      (LAdicSheaf.isConstructibleEtaleModule_padicTower _ m.unop)
      (LAdicSheaf.isTorsionEtaleModule_padicTower _ m.unop) r)
    ⟨m.unop + 1, LAdicSheaf.lowerShriekTower_annihilated B ℓ g jg G r m.unop⟩ (-r + i)
  exact @Finite.of_equiv _ _ hf
    ((LAdicSheaf.lerayGradedTowerIso g jg fW jW kbar G C ψ r i).app m).toLinearEquiv.symm.toEquiv

/-- The weight bound `≤ b + i` on the graded pieces `H^{i-r}_c(W_k̄, Rʳ g_! G'ₘ)` of the Leray
tower, from the bound `≤ b + r + a` on `H^a_c(W_k̄, Rʳ g_! G)`. -/
theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_lerayGradedTower
    (hT : LowerShriekConstructibilityInput B)
    (hfinW : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar W fW)
    (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg)
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} (b : ℤ)
    (hR : ∀ (r : ℕ) (a : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B W ℓ fW jW kbar
          (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) a)],
      IsCharpolyNormMixedOfWeightLE q' ι (b + r + a)
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B W ℓ fW jW kbar p q hcard
          (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) a).hom)
    (r : ℕ) (i : ℤ) :
    ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
        ((LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙
          compactSupportGradedHomology ℤ_[ℓ] fW jW kbar r i)),
      IsCharpolyNormMixedOfWeightLE q' ι (b + i) ((rationalLim.{u + 1} (ℓ := ℓ)).map
        (Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
          (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
            (CochainComplex.Plus.gradedFunctor r) i))).hom := by
  have hc := LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput
    B ℓ g jg hT G r
  have := (hfinW jW (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) (-r + i)).1
  have := LAdicSheaf.finiteDimensional_rationalLim_lowerShriekTower B ℓ g jg fW jW kbar G r hc
    (-r + i)
  let e := LAdicSheaf.lerayGradedTowerIso g jg fW jW kbar G C ψ r i
  have := finiteDimensional_rationalLim_of_iso.{u + 1} (ℓ := ℓ) e.symm
  refine ⟨inferInstance, ?_⟩
  rw [isCharpolyNormMixedOfWeightLE_rationalLim_iff_of_iso e _ _
    (LAdicSheaf.lerayGradedTowerIso_hom_frobenius g jg fW jW kbar p q hcard G C ψ r i),
    ← LAdicSheaf.isCharpolyNormMixedOfWeightLE_higherDirectImageShriek_iff B ℓ g jg fW jW kbar
      p q hcard G r hc (-r + i)]
  have h := hR r (-r + i)
  rwa [show b + (r : ℤ) + (-r + i) = b + i by ring] at h

/-- The comparison `Hⁱ_c(U_k̄, G'ₘ) ≅ Hⁱ_c(W_k̄, C G'ₘ)` along the levels of the flat model. -/
def LAdicSheaf.lerayCompactSupportTowerIso
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW))) (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (φ : LAdicSheaf.torsionCompactSupport B ℓ g fW kbar jU ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar) (i : ℤ) :
    LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar i ≅
      (LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙
        compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i :=
  Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G) (Functor.isoWhiskerRight φ
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i))

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] in
/-- The isomorphism `LAdicSheaf.lerayCompactSupportTowerIso` intertwines the Frobenius of `U` with
that of `W`, given a comparison `φ` compatible with the Frobenius. -/
theorem LAdicSheaf.lerayCompactSupportTowerIso_hom_frobenius
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW))) (G : LAdicSheaf B U ℓ)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (φ : LAdicSheaf.torsionCompactSupport B ℓ g fW kbar jU ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar)
    (hφ : Functor.whiskerLeft ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _)
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar
          p q hcard) ≫ φ.hom =
      φ.hom ≫ Functor.whiskerLeft C
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard)) (i : ℤ) :
    Functor.whiskerLeft (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G))
        (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar p q hcard i) ≫
      (LAdicSheaf.lerayCompactSupportTowerIso g fW jW kbar jU G C φ i).hom =
    (LAdicSheaf.lerayCompactSupportTowerIso g fW jW kbar jU G C φ i).hom ≫
      Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
        (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard (𝟭 _) i) := by
  refine NatTrans.ext (funext fun m => ?_)
  have h := congrArg (fun t => (DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{u + 1} ℤ_[ℓ]) i).map (t.app ((LAdicSheaf.flatModelTorsionTower G).obj m))) hφ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp] at h
  exact h

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian U.1] [AlgebraicGeometry.IsNoetherian W.1]
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] [Fintype k] [LocallyOfFiniteType fW] [QuasiCompact fW]
  [IsSeparated fW] in
/-- On a tower of complexes computing `Rg_!`, the truncation `τ_{≥ 0}` induces an isomorphism on
`Hⁱ_c(W_k̄, -)`. -/
theorem LAdicSheaf.isIso_whiskerLeft_πTruncGE_lerayComplex
    (P : ℕᵒᵖ ⥤ (IsLPowerTorsion ℓ U.1).FullSubcategory)
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) (i : ℤ) :
    IsIso (Functor.whiskerLeft (P ⋙ C) (Functor.whiskerRight (CochainComplex.Plus.πTruncGE 0)
      (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro m
  have : ((P ⋙ C).obj m).obj.IsGE 0 := isGE_lerayComplex B ℓ g jg C ψ (P.obj m)
  exact isIso_compactSupport_πTruncGE_zero ℤ_[ℓ] fW jW kbar i ((P ⋙ C).obj m)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] in
/-- **The `U` side of the Leray weight implication**: a weight bound on `Hⁱ_c(W_k̄, τ_{≥ 0} C G'ₘ)`
gives the same bound on `Hⁱ_c(U_k̄, G ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_lerayTruncTower
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)))
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg)
    (φ : LAdicSheaf.torsionCompactSupport B ℓ g fW kbar jU ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar)
    (hφ : Functor.whiskerLeft ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _)
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar
          p q hcard) ≫ φ.hom =
      φ.hom ≫ Functor.whiskerLeft C
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard))
    (G : LAdicSheaf B U ℓ) {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      (B.inclusion.map g ≫ fW) jU kbar G i)]
    (hW : ∃ _ : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
        ((LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙
          compactSupportTruncHomology ℤ_[ℓ] fW jW kbar 0 i)),
      IsCharpolyNormMixedOfWeightLE q' ι w ((rationalLim.{u + 1} (ℓ := ℓ)).map
        (Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
          (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
            (CochainComplex.Plus.truncGEFunctor 0) i))).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map g ≫ fW) jU
        kbar p q hcard G i).hom := by
  obtain ⟨_, hW⟩ := hW
  let N := LAdicSheaf.torsionBound G
  have h₁ := LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel G N
  have h₂ := LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel G N
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      (B.inclusion.map g ≫ fW) jU kbar (LAdicSheaf.flatModel B ℓ G) i) :=
    LinearEquiv.finiteDimensional
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso
        B U ℓ (B.inclusion.map g ≫ fW) jU kbar (LAdicSheaf.toTorsionFreeModel G N)
        (LAdicSheaf.fromTorsionFreeModel G N) N h₁ h₂ i).toLinearEquiv
  rw [isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_isogeny
    B U ℓ (B.inclusion.map g ≫ fW) jU kbar p q hcard (LAdicSheaf.toTorsionFreeModel G N)
    (LAdicSheaf.fromTorsionFreeModel G N) N h₁ h₂ i]
  let e₁ := LAdicSheaf.lerayCompactSupportTowerIso g fW jW kbar jU G C φ i
  have := LAdicSheaf.isIso_whiskerLeft_πTruncGE_lerayComplex g jg fW jW kbar
    (LAdicSheaf.flatModelTorsionTower G) C ψ i
  let e₂ : (LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙
        compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i ≅
      (LAdicSheaf.flatModelTorsionTower G ⋙ C) ⋙ compactSupportTruncHomology ℤ_[ℓ] fW jW kbar 0 i :=
    asIso (Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
      (Functor.whiskerRight (CochainComplex.Plus.πTruncGE 0)
        (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i)))
  have he₂ : Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
        (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard (𝟭 _) i) ≫ e₂.hom =
      e₂.hom ≫ Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
        (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor 0) i) := by
    change _ ≫ Functor.whiskerLeft _ _ = Functor.whiskerLeft _ _ ≫ _
    simp only [← Functor.whiskerLeft_comp, compactSupportFrobeniusAlong_whiskerRight]
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} (ℓ := ℓ) (e₁ ≪≫ e₂).symm
  rwa [LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff
    B U ℓ (B.inclusion.map g ≫ fW) jU kbar p q hcard _ i,
    isCharpolyNormMixedOfWeightLE_rationalLim_iff_of_iso (e₁ ≪≫ e₂) _ _ (by
      calc _ = (Functor.whiskerLeft (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G))
              (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar p q hcard i) ≫
              e₁.hom) ≫ e₂.hom := (Category.assoc _ _ _).symm
        _ = (e₁.hom ≫ Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
              (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard (𝟭 _) i)) ≫ e₂.hom := by
          rw [LAdicSheaf.lerayCompactSupportTowerIso_hom_frobenius g fW jW kbar p q hcard jU G C φ
            hφ i]
        _ = e₁.hom ≫ (e₂.hom ≫ Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G ⋙ C)
              (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
                (CochainComplex.Plus.truncGEFunctor 0) i)) := by rw [Category.assoc, he₂]
        _ = _ := (Category.assoc _ _ _).symm)]

/-- **The Leray weight implication, from a complex functor computing `Rg_!` compatibly with the
Frobenius** (the core of Tag 03VH's Leray step). -/
theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_lerayComplex
    (hT : LowerShriekConstructibilityInput B)
    (hfinT : ∀ F : EtaleModules.{u, 0} ℤ_[ℓ] W.1,
      IsBigSiteConstructibleEtaleModule.{u, 0} B W ℤ_[ℓ] F → IsLPowerTorsion ℓ W.1 F →
        ∀ a, Finite ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar a).obj F))
    (hfinW : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar W fW)
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)))
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg)
    (φ : LAdicSheaf.torsionCompactSupport B ℓ g fW kbar jU ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar)
    (hφ : Functor.whiskerLeft ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _)
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar
          p q hcard) ≫ φ.hom =
      φ.hom ≫ Functor.whiskerLeft C
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard))
    (G : LAdicSheaf B U ℓ) {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} (b : ℤ)
    (hR : ∀ (r : ℕ) (a : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B W ℓ fW jW kbar
          (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) a)],
      IsCharpolyNormMixedOfWeightLE q' ι (b + r + a)
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B W ℓ fW jW kbar p q hcard
          (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) a).hom)
    (i : ℤ) [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      (B.inclusion.map g ≫ fW) jU kbar G i)] :
    IsCharpolyNormMixedOfWeightLE q' ι (b + i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map g ≫ fW) jU
        kbar p q hcard G i).hom := by
  let L := LAdicSheaf.flatModelTorsionTower G ⋙ C
  have hdesc := isCharpolyNormMixedOfWeightLE_rationalLim_of_descending (ℓ := ℓ)
    (fun n => L ⋙ compactSupportTruncHomology ℤ_[ℓ] fW jW kbar n i)
    (fun n => L ⋙ compactSupportGradedHomology ℤ_[ℓ] fW jW kbar n i)
    (fun n => Functor.whiskerLeft L (compactSupportGradedToTrunc ℤ_[ℓ] fW jW kbar n i))
    (fun n => Functor.whiskerLeft L (compactSupportTruncToTrunc ℤ_[ℓ] fW jW kbar n i))
    (fun n m => exact_compactSupportGradedToTrunc_truncToTrunc ℤ_[ℓ] fW jW kbar n i (L.obj m)) i
    (fun n hn m => isZero_compactSupportTruncHomology ℤ_[ℓ] fW jW kbar n i hn (L.obj m))
    (fun n hn m => by
      obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact LAdicSheaf.finite_lerayGradedTower g jg fW jW kbar hT hfinT G C ψ r i m)
    (fun n => Functor.whiskerLeft L (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
      (CochainComplex.Plus.truncGEFunctor n) i))
    (fun n => Functor.whiskerLeft L (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
      (CochainComplex.Plus.gradedFunctor n) i))
    (fun n => by
      simp only [← Functor.whiskerLeft_comp, compactSupportGradedToTrunc_frobenius])
    (fun n => by
      simp only [← Functor.whiskerLeft_comp, compactSupportTruncToTrunc_frobenius])
    (q' := q') (ι := ι) (b := b + i)
    (fun n hn => by
      obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact LAdicSheaf.isCharpolyNormMixedOfWeightLE_lerayGradedTower g jg fW jW kbar p q hcard
        hT hfinW G C ψ b hR r i)
    0 le_rfl
  exact LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_lerayTruncTower g jg fW jW kbar p q hcard jU
    C ψ φ hφ G i hdesc

variable (B ℓ) in
/-- **Finiteness of `H^p_c(X_k̄, F)` for constructible ℓ-power torsion sheaves** (Tag 03V3 with
torsion coefficients): for `X` separated of finite type over a finite field `k` of characteristic
`p ≠ ℓ`, with a compactification `j`, and a constructible sheaf `F` of `ℤ_ℓ`-modules on `X`
killed by a power of `ℓ`, every `H^a_c(X_k̄, F)` is finite. -/
def LAdicSheaf.TorsionCompactSupportFinitenessInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ q →
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
      (F : EtaleModules.{u, 0} ℤ_[ℓ] X.1), IsBigSiteConstructibleEtaleModule.{u, 0} B X ℤ_[ℓ] F →
      IsLPowerTorsion ℓ X.1 F →
        ∀ a : ℤ, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar a).obj F)

variable (B ℓ) in
/-- **The Leray weight implication for `Rʳ g_! G`** (Weil II 3.3; the Leray step of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `LAdicSheaf.LerayWeightInput` holds for the
family `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekFamily`, given the Leray
comparison with Frobenius (`LAdicSheaf.LerayFrobeniusComparison`, Tags 0F7J and 0F7L) for the
compactifications of the base (which exist by Nagata's theorem, Tag 0F41), the constructibility
of `Rᵠ g_!` (Tag 0GL0), and the finiteness of compactly supported cohomology (Tag 03V3). -/
theorem LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily
    (hLFC : ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
      [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
      ℓ ≠ p → ∀ (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
        [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
        [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
        (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW],
        ∀ jW : CompactificationOf (Over.mk fW),
          LAdicSheaf.LerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard)
    (hT : LowerShriekConstructibilityInput B)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hfinT : LAdicSheaf.TorsionCompactSupportFinitenessInput B ℓ) :
    LAdicSheaf.LerayWeightInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) := by
  intro k _ _ kbar _ _ _ p q _ _ hcard hℓ ι U W _ _ g _ _ _ jg fW _ _ _ G b hR
  -- a compactification of `W` over `k` exists (Nagata, Tag 0F41)
  let jW : CompactificationOf (Over.mk fW) := (IsCofiltered.nonempty (C := CompactificationOf
    (Over.mk fW))).some
  obtain ⟨jU, C, ψ, φ, hφ⟩ := hLFC k kbar p q hcard hℓ U W g jg fW jW
  exact ⟨jU, fun i _ => LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_lerayComplex g jg fW jW kbar
    p q hcard hT (hfinT k kbar p q hcard hℓ W fW jW) (hfin k kbar p q hcard hℓ W fW) jU C ψ φ hφ G b
    (fun r a _ => hR r jW a) i⟩

end Leray

end Stacks.EtaleCohomology
