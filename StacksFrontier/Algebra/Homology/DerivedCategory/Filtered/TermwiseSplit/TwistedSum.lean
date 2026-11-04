module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.TermwiseSplit.ExtensionSteps

/-!
# The twisted sum and the termwise split lifting

The twisting data `Twist`, the twisted direct sum of two complexes, the source's induction
producing a twist (`exists_twist`), its assembly into a filtered complex (`twistedSumFiltered`,
`exists_of_twist`), and [Stacks, Tag 05TV]
(`CochainComplex.exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredTermwiseSplit

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

namespace CochainComplex.FilteredInjective.TermwiseSplit

open CochainComplex.FilteredInjective.Degreewise
open CochainComplex.FilteredInjective.Resolution (filtrationOfSteps homFromDegreeZero
  homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne)

attribute [local simp] evalFil_ι_app homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne

/-! ### The twisting data -/

/-- The twisting data of the source's construction: morphisms `δ^n : J^n ⟶ I^{n + 1}` of filtered
objects with `δ^{n + 1} ≫ d_J^n = d_I^{n + 1} ≫ δ^n`, which is what makes the matrix differential
`d_M^n = (d_I^n, (-1)^{n + 1} δ^n; 0, d_J^n)` on `M^n = I^n ⊕ J^n` square to zero. -/
private structure Twist (I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) where
  /-- The twisting maps `δ^n : J^n ⟶ I^{n + 1}`. -/
  δ : ∀ n : ℤ, evalFil J n ⟶ evalFil I (n + 1)
  /-- The compatibility of the twisting maps with the differentials. -/
  comm : ∀ n : ℤ, evalD J n ≫ δ (n + 1) = δ n ≫ evalD I (n + 1)

/-! ### The twisted direct sum of two complexes -/

section TwistedSum

/-- A biproduct of monomorphisms is a monomorphism. -/
private lemma mono_biprod_map {W X Y Z : 𝒜} (f : W ⟶ X) (g : Y ⟶ Z) [Mono f] [Mono g] :
    Mono (biprod.map f g) :=
  ⟨fun u v huv => by
    apply biprod.hom_ext
    · rw [← cancel_mono f]
      simpa using congrArg (fun m => m ≫ biprod.fst) huv
    · rw [← cancel_mono g]
      simpa using congrArg (fun m => m ≫ biprod.snd) huv⟩

/-- The composite of two biproducts of morphisms is the biproduct of the composites. -/
public lemma biprod_map_comp_map {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} [HasBinaryBiproduct X₁ Y₁] [HasBinaryBiproduct X₂ Y₂]
    [HasBinaryBiproduct X₃ Y₃] (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃)
    (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

/-- A lift followed by a biproduct of morphisms is the lift of the composites. -/
private lemma biprod_lift_comp_map {W X₁ X₂ Y₁ Y₂ : 𝒜} (f : W ⟶ X₁) (g : W ⟶ Y₁) (u : X₁ ⟶ X₂)
    (v : Y₁ ⟶ Y₂) : biprod.lift f g ≫ biprod.map u v = biprod.lift (f ≫ u) (g ≫ v) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- Precomposing a lift is the lift of the precomposites. -/
private lemma comp_biprod_lift {W W' X Y : 𝒜} (h : W' ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The differential of the twisted direct sum: the matrix `(d_X, δ; 0, d_Y)` on `X^n ⊕ Y^n`. -/
private noncomputable def twistedSumD (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)) (n m : ℤ) : X.X n ⊞ Y.X n ⟶ X.X m ⊞ Y.X m :=
  biprod.lift (biprod.fst ≫ X.d n m +
      biprod.snd ≫ (if h : n + 1 = m then δ n ≫ eqToHom (congrArg X.X h) else 0))
    (biprod.snd ≫ Y.d n m)

@[local simp]
private lemma twistedSumD_succ (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)) (n : ℤ) :
    twistedSumD X Y δ n (n + 1) =
      biprod.lift (biprod.fst ≫ X.d n (n + 1) + biprod.snd ≫ δ n)
        (biprod.snd ≫ Y.d n (n + 1)) := by
  simp [twistedSumD]

private lemma twistedSumD_eq_zero (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)) {n m : ℤ} (h : n + 1 ≠ m) :
    twistedSumD X Y δ n m = 0 := by
  apply biprod.hom_ext <;> simp [twistedSumD, h]

/-- The twisted direct sum `M^n = X^n ⊕ Y^n` of two complexes, with differential
`d_M^n = (d_X^n, δ^n; 0, d_Y^n)`. The twisting maps `δ^n : Y^n ⟶ X^{n + 1}` are asked to
anticommute with the differentials, which is exactly what makes `d_M` square to zero. -/
private noncomputable def twistedSum (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1))
    (hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0) :
    CochainComplex 𝒜 ℤ where
  X n := X.X n ⊞ Y.X n
  d := twistedSumD X Y δ
  shape _ _ hij := twistedSumD_eq_zero X Y δ hij
  d_comp_d' i j k hij hjk := by
    obtain rfl : j = i + 1 := hij.symm
    obtain rfl : k = i + 1 + 1 := hjk.symm
    rw [twistedSumD_succ, twistedSumD_succ]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, Preadditive.comp_add, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, Preadditive.add_comp, Category.assoc,
        HomologicalComplex.d_comp_d, comp_zero, zero_add, Category.assoc, Category.assoc,
        ← Preadditive.comp_add, hδ i, comp_zero, zero_comp]
    · simp

@[local simp]
private lemma twistedSum_d (X Y : CochainComplex 𝒜 ℤ) (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1))
    (hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0) (n : ℤ) :
    (twistedSum X Y δ hδ).d n (n + 1) =
      biprod.lift (biprod.fst ≫ X.d n (n + 1) + biprod.snd ≫ δ n)
        (biprod.snd ≫ Y.d n (n + 1)) :=
  twistedSumD_succ X Y δ n

/-- The inclusion `X^• ⟶ M^•` of the first summand of a twisted direct sum. -/
private noncomputable def twistedSumInl (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1))
    (hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0) :
    X ⟶ twistedSum X Y δ hδ where
  f _ := biprod.inl
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    change biprod.inl ≫ twistedSumD X Y δ i (i + 1) = X.d i (i + 1) ≫ biprod.inl
    apply biprod.hom_ext <;> simp [Preadditive.comp_add]

/-- The projection `M^• ⟶ Y^•` onto the second summand of a twisted direct sum. -/
private noncomputable def twistedSumSnd (X Y : CochainComplex 𝒜 ℤ)
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1))
    (hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0) :
    twistedSum X Y δ hδ ⟶ Y where
  f _ := biprod.snd
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    change biprod.snd ≫ Y.d i (i + 1) = twistedSumD X Y δ i (i + 1) ≫ biprod.snd
    simp

/-- A pair of morphisms compatible with the twistings induces a morphism of twisted direct
sums. -/
private noncomputable def twistedSumMap {X Y X' Y' : CochainComplex 𝒜 ℤ}
    {δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)}
    {hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0}
    {δ' : ∀ n : ℤ, Y'.X n ⟶ X'.X (n + 1)}
    {hδ' : ∀ n : ℤ, δ' n ≫ X'.d (n + 1) (n + 1 + 1) + Y'.d n (n + 1) ≫ δ' (n + 1) = 0}
    (φ : X ⟶ X') (ψ : Y ⟶ Y') (h : ∀ n : ℤ, δ n ≫ φ.f (n + 1) = ψ.f n ≫ δ' n) :
    twistedSum X Y δ hδ ⟶ twistedSum X' Y' δ' hδ' where
  f n := biprod.map (φ.f n) (ψ.f n)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    change biprod.map (φ.f i) (ψ.f i) ≫ twistedSumD X' Y' δ' i (i + 1)
      = twistedSumD X Y δ i (i + 1) ≫ biprod.map (φ.f (i + 1)) (ψ.f (i + 1))
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [Preadditive.comp_add, Preadditive.add_comp, h i]

@[local simp]
private lemma twistedSumMap_f {X Y X' Y' : CochainComplex 𝒜 ℤ}
    {δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)}
    {hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0}
    {δ' : ∀ n : ℤ, Y'.X n ⟶ X'.X (n + 1)}
    {hδ' : ∀ n : ℤ, δ' n ≫ X'.d (n + 1) (n + 1 + 1) + Y'.d n (n + 1) ≫ δ' (n + 1) = 0}
    (φ : X ⟶ X') (ψ : Y ⟶ Y') (h : ∀ n : ℤ, δ n ≫ φ.f (n + 1) = ψ.f n ≫ δ' n) (n : ℤ) :
    (twistedSumMap (hδ := hδ) (hδ' := hδ') φ ψ h).f n = biprod.map (φ.f n) (ψ.f n) :=
  rfl

end TwistedSum

/-! ### Morphisms out of a complex concentrated in degree `0` -/

/-- A square of morphisms out of complexes concentrated in degree `0` commutes as soon as it
commutes in degree `0`. -/
private lemma homFromDegreeZero_comp_eq {K K' L L' : CochainComplex 𝒜 ℤ}
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X n)) (hK' : ∀ n : ℤ, n ≠ 0 → IsZero (K'.X n))
    (g : K.X 0 ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) (g' : K'.X 0 ⟶ L'.X 0) (hg' : g' ≫ L'.d 0 1 = 0)
    (φ : K ⟶ K') (ψ : L ⟶ L') (h : g ≫ ψ.f 0 = φ.f 0 ≫ g') :
    homFromDegreeZero hK g hg ≫ ψ = φ ≫ homFromDegreeZero hK' g' hg' := by
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, homFromDegreeZero_f_zero,
      homFromDegreeZero_f_zero]
    exact h
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      homFromDegreeZero_f_of_ne _ _ _ hn, homFromDegreeZero_f_of_ne _ _ _ hn, zero_comp, comp_zero]

/-! ### The source's induction -/

/-- The vanishing which lets the source's construction take one more step at `J^k`: the composite
`δ^k ≫ d_I^{k + 1}` kills the previous map into `J^k`, which is `c` for `k = 0` and `d_J^{k - 1}`
afterwards. -/
private def TwistCond {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (c : C ⟶ J) :
    (k : ℕ) → (evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)) → Prop
  | 0, d => ((evalFunctor 0).map c ≫ d ≫ evalD I ((0 : ℤ) + 1)).hom = 0
  | k + 1, d => (evalD J (k : ℤ) ≫ d ≫ evalD I ((k : ℤ) + 1 + 1)).hom = 0

/-- One step of the source's induction: a twisting map in degree `k` whose composite with
`d_I^{k + 1}` kills the previous map into `J^k` extends to a twisting map in degree `k + 1`. -/
private theorem exists_twistStep {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0] [J.X.IsStrictlyGE 0]
    (c : C ⟶ J) (hc : CochainComplex.filteredQuasiIso 𝒜 c)
    (hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, (evalFil I n).filtration.IsFinite)
    (hIinj : ∀ p n : ℤ, Injective ((gr p).obj (evalFil I n)))
    (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)) (hd : TwistCond c k d) :
    ∃ d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1),
      evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d' := by
  match k with
  | 0 =>
      obtain ⟨ψ, hψ⟩ := exists_comp_evalD_eq_of_map_comp_eq_zero c hc hC hJfin
        (hIfin ((0 : ℤ) + 1 + 1)) (fun p => hIinj p ((0 : ℤ) + 1 + 1))
        (d ≫ evalD I ((0 : ℤ) + 1)) hd
      refine ⟨ψ, hψ, ?_⟩
      show (evalD J ((0 : ℤ)) ≫ ψ ≫ evalD I ((0 : ℤ) + 1 + 1)).hom = 0
      rw [← Category.assoc, hψ, Category.assoc]
      exact comp_evalD_comp_evalD_hom I ((0 : ℤ) + 1) d
  | k + 1 =>
      -- The composite is spelled with the index `((k + 1 : ℕ) : ℤ)` carried by `d`, so that the
      -- only place where it has to be identified with `(k : ℤ) + 1` is the outer application.
      obtain ⟨ψ, hψ⟩ := exists_comp_evalD_eq_of_evalD_comp_eq_zero c hc hC hJfin
        (hIfin ((k : ℤ) + 1 + 1 + 1)) (fun p => hIinj p ((k : ℤ) + 1 + 1 + 1))
        (k : ℤ) (Int.natCast_nonneg k)
        (X := evalFil I ((k : ℤ) + 1 + 1 + 1))
        (φ := d ≫ evalD I (((k + 1 : ℕ) : ℤ) + 1)) hd
      refine ⟨ψ, hψ, ?_⟩
      show (evalD J ((k : ℤ) + 1) ≫ ψ ≫ evalD I ((k : ℤ) + 1 + 1 + 1)).hom = 0
      rw [← Category.assoc, hψ, Category.assoc]
      exact comp_evalD_comp_evalD_hom I ((k : ℤ) + 1 + 1) d

/-- The sequence of twisting maps of the source's induction, in nonnegative degrees. -/
private def twistSeq {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (c : C ⟶ J)
    (step : ∀ (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)), TwistCond c k d →
      {d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1) //
        evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d'})
    (d₀ : evalFil J ((0 : ℤ)) ⟶ evalFil I ((0 : ℤ) + 1)) (hd₀ : TwistCond c 0 d₀) :
    (k : ℕ) → {d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1) // TwistCond c k d}
  | 0 => ⟨d₀, hd₀⟩
  | k + 1 =>
      ⟨(step k (twistSeq c step d₀ hd₀ k).1 (twistSeq c step d₀ hd₀ k).2).1,
        (step k (twistSeq c step d₀ hd₀ k).1 (twistSeq c step d₀ hd₀ k).2).2.2⟩

private lemma twistSeq_comm {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (c : C ⟶ J)
    (step : ∀ (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)), TwistCond c k d →
      {d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1) //
        evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d'})
    (d₀ : evalFil J ((0 : ℤ)) ⟶ evalFil I ((0 : ℤ) + 1)) (hd₀ : TwistCond c 0 d₀) (k : ℕ) :
    evalD J (k : ℤ) ≫ (twistSeq c step d₀ hd₀ (k + 1)).1 =
      (twistSeq c step d₀ hd₀ k).1 ≫ evalD I ((k : ℤ) + 1) :=
  (step k (twistSeq c step d₀ hd₀ k).1 (twistSeq c step d₀ hd₀ k).2).2.1

/-- The `ℤ`-indexed family of twisting maps: the sequence of the source's induction in nonnegative
degrees, and zero in the negative degrees, where `J^•` vanishes. -/
private noncomputable def twistFamily {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (c : C ⟶ J)
    (step : ∀ (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)), TwistCond c k d →
      {d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1) //
        evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d'})
    (d₀ : evalFil J ((0 : ℤ)) ⟶ evalFil I ((0 : ℤ) + 1)) (hd₀ : TwistCond c 0 d₀) :
    ∀ n : ℤ, evalFil J n ⟶ evalFil I (n + 1)
  | Int.ofNat k => (twistSeq c step d₀ hd₀ k).1
  | Int.negSucc _ => 0

private lemma twistFamily_comm {C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [J.X.IsStrictlyGE 0] (c : C ⟶ J)
    (step : ∀ (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)), TwistCond c k d →
      {d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1) //
        evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d'})
    (d₀ : evalFil J ((0 : ℤ)) ⟶ evalFil I ((0 : ℤ) + 1)) (hd₀ : TwistCond c 0 d₀) (n : ℤ) :
    evalD J n ≫ twistFamily c step d₀ hd₀ (n + 1) =
      twistFamily c step d₀ hd₀ n ≫ evalD I (n + 1) := by
  match n with
  | Int.ofNat k => exact twistSeq_comm c step d₀ hd₀ k
  | Int.negSucc k =>
      refine FilteredObject.hom_ext ?_
      exact (J.X.isZero_of_isStrictlyGE 0 (Int.negSucc k) (Int.negSucc_lt_zero k)).eq_of_src _ _

/-- The inductive heart of [Stacks, Tag 05TV]: the twisting maps `δ^n`, the extension
`b : B ⟶ I^0` of `a` along the strict monomorphism `α`, and the identity
`b ≫ d_I^0 = β ≫ c ≫ δ^0` which makes `b ⊕ (β ≫ c)` a morphism of complexes. Both extension
problems are solved by [Stacks, Tag 05TR]. -/
private theorem exists_twist {A B C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    [I.X.IsStrictlyGE 0] [J.X.IsStrictlyGE 0]
    (α : A ⟶ B) (β : B ⟶ C) (a : A ⟶ I) (c : C ⟶ J) (hcomp : α.hom ≫ β.hom = 0)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (_ha : CochainComplex.filteredQuasiIso 𝒜 a) (hc : CochainComplex.filteredQuasiIso 𝒜 c)
    (hA : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((A.filtration.ι.app (op p)).f n) ∧
      IsZero ((A.filtration.obj (op q)).X n))
    (hB : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((B.filtration.ι.app (op p)).f n) ∧
      IsZero ((B.filtration.obj (op q)).X n))
    (hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ, Injective (((gr p).obj I).X n)) :
    ∃ (t : Twist I J) (b : evalFil B 0 ⟶ evalFil I 0),
      (evalFunctor 0).map α ≫ b = (evalFunctor 0).map a ∧
      b ≫ evalD I 0 = (evalFunctor 0).map β ≫ (evalFunctor 0).map c ≫ t.δ 0 := by
  have hIfin' : ∀ n : ℤ, (evalFil I n).filtration.IsFinite := isFinite_eval hIfin
  have hIinj : ∀ p n : ℤ, Injective ((gr p).obj (evalFil I n)) := fun p n =>
    Injective.of_iso (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (I.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) (hI p n)
  have := isStrictHom_evalFunctor_map_of_shortExact_gradedPiece α β hgr hcomp hA hB 0
  -- the extension `b : B ⟶ I^0` of `a` along the strict monomorphism `α`
  obtain ⟨b, hb⟩ := factors_of_isFilteredInjective ((evalFunctor 0).map a)
    ((evalFunctor 0).map α) ⟨hIfin' 0, fun p => hIinj p 0⟩
  have hA1 : IsZero (A.X.X (0 + 1)) := A.X.isZero_of_isStrictlyLE 0 (0 + 1) (by norm_num)
  have hab : ((evalFunctor 0).map α ≫ b ≫ evalD I 0).hom = 0 := by
    have h1 : α.hom.f 0 ≫ b.hom = a.hom.f 0 := congrArg (fun f => FilteredObject.Hom.hom f) hb
    show α.hom.f 0 ≫ b.hom ≫ I.X.d 0 (0 + 1) = 0
    rw [← Category.assoc, h1, a.hom.comm 0 (0 + 1), hA1.eq_of_tgt (A.X.d 0 (0 + 1)) 0, zero_comp]
  -- the descent `b̄ : C ⟶ I^1` of `b ≫ d_I^0` along the cokernel `β`
  obtain ⟨bbar, hbbar, -⟩ := existsUnique_comp_eq_of_shortExact_gradedPiece α β hgr hcomp
    hA hB hC 0 (b ≫ evalD I 0) hab
  have hkey : ((evalFunctor 0).map β ≫ bbar ≫ evalD I ((0 : ℤ) + 1)).hom = 0 := by
    rw [← Category.assoc, hbbar, Category.assoc]
    exact comp_evalD_comp_evalD_hom I 0 b
  have hbbar2 : (bbar ≫ evalD I ((0 : ℤ) + 1)).hom = 0 := by
    have hg : ((evalFunctor 0).map α ≫
        (evalFunctor 0).map β ≫ bbar ≫ evalD I ((0 : ℤ) + 1)).hom = 0 := by
      show α.hom.f 0 ≫ ((evalFunctor 0).map β ≫ bbar ≫ evalD I ((0 : ℤ) + 1)).hom = 0
      rw [hkey, comp_zero]
    obtain ⟨h, -, huniq⟩ := existsUnique_comp_eq_of_shortExact_gradedPiece α β hgr hcomp hA hB hC 0
      ((evalFunctor 0).map β ≫ bbar ≫ evalD I ((0 : ℤ) + 1)) hg
    have h1 := huniq (bbar ≫ evalD I ((0 : ℤ) + 1)) rfl
    have h2 := huniq 0 (FilteredObject.hom_ext (by
      show β.hom.f 0 ≫ (0 : evalFil C 0 ⟶ evalFil I ((0 : ℤ) + 1 + 1)).hom =
        ((evalFunctor 0).map β ≫ bbar ≫ evalD I ((0 : ℤ) + 1)).hom
      rw [zero_hom, comp_zero, hkey]))
    rw [h1, ← h2, zero_hom]
  -- the extension `δ^0 : J^0 ⟶ I^1` of `b̄` along the strict monomorphism `c`
  have := isStrictHom_evalFunctor_map_of_filteredQuasiIso c hc hC hJfin
  obtain ⟨d₀, hd₀⟩ := factors_of_isFilteredInjective bbar ((evalFunctor 0).map c)
    ⟨hIfin' ((0 : ℤ) + 1), fun p => hIinj p ((0 : ℤ) + 1)⟩
  have hcond : TwistCond c 0 d₀ := by
    show ((evalFunctor 0).map c ≫ d₀ ≫ evalD I ((0 : ℤ) + 1)).hom = 0
    rw [← Category.assoc, hd₀]
    exact hbbar2
  -- and the induction
  have step : ∀ (k : ℕ) (d : evalFil J (k : ℤ) ⟶ evalFil I ((k : ℤ) + 1)), TwistCond c k d →
      {d' : evalFil J ((k : ℤ) + 1) ⟶ evalFil I ((k : ℤ) + 1 + 1) //
        evalD J (k : ℤ) ≫ d' = d ≫ evalD I ((k : ℤ) + 1) ∧ TwistCond c (k + 1) d'} :=
    fun k d hd => ⟨_, Classical.choose_spec
      (exists_twistStep c hc hC hJfin hIfin' hIinj k d hd)⟩
  refine ⟨⟨twistFamily c step d₀ hcond, twistFamily_comm c step d₀ hcond⟩, b, hb, ?_⟩
  show b ≫ evalD I 0 = (evalFunctor 0).map β ≫ (evalFunctor 0).map c ≫ d₀
  rw [hd₀, hbbar]

/-! ### Assembling a twist into a filtered complex -/

section Assembly

variable {I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

/-- The inclusion of a step of a filtered complex factors through the smaller steps, degreewise. -/
private lemma diagram_map_f_comp_ι_app_f (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    {i j : ℤᵒᵖ} (f : i ⟶ j) (n : ℤ) :
    (K.filtration.diagram.map f).f n ≫ (K.filtration.ι.app j).f n = (K.filtration.ι.app i).f n :=
  congrArg (fun g : K.filtration.obj i ⟶ K.X => g.f n)
    (Filtration.diagram_map_comp_ι_app K.filtration f)

namespace Twist

/-- The twisting map `δ^n : J^n ⟶ I^{n + 1}` of a twist, read in `𝒜`. -/
private def hom (t : Twist I J) (n : ℤ) : J.X.X n ⟶ I.X.X (n + 1) :=
  (t.δ n).hom

/-- The twisting map `δ^n` of a twist on the `p`-th steps of the filtrations,
`F^p J^n ⟶ F^p I^{n + 1}`. -/
private def app (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    (J.filtration.obj i).X n ⟶ (I.filtration.obj i).X (n + 1) :=
  (t.δ n).natTrans.app i

private lemma app_comp_ι (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    t.app i n ≫ (I.filtration.ι.app i).f (n + 1) = (J.filtration.ι.app i).f n ≫ t.hom n :=
  (t.δ n).comm i

private lemma hom_comm (t : Twist I J) (n : ℤ) :
    J.X.d n (n + 1) ≫ t.hom (n + 1) = t.hom n ≫ I.X.d (n + 1) (n + 1 + 1) :=
  congrArg (fun f => FilteredObject.Hom.hom f) (t.comm n)

private lemma app_comm (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    (J.filtration.obj i).d n (n + 1) ≫ t.app i (n + 1) =
      t.app i n ≫ (I.filtration.obj i).d (n + 1) (n + 1 + 1) :=
  congrArg (fun f => FilteredObject.Hom.natTrans f |>.app i) (t.comm n)

private lemma app_comp_diagram_map (t : Twist I J) {i j : ℤᵒᵖ} (f : i ⟶ j) (n : ℤ) :
    t.app i n ≫ (I.filtration.diagram.map f).f (n + 1) =
      (J.filtration.diagram.map f).f n ≫ t.app j n := by
  have := mono_ι_app_f I j (n + 1)
  rw [← cancel_mono ((I.filtration.ι.app j).f (n + 1)), Category.assoc,
    diagram_map_f_comp_ι_app_f I f, Category.assoc, t.app_comp_ι j n, ← Category.assoc,
    diagram_map_f_comp_ι_app_f J f, t.app_comp_ι i n]

end Twist

/-- The sign `(-1)^{n + 1}` with which the source twists the differential of `M^•`. -/
private def twistSign (n : ℤ) : ℤ := ((n + 1).negOnePow : ℤ)

private lemma twistSign_succ (n : ℤ) : twistSign (n + 1) = -twistSign n := by
  simp [twistSign, Int.negOnePow_succ]

private lemma twistSign_zero : twistSign 0 = -1 := by decide

/-- The twisting family `(-1)^{n + 1} δ^n : J^n ⟶ I^{n + 1}` of the underlying complexes. -/
private noncomputable def twistδ (t : Twist I J) (n : ℤ) : J.X.X n ⟶ I.X.X (n + 1) :=
  twistSign n • t.hom n

/-- The twisting family of the `p`-th steps of the filtrations. -/
private noncomputable def twistδStep (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    (J.filtration.obj i).X n ⟶ (I.filtration.obj i).X (n + 1) :=
  twistSign n • t.app i n

/-- Scaling by consecutive signs turns a commuting square into an anticommuting one. -/
private lemma twistSign_smul_anticomm {X Y X' Y' : 𝒜} (f : X ⟶ Y) (f' : X' ⟶ Y') (d : X ⟶ X')
    (d' : Y ⟶ Y') (h : d ≫ f' = f ≫ d') (n : ℤ) :
    (twistSign n • f) ≫ d' + d ≫ (twistSign (n + 1) • f') = 0 := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, h, twistSign_succ, neg_smul, add_neg_cancel]

/-- Scaling by a sign preserves a commuting square. -/
private lemma zsmul_comp_eq_comp_zsmul {X Y X' Y' : 𝒜} {f : X ⟶ Y} {g : Y ⟶ Y'} {g' : X ⟶ X'}
    {f' : X' ⟶ Y'} (s : ℤ) (h : f ≫ g = g' ≫ f') : (s • f) ≫ g = g' ≫ (s • f') := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, h]

private lemma twistδ_anticomm (t : Twist I J) (n : ℤ) :
    twistδ t n ≫ I.X.d (n + 1) (n + 1 + 1) + J.X.d n (n + 1) ≫ twistδ t (n + 1) = 0 :=
  twistSign_smul_anticomm _ _ _ _ (t.hom_comm n) n

private lemma twistδStep_anticomm (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    twistδStep t i n ≫ (I.filtration.obj i).d (n + 1) (n + 1 + 1) +
      (J.filtration.obj i).d n (n + 1) ≫ twistδStep t i (n + 1) = 0 :=
  twistSign_smul_anticomm _ _ _ _ (t.app_comm i n) n

/-- The underlying complex `M^n = I^n ⊕ J^n` of the assembled resolution. -/
private noncomputable def twistedSumX (t : Twist I J) : CochainComplex 𝒜 ℤ :=
  twistedSum I.X J.X (twistδ t) (twistδ_anticomm t)

/-- The step `F^p M^• = F^p I^• ⊕ F^p J^•` of the filtration of `M^•`. -/
private noncomputable def twistedSumStep (t : Twist I J) (i : ℤᵒᵖ) : CochainComplex 𝒜 ℤ :=
  twistedSum (I.filtration.obj i) (J.filtration.obj i) (twistδStep t i) (twistδStep_anticomm t i)

/-- The inclusion `F^p M^• ⟶ M^•`. -/
private noncomputable def twistedSumStepι (t : Twist I J) (i : ℤᵒᵖ) :
    twistedSumStep t i ⟶ twistedSumX t :=
  twistedSumMap (I.filtration.ι.app i) (J.filtration.ι.app i) (fun n =>
    zsmul_comp_eq_comp_zsmul _ (t.app_comp_ι i n))

@[local simp]
private lemma twistedSumStepι_f (t : Twist I J) (i : ℤᵒᵖ) (n : ℤ) :
    (twistedSumStepι t i).f n =
      biprod.map ((I.filtration.ι.app i).f n) ((J.filtration.ι.app i).f n) :=
  rfl

private lemma mono_twistedSumStepι (t : Twist I J) (i : ℤᵒᵖ) : Mono (twistedSumStepι t i) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  have := mono_ι_app_f I i n
  have := mono_ι_app_f J i n
  rw [twistedSumStepι_f]
  exact mono_biprod_map _ _

/-- The step `F^p M^•` of the filtration of `M^•`, as a subobject of `M^•`. -/
private noncomputable def twistedSumStepMonoOver (t : Twist I J) (i : ℤᵒᵖ) :
    MonoOver (twistedSumX t) :=
  haveI := mono_twistedSumStepι t i
  MonoOver.mk (twistedSumStepι t i)

/-- The inclusion `F^p M^• ⟶ F^q M^•` for `q ≤ p`. -/
private noncomputable def twistedSumStepMap (t : Twist I J) {i j : ℤᵒᵖ} (f : i ⟶ j) :
    twistedSumStep t i ⟶ twistedSumStep t j :=
  twistedSumMap (I.filtration.diagram.map f) (J.filtration.diagram.map f) (fun n =>
    zsmul_comp_eq_comp_zsmul _ (t.app_comp_diagram_map f n))

private lemma twistedSumStepMap_comp_ι (t : Twist I J) {i j : ℤᵒᵖ} (f : i ⟶ j) :
    twistedSumStepMap t f ≫ twistedSumStepι t j = twistedSumStepι t i := by
  ext n
  show biprod.map ((I.filtration.diagram.map f).f n) ((J.filtration.diagram.map f).f n) ≫
      biprod.map ((I.filtration.ι.app j).f n) ((J.filtration.ι.app j).f n)
    = biprod.map ((I.filtration.ι.app i).f n) ((J.filtration.ι.app i).f n)
  rw [biprod_map_comp_map, diagram_map_f_comp_ι_app_f I f, diagram_map_f_comp_ι_app_f J f]
  rfl

/-- The filtered complex `M^•` of [Stacks, Tag 05TV]: the twisted direct sum `I^• ⊕ J^•`, filtered
by `F^p M^• = F^p I^• ⊕ F^p J^•`. -/
private noncomputable def twistedSumFiltered (t : Twist I J) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := twistedSumX t
  filtration := filtrationOfSteps (fun p => twistedSumStepMonoOver t (op p))
    (fun _ _ hqp => ⟨MonoOver.homMk (twistedSumStepMap t (homOfLE hqp).op)
      (twistedSumStepMap_comp_ι t (homOfLE hqp).op)⟩)

private lemma twistedSumFiltered_filtration_obj (t : Twist I J) (i : ℤᵒᵖ) :
    (twistedSumFiltered t).filtration.obj i = twistedSumStep t i :=
  rfl

@[local simp]
private lemma twistedSumFiltered_filtration_ι_app (t : Twist I J) (i : ℤᵒᵖ) :
    (twistedSumFiltered t).filtration.ι.app i = twistedSumStepι t i :=
  rfl

/-- The inclusion `I^• ⟶ M^•` of the first summand. -/
private noncomputable def twistedSumFilteredInl (t : Twist I J) : I ⟶ twistedSumFiltered t :=
  FilteredObject.homMk (twistedSumInl I.X J.X (twistδ t) (twistδ_anticomm t))
    (fun i => twistedSumInl (I.filtration.obj i) (J.filtration.obj i) (twistδStep t i)
      (twistδStep_anticomm t i))
    (fun i => by
      ext n
      change biprod.inl ≫ biprod.map ((I.filtration.ι.app i).f n) ((J.filtration.ι.app i).f n)
        = (I.filtration.ι.app i).f n ≫ biprod.inl
      simp)

@[local simp]
private lemma twistedSumFilteredInl_hom_f (t : Twist I J) (n : ℤ) :
    (twistedSumFilteredInl t).hom.f n = biprod.inl :=
  rfl

/-- The projection `M^• ⟶ J^•` onto the second summand. -/
private noncomputable def twistedSumFilteredSnd (t : Twist I J) : twistedSumFiltered t ⟶ J :=
  FilteredObject.homMk (twistedSumSnd I.X J.X (twistδ t) (twistδ_anticomm t))
    (fun i => twistedSumSnd (I.filtration.obj i) (J.filtration.obj i) (twistδStep t i)
      (twistδStep_anticomm t i))
    (fun i => by
      ext n
      change biprod.snd ≫ (J.filtration.ι.app i).f n
        = biprod.map ((I.filtration.ι.app i).f n) ((J.filtration.ι.app i).f n) ≫ biprod.snd
      simp)

@[local simp]
private lemma twistedSumFilteredSnd_hom_f (t : Twist I J) (n : ℤ) :
    (twistedSumFilteredSnd t).hom.f n = biprod.snd :=
  rfl

/-- A morphism into `X^0 ⊕ Y^0` whose two components satisfy the source's identities in degree `0`
is killed by the twisted differential. -/
private lemma lift_comp_twistedSumD {X Y : CochainComplex 𝒜 ℤ} {Z : 𝒜}
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1)) (g₁ : Z ⟶ X.X 0) (g₂ : Z ⟶ Y.X 0)
    (h₁ : g₁ ≫ X.d 0 (0 + 1) + g₂ ≫ δ 0 = 0) (h₂ : g₂ ≫ Y.d 0 (0 + 1) = 0) :
    biprod.lift g₁ g₂ ≫ twistedSumD X Y δ 0 (0 + 1) = 0 := by
  rw [twistedSumD_succ]
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [zero_comp, Category.assoc, biprod.lift_fst, Preadditive.comp_add, biprod.lift_fst_assoc,
      biprod.lift_snd_assoc]
    exact h₁
  · rw [zero_comp, Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc]
    exact h₂

/-- A morphism into a twisted direct sum whose two components satisfy the source's identities in
degree `0` lands in the cocycles. -/
private lemma lift_comp_twistedSum_d {X Y : CochainComplex 𝒜 ℤ} {Z : 𝒜}
    (δ : ∀ n : ℤ, Y.X n ⟶ X.X (n + 1))
    (hδ : ∀ n : ℤ, δ n ≫ X.d (n + 1) (n + 1 + 1) + Y.d n (n + 1) ≫ δ (n + 1) = 0)
    (g₁ : Z ⟶ X.X 0) (g₂ : Z ⟶ Y.X 0) (h₁ : g₁ ≫ X.d 0 (0 + 1) + g₂ ≫ δ 0 = 0)
    (h₂ : g₂ ≫ Y.d 0 (0 + 1) = 0) :
    biprod.lift g₁ g₂ ≫ (twistedSum X Y δ hδ).d 0 (0 + 1) = 0 :=
  lift_comp_twistedSumD δ g₁ g₂ h₁ h₂

end Assembly

/-- The assembly step of [Stacks, Tag 05TV]: the twisted direct sum `M^n = I^n ⊕ J^n` with
differential `(d_I^n, (-1)^{n + 1} δ^n; 0, d_J^n)`, filtered by `F^p M^n = F^p I^n ⊕ F^p J^n`, is
a filtered complex, `0 → I^• → M^• → J^• → 0` is short exact and termwise split, and
`b ⊕ (β ≫ c)` is a morphism of filtered complexes `B ⟶ M^•` making both squares commute. -/
private theorem exists_of_twist {A B C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    (α : A ⟶ B) (β : B ⟶ C) (a : A ⟶ I) (c : C ⟶ J) (t : Twist I J) (b : evalFil B 0 ⟶ evalFil I 0)
    (hcomp : α.hom ≫ β.hom = 0)
    (hb : (evalFunctor 0).map α ≫ b = (evalFunctor 0).map a)
    (hd : b ≫ evalD I 0 = (evalFunctor 0).map β ≫ (evalFunctor 0).map c ≫ t.δ 0)
    (hB0 : ∀ n : ℤ, n ≠ 0 → IsZero (B.X.X n)) :
    ∃ (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (u : I ⟶ M) (v : M ⟶ J) (b' : B ⟶ M)
      (huv : u.hom ≫ v.hom = 0), (ShortComplex.mk u.hom v.hom huv).ShortExact ∧
      α ≫ b' = a ≫ u ∧ b' ≫ v = β ≫ c ∧
      ∀ n : ℤ, ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n),
        u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
        (∀ p : ℤ, ∃ rp : (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n,
          rp ≫ (I.filtration.ι.app (op p)).f n = (M.filtration.ι.app (op p)).f n ≫ r) ∧
        (∀ p : ℤ, ∃ sp : (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n,
          sp ≫ (M.filtration.ι.app (op p)).f n = (J.filtration.ι.app (op p)).f n ≫ s) := by
  -- The components of `b`, with their types spelled in `𝒜` rather than through `evalFil`.
  obtain ⟨bhom, bapp, bcomm, hbhom, hdhom, hdstep⟩ :
      ∃ (bhom : B.X.X 0 ⟶ I.X.X 0)
        (bapp : ∀ i : ℤᵒᵖ, (B.filtration.obj i).X 0 ⟶ (I.filtration.obj i).X 0),
        (∀ i, bapp i ≫ (I.filtration.ι.app i).f 0 = (B.filtration.ι.app i).f 0 ≫ bhom) ∧
        α.hom.f 0 ≫ bhom = a.hom.f 0 ∧
        bhom ≫ I.X.d 0 (0 + 1) = β.hom.f 0 ≫ c.hom.f 0 ≫ t.hom 0 ∧
        ∀ i : ℤᵒᵖ, bapp i ≫ (I.filtration.obj i).d 0 (0 + 1) =
          (β.natTrans.app i).f 0 ≫ (c.natTrans.app i).f 0 ≫ t.app i 0 :=
    ⟨b.hom, fun i => b.natTrans.app i, fun i => b.comm i,
      congrArg (fun f => FilteredObject.Hom.hom f) hb,
      congrArg (fun f => FilteredObject.Hom.hom f) hd,
      fun i => congrArg (fun f => FilteredObject.Hom.natTrans f |>.app i) hd⟩
  have hA0 : ∀ n : ℤ, n ≠ 0 → IsZero (A.X.X n) := fun n hn => by
    rcases lt_or_gt_of_ne hn with h | h
    exacts [A.X.isZero_of_isStrictlyGE 0 n h, A.X.isZero_of_isStrictlyLE 0 n h]
  have hC1 : IsZero (C.X.X (0 + 1)) := C.X.isZero_of_isStrictlyLE 0 (0 + 1) (by norm_num)
  have hBstep : ∀ (i : ℤᵒᵖ) (n : ℤ), n ≠ 0 → IsZero ((B.filtration.obj i).X n) := fun i n hn =>
    IsZero.of_mono ((B.filtration.ι.app i).f n) (hB0 n hn)
  have h₁ : biprod.lift bhom ((β.hom ≫ c.hom).f 0) ≫ (twistedSumX t).d 0 (0 + 1) = 0 := by
    refine lift_comp_twistedSum_d _ _ _ _ ?_ ?_
    · rw [twistδ, twistSign_zero, Preadditive.comp_zsmul, hdhom, HomologicalComplex.comp_f,
        neg_smul, one_smul, Category.assoc, add_neg_cancel]
    · rw [HomologicalComplex.comp_f, Category.assoc, c.hom.comm 0 (0 + 1),
        hC1.eq_of_tgt (C.X.d 0 (0 + 1)) 0, zero_comp, comp_zero]
  have h₂ : ∀ i : ℤᵒᵖ, biprod.lift (bapp i) ((β.natTrans.app i ≫ c.natTrans.app i).f 0) ≫
      (twistedSumStep t i).d 0 (0 + 1) = 0 := by
    intro i
    have := mono_ι_app_f C i (0 + 1)
    have hCi : IsZero ((C.filtration.obj i).X (0 + 1)) :=
      IsZero.of_mono ((C.filtration.ι.app i).f (0 + 1)) hC1
    refine lift_comp_twistedSum_d _ _ _ _ ?_ ?_
    · rw [twistδStep, twistSign_zero, Preadditive.comp_zsmul, hdstep i,
        HomologicalComplex.comp_f, neg_smul, one_smul, Category.assoc, add_neg_cancel]
    · rw [HomologicalComplex.comp_f, Category.assoc, (c.natTrans.app i).comm 0 (0 + 1),
        hCi.eq_of_tgt ((C.filtration.obj i).d 0 (0 + 1)) 0, zero_comp, comp_zero]
  have h₃ : ∀ i : ℤᵒᵖ, biprod.lift (bapp i) ((β.natTrans.app i ≫ c.natTrans.app i).f 0) ≫
      biprod.map ((I.filtration.ι.app i).f 0) ((J.filtration.ι.app i).f 0)
      = (B.filtration.ι.app i).f 0 ≫ biprod.lift bhom ((β.hom ≫ c.hom).f 0) := by
    intro i
    have hβc : (β.natTrans.app i ≫ c.natTrans.app i).f 0 ≫ (J.filtration.ι.app i).f 0
        = (B.filtration.ι.app i).f 0 ≫ (β.hom ≫ c.hom).f 0 :=
      congrArg (fun g : B.filtration.obj i ⟶ J.X => g.f 0) ((β ≫ c).comm i)
    rw [biprod_lift_comp_map, comp_biprod_lift, bcomm i, hβc]
    rfl
  obtain ⟨b', hb'0, hb'ne⟩ : ∃ b' : B ⟶ twistedSumFiltered t,
      b'.hom.f 0 = biprod.lift bhom ((β.hom ≫ c.hom).f 0) ∧ ∀ n : ℤ, n ≠ 0 → b'.hom.f n = 0 := by
    refine ⟨FilteredObject.homMk
        (homFromDegreeZero hB0 (biprod.lift bhom ((β.hom ≫ c.hom).f 0)) h₁)
        (fun i => homFromDegreeZero (hBstep i)
          (biprod.lift (bapp i) ((β.natTrans.app i ≫ c.natTrans.app i).f 0)) (h₂ i))
        (fun i => homFromDegreeZero_comp_eq _ _ _ _ _ _ _ _ (h₃ i)), ?_, ?_⟩
    · exact homFromDegreeZero_f_zero hB0 _ h₁
    · exact fun n hn => homFromDegreeZero_f_of_ne hB0 _ h₁ hn
  refine ⟨twistedSumFiltered t, twistedSumFilteredInl t, twistedSumFilteredSnd t, b',
    ?_, ?_, ?_, ?_, ?_⟩
  · ext n
    exact biprod.inl_snd
  · refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
    exact ShortComplex.Splitting.shortExact
      ⟨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd, biprod.total⟩
  · apply FilteredObject.hom_ext
    ext n
    by_cases hn : n = 0
    · subst hn
      have hlhs : (α ≫ b').hom.f 0 = α.hom.f 0 ≫ biprod.lift bhom ((β.hom ≫ c.hom).f 0) := by
        rw [← hb'0]; rfl
      have hrhs : (a ≫ twistedSumFilteredInl t).hom.f 0
          = a.hom.f 0 ≫ (biprod.inl : I.X.X 0 ⟶ I.X.X 0 ⊞ J.X.X 0) := rfl
      rw [hlhs, hrhs]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.inl_fst, Category.comp_id]
        exact hbhom
      · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.inl_snd, comp_zero,
          HomologicalComplex.comp_f, ← Category.assoc,
          ← HomologicalComplex.comp_f α.hom β.hom 0, hcomp]
        simp
    · have hlhs : (α ≫ b').hom.f n = α.hom.f n ≫ b'.hom.f n := rfl
      have hrhs : (a ≫ twistedSumFilteredInl t).hom.f n
          = a.hom.f n ≫ (biprod.inl : I.X.X n ⟶ I.X.X n ⊞ J.X.X n) := rfl
      rw [hlhs, hrhs, hb'ne n hn, (hA0 n hn).eq_of_src (a.hom.f n) 0]
      exact comp_zero.trans zero_comp.symm
  · apply FilteredObject.hom_ext
    ext n
    by_cases hn : n = 0
    · subst hn
      have hlhs : (b' ≫ twistedSumFilteredSnd t).hom.f 0
          = biprod.lift bhom ((β.hom ≫ c.hom).f 0) ≫ biprod.snd := by
        rw [← hb'0]; rfl
      rw [hlhs]
      exact biprod.lift_snd _ _
    · have hlhs : (b' ≫ twistedSumFilteredSnd t).hom.f n
          = b'.hom.f n ≫ (biprod.snd : I.X.X n ⊞ J.X.X n ⟶ J.X.X n) := rfl
      have hrhs : (β ≫ c).hom.f n = β.hom.f n ≫ c.hom.f n := rfl
      rw [hlhs, hrhs, hb'ne n hn, (hB0 n hn).eq_of_src (β.hom.f n) 0]
      exact zero_comp.trans zero_comp.symm
  · exact fun n => ⟨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd,
      fun _ => ⟨biprod.fst, (biprod.map_fst _ _).symm⟩,
      fun _ => ⟨biprod.inr, biprod.inr_map _ _⟩⟩

end CochainComplex.FilteredInjective.TermwiseSplit

namespace CochainComplex

open FilteredInjective.TermwiseSplit in
/-- **Stacks 05TV.** Let `𝒜` be an abelian category and let `0 → A → B → C → 0` be a short exact
sequence of `Fil^f(𝒜)`, i.e. morphisms `α : A ⟶ B`, `β : B ⟶ C` of filtered objects with finite
filtrations whose composite vanishes and whose graded pieces form short exact sequences
`0 → gr^p A → gr^p B → gr^p C → 0`.
Let `a : A[0] ⟶ I^•` and `c : C[0] ⟶ J^•` be filtered quasi-isomorphisms, where `I^•` and `J^•`
are complexes of filtered objects with finite filtrations, vanishing in negative degrees, and
where each `I^n` is a filtered injective object of `Fil^f(𝒜)`. Then
there are a complex `M^•` of filtered objects, morphisms `u : I^• ⟶ M^•`, `v : M^• ⟶ J^•` and
`b : B[0] ⟶ M^•` such that `0 → I^• → M^• → J^• → 0` is short exact, `α ≫ b = a ≫ u` and
`b ≫ v = β ≫ c`, and the sequence `0 → I^n → M^n → J^n → 0` splits in `Fil(𝒜)` in each degree
`n`: there are a retraction `r` of `u^n` and a section `s` of `v^n` compatible with the
filtrations. Filtered objects are placed in degree `0` by taking the filtered complexes `A`, `B`,
`C` to be concentrated in degree `0`. -/
@[stacks 05TV]
public theorem exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B C I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    [I.X.IsStrictlyGE 0] [J.X.IsStrictlyGE 0]
    (α : A ⟶ B) (β : B ⟶ C) (a : A ⟶ I) (c : C ⟶ J)
    (hcomp : α.hom ≫ β.hom = 0)
    (hgr : ∀ p : ℤ, (ShortComplex.mk ((gr p).map α)
      ((gr p).map β) (by
        have hz : ∀ q : ℤᵒᵖ, (α ≫ β).natTrans.app q = 0 := fun q =>
          zero_of_comp_mono (C.filtration.ι.app q) (by simp [hcomp])
        rw [← Functor.map_comp]
        apply coequalizer.hom_ext
        simp only [grMap_map, cokernel.π_desc, hz, zero_comp]
        exact comp_zero.symm)).ShortExact)
    (ha : filteredQuasiIso 𝒜 a) (hc : filteredQuasiIso 𝒜 c)
    (hA : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((A.filtration.ι.app (op p)).f n) ∧
      IsZero ((A.filtration.obj (op q)).X n))
    (hB : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((B.filtration.ι.app (op p)).f n) ∧
      IsZero ((B.filtration.obj (op q)).X n))
    (hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective) :
    ∃ (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (u : I ⟶ M) (v : M ⟶ J) (b : B ⟶ M)
      (huv : u.hom ≫ v.hom = 0), (ShortComplex.mk u.hom v.hom huv).ShortExact ∧
      α ≫ b = a ≫ u ∧ b ≫ v = β ≫ c ∧
      ∀ n : ℤ, ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n),
        u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
        (∀ p : ℤ, ∃ rp : (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n,
          rp ≫ (I.filtration.ι.app (op p)).f n = (M.filtration.ι.app (op p)).f n ≫ r) ∧
        (∀ p : ℤ, ∃ sp : (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n,
          sp ≫ (M.filtration.ι.app (op p)).f n = (J.filtration.ι.app (op p)).f n ≫ s) := by
  obtain ⟨t, b, hb, hd⟩ :=
    exists_twist α β a c hcomp (fun p _ => hgr p) ha hc hA hB hC
      (fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1) hJfin
      (fun p n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).2 p)
  exact exists_of_twist α β a c t b hcomp hb hd
    (fun n hn => isZero_X_of_ne_zero α β (fun p _ => hgr p) hB hcomp n hn)

end CochainComplex

end FilteredTermwiseSplit

end
