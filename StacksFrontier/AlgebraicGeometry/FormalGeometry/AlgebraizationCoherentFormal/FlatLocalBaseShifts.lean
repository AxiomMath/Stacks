module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerBoundary

/-!
# The shift maps of the ideal-power pieces over a Noetherian local base

In the situation of Stacks 0EJU — a Noetherian local ring `(R, 𝔪)` with `R → A`, `I = 𝔪 A`, and
a coherent `I`-adic system `(F_n)` on `U` whose formal stalks are flat over `R` — fix a finite
family `g₁, …, g_d` of generators of `𝔪`, whose images `fₗ` in `A` generate `I`.

The *up maps* `F_n ⟶ F_(n+1)` lift multiplication by `fₗ` along the transitions; they carry
`Iⁿ⁺¹ F_(n+1)` into `Iⁿ⁺² F_(n+2)`, which defines the *shift maps*
`μₗ : Iⁿ⁺¹ F_(n+1) ⟶ Iⁿ⁺² F_(n+2)`. The shifts commute with each other, and after any additive
functor `G` every element of `G(Iⁿ⁺² F_(n+2))` is a sum `∑ₗ G(μₗ)(yₗ)`.

## Main definitions

* `Stacks.Algebraization.maxGens` — a finite generating set of `𝔪`.
* `Stacks.Algebraization.genSection` — the global function on `U` given by a generator.
* `Stacks.Algebraization.upMap` — the up map `F_n ⟶ F_(n+1)` of a generator.
* `Stacks.Algebraization.shiftSub` — the shift `Iⁿ⁺¹ F_(n+1) ⟶ Iⁿ⁺² F_(n+2)` of a generator.

## Main results

* `Stacks.Algebraization.shiftSub_comm` — the shifts of two generators commute.
* `Stacks.Algebraization.exists_sum_shiftSub` — after any additive functor, every element of
  degree `n + 1` is a sum of shifts of elements of degree `n`.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] hasFiniteBiproducts_schemeModules

/-! ### Multiplication by a global function -/

section SectionSmul

variable {X : Scheme.{u}}

/-- Multiplication by a global function commutes with every morphism of `𝒪_X`-modules. -/
theorem comp_sectionSmul {M N : X.Modules} (f : M ⟶ N) (b : Γ(X, ⊤)) :
    f ≫ sectionSmul b N = sectionSmul b M ≫ f :=
  (Stacks.RegularSequence.globalSmulCenter X b).naturality f

/-- Multiplication by `a` followed by multiplication by `b` is multiplication by `b * a`. -/
theorem sectionSmul_comp (a b : Γ(X, ⊤)) (M : X.Modules) :
    sectionSmul a M ≫ sectionSmul b M = sectionSmul (b * a) M := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext x
  change X.presheaf.map V.leTop.op b • (X.presheaf.map V.leTop.op a • x) =
    X.presheaf.map V.leTop.op (b * a) • x
  rw [smul_smul, map_mul]

/-- Multiplication by a global function, as an additive map into the endomorphisms of `M`. -/
def sectionSmulHom (M : X.Modules) : Γ(X, ⊤) →+ (M ⟶ M) where
  toFun b := sectionSmul b M
  map_zero' := by
    refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
    ext x
    change X.presheaf.map V.leTop.op 0 • x = 0
    rw [map_zero, zero_smul]
  map_add' a b := by
    refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
    ext x
    change X.presheaf.map V.leTop.op (a + b) • x =
      X.presheaf.map V.leTop.op a • x + X.presheaf.map V.leTop.op b • x
    rw [map_add, add_smul]

/-- Multiplication by a finite sum of global functions is the sum of the multiplications. -/
theorem sectionSmul_sum {ι : Type*} (s : Finset ι) (b : ι → Γ(X, ⊤)) (M : X.Modules) :
    sectionSmul (∑ i ∈ s, b i) M = ∑ i ∈ s, sectionSmul (b i) M :=
  map_sum (sectionSmulHom M) b s

end SectionSmul

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (B : FlatLocalBase S F)

/-! ### Generators of the maximal ideal -/

/-- A finite generating set of the maximal ideal of the Noetherian local base ring. -/
def maxGens : Finset B.R :=
  (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B.R)).choose

/-- The elements of `maxGens` span the maximal ideal of the base ring. -/
theorem span_maxGens : Ideal.span (maxGens S F B : Set B.R) = IsLocalRing.maximalIdeal B.R :=
  (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B.R)).choose_spec

/-- Every element of `maxGens` lies in the maximal ideal of the base ring. -/
theorem mem_maximalIdeal_of_mem_maxGens (l : maxGens S F B) :
    (l : B.R) ∈ IsLocalRing.maximalIdeal B.R := by
  rw [← span_maxGens S F B]
  exact Ideal.subset_span l.2

/-- The global function on `U` determined by a generator of `𝔪`. -/
abbrev genSection (l : maxGens S F B) : Γ(S.U.toScheme, ⊤) := scalarMap S (B.φ l)

/-- The image in `A` of a generator of `𝔪` lies in `I`. -/
theorem gen_mem_I (l : maxGens S F B) : B.φ l ∈ S.I := by
  rw [B.I_eq]
  exact Ideal.mem_map_of_mem _ (mem_maximalIdeal_of_mem_maxGens S F B l)

/-- The images of the generators of `𝔪` generate `I`. -/
theorem I_eq_span_gens : S.I = Ideal.span (Set.range fun l : maxGens S F B => B.φ l) := by
  rw [B.I_eq, ← span_maxGens S F B, Ideal.map_span]
  congr 1
  ext x
  simp

/-- The global function of a generator of `𝔪` restricts on every open to a section of `I`. -/
theorem restrictMemIdealPow_genSection (l : maxGens S F B) :
    RestrictMemIdealPow (idealOnOpen S) 1 (genSection S F B l) :=
  restrictMemIdealPow_scalarMap S 1 (by simpa using gen_mem_I S F B l)

/-! ### The up maps -/

/-- The transition `F_(n+1) ⟶ F_n`. -/
abbrev succTrans (n : ℕ) : F.obj.obj (op (n + 1)) ⟶ F.obj.obj (op n) :=
  F.obj.map (homOfLE (Nat.le_succ n)).op

/-- There is a morphism `u : F_n ⟶ F_(n+1)` whose composites with the transition `F_(n+1) ⟶ F_n`
on either side are multiplication by the global function of a generator. -/
theorem exists_upMap (l : maxGens S F B) (n : ℕ) :
    ∃ u : F.obj.obj (op n) ⟶ F.obj.obj (op (n + 1)),
      succTrans S F n ≫ u = sectionSmul (genSection S F B l) (F.obj.obj (op (n + 1))) ∧
        u ≫ succTrans S F n = sectionSmul (genSection S F B l) (F.obj.obj (op n)) :=
  exists_transitionSmulUp F (Nat.le_succ n) (le_refl (n + 1))
    (restrictMemIdealPow_genSection S F B l)

/-- **The up map of a generator**: multiplication by `fₗ`, lifted to `F_n ⟶ F_(n+1)`. -/
def upMap (l : maxGens S F B) (n : ℕ) : F.obj.obj (op n) ⟶ F.obj.obj (op (n + 1)) :=
  (exists_upMap S F B l n).choose

/-- The transition `F_(n+1) ⟶ F_n` followed by the up map is multiplication by the generator on
`F_(n+1)`. -/
theorem trans_upMap (l : maxGens S F B) (n : ℕ) :
    succTrans S F n ≫ upMap S F B l n =
      sectionSmul (genSection S F B l) (F.obj.obj (op (n + 1))) :=
  (exists_upMap S F B l n).choose_spec.1

/-- The up map followed by the transition `F_(n+1) ⟶ F_n` is multiplication by the generator on
`F_n`. -/
theorem upMap_trans (l : maxGens S F B) (n : ℕ) :
    upMap S F B l n ≫ succTrans S F n = sectionSmul (genSection S F B l) (F.obj.obj (op n)) :=
  (exists_upMap S F B l n).choose_spec.2

/-- Two transitions `F_(n+2) ⟶ F_n` followed by the up maps of `l'` and `l` give multiplication
by the product of the two generators on `F_(n+2)`. -/
theorem succTrans_succTrans_upMap_upMap (l l' : maxGens S F B) (n : ℕ) :
    succTrans S F (n + 1) ≫ succTrans S F n ≫ upMap S F B l' n ≫ upMap S F B l (n + 1) =
      sectionSmul (genSection S F B l * genSection S F B l') (F.obj.obj (op (n + 2))) := by
  rw [← Category.assoc (succTrans S F n), trans_upMap, ← Category.assoc, comp_sectionSmul,
    Category.assoc, trans_upMap, sectionSmul_comp]

/-- The up maps of two generators commute. -/
theorem upMap_comm (l l' : maxGens S F B) (n : ℕ) :
    upMap S F B l' n ≫ upMap S F B l (n + 1) = upMap S F B l n ≫ upMap S F B l' (n + 1) := by
  have : Epi (succTrans S F n) := F.property.epi_map (Nat.le_succ n)
  have : Epi (succTrans S F (n + 1)) := F.property.epi_map (Nat.le_succ (n + 1))
  rw [← cancel_epi (succTrans S F n), ← cancel_epi (succTrans S F (n + 1)),
    succTrans_succTrans_upMap_upMap, succTrans_succTrans_upMap_upMap, mul_comm]

/-! ### The shift maps -/

/-- The up map `F_(n+1) ⟶ F_(n+2)`, restricted to `Iⁿ⁺¹ F_(n+1)`, vanishes after the projection
of `F_(n+2)` onto its quotient by `Iⁿ⁺² F_(n+2)`. -/
theorem idealPowerSub_ι_upMap_comp_π (l : maxGens S F B) (n : ℕ) :
    ((idealPowerSub S F n).ι ≫ upMap S F B l (n + 1)) ≫
      (idealPowerShortComplex S F (n + 1)).g = 0 := by
  have : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  obtain ⟨e, he⟩ := F.property.2.2 (n + 1)
  have hzero := idealPowerMultiple_ι_comp_sectionSmul (F.obj.obj (op (n + 1))) (k := 1)
    (d := n + 1) (r := n + 1 + 1) (by omega) (F.property.idealPowerMultiple_eq_bot (n + 1))
    (restrictMemIdealPow_genSection S F B l)
  have hπ : (idealPowerShortComplex S F (n + 1)).g = succTrans S F (n + 1) ≫ e.inv :=
    (Iso.eq_comp_inv e).mpr he
  rw [hπ]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun φ ↦ φ ≫ e.inv) ((Category.assoc _ _ _).trans
      ((congrArg (fun φ ↦ (idealPowerSub S F n).ι ≫ φ) (upMap_trans S F B l (n + 1))).trans
        hzero))).trans zero_comp)

/-- **The shift of a generator**, `Iⁿ⁺¹ F_(n+1) ⟶ Iⁿ⁺² F_(n+2)`: the restriction of its up map
`F_(n+1) ⟶ F_(n+2)`. -/
def shiftSub (l : maxGens S F B) (n : ℕ) :
    (idealPowerSub S F n).toSheafOfModules ⟶ (idealPowerSub S F (n + 1)).toSheafOfModules :=
  (idealPowerShortComplex_shortExact S F (n + 1)).exact.lift
    ((idealPowerSub S F n).ι ≫ upMap S F B l (n + 1))
    (idealPowerSub_ι_upMap_comp_π S F B l n)

/-- The shift of a generator, followed by the inclusion of `Iⁿ⁺² F_(n+2)`, is the inclusion of
`Iⁿ⁺¹ F_(n+1)` followed by the up map. -/
theorem shiftSub_ι (l : maxGens S F B) (n : ℕ) :
    shiftSub S F B l n ≫ (idealPowerSub S F (n + 1)).ι =
      (idealPowerSub S F n).ι ≫ upMap S F B l (n + 1) :=
  (idealPowerShortComplex_shortExact S F (n + 1)).exact.lift_f _ _

/-- Two composites of lifts through monomorphisms agree when the composites of the morphisms they
lift do. -/
theorem comp_eq_comp_of_lift {C : Type*} [Category C] {K₀ K₁ K₂ T₁ T₂ T₃ : C}
    (i₀ : K₀ ⟶ T₁) (i₁ : K₁ ⟶ T₂) (i₂ : K₂ ⟶ T₃)
    (hi₂ : ∀ f g : K₀ ⟶ K₂, f ≫ i₂ = g ≫ i₂ → f = g)
    {a a' : K₀ ⟶ K₁} {b b' : K₁ ⟶ K₂} {u u' : T₁ ⟶ T₂} {v v' : T₂ ⟶ T₃}
    (ha : a ≫ i₁ = i₀ ≫ u) (ha' : a' ≫ i₁ = i₀ ≫ u') (hb : b ≫ i₂ = i₁ ≫ v)
    (hb' : b' ≫ i₂ = i₁ ≫ v') (huv : u ≫ v = u' ≫ v') : a ≫ b = a' ≫ b' := by
  refine hi₂ _ _ ?_
  rw [Category.assoc, Category.assoc, hb, hb', ← Category.assoc, ← Category.assoc, ha, ha',
    Category.assoc, Category.assoc, huv]

/-- The shifts of two generators commute. -/
theorem shiftSub_comm (l l' : maxGens S F B) (n : ℕ) :
    shiftSub S F B l' n ≫ shiftSub S F B l (n + 1) =
      shiftSub S F B l n ≫ shiftSub S F B l' (n + 1) :=
  comp_eq_comp_of_lift _ _ _ (cancel_sheafSubmodule_ι (idealPowerSub S F (n + 1 + 1)))
    (shiftSub_ι S F B l' n) (shiftSub_ι S F B l n) (shiftSub_ι S F B l (n + 1))
    (shiftSub_ι S F B l' (n + 1)) (upMap_comm S F B l l' (n + 1))

/-! ### Generation in degree one -/

/-- A morphism `c`, cancelled against an epimorphism `t` and a monomorphism `i₁`, equals the sum
`∑ₗ c'ₗ ≫ μₗ` when the corresponding composites agree. -/
theorem eq_sum_comp_of_cancel {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (s : Finset ι) {T₀ T₁ T₂ K₀ K₁ : C} (t : T₂ ⟶ T₀) (τ : T₂ ⟶ T₁) (t' : T₁ ⟶ T₀)
    (htt : τ ≫ t' = t) [Epi t] (i₀ : K₀ ⟶ T₁) (i₁ : K₁ ⟶ T₂)
    (hi₁ : ∀ f g : T₀ ⟶ K₁, f ≫ i₁ = g ≫ i₁ → f = g)
    (c : T₀ ⟶ K₁) (c' : ι → (T₀ ⟶ K₀)) (μ : ι → (K₀ ⟶ K₁)) (up : ι → (T₁ ⟶ T₂))
    (m₂ : T₂ ⟶ T₂) (m₁ : ι → (T₁ ⟶ T₁)) (m : ι → (T₂ ⟶ T₂))
    (hc : t ≫ c ≫ i₁ = m₂) (hc' : ∀ l, t' ≫ c' l ≫ i₀ = m₁ l)
    (hμ : ∀ l, μ l ≫ i₁ = i₀ ≫ up l) (hm : ∀ l, τ ≫ m₁ l ≫ up l = m l)
    (hsum : m₂ = ∑ l ∈ s, m l) : c = ∑ l ∈ s, c' l ≫ μ l := by
  refine hi₁ _ _ ((cancel_epi t).mp ?_)
  rw [hc, Preadditive.sum_comp, Preadditive.comp_sum, hsum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← hm l, Category.assoc, hμ l, ← htt, Category.assoc, ← Category.assoc (c' l),
    ← Category.assoc t', hc' l]

/-- After an additive functor, a target decomposed as a finite direct sum whose components are
sums of composites with a family `μ` is spanned by the images of the `G(μₗ)`. -/
theorem exists_eq_sum_map_of_isIso {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {A' : Type*} [Ring A'] (G : C ⥤ ModuleCat.{v} A') [G.Additive]
    {L : Type*} [Fintype L] {k : ℕ} {T K K' : C} (D : (⨁ fun _ : Fin k => T) ⟶ K') [IsIso D]
    (c' : Fin k → L → (T ⟶ K)) (μ : L → (K ⟶ K'))
    (hD : ∀ i, biproduct.ι (fun _ : Fin k => T) i ≫ D = ∑ l, c' i l ≫ μ l) (x : G.obj K') :
    ∃ y : L → G.obj K, x = ∑ l, (G.map (μ l)).hom (y l) := by
  classical
  let z := (G.map (inv D)).hom x
  have hx : x = (G.map D).hom z := by
    change x = (G.map (inv D) ≫ G.map D).hom x
    rw [← G.map_comp, IsIso.inv_hom_id, G.map_id]
    rfl
  have hz : z = ∑ i, (G.map (biproduct.ι (fun _ : Fin k ↦ T) i)).hom
      ((G.map (biproduct.π (fun _ : Fin k ↦ T) i)).hom z) := by
    have h := congrArg (fun φ ↦ (G.map φ).hom z) (biproduct.total (f := fun _ : Fin k ↦ T))
    simp only [G.map_id, G.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, G.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.symm
  have hD' (i : Fin k) (w : G.obj T) :
      (G.map D).hom ((G.map (biproduct.ι (fun _ : Fin k ↦ T) i)).hom w) =
      ∑ l, (G.map (μ l)).hom ((G.map (c' i l)).hom w) := by
    simpa only [G.map_comp, G.map_sum, ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
      LinearMap.comp_apply] using congrArg (fun φ ↦ (G.map φ).hom w) (hD i)
  refine ⟨fun l ↦ ∑ i, (G.map (c' i l)).hom ((G.map (biproduct.π (fun _ : Fin k ↦ T) i)).hom z),
    ?_⟩
  calc x = (G.map D).hom z := hx
    _ = (G.map D).hom (∑ i, (G.map (biproduct.ι (fun _ : Fin k ↦ T) i)).hom
          ((G.map (biproduct.π (fun _ : Fin k ↦ T) i)).hom z)) := congrArg (G.map D).hom hz
    _ = ∑ i, ∑ l, (G.map (μ l)).hom ((G.map (c' i l)).hom
          ((G.map (biproduct.π (fun _ : Fin k ↦ T) i)).hom z)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ hD' i _
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [map_sum]

/-- The transition `F_(n+2) ⟶ F_(n+1)` followed by the transition `F_(n+1) ⟶ F_0` is the
transition `F_(n+2) ⟶ F_0`. -/
theorem succTrans_zero (n : ℕ) :
    succTrans S F (n + 1) ≫ F.obj.map (homOfLE (Nat.zero_le (n + 1))).op =
      F.obj.map (homOfLE (Nat.zero_le (n + 1 + 1))).op := by
  rw [← F.obj.map_comp]
  rfl

/-- An element of `𝔪ⁿ⁺²` is `∑ₗ gₗ sₗ` with every `sₗ ∈ 𝔪ⁿ⁺¹`. -/
theorem exists_eq_sum_gen_mul (n : ℕ) (r : B.R)
    (hr : r ∈ IsLocalRing.maximalIdeal B.R ^ (n + 1 + 1)) :
    ∃ a : maxGens S F B → B.R, (∀ l, a l ∈ IsLocalRing.maximalIdeal B.R ^ (n + 1)) ∧
      ∑ l : maxGens S F B, (l : B.R) * a l = r := by
  classical
  have hmem : r ∈ IsLocalRing.maximalIdeal B.R ^ (n + 1) •
      Submodule.span B.R (Set.range fun l : maxGens S F B ↦ (l : B.R)) := by
    have hrange : Set.range (fun l : maxGens S F B ↦ (l : B.R)) = (maxGens S F B : Set B.R) := by
      ext x
      simp
    rwa [hrange, ← Ideal.span, span_maxGens S F B, Ideal.smul_eq_mul, ← pow_succ]
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hmem
  refine ⟨a, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **Generation in degree one.** In the situation of Stacks 0EJU, after any additive functor
`G`, every element of `G(Iⁿ⁺² F_(n+2))` is a sum `∑ₗ G(μₗ)(yₗ)` of shifts of elements of
`G(Iⁿ⁺¹ F_(n+1))`. -/
theorem exists_sum_shiftSub {A' : Type*} [Ring A'] (G : S.U.toScheme.Modules ⥤ ModuleCat.{v} A')
    [G.Additive] (n : ℕ) (x : G.obj (idealPowerSub S F (n + 1)).toSheafOfModules) :
    ∃ y : maxGens S F B → G.obj (idealPowerSub S F n).toSheafOfModules,
      x = ∑ l, (G.map (shiftSub S F B l n)).hom (y l) := by
  classical
  have := F.property.isQuasicoherent (n + 1 + 1)
  have := F.property.isQuasicoherent (n + 1)
  obtain ⟨e, he⟩ := exists_quotientZeroIso F (n + 1 + 1)
  obtain ⟨e', he'⟩ := exists_quotientZeroIso F (n + 1)
  obtain ⟨k, r, hr, hb, hiso⟩ := exists_isIso_idealPowerDesc S F B (n + 1) e he
  choose a ha hsum using fun i ↦ exists_eq_sum_gen_mul S F B n (r i) (hr i)
  have hs : ∀ i l, RestrictMemIdealPow (idealOnOpen S) (n + 1) (scalarMap S (B.φ (a i l))) :=
    fun i l ↦ restrictMemIdealPow_scalarMap S (n + 1) <| by
      rw [B.I_eq, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (ha i l)
  have : Epi (F.obj.map (homOfLE (Nat.zero_le (n + 1 + 1))).op) :=
    F.property.epi_map (Nat.zero_le (n + 1 + 1))
  refine exists_eq_sum_map_of_isIso (C := S.U.toScheme.Modules) G
    (idealPowerDesc (F.obj.obj (op (n + 1 + 1))) (n + 1 + 1)
      (F.property.idealPowerMultiple_eq_bot (n + 1 + 1)) hb e)
    (fun i l ↦ idealPowerComponent (F.obj.obj (op (n + 1))) (n + 1)
      (F.property.idealPowerMultiple_eq_bot (n + 1)) (hs i l) e')
    (fun l ↦ shiftSub S F B l n) (fun i ↦ ?_) x
  refine (biproduct.ι_desc _ i).trans ?_
  refine eq_sum_comp_of_cancel (C := S.U.toScheme.Modules) Finset.univ
    (F.obj.map (homOfLE (Nat.zero_le (n + 1 + 1))).op)
    (succTrans S F (n + 1)) (F.obj.map (homOfLE (Nat.zero_le (n + 1))).op)
    (succTrans_zero S F n) (idealPowerSub S F n).ι (idealPowerSub S F (n + 1)).ι
    (cancel_sheafSubmodule_ι (idealPowerSub S F (n + 1))) _ _ (fun l ↦ shiftSub S F B l n)
    (fun l ↦ upMap S F B l (n + 1)) _ _
    (fun l ↦ sectionSmul (genSection S F B l * scalarMap S (B.φ (a i l)))
      (F.obj.obj (op (n + 1 + 1))))
    (comp_idealPowerComponent_comp_ι _ _ _ (hb i) e he)
    (fun l ↦ comp_idealPowerComponent_comp_ι _ _ _ (hs i l) e' he')
    (fun l ↦ shiftSub_ι S F B l n) (fun l ↦ ?_) ?_
  · rw [← Category.assoc, comp_sectionSmul, Category.assoc, trans_upMap, sectionSmul_comp]
  · rw [← sectionSmul_sum, ← hsum i, map_sum, map_sum]
    exact congrArg (fun b ↦ sectionSmul b _)
      (Finset.sum_congr rfl fun l _ ↦ by rw [map_mul, map_mul])

end Stacks.Algebraization

end
