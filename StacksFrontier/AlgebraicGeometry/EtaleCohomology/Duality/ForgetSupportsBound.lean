module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.Algebra.Homology.RightDerivedDeltaOne

/-!
# Forgetting supports in degree one, up to bounded torsion

Let `L ⊣ R` be an adjunction between abelian categories with `L` exact, as for
`j^{-1} ⊣ j_*` along an open immersion `j : U → Y`. For objects `O` of the source and `G` of the
target, the degree-one adjunction map

`Ext¹(O, R G) ⟶ Ext¹(L O, G)`, `y ↦ L(y) ∘ ε_G`

(`Stacks.ExtAdjunction.extMap`, read for `O = Λ_Y` as `H¹(Y, j_* G) → H¹(U, G)`) is injective
(`Stacks.ExtAdjunction.injective_extMap_one`), and its cokernel is killed by every integer killing
`R¹R G` (`Stacks.ExtAdjunction.exists_extMap_eq_nsmul_of_rightDerived`): this is the low degree
part `0 → H¹(Y, j_* G) → H¹(U, G) → H⁰(Y, R¹j_* G)` of the Leray spectral sequence. Both are
read off an injective presentation `0 → G → I → C → 0`: `0 → R G → R I → ker(R C → R¹R G) → 0`
is short exact with injective middle term, and `L` carries it to a sequence mapping to the
presentation.

Composing with `Ext¹(O, P) → Ext¹(O, R G)` for a monomorphism `P ↪ R G` whose cokernel is killed
by `N₁` (for `P = j_! G`, the cokernel of `j_! G ↪ j_* G`), the *forget supports* map
`H¹_c(U, G) → H¹(U, G)` has kernel killed by `N₁` and cokernel killed by `N₁ N₂`, `N₂` killing
`R¹j_* G` (`Stacks.ExtAdjunction.forgetSupports_bounds`). These are the two local terms of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`.

## Main results

* `Stacks.ExtAdjunction.injective_extMap_one`.
* `Stacks.ExtAdjunction.exists_extMap_eq_nsmul_of_rightDerived`.
* `Stacks.ExtAdjunction.forgetSupports_bounds`.
-/

@[expose] public noncomputable section

universe w w' v v' u u'

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.RightDerivedDeltaOne

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- Composition of `Ext` is additive in the first argument: `(n • x) ∘ y = n • (x ∘ y)`. -/
private theorem ext_nsmul_comp {X Y Z : C} {a b c : ℕ} (x : Ext X Y a) (y : Ext Y Z b)
    (h : a + b = c) (n : ℕ) : (n • x).comp y h = n • x.comp y h :=
  DFunLike.congr_fun (map_nsmul (Ext.bilinearComp _ _ _ _ _ _ h) n x) y

/-- `Ext.mk₀` commutes with multiplication by a natural number. -/
private theorem ext_mk₀_nsmul {X Y : C} (f : X ⟶ Y) (n : ℕ) : Ext.mk₀ (n • f) = n • Ext.mk₀ f :=
  map_nsmul (Ext.addEquiv₀ (X := X) (Y := Y)).symm n f

/-- If `N` kills `Y`, then `N` kills every `Ext X Y i`. -/
private theorem ext_nsmul_eq_zero_of_nsmul_id {X Y : C} {i N : ℕ} (hY : N • 𝟙 Y = 0)
    (y : Ext X Y i) : N • y = 0 := by
  have h := map_nsmul ((Ext.bilinearComp _ _ _ _ _ _ (add_zero i)) y) N (Ext.mk₀ (𝟙 Y))
  rw [← ext_mk₀_nsmul] at h
  change y.comp (Ext.mk₀ (N • 𝟙 Y)) (add_zero i) = N • y.comp (Ext.mk₀ (𝟙 Y)) (add_zero i) at h
  rw [hY, Ext.mk₀_zero, Ext.comp_zero, Ext.comp_mk₀_id] at h
  exact h.symm

/-- **`Ext¹` with an object killed by `N` is killed by `N`, after pushing a short exact sequence
with such a cokernel.** For a monomorphism `u : P ↪ P'` with cokernel killed by `N`, an element of
`Ext¹(O, P)` dying in `Ext¹(O, P')` is killed by `N`, and `N` times any element of `Ext¹(O, P')`
comes from `Ext¹(O, P)`. -/
theorem ext_one_bounds_of_mono {O P P' : C} (u : P ⟶ P') [Mono u] {N : ℕ}
    (hN : N • 𝟙 (cokernel u) = 0) :
    (∀ w : Ext O P 1, w.comp (Ext.mk₀ u) (add_zero 1) = 0 → N • w = 0) ∧
      ∀ z : Ext O P' 1, ∃ w : Ext O P 1, w.comp (Ext.mk₀ u) (add_zero 1) = N • z := by
  let SQ := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hSQ : SQ.ShortExact := { exact := ShortComplex.exact_cokernel u }
  refine ⟨fun w hw => ?_, fun z => ?_⟩
  · obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ O hSQ w hw (zero_add 1)
    rw [← hx₃, ← ext_nsmul_comp, ext_nsmul_eq_zero_of_nsmul_id hN x₃, Ext.zero_comp]
  · exact Ext.covariant_sequence_exact₂ O hSQ (N • z) (by
      rw [ext_nsmul_comp, ext_nsmul_eq_zero_of_nsmul_id hN])

variable [EnoughInjectives D] [HasInjectiveResolutions D] [R.Additive] [PreservesFiniteLimits R]

/-- The injective presentation `0 → G → I → C → 0`. -/
abbrev presentation (G : D) : ShortComplex D :=
  ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)

omit [HasExt.{w'} D] [HasInjectiveResolutions D] in
/-- The injective presentation `0 → G → I → C → 0` is short exact. -/
theorem presentation_shortExact (G : D) : (presentation G).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- The middle term of the injective presentation is injective. -/
instance (G : D) : Injective (presentation G).X₂ := (inferInstance : Injective (Injective.under G))

/-- `0 → R G → R I → ker(R C → R¹R G) → 0`. -/
abbrev rightPresentation (G : D) : ShortComplex C :=
  ShortComplex.mk (R.map (presentation G).f)
    (kernel.lift (deltaOne R (presentation_shortExact G)) (R.map (presentation G).g)
      (map_g_comp_deltaOne (presentation_shortExact G) R)) (by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, zero_comp, ← R.map_comp,
      (presentation G).zero, R.map_zero])

omit [HasExt.{w} C] [HasExt.{w'} D] in
/-- The sequence `0 → R G → R I → ker(R C → R¹R G) → 0` is short exact. -/
theorem rightPresentation_shortExact (G : D) : (rightPresentation (R := R) G).ShortExact := by
  have hS := presentation_shortExact G
  let ψ : rightPresentation (R := R) G ⟶ (presentation G).map R :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι (deltaOne R hS)
      comm₁₂ := by simp
      comm₂₃ := by simp }
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
        (hS.exact.map_of_mono_of_preservesKernel R hS.mono_f inferInstance)
      mono_f := by
        have := hS.mono_f
        exact R.map_mono _
      epi_g := (exact_map_g_deltaOne hS R).epi_kernelLift }

include adj in
omit [HasExt.{w} C] [HasExt.{w'} D] [PreservesFiniteLimits R] in
/-- The middle term `R I` of `rightPresentation` is injective, `R` having an exact left
adjoint. -/
theorem injective_rightPresentation_X₂ (G : D) : Injective (rightPresentation (R := R) G).X₂ :=
  Injective.injective_of_adjoint adj _

/-- The map from `L` of `rightPresentation` to `presentation`, by the counit. -/
def presentationCounit (G : D) : (rightPresentation (R := R) G).map L ⟶ presentation G :=
  { τ₁ := adj.counit.app G
    τ₂ := adj.counit.app _
    τ₃ := L.map (kernel.ι _) ≫ adj.counit.app _
    comm₁₂ := (adj.counit.naturality _).symm
    comm₂₃ := by
      dsimp
      rw [← Category.assoc, ← L.map_comp, kernel.lift_ι]
      exact (adj.counit.naturality _).symm }

/-- `extMap (b ∘ [SY]) = (L b ∘ ι ∘ ε) ∘ [S]`. -/
theorem extMap_comp_extClass (G : D) {O : C} (b : O ⟶ (rightPresentation (R := R) G).X₃) :
    extMap adj O G 1
        ((Ext.mk₀ b).comp (rightPresentation_shortExact (R := R) G).extClass (zero_add 1)) =
      (Ext.mk₀ (L.map b ≫ (presentationCounit adj G).τ₃)).comp
        (presentation_shortExact G).extClass (zero_add 1) := by
  rw [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_extClass, Ext.comp_assoc_of_third_deg_zero]
  have hn := ((rightPresentation_shortExact (R := R) G).map_of_exact L).extClass_naturality
    (presentation_shortExact G) (presentationCounit adj G)
  show _ = (Ext.mk₀ (L.map b ≫ (presentationCounit adj G).τ₃)).comp _ _
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  exact congrArg (fun z => (Ext.mk₀ (L.map b)).comp z (zero_add 1)) hn

/-- `extMap (b ∘ [SY]) = (L (b ∘ ι) ∘ ε) ∘ [S]`, where `ι : ker(R C → R¹R G) ↪ R C`. -/
private theorem extMap_comp_extClass_kernel_ι (G : D) {O : C}
    (b : O ⟶ (rightPresentation (R := R) G).X₃) :
    extMap adj O G 1
        ((Ext.mk₀ b).comp (rightPresentation_shortExact (R := R) G).extClass (zero_add 1)) =
      (Ext.mk₀ (L.map (b ≫ kernel.ι (deltaOne R (presentation_shortExact G))) ≫
        adj.counit.app _)).comp (presentation_shortExact G).extClass (zero_add 1) := by
  rw [extMap_comp_extClass]
  simp [presentationCounit]

/-- **The degree-one adjunction map is injective** (`H¹(Y, j_* G) ↪ H¹(U, G)`). -/
theorem injective_extMap_one (O : C) (G : D) : Function.Injective (extMap adj O G 1) := by
  have hSY := rightPresentation_shortExact (R := R) G
  have hS := presentation_shortExact G
  have := injective_rightPresentation_X₂ adj G
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨d₀, hd₀⟩ := Ext.covariant_sequence_exact₁ O hSY z (Ext.eq_zero_of_injective _)
    (zero_add 1)
  obtain ⟨d, rfl⟩ := (Ext.mk₀_bijective _ _).2 d₀
  rw [← hd₀, extMap_comp_extClass_kernel_ι] at hz
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (L.obj O) hS _ (zero_add 1) hz
  obtain ⟨e, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have he := (Ext.mk₀_bijective _ _).1 hx₂
  have hd : d = adj.homEquiv _ _ e ≫ (rightPresentation (R := R) G).g := by
    rw [← cancel_mono (kernel.ι (deltaOne R hS)), Category.assoc]
    show d ≫ kernel.ι _ = adj.homEquiv _ _ e ≫ (kernel.lift _ _ _ ≫ kernel.ι _)
    rw [kernel.lift_ι, ← adj.homEquiv_naturality_right, he]
    simp [Adjunction.homEquiv_unit]
  rw [← hd₀, hd, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hSY.comp_extClass,
    Ext.comp_zero]

/-- **The cokernel of the degree-one adjunction map is killed by every integer killing
`R¹R G`** (`H¹(U, G) / H¹(Y, j_* G) ↪ H⁰(Y, R¹j_* G)`). -/
theorem exists_extMap_eq_nsmul_of_rightDerived (O : C) (G : D) {N : ℕ}
    (hN : N • 𝟙 ((R.rightDerived 1).obj G) = 0) (x : Ext (L.obj O) G 1) :
    ∃ y : Ext O (R.obj G) 1, extMap adj O G 1 y = N • x := by
  have hS := presentation_shortExact G
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (L.obj O) hS x (Ext.eq_zero_of_injective _)
    (zero_add 1)
  obtain ⟨c, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₃
  let c' := adj.homEquiv _ _ c
  have hb : (N • c') ≫ deltaOne R hS = 0 := by
    rw [Preadditive.nsmul_comp, ← Preadditive.comp_nsmul,
      show N • deltaOne R hS = deltaOne R hS ≫ (N • 𝟙 _) by
        rw [Preadditive.comp_nsmul, Category.comp_id], hN, comp_zero, comp_zero]
  refine ⟨(Ext.mk₀ (kernel.lift _ (N • c') hb)).comp
    (rightPresentation_shortExact (R := R) G).extClass (zero_add 1), ?_⟩
  rw [extMap_comp_extClass_kernel_ι, ← hx₃]
  have e2 : L.map c' ≫ adj.counit.app _ = c := by
    simp [c', Adjunction.homEquiv_unit]
  rw [kernel.lift_ι, L.map_nsmul, Preadditive.nsmul_comp, e2]
  rw [ext_mk₀_nsmul, ext_nsmul_comp]

/-- **Forgetting supports in degree one, up to bounded torsion.** For a monomorphism
`u : P ↪ R G` with cokernel killed by `N₁` and `R¹R G` killed by `N₂`, the map
`w ↦ extMap (w ∘ u) : Ext¹(O, P) → Ext¹(L O, G)` has kernel killed by `N₁`, and `N₁ N₂` times
every element of `Ext¹(L O, G)` is in its image. -/
theorem forgetSupports_bounds (O : C) (G : D) {P : C} (u : P ⟶ R.obj G) [Mono u] {N₁ N₂ : ℕ}
    (h₁ : N₁ • 𝟙 (cokernel u) = 0) (h₂ : N₂ • 𝟙 ((R.rightDerived 1).obj G) = 0) :
    (∀ w : Ext O P 1, extMap adj O G 1 (w.comp (Ext.mk₀ u) (add_zero 1)) = 0 → N₁ • w = 0) ∧
      ∀ x : Ext (L.obj O) G 1, ∃ w : Ext O P 1,
        extMap adj O G 1 (w.comp (Ext.mk₀ u) (add_zero 1)) = (N₁ * N₂) • x := by
  obtain ⟨hk, hc⟩ := ext_one_bounds_of_mono u h₁ (O := O)
  refine ⟨fun w hw => hk w ((injective_extMap_one adj O G).eq_iff' (map_zero _) |>.1 hw),
    fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_extMap_eq_nsmul_of_rightDerived adj O G h₂ x
  obtain ⟨w, hw⟩ := hc y
  exact ⟨w, by rw [hw, map_nsmul, hy, smul_smul]⟩

end Stacks.ExtAdjunction

end
