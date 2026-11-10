module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Generation
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Curves.VeryAmpleSixthPower
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# The section ring of a globally generated invertible sheaf on a curve

Let `f : X ⟶ Spec k` be proper with `X` of dimension at most one, and let `L` be an invertible
`𝒪_X`-module which is globally generated and has `H¹(X, L) = 0`. This file proves that the graded
section ring `S = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` is generated over `S₀` in degrees one and
two, and hence that its second Veronese subring `S^{(2)} = ⨁_n S_{2n}` is generated in degree
one. This is the algebraic half of the proof of [Stacks, Tag 0E8W].

## The argument

Choose finitely many global sections `s₁, …, s_r` of `L` generating it, so that the evaluation map
`ε : 𝒪_X^{⊕ r} ⟶ L` is an epimorphism, and let `K` be its kernel. Tensoring the short exact
sequence `0 ⟶ K ⟶ 𝒪_X^{⊕ r} ⟶ L ⟶ 0` with `L ^⊗ m` (an exact functor, `L` being invertible)
gives `0 ⟶ K ⊗ L ^⊗ m ⟶ (L ^⊗ m)^{⊕ r} ⟶ L ^⊗ (m + 1) ⟶ 0`, whose map on global sections is
`(t_i) ↦ ∑ s_i t_i`. Since `H²` vanishes on the one-dimensional `X`:

* `H¹(L ^⊗ m) = 0` for every `m ≥ 1`, by induction on `m`;
* the Koszul map `𝒪_X^{⊕ r × r} ⟶ 𝒪_X^{⊕ r} ⊗ L`, `e_{(i, j)} ↦ e_i ⊗ s_j - e_j ⊗ s_i`, maps onto
  `K ⊗ L` (commutativity of the section ring makes it land there, and the epimorphism
  `K ⊗ 𝒪_X^{⊕ r} ⟶ K ⊗ L` factors through it); twisting, `K ⊗ L ^⊗ (p + 1)` is a quotient of
  `(L ^⊗ p)^{⊕ r × r}`, so `H¹(K ⊗ L ^⊗ (p + 1)) = 0` for `p ≥ 1`;
* hence `Γ(L) ⊗ Γ(L ^⊗ m) ⟶ Γ(L ^⊗ (m + 1))` is onto for `m ≥ 2`.

The source instead passes to an algebraically closed ground field and uses a regular section of
`L` nonvanishing on the zero scheme of a second one; the Koszul complex makes that detour
unnecessary and works over any field.

## Main results

* `Stacks.Curves.SectionRingDegreeTwo.exists_sum_mul_eq`: for `m ≥ 2` every global section of
  `L ^⊗ (1 + m)` is `∑ s_i t_i` with `t_i` sections of `L ^⊗ m`.
* `Stacks.Curves.SectionRingDegreeTwo.veroneseGeneratedInDegOne_two_of_mul`: a graded ring
  generated in degrees one and two has its second Veronese generated in degree one.
* `Stacks.Curves.SectionRingDegreeTwo.veroneseGeneratedInDegOne_two`: `S^{(2)}` is generated in
  degree one.

## References

* [Stacks Project, Tag 0E8W](https://stacks.math.columbia.edu/tag/0E8W)
* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Stacks.Ample Stacks.GradedSections Stacks.TensorPowers
open Stacks.AmpleFiniteAvoidance (grading)

universe u

namespace Stacks.Curves.SectionRingDegreeTwo

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

-- Finite biproducts in `X.Modules`, for the preadditive structure installed above.
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Tensoring on the left in `X.Modules` is additive. -/
local instance schemeTensorLeftAdditiveSRD {X : Scheme.{u}} (M : X.Modules) :
    (tensorLeft M).Additive :=
  Stacks.SectionRingGeometric.tensorLeftAdditive X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

section Twist

variable {X : Scheme.{u}} (L : X.Modules)

/-- The functor `F ↦ F ⊗ L ⊗ ⋯ ⊗ L` with `m` factors `L`, nested to the left. -/
def twistFunctor : ℕ → (X.Modules ⥤ X.Modules)
  | 0 => 𝟭 _
  | m + 1 => twistFunctor m ⋙ tensorRight L

/-- Twisting zero times is the identity functor `𝟭 X.Modules`. -/
@[simp] theorem twistFunctor_zero : twistFunctor L 0 = 𝟭 _ := rfl

/-- Twisting `m + 1` times is twisting `m` times followed by `- ⊗ L`. -/
theorem twistFunctor_succ (m : ℕ) :
    twistFunctor L (m + 1) = twistFunctor L m ⋙ tensorRight L :=
  rfl

variable [IsInvertibleModule X L]

/-- Twisting `m` times by an invertible module is an equivalence. -/
instance isEquivalence_twistFunctor : ∀ m : ℕ, (twistFunctor L m).IsEquivalence
  | 0 => inferInstanceAs (𝟭 X.Modules).IsEquivalence
  | m + 1 => by
      have := isEquivalence_twistFunctor m
      have := Stacks.AmpleEventualGeneration.isEquivalence_tensorRight L
      exact inferInstanceAs (twistFunctor L m ⋙ tensorRight L).IsEquivalence

/-- Twisting `m` times is an additive functor. -/
instance additive_twistFunctor : ∀ m : ℕ, (twistFunctor L m).Additive
  | 0 => inferInstanceAs (𝟭 X.Modules).Additive
  | m + 1 => by
      have := additive_twistFunctor m
      exact inferInstanceAs (twistFunctor L m ⋙ tensorRight L).Additive

/-- Twisting once more commutes with twisting `m` times. -/
def twistFunctorCommIso : ∀ m : ℕ,
    tensorRight L ⋙ twistFunctor L m ≅ twistFunctor L m ⋙ tensorRight L
  | 0 => Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | m + 1 =>
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (twistFunctorCommIso m) _

/-- `(twistFunctor L m).obj 𝒪 ≅ L ^⊗ m`, as the identity in each degree. -/
def twistUnitIso : ∀ m : ℕ, (twistFunctor L m).obj (𝟙_ X.Modules) ≅ natTensorPow L m
  | 0 => Iso.refl _
  | m + 1 => whiskerRightIso (twistUnitIso m) L

/-- `(twistFunctor L m).obj (L ^⊗ n) ≅ L ^⊗ (n + m)`, as the identity in each degree. -/
def twistPowIso (n : ℕ) :
    ∀ m : ℕ, (twistFunctor L m).obj (natTensorPow L n) ≅ natTensorPow L (n + m)
  | 0 => Iso.refl _
  | m + 1 => whiskerRightIso (twistPowIso n m) L

omit [IsInvertibleModule X L] in
/-- **The twist of a section is multiplication by it.** -/
theorem twistFunctor_map_comp_twistPowIso {n : ℕ} (t : powSections L n) : ∀ m : ℕ,
    (twistFunctor L m).map t ≫ (twistPowIso L n m).hom = (twistUnitIso L m).hom ≫ mulMap t m
  | 0 => by
      change t ≫ 𝟙 _ = 𝟙 _ ≫ t
      rw [Category.comp_id, Category.id_comp]
  | m + 1 => by
      change ((twistFunctor L m).map t ▷ L) ≫ ((twistPowIso L n m).hom ▷ L) =
        ((twistUnitIso L m).hom ▷ L) ≫ (mulMap t m ▷ L)
      rw [← comp_whiskerRight, ← comp_whiskerRight, twistFunctor_map_comp_twistPowIso t m]

end Twist

/-! ### Vanishing of cohomology on finite direct sums -/

section Biproduct

/-- An additive functor kills a finite biproduct of objects it kills. -/
theorem isZero_obj_biproduct {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {J : Type} [Finite J] (Y : J → C)
    [HasBiproduct Y] (h : ∀ j, IsZero (G.obj (Y j))) : IsZero (G.obj (⨁ Y)) := by
  classical
  have := Fintype.ofFinite J
  rw [IsZero.iff_id_eq_zero, ← G.map_id, ← biproduct.total (f := Y), G.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [G.map_comp, (h j).eq_of_tgt (G.map (biproduct.π Y j)) 0, zero_comp]

end Biproduct

/-! ### The evaluation map and its twists -/

section Koszul

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
  {I : Type} [Fintype I] (s : I → powSections L 1)

/-- The evaluation map `𝒪_X^{⊕ I} ⟶ L` of a finite family of global sections of `L`. -/
def evalMap : (⨁ fun _ : I => 𝟙_ X.Modules) ⟶ natTensorPow L 1 := biproduct.desc s

/-- The short complex `0 ⟶ K ⟶ 𝒪_X^{⊕ I} ⟶ L ⟶ 0`, with `K` the kernel of the evaluation map. -/
abbrev baseComplex : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (evalMap L s)) (evalMap L s) (kernel.condition _)

omit [IsInvertibleModule X L] in
/-- When the evaluation map is an epimorphism, `0 ⟶ K ⟶ 𝒪_X^{⊕ I} ⟶ L ⟶ 0` is short exact. -/
theorem baseComplex_shortExact [Epi (evalMap L s)] : (baseComplex L s).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι (evalMap L s)))
  epi_g := inferInstanceAs (Epi (evalMap L s))

/-- The base short complex twisted `m` times by `L`. -/
abbrev levelComplex (m : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk ((twistFunctor L m).map (kernel.ι (evalMap L s)))
    ((twistFunctor L m).map (evalMap L s)) (by rw [← Functor.map_comp, kernel.condition,
      Functor.map_zero])

/-- When the evaluation map is an epimorphism, each twist of the base complex is short exact. -/
theorem levelComplex_shortExact [Epi (evalMap L s)] (m : ℕ) :
    (levelComplex L s m).ShortExact :=
  (baseComplex_shortExact L s).map_of_exact (twistFunctor L m)

omit [IsInvertibleModule X L] in
/-- `λ⁻¹ ≫ (g ⊗ (t ≫ λ)) = t ≫ (g ▷ L)`, for `t` a section of `L`. -/
theorem leftUnitor_inv_comp_tensorHom {Y : X.Modules} (g : 𝟙_ X.Modules ⟶ Y)
    (t : powSections L 1) :
    (λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ (t ≫ (λ_ L).hom)) = t ≫ (g ▷ L) := by
  rw [tensorHom_def', ← Category.assoc, ← leftUnitor_inv_naturality]
  show ((t ≫ (λ_ L).hom) ≫ (λ_ L).inv) ≫ (g ▷ L) = t ≫ (g ▷ L)
  simp

omit [IsInvertibleModule X L] in
/-- `λ⁻¹ ≫ (a ⊗ (b ≫ λ)) = a · b`, for two sections of `L`. -/
theorem leftUnitor_inv_comp_tensorHom_eq_mul (a b : powSections L 1) :
    (λ_ (𝟙_ X.Modules)).inv ≫ (a ⊗ₘ (b ≫ (λ_ L).hom)) = mul a b :=
  (leftUnitor_inv_comp_tensorHom L a b).trans (mul_def a b).symm

/-- **The Koszul map** `𝒪_X^{⊕ I × I} ⟶ 𝒪_X^{⊕ I} ⊗ L`, `e_{(i,j)} ↦ e_i ⊗ s_j - e_j ⊗ s_i`. -/
def koszulMap : (⨁ fun _ : I × I => 𝟙_ X.Modules) ⟶ (⨁ fun _ : I => 𝟙_ X.Modules) ⊗ L :=
  biproduct.desc fun p : I × I =>
    (λ_ (𝟙_ X.Modules)).inv ≫
        (biproduct.ι (fun _ : I => 𝟙_ X.Modules) p.1 ⊗ₘ (s p.2 ≫ (λ_ L).hom)) -
      (λ_ (𝟙_ X.Modules)).inv ≫
        (biproduct.ι (fun _ : I => 𝟙_ X.Modules) p.2 ⊗ₘ (s p.1 ≫ (λ_ L).hom))

omit [IsInvertibleModule X L] in
/-- The second map of the base complex twisted once is `evalMap L s ▷ L`. -/
theorem levelComplex_one_g : (levelComplex L s 1).g = evalMap L s ▷ L := rfl

/-- The Koszul map composed with `evalMap L s ▷ L` is zero. -/
theorem koszulMap_comp_g : koszulMap L s ≫ (evalMap L s ▷ L) = 0 := by
  refine biproduct.hom_ext' _ _ fun p => ?_
  rw [koszulMap, biproduct.ι_desc_assoc, comp_zero, Preadditive.sub_comp,
    Category.assoc, Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, evalMap, biproduct.ι_desc, biproduct.ι_desc,
    Category.comp_id, Category.comp_id, leftUnitor_inv_comp_tensorHom_eq_mul,
    leftUnitor_inv_comp_tensorHom_eq_mul, ← mul_comm' (s p.2) (s p.1), powCongr_rfl,
    Category.comp_id, sub_self]

/-- The `j`-th column inclusion `𝒪_X^{⊕ I} ⟶ 𝒪_X^{⊕ I × I}`, `e_i ↦ e_{(i, j)}`. -/
def columnMap (j : I) : (⨁ fun _ : I => 𝟙_ X.Modules) ⟶ ⨁ fun _ : I × I => 𝟙_ X.Modules :=
  biproduct.desc fun i => biproduct.ι (fun _ : I × I => 𝟙_ X.Modules) (i, j)

omit [IsInvertibleModule X L] in
/-- The `j`-th column of the Koszul map sends `e_i` to `e_i ⊗ s_j - e_j ⊗ s_i`. -/
theorem columnMap_comp_koszulMap (j : I) :
    columnMap j ≫ koszulMap L s =
      (ρ_ _).inv ≫ ((⨁ fun _ : I => 𝟙_ X.Modules) ◁ (s j ≫ (λ_ L).hom)) -
        evalMap L s ≫ (biproduct.ι (fun _ : I => 𝟙_ X.Modules) j ▷ L) := by
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [columnMap, biproduct.ι_desc_assoc, koszulMap, biproduct.ι_desc, Preadditive.comp_sub]
  congr 1
  · rw [rightUnitor_inv_naturality_assoc, ← tensorHom_def, unitors_inv_equal]
  · rw [evalMap, biproduct.ι_desc_assoc, leftUnitor_inv_comp_tensorHom]

/-- The Koszul map lands in `K ⊗ L`, the kernel of `evalMap ▷ L`. -/
def koszulLift [Epi (evalMap L s)] :
    (⨁ fun _ : I × I => 𝟙_ X.Modules) ⟶ kernel (evalMap L s) ⊗ L :=
  haveI := (levelComplex_shortExact L s 1).mono_f
  (levelComplex_shortExact L s 1).exact.lift (koszulMap L s) (koszulMap_comp_g L s)

/-- The lift of the Koszul map to `K ⊗ L`, followed by the inclusion `K ⊗ L ⟶ 𝒪_X^{⊕ I} ⊗ L`,
is the Koszul map. -/
theorem koszulLift_comp [Epi (evalMap L s)] :
    koszulLift L s ≫ (kernel.ι (evalMap L s) ▷ L) = koszulMap L s :=
  have := (levelComplex_shortExact L s 1).mono_f
  (levelComplex_shortExact L s 1).exact.lift_f (koszulMap L s) (koszulMap_comp_g L s)

/-- **The Koszul complex `𝒪_X^{⊕ I × I} ⟶ 𝒪_X^{⊕ I} ⊗ L ⟶ L ⊗ L` is exact**: the Koszul map
is an epimorphism onto `K ⊗ L`. The epimorphism `K ⊗ 𝒪_X^{⊕ I} ⟶ K ⊗ L` factors through it. -/
theorem epi_koszulLift [Epi (evalMap L s)] : Epi (koszulLift L s) := by
  classical
  set K := kernel (evalMap L s)
  let q : K ⊗ (⨁ fun _ : I => 𝟙_ X.Modules) ⟶ ⨁ fun _ : I × I => 𝟙_ X.Modules :=
    ∑ j, (K ◁ biproduct.π (fun _ : I => 𝟙_ X.Modules) j) ≫ (ρ_ K).hom ≫
      kernel.ι (evalMap L s) ≫ columnMap j
  have hq : q ≫ koszulLift L s = K ◁ (evalMap L s ≫ (λ_ L).hom) := by
    have : Mono (kernel.ι (evalMap L s) ▷ L) := (levelComplex_shortExact L s 1).mono_f
    refine (cancel_mono (kernel.ι (evalMap L s) ▷ L)).1 ?_
    rw [Category.assoc, koszulLift_comp, Preadditive.sum_comp]
    have hcol : ∀ j, (ρ_ K).hom ≫ kernel.ι (evalMap L s) ≫ columnMap j ≫ koszulMap L s =
        (K ◁ (s j ≫ (λ_ L).hom)) ≫ (kernel.ι (evalMap L s) ▷ L) := by
      intro j
      rw [columnMap_comp_koszulMap, Preadditive.comp_sub, Preadditive.comp_sub,
        kernel.condition_assoc, zero_comp, comp_zero, sub_zero, rightUnitor_inv_naturality_assoc,
        Iso.hom_inv_id_assoc, whisker_exchange]
    simp only [Category.assoc, hcol]
    have hsum : ∑ j, (K ◁ biproduct.π (fun _ : I => 𝟙_ X.Modules) j) ≫
        (K ◁ (s j ≫ (λ_ L).hom)) = K ◁ (evalMap L s ≫ (λ_ L).hom) := by
      rw [evalMap, biproduct.desc_eq, Preadditive.sum_comp]
      change _ = (tensorLeft K).map _
      rw [Functor.map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = K ◁ _
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← hsum, Preadditive.sum_comp]
    simp only [Category.assoc]
  have : PreservesColimitsOfSize.{u, u} (tensorLeft K) :=
    Stacks.SheafInternalHom.preservesColimitsOfSize_tensorLeft X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) K
  have : Epi (K ◁ (evalMap L s ≫ (λ_ L).hom)) :=
    (tensorLeft K).map_epi (evalMap L s ≫ (λ_ L).hom)
  rw [← hq] at this
  exact epi_of_epi q (koszulLift L s)

end Koszul

/-! ### Cohomology -/

section Cohomology

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Cohomology over the field is an additive functor. -/
local instance additive_cohomologyOverFieldFunctorSRD (n : ℕ) :
    (cohomologyOverFieldFunctor k f n).Additive where
  map_add {M N a b} := by
    have := AlgebraicGeometry.evaluationAdditive X
    exact (congrArg (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
      (Functor.map_add ((_root_.SheafOfModules.evaluation X.ringCatSheaf
        (Opposite.op (⊤ : X.Opens))).rightDerived n))).trans
      (Functor.map_add (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom))

/-- `Hⁿ(ℱ₂) ⟶ Hⁿ(ℱ₃)` is onto when `Hⁿ⁺¹(ℱ₁) = 0`. -/
theorem surjective_cohomologyOverFieldMap_g {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n : ℕ) (h : IsZero (cohomologyOverField k f S.X₁ (n + 1))) :
    Function.Surjective (cohomologyOverFieldMap k f S.g n) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have := ModuleCat.subsingleton_of_isZero h
  exact fun b => (hgd n b).mp (Subsingleton.elim _ _)

/-- `Hⁿ(ℱ₃) = 0` when `Hⁿ(ℱ₂) = 0` and `Hⁿ⁺¹(ℱ₁) = 0`. -/
theorem isZero_cohomologyOverField_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n : ℕ) (h₂ : IsZero (cohomologyOverField k f S.X₂ n))
    (h₁ : IsZero (cohomologyOverField k f S.X₁ (n + 1))) :
    IsZero (cohomologyOverField k f S.X₃ n) := by
  have := ModuleCat.subsingleton_of_isZero h₂
  have : Subsingleton (cohomologyOverField k f S.X₃ n) :=
    (surjective_cohomologyOverFieldMap_g k f hS n h₁).subsingleton
  exact ModuleCat.isZero_of_subsingleton _

variable (L : X.Modules) [IsInvertibleModule X L] {I : Type} [Fintype I]
  (s : I → powSections L 1)

omit [IsInvertibleModule X L] in
/-- If `H¹(X, L ^⊗ m) = 0`, then `H¹` vanishes on the `m`-fold twist of `𝒪_X^{⊕ J}`. -/
theorem isZero_cohomologyOverField_twist_biproduct (m : ℕ)
    (hm : IsZero (cohomologyOverField k f (natTensorPow L m) 1)) (J : Type) [Finite J] :
    IsZero (cohomologyOverField k f ((twistFunctor L m).obj (⨁ fun _ : J => 𝟙_ X.Modules)) 1) :=
  isZero_obj_biproduct (twistFunctor L m ⋙ cohomologyOverFieldFunctor k f 1) _ fun _ =>
    hm.of_iso (cohomologyOverFieldIso k f (twistUnitIso L m) 1)

variable [Epi (evalMap L s)] (hH2 : ∀ M : X.Modules, IsZero (cohomologyOverField k f M 2))
  (h1 : IsZero (cohomologyOverField k f (natTensorPow L 1) 1))
include s hH2 h1

/-- **`H¹(X, L ^⊗ n) = 0` for every `n ≥ 1`.** -/
theorem isZero_cohomologyOverField_one_natTensorPow :
    ∀ n, 1 ≤ n → IsZero (cohomologyOverField k f (natTensorPow L n) 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h1
  | succ n hn ih =>
    have h := (isZero_cohomologyOverField_X₃ k f (levelComplex_shortExact L s n) 1
      (isZero_cohomologyOverField_twist_biproduct k f L n ih I) (hH2 _)).of_iso
      (cohomologyOverFieldIso k f (twistPowIso L 1 n) 1).symm
    rwa [Nat.add_comm] at h

/-- **`H¹(X, K ⊗ L ^⊗ (p + 1)) = 0` for every `p ≥ 1`**, `K` the kernel of the evaluation map. -/
theorem isZero_cohomologyOverField_one_levelComplex_X₁ (p : ℕ) (hp : 1 ≤ p) :
    IsZero (cohomologyOverField k f (levelComplex L s (p + 1)).X₁ 1) := by
  let E : (twistFunctor L p).obj (⨁ fun _ : I × I => 𝟙_ X.Modules) ⟶
      (levelComplex L s (p + 1)).X₁ :=
    (twistFunctor L p).map (koszulLift L s) ≫
      ((twistFunctorCommIso L p).app (kernel (evalMap L s))).hom
  have := epi_koszulLift L s
  have : Epi E := epi_comp' ((twistFunctor L p).map_epi _)
    (inferInstance : Epi ((twistFunctorCommIso L p).app (kernel (evalMap L s))).hom)
  exact isZero_cohomologyOverField_X₃ k f
    (S := ShortComplex.mk (kernel.ι E) E (kernel.condition E))
    { exact := ShortComplex.exact_kernel _ } 1
    (isZero_cohomologyOverField_twist_biproduct k f L p
      (isZero_cohomologyOverField_one_natTensorPow k f L s hH2 h1 p hp) (I × I)) (hH2 _)

/-- **Multiplication `Γ(L) ⊗ Γ(L ^⊗ m) ⟶ Γ(L ^⊗ (1 + m))` is onto for `m ≥ 2`**, through the
generating family `s`. -/
theorem exists_sum_mul_eq (m : ℕ) (hm : 2 ≤ m) (t : powSections L (1 + m)) :
    ∃ u : I → powSections L m, t = ∑ i, mul (s i) (u i) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  set S := levelComplex L s (p + 1)
  have hsurj := surjective_cohomologyOverFieldMap_g k f (levelComplex_shortExact L s (p + 1)) 0
    (isZero_cohomologyOverField_one_levelComplex_X₁ k f L s hH2 h1 p (by omega))
  set tt : 𝟙_ X.Modules ⟶ S.X₃ := t ≫ (twistPowIso L 1 (p + 1)).inv
  obtain ⟨b, hb⟩ := hsurj ((cohomologyOverFieldZeroEquivSections k f S.X₃).symm
    (Stacks.SectionProduct.globalSection X _ tt))
  set g : 𝟙_ X.Modules ⟶ S.X₂ := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    S.X₂).symm (cohomologyOverFieldZeroEquivSections k f S.X₂ b)
  have hg : g ≫ S.g = tt := by
    apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X S.X₃).injective
    change Stacks.SectionProduct.globalSection X _ (g ≫ S.g) =
      Stacks.SectionProduct.globalSection X _ tt
    rw [Stacks.SectionProduct.globalSection_comp]
    change S.g.app ⊤ ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X S.X₂)
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X S.X₂).symm _)) = _
    rw [AddEquiv.apply_symm_apply, ← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap,
      hb, Equiv.apply_symm_apply]
  refine ⟨fun i => g ≫ (twistFunctor L (p + 1)).map (biproduct.π _ i) ≫
    (twistUnitIso L (p + 1)).hom, ?_⟩
  have hstep : ∀ i, mul (s i) (g ≫ (twistFunctor L (p + 1)).map (biproduct.π _ i) ≫
      (twistUnitIso L (p + 1)).hom) = g ≫ (twistFunctor L (p + 1)).map (biproduct.π _ i ≫ s i) ≫
        (twistPowIso L 1 (p + 1)).hom := by
    intro i
    rw [mul_def]
    simp only [Category.assoc]
    rw [← twistFunctor_map_comp_twistPowIso, Functor.map_comp, Category.assoc]
  simp only [hstep]
  rw [show (∑ x, g ≫ (twistFunctor L (p + 1)).map
      (biproduct.π (fun _ : I => 𝟙_ X.Modules) x ≫ s x) ≫
      (twistPowIso L 1 (p + 1)).hom) = g ≫ (twistFunctor L (p + 1)).map
        (∑ x, biproduct.π (fun _ : I => 𝟙_ X.Modules) x ≫ s x) ≫ (twistPowIso L 1 (p + 1)).hom by
    rw [Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum], ← biproduct.desc_eq]
  change t = (g ≫ S.g) ≫ (twistPowIso L 1 (p + 1)).hom
  rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Cohomology

/-! ### A finite generating family -/

section Generation

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **A globally generated invertible module on a quasi-compact scheme is a quotient of a finite
free module through finitely many of its global sections.** -/
theorem exists_epi_evalMap [CompactSpace X]
    (hgg : _root_.SheafOfModules.IsGeneratedByGlobalSections L) :
    ∃ (r : ℕ) (s : Fin r → powSections L 1), Epi (evalMap L s) := by
  obtain ⟨σ₀⟩ := hgg
  obtain ⟨σ, hfin⟩ := Stacks.AmpleEventualGeneration.isFinGen_of_generatingSections
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule L) σ₀
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin σ.I
  let π : (∐ fun _ : σ.I => unitModule X) ⟶ L :=
    (σ.π : Stacks.AmpleGlobalGeneration.freeModule X σ.I ⟶ L)
  let u := Stacks.AmpleGlobalGeneration.unitModuleIsoUnit X
  let sec : Fin r → powSections L 1 := fun i =>
    u.inv ≫ Sigma.ι (fun _ : σ.I => unitModule X) (e.symm i) ≫ π ≫ (λ_ L).inv
  refine ⟨r, sec, ?_⟩
  let Φ : (∐ fun _ : σ.I => unitModule X) ⟶ ⨁ fun _ : Fin r => 𝟙_ X.Modules :=
    Sigma.desc fun i => u.hom ≫ biproduct.ι (fun _ : Fin r => 𝟙_ X.Modules) (e i)
  have hΦ : Φ ≫ evalMap L sec = π ≫ (λ_ L).inv := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_comp_desc_assoc, Category.assoc, evalMap, biproduct.ι_desc]
    simp only [sec, Iso.hom_inv_id_assoc, Equiv.symm_apply_apply]
  have : Epi (Φ ≫ evalMap L sec) := by
    rw [hΦ]
    exact epi_comp' σ.epi inferInstance
  exact epi_of_epi Φ (evalMap L sec)

end Generation

/-! ### The section ring is generated in degrees one and two -/

section Graded

/-- Left multiplication by `a` maps the additive closure of `S` into that of `T` as soon as it
maps `S` into it. -/
private theorem mul_mem_closure_of_forall_mem {A : Type*} [NonUnitalNonAssocSemiring A]
    {S T : Set A} (a : A) {x : A} (hx : x ∈ AddSubmonoid.closure S)
    (h : ∀ y ∈ S, a * y ∈ AddSubmonoid.closure T) : a * x ∈ AddSubmonoid.closure T := by
  induction hx using AddSubmonoid.closure_induction with
  | zero => simp
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact add_mem hy hz
  | mem y hy => exact h y hy

/-- **Generation in degrees one and two makes the second Veronese generated in degree one.** If
every homogeneous element of degree `m + 1 ≥ 3` of a graded ring is a sum of products of an
element of degree one and an element of degree `m`, then every `S_{2n}` with `n ≥ 1` is the span
of the `n`-fold products of elements of `S_2`. -/
theorem veroneseGeneratedInDegOne_two_of_mul {A : Type*} [CommRing A] {σ : Type*}
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (h : ∀ m, 2 ≤ m → ∀ x ∈ 𝒜 (m + 1),
      x ∈ AddSubmonoid.closure {y | ∃ a ∈ 𝒜 1, ∃ b ∈ 𝒜 m, y = a * b}) :
    Stacks.Veronese.VeroneseGeneratedInDegOne 𝒜 2 := by
  have key : ∀ n, 1 ≤ n → ∀ x ∈ 𝒜 (n * 2),
      x ∈ AddSubmonoid.closure (Stacks.Veronese.degOneProducts 𝒜 2 n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro x hx
      refine AddSubmonoid.subset_closure ⟨fun _ => x, fun _ => by simpa using hx, ?_⟩
      simp
    | succ n hn ih =>
      intro x hx
      rw [show (n + 1) * 2 = (n * 2 + 1) + 1 by omega] at hx
      have hx' := h (n * 2 + 1) (by omega) x hx
      clear hx
      refine AddSubmonoid.closure_le.2 (fun y hy => ?_) hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      refine mul_mem_closure_of_forall_mem a (h (n * 2) (by omega) b hb) fun y hy => ?_
      obtain ⟨c, hc, d, hd, rfl⟩ := hy
      rw [← mul_assoc]
      refine mul_mem_closure_of_forall_mem (a * c) (ih d hd) fun y hy => ?_
      obtain ⟨g, hg, rfl⟩ := hy
      refine AddSubmonoid.subset_closure ⟨Fin.cons (a * c) g, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using SetLike.mul_mem_graded ha hc
        · simpa using hg j
      · rw [Fin.prod_cons]
  intro n hn
  refine Set.Subset.antisymm (fun x hx => ?_) (Stacks.Veronese.span_degOneProducts_subset 𝒜 2 n)
  have hle : AddSubmonoid.closure (Stacks.Veronese.degOneProducts 𝒜 2 n) ≤
      (Submodule.span (Stacks.Veronese.gradeZero 𝒜)
        (Stacks.Veronese.degOneProducts 𝒜 2 n)).toAddSubmonoid :=
    AddSubmonoid.closure_le.2 Submodule.subset_span
  exact hle (key n hn x hx)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The section ring is generated by its degree-one part over degree two**: under the
hypotheses of `exists_sum_mul_eq`, every homogeneous element of `Γ_*(X, L)` of degree `m + 1`
with `m ≥ 2` is a sum of products of an element of degree one and one of degree `m`. -/
theorem mem_closure_mul_of_cohomology (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    {I : Type} [Fintype I] (s : I → powSections L 1) [Epi (evalMap L s)]
    (hH2 : ∀ M : X.Modules, IsZero (cohomologyOverField k f M 2))
    (h1 : IsZero (cohomologyOverField k f (natTensorPow L 1) 1)) (m : ℕ) (hm : 2 ≤ m)
    (x : sectionRing L) (hx : x ∈ grading L (m + 1)) :
    x ∈ AddSubmonoid.closure {y | ∃ a ∈ grading L 1, ∃ b ∈ grading L m, y = a * b} := by
  obtain ⟨t, rfl⟩ := (Stacks.ExternalGrading.mem_summand_iff).1 hx
  obtain ⟨v, hv⟩ := exists_sum_mul_eq k f L s hH2 h1 m hm
    (t ≫ eqToHom (congrArg (natTensorPow L) (Nat.add_comm m 1)))
  have hof : DirectSum.of (powSections L) (m + 1) t = DirectSum.of (powSections L) (1 + m)
      (t ≫ eqToHom (congrArg (natTensorPow L) (Nat.add_comm m 1))) :=
    DirectSum.of_eq_of_gradedMonoid_eq (mk_eq (Nat.add_comm m 1) t)
  rw [hof, hv, map_sum]
  refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.subset_closure ?_
  refine ⟨DirectSum.of _ 1 (s i), Stacks.ExternalGrading.of_mem_summand _ _,
    DirectSum.of _ m (v i), Stacks.ExternalGrading.of_mem_summand _ _, ?_⟩
  rw [DirectSum.of_mul_of]
  rfl

/-- **The second Veronese of the section ring of a globally generated invertible module with
`H¹(X, L) = 0` on a proper curve is generated in degree one.** Let `f : X ⟶ Spec k` be proper with
`X` of dimension at most one, and `L` an invertible `𝒪_X`-module which is globally generated
with `H¹(X, L) = 0`. Then the section ring `S = Γ_*(X, L)` is generated over `S₀` in degrees one
and two, and hence `S^{(2)} = ⨁_n S_{2n}` is generated in degree one.

This is the algebraic content of the proof of [Stacks, Tag 0E8W]. The source reaches the
surjectivity of `Γ(L) ⊗ Γ(L ^⊗ m) ⟶ Γ(L ^⊗ (m + 1))` for `m ≥ 2` through a regular section
after extending the ground field to an algebraically closed one; here it comes, over the given
field, from the Koszul complex of the surjection `𝒪_X^{⊕ r} ⟶ L` given by finitely many
generating global sections, together with the vanishing of `H²` on a one-dimensional scheme. -/
theorem veroneseGeneratedInDegOne_two (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hgg : _root_.SheafOfModules.IsGeneratedByGlobalSections L)
    (hH1 : IsZero (cohomologyOverField k f L 1)) :
    Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) 2 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨r, s, hs⟩ := exists_epi_evalMap L hgg
  have hH2 : ∀ M : X.Modules, IsZero (cohomologyOverField k f M 2) := fun M =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f M (d := 1) (by simpa using hdim)
      (by omega)
  exact veroneseGeneratedInDegOne_two_of_mul (grading L) fun m hm x hx =>
    mem_closure_mul_of_cohomology L k f s hH2 (hH1.of_iso (cohomologyOverFieldIso k f (λ_ L) 1))
      m hm x hx

end Graded

end Stacks.Curves.SectionRingDegreeTwo

end
