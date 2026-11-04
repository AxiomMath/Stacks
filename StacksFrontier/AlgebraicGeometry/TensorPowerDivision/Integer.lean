module

public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.MonoidalMul
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleReduction.Basic

/-!
# Dividing a section of `L ^⊗ (k + n)` by a nonvanishing section of `L ^⊗ k`, in integer degree

For an invertible module `L` and a global section `t` of the integer tensor power `L ^⊗ k`
(`Stacks.AmpleProjectiveImmersion.tensorPowerModule`, `k : ℤ`), multiplication by `t`,

`Γ(L ^⊗ n, U) ⟶ Γ(L ^⊗ (k + n), U)`,

is bijective for every `n : ℤ` and every open `U` inside the nonvanishing open of `t`. Its inverse
is the quotient `a ↦ a / t`, and the cancellation `(u · a) / (u · t) = a / t` holds.

## Main definitions

* `Stacks.TensorPowerDivision.intMulMap`: multiplication by a section of `L ^⊗ k` read as a
  morphism out of the monoidal unit, as a morphism `L ^⊗ n ⟶ L ^⊗ (k + n)` of `𝒪_X`-modules.
* `Stacks.TensorPowerDivision.intSecOf`: a global section of `L ^⊗ k`, read as a morphism out of
  the monoidal unit.
* `Stacks.TensorPowerDivision.intMulLinear` and `Stacks.TensorPowerDivision.intMulEquiv`:
  multiplication by a global section `t` of `L ^⊗ k`, as a `Γ(X, U)`-linear map and — for `U`
  inside the nonvanishing open of `t` — as a linear equivalence.
* `Stacks.TensorPowerDivision.intMulSections`: the product of two global sections of tensor
  powers, a global section of `L ^⊗ (k + n)`.
* `Stacks.TensorPowerDivision.intDivOf` and `Stacks.TensorPowerDivision.intDivTop`: the quotient
  `a / t` of a section of `L ^⊗ (k + n)` over `U ≤ V`, and of a *global* section, by `t`.

## Main results

* `Stacks.TensorPowerDivision.bijective_app_intMulMap`: multiplication by a nonvanishing global
  section of `L ^⊗ k` is a bijection `Γ(L ^⊗ n, U) → Γ(L ^⊗ (k + n), U)` for all `k n : ℤ` and
  every `U` inside the nonvanishing open.
* `Stacks.TensorPowerDivision.mul_intDivOf` and
  `Stacks.TensorPowerDivision.intDivOf_eq_of_mul_eq`: the defining identity `(a / t) · t = a` and
  its uniqueness; `Stacks.TensorPowerDivision.existsUnique_intMul_eq` is the two together.
* `Stacks.TensorPowerDivision.intDivOf_add` and `Stacks.TensorPowerDivision.intDivOf_smul`: the
  quotient is `Γ(X, U)`-linear in the numerator.
* `Stacks.TensorPowerDivision.map_intDivOf` and `Stacks.TensorPowerDivision.map_intDivTop`: the
  quotient commutes with restriction to a smaller open.
* `Stacks.TensorPowerDivision.intDivTop_intMulSections`: `(t · b) / t = b|_V`.
* `Stacks.TensorPowerDivision.intMulMap_comp` and
  `Stacks.TensorPowerDivision.intMulMap_intMulSections`: multiplication by a product of two
  sections is multiplication by each in turn, up to the transport `m + (k + n) = m + k + n`.
* `Stacks.TensorPowerDivision.intMulIso_assoc`: associativity of the multiplication, read at the
  scheme spelling.
* `Stacks.TensorPowerDivision.intDivTop_intMulSections_cancel`: the cancellation
  `(u · a) / (u · t) = a / t`, for `u` a further global section of a tensor power.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SectionProduct (globalSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.TensorPowerDivision

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-! ### Multiplication by a section of an integer tensor power -/

section Mul

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The coherent multiplication `L ^⊗ k ⊗ L ^⊗ n ≅ L ^⊗ (k + n)` of the integer tensor powers, at
the scheme spelling: `Stacks.SheafOfModules.TensorPower.monoidalMulIso` at the structure sheaf of
`X`. -/
def intMulIso (k n : ℤ) :
    tensorPowerModule X L k ⊗ tensorPowerModule X L n ≅ tensorPowerModule X L (k + n) :=
  Stacks.SheafOfModules.TensorPower.monoidalMulIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L k n

/-- Reindexing the integer tensor powers along an equality of degrees, at the scheme spelling. -/
def intPowReindex {a b : ℤ} (h : a = b) :
    tensorPowerModule X L a ≅ tensorPowerModule X L b :=
  haveI := Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  Stacks.SheafOfModules.TensorPower.tensorPowerReindex X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L h

/-- Associativity of the multiplication `intMulIso`, in every integer degree. -/
theorem intMulIso_assoc (a b c : ℤ) :
    (intMulIso L a b).hom ▷ tensorPowerModule X L c ≫ (intMulIso L (a + b) c).hom =
      (α_ (tensorPowerModule X L a) (tensorPowerModule X L b)
          (tensorPowerModule X L c)).hom ≫
        tensorPowerModule X L a ◁ (intMulIso L b c).hom ≫
          (intMulIso L a (b + c)).hom ≫ (intPowReindex L (Int.add_assoc a b c).symm).hom :=
  Stacks.SheafOfModules.TensorPower.monoidalMulIso_assoc X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L a b c

/-- Multiplication by a section of `L ^⊗ k` read as a morphism out of the monoidal unit, as a
morphism `L ^⊗ n ⟶ L ^⊗ (k + n)`: the left unitor, then `τ` whiskered on the right by `L ^⊗ n`,
then the multiplication. -/
def intMulMap {k : ℤ} (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k) (n : ℤ) :
    tensorPowerModule X L n ⟶ tensorPowerModule X L (k + n) :=
  (λ_ (tensorPowerModule X L n)).inv ≫
    (τ ▷ tensorPowerModule X L n) ≫ (intMulIso L k n).hom

/-- Multiplying by a product of two sections is multiplying by each in turn, up to the transport
`m + (k + n) = m + k + n`, the product of `σ` and `τ` being `τ` followed by multiplication by
`σ`. -/
theorem intMulMap_comp {m k : ℤ} (σ : 𝟙_ X.Modules ⟶ tensorPowerModule X L m)
    (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k) (n : ℤ) :
    intMulMap L (τ ≫ intMulMap L σ k) n
      = intMulMap L τ n ≫ intMulMap L σ (k + n) ≫
          (intPowReindex L (Int.add_assoc m k n).symm).hom := by
  simp only [intMulMap, comp_whiskerRight, Category.assoc]
  slice_lhs 5 6 => rw [intMulIso_assoc]
  slice_lhs 4 5 => rw [associator_naturality_left]
  slice_lhs 3 4 => rw [← leftUnitor_tensor_inv]
  slice_lhs 4 5 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [← leftUnitor_inv_naturality]
  simp only [Category.assoc]

/-- Multiplication by a nonvanishing global section of `L ^⊗ k` is a bijection from the sections of
`L ^⊗ n` to those of `L ^⊗ (k + n)`, over every open inside the nonvanishing open, for all integers
`k` and `n`. -/
theorem bijective_app_intMulMap {k : ℤ} (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k)
    {W : X.Opens}
    (hW : W ≤ nonvanishingOpen X (tensorPowerModule X L k) (globalSection X _ τ))
    (n : ℤ) {U : X.Opens} (hU : U ≤ W) :
    Function.Bijective ((intMulMap L τ n).app U) := by
  rw [intMulMap]
  exact ((bijective_app_of_isIso (intMulIso L k n).hom U).comp
    (bijective_app_of_bijStalk (τ ▷ tensorPowerModule X L n)
      (fun _ hy ↦ bijStalk_whiskerRight τ (tensorPowerModule X L n) hy
        fun _ h ↦ bijective_app_of_le_nonvanishingOpen _ τ hW h) hU)).comp
    (bijective_app_of_isIso (λ_ (tensorPowerModule X L n)).inv U)

end Mul

/-! ### Division across degrees -/

section Division

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {k : ℤ}
  (t : Γ(tensorPowerModule X L k, ⊤))

/-- A global section of an integer tensor power, read as a morphism out of the monoidal unit: the
inverse of `Stacks.SectionProduct.globalSection`. -/
def intSecOf : 𝟙_ X.Modules ⟶ tensorPowerModule X L k :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (tensorPowerModule X L k)).symm t

/-- The global section named by `intSecOf L t` is `t`. -/
@[simp] theorem globalSection_intSecOf :
    globalSection X (tensorPowerModule X L k) (intSecOf L t) = t :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (tensorPowerModule X L k)).apply_symm_apply t

/-- The morphism out of the unit attached to the global section named by `τ` is `τ`. -/
@[simp] theorem intSecOf_globalSection (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k) :
    intSecOf L (globalSection X (tensorPowerModule X L k) τ) = τ :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (tensorPowerModule X L k)).symm_apply_apply τ

/-- Multiplication by a global section `t` of `L ^⊗ k`, as a `Γ(X, U)`-linear map from the sections
of `L ^⊗ n` over `U` to those of `L ^⊗ (k + n)`. -/
def intMulLinear (n : ℤ) (U : X.Opens) :
    Γ(tensorPowerModule X L n, U) →ₗ[Γ(X, U)] Γ(tensorPowerModule X L (k + n), U) where
  toFun := (intMulMap L (intSecOf L t) n).app U
  map_add' := map_add _
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x

/-- `intMulLinear L t n U` applies `intMulMap L (intSecOf L t) n` to the sections over `U`. -/
@[simp] theorem intMulLinear_apply (n : ℤ) (U : X.Opens)
    (b : Γ(tensorPowerModule X L n, U)) :
    intMulLinear L t n U b = (intMulMap L (intSecOf L t) n).app U b := rfl

/-- The product of two global sections of integer tensor powers, a global section of
`L ^⊗ (k + n)`: multiplication by the first applied to the second. -/
def intMulSections {n : ℤ} (b : Γ(tensorPowerModule X L n, ⊤)) :
    Γ(tensorPowerModule X L (k + n), ⊤) :=
  (intMulMap L (intSecOf L t) n).app ⊤ b

/-- The morphism out of the unit attached to a product of two sections is the second followed by
multiplication by the first. -/
theorem intSecOf_intMulSections {n : ℤ} (b : Γ(tensorPowerModule X L n, ⊤)) :
    intSecOf L (intMulSections L t b) = intSecOf L b ≫ intMulMap L (intSecOf L t) n := by
  have h : intMulSections L t b
      = globalSection X _ (intSecOf L b ≫ intMulMap L (intSecOf L t) n) := by
    rw [Stacks.SectionProduct.globalSection_comp, globalSection_intSecOf]
    rfl
  rw [h, intSecOf_globalSection]

/-- Multiplication by a product of two sections is multiplication by each in turn, up to the
transport `m + (k + n) = m + k + n`. -/
theorem intMulMap_intMulSections {m : ℤ} (u : Γ(tensorPowerModule X L m, ⊤)) (n : ℤ) :
    intMulMap L (intSecOf L (intMulSections L u t)) n
      = intMulMap L (intSecOf L t) n ≫ intMulMap L (intSecOf L u) (k + n) ≫
          (intPowReindex L (Int.add_assoc m k n).symm).hom := by
  rw [intSecOf_intMulSections]
  exact intMulMap_comp L (intSecOf L u) (intSecOf L t) n

/-- On the restriction of a global section, multiplication by `t` is the product of global
sections, restricted. -/
theorem intMulLinear_resTop {n : ℤ} (b : Γ(tensorPowerModule X L n, ⊤)) (U : X.Opens) :
    intMulLinear L t n U (resTop (tensorPowerModule X L n) b U)
      = resTop (tensorPowerModule X L (k + n)) (intMulSections L t b) U :=
  (Stacks.TensorPowerTrivialize.resTop_app (intMulMap L (intSecOf L t) n) b U).symm

variable {V : X.Opens} (hV : V ≤ nonvanishingOpen X (tensorPowerModule X L k) t)

include hV in
/-- Multiplication by `t` is bijective on the sections over every open inside `V`. -/
theorem bijective_intMulLinear (n : ℤ) {U : X.Opens} (hU : U ≤ V) :
    Function.Bijective (intMulLinear L t n U) :=
  bijective_app_intMulMap L (intSecOf L t) (by rwa [globalSection_intSecOf]) n hU

/-- Multiplication by `t` as a linear equivalence `Γ(L ^⊗ n, U) ≃ₗ Γ(L ^⊗ (k + n), U)`, for `U`
inside the nonvanishing open of `t`. -/
def intMulEquiv (n : ℤ) {U : X.Opens} (hU : U ≤ V) :
    Γ(tensorPowerModule X L n, U) ≃ₗ[Γ(X, U)] Γ(tensorPowerModule X L (k + n), U) :=
  LinearEquiv.ofBijective (intMulLinear L t n U) (bijective_intMulLinear L t hV n hU)

/-- `intMulEquiv L t hV n hU` applies `intMulMap L (intSecOf L t) n` to the sections over `U`. -/
@[simp] theorem intMulEquiv_apply (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (b : Γ(tensorPowerModule X L n, U)) :
    intMulEquiv L t hV n hU b = (intMulMap L (intSecOf L t) n).app U b := rfl

/-- The quotient `a / t`: the unique section of `L ^⊗ n` over `U ≤ V` whose product with `t` is the
given section `a` of `L ^⊗ (k + n)`. -/
def intDivOf (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (a : Γ(tensorPowerModule X L (k + n), U)) : Γ(tensorPowerModule X L n, U) :=
  (intMulEquiv L t hV n hU).symm a

/-- The defining identity of the quotient: `(a / t) · t = a`. -/
theorem mul_intDivOf (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (a : Γ(tensorPowerModule X L (k + n), U)) :
    (intMulMap L (intSecOf L t) n).app U (intDivOf L t hV n hU a) = a :=
  (intMulEquiv L t hV n hU).apply_symm_apply a

/-- A section whose product with `t` is `a` is the quotient `a / t`. -/
theorem intDivOf_eq_of_mul_eq (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    {a : Γ(tensorPowerModule X L (k + n), U)} {b : Γ(tensorPowerModule X L n, U)}
    (h : (intMulMap L (intSecOf L t) n).app U b = a) : intDivOf L t hV n hU a = b := by
  subst h
  exact (intMulEquiv L t hV n hU).symm_apply_apply b

include hV in
/-- Existence and uniqueness of the quotient, in one statement. -/
theorem existsUnique_intMul_eq (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (a : Γ(tensorPowerModule X L (k + n), U)) :
    ∃! b : Γ(tensorPowerModule X L n, U), (intMulMap L (intSecOf L t) n).app U b = a :=
  (bijective_intMulLinear L t hV n hU).existsUnique a

/-- Dividing a product by its factor `t` returns the other factor. -/
theorem intDivOf_mul (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (b : Γ(tensorPowerModule X L n, U)) :
    intDivOf L t hV n hU ((intMulMap L (intSecOf L t) n).app U b) = b :=
  intDivOf_eq_of_mul_eq L t hV n hU rfl

/-- The quotient is additive in the numerator. -/
theorem intDivOf_add (n : ℤ) {U : X.Opens} (hU : U ≤ V)
    (a a' : Γ(tensorPowerModule X L (k + n), U)) :
    intDivOf L t hV n hU (a + a') = intDivOf L t hV n hU a + intDivOf L t hV n hU a' :=
  map_add (intMulEquiv L t hV n hU).symm a a'

/-- The quotient is `Γ(X, U)`-linear in the numerator. -/
theorem intDivOf_smul (n : ℤ) {U : X.Opens} (hU : U ≤ V) (r : Γ(X, U))
    (a : Γ(tensorPowerModule X L (k + n), U)) :
    intDivOf L t hV n hU (r • a) = r • intDivOf L t hV n hU a :=
  map_smul (intMulEquiv L t hV n hU).symm r a

/-- The quotient commutes with restriction to a smaller open. -/
theorem map_intDivOf (n : ℤ) {U U' : X.Opens} (hU : U ≤ V) (i : U' ⟶ U)
    (a : Γ(tensorPowerModule X L (k + n), U)) :
    (tensorPowerModule X L n).presheaf.map i.op (intDivOf L t hV n hU a)
      = intDivOf L t hV n (i.le.trans hU)
          ((tensorPowerModule X L (k + n)).presheaf.map i.op a) := by
  refine (intDivOf_eq_of_mul_eq L t hV n (i.le.trans hU) ?_).symm
  simpa [mul_intDivOf] using ConcreteCategory.congr_hom
    ((intMulMap L (intSecOf L t) n).mapPresheaf.naturality i.op) (intDivOf L t hV n hU a)

/-- The quotient of a global section by `t`, as a section of `L ^⊗ n` over `V`. -/
def intDivTop (n : ℤ) (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    Γ(tensorPowerModule X L n, V) :=
  intDivOf L t hV n le_rfl (resTop (tensorPowerModule X L (k + n)) a V)

/-- The defining identity of `intDivTop`: `(a / t) · t = a|_V`. -/
theorem mul_intDivTop (n : ℤ) (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    (intMulMap L (intSecOf L t) n).app V (intDivTop L t hV n a)
      = resTop (tensorPowerModule X L (k + n)) a V :=
  mul_intDivOf L t hV n le_rfl _

/-- `intDivTop` commutes with restriction. -/
theorem map_intDivTop (n : ℤ) {U : X.Opens} (i : U ⟶ V)
    (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    (tensorPowerModule X L n).presheaf.map i.op (intDivTop L t hV n a)
      = intDivOf L t hV n i.le (resTop (tensorPowerModule X L (k + n)) a U) := by
  rw [intDivTop, map_intDivOf]
  exact congrArg (intDivOf L t hV n i.le)
    (Stacks.TensorPowerTrivialize.res_resTop _ a i)

/-- `(t · b) / t = b|_V`, for `b` a global section of `L ^⊗ n`. -/
theorem intDivTop_intMulSections {n : ℤ} (b : Γ(tensorPowerModule X L n, ⊤)) :
    intDivTop L t hV n (intMulSections L t b) = resTop (tensorPowerModule X L n) b V :=
  intDivOf_eq_of_mul_eq L t hV n le_rfl (intMulLinear_resTop L t b V)

/-- The cancellation `(u · a) / (u · t) = a / t`, for `u` a global section of a further tensor
power whose product with `t` does not vanish on `V` either. -/
theorem intDivTop_intMulSections_cancel {m : ℤ} (u : Γ(tensorPowerModule X L m, ⊤))
    (hVu : V ≤ nonvanishingOpen X (tensorPowerModule X L (m + k)) (intMulSections L u t))
    (n : ℤ) (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    intDivTop L (intMulSections L u t) hVu n
        ((intPowReindex L (Int.add_assoc m k n).symm).hom.app ⊤ (intMulSections L u a))
      = intDivTop L t hV n a := by
  refine intDivOf_eq_of_mul_eq L (intMulSections L u t) hVu n le_rfl ?_
  rw [intMulMap_intMulSections, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, mul_intDivTop,
    ← Stacks.TensorPowerTrivialize.resTop_app, ← Stacks.TensorPowerTrivialize.resTop_app]
  rfl

end Division

end Stacks.TensorPowerDivision

end
