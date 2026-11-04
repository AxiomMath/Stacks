module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedSectionRingMap
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios

/-!
# The Weierstrass monomials in the section ring of an invertible module

For sections `s`, `x`, `y` of the tensor powers `L`, `L^{⊗2}`, `L^{⊗3}` of an invertible module,
the six monomials of degree six `s⁶, s⁴x, s³y, s²x², sxy, x³` and the square `y²`. When `s` is the
canonical section of `O(0)` on an elliptic curve and `x`, `y` have poles of exact orders `2` and
`3` along the zero section, the monomials are a basis of the degree-six sections, and the
expansion of `y²` in them is the Weierstrass equation.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.weierstrassMonomials`: the six monomials.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.ySq`: the square of `y`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections secOf)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.SectionProduct (globalSection)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

section Monomials

variable {Y : Scheme.{u}} (L : Y.Modules) (s : Γ(natTensorPow L 1, ⊤)) (x : Γ(natTensorPow L 2, ⊤))
  (y : Γ(natTensorPow L 3, ⊤))

/-- The square `s²` of a degree-one section. -/
def sq : Γ(natTensorPow L 2, ⊤) := mulSections L s s

/-- The cube `s³` of a degree-one section. -/
def cube : Γ(natTensorPow L 3, ⊤) := mulSections L (sq L s) s

/-- **The six Weierstrass monomials of degree six** in sections `s`, `x`, `y` of degrees `1`,
`2`, `3`: `s⁶, s⁴x, s³y, s²x², sxy, x³`, in this order. -/
def weierstrassMonomials : Fin 6 → Γ(natTensorPow L 6, ⊤) :=
  ![mulSections L (cube L s) (cube L s),
    mulSections L (mulSections L (cube L s) s) x,
    mulSections L (cube L s) y,
    mulSections L (sq L s) (mulSections L x x),
    mulSections L (mulSections L s x) y,
    mulSections L (mulSections L x x) x]

/-- The square `y²` of a degree-three section, in degree six. -/
def ySq : Γ(natTensorPow L 6, ⊤) := mulSections L y y

end Monomials


/-! ### Sections of tensor powers as homogeneous elements of the section ring -/

section SectionRing

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- The homogeneous element of degree `n` of the section ring `Γ_*(Y, L)` attached to a section
of `L^{⊗ n}`. -/
def toSectionRing (n : ℕ) (t : Γ(natTensorPow L n, ⊤)) : sectionRing L :=
  DirectSum.of (powSections L) n (secOf L t)

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The map `toSectionRing L n` from sections of `L^{⊗ n}` to the section ring is injective. -/
theorem toSectionRing_injective (n : ℕ) : Function.Injective (toSectionRing L n) := by
  intro a b h
  have h' := DirectSum.of_injective (β := powSections L) n h
  rw [← Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf L a,
    ← Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf L b, h']

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The product of sections is the product in the section ring. -/
theorem toSectionRing_mulSections {n m : ℕ} (a : Γ(natTensorPow L n, ⊤))
    (b : Γ(natTensorPow L m, ⊤)) :
    toSectionRing L (n + m) (mulSections L a b) = toSectionRing L n a * toSectionRing L m b := by
  have h := Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_globalSection L (secOf L a)
    (secOf L b)
  rw [Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf] at h
  rw [toSectionRing, toSectionRing, toSectionRing, h,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf_globalSection,
    Stacks.SectionProduct.of_mul_of]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The homogeneous element attached to a sum of sections is the sum of the elements. -/
theorem toSectionRing_add {n : ℕ} (a b : Γ(natTensorPow L n, ⊤)) :
    toSectionRing L n (a + b) = toSectionRing L n a + toSectionRing L n b := by
  rw [toSectionRing, toSectionRing, toSectionRing, ← map_add]
  congr 1
  exact (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y (natTensorPow L n)).symm.map_add
    a b

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- A scalar multiple of a section is its product with the scalar in degree zero. -/
theorem toSectionRing_smul {n : ℕ} (r : Γ(Y, ⊤)) (t : Γ(natTensorPow L n, ⊤)) :
    toSectionRing L n (r • t) =
      toSectionRing L n t *
        Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom L r := by
  have h1 : Stacks.SectionRingGeometric.unitScalar Y
      ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r) = r :=
    (Stacks.SectionRingGeometric.unitScalarEquiv Y).apply_symm_apply r
  have h2 : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y (natTensorPow L n)
      ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ secOf L t) = r • t := by
    rw [Stacks.SectionRingGeometric.globalSection_unitComp, h1]
    exact congrArg (fun z => r • z)
      (Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf L t)
  have hsec : secOf L (r • t) =
      (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ secOf L t := by
    rw [← h2]
    exact Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf_globalSection L _
  rw [toSectionRing, toSectionRing, hsec,
    Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom_apply,
    Stacks.SectionProduct.of_mul_of]
  rfl

/-- The element attached to the product of a section with itself is the square of its element. -/
private theorem toSectionRing_mulSections_self {Y : Scheme.{u}} (L : Y.Modules) {n : ℕ}
    (a : Γ(natTensorPow L n, ⊤)) :
    toSectionRing L (n + n) (mulSections L a a) = toSectionRing L n a ^ 2 := by
  rw [toSectionRing_mulSections, pow_two]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The element attached to the section `s²` of `L^{⊗ 2}` is the square of the element attached
to `s`. -/
theorem toSectionRing_sq (s : Γ(natTensorPow L 1, ⊤)) :
    toSectionRing L 2 (sq L s) = toSectionRing L 1 s ^ 2 := by
  exact toSectionRing_mulSections_self L s

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The element attached to the section `s³` of `L^{⊗ 3}` is the cube of the element attached
to `s`. -/
theorem toSectionRing_cube (s : Γ(natTensorPow L 1, ⊤)) :
    toSectionRing L 3 (cube L s) = toSectionRing L 1 s ^ 3 := by
  show toSectionRing L (2 + 1) (mulSections L (sq L s) s) = _
  rw [toSectionRing_mulSections, toSectionRing_sq, pow_succ _ 2]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The square of `y` in the section ring. -/
theorem toSectionRing_ySq (y : Γ(natTensorPow L 3, ⊤)) :
    toSectionRing L 6 (ySq L y) = toSectionRing L 3 y ^ 2 := by
  exact toSectionRing_mulSections_self L y

/-- **The Weierstrass monomials in the section ring** are the monomials `s⁶, s⁴x, s³y, s²x², sxy,
x³` in the homogeneous elements attached to `s`, `x` and `y`. -/
theorem toSectionRing_weierstrassMonomials (s : Γ(natTensorPow L 1, ⊤))
    (x : Γ(natTensorPow L 2, ⊤)) (y : Γ(natTensorPow L 3, ⊤)) :
    toSectionRing L 6 ∘ weierstrassMonomials L s x y =
      ![toSectionRing L 1 s ^ 6, toSectionRing L 1 s ^ 4 * toSectionRing L 2 x,
        toSectionRing L 1 s ^ 3 * toSectionRing L 3 y,
        toSectionRing L 1 s ^ 2 * toSectionRing L 2 x ^ 2,
        toSectionRing L 1 s * toSectionRing L 2 x * toSectionRing L 3 y,
        toSectionRing L 2 x ^ 3] := by
  funext i
  fin_cases i
  · show toSectionRing L (3 + 3) (mulSections L (cube L s) (cube L s)) = _
    rw [toSectionRing_mulSections, toSectionRing_cube]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    ring
  · show toSectionRing L ((3 + 1) + 2) (mulSections L (mulSections L (cube L s) s) x) = _
    rw [toSectionRing_mulSections, toSectionRing_mulSections, toSectionRing_cube]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · show toSectionRing L (3 + 3) (mulSections L (cube L s) y) = _
    rw [toSectionRing_mulSections, toSectionRing_cube]
    rfl
  · show toSectionRing L (2 + (2 + 2)) (mulSections L (sq L s) (mulSections L x x)) = _
    rw [toSectionRing_mulSections, toSectionRing_mulSections_self, toSectionRing_sq]
    rfl
  · show toSectionRing L ((1 + 2) + 3) (mulSections L (mulSections L s x) y) = _
    rw [toSectionRing_mulSections, toSectionRing_mulSections]
    rfl
  · show toSectionRing L ((2 + 2) + 2) (mulSections L (mulSections L x x) x) = _
    rw [toSectionRing_mulSections, toSectionRing_mulSections, ← pow_two, ← pow_succ]
    rfl

end SectionRing

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
