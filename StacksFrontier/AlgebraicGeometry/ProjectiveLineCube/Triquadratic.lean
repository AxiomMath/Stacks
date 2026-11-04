module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.Chart
public import StacksFrontier.AlgebraicGeometry.SectionDivision.TripleTensor
public import StacksFrontier.AlgebraicGeometry.SectionDivision.Pullback
public import StacksFrontier.AlgebraicGeometry.SectionDivision.Trivialization

/-!
# Triquadratic forms on a product of three projective lines

On `P = S × ℙ¹ × ℙ¹ × ℙ¹` let `𝓗ᵢ = prᵢ^*𝒪(1)` with coordinate sections `prᵢ^*T₀`, `prᵢ^*T₁`.
The module `𝓗ᵢ ⊗ 𝓗ᵢ` has the three quadratic monomials `m₀ = T₀ ⊗ T₀`, `m₁ = T₀ ⊗ T₁`,
`m₂ = T₁ ⊗ T₁`, so integer arrays `a : Fin 3 → Fin 3 → ℤ` give *biquadratic forms*
`∑ a i j · mᵢ ⊗ mⱼ`, global sections of `M = 𝓗₀² ⊗ 𝓗₁²`. Three of them, `A, B, C`, together with
the coordinates `z₀, z₁` of the third factor, give the *triquadratic form*

`F = A z₀² + B z₀ z₁ + C z₁²`,

a global section of `𝒪(2, 2, 2) = (M ⊗ 𝓗₂) ⊗ 𝓗₂`.

On the chart `V_c = ⋂ᵢ prᵢ⁻¹ D₊(T_{c i})` the frame `T_{c 0}² ⊗ T_{c 1}² ⊗ T_{c 2} ⊗ T_{c 2}`
does not vanish, and the ratio of `F` to it is the dehomogenization of `F`: if `a, b, c` are the
ratios of `A, B, C` to the frame `T_{c 0}² ⊗ T_{c 1}²` of `M` (themselves the dehomogenized
biquadratic polynomials in the first two chart coordinates `x₀, x₁`), the ratio of `F` is
`a x₂^{e₀} + b x₂^{e₁} + c x₂^{e₂}` with `e_k = k` if `c 2 = 0` and `e_k = 2 - k` if `c 2 = 1`.

## Main definitions

* `AlgebraicGeometry.projectiveLineCube.biquadraticModule`, `triquadraticModule`: `M` and
  `(M ⊗ 𝓗₂) ⊗ 𝓗₂`.
* `AlgebraicGeometry.projectiveLineCube.biquadraticSection a`: `∑ a i j · mᵢ ⊗ mⱼ`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSection A B C`: `A z₀² + B z₀ z₁ + C z₁²`.
* `AlgebraicGeometry.projectiveLineCube.chartFrame c`: the nonvanishing frame on `V_c`.
* `AlgebraicGeometry.projectiveLineCube.biquadraticChartPolynomial a c`: the dehomogenization of
  a biquadratic form on the chart `(c 0, c 1)`.

## Main results

* `AlgebraicGeometry.projectiveLineCube.divBySection_coordinate_chartOpen`: on `V_c` the ratio
  `prᵢ^*T_b / prᵢ^*T_{c i}` is `1` or the `i`-th chart coordinate.
* `AlgebraicGeometry.projectiveLineCube.divBySection_biquadraticSection`: the local equation of a
  biquadratic form is its dehomogenization.
* `AlgebraicGeometry.projectiveLineCube.divBySection_triquadraticSection`: **the local equation
  of `A z₀² + B z₀ z₁ + C z₁²` on `V_c`.**

## Implementation notes

The products of global sections in `triquadraticSection` are
`Stacks.SheafOfModules.tensorSectionsAt` over `⊤`, bracketed as `(A ⊗ zₐ) ⊗ z_b`; this is the
form in which a binary quadratic form with coefficients in `M` is evaluated at the point
`(z₀ : z₁)` of the third factor.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace projectiveLineCube

open cubeProduct Stacks.SheafOfModules

variable (S : Scheme.{u})

/-! ### The ratio of two coordinates -/

/-- The ratio `T_b / Tₐ` of two homogeneous coordinates of `ℙ¹_ℤ` on `D₊(Tₐ)`. -/
def lineRatio (a b : Fin 2) : Γ(projectiveSpaceAtUniverse.{u} 1, projectiveLineBasicOpen.{u} a) :=
  divBySection (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)
    (projectiveLineBasicOpen_le_nonvanishingOpen a)
    ((Segre.coordinateSection.{u} 1 b).eval (op (projectiveLineBasicOpen.{u} a)))

/-- The ratio `Tₐ / Tₐ` is `1`. -/
@[simp]
theorem lineRatio_self (a : Fin 2) : lineRatio.{u} a a = 1 :=
  divBySection_coordinateSection_self a

/-- The ratio of the other coordinate to `Tₐ` is the coordinate of the chart `D₊(Tₐ)`. -/
theorem lineRatio_rev (a : Fin 2) : lineRatio.{u} a a.rev = projectiveLineBasicOpenCoordinate a :=
  (projectiveLineBasicOpenCoordinate_eq_divBySection a).symm

/-- An open contained in `prᵢ⁻¹ D₊(Tₐ)` is contained in the nonvanishing locus of `prᵢ^*Tₐ`. -/
theorem le_nonvanishingOpen_coordinate {i : Fin 3} {a : Fin 2} {V : (projectiveLineCube S).Opens}
    (hV : V ≤ proj S _ i ⁻¹ᵁ projectiveLineBasicOpen.{u} a) :
    V ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i)
      (coordinate S i a) := by
  rwa [nonvanishingOpen_coordinate]

/-- **The ratio of two pulled-back coordinates is the pullback of their ratio.** -/
theorem divBySection_coordinate {i : Fin 3} (a b : Fin 2) {V : (projectiveLineCube S).Opens}
    (hV : V ≤ proj S _ i ⁻¹ᵁ projectiveLineBasicOpen.{u} a) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i) (coordinate S i a)
        (le_nonvanishingOpen_coordinate S hV) ((coordinate S i b).eval (op V)) =
      (proj S _ i).appLE (projectiveLineBasicOpen.{u} a) V hV (lineRatio a b) := by
  have hV' : V ≤ proj S _ i ⁻¹ᵁ nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) :=
    hV.trans fun x hx => projectiveLineBasicOpen_le_nonvanishingOpen a hx
  refine (divBySection_modulePullbackSection (proj S _ i)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)
    (Segre.coordinateSection.{u} 1 b) hV').trans ?_
  have h := projectiveLineBasicOpen_le_nonvanishingOpen.{u} a
  have h1 := map_divBySection (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) h le_rfl
    ((Segre.coordinateSection.{u} 1 b).eval (op (nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a))))
  have h2 := secRestr_sections_eval (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 b) h
  have h3 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.map_appLE (proj S _ i) hV (homOfLE h).op)) (divBySection
      (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) le_rfl
      ((Segre.coordinateSection.{u} 1 b).eval (op (nonvanishingOpen
        (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
        (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)))))
  refine h3.symm.trans ?_
  simp only [CommRingCat.comp_apply]
  rw [h1, h2]
  rfl

/-- On the chart `V_c`, the ratio `prᵢ^*T_b / prᵢ^*T_{c i}` is `1` for `b = c i` and the `i`-th
chart coordinate otherwise. -/
theorem divBySection_coordinate_chartOpen (c : Fin 3 → Fin 2) (i : Fin 3) (b : Fin 2) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i)
        (coordinate S i (c i)) (le_nonvanishingOpen_coordinate S (chartOpen_le S c i))
        ((coordinate S i b).eval (op (chartOpen S c))) =
      if b = c i then 1 else chartCoordinate S c i := by
  rw [divBySection_coordinate S (c i) b (chartOpen_le S c i)]
  split_ifs with h
  · subst h
    rw [lineRatio_self, map_one]
  · obtain rfl : b = (c i).rev := by
      revert h
      generalize c i = a
      fin_cases a <;> fin_cases b <;> simp
    rw [lineRatio_rev]
    rfl

/-- `divBySection_coordinate_chartOpen` with the denominator index given up to equality. -/
theorem divBySection_coordinate_chartOpen_of_eq (c : Fin 3 → Fin 2) (i : Fin 3) (a b : Fin 2)
    (ha : a = c i)
    (hV : chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (lineBundle S i) (coordinate S i a)) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i)
        (coordinate S i a) hV ((coordinate S i b).eval (op (chartOpen S c))) =
      if b = c i then 1 else chartCoordinate S c i := by
  subst ha
  exact divBySection_coordinate_chartOpen S c i b

/-! ### Quadratic monomials and triquadratic forms -/

/-- `𝓗ᵢ ⊗ 𝓗ᵢ`. -/
abbrev lineBundleSq (i : Fin 3) : (projectiveLineCube S).Modules :=
  Scheme.Modules.tensorObj (lineBundle S i) (lineBundle S i)

/-- `M = 𝓗₀² ⊗ 𝓗₁²`, the module of biquadratic forms in the first two factors. -/
abbrev biquadraticModule : (projectiveLineCube S).Modules :=
  Scheme.Modules.tensorObj (lineBundleSq S 0) (lineBundleSq S 1)

/-- `M ⊗ 𝓗₂`. -/
abbrev biquadraticLinearModule : (projectiveLineCube S).Modules :=
  Scheme.Modules.tensorObj (biquadraticModule S) (lineBundle S 2)

/-- `𝒪(2, 2, 2) = (M ⊗ 𝓗₂) ⊗ 𝓗₂`, the module of triquadratic forms. -/
abbrev triquadraticModule : (projectiveLineCube S).Modules :=
  Scheme.Modules.tensorObj (biquadraticLinearModule S) (lineBundle S 2)

/-- `𝓗ᵢ ⊗ 𝓗ᵢ` is invertible. -/
instance isInvertible_lineBundleSq (i : Fin 3) :
    IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (lineBundleSq S i) :=
  tensorProduct_isInvertible _ _ _ _

/-- `M = 𝓗₀² ⊗ 𝓗₁²` is invertible. -/
instance isInvertible_biquadraticModule :
    IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (biquadraticModule S) :=
  tensorProduct_isInvertible _ _ _ _

/-- `M ⊗ 𝓗₂` is invertible. -/
instance isInvertible_biquadraticLinearModule :
    IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property
      (biquadraticLinearModule S) :=
  tensorProduct_isInvertible _ _ _ _

/-- `𝒪(2, 2, 2) = (M ⊗ 𝓗₂) ⊗ 𝓗₂` is invertible. -/
instance isInvertible_triquadraticModule :
    IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (triquadraticModule S) :=
  tensorProduct_isInvertible _ _ _ _

/-- `𝒪(2, 2, 2)` is invertible as a sheaf of modules over the scheme `S × ℙ¹ × ℙ¹ × ℙ¹`. -/
instance isInvertible_triquadraticModule_algebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineCube S).sheaf.obj
      (projectiveLineCube S).ringCatSheaf.property (triquadraticModule S) :=
  (isInvertible_iff_algebraicGeometry _ _ _).mp (isInvertible_triquadraticModule S)

/-- The first coordinate index of the quadratic monomials `T₀T₀, T₀T₁, T₁T₁`. -/
def quadraticFirst : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The second coordinate index of the quadratic monomials `T₀T₀, T₀T₁, T₁T₁`. -/
def quadraticSecond : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The quadratic monomial `T₀T₀`, `T₀T₁` or `T₁T₁` (for `k = 0, 1, 2`) in the coordinates of
the `i`-th factor, a global section of `𝓗ᵢ ⊗ 𝓗ᵢ`. -/
def quadraticMonomial (i : Fin 3) (k : Fin 3) : (lineBundleSq S i).sections :=
  tensorSections (lineBundle S i) (lineBundle S i) (coordinate S i (quadraticFirst k))
    (coordinate S i (quadraticSecond k))

/-- The biquadratic monomial `m_i ⊗ m_j` in the first two factors, a global section of `M`. -/
def biquadraticMonomial (i j : Fin 3) : (biquadraticModule S).sections :=
  tensorSections (lineBundleSq S 0) (lineBundleSq S 1) (quadraticMonomial S 0 i)
    (quadraticMonomial S 1 j)

/-- The biquadratic form `∑ a i j · m_i ⊗ m_j` with integer coefficients, a global section of
`M = 𝓗₀² ⊗ 𝓗₁²`. -/
def biquadraticSection (a : Fin 3 → Fin 3 → ℤ) : Γ(biquadraticModule S, ⊤) :=
  ∑ i, ∑ j, a i j • (biquadraticMonomial S i j).eval (op ⊤)

/-- The `a`-th homogeneous coordinate `pr₂^*Tₐ` of the third factor, as an element of
`Γ(𝓗₂, ⊤)`. -/
abbrev thirdCoordinate (a : Fin 2) : Γ(lineBundle S 2, ⊤) := (coordinate S 2 a).eval (op ⊤)

/-- **The triquadratic form `A z₀² + B z₀ z₁ + C z₁²`** attached to three biquadratic forms
`A, B, C` (global sections of `M = 𝓗₀² ⊗ 𝓗₁²`), with `z₀, z₁` the coordinates of the third
factor: a global section of `𝒪(2, 2, 2) = (M ⊗ 𝓗₂) ⊗ 𝓗₂`. -/
def triquadraticSection (A B C : Γ(biquadraticModule S, ⊤)) : Γ(triquadraticModule S, ⊤) :=
  tensorSectionsAt (projectiveLineCube S).sheaf.obj (projectiveLineCube S).ringCatSheaf.property
      (op ⊤) _ _ (tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) _ _ A (thirdCoordinate S 0))
      (thirdCoordinate S 0) +
    tensorSectionsAt (projectiveLineCube S).sheaf.obj (projectiveLineCube S).ringCatSheaf.property
      (op ⊤) _ _ (tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) _ _ B (thirdCoordinate S 0))
      (thirdCoordinate S 1) +
    tensorSectionsAt (projectiveLineCube S).sheaf.obj (projectiveLineCube S).ringCatSheaf.property
      (op ⊤) _ _ (tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) _ _ C (thirdCoordinate S 1))
      (thirdCoordinate S 1)

/-! ### The local equation on a chart -/

/-- The index of the square `Tₐ ⊗ Tₐ` among the quadratic monomials. -/
def frameIndex : Fin 2 → Fin 3 := ![0, 2]

/-- The first coordinate index of the square `Tₐ ⊗ Tₐ` is `a`. -/
theorem quadraticFirst_frameIndex (a : Fin 2) : quadraticFirst (frameIndex a) = a := by
  fin_cases a <;> rfl

/-- The second coordinate index of the square `Tₐ ⊗ Tₐ` is `a`. -/
theorem quadraticSecond_frameIndex (a : Fin 2) : quadraticSecond (frameIndex a) = a := by
  fin_cases a <;> rfl

/-- The frame `T_{c 0}² ⊗ T_{c 1}²` of `M` on the chart `V_c`. -/
def biquadraticFrame (c : Fin 3 → Fin 2) : (biquadraticModule S).sections :=
  biquadraticMonomial S (frameIndex (c 0)) (frameIndex (c 1))

/-- The frame `(T_{c 0}² ⊗ T_{c 1}² ⊗ T_{c 2}) ⊗ T_{c 2}` of `𝒪(2, 2, 2)` on the chart `V_c`. -/
def chartFrame (c : Fin 3 → Fin 2) : (triquadraticModule S).sections :=
  tensorSections (biquadraticLinearModule S) (lineBundle S 2)
    (tensorSections (biquadraticModule S) (lineBundle S 2) (biquadraticFrame S c)
      (coordinate S 2 (c 2))) (coordinate S 2 (c 2))

/-- The coordinate `prᵢ^*Tₐ` does not vanish on the chart `V_c` when `a = c i`. -/
private theorem chartOpen_le_nonvanishingOpen_coordinate_of_eq (c : Fin 3 → Fin 2) (i : Fin 3)
    {a : Fin 2} (ha : a = c i) :
    chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (lineBundle S i) (coordinate S i a) := by
  subst ha
  exact le_nonvanishingOpen_coordinate S (chartOpen_le S c i)

/-- The square `T_{c i} ⊗ T_{c i}` does not vanish on the chart `V_c`. -/
theorem chartOpen_le_nonvanishingOpen_quadraticMonomial (c : Fin 3 → Fin 2) (i : Fin 3) :
    chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (lineBundleSq S i) (quadraticMonomial S i (frameIndex (c i))) :=
  le_nonvanishingOpen_tensorSections (lineBundle S i) (lineBundle S i) _ _
    (chartOpen_le_nonvanishingOpen_coordinate_of_eq S c i (quadraticFirst_frameIndex (c i)))
    (chartOpen_le_nonvanishingOpen_coordinate_of_eq S c i (quadraticSecond_frameIndex (c i)))

/-- The frame `T_{c 0}² ⊗ T_{c 1}²` of `M` does not vanish on the chart `V_c`. -/
theorem chartOpen_le_nonvanishingOpen_biquadraticFrame (c : Fin 3 → Fin 2) :
    chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (biquadraticModule S) (biquadraticFrame S c) :=
  le_nonvanishingOpen_tensorSections (lineBundleSq S 0) (lineBundleSq S 1) _ _
    (chartOpen_le_nonvanishingOpen_quadraticMonomial S c 0)
    (chartOpen_le_nonvanishingOpen_quadraticMonomial S c 1)

/-- The section `T_{c 0}² ⊗ T_{c 1}² ⊗ T_{c 2}` of `M ⊗ 𝓗₂` does not vanish on the chart `V_c`. -/
theorem chartOpen_le_nonvanishingOpen_biquadraticLinearFrame (c : Fin 3 → Fin 2) :
    chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (biquadraticLinearModule S) (tensorSections (biquadraticModule S) (lineBundle S 2)
        (biquadraticFrame S c) (coordinate S 2 (c 2))) :=
  le_nonvanishingOpen_tensorSections (biquadraticModule S) (lineBundle S 2) _ _
    (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
    (le_nonvanishingOpen_coordinate S (chartOpen_le S c 2))

/-- **The frame does not vanish on its chart.** -/
theorem chartOpen_le_nonvanishingOpen_chartFrame (c : Fin 3 → Fin 2) :
    chartOpen S c ≤ nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
      (triquadraticModule S) (chartFrame S c) :=
  le_nonvanishingOpen_tensorSections (biquadraticLinearModule S) (lineBundle S 2) _ _
    (chartOpen_le_nonvanishingOpen_biquadraticLinearFrame S c)
    (le_nonvanishingOpen_coordinate S (chartOpen_le S c 2))

/-- The exponent of the chart coordinate in the dehomogenization of the quadratic monomial `k`
on the chart `D₊(Tₐ)`: `k` if `a = 0` and `2 - k` if `a = 1`. -/
def dehomExponent (a : Fin 2) (k : Fin 3) : ℕ := if a = 0 then k else 2 - k

/-- The product of the two factors, each `1` or `x` according as the corresponding coordinate
index of the quadratic monomial `k` is `a`, is `x ^ dehomExponent a k`. -/
theorem ite_mul_ite_eq_pow_dehomExponent {A : Type*} [Monoid A] (x : A) (a : Fin 2) (k : Fin 3) :
    ((if quadraticFirst k = a then 1 else x) * if quadraticSecond k = a then 1 else x) =
      x ^ dehomExponent a k := by
  fin_cases a <;> fin_cases k <;> simp [quadraticFirst, quadraticSecond, dehomExponent, pow_two]

/-- **The ratio of a quadratic monomial to the square of the chart coordinate.** -/
theorem divBySection_quadraticMonomial (c : Fin 3 → Fin 2) (i k : Fin 3) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (lineBundleSq S i)
        (quadraticMonomial S i (frameIndex (c i)))
        (chartOpen_le_nonvanishingOpen_quadraticMonomial S c i)
        ((quadraticMonomial S i k).eval (op (chartOpen S c))) =
      chartCoordinate S c i ^ dehomExponent (c i) k := by
  refine (divBySection_tensorSections (lineBundle S i) (lineBundle S i) _ _ _ _
    (chartOpen_le_nonvanishingOpen_coordinate_of_eq S c i (quadraticFirst_frameIndex _))
    (chartOpen_le_nonvanishingOpen_coordinate_of_eq S c i (quadraticSecond_frameIndex _))).trans ?_
  rw [divBySection_coordinate_chartOpen_of_eq S c i _ _ (quadraticFirst_frameIndex (c i)),
    divBySection_coordinate_chartOpen_of_eq S c i _ _ (quadraticSecond_frameIndex (c i))]
  exact ite_mul_ite_eq_pow_dehomExponent _ _ _

/-- The ratio of a biquadratic monomial to the frame of `M`. -/
theorem divBySection_biquadraticMonomial (c : Fin 3 → Fin 2) (i j : Fin 3) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
        (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
        ((biquadraticMonomial S i j).eval (op (chartOpen S c))) =
      chartCoordinate S c 0 ^ dehomExponent (c 0) i *
        chartCoordinate S c 1 ^ dehomExponent (c 1) j := by
  refine (divBySection_tensorSections (lineBundleSq S 0) (lineBundleSq S 1) _ _ _ _
    (chartOpen_le_nonvanishingOpen_quadraticMonomial S c 0)
    (chartOpen_le_nonvanishingOpen_quadraticMonomial S c 1)).trans ?_
  rw [divBySection_quadraticMonomial, divBySection_quadraticMonomial]

/-- The dehomogenization of the biquadratic form with coefficients `a` on the chart `(c₀, c₁)`
of `ℙ¹ × ℙ¹`: the integer polynomial `∑ a i j x₀^{e(c₀, i)} x₁^{e(c₁, j)}` in the first two of
three variables. -/
def biquadraticChartPolynomial (a : Fin 3 → Fin 3 → ℤ) (c : Fin 3 → Fin 2) :
    MvPolynomial (Fin 3) ℤ :=
  ∑ i, ∑ j, MvPolynomial.C (a i j) * (MvPolynomial.X 0 ^ dehomExponent (c 0) i *
    MvPolynomial.X 1 ^ dehomExponent (c 1) j)

/-- **The local equation of a biquadratic form on a chart is its dehomogenization.** -/
theorem divBySection_biquadraticSection (a : Fin 3 → Fin 3 → ℤ) (c : Fin 3 → Fin 2) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
        (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
        ((biquadraticModule S).presheaf.map (homOfLE le_top).op (biquadraticSection S a)) =
      MvPolynomial.eval₂ (Int.castRingHom _) (chartCoordinate S c)
        (biquadraticChartPolynomial a c) := by
  have hres : (biquadraticModule S).presheaf.map (homOfLE le_top).op (biquadraticSection S a) =
      ∑ i, ∑ j, a i j • (biquadraticMonomial S i j).eval (op (chartOpen S c)) :=
    (map_sum (ConcreteCategory.hom ((biquadraticModule S).presheaf.map
      (homOfLE le_top).op)) _ _).trans (Finset.sum_congr rfl fun i _ =>
        (map_sum (ConcreteCategory.hom ((biquadraticModule S).presheaf.map
          (homOfLE le_top).op)) _ _).trans (Finset.sum_congr rfl fun j _ =>
        (map_zsmul (ConcreteCategory.hom ((biquadraticModule S).presheaf.map
          (homOfLE le_top).op)) _ _).trans
          (congrArg _ (PresheafOfModules.sections_property (biquadraticMonomial S i j)
            (homOfLE le_top).op))))
  rw [hres]
  refine (divBySection_sum (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
    (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c) _
    Finset.univ).trans ?_
  simp only [biquadraticChartPolynomial, MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (divBySection_sum (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
    (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c) _
    Finset.univ).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (divBySection_zsmul (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
    (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c) (a i j)
    _).trans ?_
  rw [zsmul_eq_mul, divBySection_biquadraticMonomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C]
  simp [MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]

/-- The ratio of `m ⊗ z_α ⊗ z_β` to the frame `(T_{c 0}² ⊗ T_{c 1}² ⊗ T_{c 2}) ⊗ T_{c 2}`. -/
theorem divBySection_tensorSectionsAt_chartFrame (c : Fin 3 → Fin 2)
    (m : Γ(biquadraticModule S, chartOpen S c)) (α β : Fin 2) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (triquadraticModule S)
        (chartFrame S c) (chartOpen_le_nonvanishingOpen_chartFrame S c)
        (tensorSectionsAt (projectiveLineCube S).sheaf.obj
          (projectiveLineCube S).ringCatSheaf.property (op (chartOpen S c)) _ _
          (tensorSectionsAt (projectiveLineCube S).sheaf.obj
            (projectiveLineCube S).ringCatSheaf.property (op (chartOpen S c)) _ _ m
            ((coordinate S 2 α).eval (op (chartOpen S c))))
          ((coordinate S 2 β).eval (op (chartOpen S c)))) =
      divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
          (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c) m *
        ((if α = c 2 then 1 else chartCoordinate S c 2) *
          if β = c 2 then 1 else chartCoordinate S c 2) := by
  refine (divBySection_tensorSectionsAt (biquadraticLinearModule S) (lineBundle S 2) _ _
    (chartOpen_le_nonvanishingOpen_biquadraticLinearFrame S c)
    (le_nonvanishingOpen_coordinate S (chartOpen_le S c 2)) _ _).trans ?_
  refine (congrArg₂ (· * ·) (divBySection_tensorSectionsAt (biquadraticModule S) (lineBundle S 2)
    _ _ (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
    (le_nonvanishingOpen_coordinate S (chartOpen_le S c 2)) m _)
    (divBySection_coordinate_chartOpen S c 2 β)).trans ?_
  rw [divBySection_coordinate_chartOpen S c 2 α, mul_assoc]

/-- **The local equation of `A z₀² + B z₀ z₁ + C z₁²` on a chart**: on `V_c` its ratio to the
frame is `a + b x₂^{e(c₂, 1)} + c x₂^{e(c₂, 2)}` read in the chart coordinate `x₂` of the third
factor, where `a, b, c` are the ratios of `A, B, C` to the frame of `M` (and the exponent of
`x₂` in front of `a` is `e(c₂, 0)`). -/
theorem divBySection_triquadraticSection (A B C : Γ(biquadraticModule S, ⊤))
    (c : Fin 3 → Fin 2) :
    divBySection (X := (projectiveLineCube S).toRingedSpace) (triquadraticModule S)
        (chartFrame S c) (chartOpen_le_nonvanishingOpen_chartFrame S c)
        ((triquadraticModule S).presheaf.map (homOfLE le_top).op
          (triquadraticSection S A B C)) =
      divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
          (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
          ((biquadraticModule S).presheaf.map (homOfLE le_top).op A) *
          chartCoordinate S c 2 ^ dehomExponent (c 2) 0 +
        divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
          (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
          ((biquadraticModule S).presheaf.map (homOfLE le_top).op B) *
          chartCoordinate S c 2 ^ dehomExponent (c 2) 1 +
        divBySection (X := (projectiveLineCube S).toRingedSpace) (biquadraticModule S)
          (biquadraticFrame S c) (chartOpen_le_nonvanishingOpen_biquadraticFrame S c)
          ((biquadraticModule S).presheaf.map (homOfLE le_top).op C) *
          chartCoordinate S c 2 ^ dehomExponent (c 2) 2 := by
  have hres : ∀ (D : Γ(biquadraticModule S, ⊤)) (α β : Fin 2),
      (triquadraticModule S).presheaf.map (homOfLE le_top).op
        (tensorSectionsAt (projectiveLineCube S).sheaf.obj
          (projectiveLineCube S).ringCatSheaf.property (op ⊤) _ _
          (tensorSectionsAt (projectiveLineCube S).sheaf.obj
            (projectiveLineCube S).ringCatSheaf.property (op ⊤) _ _ D (thirdCoordinate S α))
          (thirdCoordinate S β)) =
      tensorSectionsAt (projectiveLineCube S).sheaf.obj
          (projectiveLineCube S).ringCatSheaf.property (op (chartOpen S c))
          (biquadraticLinearModule S) (lineBundle S 2)
          (tensorSectionsAt (projectiveLineCube S).sheaf.obj
            (projectiveLineCube S).ringCatSheaf.property (op (chartOpen S c))
            (biquadraticModule S) (lineBundle S 2)
            ((biquadraticModule S).presheaf.map (homOfLE le_top).op D)
            ((coordinate S 2 α).eval (op (chartOpen S c))))
          ((coordinate S 2 β).eval (op (chartOpen S c))) := by
    intro D α β
    refine (Stacks.SectionProduct.map_tensorSectionsAt (biquadraticLinearModule S)
      (lineBundle S 2) (homOfLE le_top) _ _).trans ?_
    exact congrArg₂ (fun x y => tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op (chartOpen S c))
        (biquadraticLinearModule S) (lineBundle S 2) x y)
      ((Stacks.SectionProduct.map_tensorSectionsAt (biquadraticModule S) (lineBundle S 2)
        (homOfLE le_top) _ _).trans (congrArg _
          (PresheafOfModules.sections_property (coordinate S 2 α) (homOfLE le_top).op)))
      (PresheafOfModules.sections_property (coordinate S 2 β) (homOfLE le_top).op)
  have hsplit := (map_add (ConcreteCategory.hom ((triquadraticModule S).presheaf.map
    (homOfLE le_top).op)) _ _).trans (congrArg₂ (· + ·)
      ((map_add (ConcreteCategory.hom ((triquadraticModule S).presheaf.map
        (homOfLE le_top).op)) _ _).trans (congrArg₂ (· + ·) (hres A 0 0) (hres B 0 1)))
      (hres C 1 1))
  refine (congrArg (divBySection (X := (projectiveLineCube S).toRingedSpace)
    (triquadraticModule S) (chartFrame S c) (chartOpen_le_nonvanishingOpen_chartFrame S c))
      hsplit).trans ?_
  refine (divBySection_add (X := (projectiveLineCube S).toRingedSpace) _ _ _ _ _).trans ?_
  refine congrArg₂ (· + ·) ((divBySection_add (X := (projectiveLineCube S).toRingedSpace)
    _ _ _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)) ?_
  · exact (divBySection_tensorSectionsAt_chartFrame S c _ 0 0).trans
      (congrArg _ (ite_mul_ite_eq_pow_dehomExponent _ (c 2) 0))
  · exact (divBySection_tensorSectionsAt_chartFrame S c _ 0 1).trans
      (congrArg _ (ite_mul_ite_eq_pow_dehomExponent _ (c 2) 1))
  · exact (divBySection_tensorSectionsAt_chartFrame S c _ 1 1).trans
      (congrArg _ (ite_mul_ite_eq_pow_dehomExponent _ (c 2) 2))

end projectiveLineCube

end AlgebraicGeometry
