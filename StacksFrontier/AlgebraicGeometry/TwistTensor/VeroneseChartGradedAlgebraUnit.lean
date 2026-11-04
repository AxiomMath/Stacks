module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.VeroneseChartGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackMultiplication
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.PullbackTwistRegroupingFamily

/-!
# Situation 01QH's map preserves the unit

Let `X` be a scheme, `𝓛` an ample invertible sheaf on `X`, `S = Γ_*(X, 𝓛)` and `Y = Proj S`, and
let `f : X ⟶ Y` be the canonical morphism of [Stacks, Tag 01PZ].  Situation [Stacks, Tag 01QH]
equips `f` with a `ℤ`-graded `𝒪_X`-algebra map `⨁_{n ∈ ℤ} f^*𝒪_Y(n) ⟶ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`.  Its
degreewise components are `Stacks.SectionRingVeroneseChart.twistComparison` and its
multiplicativity in an arbitrary integer bidegree is
`Stacks.SectionRingVeroneseChart.twistComparison_mul`; **this file supplies the remaining datum of
an algebra map, preservation of the unit.**

## The route, and why no global-sections argument is needed

The degree-zero pieces of both graded algebras are `𝒪_X`, so the statement is a triangle: the
degree-zero component carries the unit of the source algebra to the unit of the target.  Both
units are forced, and that is what makes the triangle a consequence of the bidegree square rather
than of a separate computation.

* The **target** unit is `(Stacks.Ample.tensorPowModuleZeroIso X 𝓛).inv`, and its left unit law
  against [Stacks, Tag 01CU]'s addition law is
  `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int`, in every integer
  degree.
* The **source** unit is `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit` — the unit
  `𝒪_{Proj 𝒮} ≅ 𝒪_{Proj 𝒮}(0)` of [Stacks, Tag 01MO]'s multiplication, pulled back along the
  canonical morphism and conjugated by [Stacks, Tag 01CD] — and its left unit law against the
  pulled-back multiplication is
  `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_left`.  **Both were already in the
  library**, for an arbitrary morphism of ringed spaces into `Proj 𝒮` and an arbitrary integer
  degree; `pbTwistUnit` and `pbTwistUnit_pbTwistMul` are those two read at the
  `Stacks.SectionRingVeroneseChart.pbTwistMul` spelling of the source algebra.

Given the two unit laws, the bidegree square at `(0, m)` says that the comparison's degree-zero
component, prefixed by the source unit, and the target unit become equal after tensoring on the
right by the comparison in the degree `m`; and tensoring on the right by an invertible
`𝒪_X`-module is an equivalence ([Stacks, Tag 0FFM],
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`), hence faithful, so the two
are equal.  `f^*𝒪_Y(m)` is invertible in every degree
(`Stacks.SectionRingVeroneseChart.isInvertibleModule_pbTwist`), so this is available at every `m`.

The cancellation is the whole content of the implication, and it replaces the argument the
predecessor of this file recorded as owed: that the degree-zero component is an isomorphism of
`𝒪_X`-modules, hence multiplication by a global unit, which the bidegree `(0, 0)` case shows
idempotent, hence `1`.  That argument is about global sections, no part of it is formalized in
this repository, and none of it is needed — the uniqueness of a unit for an invertible-object
multiplication is a cancellation, not a computation.

## Main definitions

* `Stacks.SectionRingVeroneseChart.pbTwistUnit`: **the unit of the graded `𝒪_X`-algebra
  `⨁_{n ∈ ℤ} f^*𝒪_Y(n)`**, `𝒪_X ⟶ f^*𝒪_Y(0)`.

## Main results

* `Stacks.SectionRingVeroneseChart.pbTwistUnit_twistComparison`: **unit preservation for Situation
  [Stacks, Tag 01QH]'s map** — the degree-zero component carries `pbTwistUnit` to the unit
  `(tensorPowModuleZeroIso X 𝓛).inv` of [Stacks, Tag 01CU]'s addition law.
* `Stacks.SectionRingVeroneseChart.unit_comp_twistComparison_of_mul`: the same for **any** map
  `𝒪_X ⟶ f^*𝒪_Y(0)` satisfying the source algebra's left unit law in a single degree, which is
  the form that says the datum is forced; `pbTwistUnit_twistComparison` is it at `pbTwistUnit`.
* `Stacks.SectionRingVeroneseChart.pbTwistUnit_eq_of_mul`: a unit of `pbTwistMul` is unique, so
  `pbTwistUnit` is *the* unit and the triangle above is not a statement about a chosen map.
* `Stacks.SectionRingVeroneseChart.pbTwistUnit_pbTwistMul` and `pbTwistMul_pbTwistUnit`: the
  source algebra's left and right unit laws, which together make `pbTwistUnit` a unit for
  `pbTwistMul` and not merely a left unit.
* `Stacks.SectionRingVeroneseChart.twistComparison_congr`: the comparison commutes with the
  transport along an equality of degrees, which is what lets the square at `(0, m)` be read
  against the degree `m` rather than the degree `0 + m`.
* `Stacks.Monoidal.unit_whiskerRight_free`: the free-shape cancellation the argument above is,
  with every object and morphism a variable.

## Implementation notes

**The source multiplication and unit are consumed, not rebuilt.**
`Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMulRS` and
`Stacks.SectionRingVeroneseChart.pbTwistMul` are the same map at two spellings of the category of
sheaves of modules — `Stacks.RingedSpace.structureRingSheaf X` against `X.Modules` — and the only
difference between the two terms is that one inverts [Stacks, Tag 01CD]'s comparison with
`CategoryTheory.inv` and the other with `Iso.inv`.  `pbTwistMul_eq_pullbackTwistMul` crosses that,
exactly as `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulHom_eq_pullbackTwistMul` does on
[Stacks, Tag 01MU]'s open `W₁`.

**The cancellation is isolated into a free-shape lemma.** `unit_whiskerRight_free` has every
object and morphism a variable, so the two spellings of the structure-ring sheaf never meet inside
a unification; the instantiation below is a term, where `:=` is tolerant of the definitional
unfolding that `rw` and `simp only` refuse on these goals.  This is the discipline of
`StacksFrontier/AlgebraicGeometry/TwistTensor/VeroneseChartGradedAlgebra.lean`.

**The degree is left free in the cancellation.** Taking `m = 0` would make both transports of the
total degree transports along `0 + 0 = 0` and collapse them, but only up to the definitional
unfolding of `Int.add`, which is not available at the transparency `rw` works at.
`twistComparison_congr` moves the square from the degree `0 + m` to the degree `m` for every `m`
instead, at no extra cost.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.PullbackTensorCoherence (pullbackTensorComparison)

namespace Stacks.Monoidal

section Free

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **A unit is determined by a bidegree square and the two left unit laws, after tensoring on the
right.**  Let `u` and `v` be the multiplications of two graded algebras in the bidegree `(0, m)`,
`φ₀`, `φₘ` and `φₛ` the three components of a comparison between them, `ηA` a unit for the source
and `uB` the target's identification of its degree-zero piece with the monoidal unit; let `tA` and
`tB` be the transports of the total degree the two unit laws carry.  Then the source unit followed
by the degree-zero component, and the target unit, agree after tensoring on the right by the
source's degree-`m` piece.

Removing that last tensor factor is a separate step: it needs the degree-`m` piece to be
invertible, which is a statement about the ambient category and not about this diagram. -/
theorem unit_whiskerRight_free {A₀ Aₘ Aₛ B₀ Bₘ Bₛ : D}
    (u : A₀ ⊗ Aₘ ⟶ Aₛ) (v : B₀ ⊗ Bₘ ≅ Bₛ)
    (φ₀ : A₀ ⟶ B₀) (φₘ : Aₘ ≅ Bₘ) (φₛ : Aₛ ⟶ Bₛ)
    (ηA : 𝟙_ D ⟶ A₀) (uB : B₀ ≅ 𝟙_ D) (tA : Aₘ ⟶ Aₛ) (tB : Bₛ ⟶ Bₘ)
    (hsq : u ≫ φₛ = (φ₀ ⊗ₘ φₘ.hom) ≫ v.hom)
    (hA : ηA ▷ Aₘ ≫ u = (λ_ Aₘ).hom ≫ tA)
    (hB : uB.hom ▷ Bₘ ≫ (λ_ Bₘ).hom = v.hom ≫ tB)
    (ht : tA ≫ φₛ ≫ tB = φₘ.hom) :
    (ηA ≫ φ₀) ▷ Aₘ = uB.inv ▷ Aₘ := by
  have hiso : IsIso (v.hom ≫ tB) := by
    rw [← hB]
    infer_instance
  have hunitB : uB.inv ▷ Bₘ ≫ v.hom ≫ tB = (λ_ Bₘ).hom := by
    rw [← hB, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, uB.inv_hom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  have hleft : ((ηA ≫ φ₀) ⊗ₘ φₘ.hom) ≫ v.hom ≫ tB = (λ_ Aₘ).hom ≫ φₘ.hom := by
    have hsplit : ((ηA ≫ φ₀) ⊗ₘ φₘ.hom) = ηA ▷ Aₘ ≫ (φ₀ ⊗ₘ φₘ.hom) := by
      simp [MonoidalCategory.tensorHom_def]
    rw [hsplit]
    simp only [Category.assoc]
    rw [← reassoc_of% hsq, reassoc_of% hA, ht]
  have hright : (uB.inv ⊗ₘ φₘ.hom) ≫ v.hom ≫ tB = (λ_ Aₘ).hom ≫ φₘ.hom := by
    have hsplit : (uB.inv ⊗ₘ φₘ.hom) = 𝟙_ D ◁ φₘ.hom ≫ uB.inv ▷ Bₘ := by
      rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [hsplit]
    simp only [Category.assoc]
    rw [hunitB]
    exact MonoidalCategory.leftUnitor_naturality _
  refine (cancel_mono (B₀ ◁ φₘ.hom)).mp ?_
  rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def]
  exact (cancel_mono (v.hom ≫ tB)).mp (hleft.trans hright.symm)

end Free

end Stacks.Monoidal

namespace Stacks.SectionRingVeroneseChart

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

/-! ### The canonical morphism as a morphism of ringed spaces -/

/-- The canonical morphism of [Stacks, Tag 01PZ], read as a morphism of ringed spaces.  This is
the spelling `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit` and the unit laws of the
pulled-back multiplication of [Stacks, Tag 01MO] are stated at. -/
abbrev projHomRS :
    X.toRingedSpace ⟶ (AlgebraicGeometry.Proj (grading L)).toRingedSpace :=
  (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL).toLRSHom.toShHom

/-! ### The unit of the source algebra -/

/-- **The unit of the graded `𝒪_X`-algebra `⨁_{n ∈ ℤ} f^*𝒪_Y(n)`**, `𝒪_X ⟶ f^*𝒪_Y(0)`: the unit
`𝒪_{Proj 𝒮} ≅ 𝒪_{Proj 𝒮}(0)` of [Stacks, Tag 01MO]'s multiplication, pulled back along the
canonical morphism of [Stacks, Tag 01PZ] and conjugated by the comparison of [Stacks, Tag 01CD].

This is `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit`, which exists for an arbitrary
morphism of ringed spaces into `Proj 𝒮`, read at the `X.Modules` spelling; the ascription is the
whole content, and `pbTwistUnit_eq` records that it changes no term. -/
def pbTwistUnit : 𝟙_ X.Modules ⟶ pbTwist L hL 0 :=
  Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit (grading L) (projHomRS L hL)

/-- **The retyping changes no term.** -/
theorem pbTwistUnit_eq :
    pbTwistUnit L hL =
      Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit (grading L) (projHomRS L hL) :=
  rfl

/-- **The source multiplication is the pulled-back multiplication of the twists**, at the
ringed-space spelling the unit laws of [Stacks, Tag 01MO]'s multiplication are stated at.  The two
terms differ only in how the comparison of [Stacks, Tag 01CD] is inverted — `CategoryTheory.inv`
there, `Iso.inv` in `pbTwistMul`.

This is the mirror of
`Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulHom_eq_pullbackTwistMul`, which crosses the
same boundary on [Stacks, Tag 01MU]'s open `W₁`. -/
theorem pbTwistMul_eq_pullbackTwistMul (n m : ℤ) :
    pbTwistMul L hL n m =
      Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMulRS (grading L) (projHomRS L hL) n m := by
  have hinv : inv (pullbackTensorComparison (projHomRS L hL)
        (Stacks.AlgebraicGeometry.TwistTensor.twist (grading L) n)
        (Stacks.AlgebraicGeometry.TwistTensor.twist (grading L) m)) =
      (pullbackTensorModulesIso (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)
        (twistingSheaf (grading L) n) (twistingSheaf (grading L) m)).inv :=
    IsIso.inv_eq_of_hom_inv_id
      (pullbackTensorModulesIso (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)
        (twistingSheaf (grading L) n) (twistingSheaf (grading L) m)).hom_inv_id
  rw [pbTwistMul_eq, Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMulRS_eq,
    Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul, hinv]
  rfl

/-- **The left unit law of the source algebra**, in every integer degree `m`: multiplying by
`pbTwistUnit` on the left is the left unitor of [Stacks, Tag 01CA], up to the transport of the
total degree along `m = 0 + m`.

This is `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_left` — which holds for an
arbitrary morphism of ringed spaces into `Proj 𝒮`, with no hypothesis on it — read at the
`pbTwistMul` spelling. -/
theorem pbTwistUnit_pbTwistMul (m : ℤ) :
    pbTwistUnit L hL ▷ pbTwist L hL m ≫ pbTwistMul L hL 0 m =
      (λ_ (pbTwist L hL m)).hom ≫ eqToHom (congrArg (pbTwist L hL) (zero_add m).symm) := by
  rw [pbTwistMul_eq_pullbackTwistMul, pbTwistUnit_eq]
  refine Eq.trans (Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_left
    (grading L) (projHomRS L hL) m) ?_
  rw [eqToHom_map]
  rfl

/-- **The right unit law of the source algebra**, in every integer degree `n`: multiplying by
`pbTwistUnit` on the right is the right unitor of [Stacks, Tag 01CA], up to the transport of the
total degree along `n = n + 0`.  With `pbTwistUnit_pbTwistMul` this is what makes `pbTwistUnit` a
unit for `pbTwistMul` and not merely a left unit.

This is `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_right` read at the `pbTwistMul`
spelling. -/
theorem pbTwistMul_pbTwistUnit (n : ℤ) :
    pbTwist L hL n ◁ pbTwistUnit L hL ≫ pbTwistMul L hL n 0 =
      (ρ_ (pbTwist L hL n)).hom ≫ eqToHom (congrArg (pbTwist L hL) (add_zero n).symm) := by
  rw [pbTwistMul_eq_pullbackTwistMul, pbTwistUnit_eq]
  refine Eq.trans (Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_right
    (grading L) (projHomRS L hL) n) ?_
  rw [eqToHom_map]
  rfl

/-! ### The comparison against the transport of the degree -/

/-- **The comparison commutes with the transport along an equality of degrees.**  Both transports
are the identity once the equality is eliminated, so this is the statement that the family
`twistComparison` is indexed by the degree and by nothing else. -/
theorem twistComparison_congr {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (pbTwist L hL) h) ≫ twistComparison L hL b ≫
        (tensorPowModuleCongr X L h.symm).hom =
      twistComparison L hL a := by
  cases h
  simp only [Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleCongr_hom, eqToHom_refl,
    Category.comp_id, Category.id_comp]

/-! ### Unit preservation -/

/-- **Unit preservation, for any map satisfying the source algebra's left unit law in a single
degree.**  If `η : 𝒪_X ⟶ f^*𝒪_Y(0)` multiplies as the unit does in the bidegree `(0, m)` for one
integer `m`, then the degree-zero component of Situation [Stacks, Tag 01QH]'s map carries `η` to
the unit `(tensorPowModuleZeroIso X 𝓛).inv` of [Stacks, Tag 01CU]'s addition law.

The input is the bidegree square `twistComparison_mul` at `(0, m)` together with the target's left
unit law `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int`; the free-shape
`Stacks.Monoidal.unit_whiskerRight_free` turns the two into an equality of the two candidates
tensored on the right by `f^*𝒪_Y(m)`, and tensoring on the right by that invertible module is an
equivalence ([Stacks, Tag 0FFM]), hence faithful. -/
theorem unit_comp_twistComparison_of_mul (m : ℤ) {η : 𝟙_ X.Modules ⟶ pbTwist L hL 0}
    (hη : η ▷ pbTwist L hL m ≫ pbTwistMul L hL 0 m =
      (λ_ (pbTwist L hL m)).hom ≫ eqToHom (congrArg (pbTwist L hL) (zero_add m).symm)) :
    η ≫ twistComparison L hL 0 = (tensorPowModuleZeroIso X L).inv := by
  have key : (η ≫ twistComparison L hL 0) ▷ pbTwist L hL m =
      (tensorPowModuleZeroIso X L).inv ▷ pbTwist L hL m :=
    Stacks.Monoidal.unit_whiskerRight_free (pbTwistMul L hL 0 m)
      (tensorPowModuleAddIso X L 0 m) (twistComparison L hL 0) (twistComparisonIso L hL m)
      (twistComparison L hL (0 + m)) η (tensorPowModuleZeroIso X L)
      (eqToHom (congrArg (pbTwist L hL) (zero_add m).symm))
      (tensorPowModuleCongr X L (zero_add m)).hom
      (twistComparison_mul L hL 0 m) hη
      (Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int X L m)
      (twistComparison_congr L hL (zero_add m).symm)
  have : (tensorRightModules X (pbTwist L hL m)).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  rw [Stacks.AlgebraicGeometry.PullbackTwistRegrouping.whiskerRight_eq_tensorRightModules,
    Stacks.AlgebraicGeometry.PullbackTwistRegrouping.whiskerRight_eq_tensorRightModules] at key
  exact (tensorRightModules X (pbTwist L hL m)).map_injective key

/-- **A unit of the source algebra is unique**, so `pbTwistUnit` is *the* unit of
`pbTwistMul` and unit preservation below is not a statement about a chosen map.  Both candidates
multiply as the unit does in the bidegree `(0, m)`, hence agree after tensoring on the right by
the invertible module `f^*𝒪_Y(m)`. -/
theorem pbTwistUnit_eq_of_mul (m : ℤ) {η : 𝟙_ X.Modules ⟶ pbTwist L hL 0}
    (hη : η ▷ pbTwist L hL m ≫ pbTwistMul L hL 0 m =
      (λ_ (pbTwist L hL m)).hom ≫ eqToHom (congrArg (pbTwist L hL) (zero_add m).symm)) :
    η = pbTwistUnit L hL := by
  have := isIso_twistComparison L hL 0
  exact (cancel_mono (twistComparison L hL 0)).mp
    ((unit_comp_twistComparison_of_mul L hL m hη).trans
      (unit_comp_twistComparison_of_mul L hL m (pbTwistUnit_pbTwistMul L hL m)).symm)

/-- **Situation [Stacks, Tag 01QH]'s map preserves the unit.**  The degree-zero component of the
map carries the unit `pbTwistUnit` of the source graded `𝒪_X`-algebra `pbTwistMul` — the
multiplication of the twisting sheaves of [Stacks, Tag 01MO], pulled back along the canonical
morphism of [Stacks, Tag 01PZ] and conjugated by [Stacks, Tag 01CD] — to the unit of
[Stacks, Tag 01CU]'s addition law for the tensor powers of `𝓛`, whose degree-zero piece is `𝒪_X`
by `Stacks.Ample.tensorPowModuleZeroIso`.

Together with the degreewise family `twistComparison` and the bidegree square
`twistComparison_mul` this is the `ℤ`-graded `𝒪_X`-algebra map
`⨁_{n ∈ ℤ} f^*𝒪_Y(n) ⟶ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}` the Situation equips the canonical morphism with,
including the unit datum that distinguishes `Stacks.SheafOfModules.GradedAlgebra.UnitalHom` from
`Stacks.SheafOfModules.GradedAlgebra.Hom` (both registered for [Stacks, Tag 0FQW]).

`pbTwistUnit_eq_of_mul` says the source unit is unique, so no choice is being made here. -/
@[stacks 01QH "unit preservation: the degree-zero component of the Situation's map carries the \
unit pbTwistUnit of the source graded O_X-algebra pbTwistMul -- Tag 01MO's multiplication of the \
twisting sheaves pulled back along the canonical morphism of Tag 01PZ and conjugated by Tag 01CD \
-- to the unit of Tag 01CU's addition law for the tensor powers of L, whose degree-zero piece is \
O_X by tensorPowModuleZeroIso. This is the extra datum of SheafOfModules.GradedAlgebra.UnitalHom \
over GradedAlgebra.Hom (both registered for 0FQW). With the degreewise family twistComparison and \
the bidegree square twistComparison_mul the three jointly give the Z-graded O_X-algebra map the \
Situation equips the canonical morphism with. The source unit is unique \
(pbTwistUnit_eq_of_mul), so no choice is made"]
theorem pbTwistUnit_twistComparison :
    pbTwistUnit L hL ≫ twistComparison L hL 0 = (tensorPowModuleZeroIso X L).inv :=
  unit_comp_twistComparison_of_mul L hL 0 (pbTwistUnit_pbTwistMul L hL 0)

end Monoidal

end Stacks.SectionRingVeroneseChart

end
