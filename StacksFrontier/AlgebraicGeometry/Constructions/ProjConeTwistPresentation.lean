module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.Cone
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# The twist algebras of a homogeneous spectrum and the direct images of its cone

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a nonnegatively graded ring and `P = Proj A`. The twisting sheaves
`𝒪_P(m)` all have the same underlying module, the regular module `A`, so a local section of
`𝒪_P(m)` is a function into the localizations `A_x` that is locally a fraction `a / s` with `a`
and `s` homogeneous and `deg a - deg s = m`. Multiplying such fractions adds the degrees, which
makes the family `m ↦ 𝒪_P(m)` a sheaf of `ℤ`-graded `𝒪_P`-algebras

  `⨁_{m ∈ ℤ} 𝒪_P(m)`,

and its nonnegative part a second one,

  `⨁_{m ≥ 0} 𝒪_P(m)`,

whose pieces in negative degrees vanish. These are the two algebras that present the cone
`L = Proj(⨁_{d ≥ 0} A_{≥ d})` and its punctured part `U ⊆ L` as relative spectra over `P`:
`L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` and `U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`.

We construct the two graded algebras and the inclusion of the first in the second, and on the
geometric side the two direct-image algebras `π_* 𝒪_L` and `(π|_U)_* 𝒪_U` over `P` together with
the restriction morphism between them.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.twistMul`: multiplication
  `𝒪_P(i) × 𝒪_P(j) → 𝒪_P(i + j)` of local sections of twisting sheaves.
* `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra`: the sheaf of graded algebras
  `⨁_{m ∈ ℤ} 𝒪_P(m)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistingSheaf` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra`: the homogeneous pieces of
  `⨁_{m ≥ 0} 𝒪_P(m)` and the sheaf of graded algebras they form.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebra`: the inclusion
  `⨁_{m ≥ 0} 𝒪_P(m) ⟶ ⨁_{m ∈ ℤ} 𝒪_P(m)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebra` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebra`: the `𝒪_P`-algebras `π_* 𝒪_L`
  and `(π|_U)_* 𝒪_U`, and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneToPuncturedConeAlgebra` the restriction morphism
  between them.
* `Stacks.AlgebraicGeometry.ProjConeTwist.structureSheafToTwistZero`: the comparison of the
  structure sheaf with the untwisted sheaf `𝒪_P(0)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.mul_mem_moduleSections`: the product of a local
  fraction of degree `i` and one of degree `j` is a local fraction of degree `i + j`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegPieceIso`: in nonnegative degrees the pieces of
  `⨁_{m ≥ 0} 𝒪_P(m)` are the twisting sheaves, and
  `Stacks.AlgebraicGeometry.ProjConeTwist.isZero_nonnegTwistingSheaf`: in negative degrees they
  vanish.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebra_app_natCast`: the
  inclusion of the two algebras is the identity on each nonnegative twist.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneToPuncturedConeAlgebra_app`: over an open of `P`
  the restriction morphism of the two direct-image algebras is the canonical map on functions
  induced by the open immersion of the punctured cone.
* `Stacks.AlgebraicGeometry.ProjConeTwist.structureSheafToTwistZero_bijective`: over every open
  the comparison of the structure sheaf with `𝒪_P(0)` is a bijection, and
  `Stacks.AlgebraicGeometry.ProjConeTwist.structureSheafToTwistZero_mul` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.structureSheafToTwistZero_one`: it is multiplicative
  and unital, so the degree-zero piece of either twist algebra is the structure sheaf.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ZeroObject
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u v w

section Twist

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The action of `ℕ` on `ℤ` by addition of the cast. -/
local instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-! ### Homogeneous degrees in a shifted grading -/

omit [GradedRing 𝒜] in
/-- A homogeneous element of degree `d` lies in degree `e` of the grading shifted by `t`, as
soon as `d = e + t`. -/
theorem mem_twistGrading_of_mem {t e : ℤ} {d : ℕ} (h : (d : ℤ) = e + t) {a : A}
    (ha : a ∈ 𝒜 d) : a ∈ twistGrading (S := A) 𝒜 t e := by
  have h0 : (0 : ℤ) ≤ e + t := h ▸ Int.natCast_nonneg d
  have hd : (e + t).toNat = d := by omega
  simpa [integerGrading, h0, hd] using ha

omit [GradedRing 𝒜] in
/-- Degree `e` of the grading shifted by `t` is the homogeneous part of degree `e + t`. -/
theorem mem_of_mem_twistGrading {t e : ℤ} (h : 0 ≤ e + t) {a : A}
    (ha : a ∈ twistGrading (S := A) 𝒜 t e) : a ∈ 𝒜 (e + t).toNat := by
  simpa [integerGrading, h] using ha

omit [GradedRing 𝒜] in
/-- The pieces of a shifted grading vanish below the shift. -/
theorem eq_zero_of_mem_twistGrading {t e : ℤ} (h : e + t < 0) {a : A}
    (ha : a ∈ twistGrading (S := A) 𝒜 t e) : a = 0 := by
  simpa [integerGrading, not_le.mpr h] using ha

/-! ### Multiplication of local fractions -/

/-- The product of a local fraction of degree `i` and one of degree `j` is a local fraction of
degree `i + j`. -/
theorem mul_mem_moduleSections (i j : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a b : ∀ x : U, ModuleFiber (M := A) 𝒜 x.1)
    (ha : a ∈ moduleSections 𝒜 (twistGrading (S := A) 𝒜 i) U)
    (hb : b ∈ moduleSections 𝒜 (twistGrading (S := A) 𝒜 j) U) :
    (fun x => a x * b x) ∈ moduleSections 𝒜 (twistGrading (S := A) 𝒜 (i + j)) U := by
  intro x
  obtain ⟨V, hxV, iV, n, m, s, hm, hs, hns, hav⟩ := ha x
  obtain ⟨W, hxW, iW, k, m', s', hm', hs', hns', hbw⟩ := hb x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV, n + k, m * m', s * s', ?_,
    by simpa using SetLike.mul_mem_graded hs hs',
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hns ⟨y.1, y.2.1⟩) (hns' ⟨y.1, y.2.2⟩), ?_⟩
  · by_cases hni : 0 ≤ (n : ℤ) + i
    · by_cases hkj : 0 ≤ (k : ℤ) + j
      · refine mem_twistGrading_of_mem 𝒜
          (d := ((n : ℤ) + i).toNat + ((k : ℤ) + j).toNat) (by omega) ?_
        exact SetLike.mul_mem_graded (mem_of_mem_twistGrading 𝒜 hni hm)
          (mem_of_mem_twistGrading 𝒜 hkj hm')
      · rw [eq_zero_of_mem_twistGrading 𝒜 (by omega) hm', mul_zero]
        exact zero_mem _
    · rw [eq_zero_of_mem_twistGrading 𝒜 (by omega) hm, zero_mul]
      exact zero_mem _
  · intro y
    refine (congrArg₂ (· * ·) (hav ⟨y.1, y.2.1⟩) (hbw ⟨y.1, y.2.2⟩)).trans ?_
    exact LocalizedModule.mk_mul_mk

/-- Two local sections of a twist agree as soon as they agree in every fibre. -/
theorem twistSection_ext {n : ℤ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    {a b : (twistingSheaf 𝒜 n).val.obj U} (h : ∀ x, a.1 x = b.1 x) : a = b :=
  Subtype.ext (funext h)

/-- The product of a local section of `𝒪(i)` and one of `𝒪(j)`, as a local section of
`𝒪(i + j)`: the product of their values in every fibre. -/
def twistMulSection (i j : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 i).val.obj U) (b : (twistingSheaf 𝒜 j).val.obj U) :
    (twistingSheaf 𝒜 (i + j)).val.obj U :=
  ⟨fun x => a.1 x * b.1 x, mul_mem_moduleSections 𝒜 i j U.unop a.1 b.1 a.2 b.2⟩

/-- The value of `twistMulSection` at a point is the product of the two values. -/
@[simp] theorem twistMulSection_val (i j : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 i).val.obj U) (b : (twistingSheaf 𝒜 j).val.obj U) (x : U.unop) :
    (twistMulSection 𝒜 i j U a b).1 x = a.1 x * b.1 x := rfl

/-- Multiplication of twists `𝒪(i) × 𝒪(j) → 𝒪(i + j)`, as a bilinear map of sheaves of modules. -/
def twistMul (i j : ℤ) :
    SheafOfModules.BilinearMap (twistingSheaf 𝒜 i) (twistingSheaf 𝒜 j)
      (twistingSheaf 𝒜 (i + j)) where
  app U :=
    AddMonoidHom.mk'
      (fun a => AddMonoidHom.mk' (twistMulSection 𝒜 i j U a)
        (fun b c => twistSection_ext 𝒜 fun x => mul_add (a.1 x) (b.1 x) (c.1 x)))
      (fun a a' => AddMonoidHom.ext fun b =>
        twistSection_ext 𝒜 fun x => add_mul (a.1 x) (a'.1 x) (b.1 x))
  map_smul_left U r a b := by
    refine twistSection_ext 𝒜 fun x => ?_
    change (HomogeneousLocalization.val (r.1 x) • a.1 x) * b.1 x =
      HomogeneousLocalization.val (r.1 x) • (a.1 x * b.1 x)
    exact smul_mul_assoc _ _ _
  map_smul_right U r a b := by
    refine twistSection_ext 𝒜 fun x => ?_
    change a.1 x * (HomogeneousLocalization.val (r.1 x) • b.1 x) =
      HomogeneousLocalization.val (r.1 x) • (a.1 x * b.1 x)
    exact mul_smul_comm _ _ _
  naturality f a b := rfl

/-! ### The graded algebra of all integral twists -/

/-- The constant section `1` of the untwisted sheaf is a local fraction of degree zero. -/
theorem one_mem_moduleSections (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (fun _ : U => (1 : ModuleFiber (M := A) 𝒜 _)) ∈
      moduleSections 𝒜 (twistGrading (S := A) 𝒜 0) U := fun x =>
  ⟨U, x.2, 𝟙 _, 0, 1, 1, mem_twistGrading_of_mem 𝒜 (by simp) (SetLike.one_mem_graded 𝒜),
    SetLike.one_mem_graded 𝒜, fun y => y.1.isPrime.one_notMem,
    fun _ => OreLocalization.one_def⟩

/-- The unit section of the untwisted sheaf. -/
def twistOne : (twistingSheaf 𝒜 0).sections :=
  PresheafOfModules.sectionsMk (fun U => ⟨_, one_mem_moduleSections 𝒜 U.unop⟩)
    fun {_ _} _ => rfl

/-- The unit section of the untwisted sheaf has value `1` at every point. -/
@[simp] theorem twistOne_val (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (x : U.unop) :
    ((twistOne 𝒜).eval U).1 x = 1 := rfl

/-- Local sections of two twists of equal index are heterogeneously equal once their values
agree. -/
theorem twist_heq {d e : ℤ} (h : d = e) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    {a : (twistingSheaf 𝒜 d).val.obj U} {b : (twistingSheaf 𝒜 e).val.obj U}
    (hab : ∀ x, a.1 x = b.1 x) : HEq a b := by
  subst h
  exact heq_of_eq (twistSection_ext 𝒜 hab)
/-- The product of local sections of the twists is associative, as a heterogeneous equality between
the pieces of degree `(i + j) + k` and `i + (j + k)`. -/
theorem twistMul_heq_assoc (i j k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : (twistingSheaf 𝒜 i).val.obj U) (y : (twistingSheaf 𝒜 j).val.obj U)
    (z : (twistingSheaf 𝒜 k).val.obj U) :
    HEq ((twistMul 𝒜 (i + j) k).app U ((twistMul 𝒜 i j).app U x y) z)
      ((twistMul 𝒜 i (j + k)).app U x ((twistMul 𝒜 j k).app U y z)) := by
  refine twist_heq 𝒜 (add_assoc i j k) fun p => ?_
  change x.1 p * y.1 p * z.1 p = x.1 p * (y.1 p * z.1 p)
  exact mul_assoc _ _ _

/-- The unit section is a left identity for the product of twists. -/
theorem twistMul_heq_one_mul (i : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : (twistingSheaf 𝒜 i).val.obj U) :
    HEq ((twistMul 𝒜 0 i).app U ((twistOne 𝒜).eval U) x) x := by
  refine twist_heq 𝒜 (zero_add i) fun p => ?_
  change (1 : ModuleFiber (M := A) 𝒜 _) * x.1 p = x.1 p
  exact one_mul _

/-- The unit section is a right identity for the product of twists. -/
theorem twistMul_heq_mul_one (i : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : (twistingSheaf 𝒜 i).val.obj U) :
    HEq ((twistMul 𝒜 i 0).app U x ((twistOne 𝒜).eval U)) x := by
  refine twist_heq 𝒜 (add_zero i) fun p => ?_
  change x.1 p * (1 : ModuleFiber (M := A) 𝒜 _) = x.1 p
  exact mul_one _

/-- The graded algebra `⨁_{m ∈ ℤ} 𝒪_P(m)` of all integral twists on `P = Proj A`. -/
@[stacks 0EKG "the graded algebra of all integral twists"]
def integerTwistAlgebra :
    SheafOfModules.GradedAlgebra (AlgebraicGeometry.Proj 𝒜).ringCatSheaf where
  piece n := twistingSheaf 𝒜 n
  mul := twistMul 𝒜
  one := twistOne 𝒜
  mul_assoc i j k U x y z := twistMul_heq_assoc 𝒜 i j k U x y z
  one_mul i U x := twistMul_heq_one_mul 𝒜 i U x
  mul_one i U x := twistMul_heq_mul_one 𝒜 i U x

/-! ### The graded algebra of nonnegative twists -/

/-- An element of a sheaf of modules that is a zero object vanishes. -/
theorem eq_zero_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M)
    {U : (Opens X)ᵒᵖ} (a : M.val.obj U) : a = 0 := by
  have h : (CategoryTheory.CategoryStruct.id M) = 0 := hM.eq_of_src _ _
  exact congrArg (fun f : M ⟶ M => (ConcreteCategory.hom (f.val.app U)) a) h

/-- The zero bilinear map of sheaves of modules. -/
def zeroBilinear {X : Scheme.{u}} (M N P : X.Modules) : SheafOfModules.BilinearMap M N P where
  app _ := 0
  map_smul_left _ _ _ _ := by simp
  map_smul_right _ _ _ _ := by simp
  naturality _ _ _ := by
    change (ConcreteCategory.hom (P.val.map _)) 0 = 0
    exact map_zero _

/-- The `n`-th homogeneous piece of the algebra of nonnegative twists: the `n`-th twisting sheaf
for `n ≥ 0`, and the zero sheaf for `n < 0`. -/
def nonnegTwistingSheaf : ℤ → (AlgebraicGeometry.Proj 𝒜).Modules
  | (m : ℕ) => twistingSheaf 𝒜 (m : ℤ)
  | .negSucc _ => 0

/-- In a nonnegative degree `m` the piece of the algebra of nonnegative twists is `𝒪(m)`. -/
@[simp] theorem nonnegTwistingSheaf_natCast (m : ℕ) :
    nonnegTwistingSheaf 𝒜 (m : ℤ) = twistingSheaf 𝒜 (m : ℤ) := rfl

/-- In negative degrees the pieces of the algebra of nonnegative twists vanish. -/
@[stacks 0EKG "the homogeneous pieces in negative degrees"]
theorem isZero_nonnegTwistingSheaf {n : ℤ} (hn : n < 0) :
    IsZero (nonnegTwistingSheaf 𝒜 n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := ⟨(-n - 1).toNat, by omega⟩
  exact isZero_zero _

/-- Zero sections of two pieces of equal degree are heterogeneously equal. -/
theorem nonneg_heq_zero {d e : ℤ} (h : d = e) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} :
    HEq (0 : (nonnegTwistingSheaf 𝒜 d).val.obj U)
      (0 : (nonnegTwistingSheaf 𝒜 e).val.obj U) := by
  subst h
  rfl

/-- Multiplication in the algebra of nonnegative twists: multiplication of twists in
nonnegative degrees, and the zero map as soon as one of the two degrees is negative. -/
def nonnegTwistMul : ∀ i j : ℤ, SheafOfModules.BilinearMap (nonnegTwistingSheaf 𝒜 i)
    (nonnegTwistingSheaf 𝒜 j) (nonnegTwistingSheaf 𝒜 (i + j))
  | (m : ℕ), (k : ℕ) => twistMul 𝒜 (m : ℤ) (k : ℤ)
  | (_ : ℕ), .negSucc _ => zeroBilinear _ _ _
  | .negSucc _, _ => zeroBilinear _ _ _

/-- In nonnegative degrees the multiplication of nonnegative twists is the multiplication of
twists. -/
@[simp] theorem nonnegTwistMul_natCast (m k : ℕ) :
    nonnegTwistMul 𝒜 (m : ℤ) (k : ℤ) = twistMul 𝒜 (m : ℤ) (k : ℤ) := rfl

/-- In nonnegative degrees the product of nonnegative twists is the pointwise product of values. -/
@[simp] theorem nonnegTwistMul_val (m k : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (nonnegTwistingSheaf 𝒜 (m : ℤ)).val.obj U)
    (b : (nonnegTwistingSheaf 𝒜 (k : ℤ)).val.obj U) (x : U.unop) :
    ((nonnegTwistMul 𝒜 (m : ℤ) (k : ℤ)).app U a b).1 x = a.1 x * b.1 x := rfl

/-- In a negative first degree the multiplication of nonnegative twists vanishes. -/
theorem nonnegTwistMul_eq_zero_of_neg_left {i j : ℤ} (hi : i < 0)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (nonnegTwistingSheaf 𝒜 i).val.obj U) (b : (nonnegTwistingSheaf 𝒜 j).val.obj U) :
    (nonnegTwistMul 𝒜 i j).app U a b = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = Int.negSucc m := ⟨(-i - 1).toNat, by omega⟩
  rfl

/-- In a negative second degree the multiplication of nonnegative twists vanishes. -/
theorem nonnegTwistMul_eq_zero_of_neg_right {i j : ℤ} (hj : j < 0)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (nonnegTwistingSheaf 𝒜 i).val.obj U) (b : (nonnegTwistingSheaf 𝒜 j).val.obj U) :
    (nonnegTwistMul 𝒜 i j).app U a b = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
  cases i with
  | ofNat m => rfl
  | negSucc m => rfl

/-- The graded algebra `⨁_{m ≥ 0} 𝒪_P(m)` of nonnegative twists on `P = Proj A`. -/
@[stacks 0EKG "the graded algebra of nonnegative twists"]
def nonnegTwistAlgebra :
    SheafOfModules.GradedAlgebra (AlgebraicGeometry.Proj 𝒜).ringCatSheaf where
  piece := nonnegTwistingSheaf 𝒜
  mul := nonnegTwistMul 𝒜
  one := twistOne 𝒜
  mul_assoc i j k U x y z := by
    rcases lt_or_ge i 0 with hi | hi
    · have hA : (nonnegTwistMul 𝒜 (i + j) k).app U ((nonnegTwistMul 𝒜 i j).app U x y) z = 0 := by
        rw [nonnegTwistMul_eq_zero_of_neg_left 𝒜 hi U x y, map_zero, AddMonoidHom.zero_apply]
      have hB : (nonnegTwistMul 𝒜 i (j + k)).app U x ((nonnegTwistMul 𝒜 j k).app U y z) = 0 :=
        nonnegTwistMul_eq_zero_of_neg_left 𝒜 hi U x _
      rw [hA, hB]
      exact nonneg_heq_zero 𝒜 (add_assoc i j k)
    rcases lt_or_ge j 0 with hj | hj
    · have hA : (nonnegTwistMul 𝒜 (i + j) k).app U ((nonnegTwistMul 𝒜 i j).app U x y) z = 0 := by
        rw [nonnegTwistMul_eq_zero_of_neg_right 𝒜 hj U x y, map_zero, AddMonoidHom.zero_apply]
      have hB : (nonnegTwistMul 𝒜 i (j + k)).app U x ((nonnegTwistMul 𝒜 j k).app U y z) = 0 := by
        rw [nonnegTwistMul_eq_zero_of_neg_left 𝒜 hj U y z, map_zero]
      rw [hA, hB]
      exact nonneg_heq_zero 𝒜 (add_assoc i j k)
    rcases lt_or_ge k 0 with hk | hk
    · have hA : (nonnegTwistMul 𝒜 (i + j) k).app U ((nonnegTwistMul 𝒜 i j).app U x y) z = 0 :=
        nonnegTwistMul_eq_zero_of_neg_right 𝒜 hk U _ z
      have hB : (nonnegTwistMul 𝒜 i (j + k)).app U x ((nonnegTwistMul 𝒜 j k).app U y z) = 0 := by
        rw [nonnegTwistMul_eq_zero_of_neg_right 𝒜 hk U y z, map_zero]
      rw [hA, hB]
      exact nonneg_heq_zero 𝒜 (add_assoc i j k)
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, k = (q : ℤ) := ⟨k.toNat, by omega⟩
    refine twist_heq 𝒜 (add_assoc (m : ℤ) (p : ℤ) (q : ℤ)) fun s => ?_
    change x.1 s * y.1 s * z.1 s = x.1 s * (y.1 s * z.1 s)
    exact mul_assoc _ _ _
  one_mul i U x := by
    rcases lt_or_ge i 0 with hi | hi
    · rw [nonnegTwistMul_eq_zero_of_neg_right 𝒜 hi U _ x]
      refine (nonneg_heq_zero 𝒜 (zero_add i)).trans ?_
      exact heq_of_eq (eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 hi) x).symm
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
    refine twist_heq 𝒜 (zero_add (m : ℤ)) fun s => ?_
    change (1 : ModuleFiber (M := A) 𝒜 _) * x.1 s = x.1 s
    exact one_mul _
  mul_one i U x := by
    rcases lt_or_ge i 0 with hi | hi
    · rw [nonnegTwistMul_eq_zero_of_neg_left 𝒜 hi U x _]
      refine (nonneg_heq_zero 𝒜 (add_zero i)).trans ?_
      exact heq_of_eq (eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 hi) x).symm
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
    refine twist_heq 𝒜 (add_zero (m : ℤ)) fun s => ?_
    change x.1 s * (1 : ModuleFiber (M := A) 𝒜 _) = x.1 s
    exact mul_one _

/-- The `n`-th piece of the algebra of all integral twists is `𝒪(n)`. -/
@[simp] theorem integerTwistAlgebra_piece (n : ℤ) :
    (integerTwistAlgebra 𝒜).piece n = twistingSheaf 𝒜 n := rfl

/-- The multiplication of the algebra of all integral twists is `twistMul`. -/
@[simp] theorem integerTwistAlgebra_mul (i j : ℤ) :
    (integerTwistAlgebra 𝒜).mul i j = twistMul 𝒜 i j := rfl

/-- The `n`-th piece of the algebra of nonnegative twists is `nonnegTwistingSheaf 𝒜 n`. -/
@[simp] theorem nonnegTwistAlgebra_piece (n : ℤ) :
    (nonnegTwistAlgebra 𝒜).piece n = nonnegTwistingSheaf 𝒜 n := rfl

/-- The multiplication of the algebra of nonnegative twists is `nonnegTwistMul`. -/
@[simp] theorem nonnegTwistAlgebra_mul (i j : ℤ) :
    (nonnegTwistAlgebra 𝒜).mul i j = nonnegTwistMul 𝒜 i j := rfl

/-! ### Comparison of the two graded algebras -/

/-- In nonnegative degrees the piece of the algebra of nonnegative twists is the twisting sheaf. -/
@[stacks 0EKG "the homogeneous pieces in nonnegative degrees"]
def nonnegPieceIso {n : ℤ} (hn : 0 ≤ n) :
    (nonnegTwistAlgebra 𝒜).piece n ≅ twistingSheaf 𝒜 n :=
  eqToIso (by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    rfl)

/-- The degreewise comparison morphism: the identity in nonnegative degrees, and the zero
morphism out of the zero sheaf in negative degrees. -/
def nonnegToIntegerApp : ∀ n : ℤ, nonnegTwistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n
  | (_ : ℕ) => CategoryStruct.id _
  | .negSucc k =>
    (isZero_nonnegTwistingSheaf 𝒜 (Int.negSucc_lt_zero k)).to_ _

/-- A bilinear map of sheaves of modules vanishes on a zero first argument. -/
private theorem bilinear_zero_left {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R}
    (f : SheafOfModules.BilinearMap M N P) (U : Cᵒᵖ) (y : N.val.obj U) :
    f.app U 0 y = 0 :=
  DFunLike.congr_fun (map_zero (f.app U)) y

/-- A bilinear map of sheaves of modules vanishes on a zero second argument. -/
private theorem bilinear_zero_right {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R}
    (f : SheafOfModules.BilinearMap M N P) (U : Cᵒᵖ) (x : M.val.obj U) :
    f.app U x 0 = 0 := map_zero _

/-- Both sides of the multiplicativity equation vanish when one of the degrees is negative. -/
private theorem nonnegToIntegerApp_map_mul_of_neg {i j : ℤ} (h : i < 0 ∨ j < 0)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : (nonnegTwistingSheaf 𝒜 i).val.obj U) (y : (nonnegTwistingSheaf 𝒜 j).val.obj U) :
    (nonnegToIntegerApp 𝒜 (i + j)).val.app U ((nonnegTwistMul 𝒜 i j).app U x y) =
      (twistMul 𝒜 i j).app U ((nonnegToIntegerApp 𝒜 i).val.app U x)
        ((nonnegToIntegerApp 𝒜 j).val.app U y) := by
  rcases h with h | h
  · have hx : (nonnegToIntegerApp 𝒜 i).val.app U x = 0 := by
      rw [eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 h) x]
      exact map_zero _
    exact (congrArg (fun t => (nonnegToIntegerApp 𝒜 (i + j)).val.app U t)
      (nonnegTwistMul_eq_zero_of_neg_left 𝒜 h U x y)).trans <| (map_zero _).trans <|
      (bilinear_zero_left _ _ _).symm.trans <|
      congrArg (fun t => (twistMul 𝒜 i j).app U t ((nonnegToIntegerApp 𝒜 j).val.app U y)) hx.symm
  · have hy : (nonnegToIntegerApp 𝒜 j).val.app U y = 0 := by
      rw [eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 h) y]
      exact map_zero _
    exact (congrArg (fun t => (nonnegToIntegerApp 𝒜 (i + j)).val.app U t)
      (nonnegTwistMul_eq_zero_of_neg_right 𝒜 h U x y)).trans <| (map_zero _).trans <|
      (bilinear_zero_right _ _ _).symm.trans <|
      congrArg (fun t => (twistMul 𝒜 i j).app U ((nonnegToIntegerApp 𝒜 i).val.app U x) t) hy.symm

/-- The degreewise comparison morphisms preserve products of homogeneous sections. -/
theorem nonnegToIntegerApp_map_mul (i j : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : (nonnegTwistingSheaf 𝒜 i).val.obj U) (y : (nonnegTwistingSheaf 𝒜 j).val.obj U) :
    (nonnegToIntegerApp 𝒜 (i + j)).val.app U ((nonnegTwistMul 𝒜 i j).app U x y) =
      (twistMul 𝒜 i j).app U ((nonnegToIntegerApp 𝒜 i).val.app U x)
        ((nonnegToIntegerApp 𝒜 j).val.app U y) := by
  cases i with
  | negSucc m => exact nonnegToIntegerApp_map_mul_of_neg 𝒜 (.inl (Int.negSucc_lt_zero m)) U x y
  | ofNat m =>
    cases j with
    | negSucc k =>
      exact nonnegToIntegerApp_map_mul_of_neg 𝒜 (.inr (Int.negSucc_lt_zero k)) U x y
    | ofNat k => rfl

/-- The inclusion `⨁_{m ≥ 0} 𝒪_P(m) ⟶ ⨁_{m ∈ ℤ} 𝒪_P(m)` of graded algebras. -/
@[stacks 0EKG "the inclusion of the nonnegative twist algebra in the integral one"]
def nonnegToIntegerTwistAlgebra :
    SheafOfModules.GradedAlgebra.Hom (nonnegTwistAlgebra 𝒜) (integerTwistAlgebra 𝒜) where
  app := nonnegToIntegerApp 𝒜
  map_mul i j U x y := nonnegToIntegerApp_map_mul 𝒜 i j U x y

/-- In nonnegative degrees the inclusion of the two twist algebras is the identity. -/
@[stacks 0EKG "the inclusion is the identity on each nonnegative twist"]
theorem nonnegToIntegerTwistAlgebra_app_natCast (m : ℕ) :
    (nonnegToIntegerTwistAlgebra 𝒜).app (m : ℤ) = CategoryStruct.id _ := rfl

end Twist

/-! ### The two direct-image algebras of the cone -/

section ConeTwist

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The action of `ℕ` on `ℤ` by addition of the cast. -/
local instance instVAddNatInt₂ : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

section Cone

variable {B : Type u} {τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

variable {𝒜 ℬ} (c : ProjAndSpec.ConeData 𝒜 ℬ)

/-- The direct-image algebra `π_* 𝒪_L` of the cone. -/
@[stacks 0EKG "the direct-image algebra of the cone"]
def coneAlgebra : Stacks.RelativeSpec.AlgebraSheaf (AlgebraicGeometry.Proj 𝒜) :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebra (ProjAndSpec.pi c)

/-- The direct-image algebra `(π|_U)_* 𝒪_U` of the punctured cone, the part of `L` lying over
`U = X ∖ V(A₊)`. -/
@[stacks 0EKG "the direct-image algebra of the punctured cone"]
def puncturedConeAlgebra : Stacks.RelativeSpec.AlgebraSheaf (AlgebraicGeometry.Proj 𝒜) :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
    ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)

/-- Restriction of functions from the cone to the punctured cone, as a morphism of
`𝒪_P`-algebras. -/
@[stacks 0EKG "the inclusion of the two direct-image algebras"]
def coneToPuncturedConeAlgebra : coneAlgebra c ⟶ puncturedConeAlgebra c :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux (ProjAndSpec.pi c)
    (ProjAndSpec.openUInL c).ι

/-- Over an open of `P` the restriction map of the two direct-image algebras is the canonical map
on functions induced by the open immersion of the punctured cone. -/
@[stacks 0EKG "the restriction formula for the inclusion of the two algebras"]
theorem coneToPuncturedConeAlgebra_app (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (hle : ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c) ⁻¹ᵁ U ≤
      (ProjAndSpec.openUInL c).ι ⁻¹ᵁ (ProjAndSpec.pi c ⁻¹ᵁ U)) :
    (coneToPuncturedConeAlgebra c).right.hom.app (op U) =
      (ProjAndSpec.openUInL c).ι.appLE (ProjAndSpec.pi c ⁻¹ᵁ U)
        (((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c) ⁻¹ᵁ U) hle := by
  have h := Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux_app (ProjAndSpec.pi c)
    (ProjAndSpec.openUInL c).ι ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c) rfl U hle
  simpa [coneToPuncturedConeAlgebra, coneAlgebra, puncturedConeAlgebra] using h

end Cone

end ConeTwist

section TwistZero

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The action of `ℕ` on `ℤ` by addition of the cast. -/
local instance instVAddNatInt₃ : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-! ### The degree-zero piece is the structure sheaf -/

/-- The value of a section of the structure sheaf, read in the localizations of `A`, is a local
fraction of degree zero. -/
theorem val_mem_moduleSections (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    (fun x : U => HomogeneousLocalization.val (r.1 x)) ∈
      moduleSections 𝒜 (twistGrading (S := A) 𝒜 0) U := by
  intro x
  obtain ⟨V, hxV, iV, n, ⟨num, hnum⟩, ⟨den, hden⟩, hnin, hr⟩ := r.2 x
  exact ⟨V, hxV, iV, n, num, den, mem_twistGrading_of_mem 𝒜 (by simp) hnum, hden, hnin,
    fun y => (congrArg HomogeneousLocalization.val (hr y)).trans
      (HomogeneousLocalization.val_mk _)⟩

/-- A section of the structure sheaf, read in the localizations of `A`, as a section of the
untwisted sheaf. -/
@[stacks 0EKG "the comparison of the degree-zero piece with the structure sheaf"]
def structureSheafToTwistZero (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    (twistingSheaf 𝒜 0).val.obj (op U) :=
  ⟨fun x => HomogeneousLocalization.val (r.1 x), val_mem_moduleSections 𝒜 U r⟩

/-- The value of `structureSheafToTwistZero 𝒜 U r` at a point is the value of `r` there, read in
the localization of `A`. -/
@[simp] theorem structureSheafToTwistZero_val (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (x : U) :
    (structureSheafToTwistZero 𝒜 U r).1 x = HomogeneousLocalization.val (r.1 x) := rfl

/-- The comparison carries the unit section of the structure sheaf to the unit section of the
untwisted sheaf. -/
@[stacks 0EKG "the degree-zero comparison preserves the unit"]
theorem structureSheafToTwistZero_one (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    structureSheafToTwistZero 𝒜 U 1 = (twistOne 𝒜).eval (op U) :=
  twistSection_ext 𝒜 fun _ => HomogeneousLocalization.val_one

/-- The comparison is multiplicative, the product on the right being the degree-zero part of the
multiplication of twists. -/
@[stacks 0EKG "the degree-zero comparison is multiplicative"]
theorem structureSheafToTwistZero_mul (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r r' : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    structureSheafToTwistZero 𝒜 U (r * r') =
      twistMulSection 𝒜 0 0 (op U) (structureSheafToTwistZero 𝒜 U r)
        (structureSheafToTwistZero 𝒜 U r') :=
  twistSection_ext 𝒜 fun _ => HomogeneousLocalization.val_mul _ _

/-- The comparison commutes with restriction to a smaller open. -/
theorem structureSheafToTwistZero_restrict {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) :
    structureSheafToTwistZero 𝒜 V
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.map i.op r) =
      (twistingSheaf 𝒜 0).val.map i.op (structureSheafToTwistZero 𝒜 U r) := rfl

/-- The comparison of the structure sheaf with `𝒪_P(0)` is injective over every open. -/
@[stacks 0EKG "injectivity of the degree-zero comparison"]
theorem structureSheafToTwistZero_injective (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Function.Injective (structureSheafToTwistZero 𝒜 U) := by
  intro r r' h
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  exact congrFun (Subtype.ext_iff.mp h) x

/-- The comparison of the structure sheaf with `𝒪_P(0)` is surjective over every open. -/
@[stacks 0EKG "surjectivity of the degree-zero comparison"]
theorem structureSheafToTwistZero_surjective (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Function.Surjective (structureSheafToTwistZero 𝒜 U) := by
  classical
  intro a
  have hmem : ∀ {n : ℕ} {m : A}, m ∈ twistGrading (S := A) 𝒜 0 (n : ℤ) → m ∈ 𝒜 n := fun h => by
    simpa using mem_of_mem_twistGrading 𝒜 (by omega) h
  have key : ∀ x : U, ∃ h : HomogeneousLocalization.AtPrime 𝒜
      x.1.asHomogeneousIdeal.toIdeal, HomogeneousLocalization.val h = a.1 x := by
    intro x
    obtain ⟨V, hxV, iV, n, m, s, hm, hs, hns, hav⟩ := a.2 x
    exact ⟨HomogeneousLocalization.mk ⟨n, ⟨m, hmem hm⟩, ⟨s, hs⟩, hns ⟨x.1, hxV⟩⟩,
      (HomogeneousLocalization.val_mk _).trans (hav ⟨x.1, hxV⟩).symm⟩
  choose r hr using key
  have hrmem : r ∈ ProjectiveSpectrum.StructureSheaf.sectionsSubring (op U) := by
    intro x
    obtain ⟨V, hxV, iV, n, m, s, hm, hs, hns, hav⟩ := a.2 x
    refine ⟨V, hxV, iV, n, ⟨m, hmem hm⟩, ⟨s, hs⟩, hns, fun y => ?_⟩
    refine HomogeneousLocalization.val_injective _ ?_
    rw [HomogeneousLocalization.val_mk]
    exact (hr (iV y)).trans (hav y)
  exact ⟨⟨r, hrmem⟩, twistSection_ext 𝒜 fun x => hr x⟩

/-- The degree-zero piece of the twist algebra is the structure sheaf: over every open the
comparison is a bijection. -/
@[stacks 0EKG "the degree-zero piece is the structure sheaf"]
theorem structureSheafToTwistZero_bijective (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Function.Bijective (structureSheafToTwistZero 𝒜 U) :=
  ⟨structureSheafToTwistZero_injective 𝒜 U, structureSheafToTwistZero_surjective 𝒜 U⟩

end TwistZero

end Stacks.AlgebraicGeometry.ProjConeTwist

end
