module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtension
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.Constructed

/-!
# The complex `⨁ₙ Mₙ[n]` over `k[x][ε]` and its derived Hom out of `k[x]`

Let `k` be a field, `A = k[x][ε]` with `ε² = 0`, `B = A/(ε) = k[x]` and `Mₙ = A/(ε, xⁿ)`. The
example [Stacks, Tag 0A9M] considers the object `K = ⨁ₙ Mₙ[n]` of `D(A)` and computes
`H⁰(RHom(B, K))`. This file carries out that computation in the derived category of modules, at
an arbitrary chosen model of the derived categories involved:

* the canonical map from the direct sum `K = ⨁ₙ Mₙ₊₁[n+1]` to the direct product `∏ₙ Mₙ₊₁[n+1]`
  is an isomorphism in `D(A)` (by [Stacks, Tag 0A5L] and [Stacks, Tag 07KC], every cohomology
  object of either side is the cohomology of a single summand);
* each cohomology module of `K` is a finite `A`-module annihilated by a power of `x`;
* `H⁰(RHom(B, K)) = Ext⁰_A(B, K) = ∏ₙ Ext^{n+1}_A(B, Mₙ₊₁) = ∏ₙ Mₙ₊₁` as `A`-modules, using
  [Stacks, Tag 0A71] for the first equality, `K = ∏` for the second and the periodic resolution
  of `B` (`Stacks.SquareZeroExt.coefficientModule_ext`) for the third.

The summand `M₀ = 0` of the source is dropped, so the sum is indexed by `n + 1` for `n : ℕ`.

## Main definitions

* `Stacks.SquareZeroExt.shiftedCoefficientModule`: the object `Mₙ₊₁[n+1]` of `D(A)`.
* `Stacks.SquareZeroExt.coefficientSum`: `K = ⨁ₙ Mₙ₊₁[n+1]`.
* `Stacks.SquareZeroExt.coefficientSumToProduct`: the canonical map `⨁ₙ Mₙ₊₁[n+1] ⟶ ∏ₙ Mₙ₊₁[n+1]`.
* `Stacks.SquareZeroExt.derivedHomCoefficientSumHomologyZero`: `H⁰(RHom(B, K)) ≃ ∏ₙ Mₙ₊₁`.

## Main results

* `Stacks.SquareZeroExt.isIso_coefficientSumToProduct`: the sum is the product.
* `Stacks.SquareZeroExt.finite_homology_coefficientSum`: the cohomology of `K` is finite.
* `Stacks.SquareZeroExt.exists_xpow_smul_homology_coefficientSum`: every cohomology class of `K`
  is annihilated by a power of `x`.

## References

* [Stacks Project, Tag 0A9M](https://stacks.math.columbia.edu/tag/0A9M)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace Stacks.SquareZeroExt

/-! ### Generalities -/

section General

/-- In a coproduct of a family which vanishes away from `i`, the inclusion of the `i`-th summand
is an isomorphism. -/
theorem isIso_cofan_inj_of_isZero {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type*}
    {F : J → C} (c : Cofan F) (hc : IsColimit c) (i : J)
    (h : ∀ j, j ≠ i → IsZero (F j)) : IsIso (c.inj i) := by
  classical
  let p := Cofan.IsColimit.desc hc fun j => if e : j = i then eqToHom (congrArg F e) else 0
  refine ⟨⟨p, ?_, ?_⟩⟩
  · simp [p, Cofan.IsColimit.fac]
  · refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    by_cases hj : j = i
    · subst j
      simp [p, ← Category.assoc, Cofan.IsColimit.fac]
    · exact (h j hj).eq_of_src _ _

/-- In a product of a family which vanishes away from `i`, the projection onto the `i`-th factor
is an isomorphism. -/
theorem isIso_fan_proj_of_isZero {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type*}
    {F : J → C} (c : Fan F) (hc : IsLimit c) (i : J)
    (h : ∀ j, j ≠ i → IsZero (F j)) : IsIso (c.proj i) := by
  classical
  let p := Fan.IsLimit.lift hc fun j => if e : i = j then eqToHom (congrArg F e) else 0
  refine ⟨⟨p, ?_, ?_⟩⟩
  · refine Fan.IsLimit.hom_ext hc _ _ fun j => ?_
    by_cases hj : j = i
    · subst j
      simp [p, Category.assoc, Fan.IsLimit.fac]
    · exact (h j hj).eq_of_tgt _ _
  · simp [p, Fan.IsLimit.fac]

/-- Morphisms into a product in an `R`-linear category are families of morphisms into the
factors, `R`-linearly. -/
def homPiLinearEquiv (R : Type*) [Semiring R] {C : Type*} [Category* C] [Preadditive C]
    [Linear R C] {J : Type*} (X : C) (F : J → C) [HasProduct F] :
    (X ⟶ ∏ᶜ F) ≃ₗ[R] ∀ j, X ⟶ F j where
  toFun f j := f ≫ Pi.π F j
  invFun := Pi.lift
  left_inv f := Pi.hom_ext _ _ fun j => by simp
  right_inv f := funext fun j => by simp
  map_add' f g := funext fun j => by simp
  map_smul' r f := funext fun j => by simp

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The cohomology of `M[0]⟦n⟧` in degree `q` is the cohomology of `M[0]` in degree `n + q`. -/
def homologyShiftSingleIso (M : C) (n q : ℤ) :
    (DerivedCategory.homologyFunctor C q).obj (((DerivedCategory.singleFunctor C 0).obj M)⟦n⟧) ≅
      (DerivedCategory.homologyFunctor C (n + q)).obj ((DerivedCategory.singleFunctor C 0).obj M) :=
  ((DerivedCategory.homologyFunctor C 0).shiftIso n q (n + q) rfl).app _

/-- The cohomology of `M[0]` vanishes in every degree `q ≠ 0`. -/
theorem isZero_homology_singleFunctor (M : C) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C q).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) := by
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact DerivedCategory.isZero_of_isGE _ 0 q hq
  · exact DerivedCategory.isZero_of_isLE _ 0 q hq

/-- The cohomology of `M[0]⟦n⟧` in degree `-n` is `M`. -/
def homologyShiftSingleSelfIso (M : C) {n q : ℤ} (h : n + q = 0) :
    (DerivedCategory.homologyFunctor C q).obj (((DerivedCategory.singleFunctor C 0).obj M)⟦n⟧) ≅
      M :=
  homologyShiftSingleIso M n q ≪≫
    eqToIso (congrArg (fun d => (DerivedCategory.homologyFunctor C d).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) h) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M

end General

/-! ### The objects `Mₙ₊₁[n+1]` and their direct sum -/

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (ModuleCat.{u} (sourceRing k))]

/-- The object `Mₙ₊₁[n+1]` of `D(A)`, where `A = k[x][ε]` and `Mₙ₊₁ = A/(ε, xⁿ⁺¹)`. -/
abbrev shiftedCoefficientModule (n : ℕ) : DerivedCategory (ModuleCat.{u} (sourceRing k)) :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} (sourceRing k)) 0).obj
    (coefficientModule k (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧

/-- Modules over a ring have exact countable direct sums. -/
theorem moduleCat_hasExactCountableDirectSums (R : Type u) [Ring R] :
    HasExactCountableDirectSums (ModuleCat.{u} R) :=
  ⟨⟨fun _ _ => inferInstance⟩, fun _ _ => ⟨inferInstance, inferInstance⟩⟩

/-- The derived category `D(R)` of modules over a ring has countable coproducts. -/
instance hasCoproductsOfShape_nat_derivedCategory (R : Type u) [Ring R]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] :
    HasCoproductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  have := derivedCategory_hasCountableCoproducts (ModuleCat.{u} R)
    (moduleCat_hasExactCountableDirectSums R)
  inferInstance

/-- The derived category `D(R)` of modules over a ring has countable products. -/
instance hasProductsOfShape_nat_derivedCategory (R : Type u) [Ring R]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_nat

/-- The cohomology functors of `D(R)` commute with countable direct sums. -/
theorem preservesColimitsOfShape_homologyFunctor (R : Type u) [Ring R]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] (q : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) := by
  let h := moduleCat_hasExactCountableDirectSums R
  have := h.hasCoproducts
  have : HasColimitsOfShape (Discrete ℕ) (ModuleCat.{u} R) := h.hasCoproducts.1 ℕ
  have : HasColimitsOfShape (Discrete ℕ) (CochainComplex (ModuleCat.{u} R) ℤ) :=
    HomologicalComplex.instHasColimitsOfShape
  have := derivedCategory_Q_preservesCoproductsOfShape (ModuleCat.{u} R) h ℕ
  have := homologicalComplex_homologyFunctor_preservesCoproducts (ModuleCat.{u} R) h ℕ q
  have : PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors _ q).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) ℕ

/-- The cohomology functors of `D(R)` commute with countable direct products. -/
theorem preservesLimitsOfShape_homologyFunctor (R : Type u) [Ring R]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] (q : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) :=
  Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison _ fun X =>
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X q

/-- **The object `K = ⨁ₙ Mₙ[n]` of [Stacks, Tag 0A9M]**, as an object of `D(A)`; the summand
`M₀ = 0` is dropped. -/
abbrev coefficientSum : DerivedCategory (ModuleCat.{u} (sourceRing k)) :=
  ∐ shiftedCoefficientModule k

/-- The canonical map from the direct sum `⨁ₙ Mₙ₊₁[n+1]` to the direct product. -/
def coefficientSumToProduct : coefficientSum k ⟶ ∏ᶜ shiftedCoefficientModule k :=
  Sigma.desc fun i => Pi.lift fun j =>
    if h : i = j then eqToHom (congrArg (shiftedCoefficientModule k) h) else 0

/-- The `n`-th component of `Stacks.SquareZeroExt.coefficientSumToProduct` on the `n`-th summand
is the identity of `Mₙ₊₁[n+1]`. -/
@[reassoc (attr := simp)]
theorem ι_coefficientSumToProduct_π (n : ℕ) :
    Sigma.ι (shiftedCoefficientModule k) n ≫ coefficientSumToProduct k ≫
      Pi.π (shiftedCoefficientModule k) n = 𝟙 _ := by
  simp [coefficientSumToProduct]

/-- The cohomology of `Mₙ₊₁[n+1]` in degree `q` vanishes unless `n + 1 + q = 0`. -/
private theorem isZero_homology_shiftedCoefficientModule_of_ne (q : ℤ) (n : ℕ)
    (h : ((n + 1 : ℕ) : ℤ) + q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q).obj
      (shiftedCoefficientModule k n)) :=
  (isZero_homology_singleFunctor _ h).of_iso (homologyShiftSingleIso _ _ q)

/-- `Mₙ₊₁[n+1]` has cohomology only in degree `-(n+1)`. -/
theorem isZero_homology_shiftedCoefficientModule (q : ℤ) (j : ℕ) (hj : j ≠ (-q - 1).toNat) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q).obj
      (shiftedCoefficientModule k j)) :=
  isZero_homology_shiftedCoefficientModule_of_ne k q j (by omega)

/-- On `H^q`, the inclusion of the summand `Mₙ₊₁[n+1]` with `n + 1 = -q` into `⨁ₙ Mₙ₊₁[n+1]` is
an isomorphism. -/
theorem isIso_homology_map_ι (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q).map
      (Sigma.ι (shiftedCoefficientModule k) (-q - 1).toNat)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q
  have := preservesColimitsOfShape_homologyFunctor (sourceRing k) q
  exact isIso_cofan_inj_of_isZero (Cofan.mk _ fun j => H.map (Sigma.ι _ j))
    (Cofan.isColimitMapCoconeEquiv H _ _ (isColimitOfPreserves H (coproductIsCoproduct _))) _
    fun j hj => isZero_homology_shiftedCoefficientModule k q j hj

/-- **The direct sum is the direct product**: the canonical map `⨁ₙ Mₙ₊₁[n+1] ⟶ ∏ₙ Mₙ₊₁[n+1]`
is an isomorphism in `D(A)`, the equality `⨁ Mₙ[n] = ∏ Mₙ[n]` of [Stacks, Tag 0A9M]. Both sides
have, in degree `q`, the cohomology of the single summand placed in degree `q`, because cohomology
commutes with countable direct sums and products in `D(A)` ([Stacks, Tag 0A5L],
[Stacks, Tag 07KC]). -/
theorem isIso_coefficientSumToProduct : IsIso (coefficientSumToProduct k) := by
  refine (DerivedCategory.isIso_iff _ _).mpr fun q => ?_
  let F := shiftedCoefficientModule k
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q
  let i := (-q - 1).toNat
  have := preservesLimitsOfShape_homologyFunctor (sourceRing k) q
  have hι : IsIso (H.map (Sigma.ι F i)) := isIso_homology_map_ι k q
  have hπ : IsIso (H.map (Pi.π F i)) :=
    isIso_fan_proj_of_isZero (Fan.mk _ fun j => H.map (Pi.π F j))
      (Fan.isLimitMapConeEquiv H F _ (isLimitOfPreserves H (productIsProduct F))) i
      fun j hj => isZero_homology_shiftedCoefficientModule k q j hj
  have : IsIso (H.map (Sigma.ι F i) ≫ H.map (coefficientSumToProduct k) ≫ H.map (Pi.π F i)) := by
    rw [← H.map_comp, ← H.map_comp, ι_coefficientSumToProduct_π, H.map_id]
    infer_instance
  have : IsIso (H.map (coefficientSumToProduct k) ≫ H.map (Pi.π F i)) :=
    IsIso.of_isIso_comp_left (H.map (Sigma.ι F i)) _
  exact IsIso.of_isIso_comp_right _ (H.map (Pi.π F i))

/-! ### The cohomology of `K` -/

/-- **The cohomology of `K = ⨁ₙ Mₙ[n]` is finite**: in each degree it is a single `Mₙ` or zero. -/
theorem finite_homology_coefficientSum (q : ℤ) :
    Module.Finite (sourceRing k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q).obj
        (coefficientSum k)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q
  let i := (-q - 1).toNat
  have := isIso_homology_map_ι k q
  let e := asIso (H.map (Sigma.ι (shiftedCoefficientModule k) i))
  suffices Module.Finite (sourceRing k) (H.obj (shiftedCoefficientModule k i)) from
    Module.Finite.equiv e.toLinearEquiv
  by_cases h : ((i + 1 : ℕ) : ℤ) + q = 0
  · exact Module.Finite.equiv (homologyShiftSingleSelfIso _ h).symm.toLinearEquiv
  · have : Subsingleton (H.obj (shiftedCoefficientModule k i)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_homology_shiftedCoefficientModule_of_ne k q i h)
    infer_instance

/-- **Every cohomology class of `K = ⨁ₙ Mₙ[n]` is annihilated by a power of `x`**, the power
depending on the class: in degree `-n` the cohomology is `Mₙ`, annihilated by `xⁿ`. -/
theorem exists_xpow_smul_homology_coefficientSum (q : ℤ)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q).obj
      (coefficientSum k)) :
    ∃ n : ℕ, (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n • m = 0 := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (sourceRing k)) q
  let i := (-q - 1).toNat
  have := isIso_homology_map_ι k q
  let f := H.map (Sigma.ι (shiftedCoefficientModule k) i)
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance m
  suffices ∃ n : ℕ,
      (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n • y = 0 by
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by rw [← map_smul, hn, map_zero]⟩
  by_cases h : ((i + 1 : ℕ) : ℤ) + q = 0
  · let e := homologyShiftSingleSelfIso (coefficientModule k (i + 1)) h
    refine ⟨i + 1, (ModuleCat.mono_iff_injective e.hom).mp inferInstance ?_⟩
    rw [map_smul, map_zero]
    exact coefficientModule_xpow_smul k (i + 1) _
  · exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_shiftedCoefficientModule_of_ne k q i h)).elim _ _⟩

/-! ### `H⁰(RHom(B, K)) = ∏ₙ Mₙ` -/

variable [HasDerivedCategory.{w'} (ModuleCat.{u} (Polynomial k))]

/-- `B = k[x]` with its module structure restricted along `A ⟶ B` is the residue module
`Stacks.SquareZeroExt.residue`. The module `ULift B` is the free rank-one `B`-module in which the
comparison of [Stacks, Tag 0A71] is stated. -/
def restrictScalarsULiftIsoResidue :
    (ModuleCat.restrictScalars (proj (Polynomial k))).obj
        (ModuleCat.of (Polynomial k) (ULift.{u} (Polynomial k))) ≅
      residue (Polynomial k) :=
  LinearEquiv.toModuleIso
    { toFun := ULift.down
      invFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **The degree-zero cohomology of `RHom(B, K)` is `∏ₙ Mₙ`**, `A`-linearly, for
`K = ⨁ₙ Mₙ[n]` the object of [Stacks, Tag 0A9M]. This is the chain
`H⁰(RHom(B, K)) = Ext⁰_A(B, K) = ∏ₙ Ext^{n+1}_A(B, Mₙ₊₁) = ∏ₙ Mₙ₊₁` of the source: the first
equality is [Stacks, Tag 0A71] (`Dualizing.derivedHomHomologyLinearEquivExt`), the second is
`K = ∏ₙ Mₙ₊₁[n+1]` (`Stacks.SquareZeroExt.isIso_coefficientSumToProduct`) and the third is the
periodic resolution of `B` (`Stacks.SquareZeroExt.coefficientModule_ext`).

The left side is restricted from `B` to `A`, which is how [Stacks, Tag 0A71] reads it. -/
def derivedHomCoefficientSumHomologyZero :
    (ModuleCat.restrictScalars (proj (Polynomial k))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
          ((Dualizing.AnyModel.derivedHom.{u, u, u, w, w'} (proj (Polynomial k))).obj
            (coefficientSum k))) ≃ₗ[sourceRing k]
      ∀ n : ℕ, coefficientModule k (n + 1) :=
  have := isIso_coefficientSumToProduct k
  ((Dualizing.derivedHomHomologyLinearEquivExt.{u, u, w, w'} (proj (Polynomial k))).linearEquiv
    (coefficientSum k) 0).trans <|
  (Linear.homCongr (sourceRing k)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (sourceRing k)) 0).mapIso
      (restrictScalarsULiftIsoResidue k))
    ((shiftFunctorZero _ ℤ).app (coefficientSum k) ≪≫
      asIso (coefficientSumToProduct k))).trans <|
  (homPiLinearEquiv (sourceRing k) _ (shiftedCoefficientModule k)).trans <|
  LinearEquiv.piCongrRight fun n =>
    (Abelian.Ext.homLinearEquiv (R := sourceRing k)).symm.trans
      (coefficientModule_ext k (n + 1) (n + 1))

/-- **`H⁰(RHom(B, K))` is not power torsion**: it contains an element annihilated by no power of
`x`, whereas every cohomology class of `K` is annihilated by one
(`Stacks.SquareZeroExt.exists_xpow_smul_homology_coefficientSum`). The element is
`(1, 1, 1, …)` of `∏ₙ Mₙ₊₁`. -/
theorem exists_forall_xpow_smul_ne_zero_derivedHom :
    ∃ m : (DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((Dualizing.AnyModel.derivedHom.{u, u, u, w, w'} (proj (Polynomial k))).obj
          (coefficientSum k)),
      ∀ n : ℕ, (Polynomial.X : Polynomial k) ^ n • m ≠ 0 := by
  obtain ⟨m, hm⟩ := coefficientModuleProduct_not_powerTorsion k
  let e := derivedHomCoefficientSumHomologyZero k
  refine ⟨e.symm m, fun n hn => hm n ?_⟩
  have h : (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n • e.symm m = 0 :=
    hn
  simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using congrArg e h

end Stacks.SquareZeroExt

end
