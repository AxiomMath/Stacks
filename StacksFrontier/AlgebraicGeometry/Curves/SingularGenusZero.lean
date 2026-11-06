module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.FiniteStalk
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationClosedFibre
public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZeroAlgebra
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.StructureSheafMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkLength
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.PrepareDeltaInvariant

/-!
# Singular proper curves of genus zero

Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`. [Stacks, Tag 0DJB] says that if
`X` is singular of genus zero, then `X` is obtained from a projective line over a nontrivial
finite extension `k'` of `k` by replacing a `k'`-rational point by a `k`-rational point: the
normalization `ν : X' ⟶ X` is `𝐏¹_{k'}`, it is an isomorphism away from one point `x' ↦ x`, and
`ν_* 𝒪_{X'} / 𝒪_X` is the skyscraper `κ(x') / κ(x) = k' / k` at `x`.

## The argument

Write `k' = H⁰(X', 𝒪_{X'})`, a finite field extension of `k` of degree `n`, and
`𝒬 = ν_* 𝒪_{X'} / 𝒪_X`, which is supported at the singular points.

* The long exact sequence of `0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X'} ⟶ 𝒬 ⟶ 0`, with `H¹(X, 𝒪_X) = 0` and
  `H¹(X, 𝒬) = 0`, gives `H¹(X', 𝒪_{X'}) = 0` and `dim_k H⁰(X, 𝒬) = n - 1`
  (`AlgebraicGeometry.normalization_cohomology_of_genus_eq_zero`).
* `H⁰(X, 𝒬)` is the sum of the stalks `𝒬_s = B_s / A_s`, `A_s = 𝒪_{X, s}`,
  `B_s = (ν_* 𝒪_{X'})_s` (`AlgebraicGeometry.cohomologyOverFieldZeroLinearEquivPiStalk`), and
  each singular point contributes at least `n / 2`
  (`Stacks.Curves.finrank_le_two_mul_finrank_quotient_range`). So there is exactly one singular
  point `x`, with `dim_k 𝒬_x = n - 1`
  (`AlgebraicGeometry.exists_singularLocus_eq_singleton`).
* At `x` the equality case
  (`Stacks.Curves.finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq`)
  gives `κ(x) = k`, `B_x` local with residue field `k'` and maximal ideal `𝔪_x B_x ⊆ A_x`; hence
  one point `x'` over `x`, `κ(x') = k'`, and `𝒬_x = κ(x') / κ(x)`
  (`AlgebraicGeometry.nonempty_stalk_normalizationQuotient_linearEquiv`).
* `X'` is a normal proper curve of genus zero over `k'` with a `k'`-rational point, which carries
  an invertible module of degree one
  (`AlgebraicGeometry.exists_invertibleCurveDegree_eq_one_of_gcd` at the single point `x'`), hence
  is `𝐏¹_{k'}` (`AlgebraicGeometry.exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one`).

The source bounds the dimension of the image of `𝒪_X(U)` in `End_k(H⁰(X, 𝒬))` by `n - 1` as "a
property of commutative subalgebras of matrix algebras", which is false in general (Schur's bound
is `⌊m² / 4⌋ + 1`); the conductor is not used here, see
`StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZeroAlgebra`.

## Main results

* `AlgebraicGeometry.exists_projectiveLine_normalization_of_genus_eq_zero`: **[Stacks, Tag
  0DJB]**, all six clauses.
* `AlgebraicGeometry.exists_singularLocus_eq_singleton`: such a curve has one singular point.
* `AlgebraicGeometry.normalization_stalk_count`: the dimension count at a singular point.
* `AlgebraicGeometry.cohomologyOverFieldZeroLinearEquivPiStalk`: `H⁰(X, ℱ) = ⨁_{x ∈ Supp ℱ} ℱ_x`
  `k`-linearly, for `ℱ` coherent with zero-dimensional support.

## Implementation notes

The normalization is `AlgebraicGeometry.normalizationOverField k f`, the quotient `𝒬` is
`Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationQuotient` and the skyscraper is
`Stacks.AlgebraicGeometry.NormalizationQuotient.skyscraperModule`, as in [Stacks, Tag 0C1R]. The
field `k'` is the type of global sections `Γ(X', ⊤)` with the field structure of
[Stacks, Tag 0C6P], and the structure morphism `X' ⟶ Spec k'` is `X'.toSpecΓ`. A rational point
is a section of the structure morphism; the one through a point with residue field `k` is
`Spec k ≅ Spec κ(x) ⟶ X` (`AlgebraicGeometry.fromSpecResidueField_comp_eq_id_of_bijective`).

## References

* [Stacks Project, Tag 0DJB](https://stacks.math.columbia.edu/tag/0DJB)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.NormalizationQuotient
open Stacks.AlgebraicGeometry
  (NormalizationQuotientDirectSum.isClosed_singleton_of_not_mem_regularLocus
    NormalizationQuotientDirectSum.normalizationQuotientIsoCoproductSkyscraper
    NormalizationQuotientDirectSum.mem_regularLocus_of_mem_genericPoints)
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The residue field at a closed point of a scheme locally of finite type over `k` is a finite
extension of `k`** (Zariski's lemma), for the `k`-algebra structure through the structure
morphism. -/
theorem finite_residueField_over_field_of_isClosed [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have : IsClosedImmersion (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_isClosedImmersion.mp hx
    exact ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp inferInstance).2
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (X.residueField x) := by
    show RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- **A point with residue field `k` is a `k`-rational point.** If the residue field of `X` at `x`
is `k`, through the structure morphism, then `Spec k ≅ Spec κ(x) ⟶ X` is a section of
`f : X ⟶ Spec k`. -/
theorem fromSpecResidueField_comp_eq_id_of_bijective (x : X)
    (h : Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom) :
    (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ h).symm.toRingHom) ≫
      X.fromSpecResidueField x) ≫ f = 𝟙 _ := by
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  refine (congrArg (fun t => (t ≫ f.residueFieldMap x) ≫ CommRingCat.ofHom
    (RingEquiv.ofBijective _ h).symm.toRingHom)
    (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (f x))).trans ?_
  ext c
  show (RingEquiv.ofBijective _ h).symm
    ((f.residueFieldMap x) ((Spec (.of k)).Γevaluation (f x) ((Scheme.ΓSpecIso (.of k)).inv c))) = c
  rw [Scheme.Γevaluation_naturality_apply]
  exact (RingEquiv.ofBijective _ h).symm_apply_apply c

/-- On a global section, the evaluation at a point `y` of the stalk of `ν_* 𝒪_{X^ν}` is the value
of the section at `y`. -/
theorem normalizationFiberResidueMap_germ_top
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (y : {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x})
    (a : Γ(Scheme.normalizationScheme X hX, ⊤)) :
    normalizationFiberResidueMap X hX x y
        (((Scheme.normalization X hX).base _*
          (Scheme.normalizationScheme X hX).presheaf).germ ⊤ x trivial a) =
      (Scheme.normalizationScheme X hX).Γevaluation y.1 a := by
  obtain ⟨y, rfl⟩ := y
  show (Scheme.normalizationScheme X hX).residue y
      ((Scheme.normalizationScheme X hX).presheaf.stalkPushforward CommRingCat
        (Scheme.normalization X hX).base y
        (((Scheme.normalization X hX).base _*
          (Scheme.normalizationScheme X hX).presheaf).germ ⊤ _ trivial a)) = _
  exact congrArg (fun φ => ((φ ≫ (Scheme.normalizationScheme X hX).residue y).hom a))
    (TopCat.Presheaf.stalkPushforward_germ CommRingCat (Scheme.normalization X hX).base
      (Scheme.normalizationScheme X hX).presheaf ⊤ y trivial)

/-- **The fibre of the normalization over a point whose pushforward stalk is local is one
point.** If the extension `𝔪_x B` of the maximal ideal of `A = 𝒪_{X, x}` to the integral
extension `B = (ν_* 𝒪_{X^ν})_x` is maximal, then exactly one point `x'` of `X^ν` lies over `x`,
and `κ(x') ≅ B / 𝔪_x B` compatibly with the evaluation of germs at `x'`. -/
theorem existsUnique_normalization_fiber_of_isMaximal
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    [IsFinite (Scheme.normalization X hX)]
    (hmax : (letI := normalizationPushforwardStalkAlgebra X hX x
      Ideal.map (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).IsMaximal) :
    letI := normalizationPushforwardStalkAlgebra X hX x
    ∃ y : {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x},
      (∀ z : {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x}, z = y) ∧
      ∃ e : (Scheme.normalizationScheme X hX).residueField y.1 ≃+*
          (normalizationPushforwardStalk X hX x ⧸
            Ideal.map (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x))
              (IsLocalRing.maximalIdeal (X.presheaf.stalk x))),
        e.toRingHom.comp (normalizationFiberResidueMap X hX x y) = Ideal.Quotient.mk _ := by
  let := normalizationPushforwardStalkAlgebra X hX x
  set mB := Ideal.map (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have : Module.Finite (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    Stacks.GlueSquishFactor.module_finite_stalk_pushforward (Scheme.normalization X hX) x
  have : Algebra.IsIntegral (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    Algebra.IsIntegral.of_finite _ _
  have huniqM : ∀ m : MaximalSpectrum (normalizationPushforwardStalk X hX x), m = ⟨mB, hmax⟩ :=
    fun m => MaximalSpectrum.ext (hmax.eq_of_le m.isMaximal.ne_top
      (Stacks.Curves.map_maximalIdeal_le_of_isMaximal m.asIdeal)).symm
  obtain ⟨F, hF⟩ := normalizationFiberEquivMaximalSpectrum X hX x
  refine ⟨F.symm ⟨mB, hmax⟩, fun z => F.injective (by rw [huniqM (F z), huniqM (F _)]), ?_⟩
  obtain ⟨e, he, -⟩ := hF (F.symm ⟨mB, hmax⟩)
  have key : (F (F.symm ⟨mB, hmax⟩)).asIdeal = mB := by rw [F.apply_symm_apply]
  refine ⟨e.trans (Ideal.quotEquivOfEq key), ?_⟩
  ext b
  have := congrArg (fun φ => Ideal.quotEquivOfEq key (φ b)) he
  simpa using this

/-- **An open subscheme of the regular locus is normal.** -/
theorem isNormal_of_subset_regularLocus (U : X.Opens) (hU : (U : Set X) ⊆ regularLocus X) :
    IsNormal U.toScheme := by
  rw [isNormal_iff_stalk_normal]
  intro z
  have hreg : IsRegularLocalRing (X.presheaf.stalk z.1) := hU z.2
  have : IsDomain (X.presheaf.stalk z.1) := IsRegularLocalRing.isDomain _
  have : IsIntegrallyClosed (X.presheaf.stalk z.1) := isIntegrallyClosed_of_isRegularLocalRing _
  let e := (U.stalkIso z).commRingCatIsoToRingEquiv
  have : IsDomain (U.toScheme.presheaf.stalk z) := Function.Injective.isDomain e.toRingHom
      e.injective
  exact ⟨this, IsIntegrallyClosed.of_equiv e.symm⟩

/-- A morphism `Spec K ⟶ Spec κ(x) ⟶ X` through the residue field at `x` passes through `x`. -/
theorem specMap_comp_fromSpecResidueField_apply {K : Type u} [Field K] (x : X) (e : X.residueField
    x →+* K)
    (z : Spec (.of K)) : (Spec.map (CommRingCat.ofHom e) ≫ X.fromSpecResidueField x) z = x := by
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- **The stalk of `ν_* 𝒪_{X^ν} / 𝒪_X` at a point with one-point fibre is `κ(x') / κ(x)`.** Let
`y` be a point of the normalization `X^ν` of a reduced scheme `X`, finite over `X`, such that the
extension `𝔪 B` of the maximal ideal of `A = 𝒪_{X, ν(y)}` to `B = (ν_* 𝒪_{X^ν})_{ν(y)}` is maximal
and contained in the image of `A`. Then the stalk at `ν(y)` of the quotient `𝒬` is
`κ(y) / A`, the quotient of `κ(y)` by the image of `A`, as an `A`-module. -/
theorem nonempty_stalk_normalizationQuotient_linearEquiv [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [IsFinite (Scheme.normalization X hX)] (y : Scheme.normalizationScheme X hX)
    (hmax : (letI := normalizationPushforwardStalkAlgebra X hX (Scheme.normalization X hX y)
      Ideal.map (algebraMap (X.presheaf.stalk (Scheme.normalization X hX y))
        (normalizationPushforwardStalk X hX (Scheme.normalization X hX y)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (Scheme.normalization X hX y)))).IsMaximal)
    (hsub : letI := normalizationPushforwardStalkAlgebra X hX (Scheme.normalization X hX y)
      ∀ b ∈ Ideal.map (algebraMap (X.presheaf.stalk (Scheme.normalization X hX y))
          (normalizationPushforwardStalk X hX (Scheme.normalization X hX y)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (Scheme.normalization X hX y))),
        b ∈ Set.range (algebraMap (X.presheaf.stalk (Scheme.normalization X hX y))
          (normalizationPushforwardStalk X hX (Scheme.normalization X hX y)))) :
    letI : Algebra (X.presheaf.stalk (Scheme.normalization X hX y))
        ((Scheme.normalizationScheme X hX).residueField y) :=
      ((Scheme.normalization X hX).stalkMap y ≫ (Scheme.normalizationScheme X hX).residue
          y).hom.toAlgebra
    Nonempty (OXModule.stalk (normalizationQuotient X hX) (Scheme.normalization X hX y) ≃ₗ[
        X.presheaf.stalk (Scheme.normalization X hX y)]
      ((Scheme.normalizationScheme X hX).residueField y ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk (Scheme.normalization X hX y))
          ((Scheme.normalizationScheme X hX).residueField y)))) := by
  let algκ : Algebra (X.presheaf.stalk (Scheme.normalization X hX y))
      ((Scheme.normalizationScheme X hX).residueField y) :=
    ((Scheme.normalization X hX).stalkMap y ≫ (Scheme.normalizationScheme X hX).residue
        y).hom.toAlgebra
  let algAB := normalizationPushforwardStalkAlgebra X hX (Scheme.normalization X hX y)
  let A := X.presheaf.stalk (Scheme.normalization X hX y)
  let B := normalizationPushforwardStalk X hX (Scheme.normalization X hX y)
  let mB := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
  have : Module.Finite A B :=
    Stacks.GlueSquishFactor.module_finite_stalk_pushforward (Scheme.normalization X hX)
      (Scheme.normalization X hX y)
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite _ _
  -- the residue map `B → κ(y)` and its kernel
  let res := normalizationFiberResidueMap X hX (Scheme.normalization X hX y) ⟨y, rfl⟩
  have hres : ∀ a : A, res (algebraMap A B a) = algebraMap A _ a := fun a => rfl
  obtain ⟨F, hF⟩ := normalizationFiberEquivMaximalSpectrum X hX (Scheme.normalization X hX y)
  obtain ⟨e, he, -⟩ := hF ⟨y, rfl⟩
  have hFy : (F ⟨y, rfl⟩).asIdeal = mB :=
    (hmax.eq_of_le (F ⟨y, rfl⟩).isMaximal.ne_top
      (Stacks.Curves.map_maximalIdeal_le_of_isMaximal _)).symm
  have hker : ∀ b, res b = 0 ↔ b ∈ mB := fun b => by
    rw [← hFy, ← Ideal.Quotient.eq_zero_iff_mem, ← he]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      map_eq_zero_iff _ e.injective]
    rfl
  have hsurj : Function.Surjective res := fun z => by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e z)
    refine ⟨b, e.injective ?_⟩
    rw [← hb]
    exact congrArg (fun φ : B →+* _ => φ b) he
  let ρ : B →ₗ[A] (Scheme.normalizationScheme X hX).residueField y :=
    { toFun := res
      map_add' := map_add res
      map_smul' := fun a b => by
        simp only [Algebra.smul_def, map_mul, hres, RingHom.id_apply] }
  let σ := (LinearMap.range (Algebra.linearMap A B)).mapQ
    (LinearMap.range (Algebra.linearMap A ((Scheme.normalizationScheme X hX).residueField y))) ρ
    (by rintro _ ⟨a, rfl⟩; exact ⟨a, (hres a).symm⟩)
  have hσinj : Function.Injective σ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ z
    change Submodule.mkQ _ (ρ b) = 0 at hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨a, ha⟩ := hz
    have hmem : b - algebraMap A B a ∈ mB := by
      rw [← hker, map_sub, hres]
      exact sub_eq_zero.mpr ha.symm
    obtain ⟨a', ha'⟩ := hsub _ hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨a' + a, by rw [Algebra.linearMap_apply, map_add, ha', sub_add_cancel]⟩
  have hσsurj : Function.Surjective σ := by
    intro z
    obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨b, rfl⟩ := hsurj t
    exact ⟨Submodule.mkQ _ b, rfl⟩
  obtain ⟨e0⟩ := normalizationQuotientStalk_linearEquiv_quotient_range X hX
    (Scheme.normalization X hX y)
  exact ⟨e0.trans (LinearEquiv.ofBijective σ ⟨hσinj, hσsurj⟩)⟩

/-- The skyscraper maps induced by two composable maps compose. -/
private theorem skyscraperMapHomApp_comp_eq_id (x : X) {N N' : ModuleCat.{u} (X.presheaf.stalk x)}
    (g : N ⟶ N') (g' : N' ⟶ N) (hg : g ≫ g' = 𝟙 N) (U : (Opens X)ᵒᵖ) :
    OXModule.skyscraperMapHomApp x g U ≫ OXModule.skyscraperMapHomApp x g' U = 𝟙 _ := by
  classical
  by_cases h : x ∈ U.unop
  · simp only [OXModule.skyscraperMapHomApp, dif_pos h, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp_assoc, hg]
    simp
  · have hsub : Subsingleton (OXModule.skyscraperObj x N U) := by
      have : (OXModule.skyscraperObj x N U) = ModuleCat.of _ PUnit.{u+1} := by
        rw [OXModule.skyscraperObj, dite_eq_right h]
      rw [this]; exact inferInstanceAs (Subsingleton PUnit.{u+1})
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- **The skyscraper `𝒪_X`-module at `x` depends functorially on its stalk**, in that an
isomorphism of `𝒪_{X, x}`-modules induces an isomorphism of skyscraper modules. -/
def skyscraperModuleIsoOfIso (x : X) {N N' : ModuleCat.{u} (X.presheaf.stalk x)} (e : N ≅ N') :
    skyscraperModule X x N ≅ skyscraperModule X x N' :=
  OXModule.sheafify.mapIso
    { hom := OXModule.skyscraperPOMMap x e.hom
      inv := OXModule.skyscraperPOMMap x e.inv
      hom_inv_id := PresheafOfModules.hom_ext fun U => by
        rw [PresheafOfModules.comp_app]
        exact skyscraperMapHomApp_comp_eq_id x e.hom e.inv e.hom_inv_id U
      inv_hom_id := PresheafOfModules.hom_ext fun U => by
        rw [PresheafOfModules.comp_app]
        exact skyscraperMapHomApp_comp_eq_id x e.inv e.hom e.inv_hom_id U }



section ZeroDimensionalSupport

variable [IsProper f] (F : X.Modules) [F.IsCoherent]
  (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0)

/-- **`H⁰(X, ℱ) = ⨁_{x ∈ Supp ℱ} ℱ_x` as `k`-vector spaces**, for a coherent module `ℱ` with
zero-dimensional support on a proper scheme over `k`, each stalk carrying the `k`-structure of the
local ring. This is `AlgebraicGeometry.suppStalkPiAddEquiv` ([Stacks, Tag 0AYT] (2)) with its
`k`-linearity: the germ maps are linear over the maps from global sections to the local rings. -/
def cohomologyOverFieldZeroLinearEquivPiStalk :
    cohomologyOverField k f F 0 ≃ₗ[k] ∀ x : ↥(_root_.SheafOfModules.supp F),
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp) ≫
        X.presheaf.germ ⊤ x.1 trivial).hom).obj (OXModule.stalk F x.1) :=
  (cohomologyOverFieldZeroLinearIso k f F).toLinearEquiv.trans
    { toAddEquiv := suppStalkPiAddEquiv k f F hF
      map_smul' := fun _ s => funext fun x =>
        PresheafOfModules.germ_smul (R := X.presheaf) F.val x.1 ⊤ trivial _ s }

/-- Each stalk of a coherent module with zero-dimensional support on a proper scheme over `k` is
finite-dimensional over `k`. -/
private theorem finiteDimensional_stalk_of_supp_le_zero
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0)
    (x : ↥(_root_.SheafOfModules.supp F)) :
    FiniteDimensional k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appLE ⊤ ⊤ (by simp) ≫ X.presheaf.germ ⊤ x.1 trivial).hom).obj (OXModule.stalk F x.1)) := by
  have := finiteDimensional_cohomologyOverField_of_isProper k f F 0
  have := Module.Finite.equiv (cohomologyOverFieldZeroLinearEquivPiStalk k f F hF)
  classical
  exact Module.Finite.of_surjective (LinearMap.proj (R := k)
    (φ := fun y : ↥(_root_.SheafOfModules.supp F) =>
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ _ ≫
        X.presheaf.germ ⊤ y.1 trivial).hom).obj (OXModule.stalk F y.1)) x)
    fun y => ⟨Pi.single x y, by simp⟩

/-- **`dim_k H⁰(X, ℱ) = ∑_{x ∈ Supp ℱ} dim_k ℱ_x`** for a coherent module `ℱ` with
zero-dimensional support on a proper scheme over `k`. -/
theorem finrank_cohomologyOverField_zero_eq_sum_finrank_stalk :
    letI : Fintype ↥(_root_.SheafOfModules.supp F) := (finite_supp_of_supp_le_zero k f F hF).fintype
    Module.finrank k (cohomologyOverField k f F 0) =
      ∑ x : ↥(_root_.SheafOfModules.supp F), Module.finrank k
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp) ≫
          X.presheaf.germ ⊤ x.1 trivial).hom).obj (OXModule.stalk F x.1)) := by
  let : Fintype ↥(_root_.SheafOfModules.supp F) := (finite_supp_of_supp_le_zero k f F hF).fintype
  have e := cohomologyOverFieldZeroLinearEquivPiStalk k f F hF
  have := finiteDimensional_stalk_of_supp_le_zero k f F hF
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end ZeroDimensionalSupport

section Curve

variable [IsCurve k f]

/-- The normalization of a curve over `k`, with its induced structure morphism, is a curve over
`k`. -/
theorem isCurve_normalizationOverField_comp : IsCurve k (normalizationOverField k f ≫ f) :=
  { toIsVariety := isVariety_normalizationOverField k f
    topologicalKrullDim_eq_one := by
      rw [topologicalKrullDim_normalizationSchemeOverField k f]
      exact IsCurve.topologicalKrullDim_eq_one f }

/-- The support of the quotient `ν_* 𝒪_{X^ν} / 𝒪_X` of a curve is its singular locus. -/
theorem supp_normalizationQuotient :
    _root_.SheafOfModules.supp
        (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)) =
      singularLocus X := by
  have hN := isNagataScheme_of_locallyOfFiniteType_over_field k f
  ext x
  refine (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).trans ?_
  rw [← normalizationQuotientStalk_nonzero_iff_mem_singularLocus X hN
      (IsCurve.topologicalKrullDim_eq_one f) x, ModuleCat.isZero_iff_subsingleton,
    not_subsingleton_iff_nontrivial]
  rfl

/-- The quotient `ν_* 𝒪_{X^ν} / 𝒪_X` of a curve is coherent. -/
theorem isCoherent_normalizationQuotient :
    (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)).IsCoherent
        := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite (normalizationOverField k f) := isFinite_normalizationOverField k f
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have : IsLocallyNoetherian (normalizationSchemeOverField k f) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k f ≫ f)
  have : (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hP : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward (normalizationOverField k f)).obj
      (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) :=
    isCoherent_pushforward_of_isFinite _ _
  exact @isCoherent_cokernel X _ _ _ ‹_› hP
    (normalizationModuleMap X (finite_irreducibleComponents_of_locallyOfFiniteType k f))

/-- The support of the quotient `ν_* 𝒪_{X^ν} / 𝒪_X` of a curve has dimension zero. -/
theorem topologicalKrullDim_supp_normalizationQuotient_le_zero :
    topologicalKrullDim (_root_.SheafOfModules.supp
        (normalizationQuotient X
          (finite_irreducibleComponents_of_locallyOfFiniteType k f))) ≤ 0 := by
  refine topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne
    (IsCurve.topologicalKrullDim_eq_one (k := k) f).le _
    (isCoherent_normalizationQuotient k f) fun x hx hsupp => ?_
  rw [supp_normalizationQuotient k f] at hsupp
  exact hsupp
      (NormalizationQuotientDirectSum.mem_regularLocus_of_mem_genericPoints
    X x (mem_genericPointsOne_iff.mp hx).1)

/-- The normalization sequence `0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X^ν} ⟶ ν_* 𝒪_{X^ν} / 𝒪_X ⟶ 0` of a curve is short
exact. -/
theorem shortExact_normalizationSequence :
    (ShortComplex.cokernelSequence
      (normalizationModuleMap X (finite_irreducibleComponents_of_locallyOfFiniteType k
          f))).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := mono_normalizationModuleMap X _

variable [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- **The cohomology of the normalization sequence of a genus-zero curve.** For a proper curve `X`
over `k` with `H⁰(X, 𝒪_X) = k` and genus zero, with normalization `ν : X^ν ⟶ X` and
`𝒬 = ν_* 𝒪_{X^ν} / 𝒪_X`, one has `H¹(X^ν, 𝒪_{X^ν}) = 0` and
`dim_k H⁰(X, 𝒬) + 1 = dim_k Γ(X^ν, 𝒪_{X^ν})`. These are the two consequences the source draws
from the long exact sequence of `0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X^ν} ⟶ 𝒬 ⟶ 0`, the sheaf `𝒬` having
zero-dimensional support. -/
theorem normalization_cohomology_of_genus_eq_zero (hgenus : genus f = 0) :
    letI : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
    IsZero (cohomologyOverField k (normalizationOverField k f ≫ f)
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf) 1) ∧
      Module.finrank k (cohomologyOverField k f
          (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)) 0) +
              1 =
        Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) := by
  let : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) f).le
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite (normalizationOverField k f) := isFinite_normalizationOverField k f
  have : IsLocallyNoetherian (normalizationSchemeOverField k f) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k f ≫ f)
  have : (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have hS := shortExact_normalizationSequence k f
  have hQcoh := isCoherent_normalizationQuotient k f
  have hQsupp := topologicalKrullDim_supp_normalizationQuotient_le_zero k f
  have hOX : (SheafOfModules.unit X.ringCatSheaf).IsCoherent := isCoherent_unit k f
  -- vanishing of `H¹` of the outer terms
  have h1O : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
    have := @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hOX 1
    have h := finrank_cohomologyOverField_one_unit_eq_genus k f
    rw [hgenus] at h
    exact ModuleCat.isZero_iff_subsingleton.mpr (Module.finrank_zero_iff.mp h)
  have h1Q : IsZero (cohomologyOverField k f
      (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)) 1) :=
    @isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k _ X f _ _ hQcoh hQsupp 1
      Nat.one_pos
  have h1P : IsZero (cohomologyOverField k f ((Scheme.Modules.pushforward
      (normalizationOverField k f)).obj
      (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 1) :=
    isZero_cohomologyOverField_of_shortExact k f hS 1 h1O h1Q
  refine ⟨h1P.of_iso (cohomologyOverFieldPushforwardIsoOfIsAffineHom k
    (normalizationOverField k f) f _ 1), ?_⟩
  -- the Euler characteristics
  have hvan : ∀ (F : X.Modules) (m : ℕ), 2 ≤ m → IsZero (cohomologyOverField k f F m) :=
    fun F m hm => isZero_cohomologyOverField_two_le k f hdim F m hm
  have hsum := finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer k f hS 2
    (fun n _ => @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hOX n)
    (fun n _ => @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hQcoh n)
    (fun n hn => hvan _ n hn) (fun n hn => hvan _ n hn)
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _ (hvan _),
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _ (hvan _),
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _ (hvan _)] at hsum
  have key : (Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
        (normalizationOverField k f)).obj
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
        (normalizationOverField k f)).obj
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 1) : ℤ) =
      ((Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ)) +
      ((Module.finrank k (cohomologyOverField k f (normalizationQuotient X
          (finite_irreducibleComponents_of_locallyOfFiniteType k f)) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (normalizationQuotient X
          (finite_irreducibleComponents_of_locallyOfFiniteType k f)) 1) : ℤ)) :=
    hsum
  have e0 : Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
      (normalizationOverField k f)).obj
      (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 0) =
      Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) :=
    (finrank_cohomologyOverField_pushforward_of_isAffineHom k (normalizationOverField k f) f
      _ 0).symm.trans (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k
        (normalizationOverField k f ≫ f))
  have z1 : ∀ (F : X.Modules), IsZero (cohomologyOverField k f F 1) →
      Module.finrank k (cohomologyOverField k f F 1) = 0 := fun F h => by
    have := ModuleCat.subsingleton_of_isZero h
    exact Module.finrank_zero_of_subsingleton
  rw [finrank_cohomologyOverField_unit_zero_eq_one, e0, z1 _ h1O, z1 _ h1Q, z1 _ h1P] at key
  omega

end Curve

/-- **The dimension count of [Stacks, Tag 0DJB] at a singular point.** Let `X` be a proper curve
over `k` with normalization `ν : X^ν ⟶ X`, let `s` be a singular point, `A = 𝒪_{X, s}`,
`B = (ν_* 𝒪_{X^ν})_s` and `k' = Γ(X^ν, 𝒪_{X^ν})`, and let `d = dim_k 𝒬_s` for the stalk of
`𝒬 = ν_* 𝒪_{X^ν} / 𝒪_X`, when it is finite. Then `[k' : k] ≤ 2 d`; and if `d + 1 = [k' : k]` then
`κ(s) = k`, the ideal `𝔪_s B` is maximal with `k' ≅ B / 𝔪_s B`, and `𝔪_s B` lies in the image of
`A`. This is `Stacks.Curves.finrank_le_two_mul_finrank_quotient_range` and
`Stacks.Curves.finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq` at `A → B`, the
stalk `𝒬_s` being `B / A` by [Stacks, Tag 0C1R]. -/
theorem normalization_stalk_count [IsCurve k f] [IsProper f] (s : X) (hs : s ∈ singularLocus X)
    (hfin : FiniteDimensional k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appTop ≫ X.presheaf.germ ⊤ s trivial).hom).obj (OXModule.stalk
          (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)) s))) :
    letI : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
    letI : Algebra k (X.residueField s) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation s).hom.toAlgebra
    letI := normalizationPushforwardStalkAlgebra X
      (finite_irreducibleComponents_of_locallyOfFiniteType k f) s
    letI : Algebra Γ(normalizationSchemeOverField k f, ⊤) (normalizationPushforwardStalk X
        (finite_irreducibleComponents_of_locallyOfFiniteType k f) s) :=
      (((normalizationOverField k f).base _*
        (normalizationSchemeOverField k f).presheaf).germ ⊤ s trivial).hom.toAlgebra
    Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) ≤ 2 * Module.finrank k
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
          f.appTop ≫ X.presheaf.germ ⊤ s trivial).hom).obj (OXModule.stalk
            (normalizationQuotient X
              (finite_irreducibleComponents_of_locallyOfFiniteType k f)) s)) ∧
      (Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
          f.appTop ≫ X.presheaf.germ ⊤ s trivial).hom).obj (OXModule.stalk
            (normalizationQuotient X
              (finite_irreducibleComponents_of_locallyOfFiniteType k f)) s)) + 1 =
          Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) →
        Module.finrank k (X.residueField s) = 1 ∧
          (Ideal.map (algebraMap (X.presheaf.stalk s)
            (normalizationPushforwardStalk X
              (finite_irreducibleComponents_of_locallyOfFiniteType k f) s))
              (IsLocalRing.maximalIdeal (X.presheaf.stalk s))).IsMaximal ∧
          Function.Bijective (algebraMap Γ(normalizationSchemeOverField k f, ⊤)
            (normalizationPushforwardStalk X
                (finite_irreducibleComponents_of_locallyOfFiniteType k f) s ⧸
              Ideal.map (algebraMap (X.presheaf.stalk s)
                (normalizationPushforwardStalk X
                  (finite_irreducibleComponents_of_locallyOfFiniteType k f) s))
                (IsLocalRing.maximalIdeal (X.presheaf.stalk s)))) ∧
          ∀ b ∈ Ideal.map (algebraMap (X.presheaf.stalk s)
              (normalizationPushforwardStalk X
                (finite_irreducibleComponents_of_locallyOfFiniteType k f) s))
              (IsLocalRing.maximalIdeal (X.presheaf.stalk s)),
            b ∈ Set.range (algebraMap (X.presheaf.stalk s)
              (normalizationPushforwardStalk X
                (finite_irreducibleComponents_of_locallyOfFiniteType k f) s))) := by
  let algΓ : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
  let algκ : Algebra k (X.residueField s) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation s).hom.toAlgebra
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  let algAB := normalizationPushforwardStalkAlgebra X hX s
  let algΓB : Algebra Γ(normalizationSchemeOverField k f, ⊤)
      (normalizationPushforwardStalk X hX s) :=
    (((normalizationOverField k f).base _*
      (normalizationSchemeOverField k f).presheaf).germ ⊤ s trivial).hom.toAlgebra
  have hdim : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) f
  have hcl : IsClosed ({s} : Set X) :=
    NormalizationQuotientDirectSum.isClosed_singleton_of_not_mem_regularLocus
      X hdim.le s hs
  have : IsFinite (normalizationOverField k f) := isFinite_normalizationOverField k f
  have hV : IsVariety k (normalizationOverField k f ≫ f) := isVariety_normalizationOverField k f
  have : IsIntegral (normalizationSchemeOverField k f) := hV.toIsIntegral
  have : IsProper (normalizationOverField k f ≫ f) := isProper_normalizationOverField_comp k f
  obtain ⟨hΓfield, hΓfin⟩ := isField_and_finite_globalSections k (normalizationOverField k f ≫ f)
  let : Field Γ(normalizationSchemeOverField k f, ⊤) := hΓfield.toField
  let algA : Algebra k (X.presheaf.stalk s) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ s trivial).hom.toAlgebra
  let algB : Algebra k (normalizationPushforwardStalk X hX s) :=
    ((algebraMap (X.presheaf.stalk s) _).comp (algebraMap k (X.presheaf.stalk s))).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk s) (normalizationPushforwardStalk X hX s) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k Γ(normalizationSchemeOverField k f, ⊤)
      (normalizationPushforwardStalk X hX s) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ s trivial (normalizationOverField k f).c
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))
  have : Module.Finite (X.presheaf.stalk s) (normalizationPushforwardStalk X hX s) :=
    Stacks.GlueSquishFactor.module_finite_stalk_pushforward (normalizationOverField k f) s
  have eκ : X.residueField s ≃ₗ[k] IsLocalRing.ResidueField (X.presheaf.stalk s) :=
    { AddEquiv.refl _ with map_smul' := fun c x => rfl }
  have : FiniteDimensional k (IsLocalRing.ResidueField (X.presheaf.stalk s)) :=
    have := finite_residueField_over_field_of_isClosed k f s hcl
    Module.Finite.equiv eκ
  -- the stalk of the quotient is `B / A`
  have hN := isNagataScheme_of_locallyOfFiniteType_over_field k f
  obtain ⟨e0⟩ := normalizationQuotientStalk_linearEquiv_quotient_range X hX s
  let e : ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appTop ≫ X.presheaf.germ ⊤ s trivial).hom).obj (OXModule.stalk
          (normalizationQuotient X hX) s)) ≃ₗ[k]
      (normalizationPushforwardStalk X hX s ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk s)
          (normalizationPushforwardStalk X hX s))) :=
    { e0.toAddEquiv with
      map_smul' := fun c x => (e0.map_smul (algebraMap k (X.presheaf.stalk s) c) x).trans
        (algebraMap_smul (X.presheaf.stalk s) c (e0 x)) }
  have : FiniteDimensional k (normalizationPushforwardStalk X hX s ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk s)
          (normalizationPushforwardStalk X hX s))) :=
    Module.Finite.equiv e
  have hR : LinearMap.range (Algebra.linearMap (X.presheaf.stalk s)
      (normalizationPushforwardStalk X hX s)) ≠ ⊤ := by
    have hne := (normalizationQuotientStalk_nonzero_iff_mem_singularLocus X hN hdim s).mpr hs
    rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hne
    have : Nontrivial (normalizationPushforwardStalk X hX s ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk s)
          (normalizationPushforwardStalk X hX s))) :=
      e0.toEquiv.symm.nontrivial
    exact Submodule.Quotient.nontrivial_iff.mp this
  rw [e.finrank_eq]
  refine ⟨Stacks.Curves.finrank_le_two_mul_finrank_quotient_range (k := k)
    (k' := Γ(normalizationSchemeOverField k f, ⊤)) hR, fun hd => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    Stacks.Curves.finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq (k := k)
      (k' := Γ(normalizationSchemeOverField k f, ⊤)) hR hd
  exact ⟨eκ.finrank_eq.trans h1, h2, h3, h4⟩

/-- Restriction of scalars along two equal ring maps gives modules of the same dimension. -/
private theorem finrank_restrictScalars_congr {R S : Type u} [Field R] [CommRing S] {φ ψ : R →+* S}
    (h : φ = ψ) (M : ModuleCat.{u} S) :
    Module.finrank R ((ModuleCat.restrictScalars φ).obj M) =
      Module.finrank R ((ModuleCat.restrictScalars ψ).obj M) := by
  subst h; rfl

/-- Restriction of scalars along two equal ring maps preserves finite dimensionality. -/
private theorem finiteDimensional_restrictScalars_congr {R S : Type u} [Field R] [CommRing S]
    {φ ψ : R →+* S} (h : φ = ψ) (M : ModuleCat.{u} S)
    (hM : FiniteDimensional R ((ModuleCat.restrictScalars φ).obj M)) :
    FiniteDimensional R ((ModuleCat.restrictScalars ψ).obj M) := by
  subst h; exact hM

/-- **A singular proper curve of genus zero with `H⁰(X, 𝒪_X) = k` has exactly one singular
point**, and at it the stalk of `𝒬 = ν_* 𝒪_{X^ν} / 𝒪_X` has dimension `[k' : k] - 1`, where
`k' = Γ(X^ν, 𝒪_{X^ν})`. The global sections of `𝒬` are the sum of its stalks at the singular
points, of total dimension `[k' : k] - 1`, while each singular point contributes at least
`[k' : k] / 2` by `AlgebraicGeometry.normalization_stalk_count`. -/
theorem exists_singularLocus_eq_singleton [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hsing : (singularLocus X).Nonempty) (hgenus : genus f = 0) :
    letI : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
    ∃ x : X, singularLocus X = {x} ∧
      FiniteDimensional k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom).obj (OXModule.stalk
          (normalizationQuotient X (finite_irreducibleComponents_of_locallyOfFiniteType k f)) x)) ∧
      Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
          f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom).obj (OXModule.stalk
            (normalizationQuotient X
              (finite_irreducibleComponents_of_locallyOfFiniteType k f)) x)) + 1 =
        Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) := by
  classical
  let algΓ : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  have hQcoh := isCoherent_normalizationQuotient k f
  have hQsupp := topologicalKrullDim_supp_normalizationQuotient_le_zero k f
  have hsupp := supp_normalizationQuotient k f
  have hcount := (normalization_cohomology_of_genus_eq_zero k f hgenus).2
  let : Fintype ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)) :=
    (finite_supp_of_supp_le_zero k f _ hQsupp).fintype
  have hsum := @finrank_cohomologyOverField_zero_eq_sum_finrank_stalk k _ X f _ _ hQcoh hQsupp
  have hφ : ∀ x : X, ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp) ≫
      X.presheaf.germ ⊤ x trivial).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := fun x =>
    congrArg (fun t : Γ(Spec (.of k), ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) =>
      ((Scheme.ΓSpecIso (.of k)).inv ≫ t ≫ X.presheaf.germ ⊤ x trivial).hom)
      (appLE_top_top_eq_appTop f (by simp))
  -- the dimension of the stalks
  let d : ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)) → ℕ := fun x =>
    Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appTop ≫ X.presheaf.germ ⊤ x.1 trivial).hom).obj
        (OXModule.stalk (normalizationQuotient X hX) x.1))
  have hsum' : Module.finrank k (cohomologyOverField k f (normalizationQuotient X hX) 0) =
      ∑ x, d x := by
    rw [hsum]
    exact Finset.sum_congr rfl fun x _ => finrank_restrictScalars_congr (hφ x.1) _
  -- finite dimensionality of each stalk
  have hfinS : ∀ x : ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)),
      FiniteDimensional k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appTop ≫ X.presheaf.germ ⊤ x.1 trivial).hom).obj
          (OXModule.stalk (normalizationQuotient X hX) x.1)) := by
    intro x
    exact finiteDimensional_restrictScalars_congr (hφ x.1) _
      (@finiteDimensional_stalk_of_supp_le_zero k _ X f _ _ hQcoh hQsupp x)
  have hlow : ∀ x : ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)),
      Module.finrank k Γ(normalizationSchemeOverField k f, ⊤) ≤ 2 * d x := fun x =>
    (normalization_stalk_count k f x.1 (hsupp ▸ x.2) (hfinS x)).1
  -- there is only one singular point
  obtain ⟨x, hx⟩ := hsing
  have hxS : x ∈ _root_.SheafOfModules.supp (normalizationQuotient X hX) := hsupp ▸ hx
  have huniq : ∀ y : ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)), y = ⟨x, hxS⟩ := by
    intro y
    by_contra hne
    have h2 : d y + d ⟨x, hxS⟩ ≤ ∑ z, d z := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hlow y
    have := hlow ⟨x, hxS⟩
    omega
  refine ⟨x, ?_, hfinS ⟨x, hxS⟩, ?_⟩
  · rw [← hsupp]
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · exact congrArg Subtype.val (huniq ⟨y, hy⟩)
    · rw [Set.mem_singleton_iff.mp hy]; exact hxS
  · have hone : ∑ z, d z = d ⟨x, hxS⟩ := by
      rw [Finset.sum_eq_single ⟨x, hxS⟩ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ _) h)]
    rw [← hcount, hsum', hone]

/-- **[Stacks, Tag 0DJB].** Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`,
singular and of genus zero, and let `ν : X' ⟶ X` be its normalization. Then there are a field
`k'`, a structure morphism `X' ⟶ Spec k'` and points `x' : Spec k' ⟶ X'`, `x : Spec k ⟶ X`
making the diagram `x' ⟶ X' ⟶ Spec k'` over `x ⟶ X ⟶ Spec k` commute, such that

1. `k'/k` is a nontrivial finite extension;
2. `X' ≅ 𝐏¹_{k'}` over `k'`;
3. `x'` is a `k'`-rational point of `X'`;
4. `x` is a `k`-rational point of `X`;
5. `ν` restricts to an isomorphism `X' ∖ {x'} ≅ X ∖ {x}`;
6. `0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X'} ⟶ 𝒬 ⟶ 0` is short exact and its cokernel `𝒬` is the skyscraper at
   `x = ν(x')` with value `κ(x') / κ(x)`, the quotient of `κ(x')` by the image of `𝒪_{X, x}`;
   the point is written `ν(x')`, which is `x` by the commutativity of the left square.

The field is `k' = H⁰(X', 𝒪_{X'})`. The dimension count at the singular points that the source
runs through the conductor and a bound on commutative subalgebras of a matrix algebra is
replaced by `Stacks.Curves.finrank_le_two_mul_finrank_quotient_range` and
`Stacks.Curves.finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq`, which use
only that `B / A` is a module over the local ring `A = 𝒪_{X, x}` and that `B / 𝔪_A B` is a
`k'`-vector space, `B = (ν_* 𝒪_{X'})_x`; see
`StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZeroAlgebra`.
The isomorphism `X' ≅ 𝐏¹_{k'}` comes from the degree-one invertible module of the rational point
`x'` by `AlgebraicGeometry.exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one`. -/
@[stacks 0DJB]
theorem exists_projectiveLine_normalization_of_genus_eq_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hsing : (singularLocus X).Nonempty) (hgenus : genus f = 0) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (f' : normalizationSchemeOverField k f ⟶ Spec (.of k'))
      (x' : Spec (.of k') ⟶ normalizationSchemeOverField k f) (x : Spec (.of k) ⟶ X),
      -- the diagram commutes
      normalizationOverField k f ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) ∧
      x' ≫ normalizationOverField k f = Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ x ∧
      -- (1)
      (Module.Finite k k' ∧ 1 < Module.finrank k k') ∧
      -- (2)
      (∃ e : normalizationSchemeOverField k f ≅
          Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k' 1),
        e.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k' 1 = f') ∧
      -- (3)
      x' ≫ f' = 𝟙 _ ∧
      -- (4)
      x ≫ f = 𝟙 _ ∧
      -- (5)
      (∃ U : X.Opens, (U : Set X) = {x (IsLocalRing.closedPoint k)}ᶜ ∧
        ((normalizationOverField k f) ⁻¹ᵁ U : Set (normalizationSchemeOverField k f)) =
          {x' (IsLocalRing.closedPoint k')}ᶜ ∧
        IsIso (normalizationOverField k f ∣_ U)) ∧
      -- (6)
      (letI : Algebra
          (X.presheaf.stalk (normalizationOverField k f (x' (IsLocalRing.closedPoint k'))))
          ((normalizationSchemeOverField k f).residueField (x' (IsLocalRing.closedPoint k'))) :=
        ((normalizationOverField k f).stalkMap (x' (IsLocalRing.closedPoint k')) ≫
          (normalizationSchemeOverField k f).residue
            (x' (IsLocalRing.closedPoint k'))).hom.toAlgebra
       (ShortComplex.cokernelSequence (normalizationModuleMap X
          (finite_irreducibleComponents_of_locallyOfFiniteType k f))).ShortExact ∧
        Nonempty (normalizationQuotient X
            (finite_irreducibleComponents_of_locallyOfFiniteType k f) ≅
          skyscraperModule X (normalizationOverField k f (x' (IsLocalRing.closedPoint k')))
            (ModuleCat.of _
              ((normalizationSchemeOverField k f).residueField (x' (IsLocalRing.closedPoint k')) ⧸
                LinearMap.range (Algebra.linearMap
                  (X.presheaf.stalk (normalizationOverField k f (x' (IsLocalRing.closedPoint k'))))
                  ((normalizationSchemeOverField k f).residueField
                    (x' (IsLocalRing.closedPoint k')))))))) := by
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  obtain ⟨x, hsingx, hfinx, hcountx⟩ := exists_singularLocus_eq_singleton k f hsing hgenus
  have hx : x ∈ singularLocus X := by rw [hsingx]; rfl
  obtain ⟨-, hstalk⟩ := normalization_stalk_count k f x hx hfinx
  obtain ⟨hκ, hmax, hbij, hsub⟩ := hstalk hcountx
  have : IsFinite (normalizationOverField k f) := isFinite_normalizationOverField k f
  have hV : IsVariety k (normalizationOverField k f ≫ f) := isVariety_normalizationOverField k f
  have : IsIntegral (normalizationSchemeOverField k f) := hV.toIsIntegral
  have : IsProper (normalizationOverField k f ≫ f) := isProper_normalizationOverField_comp k f
  obtain ⟨hΓfield, hΓfin⟩ := isField_and_finite_globalSections k (normalizationOverField k f ≫ f)
  let : Field Γ(normalizationSchemeOverField k f, ⊤) := hΓfield.toField
  have : Nontrivial Γ(normalizationSchemeOverField k f, ⊤) := ⟨hΓfield.exists_pair_ne⟩
  let algΓ : Algebra k Γ(normalizationSchemeOverField k f, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop).hom.toAlgebra
  -- `x` is a `k`-rational point
  let algκ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hψ : Function.Bijective
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
    have hinj : Function.Injective (Algebra.linearMap k (X.residueField x)) :=
      (algebraMap k (X.residueField x)).injective
    have : FiniteDimensional k (X.residueField x) :=
      Module.finite_of_finrank_eq_succ hκ
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_self, hκ])).mp hinj⟩
  -- the fibre over `x` is one point `y`, with residue field `k'`
  let := normalizationPushforwardStalkAlgebra X hX x
  let algΓB : Algebra Γ(normalizationSchemeOverField k f, ⊤)
      (normalizationPushforwardStalk X hX x) :=
    (((normalizationOverField k f).base _*
      (normalizationSchemeOverField k f).presheaf).germ ⊤ x trivial).hom.toAlgebra
  set mB := Ideal.map (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) with hmB
  obtain ⟨y, hyuniq, e', he'⟩ := existsUnique_normalization_fiber_of_isMaximal hX x hmax
  obtain ⟨y, hy⟩ := y
  subst hy
  set x₀ : Spec (.of k) ⟶ X := Spec.map (CommRingCat.ofHom
    (RingEquiv.ofBijective _ hψ).symm.toRingHom) ≫
      X.fromSpecResidueField (normalizationOverField k f y) with hx₀
  have hx₀f : x₀ ≫ f = 𝟙 _ := fromSpecResidueField_comp_eq_id_of_bijective k f _ hψ
  have hev : Function.Bijective ((normalizationSchemeOverField k f).Γevaluation y).hom := by
    have hcomp : ∀ a, e' ((normalizationSchemeOverField k f).Γevaluation y a) =
        (Ideal.Quotient.mk mB) (((normalizationOverField k f).base _*
          (normalizationSchemeOverField k f).presheaf).germ ⊤ _ trivial a) := fun a => by
      rw [← normalizationFiberResidueMap_germ_top hX _ ⟨y, rfl⟩ a]
      exact congrArg (fun φ : _ →+* _ => φ (((normalizationOverField k f).base _*
          (normalizationSchemeOverField k f).presheaf).germ ⊤ _ trivial a)) he'
    have : ((normalizationSchemeOverField k f).Γevaluation y).hom =
        e'.symm.toRingHom.comp (algebraMap Γ(normalizationSchemeOverField k f, ⊤)
          (normalizationPushforwardStalk X hX (normalizationOverField k f y) ⧸ mB)) := by
      ext a
      exact (e'.symm_apply_eq.mpr (hcomp a).symm).symm
    rw [this]
    exact e'.symm.bijective.comp hbij
  -- the structure morphism of `X^ν` over `k' = Γ(X^ν, 𝒪)`
  let f' : normalizationSchemeOverField k f ⟶ Spec (.of Γ(normalizationSchemeOverField k f, ⊤)) :=
    (normalizationSchemeOverField k f).toSpecΓ
  have hf'top : (Scheme.ΓSpecIso (.of Γ(normalizationSchemeOverField k f, ⊤))).inv ≫ f'.appTop =
      𝟙 _ := by
    show (Scheme.ΓSpecIso Γ(normalizationSchemeOverField k f, ⊤)).inv ≫
      (normalizationSchemeOverField k f).toSpecΓ.appTop = 𝟙 _
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  have hev' : Function.Bijective
      ((Scheme.ΓSpecIso (.of Γ(normalizationSchemeOverField k f, ⊤))).inv ≫
      f'.appTop ≫ (normalizationSchemeOverField k f).Γevaluation y).hom := by
    rw [← Category.assoc, hf'top, Category.id_comp]
    exact hev
  set x₀' : Spec (.of Γ(normalizationSchemeOverField k f, ⊤)) ⟶ normalizationSchemeOverField k f :=
    Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom) ≫
      (normalizationSchemeOverField k f).fromSpecResidueField y with hx₀'
  have hx₀'f' : x₀' ≫ f' = 𝟙 _ := fromSpecResidueField_comp_eq_id_of_bijective _ f' y hev'
  have hνf : normalizationOverField k f ≫ f =
      f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(normalizationSchemeOverField k f, ⊤))) := by
    apply ext_to_Spec
    show (Scheme.ΓSpecIso (.of k)).inv ≫ (normalizationOverField k f ≫ f).appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (f' ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k Γ(normalizationSchemeOverField k f, ⊤)))).appTop
    rw [Scheme.Hom.comp_appTop (f := f'), ← Scheme.ΓSpecIso_inv_naturality_assoc, hf'top,
      Category.comp_id]
    rfl
  have hring : (normalizationOverField k f).residueFieldMap y ≫
      CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom =
      CommRingCat.ofHom (RingEquiv.ofBijective _ hψ).symm.toRingHom ≫
        CommRingCat.ofHom (algebraMap k Γ(normalizationSchemeOverField k f, ⊤)) := by
    ext t
    obtain ⟨c, rfl⟩ := hψ.2 t
    show (RingEquiv.ofBijective _ hev').symm ((normalizationOverField k f).residueFieldMap y
      (X.Γevaluation _ (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))) =
      algebraMap k Γ(normalizationSchemeOverField k f, ⊤)
        ((RingEquiv.ofBijective _ hψ).symm (RingEquiv.ofBijective _ hψ c))
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq, Scheme.Γevaluation_naturality_apply]
    have h3 := ConcreteCategory.congr_hom hf'top
      (algebraMap k Γ(normalizationSchemeOverField k f, ⊤) c)
    show _ = (normalizationSchemeOverField k f).Γevaluation y
      ((f'.appTop) ((Scheme.ΓSpecIso (.of Γ(normalizationSchemeOverField k f, ⊤))).inv
        (algebraMap k Γ(normalizationSchemeOverField k f, ⊤) c)))
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at h3
    rw [h3]
    rfl
  have hsq' : Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom) ≫
      Spec.map ((normalizationOverField k f).residueFieldMap y) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(normalizationSchemeOverField k f, ⊤))) ≫
        Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hψ).symm.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map hring
  have hsq : x₀' ≫ normalizationOverField k f =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(normalizationSchemeOverField k f, ⊤))) ≫ x₀ := by
    calc x₀' ≫ normalizationOverField k f
        = Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom) ≫
            ((normalizationSchemeOverField k f).fromSpecResidueField y ≫
              normalizationOverField k f) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom) ≫
            (Spec.map ((normalizationOverField k f).residueFieldMap y) ≫
              X.fromSpecResidueField (normalizationOverField k f y)) := by
          rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hev').symm.toRingHom) ≫
            Spec.map ((normalizationOverField k f).residueFieldMap y)) ≫
              X.fromSpecResidueField (normalizationOverField k f y) := (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap k Γ(normalizationSchemeOverField k f, ⊤))) ≫
            Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective _ hψ).symm.toRingHom)) ≫
              X.fromSpecResidueField (normalizationOverField k f y) := by rw [hsq']
      _ = _ := Category.assoc _ _ _
  have hdpos : 0 < Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appTop ≫ X.presheaf.germ ⊤ (normalizationOverField k f y) trivial).hom).obj (OXModule.stalk
        (normalizationQuotient X hX) (normalizationOverField k f y))) := by
    have hne := (normalizationQuotientStalk_nonzero_iff_mem_singularLocus X
      (isNagataScheme_of_locallyOfFiniteType_over_field k f)
      (IsCurve.topologicalKrullDim_eq_one (k := k) f) _).mpr hx
    rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hne
    have : Nontrivial ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appTop ≫ X.presheaf.germ ⊤ (normalizationOverField k f y) trivial).hom).obj (OXModule.stalk
        (normalizationQuotient X hX) (normalizationOverField k f y))) := hne
    exact Module.finrank_pos
  -- the normalization is an isomorphism away from the singular point
  have hx₀pt : x₀ (IsLocalRing.closedPoint k) = normalizationOverField k f y :=
    specMap_comp_fromSpecResidueField_apply _ _ _
  have hx₀'pt : x₀' (IsLocalRing.closedPoint Γ(normalizationSchemeOverField k f, ⊤)) = y :=
    specMap_comp_fromSpecResidueField_apply _ _ _
  have hcl : IsClosed ({normalizationOverField k f y} : Set X) :=
    NormalizationQuotientDirectSum.isClosed_singleton_of_not_mem_regularLocus
      X (IsCurve.topologicalKrullDim_eq_one (k := k) f).le _ hx
  let U : X.Opens := ⟨{normalizationOverField k f y}ᶜ, hcl.isOpen_compl⟩
  have hUreg : (U : Set X) ⊆ regularLocus X := fun z hz => by
    by_contra hzr
    have : z ∈ singularLocus X := hzr
    rw [hsingx] at this
    exact hz this
  have hU : IsIso (normalizationOverField k f ∣_ U) :=
    Scheme.isIso_normalization_restrict_of_isNormal X hX U (isNormal_of_subset_regularLocus U hUreg)
  have hfib : ∀ z, normalizationOverField k f z = normalizationOverField k f y ↔ z = y :=
    fun z => ⟨fun h => congrArg Subtype.val (hyuniq ⟨z, h⟩), fun h => h ▸ rfl⟩
  have hpre : ((normalizationOverField k f) ⁻¹ᵁ U : Set (normalizationSchemeOverField k f)) =
      {y}ᶜ := by
    ext z
    exact not_congr (hfib z)
  -- the quotient `𝒬` is the skyscraper `κ(x') / κ(x)` at the singular point
  have hN := isNagataScheme_of_locallyOfFiniteType_over_field k f
  have hdim1 : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) f
  let : Unique ↥(singularLocus X) :=
    { default := ⟨normalizationOverField k f y, hx⟩
      uniq := fun s => Subtype.ext (Set.mem_singleton_iff.mp (hsingx ▸ s.2)) }
  obtain ⟨eQ⟩ :=
    NormalizationQuotientDirectSum.normalizationQuotientIsoCoproductSkyscraper
      X hN hdim1
  obtain ⟨eN⟩ := nonempty_stalk_normalizationQuotient_linearEquiv hX y hmax hsub
  let eT := eQ ≪≫ coproductUniqueIso _ ≪≫
    skyscraperModuleIsoOfIso (normalizationOverField k f y) eN.toModuleIso
  -- `X^ν` is a projective line over `k'`
  have hP1 : ∃ e : normalizationSchemeOverField k f ≅
      Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading
        Γ(normalizationSchemeOverField k f, ⊤) 1),
      e.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff
        Γ(normalizationSchemeOverField k f, ⊤) 1 = f' := by
    have : IsNormal (normalizationSchemeOverField k f) := Scheme.isNormal_normalizationScheme X hX
    have hdim' : topologicalKrullDim (normalizationSchemeOverField k f) = 1 :=
      (isCurve_normalizationOverField_comp k f).topologicalKrullDim_eq_one
    have : IsProper (f' ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k Γ(normalizationSchemeOverField k f, ⊤)))) := hνf ▸ inferInstance
    have : IsProper f' := IsProper.of_comp f' (Spec.map (CommRingCat.ofHom
        (algebraMap k Γ(normalizationSchemeOverField k f, ⊤))))
    have : IsIso
        ((Scheme.ΓSpecIso (.of Γ(normalizationSchemeOverField k f, ⊤))).inv ≫ f'.appTop) := by
      rw [hf'top]; infer_instance
    have hgenus' : genus f' = 0 := by
      have h1 := (normalization_cohomology_of_genus_eq_zero k f hgenus).1
      have : Subsingleton (cohomologyOverField k (normalizationOverField k f ≫ f)
          (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf) 1) :=
        ModuleCat.subsingleton_of_isZero h1
      have : Subsingleton (cohomologyOverField Γ(normalizationSchemeOverField k f, ⊤) f'
          (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf) 1) := this
      exact (finrank_cohomologyOverField_one_unit_eq_genus Γ(normalizationSchemeOverField k f, ⊤)
        f').symm.trans Module.finrank_zero_of_subsingleton
    have hycl : IsClosed ({y} : Set (normalizationSchemeOverField k f)) := by
      have hpre : (normalizationOverField k f).base ⁻¹' {normalizationOverField k f y} = {y} :=
        Set.ext hfib
      rw [← hpre]
      exact hcl.preimage (normalizationOverField k f).base.hom.continuous
    have : IsCurve Γ(normalizationSchemeOverField k f, ⊤) f' :=
      { topologicalKrullDim_eq_one := hdim' }
    let : Algebra Γ(normalizationSchemeOverField k f, ⊤)
        ((normalizationSchemeOverField k f).residueField y) :=
      ((Scheme.ΓSpecIso (.of Γ(normalizationSchemeOverField k f, ⊤))).inv ≫ f'.appTop ≫
        (normalizationSchemeOverField k f).Γevaluation y).hom.toAlgebra
    have hκy : Module.finrank Γ(normalizationSchemeOverField k f, ⊤)
        ((normalizationSchemeOverField k f).residueField y) = 1 := by
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap _ _) hev').finrank_eq,
        Module.finrank_self]
    obtain ⟨L, hL, hdegL⟩ := exists_invertibleCurveDegree_eq_one_of_gcd f' hdim'.le
      (n := 1) (fun _ => y) (fun _ => hycl) (fun _ => IsNormal.stalk_normal y)
      (by simpa using hκy)
    exact exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one f' hdim' hgenus' L hdegL
  refine ⟨Γ(normalizationSchemeOverField k f, ⊤), inferInstance, algΓ, f', x₀', x₀, hνf, hsq,
    ⟨hΓfin, hcountx ▸ Nat.succ_lt_succ hdpos⟩, hP1, hx₀'f', hx₀f,
    ⟨U, by rw [hx₀pt]; rfl, by rw [hx₀'pt]; exact hpre, hU⟩, ?_⟩
  rw [hx₀'pt]
  exact ⟨shortExact_normalizationSequence k f, ⟨eT⟩⟩

end AlgebraicGeometry

end
