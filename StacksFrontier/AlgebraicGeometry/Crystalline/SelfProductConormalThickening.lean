module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormal
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The inverse comparison of the conormal module of the diagonal, from the first-order thickening

Fix a global crystalline situation `(p, (S, I, γ), X)`, an object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` and a product `(U(1), T(1), δ(1))` of it with itself, presented by a
limit binary fan with projections `pr₀, pr₁`.  Let `K ⊆ 𝒪_{T(1)}` be the diagonal ideal and
`K^{[2]}` its divided square, as in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean`, which also builds the
comparison map `(Ω_{X/S})_T → K/K^{[2]}` of the second assertion of [Stacks, Tag 07J1].

This module builds the map in the other direction, by the construction the source's proof of
[Stacks, Tag 07J1] records after the reduction to the affine case.  Let `T'` be the first-order
universal thickening of `T` of [Stacks, Tag 07J2], with `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`; it is an
object of `Cris(X/S)` with two morphisms `p₀, p₁ : T' ⟶ T`, both split by the immersion
`i : T ⟶ T'`.  The universal property of the product gives a unique `q : T' ⟶ T(1)` with
`q ≫ pr₀ = p₀` and `q ≫ pr₁ = p₁`, and `i ≫ q` is the diagonal.  Since `T'` has the same
underlying space as `T`, the open `p₀⁻¹V ⊓ p₁⁻¹V` of `T(1)` pulls back along `q` to `V`, so there
is a map on sections

`q^♯ : Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)}) ⟶ Γ(V, 𝒪_T) ⊕ Ω_{T/S,δ}(V)`.

Its first coordinate is the diagonal on sections, so it carries `K` into the square-zero summand
`Ω_{T/S,δ}` and kills `K^{[2]}`; its second coordinate therefore descends to a `Γ(V, 𝒪_T)`-linear
map `K/K^{[2]} → Ω_{T/S,δ}(V)`.  On the difference of the two coprojections it is the universal
divided power derivation, by the explicit formula `p₁ - p₀ = d_{T/S,δ}` of [Stacks, Tag 07J2].

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderLift` — the morphism
  `q : T' ⟶ T(1)` of `Cris(X/S)` induced by the two retractions of `i`, and
  `smallSelfProductFirstOrderHom` its ambient component.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderPullback` — the map `q^♯` on
  sections over `p₀⁻¹V ⊓ p₁⁻¹V`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalInverse` — **the inverse
  comparison** `K/K^{[2]} → Ω_{T/S,δ}(V)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysι_comp_lift` — `i ≫ q` is the
  diagonal of the self-product.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderHom_preimage` — `q` pulls
  `p₀⁻¹V ⊓ p₁⁻¹V` back to `V`.
* `Crystalline.GlobalCrystallineSituation.sqZeroExtFst_smallSelfProductFirstOrderPullback` — the
  first coordinate of `q^♯` is the diagonal on sections, and
  `sqZeroExtFst_pullback_eq_zero` — it vanishes on the diagonal ideal.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDividedSquare_le_ker` — `q^♯` kills the
  divided square `K^{[2]}`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalInverse_difference` — the
  inverse comparison carries the class of `p₁^♯ f - p₀^♯ f` to the universal divided power
  differential of `f`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalInverse_comp_comparison` —
  **the comparison map of [Stacks, Tag 07J1] followed by the inverse comparison is the comparison
  of the presheaf of divided power differentials with the sheaf it generates**, and
  `injective_smallSelfProductConormalComparison` — so the comparison map is injective wherever
  that one is.
* `smallSelfProductConormalInverse_comp_restrictedComparison` and
  `injective_restrictedCrysDifferentialsConormalComparison` — the same two statements for the
  comparison map read out of `(Ω_{X/S})_T` through [Stacks, Tag 07IZ].

## Implementation notes

As in `SelfProductConormal.lean` the product is supplied as limit data,
`IsLimit (BinaryFan.mk pr₀ pr₁)`.

The two retractions `p₀, p₁ : T' ⟶ T` are the identity on topological spaces, which is what makes
`q ⁻¹ᵁ (p₀⁻¹V ⊓ p₁⁻¹V) = V` hold by `rfl` rather than by transport; the opens of `T'` are the
opens of `T`, recorded by `Crystalline.firstOrderThickeningOpen'`.

Sections of `𝒪_{T'}` over an open are not *syntactically* a square-zero extension — they are the
sections of a scheme whose structure sheaf happens to be one — so goals about them are not
type-correct at `implicit` transparency and `rw` frequently fails on them.  The proofs below
therefore chain `congrArg` and `Eq.trans` against the coordinate lemmas of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SqZeroExt.lean` instead of rewriting.

The `Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})`-module structure on `Ω_{T/S,δ}(V)` used to build the inverse
comparison is restriction of scalars along the diagonal on sections; the diagonal inverts the
first coprojection, so the induced `Γ(V, 𝒪_T)`-action is the standard one and the quotient map
out of `K` may be taken over the larger ring and then restricted.

## What is and is not proved

What is proved here is that the composite `(Ω_{X/S})_T(V) → K/K^{[2]} → Ω_{T/S,δ}(V)` is the
canonical map from the presheaf of divided power differentials to the sheaf it generates —
`Crystalline.dpDifferentialsToSheaf` — and hence that the comparison map is injective on every
open where that map is.  Only one of the two composites is identified here; the other needs the
injectivity of the inverse comparison, which is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalIso.lean`.

The comparison map of `SelfProductConormal.lean` is a map out of the *presheaf*
`Crystalline.dpDifferentialsPresheaf`, while the first-order thickening is built from the *sheaf*
`Crystalline.dpDifferentialsSheaf` it generates.  On an affine open lying over an affine open of
`S` the two have the same sections, by
`Crystalline.bijective_dpDifferentialsToSheaf_app` in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffinePresheaf.lean`, which rests on
`Crystalline.affineSectionsEquiv`, [Stacks, Tag 07IY] clause (2); so on such an open the
hypothesis of `injective_smallSelfProductConormalComparison` is met.  Injectivity of the inverse
comparison — equivalently that `K` is generated modulo `K^{[2]}` by the differences of the two
coprojections — is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalIso.lean`, by the uniqueness half
of the product's universal property tested against the square-zero extension
`Γ(V, 𝒪_T) ⊕ K/K^{[2]}`, which is a quotient of `Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})` by `K^{[2]}`; the
reduction needs the open `p₀⁻¹V ⊓ p₁⁻¹V` of `T(1)` to be affine, which is
`isAffineOpen_smallSelfProductOpen` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalAffine.lean`.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}

/-- The morphism `q : T' ⟶ T(1)`. -/
def smallSelfProductFirstOrderLift (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    firstOrderThickeningCrysObject S B ⟶ D :=
  (BinaryFan.IsLimit.lift' h (firstOrderThickeningCrysP₀ S B)
    (firstOrderThickeningCrysP₁ S B)).1

/-- `q ≫ pr₀ = p₀`. -/
theorem smallSelfProductFirstOrderLift_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductFirstOrderLift h ≫ pr₀ = firstOrderThickeningCrysP₀ S B :=
  (BinaryFan.IsLimit.lift' h (firstOrderThickeningCrysP₀ S B)
    (firstOrderThickeningCrysP₁ S B)).2.1

/-- `q ≫ pr₁ = p₁`. -/
theorem smallSelfProductFirstOrderLift_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductFirstOrderLift h ≫ pr₁ = firstOrderThickeningCrysP₁ S B :=
  (BinaryFan.IsLimit.lift' h (firstOrderThickeningCrysP₀ S B)
    (firstOrderThickeningCrysP₁ S B)).2.2

/-- The ambient morphism of schemes `T' ⟶ T(1)`. -/
abbrev smallSelfProductFirstOrderHom (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom ⟶
      D.obj.thickening.target.scheme :=
  (smallSelfProductFirstOrderLift h).hom.targetHom.hom

/-- The ambient morphism composed with the first projection. -/
theorem smallSelfProductFirstOrderHom_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductFirstOrderHom h ≫ pr₀.hom.targetHom.hom =
      firstOrderThickeningProjHom B.obj.thickening.target S.S.scheme B.obj.toBase.hom :=
  congrArg (fun φ : firstOrderThickeningCrysObject S B ⟶ B ↦ φ.hom.targetHom.hom)
    (smallSelfProductFirstOrderLift_fst h)

/-- The ambient morphism composed with the second projection. -/
theorem smallSelfProductFirstOrderHom_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductFirstOrderHom h ≫ pr₁.hom.targetHom.hom =
      firstOrderThickeningP₁Hom B.obj.thickening.target S.S.scheme B.obj.toBase.hom :=
  congrArg (fun φ : firstOrderThickeningCrysObject S B ⟶ B ↦ φ.hom.targetHom.hom)
    (smallSelfProductFirstOrderLift_snd h)

/-- The two retractions of `T ⟶ T'` are the identity on spaces, so they pull an open back to
itself. -/
theorem firstOrderThickeningProjHom_preimage
    (V : B.obj.thickening.target.scheme.Opens) :
    firstOrderThickeningProjHom B.obj.thickening.target S.S.scheme B.obj.toBase.hom ⁻¹ᵁ V =
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V := rfl

/-- The same for the derivation-shifted retraction. -/
theorem firstOrderThickeningP₁Hom_preimage
    (V : B.obj.thickening.target.scheme.Opens) :
    firstOrderThickeningP₁Hom B.obj.thickening.target S.S.scheme B.obj.toBase.hom ⁻¹ᵁ V =
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V := rfl

/-- `q` pulls `p₀⁻¹V ⊓ p₁⁻¹V` back to `V`. -/
theorem smallSelfProductFirstOrderHom_preimage (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductFirstOrderHom h ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V =
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V := by
  have hrw : smallSelfProductFirstOrderHom h ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V =
      (smallSelfProductFirstOrderHom h ≫ pr₀.hom.targetHom.hom) ⁻¹ᵁ V ⊓
        (smallSelfProductFirstOrderHom h ≫ pr₁.hom.targetHom.hom) ⁻¹ᵁ V := rfl
  rw [hrw, smallSelfProductFirstOrderHom_fst h, smallSelfProductFirstOrderHom_snd h,
    firstOrderThickeningProjHom_preimage, firstOrderThickeningP₁Hom_preimage, inf_idem]

/-- `q^♯ : Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)}) ⟶ Γ(V, 𝒪_{T'})`. -/
def smallSelfProductFirstOrderPullback (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ⟶
      Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
        firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) :=
  (smallSelfProductFirstOrderHom h).appLE (smallSelfProductOpen pr₀ pr₁ V)
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
    (le_of_eq (smallSelfProductFirstOrderHom_preimage h V).symm)

/-- The immersion of `T` into `T'` followed by `q` is the diagonal. -/
theorem firstOrderThickeningCrysι_comp_lift (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    firstOrderThickeningCrysι S B ≫ smallSelfProductFirstOrderLift h =
      smallSelfProductDiagonal h := by
  refine BinaryFan.IsLimit.hom_ext h ?_ ?_
  · rw [BinaryFan.mk_fst, Category.assoc, smallSelfProductFirstOrderLift_fst h,
      firstOrderThickeningCrysι_comp_P₀, smallSelfProductDiagonal_fst]
  · rw [BinaryFan.mk_snd, Category.assoc, smallSelfProductFirstOrderLift_snd h,
      firstOrderThickeningCrysι_comp_P₁, smallSelfProductDiagonal_snd]

/-- The same on ambient schemes. -/
theorem firstOrderThickeningι_comp_firstOrderHom (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom ≫
        smallSelfProductFirstOrderHom h =
      (smallSelfProductAmbientDiagonal h).hom :=
  congrArg (fun φ : B ⟶ D ↦ φ.hom.targetHom.hom) (firstOrderThickeningCrysι_comp_lift h)

/-- The immersion of `T` into `T'` is the identity on spaces. -/
theorem firstOrderThickeningι_preimage (V : B.obj.thickening.target.scheme.Opens) :
    firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom ⁻¹ᵁ
        firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V = V :=
  rfl

/-- `p₀ : T' ⟶ T` on sections over `V` is the map `p₀ : 𝒪_T ⟶ 𝒪_{T'}`. -/
theorem firstOrderThickeningProjHom_appLE (V : B.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningProjHom B.obj.thickening.target S.S.scheme B.obj.toBase.hom).appLE V
        (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
        le_rfl =
      (firstOrderThickeningP₀ B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op V) :=
  (Scheme.Hom.app_eq_appLE _).symm.trans
    (firstOrderThickeningProjHom_c_app B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      (op V))

/-- `p₁ : T' ⟶ T` on sections over `V` is the map `p₁ : 𝒪_T ⟶ 𝒪_{T'}`. -/
theorem firstOrderThickeningP₁Hom_appLE (V : B.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningP₁Hom B.obj.thickening.target S.S.scheme B.obj.toBase.hom).appLE V
        (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
        le_rfl =
      (firstOrderThickeningP₁ B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op V) :=
  (Scheme.Hom.app_eq_appLE _).symm.trans
    (firstOrderThickeningP₁Hom_c_app B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      (op V))

/-- The first coordinate of `q^♯` is the diagonal on sections. -/
theorem sqZeroExtFst_smallSelfProductFirstOrderPullback (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    sqZeroExtFst (smallSelfProductFirstOrderPullback h V y) =
      (smallSelfProductAmbientDiagonal h).hom.appLE (smallSelfProductOpen pr₀ pr₁ V) V
        (le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm) y := by
  have hc := Scheme.Hom.appLE_comp_appLE
    (firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom)
    (smallSelfProductFirstOrderHom h) (smallSelfProductOpen pr₀ pr₁ V)
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) V
    (le_of_eq (smallSelfProductFirstOrderHom_preimage h V).symm) le_rfl
  have hap := congrArg
    (fun φ : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ⟶
        Γ(B.obj.thickening.target.scheme, V) ↦ φ y) hc
  simp only [CommRingCat.comp_apply] at hap
  have hcong := appLE_congr_hom (firstOrderThickeningι_comp_firstOrderHom h)
    (smallSelfProductOpen pr₀ pr₁ V) V
    (by
      rw [firstOrderThickeningι_comp_firstOrderHom h]
      exact le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm)
    (le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm)
  have happ : (firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom).appLE
      (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) V
      le_rfl =
    (firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
      (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) :=
    (Scheme.Hom.app_eq_appLE _).symm
  have hfst : sqZeroExtFst (smallSelfProductFirstOrderPullback h V y) =
      (firstOrderThickeningι B.obj.thickening.target S.S.scheme B.obj.toBase.hom).appLE
        (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) V
        le_rfl (smallSelfProductFirstOrderPullback h V y) := by
    rw [happ]
    rfl
  rw [hfst]
  exact hap.trans (congrArg (fun φ : Γ(D.obj.thickening.target.scheme,
    smallSelfProductOpen pr₀ pr₁ V) ⟶ Γ(B.obj.thickening.target.scheme, V) ↦ φ y) hcong)

/-- `q^♯` composed with the first coprojection is `p₀ : 𝒪_T ⟶ 𝒪_{T'}`. -/
theorem smallSelfProductFirstOrderPullback_firstCoprojection
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens) :
    firstCoprojectionSection pr₀ pr₁ V ≫ smallSelfProductFirstOrderPullback h V =
      (firstOrderThickeningP₀ B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).app (op V) := by
  have hc := Scheme.Hom.appLE_comp_appLE (smallSelfProductFirstOrderHom h)
    pr₀.hom.targetHom.hom V (smallSelfProductOpen pr₀ pr₁ V)
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
    (smallSelfProductOpen_le_fst pr₀ pr₁ V)
    (le_of_eq (smallSelfProductFirstOrderHom_preimage h V).symm)
  refine hc.trans ?_
  refine (appLE_congr_hom (smallSelfProductFirstOrderHom_fst h) V
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) _
    le_rfl).trans ?_
  exact firstOrderThickeningProjHom_appLE V

/-- `q^♯` composed with the second coprojection is `p₁ : 𝒪_T ⟶ 𝒪_{T'}`. -/
theorem smallSelfProductFirstOrderPullback_secondCoprojection
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens) :
    secondCoprojectionSection pr₀ pr₁ V ≫ smallSelfProductFirstOrderPullback h V =
      (firstOrderThickeningP₁ B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).app (op V) := by
  have hc := Scheme.Hom.appLE_comp_appLE (smallSelfProductFirstOrderHom h)
    pr₁.hom.targetHom.hom V (smallSelfProductOpen pr₀ pr₁ V)
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
    (smallSelfProductOpen_le_snd pr₀ pr₁ V)
    (le_of_eq (smallSelfProductFirstOrderHom_preimage h V).symm)
  refine hc.trans ?_
  refine (appLE_congr_hom (smallSelfProductFirstOrderHom_snd h) V
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) _
    le_rfl).trans ?_
  exact firstOrderThickeningP₁Hom_appLE V

/-- `q^♯` is a homomorphism of divided power rings. -/
theorem smallSelfProductFirstOrderPullback_isDPMorphism (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V))).IsDPMorphism
      (firstOrderThickeningDividedPowers B.obj.thickening.target S.S.scheme B.obj.toBase.hom
        (op V))
      (smallSelfProductFirstOrderPullback h V).hom :=
  appLE_isDPMorphism (smallSelfProductFirstOrderLift h).hom.targetHom
    (smallSelfProductOpen pr₀ pr₁ V)
    (firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
    (le_of_eq (smallSelfProductFirstOrderHom_preimage h V).symm)

/-- A section of the diagonal ideal has vanishing first coordinate after `q^♯`. -/
theorem sqZeroExtFst_pullback_eq_zero (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    {y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)}
    (hy : y ∈ smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) :
    sqZeroExtFst (smallSelfProductFirstOrderPullback h V y) = 0 := by
  rw [sqZeroExtFst_smallSelfProductFirstOrderPullback]
  have h0 : ((smallSelfProductAmbientDiagonal h).hom.app
      (smallSelfProductOpen pr₀ pr₁ V)).hom y = 0 := RingHom.mem_ker.mp hy
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, h0, map_zero]
  rfl

/-- A section of `𝒪_{T'}` with both coordinates zero is zero. -/
theorem firstOrderThickening_eq_zero_of_coordinates
    (V : B.obj.thickening.target.scheme.Opens)
    {z : Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)}
    (h1 : sqZeroExtFst z = 0) (h2 : sqZeroExtSnd z = 0) : z = 0 :=
  sqZeroExt_ext (h1.trans sqZeroExtFst_zero.symm) (h2.trans sqZeroExtSnd_zero.symm)

/-- **`q^♯` kills the divided square.**  The pullback of a section of `K` lies in the square-zero
summand, so a product of two of them vanishes and so does a divided power of order at least two
of one of them. -/
theorem smallSelfProductDividedSquare_le_ker (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) ≤
      RingHom.ker (smallSelfProductFirstOrderPullback h V).hom := by
  rw [smallSelfProductDividedSquare, Ideal.add_eq_sup]
  refine sup_le ?_ (Ideal.span_le.mpr ?_)
  · rw [pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb ↦ RingHom.mem_ker.mpr ?_
    rw [map_mul]
    refine firstOrderThickening_eq_zero_of_coordinates V ?_ ?_
    · exact (sqZeroExtFst_mul _ _).trans (by
        rw [sqZeroExtFst_pullback_eq_zero h V ha, zero_mul])
    · exact (sqZeroExtSnd_mul _ _).trans (by
        rw [sqZeroExtFst_pullback_eq_zero h V ha, sqZeroExtFst_pullback_eq_zero h V hb,
          zero_smul, zero_smul, add_zero])
  · rintro y ⟨n, hn, x, hx, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    have hxJ : x ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) :=
      smallSelfProductDiagonalIdeal_le h _ hx
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hmem : smallSelfProductFirstOrderPullback h V x ∈
        firstOrderThickeningIdeal B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op V) :=
      (smallSelfProductFirstOrderPullback_isDPMorphism h V).ideal_comp
        (Ideal.mem_map_of_mem _ hxJ)
    refine ((smallSelfProductFirstOrderPullback_isDPMorphism h V).map_dpow
      (n := k + 1) hxJ).trans ?_
    have hfst0 := sqZeroExtFst_pullback_eq_zero h V hx
    refine firstOrderThickening_eq_zero_of_coordinates V ?_ ?_
    · refine (congrArg sqZeroExtFst (firstOrderThickeningDividedPowers_dpow_succ
        B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op V) k hmem)).trans ?_
      refine (sqZeroExtFst_mk _ _).trans ?_
      exact (congrArg
        ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow (k + 1))
        hfst0).trans (DividedPowers.dpow_eval_zero _ (by omega))
    · refine (congrArg sqZeroExtSnd (firstOrderThickeningDividedPowers_dpow_succ
        B.obj.thickening.target S.S.scheme B.obj.toBase.hom (op V) k hmem)).trans ?_
      refine (sqZeroExtSnd_mk _ _).trans ?_
      have hk0 : (B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow k
          (sqZeroExtFst (smallSelfProductFirstOrderPullback h V x)) = 0 :=
        (congrArg ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow k)
          hfst0).trans (DividedPowers.dpow_eval_zero _ (by omega))
      rw [hk0, zero_smul]
      rfl

/-- **The inverse comparison `K/K^{[2]} → (Ω_{X/S})_T(V)`**, the second coordinate of `q^♯`.
A section of `K` pulls back into the square-zero summand `Ω_{T/S,δ}` of `𝒪_{T'}`, and the
divided square is killed, so the assignment descends to the conormal module; the scalars match
because the first coprojection is inverted by the diagonal. -/
def smallSelfProductConormalInverse (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductConormal h V →ₗ[Γ(B.obj.thickening.target.scheme, V)]
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
        (op V)) := by
  letI : Algebra Γ(B.obj.thickening.target.scheme, V)
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) :=
    (firstCoprojectionSection pr₀ pr₁ V).hom.toAlgebra
  letI : Module Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
        (op V)) :=
    Module.compHom _ (smallSelfProductDiagonalSection h V).hom
  letI : IsScalarTower Γ(B.obj.thickening.target.scheme, V)
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
        (op V)) :=
    IsScalarTower.of_algebraMap_smul (by
      intro r x
      change smallSelfProductDiagonalSection h V (firstCoprojectionSection pr₀ pr₁ V r) • x = r • x
      rw [smallSelfProductDiagonalSection_firstCoprojectionSection])
  let φ : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) →ₗ[
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)]
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
        (op V)) := by
    refine
      { toFun := fun k ↦ (sqZeroExtSnd (smallSelfProductFirstOrderPullback h V k.val) :
          ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj
            (op V)))
        map_add' := ?_
        map_smul' := ?_ }
    · intro k l
      exact (congrArg sqZeroExtSnd (map_add (smallSelfProductFirstOrderPullback h V).hom
        k.val l.val)).trans (sqZeroExtSnd_add _ _)
    · intro r k
      refine (congrArg sqZeroExtSnd (map_mul (smallSelfProductFirstOrderPullback h V).hom
        r k.val)).trans ?_
      refine (sqZeroExtSnd_mul _ _).trans ?_
      rw [sqZeroExtFst_pullback_eq_zero h V k.2, zero_smul, add_zero,
        sqZeroExtFst_smallSelfProductFirstOrderPullback]
      rfl
  let ψ := (smallSelfProductDiagonalRelations h V).liftQ φ (by
    intro x hx
    change sqZeroExtSnd (smallSelfProductFirstOrderPullback h V x.val) = 0
    exact (congrArg sqZeroExtSnd
      (RingHom.mem_ker.mp (smallSelfProductDividedSquare_le_ker h V hx))).trans sqZeroExtSnd_zero)
  let e : smallSelfProductConormal h V ≃ₗ[Γ(B.obj.thickening.target.scheme, V)]
      ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ⧸
        smallSelfProductDiagonalRelations h V :=
    { toAddEquiv := AddEquiv.refl _
      map_smul' := fun _ _ ↦ rfl }
  exact (ψ.restrictScalars Γ(B.obj.thickening.target.scheme, V)).comp e.toLinearMap

/-- The inverse comparison sends the class of a section of `K` to the second coordinate of its
pullback to `T'`. -/
theorem smallSelfProductConormalInverse_class (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (k : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductConormalInverse h V (smallSelfProductClass h V k) =
      sqZeroExtSnd (smallSelfProductFirstOrderPullback h V k.val) := rfl

/-- **The inverse comparison carries the difference of the two coprojections to the universal
divided power differential.**  The pullback of `p₁^♯ f - p₀^♯ f` along `q` is the difference of
the two maps `𝒪_T ⟶ 𝒪_{T'}`, which is `(0, d f)`. -/
theorem smallSelfProductConormalInverse_difference (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductConormalInverse h V (smallSelfProductDifference h V f) =
      sheafApp B.obj.thickening.target S.S.scheme B.obj.toBase.hom V f := by
  have h0 := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
          firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) ↦
      φ f) (smallSelfProductFirstOrderPullback_firstCoprojection h V)
  have h1 := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
          firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) ↦
      φ f) (smallSelfProductFirstOrderPullback_secondCoprojection h V)
  simp only [CommRingCat.comp_apply] at h0 h1
  have hq : smallSelfProductFirstOrderPullback h V
      (smallSelfProductDifferenceHom h V f).val =
      sqZeroExtMk 0 (sheafApp B.obj.thickening.target S.S.scheme B.obj.toBase.hom V f) := by
    rw [smallSelfProductDifferenceHom_coe, map_sub, h0, h1]
    exact firstOrderThickeningP₁_sub_P₀ B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      (op V) f
  exact (congrArg sqZeroExtSnd hq).trans (sqZeroExtSnd_mk _ _)

/-- **The inverse comparison of the second assertion of [Stacks, Tag 07J1].**  The comparison map
`(Ω_{X/S})_T(V) → K/K^{[2]}` followed by the map back out of the first-order thickening is the
comparison of the presheaf of divided power differentials with the sheaf it generates.  In
particular the comparison map is injective whenever that comparison is.  This is a step of the
proof; the second assertion itself is
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIsoConormalSheaf`. -/
theorem smallSelfProductConormalInverse_comp_comparison (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (x : ↥((dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom).obj (op V))) :
    smallSelfProductConormalInverse h V ((smallSelfProductConormalComparison h V).hom x) =
      (dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op V)
        x := by
  have hx : x ∈ Submodule.span Γ(B.obj.thickening.target.scheme, V)
      (Set.range (presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V).d) :=
    (dpConstDifferentials_span (baseAppLE B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)
      (B.obj.thickening.target.dividedPowers.dividedPowers (op V))
      (baseSections B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)).ge
      Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact (congrArg (smallSelfProductConormalInverse h V)
        (smallSelfProductConormalComparison_d h V g)).trans
        (smallSelfProductConormalInverse_difference h V g)
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
  | smul r a _ ha => rw [map_smul, map_smul, map_smul, ha]

/-- **The comparison map is injective whenever the presheaf of divided power differentials
injects into the sheaf it generates over `V`.** -/
theorem injective_smallSelfProductConormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (hinj : Function.Injective ((dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom).app (op V)).hom) :
    Function.Injective (smallSelfProductConormalComparison h V).hom := by
  intro a b hab
  refine hinj ?_
  rw [← smallSelfProductConormalInverse_comp_comparison h V,
    ← smallSelfProductConormalInverse_comp_comparison h V]
  exact congrArg (smallSelfProductConormalInverse h V) hab

/-- **The same read out of `(Ω_{X/S})_T`.**  Through [Stacks, Tag 07IZ] the comparison map out
of the restriction of the crystalline differentials, followed by the inverse comparison, is again
the comparison of the presheaf of divided power differentials with the sheaf it generates. -/
theorem smallSelfProductConormalInverse_comp_restrictedComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens)
    (x : ↥((restrictedCrysDifferentials S B.obj).obj (op V))) :
    smallSelfProductConormalInverse h V
        ((restrictedCrysDifferentialsConormalComparison h V).hom x) =
      (dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op V)
        ((comparisonIsoApp B.obj V).inv.hom x) :=
  smallSelfProductConormalInverse_comp_comparison h V ((comparisonIsoApp B.obj V).inv.hom x)

/-- **The comparison map out of `(Ω_{X/S})_T` is injective whenever the presheaf of divided power
differentials injects into the sheaf it generates over `V`.** -/
theorem injective_restrictedCrysDifferentialsConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens)
    (hinj : Function.Injective ((dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom).app (op V)).hom) :
    Function.Injective (restrictedCrysDifferentialsConormalComparison h V).hom := by
  intro a b hab
  have hinv := injective_smallSelfProductConormalComparison h V hinj
    (a₁ := (comparisonIsoApp B.obj V).inv.hom a) (a₂ := (comparisonIsoApp B.obj V).inv.hom b) hab
  have hiso : Function.Injective (comparisonIsoApp B.obj V).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (comparisonIsoApp B.obj V).inv).1
  exact hiso hinv

end Crystalline.GlobalCrystallineSituation

end
