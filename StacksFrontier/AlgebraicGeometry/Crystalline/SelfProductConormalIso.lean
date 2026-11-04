module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineAffineQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsAffinePresheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormalAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormalSquareZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormalThickening

/-!
# The comparison `(Ω_{X/S})_T → K/K^{[2]}` is an isomorphism on an affine open

Fix a global crystalline situation `(p, (S, I, γ), X)`, an object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` and a product `(U(1), T(1), δ(1))` of it with itself, presented by a
limit binary fan with projections `pr₀, pr₁`.  Let `K ⊆ 𝒪_{T(1)}` be the diagonal ideal, `K^{[2]}`
its divided square and `K/K^{[2]}` the conormal module of
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean`, where the comparison map
`(Ω_{X/S})_T → K/K^{[2]}` of the second assertion of [Stacks, Tag 07J1] is built.

This module supplies the last input of that assertion's proof, the one the source obtains after
reducing to the affine case: the kernel of `q^♯`, the map on sections of the morphism
`q : T' ⟶ T(1)` out of the first-order universal thickening of [Stacks, Tag 07J2], is contained
in `K^{[2]}`.  The argument is the *uniqueness* half of the product's universal property.  Over
an affine open `V` of `T` lying over an affine open of `S` the quotient `R/K^{[2]}` of
`R = Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})` is the trivial square-zero extension
`Γ(V, 𝒪_T) ⊕ K/K^{[2]}`, with divided powers, by
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalSquareZero.lean`; the sections of
`𝒪_{T'}` over `V` map to it by `(a, ω) ↦ (a, α(ω))`, where `α` is the comparison map read out of
the *sheaf* of divided power differentials.  That map and the quotient map `R ⟶ R/K^{[2]}` agree
after both coprojections, so the two morphisms of `Cris(X/S)` they present into the product agree,
and therefore so do they; the quotient map therefore factors through `q^♯`, which forces
`ker q^♯ ⊆ K^{[2]}`.

Since the comparison map of [Stacks, Tag 07J1] is a map out of the *presheaf* of divided power
differentials while the first-order thickening is built from the *sheaf*, the two are reconciled
by `Crystalline.bijective_dpDifferentialsToSheaf_app` in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffinePresheaf.lean`, which is why the
affineness hypotheses on `V` and on the open of `S` below it are carried throughout.  They are
the hypotheses the source's own proof makes.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.dpDifferentialsSheafSectionsEquiv` — the sections of the
  presheaf of divided power differentials over `V`, identified with the sections of the sheaf.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalSheafComparison` — the
  comparison map read out of the sheaf, `Ω_{T/S,δ}(V) → K/K^{[2]}`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderToSquareZero` — the map
  `Γ(V, 𝒪_{T'}) ⟶ Γ(V, 𝒪_T) ⊕ K/K^{[2]}` of divided power rings, `(a, ω) ↦ (a, α(ω))`.

## Main results

* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalInverse_sheafComparison` — the
  inverse comparison undoes the comparison read out of the sheaf.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderToSquareZero_first` and
  `_second` — the map to the square-zero extension agrees with the quotient map after both
  coprojections.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderToSquareZero_isDPMorphism` —
  it is a homomorphism of divided power rings.
* `Crystalline.GlobalCrystallineSituation.injective_smallSelfProductConormalInverse_of_ker_le` and
  `Crystalline.GlobalCrystallineSituation.bijective_smallSelfProductConormalComparison_of_ker_le`
  — from `ker q^♯ ⊆ K^{[2]}`, the inverse comparison is injective and the comparison map is
  bijective.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductFirstOrderPullback_ker_le` — **the
  containment `ker q^♯ ⊆ K^{[2]}`**, from the uniqueness half of the product's universal
  property.
* `Crystalline.GlobalCrystallineSituation.injective_smallSelfProductConormalInverse` — the
  inverse comparison is injective.
* `Crystalline.GlobalCrystallineSituation.bijective_smallSelfProductConormalComparison` and
  `isIso_smallSelfProductConormalComparison` — the affine-local step of the second assertion:
  the comparison map is an isomorphism over an affine open of `T` lying over an affine open
  of `S`.
* `Crystalline.GlobalCrystallineSituation.bijective_restrictedCrysDifferentialsConormalComparison`
  and `isIso_restrictedCrysDifferentialsConormalComparison` — the same read out of
  `(Ω_{X/S})_T` itself, through [Stacks, Tag 07IZ].
* `Crystalline.exists_isAffineOpen_over_isAffineOpen` — those hypotheses hold on a basis of the
  topology of `T`.
* `Crystalline.GlobalCrystallineSituation.exists_isIso_smallSelfProductConormalComparison`,
  `exists_isIso_restrictedCrysDifferentialsConormalComparison` and
  `isBasis_isIso_restrictedCrysDifferentialsConormalComparison` — **Stacks, Tag 07J1**, the
  second assertion with no hypothesis on the open: every point of every open of `T` has a
  neighbourhood inside it on which the comparison is an isomorphism, so those opens form a basis
  of the topology of `T`.

## What is and is not proved

The affine-local step is proved over an affine open of `T` lying over an affine open of `S`,
which is where the source's proof establishes it — [Stacks, Tag 07J1] reduces to the affine case
before invoking the ring-level statement.  Those are hypotheses of the source's *proof* and not
of its statement, so they are discharged here against
`Crystalline.exists_isAffineOpen_over_isAffineOpen`: the three results carrying the tag quantify
over all opens of `T` and all points of them, and say the comparison is an isomorphism on a
neighbourhood basis.  That is why the tag sits on them and not on the affine-local step.

The identification is **not** assembled into an isomorphism of sheaves of `𝒪_T`-modules.  The
obstruction is not this module: `K/K^{[2]}` is built open by open in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean` because the divided second
power exists in the library only for an ideal of a ring, as
`Crystalline.secondDividedPowerIdeal` in
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/Diagonal.lean`, and there is no
divided power of a quasi-coherent subsheaf of the structure sheaf, hence no sheaf `K^{[2]}`, no
quotient sheaf `K/K^{[2]}` and no morphism of sheaves to call an isomorphism.  A basis of opens
on which the comparison is an isomorphism is what an equality of sheaves amounts to for the open
by open presentation, and it is what `isBasis_isIso_restrictedCrysDifferentialsConormalComparison`
states.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- **The affine opens lying over an affine open of the target form a basis.**  Given a point of
an open `U` of `X`, choose an affine open of `Y` around its image and then an affine open of `X`
inside `U` and inside the preimage of that one.  This is what makes the hypotheses of the results
below — affineness of the open of `T` and of an open of `S` above it — hold on a basis of the
topology of `T`, so that they restrict nothing. -/
theorem exists_isAffineOpen_over_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (VS : Y.Opens), IsAffineOpen V ∧ IsAffineOpen VS ∧ x ∈ V ∧ V ≤ U ∧
      V ≤ f ⁻¹ᵁ VS := by
  obtain ⟨VS, hVS, hxVS, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U ⊓ f ⁻¹ᵁ VS) ⟨hx, hxVS⟩
  exact ⟨V, VS, hV, hVS, hxV, hVle.trans inf_le_left, hVle.trans inf_le_right⟩

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}
  {V : B.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V)
  {VS : S.S.scheme.Opens} (hle : V ≤ B.obj.toBase.hom ⁻¹ᵁ VS) (hVS : IsAffineOpen VS)

/-! ### The comparison map read out of the sheaf of divided power differentials -/

include hV hle hVS in
/-- **The sections of the presheaf of divided power differentials over an affine open lying over
an affine open of `S` are the sections of the sheaf it generates.**  This is
`Crystalline.bijective_dpDifferentialsToSheaf_app` read as a linear equivalence. -/
def dpDifferentialsSheafSectionsEquiv :
    ↥((dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj (op V))
      ≃ₗ[Γ(B.obj.thickening.target.scheme, V)]
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).obj (op V)) :=
  let φ : ↥((dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).obj (op V)) →ₗ[Γ(B.obj.thickening.target.scheme, V)]
      ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).obj (op V)) :=
    { toFun := fun x ↦
        (dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app (op V) x
      map_add' := fun x y ↦ map_add ((dpDifferentialsToSheaf B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom).app (op V)).hom x y
      map_smul' := fun r x ↦ map_smul ((dpDifferentialsToSheaf B.obj.thickening.target
        S.S.scheme B.obj.toBase.hom).app (op V)).hom r x }
  LinearEquiv.ofBijective φ
    (bijective_dpDifferentialsToSheaf_app B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      hV hle hVS)

include hV hle hVS in
/-- The identification carries the universal differential of the presheaf to the universal
divided power derivation of the sheaf. -/
theorem dpDifferentialsSheafSectionsEquiv_d (b : Γ(B.obj.thickening.target.scheme, V)) :
    dpDifferentialsSheafSectionsEquiv hV hle hVS
        ((presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V).d b) =
      sheafApp B.obj.thickening.target S.S.scheme B.obj.toBase.hom V b := rfl

include hV hle hVS in
/-- **The comparison map of [Stacks, Tag 07J1] read out of the sheaf of divided power
differentials.**  On an affine open lying over an affine open of `S` the presheaf and the sheaf
have the same sections, so the comparison map transports. -/
def smallSelfProductConormalSheafComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj (op V))
      →ₗ[Γ(B.obj.thickening.target.scheme, V)] ↥(smallSelfProductConormal h V) where
  toFun x := (smallSelfProductConormalComparison h V).hom
    ((dpDifferentialsSheafSectionsEquiv hV hle hVS).symm x)
  map_add' x y := by
    refine (congrArg (smallSelfProductConormalComparison h V).hom
      (map_add (dpDifferentialsSheafSectionsEquiv hV hle hVS).symm x y)).trans ?_
    exact map_add (smallSelfProductConormalComparison h V).hom _ _
  map_smul' r x := by
    refine (congrArg (smallSelfProductConormalComparison h V).hom
      (map_smul (dpDifferentialsSheafSectionsEquiv hV hle hVS).symm r x)).trans ?_
    exact map_smul (smallSelfProductConormalComparison h V).hom r _

include hV hle hVS in
/-- **The comparison read out of the sheaf carries the universal divided power derivation to the
class of `p₁^♯ f - p₀^♯ f`.** -/
theorem smallSelfProductConormalSheafComparison_sheafApp
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (b : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductConormalSheafComparison hV hle hVS h
        (sheafApp B.obj.thickening.target S.S.scheme B.obj.toBase.hom V b) =
      smallSelfProductDifference h V b := by
  have he : (dpDifferentialsSheafSectionsEquiv hV hle hVS).symm
      (sheafApp B.obj.thickening.target S.S.scheme B.obj.toBase.hom V b) =
      (presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V).d b :=
    (dpDifferentialsSheafSectionsEquiv hV hle hVS).symm_apply_eq.mpr
      (dpDifferentialsSheafSectionsEquiv_d hV hle hVS b).symm
  show (smallSelfProductConormalComparison h V).hom
    ((dpDifferentialsSheafSectionsEquiv hV hle hVS).symm _) = _
  rw [he]
  exact smallSelfProductConormalComparison_d h V b

include hV hle hVS in
/-- **The inverse comparison undoes the comparison read out of the sheaf.**  Composed with the
comparison out of the presheaf the inverse comparison is the map to the sheaf, and the two
readings of the comparison differ by exactly that map. -/
theorem smallSelfProductConormalInverse_sheafComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (x : ↥((dpDifferentialsModules B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom).obj (op V))) :
    smallSelfProductConormalInverse h V
        (smallSelfProductConormalSheafComparison hV hle hVS h x) = x := by
  show smallSelfProductConormalInverse h V ((smallSelfProductConormalComparison h V).hom
    ((dpDifferentialsSheafSectionsEquiv hV hle hVS).symm x)) = x
  rw [smallSelfProductConormalInverse_comp_comparison h V]
  exact (dpDifferentialsSheafSectionsEquiv hV hle hVS).apply_symm_apply x

/-! ### The map of the first-order thickening into the square-zero extension -/

include hV hle hVS in
/-- **The map `Γ(V, 𝒪_{T'}) ⟶ Γ(V, 𝒪_T) ⊕ K/K^{[2]}`**, the identity on the first coordinate and
the comparison map read out of the sheaf on the second.  Both the source and the target are
square-zero extensions of `Γ(V, 𝒪_T)`, and the comparison is linear, so this is a ring
homomorphism. -/
def smallSelfProductFirstOrderToSquareZero (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
        firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) →+*
      TrivSqZeroExt Γ(B.obj.thickening.target.scheme, V) (smallSelfProductConormal h V) where
  toFun y := ⟨sqZeroExtFst y, smallSelfProductConormalSheafComparison hV hle hVS h
    (sqZeroExtSnd y)⟩
  map_one' :=
    TrivSqZeroExt.ext rfl (map_zero (smallSelfProductConormalSheafComparison hV hle hVS h))
  map_mul' x y :=
    TrivSqZeroExt.ext rfl
      ((congrArg (smallSelfProductConormalSheafComparison hV hle hVS h)
          (sqZeroExtSnd_mul x y)).trans
        ((map_add (smallSelfProductConormalSheafComparison hV hle hVS h) _ _).trans
          (congrArg₂ (· + ·)
            (map_smul (smallSelfProductConormalSheafComparison hV hle hVS h) _ _)
            ((map_smul (smallSelfProductConormalSheafComparison hV hle hVS h) _ _).trans
              (op_smul_eq_smul _ _).symm))))
  map_zero' :=
    TrivSqZeroExt.ext rfl (map_zero (smallSelfProductConormalSheafComparison hV hle hVS h))
  map_add' x y :=
    TrivSqZeroExt.ext rfl
      ((congrArg (smallSelfProductConormalSheafComparison hV hle hVS h)
          (sqZeroExtSnd_add x y)).trans
        (map_add (smallSelfProductConormalSheafComparison hV hle hVS h) _ _))

include hV hle hVS in
/-- The first coordinate of the map to the square-zero extension. -/
theorem smallSelfProductFirstOrderToSquareZero_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (y : Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)) :
    (smallSelfProductFirstOrderToSquareZero hV hle hVS h y).fst = sqZeroExtFst y := rfl

include hV hle hVS in
/-- The second coordinate of the map to the square-zero extension. -/
theorem smallSelfProductFirstOrderToSquareZero_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (y : Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
      firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V)) :
    (smallSelfProductFirstOrderToSquareZero hV hle hVS h y).snd =
      smallSelfProductConormalSheafComparison hV hle hVS h (sqZeroExtSnd y) := rfl

/-- If `q^♯` carries a coprojection section to the map `P` with the right coordinates, then the
map to the square-zero extension agrees with the graph of the class map on its image. -/
private theorem smallSelfProductFirstOrderToSquareZero_pullback_eq_graph
    (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (c : Γ(B.obj.thickening.target.scheme, V) ⟶
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))
    (P : Γ(B.obj.thickening.target.scheme, V) ⟶
      Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
        firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom V))
    (hP : c ≫ smallSelfProductFirstOrderPullback h V = P)
    (b : Γ(B.obj.thickening.target.scheme, V))
    (hfst : sqZeroExtFst (P b) = smallSelfProductDiagonalSection h V (c b))
    (hsnd : smallSelfProductConormalSheafComparison hV hle hVS h (sqZeroExtSnd (P b)) =
      smallSelfProductClassOf h V (c b)) :
    smallSelfProductFirstOrderToSquareZero hV hle hVS h
        (smallSelfProductFirstOrderPullback h V (c b)) =
      smallSelfProductGraphRingHom h V (c b) := by
  subst hP
  exact TrivSqZeroExt.ext hfst hsnd

include hV hle hVS in
/-- **On a section pulled back along the first coprojection the map to the square-zero extension
agrees with the graph of the class map.**  The pullback of `p₀^♯ b` to `T'` is `(b, 0)`, and the
graph sends `p₀^♯ b` to `(b, 0)` as well. -/
theorem smallSelfProductFirstOrderToSquareZero_first (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (b : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductFirstOrderToSquareZero hV hle hVS h
        (smallSelfProductFirstOrderPullback h V (firstCoprojectionSection pr₀ pr₁ V b)) =
      smallSelfProductGraphRingHom h V (firstCoprojectionSection pr₀ pr₁ V b) :=
  smallSelfProductFirstOrderToSquareZero_pullback_eq_graph hV hle hVS h _ _
    (smallSelfProductFirstOrderPullback_firstCoprojection h V) b
    ((firstOrderThickeningP₀_app_apply B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      (op V) b).trans (smallSelfProductDiagonalSection_firstCoprojectionSection h V b).symm)
    ((congrArg (smallSelfProductConormalSheafComparison hV hle hVS h)
      (firstOrderThickeningP₀_app_snd B.obj.thickening.target S.S.scheme B.obj.toBase.hom
        (op V) b)).trans
      ((map_zero (smallSelfProductConormalSheafComparison hV hle hVS h)).trans
        (smallSelfProductClassOf_first h V b).symm))

include hV hle hVS in
/-- **On a section pulled back along the second coprojection the map to the square-zero extension
agrees with the graph of the class map.**  The pullback of `p₁^♯ b` to `T'` is `(b, d b)`, and the
comparison carries `d b` to the class of `p₁^♯ b - p₀^♯ b`, which is the graph's second
coordinate. -/
theorem smallSelfProductFirstOrderToSquareZero_second (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (b : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductFirstOrderToSquareZero hV hle hVS h
        (smallSelfProductFirstOrderPullback h V (secondCoprojectionSection pr₀ pr₁ V b)) =
      smallSelfProductGraphRingHom h V (secondCoprojectionSection pr₀ pr₁ V b) :=
  smallSelfProductFirstOrderToSquareZero_pullback_eq_graph hV hle hVS h _ _
    (smallSelfProductFirstOrderPullback_secondCoprojection h V) b
    ((firstOrderThickeningP₁_app_fst B.obj.thickening.target S.S.scheme B.obj.toBase.hom
      (op V) b).trans (smallSelfProductDiagonalSection_secondCoprojectionSection h V b).symm)
    ((congrArg (smallSelfProductConormalSheafComparison hV hle hVS h)
      (firstOrderThickeningP₁_app_snd B.obj.thickening.target S.S.scheme B.obj.toBase.hom
        (op V) b)).trans
      ((smallSelfProductConormalSheafComparison_sheafApp hV hle hVS h b).trans
        (smallSelfProductClassOf_second h V b).symm))

include hV hle hVS in
/-- **The map to the square-zero extension is a homomorphism of divided power rings.**  Both
divided power structures are the square-zero ones, in which a divided power of positive order has
coordinates `(δ_n a, δ_{n-1} a · m)`, and the comparison is linear. -/
theorem smallSelfProductFirstOrderToSquareZero_isDPMorphism
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    (firstOrderThickeningDividedPowers B.obj.thickening.target S.S.scheme B.obj.toBase.hom
        (op V)).IsDPMorphism
      (smallSelfProductSquareZeroDividedPowers h V)
      (smallSelfProductFirstOrderToSquareZero hV hle hVS h) := by
  have hideal : ∀ x ∈ firstOrderThickeningIdeal B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom (op V),
      smallSelfProductFirstOrderToSquareZero hV hle hVS h x ∈
        smallSelfProductSquareZeroIdeal h V := by
    intro x hx
    refine (smallSelfProductSquareZeroIdeal_mem_iff h V _).mpr ?_
    exact (mem_firstOrderThickeningIdeal_iff B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom (op V) x).mp hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr hideal, ?_⟩
  intro n x hx
  have hfx := hideal x hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ((smallSelfProductSquareZeroDividedPowers h V).dpow_zero hfx).trans (Eq.symm ?_)
    exact (congrArg (smallSelfProductFirstOrderToSquareZero hV hle hVS h)
      ((firstOrderThickeningDividedPowers B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom (op V)).dpow_zero hx)).trans
      (map_one (smallSelfProductFirstOrderToSquareZero hV hle hVS h))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsucc := firstOrderThickeningDividedPowers_dpow_succ B.obj.thickening.target S.S.scheme
    B.obj.toBase.hom (op V) m hx
  have hcoord := smallSelfProductSquareZeroDividedPowers_coordinates h V (m + 1) (by omega)
    (smallSelfProductFirstOrderToSquareZero hV hle hVS h x) hfx
  refine TrivSqZeroExt.ext (hcoord.1.trans (Eq.symm ?_)) (hcoord.2.trans (Eq.symm ?_))
  · exact (congrArg sqZeroExtFst hsucc).trans (sqZeroExtFst_mk _ _)
  · refine ((congrArg (fun z ↦ smallSelfProductConormalSheafComparison hV hle hVS h
      (sqZeroExtSnd z)) hsucc).trans ?_)
    exact (congrArg (smallSelfProductConormalSheafComparison hV hle hVS h)
      (sqZeroExtSnd_mk _ _)).trans
      (map_smul (smallSelfProductConormalSheafComparison hV hle hVS h) _ _)

/-! ### The square-zero quotient as a divided power ring, and the two maps into it -/

/-- **The square-zero extension `Γ(V, 𝒪_T) ⊕ K/K^{[2]}` as a divided power ring.**  It is the
quotient `R/K^{[2]}` of `R = Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})`, by
`smallSelfProductGraphRingHom_surjective` and `smallSelfProductGraphRingHom_ker`, with the
divided powers transported from `δ(1)`. -/
def smallSelfProductSquareZeroRing (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : B.obj.thickening.target.scheme.Opens) : DividedPowerRing.{u} where
  carrier := TrivSqZeroExt Γ(B.obj.thickening.target.scheme, W) (smallSelfProductConormal h W)
  ideal := smallSelfProductSquareZeroIdeal h W
  dividedPowers := smallSelfProductSquareZeroDividedPowers h W

/-- **The graph of the class map as a morphism of divided power rings** onto the square-zero
extension. -/
def smallSelfProductGraphDPHom (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : B.obj.thickening.target.scheme.Opens) :
    D.obj.thickening.target.dividedPowers.toDividedPowerRing
        (op (smallSelfProductOpen pr₀ pr₁ W)) ⟶ smallSelfProductSquareZeroRing h W where
  toRingHom := smallSelfProductGraphRingHom h W
  __ := smallSelfProductGraphRingHom_isDPMorphism h W

include hV hle hVS in
/-- **`q^♯` followed by the map of the first-order thickening into the square-zero extension**, as
a morphism of divided power rings. -/
def smallSelfProductFirstOrderDPHom (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    D.obj.thickening.target.dividedPowers.toDividedPowerRing
        (op (smallSelfProductOpen pr₀ pr₁ V)) ⟶ smallSelfProductSquareZeroRing h V where
  toRingHom := (smallSelfProductFirstOrderToSquareZero hV hle hVS h).comp
    (smallSelfProductFirstOrderPullback h V).hom
  __ := DividedPowers.IsDPMorphism.comp _
    (smallSelfProductFirstOrderToSquareZero_isDPMorphism hV hle hVS h)
    (smallSelfProductFirstOrderPullback_isDPMorphism h V)

/-- **The kernel of the graph of the class map is killed by the immersion of the thickening.**
It is `K^{[2]}`, which lies in `K` and hence in the divided power ideal `J_{T(1)}`. -/
theorem smallSelfProductGraphRingHom_ker_le_immersion (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : B.obj.thickening.target.scheme.Opens) :
    RingHom.ker (smallSelfProductGraphRingHom h W) ≤
      RingHom.ker (D.obj.thickening.immersion.app (smallSelfProductOpen pr₀ pr₁ W)).hom := by
  rw [smallSelfProductGraphRingHom_ker h W]
  intro y hy
  refine RingHom.mem_ker.mpr ?_
  exact SchemeThickening.immersion_app_eq_zero_of_mem D.obj.thickening _ y
    (smallSelfProductDiagonalIdeal_le h _
      (smallSelfProductDividedSquare_le h (smallSelfProductOpen pr₀ pr₁ W) hy))

/-! ### Consequences of the containment `ker q^♯ ⊆ K^{[2]}` -/

/-- **A factorisation of the graph of the class map through `q^♯` forces
`ker q^♯ ⊆ K^{[2]}`.**  The kernel of the graph is exactly `K^{[2]}`, by
`smallSelfProductGraphRingHom_ker`. -/
theorem smallSelfProductFirstOrderPullback_ker_le_of_factorization
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (W : B.obj.thickening.target.scheme.Opens)
    (ψ : Γ(firstOrderThickeningScheme B.obj.thickening.target S.S.scheme B.obj.toBase.hom,
        firstOrderThickeningOpen' B.obj.thickening.target S.S.scheme B.obj.toBase.hom W) →+*
      TrivSqZeroExt Γ(B.obj.thickening.target.scheme, W) (smallSelfProductConormal h W))
    (hψ : ψ.comp (smallSelfProductFirstOrderPullback h W).hom =
      smallSelfProductGraphRingHom h W) :
    RingHom.ker (smallSelfProductFirstOrderPullback h W).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ W) := by
  rw [← smallSelfProductGraphRingHom_ker h W, ← hψ]
  intro x hx
  refine RingHom.mem_ker.mpr ?_
  show ψ (smallSelfProductFirstOrderPullback h W x) = 0
  rw [RingHom.mem_ker.mp hx, map_zero]

/-- **If `q^♯` kills only the divided square then the inverse comparison is injective.**  A class
in `K/K^{[2]}` killed by the inverse comparison has a representative whose pullback to `T'` has
both coordinates zero, so the representative lies in the kernel of `q^♯` and hence in
`K^{[2]}`. -/
theorem injective_smallSelfProductConormalInverse_of_ker_le
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (W : B.obj.thickening.target.scheme.Opens)
    (hker : RingHom.ker (smallSelfProductFirstOrderPullback h W).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ W)) :
    Function.Injective (smallSelfProductConormalInverse h W) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := Submodule.mkQ_surjective (smallSelfProductDiagonalRelations h W) x
  have hsnd : sqZeroExtSnd (smallSelfProductFirstOrderPullback h W k.val) = 0 :=
    smallSelfProductConormalInverse_class h W k ▸ hx
  have hfst : sqZeroExtFst (smallSelfProductFirstOrderPullback h W k.val) = 0 :=
    sqZeroExtFst_pullback_eq_zero h W k.property
  have hzero : smallSelfProductFirstOrderPullback h W k.val = 0 :=
    firstOrderThickening_eq_zero_of_coordinates W hfst hsnd
  refine (smallSelfProductClass_eq_zero h W k).mpr (hker (RingHom.mem_ker.mpr hzero))

/-- **If `q^♯` kills only the divided square then the comparison map of [Stacks, Tag 07J1] is
bijective.**  Injectivity is `injective_smallSelfProductConormalComparison` together with the
bijectivity of the comparison of the presheaf of divided power differentials with the sheaf it
generates; for surjectivity, the image of a class under the inverse comparison comes from the
presheaf, and the inverse comparison is injective. -/
theorem bijective_smallSelfProductConormalComparison_of_ker_le
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (hV : IsAffineOpen V)
    (hle : V ≤ B.obj.toBase.hom ⁻¹ᵁ VS) (hVS : IsAffineOpen VS)
    (hker : RingHom.ker (smallSelfProductFirstOrderPullback h V).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)) :
    Function.Bijective (smallSelfProductConormalComparison h V).hom := by
  have hbij := bijective_dpDifferentialsToSheaf_app B.obj.thickening.target S.S.scheme
    B.obj.toBase.hom hV hle hVS
  have hinv := injective_smallSelfProductConormalInverse_of_ker_le h V hker
  refine ⟨injective_smallSelfProductConormalComparison h V hbij.1, fun m ↦ ?_⟩
  obtain ⟨x, hx⟩ := hbij.2 (smallSelfProductConormalInverse h V m)
  refine ⟨x, hinv ?_⟩
  exact (smallSelfProductConormalInverse_comp_comparison h V x).trans hx

/-- **If `q^♯` kills only the divided square then the comparison map of [Stacks, Tag 07J1] is an
isomorphism of modules**, being bijective. -/
theorem isIso_smallSelfProductConormalComparison_of_ker_le
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (hV : IsAffineOpen V)
    (hle : V ≤ B.obj.toBase.hom ⁻¹ᵁ VS) (hVS : IsAffineOpen VS)
    (hker : RingHom.ker (smallSelfProductFirstOrderPullback h V).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)) :
    IsIso (smallSelfProductConormalComparison h V) :=
  (ConcreteCategory.isIso_iff_bijective (smallSelfProductConormalComparison h V)).mpr
    (bijective_smallSelfProductConormalComparison_of_ker_le h hV hle hVS hker)

/-- **If `q^♯` kills only the divided square then the comparison map out of `(Ω_{X/S})_T` is
bijective.**  It is the comparison out of the presheaf of divided power differentials composed
with the inverse of the identification of [Stacks, Tag 07IZ], which is an isomorphism. -/
theorem bijective_restrictedCrysDifferentialsConormalComparison_of_ker_le
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (hV : IsAffineOpen V)
    (hle : V ≤ B.obj.toBase.hom ⁻¹ᵁ VS) (hVS : IsAffineOpen VS)
    (hker : RingHom.ker (smallSelfProductFirstOrderPullback h V).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)) :
    Function.Bijective (restrictedCrysDifferentialsConormalComparison h V).hom := by
  have hcmp := bijective_smallSelfProductConormalComparison_of_ker_le h hV hle hVS hker
  have hiso : Function.Bijective (comparisonIsoApp B.obj V).inv.hom :=
    ConcreteCategory.bijective_of_isIso (comparisonIsoApp B.obj V).inv
  exact hcmp.comp hiso


/-! ### The uniqueness half of the product's universal property -/

include hV hle hVS in
/-- **`q^♯` kills only the divided square `K^{[2]}`.**  The graph of the class map and the map
`q^♯` followed by the map of the first-order thickening into the square-zero extension are two
divided power homomorphisms out of `Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})` with the same target; they agree
after both coprojections, by `smallSelfProductFirstOrderToSquareZero_first` and `_second`, and
the first is surjective with kernel inside the ideal of the immersion and presenting the divided
power ideal of the target.  The uniqueness half of the product's universal property — tested
against the object of `Cris(X/S)` that the surjection presents — therefore identifies them, so
the graph factors through `q^♯` and its kernel `K^{[2]}` contains that of `q^♯`. -/
theorem smallSelfProductFirstOrderPullback_ker_le (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    RingHom.ker (smallSelfProductFirstOrderPullback h V).hom ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) := by
  have he := crystallineProduct_affine_ext h ⟨V, hV⟩
    ⟨smallSelfProductOpen pr₀ pr₁ V, isAffineOpen_smallSelfProductOpen h hV⟩
    (smallSelfProductOpen_le_fst pr₀ pr₁ V) (smallSelfProductOpen_le_snd pr₀ pr₁ V)
    (smallSelfProductSquareZeroRing h V) (smallSelfProductGraphDPHom h V)
    (smallSelfProductFirstOrderDPHom hV hle hVS h)
    (smallSelfProductGraphRingHom_surjective h V)
    (smallSelfProductGraphRingHom_ker_le_immersion h V) rfl
    (RingHom.ext fun b ↦ (smallSelfProductFirstOrderToSquareZero_first hV hle hVS h b).symm)
    (RingHom.ext fun b ↦ (smallSelfProductFirstOrderToSquareZero_second hV hle hVS h b).symm)
  exact smallSelfProductFirstOrderPullback_ker_le_of_factorization h V
    (smallSelfProductFirstOrderToSquareZero hV hle hVS h) he.symm

include hV hle hVS in
/-- **The inverse comparison `K/K^{[2]} → Ω_{T/S,δ}(V)` is injective.** -/
theorem injective_smallSelfProductConormalInverse (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    Function.Injective (smallSelfProductConormalInverse h V) :=
  injective_smallSelfProductConormalInverse_of_ker_le h V
    (smallSelfProductFirstOrderPullback_ker_le hV hle hVS h)

include hV hle hVS in
/-- **The affine-local step of the second assertion of [Stacks, Tag 07J1].**  Over an affine
open `V` of `T` lying over an affine open of `S` the comparison map
`Ω_{T/S,δ}(V) → K/K^{[2]}` of `smallSelfProductConormalComparison` — which is
`(Ω_{X/S})_T(V) → K/K^{[2]}` by [Stacks, Tag 07IZ] — is bijective.  These are the hypotheses the
source's proof makes, which works affine locally on `T`; they are not hypotheses of the source's
statement, so the tag is carried not here but by
`exists_isIso_smallSelfProductConormalComparison` below, which discharges them against
`Crystalline.exists_isAffineOpen_over_isAffineOpen`. -/
theorem bijective_smallSelfProductConormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    Function.Bijective (smallSelfProductConormalComparison h V).hom :=
  bijective_smallSelfProductConormalComparison_of_ker_le h hV hle hVS
    (smallSelfProductFirstOrderPullback_ker_le hV hle hVS h)

include hV hle hVS in
/-- **The affine-local step of the second assertion of [Stacks, Tag 07J1], as an isomorphism of
modules.**  The tag is carried by `exists_isIso_smallSelfProductConormalComparison` below. -/
theorem isIso_smallSelfProductConormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsIso (smallSelfProductConormalComparison h V) :=
  isIso_smallSelfProductConormalComparison_of_ker_le h hV hle hVS
    (smallSelfProductFirstOrderPullback_ker_le hV hle hVS h)

include hV hle hVS in
/-- **The affine-local step of the second assertion of [Stacks, Tag 07J1], read out of
`(Ω_{X/S})_T`.**  The comparison map out of the restriction of the crystalline differentials to
the opens of `T` is bijective over an affine open lying over an affine open of `S`.  The tag is
carried by `exists_isIso_restrictedCrysDifferentialsConormalComparison` below. -/
theorem bijective_restrictedCrysDifferentialsConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    Function.Bijective (restrictedCrysDifferentialsConormalComparison h V).hom :=
  bijective_restrictedCrysDifferentialsConormalComparison_of_ker_le h hV hle hVS
    (smallSelfProductFirstOrderPullback_ker_le hV hle hVS h)

include hV hle hVS in
/-- **The affine-local step of the second assertion of [Stacks, Tag 07J1], as an isomorphism out
of `(Ω_{X/S})_T`.**  The tag is carried by
`exists_isIso_restrictedCrysDifferentialsConormalComparison` below. -/
theorem isIso_restrictedCrysDifferentialsConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsIso (restrictedCrysDifferentialsConormalComparison h V) :=
  (ConcreteCategory.isIso_iff_bijective
    (restrictedCrysDifferentialsConormalComparison h V)).mpr
    (bijective_restrictedCrysDifferentialsConormalComparison hV hle hVS h)

/-! ### The second assertion at the source's own hypotheses -/

/-- **Stacks Project, Tag 07J1, the second assertion, with no hypothesis on the open.**  Every
point of every open `W` of `T` has an open neighbourhood `V ≤ W` on which the comparison map
`Ω_{T/S,δ}(V) → K/K^{[2]}` is an isomorphism.  The affine opens of `T` lying over an affine open
of `S` are such neighbourhoods, by `isIso_smallSelfProductConormalComparison`, and they form a
basis of the topology of `T`, by `Crystalline.exists_isAffineOpen_over_isAffineOpen`. -/
@[stacks 07J1 "second assertion: the comparison Ω_{T/S,δ} → K/K^{[2]} is an isomorphism on a \
neighbourhood of every point of every open of T, with no hypothesis on the open"]
theorem exists_isIso_smallSelfProductConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) {W : B.obj.thickening.target.scheme.Opens}
    {x : B.obj.thickening.target.scheme} (hx : x ∈ W) :
    ∃ V : B.obj.thickening.target.scheme.Opens, x ∈ V ∧ V ≤ W ∧
      IsIso (smallSelfProductConormalComparison h V) := by
  obtain ⟨V, VS, hVaff, hVSaff, hxV, hVW, hVpre⟩ :=
    exists_isAffineOpen_over_isAffineOpen B.obj.toBase.hom W x hx
  exact ⟨V, hxV, hVW, isIso_smallSelfProductConormalComparison hVaff hVpre hVSaff h⟩

/-- **Stacks Project, Tag 07J1, the second assertion, with no hypothesis on the open.**  Every
point of every open `W` of `T` has an open neighbourhood `V ≤ W` on which the comparison map
`(Ω_{X/S})_T(V) → K/K^{[2]}` is an isomorphism.  This is the second assertion read out of
`(Ω_{X/S})_T` itself, through [Stacks, Tag 07IZ], and it carries no hypothesis the source does
not: the affineness of the open of `T` and of an open of `S` below it, under which the source's
own proof works, is discharged against
`Crystalline.exists_isAffineOpen_over_isAffineOpen`. -/
@[stacks 07J1 "second assertion: (Ω_{X/S})_T = K/K^{[2]} on a neighbourhood of every point of \
every open of T, with no hypothesis on the open"]
theorem exists_isIso_restrictedCrysDifferentialsConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) {W : B.obj.thickening.target.scheme.Opens}
    {x : B.obj.thickening.target.scheme} (hx : x ∈ W) :
    ∃ V : B.obj.thickening.target.scheme.Opens, x ∈ V ∧ V ≤ W ∧
      IsIso (restrictedCrysDifferentialsConormalComparison h V) := by
  obtain ⟨V, VS, hVaff, hVSaff, hxV, hVW, hVpre⟩ :=
    exists_isAffineOpen_over_isAffineOpen B.obj.toBase.hom W x hx
  exact ⟨V, hxV, hVW,
    isIso_restrictedCrysDifferentialsConormalComparison hVaff hVpre hVSaff h⟩

/-- **Stacks Project, Tag 07J1, the second assertion, as a basis of the topology of `T`.**  The
opens of `T` on which the comparison `(Ω_{X/S})_T → K/K^{[2]}` is an isomorphism form a basis of
the topology of `T`.  The conormal module is built open by open, so there is no morphism of
sheaves of `𝒪_T`-modules to call an isomorphism; a basis of opens on which the comparison is one
is what the source's equality of sheaves amounts to for that presentation. -/
@[stacks 07J1 "second assertion: the opens of T on which (Ω_{X/S})_T = K/K^{[2]} form a basis \
of the topology of T"]
theorem isBasis_isIso_restrictedCrysDifferentialsConormalComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    TopologicalSpace.Opens.IsBasis
      {W : B.obj.thickening.target.scheme.Opens |
        IsIso (restrictedCrysDifferentialsConormalComparison h W)} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨V, hxV, hVW, hViso⟩ :=
    exists_isIso_restrictedCrysDifferentialsConormalComparison h hx
  exact ⟨V, hViso, hxV, hVW⟩

end GlobalCrystallineSituation

end Crystalline

end
