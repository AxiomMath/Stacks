module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.FibreStatements
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.AffineLineFibreStalk
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.MilnorExactSequence

/-!
# The fibres of `Spec A[T] ⟶ Spec A`: boundary lifting and unit descent

Let `(S, δ)` be the base situation of chapter 42 and `Spec A ⟶ S` locally of finite type. The
injectivity of flat pullback along an affine-space bundle (Stacks 0GUB) is proved by a dévissage
of a Milnor K₁-chain into its pieces over the points of the base, and consumes two properties of
each fibre, `Stacks.Chow.FibreBoundaryLift` and `Stacks.Chow.FibreUnitDescent`. This file proves
both for the affine line `f : Spec A[T] ⟶ Spec A`, where the fibre over `y` is the affine line over
`κ(y)`; they are the computation `CH^M_t(𝔸¹_{κ(y)}, 1) = 0` for `t < 1` and
`CH^M_1(𝔸¹_{κ(y)}, 1) = κ(y)^*` of the higher Chow groups of Stacks 0GUA.

The points of the fibre over `y` are its generic point `ζ`, of relative dimension `δ(y) + 1`, and
its closed points, of relative dimension `δ(y)`, which are the closed points of the affine line
over `κ(y)`. At a closed point `w` the local ring of `closure {ζ}` is the local ring of the affine
line, a discrete valuation ring
(`Stacks.Chow.isDiscreteValuationRing_pointClosureStalk_specPolynomial`).

* **Boundary lifting.** Unless `δ(y) = k`, a K₁-chain of relative dimension `k + 1` on the fibre is
  either zero (there are no points of that dimension) or, when `δ(y) = k + 1`, a finite family of
  classes at closed points. By Milnor's exact sequence for `κ(y)(T)` such a family is the family
  of tame symbols of one class of `K₂ᴹ(κ(y)(T)) = K₂ᴹ(κ(ζ))`, and the tame symbol at a closed
  point is the local component at `w` of the first differential of Stacks 0GU9
  (`Stacks.Chow.exists_addEquiv_pointClosureMilnorBoundary`).
* **Unit descent.** When `δ(y) = k`, a K₁-chain of relative dimension `k + 1` on the fibre is a
  unit `u` of `κ(ζ) = κ(y)(T)`, and the vanishing of its divisor on the fibre says that `u` has
  order zero at every closed point of the affine line; so `u` is a constant.

## Main results

* `Stacks.Chow.isDiscreteValuationRing_pointClosureStalk_specPolynomial` — the local rings of
  the closure of a point of a fibre at the other points of that fibre are discrete valuation
  rings.
* `Stacks.Chow.fibreBoundaryLift_specPolynomial` — boundary lifting for `Spec A[T] ⟶ Spec A`.
* `Stacks.Chow.fibreUnitDescent_specPolynomial` — unit descent for `Spec A[T] ⟶ Spec A`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (A : CommRingCat.{u}) (sV : Spec A ⟶ C.S)
  [LocallyOfFiniteType sV]

attribute [local instance] isIntegral_integralComponentAt in
/-- **The local ring of the closure of a point of a fibre of `Spec A[T] ⟶ Spec A` at a
different point of the same fibre is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_pointClosureStalk_specPolynomial
    {ζ w : Spec (CommRingCat.of (Polynomial A))} (hw : ζ ⤳ w)
    (hfib : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base ζ =
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base w)
    (hne : ζ ≠ w) :
    IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
      (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))) := by
  have hζ : IsGenericFibrePoint ζ :=
    congrArg PrimeSpectrum.asIdeal (eq_fibreGenericPoint_of_specializes hw hfib hne)
  exact isDiscreteValuationRing_closureStalk _ hζ hfib.symm (Ne.symm hne)

/-- `Spec A[T] ⟶ Spec A` is an affine-space bundle of rank one. -/
theorem isAffineSpaceBundle_specMap_C :
    IsAffineSpaceBundle (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) 1 :=
  isAffineSpaceBundle_of_isPullback (g := specPolynomialToAffineLine A) (h := 𝟙 (Spec A))
    (IsPullback.of_horiz_isIso ⟨by rw [specPolynomialToAffineLine_over, Category.comp_id]⟩)
    (isAffineSpaceBundle_affineSpaceOver (Spec A) 1)

/-- Along `Spec A[T] ⟶ Spec A` the relative dimension grows by at most one. -/
theorem relativeDimension_specMap_C_comp_le (x : Spec (CommRingCat.of (Polynomial A))) :
    relativeDimension C.dimensionFunction
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) x ≤
      relativeDimension C.dimensionFunction sV
        ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base x) + 1 := by
  exact_mod_cast relativeDimension_le_add_of_isAffineSpaceBundle C _ sV _ rfl
    (isAffineSpaceBundle_specMap_C A) x

/-- Along `Spec A[T] ⟶ Spec A` the relative dimension does not drop. -/
theorem le_relativeDimension_specMap_C_comp (x : Spec (CommRingCat.of (Polynomial A))) :
    relativeDimension C.dimensionFunction sV
        ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base x) ≤
      relativeDimension C.dimensionFunction
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) x := by
  rw [relativeDimension_comp_eq_add_trdeg C.dimensionFunction sV]
  omega

/-- The generic point of the fibre over `y` has relative dimension one more than `y`. -/
theorem relativeDimension_fibreGenericPoint (y : Spec A) :
    relativeDimension C.dimensionFunction
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
        (fibreGenericPoint y) =
      relativeDimension C.dimensionFunction sV y + 1 := by
  obtain ⟨ξ, hξ, hdim, hspec⟩ := exists_relativeDimension_eq_add_of_isAffineSpaceBundle C _ sV _
    rfl (isAffineSpaceBundle_specMap_C A) y
  have heq : ξ = fibreGenericPoint y :=
    (hspec _ (specMap_C_base_fibreGenericPoint y)).antisymm
      (fibreGenericPoint_specializes hξ) |>.eq
  rw [← heq, hdim]
  push_cast
  rfl

/-- The other points of the fibre over `y` have the relative dimension of `y`. -/
theorem relativeDimension_of_ne_fibreGenericPoint {y : Spec A}
    {w : Spec (CommRingCat.of (Polynomial A))}
    (hw : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base w = y)
    (hne : w ≠ fibreGenericPoint y) :
    relativeDimension C.dimensionFunction
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) w =
      relativeDimension C.dimensionFunction sV y := by
  have hlt := relativeDimension_lt_of_specializes C
    (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
    (fibreGenericPoint_specializes hw) (Ne.symm hne)
  have hle := le_relativeDimension_specMap_C_comp C A sV w
  rw [relativeDimension_fibreGenericPoint] at hlt
  rw [hw] at hle
  omega

attribute [local instance] isIntegral_integralComponentAt
  isDiscreteValuationRing_localizationAtPrime_polynomial

/-- A point of relative dimension `δ(y) + 1` of the fibre over `y` is its generic point. -/
theorem eq_fibreGenericPoint_of_relativeDimension {y : Spec A}
    {x : Spec (CommRingCat.of (Polynomial A))}
    (hx : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base x = y)
    (hdim : relativeDimension C.dimensionFunction
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) x =
      relativeDimension C.dimensionFunction sV y + 1) :
    x = fibreGenericPoint y := by
  by_contra hne
  have := relativeDimension_of_ne_fibreGenericPoint C A sV hx hne
  omega

/-- The local ring of the closure of the generic point of a fibre at another point of the fibre has
Krull dimension one. -/
private theorem ringKrullDim_pointClosureStalk_eq_one {ζ w : Spec (CommRingCat.of (Polynomial A))}
    (hζ : IsGenericFibrePoint ζ)
    (h : w ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A)))))
    (hfib : specPolynomialBase w = specPolynomialBase ζ) (hne : w ≠ ζ) :
    ringKrullDim ((integralComponentAt ζ).subscheme.presheaf.stalk (pointClosurePoint ζ h)) = 1 :=
  have := isDiscreteValuationRing_closureStalk h hζ hfib hne
  IsDiscreteValuationRing.ringKrullDim_eq_one _

/-- A chain fixed by restriction to the fibre over `y` is supported on that fibre. -/
theorem base_eq_of_fibreRestrict_eq_self {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {f : X ⟶ Y} {y : Y} {m : ℤ} {n : ℕ} {a : MilnorChainGroup C sX m n}
    (ha : fibreRestrict C sX f y m n a = a) {x : pointsOfDimension C sX m} (hx : a.1 x ≠ 0) :
    f.base x.1 = y := by
  by_contra hxy
  exact hx (by rw [← ha]; exact milnorChainRestrict_apply_of_notMem a hxy)

/-- At a closed point of the fibre over `y`, with `δ(y) = k`, the unit of a K₁-chain supported at
the generic point `ξ` of the fibre, whose divisor has no component on the fibre, has order zero. -/
theorem ordFrac_eq_one_of_fibreRestrict_divisor_eq_zero {k : ℤ} {y : Spec A}
    (hδ' : relativeDimension C.dimensionFunction sV y = k)
    {a : PointwiseKOneGroup C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k}
    (hdiv : fibreRestrict C (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) y k 0
        (pointwiseDivisorDifferential C
          (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k a) = 0)
    {ξ : pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 1)}
    (hξ : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base ξ.1 = y)
    (hξgen : ξ.1 = fibreGenericPoint y) (hζ : IsGenericFibrePoint ξ.1)
    (hsupp : ∀ x, a.1 x ≠ 0 → x = ξ)
    (u0 : ((Spec (CommRingCat.of (Polynomial A))).residueField ξ.1)ˣ)
    (hu0 : u0 = Additive.toMul (milnorKTheoryOneAddEquiv _ (a.1 ξ)))
    (P : Ideal (Polynomial ((Spec A).residueField (specPolynomialBase ξ.1)))) [P.IsMaximal] :
    Ring.ordFrac (Localization.AtPrime P) (fibreGenericResidueFieldEquiv hζ u0) = 1 := by
  subst hu0
  obtain ⟨w, hw, rfl⟩ := exists_fibrePrime_eq P
  have hne : w ≠ ξ.1 := by
    rintro rfl
    exact ne_bot_of_isMaximal_polynomial _ (fibrePrime_self hζ)
  have hwy : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base w = y :=
    hw.trans hξ
  have hmem : w ∈ closure ({ξ.1} : Set _) :=
    specializes_iff_mem_closure.mp (hζ.specializes hw)
  have hwdim : w ∈ pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k := by
    rw [mem_pointsOfDimension, relativeDimension_of_ne_fibreGenericPoint C A sV hwy
      (by rwa [← hξgen]), hδ']
  let _ : IsLocallyNoetherian (integralComponentAt ξ.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt ξ.1).subschemeι ≫
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV))
  have hzero : (pointwiseDivisorDifferential C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k a).1
        ⟨w, hwdim⟩ = 0 := by
    have := congrArg (fun c ↦ c.1 ⟨w, hwdim⟩) hdiv
    simp only at this
    rwa [milnorChainRestrict_apply_of_mem _ hwy] at this
  have hsum := pointwiseDivisorDifferential_apply_eq_finsum C
    (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k a ⟨w, hwdim⟩
  rw [hzero, map_zero, finsum_eq_single _ ξ (fun x hx ↦ by
      by_cases h0 : a.1 x = 0
      · rw [h0, map_zero]
      · exact absurd (hsupp x h0) hx), pointClosureOrdHom_apply,
    pointClosureOrd_eq_ord C _ ξ.1 _ hmem] at hsum
  exact ordFrac_fibreGenericResidueFieldEquiv_eq_one hmem hζ hw hne _ hsum.symm

/-- **Unit descent for `Spec A[T] ⟶ Spec A`**, Stacks 0GUA for the affine line in the top
degree: a degree-one Milnor K-chain on the fibre over `y`, at the generic point of the fibre,
whose divisor has no component on the fibre, has a constant class there. -/
theorem fibreUnitDescent_specPolynomial (k : ℤ) (y : Spec A) :
    FibreUnitDescent C (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
      sV (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) 1 k y := by
  intro hδ a ha hdiv ξ hξ
  have hδ' : relativeDimension C.dimensionFunction sV y = k := by
    rw [hδ]
    push_cast
    ring
  have hξgen : ξ.1 = fibreGenericPoint y := eq_fibreGenericPoint_of_relativeDimension C A sV hξ
    (by rw [(mem_pointsOfDimension C _).mp ξ.2, hδ'])
  have hζ : IsGenericFibrePoint ξ.1 := hξgen ▸ isGenericFibrePoint_fibreGenericPoint y
  have hsupp : ∀ x : pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 1),
      a.1 x ≠ 0 → x = ξ := by
    intro x hx
    have hxy := base_eq_of_fibreRestrict_eq_self C ha hx
    exact Subtype.ext ((eq_fibreGenericPoint_of_relativeDimension C A sV hxy
      (by rw [(mem_pointsOfDimension C _).mp x.2, hδ'])).trans hξgen.symm)
  set u0 : ((Spec (CommRingCat.of (Polynomial A))).residueField ξ.1)ˣ :=
    Additive.toMul (milnorKTheoryOneAddEquiv _ (a.1 ξ)) with hu0
  have hP := ordFrac_eq_one_of_fibreRestrict_divisor_eq_zero C A sV hδ' hdiv hξ hξgen hζ hsupp
    u0 hu0
  obtain ⟨c, hc⟩ := exists_eq_C_of_ordFrac_eq_one
    ((fibreGenericResidueFieldEquiv hζ).map_ne_zero_iff.mpr u0.ne_zero) hP
  have hu0c : (u0 : (Spec (CommRingCat.of (Polynomial A))).residueField ξ.1) =
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).residueFieldMap ξ.1 c :=
    (fibreGenericResidueFieldEquiv hζ).injective (by
      rw [fibreGenericResidueFieldEquiv_residueFieldMap, ← hc])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu0c
    exact u0.ne_zero hu0c
  refine ⟨(milnorKTheoryOneAddEquiv _).symm (Additive.ofMul (Units.mk0 c hc0)), ?_⟩
  apply (milnorKTheoryOneAddEquiv _).injective
  rw [milnorKTheoryOneAddEquiv_milnorKTransport, AddEquiv.apply_symm_apply, milnorKUnitsMap_ofMul,
    ← ofMul_toMul (milnorKTheoryOneAddEquiv _ (a.1 ξ)), ← hu0]
  congr 1
  ext
  rw [hu0c]
  rfl

/-! ### The tame-symbol boundary at a closed point of the fibre -/

section Boundary

attribute [local instance] Ideal.Quotient.field

/-- **The residue of Milnor's exact sequence at a closed point is the tame symbol of the local
ring of the affine line there**, read in `k[T] ⧸ ψ`. -/
theorem milnorKTotalResidue_one_apply {k : Type u} [Field k] (θ : MilnorKTheory (RatFunc k) 2)
    (ψ : MonicIrreduciblePoint k) :
    milnorKTotalResidue k 1 θ ψ =
      milnorKTransport ((quotientRingEquivResidueField
          (Ideal.span {MonicIrreducibleOfDegree.poly ψ.2})).symm : _ →+* _) 1
        (milnorKTwoTameSymbol (A := Localization.AtPrime
            (Ideal.span {MonicIrreducibleOfDegree.poly ψ.2})) (K := RatFunc k)
          (IsDiscreteValuationRing.ringKrullDim_eq_one _) θ) := by
  refine Subtype.ext ?_
  rw [coe_milnorKTotalResidue_apply, monicIrreducibleResidue_apply, milnorKTransport_coe,
    ← dvrMilnorTameSymbol_one_eq_milnorKTwoTameSymbol
      (irreducible_algebraMap_self (p := MonicIrreducibleOfDegree.poly ψ.2))]
  rfl

/-- **Prescribing finitely many tame symbols on the affine line.** For an injective family of
closed points of the affine line over a field and finitely many classes in the degree-one Milnor
K-groups of their residue fields, some class of `K₂ᴹ(k(T))` has exactly those tame symbols. This
is the surjectivity in Milnor's exact sequence. -/
theorem exists_milnorKTwoTameSymbol_eq {k : Type u} [Field k] {ι : Type*}
    (ψ : ι → MonicIrreduciblePoint k) (hψ : Function.Injective ψ) (s : Finset ι)
    (β : ∀ i, MilnorKTheory (IsLocalRing.ResidueField
      (Localization.AtPrime (Ideal.span {MonicIrreducibleOfDegree.poly (ψ i).2}))) 1)
    (hβ : ∀ i ∉ s, β i = 0) :
    ∃ θ : MilnorKTheory (RatFunc k) 2, ∀ i, milnorKTwoTameSymbol
        (A := Localization.AtPrime (Ideal.span {MonicIrreducibleOfDegree.poly (ψ i).2}))
        (K := RatFunc k) (IsDiscreteValuationRing.ringKrullDim_eq_one _) θ = β i := by
  classical
  let γ : ∀ i, MilnorKTheory (Polynomial k ⧸ Ideal.span {MonicIrreducibleOfDegree.poly (ψ i).2})
      1 := fun i ↦ milnorKTransport ((quotientRingEquivResidueField
        (Ideal.span {MonicIrreducibleOfDegree.poly (ψ i).2})).symm : _ →+* _) 1 (β i)
  obtain ⟨θ, hθ⟩ := milnorKTotalResidue_surjective (k := k) 1
    (∑ i ∈ s, DirectSum.of (fun χ : MonicIrreduciblePoint k ↦
      MilnorKTheory (Polynomial k ⧸ Ideal.span {MonicIrreducibleOfDegree.poly χ.2}) 1)
      (ψ i) (γ i))
  refine ⟨θ, fun i ↦ ?_⟩
  have h1 := congrArg (fun x ↦ x (ψ i)) hθ
  simp only at h1
  rw [milnorKTotalResidue_one_apply, DFinsupp.finset_sum_apply] at h1
  have h2 : ∑ j ∈ s, (DirectSum.of (fun χ : MonicIrreduciblePoint k ↦
      MilnorKTheory (Polynomial k ⧸ Ideal.span {MonicIrreducibleOfDegree.poly χ.2}) 1)
      (ψ j) (γ j)) (ψ i) = γ i := by
    by_cases hi : i ∈ s
    · rw [Finset.sum_eq_single i (fun j _ hji ↦ DirectSum.of_eq_of_ne _ _ _ (hψ.ne hji).symm)
        (fun h ↦ absurd hi h), DirectSum.of_eq_same]
    · rw [Finset.sum_eq_zero (fun j hj ↦ DirectSum.of_eq_of_ne _ _ _
        (hψ.ne fun h : j = i ↦ hi (h ▸ hj)).symm)]
      show 0 = milnorKTransport _ 1 (β i)
      rw [hβ i hi, map_zero]
  rw [h2] at h1
  exact (milnorKTransport_bijective _ 1).injective h1

/-- **The local component of the first differential at a closed point of the fibre is the tame
symbol of the affine line there.** Let `ζ` be the generic point of a fibre of `Spec A[T] ⟶ Spec A`
and `w ≠ ζ` a point of that fibre, attached to the closed point `P` of the affine line over
`κ(f ζ)`. Up to an isomorphism of the targets, the local component `∂_{𝒪_{closure ζ, w}}` of
Stacks 0GU9, precomposed with the identification `κ(ζ) ≅ κ(f ζ)(T)`, is the tame symbol of the
local ring of the affine line at `P`. -/
theorem exists_addEquiv_pointClosureMilnorBoundary
    (p : Spec (CommRingCat.of (Polynomial A)) ⟶ C.S) [LocallyOfFiniteType p]
    {ζ w : Spec (CommRingCat.of (Polynomial A))} (hζ : IsGenericFibrePoint ζ)
    (h : w ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A)))))
    (P : Ideal (Polynomial ((Spec A).residueField (specPolynomialBase ζ)))) [P.IsMaximal]
    (hP : P.comap (Polynomial.mapRingHom (specEval (specPolynomialBase ζ))) = w.asIdeal)
    (hdim : ringKrullDim ((integralComponentAt ζ).subscheme.presheaf.stalk
      (pointClosurePoint ζ h)) = 1) :
    ∃ e : MilnorKTheory ((Spec (CommRingCat.of (Polynomial A))).residueField w) 1 ≃+
        MilnorKTheory (IsLocalRing.ResidueField (Localization.AtPrime P)) 1,
      ∀ θ, e (pointClosureMilnorBoundary C p ζ h hdim
          ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv hζ)).symm θ)) =
        milnorKTwoTameSymbol (A := Localization.AtPrime P)
          (K := RatFunc ((Spec A).residueField (specPolynomialBase ζ)))
          (IsDiscreteValuationRing.ringKrullDim_eq_one _) θ := by
  obtain ⟨ε, hε⟩ := exists_closureStalk_ringEquiv h hζ P hP
  let _ : IsLocallyNoetherian (integralComponentAt ζ).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt ζ).subschemeι ≫ p)
  let _ := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv ζ)
    (pointClosurePoint ζ h)
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv ζ)
    (pointClosurePoint ζ h)
  refine ⟨(milnorKTransportEquiv (pointClosureResidueFieldEquiv ζ h) 1).symm.trans
    (milnorKOneRingEquiv (IsLocalRing.ResidueField.mapEquiv ε)), fun θ ↦ ?_⟩
  have key := milnorKTwoTameSymbol_ringEquiv ε (fibreGenericResidueFieldEquiv hζ)
    (fun a ↦ (hε a).symm) hdim (IsDiscreteValuationRing.ringKrullDim_eq_one _)
    ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv hζ)).symm θ)
  rw [AddEquiv.apply_symm_apply] at key
  rw [AddEquiv.trans_apply, ← key]
  congr 1
  show (milnorKTransportEquiv (pointClosureResidueFieldEquiv ζ h) 1).symm
      (milnorKOneTransport (pointClosureResidueFieldEquiv ζ h)
        (stalkMilnorBoundary (pointClosureFunctionFieldEquiv ζ) (pointClosurePoint ζ h) hdim
          ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv hζ)).symm θ))) = _
  rw [← milnorKTransport_eq_milnorKOneTransport, ← milnorKTransportEquiv_apply,
    AddEquiv.symm_apply_apply]
  rfl

/-- **The closed points of a fibre are closed points of the affine line**, injectively, and at
each of them the local component of the first differential is the tame symbol of the affine
line. -/
theorem exists_monicIrreduciblePoint_fibre
    (p : Spec (CommRingCat.of (Polynomial A)) ⟶ C.S) [LocallyOfFiniteType p]
    {ζ : Spec (CommRingCat.of (Polynomial A))} (hζ : IsGenericFibrePoint ζ) :
    ∃ ψ : {x : Spec (CommRingCat.of (Polynomial A)) //
        specPolynomialBase x = specPolynomialBase ζ ∧ x ≠ ζ} →
        MonicIrreduciblePoint ((Spec A).residueField (specPolynomialBase ζ)),
      Function.Injective ψ ∧
        ∀ (x : {x : Spec (CommRingCat.of (Polynomial A)) //
          specPolynomialBase x = specPolynomialBase ζ ∧ x ≠ ζ})
        (h : x.1 ∈ closure ({ζ} : Set (Spec (CommRingCat.of (Polynomial A)))))
        (hdim : ringKrullDim ((integralComponentAt ζ).subscheme.presheaf.stalk
          (pointClosurePoint ζ h)) = 1),
        ∃ e : MilnorKTheory ((Spec (CommRingCat.of (Polynomial A))).residueField x.1) 1 ≃+
            MilnorKTheory (IsLocalRing.ResidueField (Localization.AtPrime
              (Ideal.span {MonicIrreducibleOfDegree.poly (ψ x).2}))) 1,
          ∀ θ, e (pointClosureMilnorBoundary C p ζ h hdim
              ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv hζ)).symm θ)) =
            milnorKTwoTameSymbol (A := Localization.AtPrime
                (Ideal.span {MonicIrreducibleOfDegree.poly (ψ x).2}))
              (K := RatFunc ((Spec A).residueField (specPolynomialBase ζ)))
              (IsDiscreteValuationRing.ringKrullDim_eq_one _) θ := by
  have hdata : ∀ x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase ζ ∧ x ≠ ζ},
      ∃ q : Polynomial ((Spec A).residueField (specPolynomialBase ζ)),
        q.Monic ∧ Irreducible q ∧ fibrePrime ζ x.1 = Ideal.span {q} := fun x ↦ by
    have := isPrime_fibrePrime x.2.1
    exact exists_monic_irreducible_span_eq inferInstance (fibrePrime_ne_bot hζ x.2.1 x.2.2)
  choose q hqm hqi hqspan using hdata
  refine ⟨fun x ↦ ⟨(q x).natDegree, ⟨q x, hqm x, hqi x, rfl⟩⟩, fun x x' hxx ↦ ?_,
    fun x h hdim ↦ ?_⟩
  · have hq : q x = q x' :=
      congrArg (fun χ : MonicIrreduciblePoint _ ↦ MonicIrreducibleOfDegree.poly χ.2) hxx
    exact Subtype.ext (eq_of_fibrePrime_eq x.2.1 x'.2.1 (by rw [hqspan, hqspan, hq]))
  · refine exists_addEquiv_pointClosureMilnorBoundary C A p hζ h _ ?_ hdim
    show (Ideal.span {q x}).comap _ = _
    rw [← hqspan x]
    exact comap_fibrePrime x.2.1

/-- Unless `δ(y)` is `k` or `k + 1`, a K₁-chain of relative dimension `k + 1` supported on the
fibre over `y` is zero: the fibre has no points of that dimension. -/
theorem eq_zero_of_fibreRestrict_eq_self_specPolynomial {k : ℤ} {y : Spec A}
    (hδ : relativeDimension C.dimensionFunction sV y ≠ k)
    (hk : relativeDimension C.dimensionFunction sV y ≠ k + 1)
    {a : PointwiseKOneGroup C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k}
    (ha : fibreRestrict C (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) y (k + 1) 1 a = a) :
    a = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_contra hx
  have hxy := base_eq_of_fibreRestrict_eq_self C ha hx
  have hxdim := (mem_pointsOfDimension C _).mp x.2
  by_cases hg : x.1 = fibreGenericPoint y
  · rw [hg, relativeDimension_fibreGenericPoint] at hxdim
    exact hδ (by omega)
  · rw [relativeDimension_of_ne_fibreGenericPoint C A sV hxy hg] at hxdim
    exact hk hxdim

/-- **The residues of a single class at the generic point of the fibre**: by Milnor's exact
sequence for `κ(y)(T)`, the classes of a K₁-chain at the closed points of the fibre over `y` are
the tame-symbol boundaries of one class of `K₂ᴹ(κ(ζ))` at the generic point `ζ` of the fibre. -/
theorem exists_pointClosureMilnorBoundary_eq_specPolynomial {k : ℤ} (y : Spec A)
    (a : PointwiseKOneGroup C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) k) :
    ∃ θ, ∀ (x : pointsOfDimension C
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 1)),
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base x.1 = y →
      x.1 ≠ fibreGenericPoint y →
      ∀ (h : x.1 ∈ closure ({fibreGenericPoint y} : Set (Spec (CommRingCat.of (Polynomial A)))))
        (hdim : ringKrullDim ((integralComponentAt (fibreGenericPoint y)).subscheme.presheaf.stalk
          (pointClosurePoint (fibreGenericPoint y) h)) = 1),
        pointClosureMilnorBoundary C
          (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
          (fibreGenericPoint y) h hdim ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv
            (isGenericFibrePoint_fibreGenericPoint y))).symm θ) = a.1 x := by
  classical
  have hζ : IsGenericFibrePoint (fibreGenericPoint y) := isGenericFibrePoint_fibreGenericPoint y
  have hζy : specPolynomialBase (fibreGenericPoint y) = y := specMap_C_base_fibreGenericPoint y
  obtain ⟨ψ, hψ, hbd⟩ := exists_monicIrreduciblePoint_fibre C A
    (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) hζ
  choose e he using hbd
  have hcl : ∀ x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase (fibreGenericPoint y) ∧ x ≠ fibreGenericPoint y},
      x.1 ∈ closure ({fibreGenericPoint y} : Set (Spec (CommRingCat.of (Polynomial A)))) :=
    fun x ↦ specializes_iff_mem_closure.mp (hζ.specializes x.2.1)
  have hdimS : ∀ x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase (fibreGenericPoint y) ∧ x ≠ fibreGenericPoint y},
      ringKrullDim ((integralComponentAt (fibreGenericPoint y)).subscheme.presheaf.stalk
        (pointClosurePoint (fibreGenericPoint y) (hcl x))) = 1 := fun x ↦
    ringKrullDim_pointClosureStalk_eq_one A hζ (hcl x) x.2.1 x.2.2
  let aF : ∀ x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase (fibreGenericPoint y) ∧ x ≠ fibreGenericPoint y},
      MilnorKTheory ((Spec (CommRingCat.of (Polynomial A))).residueField x.1) 1 := fun x ↦
    if hx : x.1 ∈ pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 1)
    then a.1 ⟨x.1, hx⟩ else 0
  have hfin : {x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase (fibreGenericPoint y) ∧ x ≠ fibreGenericPoint y} |
        aF x ≠ 0}.Finite := by
    have hA := a.2 ⊤ (by simpa using isCompact_univ)
    refine Set.Finite.of_finite_image (f := fun x : {x : Spec (CommRingCat.of (Polynomial A)) //
      specPolynomialBase x = specPolynomialBase (fibreGenericPoint y) ∧
        x ≠ fibreGenericPoint y} ↦ x.1)
      ((hA.image fun z ↦ z.1).subset ?_) (Set.injOn_of_injective Subtype.val_injective)
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxd : x.1 ∈ pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 1)
    · refine ⟨⟨x.1, hxd⟩, ⟨trivial, ?_⟩, rfl⟩
      rwa [← (dif_pos hxd : aF x = a.1 ⟨x.1, hxd⟩)]
    · exact absurd (dif_neg hxd) hx
  obtain ⟨θ, hθ⟩ := exists_milnorKTwoTameSymbol_eq ψ hψ hfin.toFinset
    (fun x ↦ e x (hcl x) (hdimS x) (aF x)) (fun x hx ↦ by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hx
      rw [hx]
      exact (e x (hcl x) (hdimS x)).map_zero)
  refine ⟨θ, fun x hxy hne h hdim ↦ ?_⟩
  have hxF : specPolynomialBase x.1 = specPolynomialBase (fibreGenericPoint y) :=
    hxy.trans hζy.symm
  apply (e ⟨x.1, hxF, hne⟩ h hdim).injective
  rw [he ⟨x.1, hxF, hne⟩ h hdim θ]
  exact (hθ ⟨x.1, hxF, hne⟩).trans (congrArg (e ⟨x.1, hxF, hne⟩ h hdim) (dif_pos x.2))

/-- A single class at one point is a locally finite Milnor K-chain. -/
theorem exists_milnorChainGroup_single {X : Scheme.{u}} {p : X ⟶ C.S} {m : ℤ} {n : ℕ}
    (z : pointsOfDimension C p m) (c : MilnorKTheory (X.residueField z.1) n) :
    ∃ η : MilnorChainGroup C p m n, η.1 z = c ∧ ∀ x, x ≠ z → η.1 x = 0 := by
  classical
  exact ⟨⟨Pi.single z c, fun U _ ↦ (Set.finite_singleton _).subset fun x hx ↦ by
      by_contra hne
      exact hx.2 (Pi.single_eq_of_ne hne _)⟩, Pi.single_eq_same _ _,
    fun x hx ↦ Pi.single_eq_of_ne hx _⟩

/-- **Boundary lifting for `Spec A[T] ⟶ Spec A`**, Stacks 0GUA for the affine line below the top
degree: away from the level of the generic points of the fibres, a degree-one Milnor K-chain on
the fibre over `y` is the tame-symbol boundary of a degree-two chain on that fibre. Below the
closed points of the fibre there is nothing to lift; at the closed points the chain is a finite
family of classes, which by Milnor's exact sequence for `κ(y)(T)` are the residues of a single
class at the generic point of the fibre. -/
theorem fibreBoundaryLift_specPolynomial (k : ℤ) (y : Spec A) :
    FibreBoundaryLift C (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV)
      sV (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) 1 k y := by
  classical
  intro hδ a ha _
  have hδ' : relativeDimension C.dimensionFunction sV y ≠ k :=
    fun h ↦ hδ (by rw [h]; push_cast; ring)
  by_cases hk : relativeDimension C.dimensionFunction sV y = k + 1
  swap
  · exact ⟨0, map_zero _, by
      rw [map_zero, map_zero, eq_zero_of_fibreRestrict_eq_self_specPolynomial C A sV hδ' hk ha]⟩
  have hζ : IsGenericFibrePoint (fibreGenericPoint y) := isGenericFibrePoint_fibreGenericPoint y
  have hζy : specPolynomialBase (fibreGenericPoint y) = y := specMap_C_base_fibreGenericPoint y
  have hζdim : fibreGenericPoint y ∈ pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 2) := by
    rw [mem_pointsOfDimension, relativeDimension_fibreGenericPoint, hk]
    ring
  obtain ⟨θ, hθ⟩ := exists_pointClosureMilnorBoundary_eq_specPolynomial C A sV y a
  obtain ⟨ηc, hηζ, hηne⟩ := exists_milnorChainGroup_single C
    (⟨fibreGenericPoint y, hζdim⟩ : pointsOfDimension C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ sV) (k + 2))
    ((milnorKTwoRingEquiv (fibreGenericResidueFieldEquiv hζ)).symm θ)
  refine ⟨ηc, ?_, ?_⟩
  · refine milnorChainRestrict_eq_self _ fun x hx ↦ ?_
    by_contra hxy
    exact hx (hηne x fun h ↦ hxy (by rw [h]; exact hζy))
  · refine Subtype.ext (funext fun x' ↦ ?_)
    by_cases hx' : (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).base x'.1 = y
    · have hne' : x'.1 ≠ fibreGenericPoint y := fun h ↦ by
        have := (mem_pointsOfDimension C _).mp x'.2
        rw [h, relativeDimension_fibreGenericPoint, hk] at this
        omega
      have hxF : specPolynomialBase x'.1 = specPolynomialBase (fibreGenericPoint y) :=
        hx'.trans hζy.symm
      rw [milnorChainRestrict_apply_of_mem _ hx',
        pointwiseMilnorBoundary_apply, pointwiseMilnorBoundaryCoeff,
        finsum_eq_single _ ⟨fibreGenericPoint y, hζdim⟩ (fun x hx ↦
          pointwiseMilnorBoundaryTerm_of_eq_zero C _ k ηc (hηne x hx) x'),
        pointwiseMilnorBoundaryTerm_of_specializes C _ k ηc ⟨fibreGenericPoint y, hζdim⟩ x'
          (hζ.specializes hxF) (ringKrullDim_pointClosureStalk_eq_one A hζ _ hxF hne'), hηζ]
      exact hθ x' hx' hne' _ _
    · rw [milnorChainRestrict_apply_of_notMem _ hx']
      by_contra h0
      exact hx' (base_eq_of_fibreRestrict_eq_self C ha (Ne.symm h0))

end Boundary

end Stacks.Chow

end
