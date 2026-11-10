module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.SetTheory.Cardinal.ENat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The general dimension formula

Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type, with `S` locally
Noetherian, and let `x` be a point of `X`. Dropping the integrality and dominance hypotheses of
the dimension formula for integral schemes (Stacks 02JU,
`AlgebraicGeometry.localDimension_add_trdeg_le`) costs the function-field term; what replaces it
is the largest residue-field transcendence degree at a generic point of an irreducible component
of `X` through `x`:

  `dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + max_ξ trdeg_{κ(f ξ)} κ(ξ)`.

## Main definitions and results

The two degrees, `AlgebraicGeometry.residueFieldTranscendenceDegree` (the transcendence degree
of `κ(x)/κ(f x)`) and `AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt` (its supremum
over the generic points of the irreducible components through a point), and the general
dimension formula itself,
`AlgebraicGeometry.ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le` (**Stacks 0BAE**),
are in `StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula`, which this module
imports. This module contains the steps of the argument sketched below;
the last of them is the formula on the irreducible component named by one minimal prime of
`𝒪_{X,x}`.

## Implementation notes

The source reduces to the integral case by cutting `X` down to the irreducible components
through `x`. Those components are indexed by the minimal primes of `𝒪_{X,x}`: the generic point
of the component of `x` corresponding to a minimal prime `p` is the image of `p` under
`AlgebraicGeometry.Scheme.fromSpecStalk`, whose range is the set of points specializing to `x`,
and the local ring of that component at `x` is `𝒪_{X,x} ⧸ p`. Since `ringKrullDim` of a ring is
the supremum of `ringKrullDim` over the quotients by its minimal primes, the inequality at `x`
is the supremum over those components of the inequality for the component, and each of those is
Stacks 02JU applied to the morphism of integral schemes induced on the reduced closures of the
generic point and of its image. The two closures carry the reduced induced structure, i.e. are
the subschemes cut out by the vanishing ideal sheaves of the closures, and the induced morphism
between them exists by the factorization criterion of Stacks 0356 and is dominant because it
takes generic point to generic point.

Comparing the two sides of Stacks 02JU with the two sides of the statement is a matter of
residue fields: the closed immersion of a reduced closure is surjective on stalks, hence an
isomorphism on residue fields, so the residue-field degree of the component at a point agrees
with that of `f` at the image point, and the function-field degree of the component agrees with
the residue-field degree of `f` at its generic point.

Transcendence degrees are counted in `ℕ∞` with `Cardinal.toENat`, and the residue-field term is
added on the left rather than subtracted on the right: the subtraction of the source would be
truncated in `WithBot ℕ∞` and would make the statement weaker when the degree exceeds the right
side. `Stacks.Chow.residueTrdeg` is the `Cardinal`-valued form of the same degree, used in the
chapter on Chow homology; the degree here is its image under `Cardinal.toENat`.

## References

* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The reduced closure of a point -/

instance reducedPointClosure_isReduced (X : Scheme.{u}) (z : X) :
    IsReduced (reducedPointClosure X z).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal ⟨closure {z}, isClosed_closure⟩

/-- The closure of a point with its reduced induced structure is an integral scheme. -/
instance reducedPointClosure_isIntegral (X : Scheme.{u}) (z : X) :
    IsIntegral (reducedPointClosure X z).subscheme := by
  let I := reducedPointClosure X z
  let e : I.subscheme ≃ₜ (closure {z} : Set X) :=
    Homeomorph.setCongr (reducedPointClosure_support X z)
  have : IrreducibleSpace I.subscheme :=
    e.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace isIrreducible_singleton.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- A morphism of schemes carries the reduced closure of a point of its source into the reduced
closure of the image point: the image of the closure is contained in the closure of the image,
so the factorization criterion of Stacks 0356 applies. -/
@[ega "IV 13.2.4" "partial"]
theorem exists_reducedPointClosure_map {X S : Scheme.{u}} (f : X ⟶ S) (η : X) :
    ∃ g : (reducedPointClosure X η).subscheme ⟶ (reducedPointClosure S (f η)).subscheme,
      g ≫ (reducedPointClosure S (f η)).subschemeι =
        (reducedPointClosure X η).subschemeι ≫ f := by
  let I := reducedPointClosure X η
  let J := reducedPointClosure S (f η)
  apply (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support J
    (I.subschemeι ≫ f)).2
  rintro _ ⟨z, rfl⟩
  have hz : (I.subschemeι z : X) ∈ closure {η} := reducedPointClosure_support X η ▸ z.2
  have hclosure := image_closure_subset_closure_image f.continuous
    (show f (I.subschemeι z) ∈ f '' closure {η} from ⟨I.subschemeι z, hz, rfl⟩)
  change f (I.subschemeι z) ∈ (J.support : Set S)
  rw [show (J.support : Set S) = closure {f η} from reducedPointClosure_support S (f η)]
  simpa using hclosure

/-- The generic point of the reduced closure of a point is that point. -/
theorem reducedPointClosureι_genericPoint (X : Scheme.{u}) (z : X) :
    (reducedPointClosure X z).subschemeι
        (genericPoint (reducedPointClosure X z).subscheme) = z := by
  let I := reducedPointClosure X z
  have hgen := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
  rw [Set.image_univ, I.range_subschemeι, reducedPointClosure_support X z,
    closure_closure] at hgen
  exact hgen.eq isGenericPoint_closure

/-- The morphism between the reduced closures induced by a morphism of schemes is dominant: it
takes the generic point to the generic point. -/
private alias reducedPointClosure_map_dominant := isDominant_map_reducedPointClosure

/-! ### Krull dimension through the minimal primes -/

/-- The Krull dimension of a ring is the supremum of the Krull dimensions of its quotients by
minimal primes: every prime contains a minimal one, and coheight is antitone. -/
@[ega "0 16.1.1"]
theorem ringKrullDim_eq_iSup_minimalQuotients {R : Type u} [CommRing R] :
    ringKrullDim R =
      ⨆ p : {p : PrimeSpectrum R // p.asIdeal ∈ (⊥ : Ideal R).minimalPrimes},
        ringKrullDim (R ⧸ p.1.asIdeal) := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  refine le_antisymm (iSup_le fun q => ?_) (iSup_le fun p => ?_)
  · obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
      (R := R) (I := (⊥ : Ideal R)) (J := q.asIdeal) bot_le
    let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
    have hp' : p'.asIdeal ∈ (⊥ : Ideal R).minimalPrimes := by simpa [p'] using hp
    calc (Order.coheight q : WithBot ℕ∞) ≤ Order.coheight p' :=
          WithBot.coe_le_coe.mpr (Order.coheight_anti
            ((PrimeSpectrum.asIdeal_le_asIdeal p' q).mpr hpq))
      _ = ringKrullDim (R ⧸ p'.asIdeal) := coheight_eq_ringKrullDim_quotient p'
      _ ≤ _ := le_iSup_of_le ⟨p', hp'⟩ le_rfl
  · rw [← coheight_eq_ringKrullDim_quotient]
    exact le_iSup_of_le p.1 le_rfl

theorem genericPointOfMinimalStalkPrime_specializes
    {X : Scheme.{u}} (x : X)
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes}) :
    (genericPointOfMinimalStalkPrime x p).1 ⤳ x := by
  have hmem : (genericPointOfMinimalStalkPrime x p).1 ∈ Set.range (X.fromSpecStalk x) :=
    ⟨OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1), rfl⟩
  rwa [Scheme.range_fromSpecStalk] at hmem

/-- The local ring at `x` of the reduced closure of the generic point named by a minimal prime
`p` of `𝒪_{X,x}` is `𝒪_{X,x} ⧸ p`. -/
theorem reducedPointClosure_stalk_dim_eq_quotient
    {X : Scheme.{u}} (x : X)
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes}) :
    ∃ z : (reducedPointClosure X (genericPointOfMinimalStalkPrime x p)).subscheme,
      (reducedPointClosure X (genericPointOfMinimalStalkPrime x p)).subschemeι z = x ∧
      ringKrullDim
          ((reducedPointClosure X
            (genericPointOfMinimalStalkPrime x p)).subscheme.presheaf.stalk z) =
        ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) := by
  let η := genericPointOfMinimalStalkPrime x p
  let I := reducedPointClosure X η.1
  have hxI : x ∈ I.support := by
    change x ∈ (closure {η.1} : Set X)
    exact specializes_iff_mem_closure.mp (genericPointOfMinimalStalkPrime_specializes x p)
  let z : I.subscheme := ⟨x, hxI⟩
  have hz : I.subschemeι z = x := rfl
  refine ⟨z, hz, ?_⟩
  let eX := X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)
  let φcat := eX.hom ≫ I.subschemeι.stalkMap z
  let φ : X.presheaf.stalk x →+* I.subscheme.presheaf.stalk z := φcat.hom
  have hsurj : Function.Surjective φ :=
    (I.subschemeι.stalkMap_surjective z).comp (ConcreteCategory.bijective_of_isIso eX.hom).2
  let pSpec : Spec (CommRingCat.of (X.presheaf.stalk x)) :=
    OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)
  have hdiag : Spec.map φcat ≫ X.fromSpecStalk x =
      I.subscheme.fromSpecStalk z ≫ I.subschemeι := by
    have hcongr : Spec.map eX.hom ≫ X.fromSpecStalk x = X.fromSpecStalk (I.subschemeι z) := by
      simpa [eX, TopCat.Presheaf.stalkCongr] using
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (Inseparable.of_eq hz.symm).ge)
    change Spec.map (eX.hom ≫ I.subschemeι.stalkMap z) ≫ X.fromSpecStalk x = _
    rw [Spec.map_comp, Category.assoc, hcongr,
      Scheme.SpecMap_stalkMap_fromSpecStalk I.subschemeι]
  have hpSpec : pSpec = (Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z))) := by
    apply (X.fromSpecStalk x).isEmbedding.injective
    change η.1 = _
    calc
      η.1 = I.subschemeι (genericPoint I.subscheme) :=
        (reducedPointClosureι_genericPoint X η.1).symm
      _ = (I.subscheme.fromSpecStalk z ≫ I.subschemeι)
            (genericPoint (Spec (I.subscheme.presheaf.stalk z))) := by
        rw [Scheme.Hom.comp_apply, fromSpecStalk_genericPoint]
      _ = _ := by rw [← hdiag, Scheme.Hom.comp_apply]
  have hker : RingHom.ker φ = p.1.asIdeal := by
    have hq : (OrderDual.ofDual (specOrderIsoPrimeSpectrum (.of (X.presheaf.stalk x))
        ((Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z)))))).asIdeal =
        RingHom.ker φ := by
      rw [genericPoint_eq_bot_of_affine]
      change (PrimeSpectrum.comap φ (⊥ : PrimeSpectrum (I.subscheme.presheaf.stalk z))).asIdeal = _
      rw [PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot]
      rfl
    rw [← hpSpec] at hq
    exact hq.symm
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := φ) hsurj))).symm

/-! ### Residue fields along a surjection on stalks -/

/-- A morphism of schemes which is surjective on the stalk at a point is an isomorphism on the
residue field there. -/
private theorem residueFieldMap_isIso_of_stalkMap_surjective
    {X Y : Scheme.{u}} (i : X ⟶ Y) (x : X)
    (hsurj : Function.Surjective (i.stalkMap x).hom) :
    IsIso (i.residueFieldMap x) := by
  let φ := (i.residueFieldMap x).hom
  have hsurj' : Function.Surjective φ := by
    intro b
    obtain ⟨b₀, hb₀⟩ := X.residue_surjective x b
    obtain ⟨a, ha⟩ := hsurj b₀
    refine ⟨Y.residue (i x) a, ?_⟩
    have hnat' := congrArg (fun k : Y.presheaf.stalk (i x) →+* X.residueField x => k a)
      (congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap i x))
    change φ (Y.residue (i x) a) = X.residue x ((i.stalkMap x).hom a) at hnat'
    rwa [ha, hb₀] at hnat'
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective φ, hsurj'⟩

/-- In a commuting square whose two vertical maps are surjective on stalks, the residue-field
transcendence degree of the top map at a point equals that of the bottom map at its image. -/
theorem residueFieldTrdeg_eq_of_closedSquare
    {A X B S : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ S) (g : A ⟶ B)
    (f : X ⟶ S) (a : A) (hsq : g ≫ j = i ≫ f)
    (hi : Function.Surjective (i.stalkMap a).hom)
    (hj : Function.Surjective (j.stalkMap (g a)).hom) :
    letI := (g.residueFieldMap a).hom.toAlgebra
    letI := (f.residueFieldMap (i a)).hom.toAlgebra
    Algebra.trdeg (B.residueField (g a)) (A.residueField a) =
      Algebra.trdeg (S.residueField (f (i a))) (X.residueField (i a)) := by
  have hp : j (g a) = f (i a) := congrArg (fun k : A ⟶ S => k a) hsq
  have hiIso : IsIso (i.residueFieldMap a) :=
    residueFieldMap_isIso_of_stalkMap_surjective i a hi
  have hjIso : IsIso (j.residueFieldMap (g a)) :=
    residueFieldMap_isIso_of_stalkMap_surjective j (g a) hj
  let eX : A.residueField a ≃+* X.residueField (i a) :=
    (asIso (i.residueFieldMap a)).symm.commRingCatIsoToRingEquiv
  let eB₀ : B.residueField (g a) ≃+* S.residueField (j (g a)) :=
    (asIso (j.residueFieldMap (g a))).symm.commRingCatIsoToRingEquiv
  let eB₁ : S.residueField (j (g a)) ≃+* S.residueField (f (i a)) :=
    (S.residueFieldCongr hp).commRingCatIsoToRingEquiv
  let eB := eB₀.trans eB₁
  let φ := (g.residueFieldMap a).hom
  let ψ := (f.residueFieldMap (i a)).hom
  let ι := (i.residueFieldMap a).hom
  let jρ := (j.residueFieldMap (g a)).hom
  let χ := ((S.residueFieldCongr hp).hom).hom
  have hcat : j.residueFieldMap (g a) ≫ g.residueFieldMap a =
      (S.residueFieldCongr hp).hom ≫ f.residueFieldMap (i a) ≫ i.residueFieldMap a := by
    have h := Scheme.Hom.residueFieldMap_congr hsq a
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at h
    simpa [hp] using h
  have hring : φ.comp jρ = ι.comp (ψ.comp χ) := by
    have h := congrArg CommRingCat.Hom.hom hcat
    simpa [φ, jρ, ι, ψ, χ, CommRingCat.hom_comp, RingHom.comp_assoc] using h
  let : Algebra (B.residueField (g a)) (A.residueField a) := φ.toAlgebra
  let : Algebra (S.residueField (f (i a))) (X.residueField (i a)) := ψ.toAlgebra
  refine Algebra.trdeg_eq_of_ringEquiv eB eX fun b => ?_
  let s := eB₀ b
  have hs : jρ s = b := eB₀.symm_apply_apply b
  have h := DFunLike.congr_fun hring s
  change φ (jρ s) = ι (ψ (χ s)) at h
  change eX (φ b) = ψ (eB b)
  rw [← hs, h]
  calc
    eX (ι (ψ (χ s))) = ψ (χ s) := eX.apply_symm_apply _
    _ = ψ (eB₁ s) := rfl
    _ = ψ (eB₁ (eB₀ (jρ s))) := by rw [show eB₀ (jρ s) = s from eB₀.apply_symm_apply s]
    _ = ψ (eB (jρ s)) := rfl

/-- For a dominant morphism of integral schemes the function-field transcendence degree is the
residue-field transcendence degree at the generic point. -/
private alias functionFieldTrdeg_eq_genericResidueFieldTrdeg :=
    toENat_trdeg_functionField_eq_residueFieldTrdeg_genericPoint

/-- Stacks 02JU transported to a commuting square of schemes whose vertical maps are surjective
on stalks: with `A` and `B` integral and `g : A ⟶ B` dominant and locally of finite type, the
dimension formula for `g` reads off the residue-field degrees of `f`. -/
theorem integralSquare_dimension_add_residueFieldTrdeg_le
    {A X B S : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ S) (g : A ⟶ B)
    (f : X ⟶ S) [IsIntegral A] [IsIntegral B] [IsDominant g]
    [IsLocallyNoetherian B] [LocallyOfFiniteType g] (a : A)
    (hsq : g ≫ j = i ≫ f)
    (hi : ∀ z : A, Function.Surjective (i.stalkMap z).hom)
    (hj : ∀ z : B, Function.Surjective (j.stalkMap z).hom) :
    ringKrullDim (A.presheaf.stalk a) +
        (residueFieldTranscendenceDegree f (i a) : WithBot ℕ∞) ≤
      ringKrullDim (B.presheaf.stalk (g a)) +
        (residueFieldTranscendenceDegree f (i (genericPoint A)) : WithBot ℕ∞) := by
  let := (dominantFunctionFieldMap g).toAlgebra
  let := (g.residueFieldMap a).hom.toAlgebra
  have h02 := localDimension_add_trdeg_le g a
  have hlocal := residueFieldTrdeg_eq_of_closedSquare i j g f a hsq (hi a) (hj (g a))
  have hgeneric := residueFieldTrdeg_eq_of_closedSquare i j g f
    (genericPoint A) hsq (hi (genericPoint A)) (hj (g (genericPoint A)))
  have hfunction := functionFieldTrdeg_eq_genericResidueFieldTrdeg g
  unfold residueFieldTranscendenceDegree
  rw [hlocal, hfunction] at h02
  unfold residueFieldTranscendenceDegree at h02
  rwa [hgeneric] at h02

/-- The dimension formula on the irreducible component of `x` named by a minimal prime of
`𝒪_{X,x}`. -/
private alias minimalStalkComponent_dimension_add_residueFieldTrdeg_le :=
    minimalPrime_localDimension_add_residueFieldTrdeg_le

end AlgebraicGeometry

end
