module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec

/-!
# The universal property of the normalization of a scheme

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. A
morphism to `X` from a normal scheme each of whose irreducible components dominates an
irreducible component of `X` factors uniquely through the normalization of `X`.

## Main results

* `IsNormalRing.liftIntegralClosureFractionRing` is the ring-level core: a ring map `A → B` with
  `A` reduced carrying non-zerodivisors to non-zerodivisors, with `B` normal, extends to the
  integral closure of `A` in its total ring of fractions, and
  `IsNormalRing.liftIntegralClosureFractionRing_unique` says the extension is unique.
* `mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes`: in a reduced ring the non-zerodivisors
  are exactly the elements avoiding every minimal prime.
* `AlgebraicGeometry.Scheme.existsUnique_lift_normalization` is Tag 035Q part (4).

## Implementation notes

The condition that every irreducible component of the source dominates an irreducible component
of the target is expressed by saying that the generic point of each component of the source maps
into `genericPoints` of the target.

The proof follows the source. One first reduces to a reduced target: a morphism from a reduced
scheme factors through the reduction (Tag 0356), the generic points are unchanged because the
closed immersion of the reduction is a homeomorphism, and the normalization of `X` is canonically
the normalization of its reduction — that last comparison is
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction` below, built from the
universal property of relative normalization (Tag 035I) after transporting the generic-point
residue spectrum along the homeomorphism.

For a reduced target the factorization is constructed affine-locally and glued. Over an affine
open `U = Spec A` of `X` the normalization is `Spec` of the integral closure `A'` of `A` in its
total ring of fractions (Tag 035P). An affine open `V = Spec B` of the source mapping into `U`
has `B` normal, hence reduced and integrally closed in its own total ring of fractions (Tag
034M); the generic-point hypothesis says every minimal prime of `B` contracts to a minimal prime
of `A`, so non-zerodivisors of `A` go to non-zerodivisors of `B` and the total rings of fractions
map. That carries `A'` into `B`. Uniqueness of the local lift is what lets the local pieces be
glued, and is also what gives global uniqueness.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-! ### The ring-level lift into a normal ring -/

/-- A normal ring is integrally closed in its total ring of fractions, in the form used below:
an integral element of the total ring of fractions comes from the ring.  This is Tag 034M. -/
@[ega "IV 6.14.1.1" "(i)"]
theorem IsNormalRing.exists_algebraMap_eq_of_isIntegral {B : Type u} [CommRing B]
    (hB : IsNormalRing B) {x : FractionRing B} (hx : IsIntegral B x) :
    ∃ b : B, algebraMap B (FractionRing B) b = x :=
  letI := hB.isIntegrallyClosed
  IsIntegrallyClosed.isIntegral_iff.mp hx

/-- The map on total rings of fractions induced by a ring map carrying non-zerodivisors to
non-zerodivisors. -/
noncomputable def RingHom.fractionRingMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) :
    FractionRing A →+* FractionRing B :=
  IsLocalization.map (FractionRing B) φ hreg

/-- The induced map on total rings of fractions commutes with the two localization maps. -/
theorem RingHom.algebraMap_comp_eq_fractionRingMap_comp {A B : Type u} [CommRing A]
    [CommRing B] (φ : A →+* B) (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) :
    (algebraMap B (FractionRing B)).comp φ =
      (φ.fractionRingMap hreg).comp (algebraMap A (FractionRing A)) := by
  ext a
  simp [RingHom.fractionRingMap]

/-- The value at one element of the lift of `φ` to the integral closure of `A` in its total ring
of fractions. -/
noncomputable def IsNormalRing.liftIntegralClosureFractionRingValue {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B)
    (x : integralClosure A (FractionRing A)) : B :=
  Classical.choose (hB.exists_algebraMap_eq_of_isIntegral
    (IsIntegral.map_of_comp_eq φ (φ.fractionRingMap hreg)
      (RingHom.algebraMap_comp_eq_fractionRingMap_comp φ hreg) x.2))

/-- The defining property of `IsNormalRing.liftIntegralClosureFractionRingValue`. -/
theorem IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B)
    (x : integralClosure A (FractionRing A)) :
    algebraMap B (FractionRing B)
        (IsNormalRing.liftIntegralClosureFractionRingValue φ hreg hB x) =
      φ.fractionRingMap hreg x.1 :=
  Classical.choose_spec (hB.exists_algebraMap_eq_of_isIntegral
    (IsIntegral.map_of_comp_eq φ (φ.fractionRingMap hreg)
      (RingHom.algebraMap_comp_eq_fractionRingMap_comp φ hreg) x.2))

/-- Let `φ : A → B` be a ring map carrying non-zerodivisors to non-zerodivisors, and let `B` be a
normal ring.  Then `φ` extends to the integral closure of `A` in its total ring of fractions: the
induced map on total rings of fractions carries an element integral over `A` to an element
integral over `B`, and `B` is integrally closed in its own total ring of fractions. -/
noncomputable def IsNormalRing.liftIntegralClosureFractionRing {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B) :
    integralClosure A (FractionRing A) →+* B where
  toFun := IsNormalRing.liftIntegralClosureFractionRingValue φ hreg hB
  map_one' := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue, map_one]
    exact map_one _
  map_mul' x y := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue,
      IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue,
      IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue]
    exact map_mul _ x.1 y.1
  map_zero' := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue, map_zero]
    exact map_zero _
  map_add' x y := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_add, IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue,
      IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue,
      IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue]
    exact map_add _ x.1 y.1

@[simp]
theorem IsNormalRing.liftIntegralClosureFractionRing_apply {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B)
    (x : integralClosure A (FractionRing A)) :
    IsNormalRing.liftIntegralClosureFractionRing φ hreg hB x =
      IsNormalRing.liftIntegralClosureFractionRingValue φ hreg hB x := rfl

/-- The lift of `φ` to the integral closure restricts to `φ`. -/
theorem IsNormalRing.liftIntegralClosureFractionRing_comp_algebraMap {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B) :
    (IsNormalRing.liftIntegralClosureFractionRing φ hreg hB).comp
      (algebraMap A (integralClosure A (FractionRing A))) = φ := by
  ext a
  apply IsFractionRing.injective B (FractionRing B)
  rw [RingHom.comp_apply, IsNormalRing.liftIntegralClosureFractionRing_apply,
    IsNormalRing.algebraMap_liftIntegralClosureFractionRingValue]
  exact (congrArg (fun k : A →+* FractionRing B => k a)
    (RingHom.algebraMap_comp_eq_fractionRingMap_comp φ hreg)).symm

/-- The lift of `φ` to the integral closure is the only ring map restricting to `φ`: every
element of the integral closure has a non-zerodivisor multiple coming from `A`. -/
theorem IsNormalRing.liftIntegralClosureFractionRing_unique {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (hreg : nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ) (hB : IsNormalRing B)
    (ψ : integralClosure A (FractionRing A) →+* B)
    (hψ : ψ.comp (algebraMap A (integralClosure A (FractionRing A))) = φ) :
    ψ = IsNormalRing.liftIntegralClosureFractionRing φ hreg hB := by
  ext x
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) x.1
  have hx : x * algebraMap A (integralClosure A (FractionRing A)) s.1 =
      algebraMap A (integralClosure A (FractionRing A)) a := Subtype.ext hs
  have key (τ : integralClosure A (FractionRing A) →+* B)
      (hτ : τ.comp (algebraMap A (integralClosure A (FractionRing A))) = φ) :
      τ x * φ s.1 = φ a := by
    have hτA (b : A) : τ (algebraMap A (integralClosure A (FractionRing A)) b) = φ b :=
      congrArg (fun k : A →+* B => k b) hτ
    simpa only [map_mul, hτA] using congrArg τ hx
  have hzero :
      (ψ x - IsNormalRing.liftIntegralClosureFractionRing φ hreg hB x) * φ s.1 = 0 := by
    rw [sub_mul, (key ψ hψ).trans
      (key _ (IsNormalRing.liftIntegralClosureFractionRing_comp_algebraMap φ hreg hB)).symm]
    simp
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (hreg s.2)).2 _ hzero)

/-! ### Non-zerodivisors in a reduced ring -/

/-- In a reduced ring the non-zerodivisors are exactly the elements lying in no minimal prime. -/
theorem mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes
    {B : Type u} [CommRing B] [IsReduced B] (b : B) :
    b ∈ nonZeroDivisors B ↔ ∀ p ∈ minimalPrimes B, b ∉ p := by
  constructor
  · intro hb p hp hbp
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hbp hp hb
  · intro hb
    rw [mem_nonZeroDivisors_iff_right]
    intro c hcb
    by_contra hne
    have hcnot : c ∉ sInf (minimalPrimes B) := by
      rw [Ideal.sInf_minimalPrimes]
      simpa [Ideal.radical_bot_of_isReduced] using hne
    have hcnot' : ¬ ∀ p ∈ minimalPrimes B, c ∈ p := by
      simpa only [Ideal.mem_sInf] using hcnot
    push Not at hcnot'
    obtain ⟨p, hp, hcp⟩ := hcnot'
    have hmul : c * b ∈ p := by rw [hcb]; exact p.zero_mem
    rcases hp.isPrime.mem_or_mem hmul with hcp' | hbp
    · exact hcp hcp'
    · exact hb p hp hbp

/-- A ring map under which every minimal prime of the target contracts to a minimal prime of the
source carries non-zerodivisors to non-zerodivisors, provided the target is reduced. -/
theorem map_mem_nonZeroDivisors_of_comap_minimalPrimes
    {A B : Type u} [CommRing A] [CommRing B] [IsReduced B] (φ : A →+* B)
    (hmap : ∀ q ∈ minimalPrimes B, Ideal.comap φ q ∈ minimalPrimes A) :
    nonZeroDivisors A ≤ (nonZeroDivisors B).comap φ := by
  intro a ha
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes]
  intro q hq hφa
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (q := Ideal.comap φ q) (show a ∈ Ideal.comap φ q from hφa) (hmap q hq) ha

namespace AlgebraicGeometry

/-! ### Preliminaries on generic points and normality -/

/-- An open subscheme of a normal scheme is normal, for an arbitrary open immersion. -/
private theorem isNormal_of_isOpenImmersion {V Z : Scheme.{u}} [IsNormal Z] (i : V ⟶ Z)
    [IsOpenImmersion i] : IsNormal V := by
  rw [isNormal_iff_stalk_normal]
  intro x
  let e := (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed (Z.presheaf.stalk (i x)) := IsNormal.stalk_normal _
  have : IsDomain (V.presheaf.stalk x) := Function.Injective.isDomain e.symm e.symm.injective
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

/-- The global sections of an affine normal scheme form a normal ring. -/
private theorem isNormalRing_sections_top {V : Scheme.{u}} [IsAffine V] [IsNormal V] :
    IsNormalRing Γ(V, ⊤) := by
  have h := (isNormal_tfae V).out 1 2
  simpa using h.mp (inferInstance : IsNormal V) ⟨⊤, isAffineOpen_top V⟩

/-! ### The affine-local lift -/

/-- The generic-point hypothesis, read on an affine chart: every minimal prime of the chart of
the source contracts to a minimal prime of the chart of the target. -/
private theorem comap_mem_minimalPrimes_appLE {X Z : Scheme.{u}} (f : Z ⟶ X)
    (U : X.Opens) (V : Z.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U)
    (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X) :
    ∀ q ∈ minimalPrimes Γ(Z, V),
      Ideal.comap (f.appLE U V hVU).hom q ∈ minimalPrimes Γ(X, U) := by
  intro q hq
  let ηV : genericPoints (V : Set Z) := (genericPointsAffineOpenEquiv hV).symm ⟨q, hq⟩
  let ηZV : {η : genericPoints Z // η.1 ∈ V} := (Scheme.genericPointsInOpenEquiv Z V).symm ηV
  have hηVsubtype : ((Scheme.genericPointsInOpenEquiv Z V ηZV).1 : V) = (ηV.1 : V) :=
    congrArg (fun ξ : genericPoints (V : Set Z) => (ξ.1 : V))
      (Equiv.apply_symm_apply (Scheme.genericPointsInOpenEquiv Z V) ηV)
  let ηZ : genericPoints Z := ηZV.1
  have hηX : f ηZ.1 ∈ genericPoints X := hgeneric ηZ
  have hηU : (f ηZ.1 : X) ∈ U := hVU ηZV.2
  let ηXU : {η : genericPoints X // η.1 ∈ U} := ⟨⟨f ηZ.1, hηX⟩, hηU⟩
  let p : minimalPrimes Γ(X, U) := genericPointsInOpenEquivMinimalPrimes hU ηXU
  have hq' : (q : Ideal Γ(Z, V)) = (hV.primeIdealOf ⟨ηZ.1, ηZV.2⟩).asIdeal := by
    calc
      (q : Ideal Γ(Z, V)) =
          (genericPointsAffineOpenEquiv hV ηV : minimalPrimes Γ(Z, V)) :=
        (congrArg Subtype.val (Equiv.apply_symm_apply (genericPointsAffineOpenEquiv hV)
          (⟨q, hq⟩ : minimalPrimes Γ(Z, V)))).symm
      _ = (hV.isoSpec.hom ηV.1).asIdeal := genericPointsAffineOpenEquiv_asIdeal hV ηV
      _ = (hV.primeIdealOf ⟨ηZ.1, ηZV.2⟩).asIdeal := by
        simp only [IsAffineOpen.primeIdealOf]
        exact (congrArg (fun x : V => (hV.isoSpec.hom x).asIdeal) hηVsubtype).symm
  have hp' : (p : Ideal Γ(X, U)) = (hU.primeIdealOf ⟨f ηZ.1, hηU⟩).asIdeal := by
    simpa [p, ηXU, ηZ] using genericPointsInOpenEquivMinimalPrimes_asIdeal hU ηXU
  have hcomap : Ideal.comap (f.appLE U V hVU).hom
      (hV.primeIdealOf ⟨ηZ.1, ηZV.2⟩).asIdeal =
      (hU.primeIdealOf ⟨f ηZ.1, hηU⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU ηZV.2)
  rw [hq', hcomap]
  exact hp'.symm ▸ p.property

/-- The lift of an affine normal scheme into the normalization over an affine open, built from
the ring-level lift of `IsNormalRing.liftIntegralClosureFractionRing` through the affine
description of the normalization over an affine open. -/
private noncomputable def affineLiftToNormalization {X V : Scheme.{u}} [IsReduced X]
    [IsAffine V] [IsNormal V]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) (φ : Γ(X, U) →+* Γ(V, ⊤))
    (hmap : ∀ q ∈ minimalPrimes Γ(V, ⊤), Ideal.comap φ q ∈ minimalPrimes Γ(X, U)) :
    V ⟶ X.normalizationScheme hX := by
  letI : IsAffine U := hU
  let lift := IsNormalRing.liftIntegralClosureFractionRing φ
    (map_mem_nonZeroDivisors_of_comap_minimalPrimes φ hmap) isNormalRing_sections_top
  let c : (X.normalization hX ⁻¹ᵁ U).toScheme ≅
      Spec (.of (integralClosure Γ(X, U) (FractionRing Γ(X, U)))) :=
    preimageNormalizationIsoSpecIntegralClosure hX U hU.isoSpec.symm
  exact V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫ c.inv ≫
    (X.normalization hX ⁻¹ᵁ U).ι

/-- The affine-local lift lies over the given morphism. -/
private theorem affineLiftToNormalization_fac {X V : Scheme.{u}} [IsReduced X]
    [IsAffine V] [IsNormal V]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) (φ : Γ(X, U) →+* Γ(V, ⊤))
    (hmap : ∀ q ∈ minimalPrimes Γ(V, ⊤), Ideal.comap φ q ∈ minimalPrimes Γ(X, U)) :
    affineLiftToNormalization hX U hU φ hmap ≫ X.normalization hX =
      V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have : IsAffine U := hU
  let A := Γ(X, U)
  let lift := IsNormalRing.liftIntegralClosureFractionRing φ
    (map_mem_nonZeroDivisors_of_comap_minimalPrimes φ hmap) isNormalRing_sections_top
  let W := X.normalization hX ⁻¹ᵁ U
  let c : W.toScheme ≅ Spec (.of (integralClosure A (FractionRing A))) :=
    preimageNormalizationIsoSpecIntegralClosure hX U hU.isoSpec.symm
  have hc : c.inv ≫ (X.normalization hX ∣_ U) ≫ hU.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) := by
    have hchart := preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U hU.isoSpec.symm
    change c.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (integralClosure A (FractionRing A)))) =
      (X.normalization hX ∣_ U) ≫ hU.isoSpec.hom at hchart
    calc
      _ = c.inv ≫ c.hom ≫ Spec.map
          (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) := by
            rw [← hchart]
      _ = _ := by simp
  dsimp [affineLiftToNormalization, A, lift, W, c]
  simp only [Category.assoc]
  have hlocal : V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫ c.inv ≫
      (X.normalization hX ∣_ U) =
        V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv := by
    apply (cancel_mono hU.isoSpec.hom).1
    calc
      _ = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫
          (c.inv ≫ (X.normalization hX ∣_ U) ≫ hU.isoSpec.hom) := by
            simp only [Category.assoc]
      _ = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap A (integralClosure A (FractionRing A)))) := by rw [hc]
      _ = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
              IsNormalRing.liftIntegralClosureFractionRing_comp_algebraMap]
      _ = (V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv) ≫
          hU.isoSpec.hom := by simp
  rw [← morphismRestrict_ι]
  calc
    _ = (V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫ c.inv ≫
        (X.normalization hX ∣_ U)) ≫ U.ι := by rfl
    _ = (V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv) ≫ U.ι :=
          congrArg (fun k : V ⟶ U.toScheme => k ≫ U.ι) hlocal
    _ = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
          simp [Category.assoc]

/-- The affine-local lift is the only lift. -/
private theorem affineLift_unique {X V : Scheme.{u}} [IsReduced X] [IsAffine V] [IsNormal V]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) (f : V ⟶ X) (hfU : ∀ x : V, f x ∈ U)
    (φ : Γ(X, U) →+* Γ(V, ⊤))
    (hφ : V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec = f)
    (hmap : ∀ q ∈ minimalPrimes Γ(V, ⊤), Ideal.comap φ q ∈ minimalPrimes Γ(X, U))
    (g : V ⟶ X.normalizationScheme hX) (hg : g ≫ X.normalization hX = f) :
    g = affineLiftToNormalization hX U hU φ hmap := by
  classical
  let A := Γ(X, U)
  let B := Γ(V, ⊤)
  let W := X.normalization hX ⁻¹ᵁ U
  let c : W.toScheme ≅ Spec (.of (integralClosure A (FractionRing A))) :=
    preimageNormalizationIsoSpecIntegralClosure hX U hU.isoSpec.symm
  let lift := IsNormalRing.liftIntegralClosureFractionRing φ
    (map_mem_nonZeroDivisors_of_comap_minimalPrimes φ hmap) isNormalRing_sections_top
  have hchart : c.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) =
      (X.normalization hX ∣_ U) ≫ hU.isoSpec.hom :=
    preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U hU.isoSpec.symm
  have hrange : Set.range g.base ⊆ (W : Set (X.normalizationScheme hX)) := by
    rintro y ⟨x, rfl⟩
    change (X.normalization hX) (g x) ∈ U
    rw [← Scheme.Hom.comp_apply, hg]
    exact hfU x
  have hrange' : Set.range g.base ⊆ Set.range W.ι := by
    simpa only [Scheme.Opens.range_ι] using hrange
  let gW := IsOpenImmersion.lift W.ι g hrange'
  have hgW : gW ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ _
  let m : Spec (.of B) ⟶ Spec (.of (integralClosure A (FractionRing A))) :=
    V.isoSpec.inv ≫ gW ≫ c.hom
  have hchart' : c.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) ≫
      hU.fromSpec = W.ι ≫ X.normalization hX := by
    rw [← Category.assoc, hchart]
    simp only [Category.assoc, hU.isoSpec_hom_fromSpec]
    exact morphismRestrict_ι (X.normalization hX) U
  have hspec : m ≫ Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) =
      Spec.map (CommRingCat.ofHom φ) := by
    apply (cancel_mono hU.fromSpec).1
    calc
      _ = V.isoSpec.inv ≫ gW ≫
          (c.hom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap A (integralClosure A (FractionRing A)))) ≫ hU.fromSpec) := by
              simp only [m, Category.assoc]
      _ = V.isoSpec.inv ≫ gW ≫ W.ι ≫ X.normalization hX := by
        simpa only [Category.assoc] using
          congrArg (fun k => V.isoSpec.inv ≫ gW ≫ k) hchart'
      _ = V.isoSpec.inv ≫ f := by rw [← Category.assoc gW, hgW, hg]
      _ = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
        rw [← hφ]; simp
      _ = _ := rfl
  let ψ : CommRingCat.of (integralClosure A (FractionRing A)) ⟶ CommRingCat.of B :=
    Spec.homEquiv m
  have hψAcat : CommRingCat.ofHom
      (ψ.hom.comp (algebraMap A (integralClosure A (FractionRing A)))) =
      CommRingCat.ofHom φ := by
    apply (Spec.map_injective).eq_iff.mp
    calc
      Spec.map (CommRingCat.ofHom
          (ψ.hom.comp (algebraMap A (integralClosure A (FractionRing A))))) =
          Spec.map ψ ≫ Spec.map
            (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) := by
              rw [← Spec.map_comp]; rfl
      _ = m ≫ Spec.map
          (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) := by
            simp [ψ]
      _ = Spec.map (CommRingCat.ofHom φ) := hspec
  have hψA : ψ.hom.comp (algebraMap A (integralClosure A (FractionRing A))) = φ :=
    congrArg CommRingCat.Hom.hom hψAcat
  have hψ := IsNormalRing.liftIntegralClosureFractionRing_unique φ
    (map_mem_nonZeroDivisors_of_comap_minimalPrimes φ hmap) isNormalRing_sections_top
    ψ.hom hψA
  have hm : m = Spec.map (CommRingCat.ofHom lift) := by
    apply Spec.homEquiv.injective
    simpa [ψ, lift] using congrArg CommRingCat.ofHom hψ
  calc
    g = gW ≫ W.ι := hgW.symm
    _ = V.isoSpec.hom ≫ m ≫ c.inv ≫ W.ι := by simp [m]
    _ = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift) ≫ c.inv ≫ W.ι := by rw [hm]

/-! ### Gluing the affine-local lifts -/

/-- The index set of the cover of the source by affine opens mapping into affine opens of the
target. -/
private def normalizationLiftIndex {X Z : Scheme.{u}} (f : Z ⟶ X) :=
  {p : X.Opens × Z.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ f ⁻¹ᵁ p.1}

/-- The cover of the source indexed by `normalizationLiftIndex`. -/
private noncomputable def normalizationLiftCover {X Z : Scheme.{u}} (f : Z ⟶ X) : Z.OpenCover :=
  Z.openCoverOfIsOpenCover (fun i : normalizationLiftIndex f => i.1.2) (by
    apply TopologicalSpace.IsOpenCover.mk
    ext z
    constructor
    · intro _
      trivial
    · intro _
      simp only [Opens.mem_iSup, SetLike.mem_coe]
      obtain ⟨_, ⟨U, hU, rfl⟩, hfzU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
      obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
        Z.isBasis_affineOpens.exists_subset_of_mem_open hfzU (f ⁻¹ᵁ U).2
      exact ⟨⟨(U, V), hU, hV, hVU⟩, hzV⟩)

/-- The chart ring map of one member of the cover. -/
private noncomputable def normalizationLiftChartHom {X Z : Scheme.{u}} (f : Z ⟶ X)
    (i : normalizationLiftIndex f) : Γ(X, i.1.1) →+* Γ(i.1.2.toScheme, ⊤) :=
  i.1.2.topIso.inv.hom.comp (f.appLE i.1.1 i.1.2 i.2.2.2).hom

/-- The generic-point hypothesis read on one member of the cover. -/
private theorem normalizationLiftChartHom_comap_minimalPrimes {X Z : Scheme.{u}} (f : Z ⟶ X)
    (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X)
    (i : normalizationLiftIndex f) :
    ∀ q ∈ minimalPrimes Γ(i.1.2.toScheme, ⊤),
      Ideal.comap (normalizationLiftChartHom f i) q ∈ minimalPrimes Γ(X, i.1.1) := by
  intro q hq
  let V : Z.Opens := i.1.2
  let q' : Ideal Γ(Z, V) := Ideal.comap V.topIso.inv.hom q
  have hq' : q' ∈ minimalPrimes Γ(Z, V) := by
    have hbij : Function.Bijective V.topIso.inv.hom :=
      ConcreteCategory.bijective_of_isIso V.topIso.inv
    have hker : (⊥ : Ideal Γ(V, ⊤)).comap V.topIso.inv.hom = ⊥ := by
      change RingHom.ker V.topIso.inv.hom = ⊥
      exact (RingHom.injective_iff_ker_eq_bot _).mp hbij.1
    have hq'' := Ideal.minimalPrimes_comap_of_surjective
      (f := V.topIso.inv.hom) hbij.2 (by simpa using hq)
    change (⊥ : Ideal Γ(Z, V)).IsMinimalPrime (Ideal.comap V.topIso.inv.hom q)
    rw [← hker]
    exact hq''
  have hr := comap_mem_minimalPrimes_appLE f i.1.1 V i.2.1 i.2.2.1 i.2.2.2 hgeneric q' hq'
  dsimp [normalizationLiftChartHom]
  rw [← Ideal.comap_comap]
  simpa [q'] using hr

/-- The affine-local lift on one member of the cover. -/
private noncomputable def normalizationLiftOnIndex {X Z : Scheme.{u}} [IsReduced X] [IsNormal Z]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X)
    (i : normalizationLiftIndex f) : (i.1.2).toScheme ⟶ X.normalizationScheme hX :=
  letI : IsAffine i.1.2.toScheme := i.2.2.1
  letI : IsNormal i.1.2.toScheme := isNormal_open i.1.2
  affineLiftToNormalization hX i.1.1 i.2.1 (normalizationLiftChartHom f i)
    (normalizationLiftChartHom_comap_minimalPrimes f hgeneric i)

/-- The local lift lies over the given morphism. -/
private theorem normalizationLiftOnIndex_fac {X Z : Scheme.{u}} [IsReduced X] [IsNormal Z]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X)
    (i : normalizationLiftIndex f) :
    normalizationLiftOnIndex hX f hgeneric i ≫ X.normalization hX = (i.1.2).ι ≫ f := by
  let U : X.Opens := i.1.1
  let V : Z.Opens := i.1.2
  have hU : IsAffineOpen U := i.2.1
  have hV : IsAffineOpen V := i.2.2.1
  have hVU : V ≤ f ⁻¹ᵁ U := i.2.2.2
  let  : IsAffine V.toScheme := hV
  let  : IsNormal V.toScheme := isNormal_open V
  let φ : Γ(X, U) →+* Γ(V, ⊤) := normalizationLiftChartHom f i
  have hchartV : V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom V.topIso.inv.hom) =
      hV.isoSpec.hom := by
    simp only [Scheme.isoSpec, asIso_hom, IsAffineOpen.isoSpec, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom]
    rfl
  have hφ : V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      V.ι ≫ f := by
    have hmapφ : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom V.topIso.inv.hom) ≫
          Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom) := by
      change Spec.map (CommRingCat.ofHom
          (V.topIso.inv.hom.comp (f.appLE U V hVU).hom)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hmapφ' : V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) =
        V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom V.topIso.inv.hom) ≫
          Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom) :=
      congrArg (fun k => V.toScheme.isoSpec.hom ≫ k) hmapφ
    calc
      _ = (V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom V.topIso.inv.hom)) ≫
          Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom) ≫ hU.fromSpec := by
            simpa only [Category.assoc] using congrArg (fun k => k ≫ hU.fromSpec) hmapφ'
      _ = hV.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom) ≫ hU.fromSpec := by
            rw [hchartV]
      _ = hV.isoSpec.hom ≫ (hV.fromSpec ≫ f) := by
            simpa only [CommRingCat.ofHom_hom, Category.assoc] using
              congrArg (fun k => hV.isoSpec.hom ≫ k)
                (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU)
      _ = V.ι ≫ f := by simp
  calc
    normalizationLiftOnIndex hX f hgeneric i ≫ X.normalization hX
        = V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec :=
      affineLiftToNormalization_fac hX U hU φ
        (normalizationLiftChartHom_comap_minimalPrimes f hgeneric i)
    _ = V.ι ≫ f := hφ

/-- The local lift on one member of the cover is the only lift there. -/
private theorem normalizationLiftOnIndex_unique {X Z : Scheme.{u}} [IsReduced X] [IsNormal Z]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X)
    (i : normalizationLiftIndex f) (g : i.1.2.toScheme ⟶ X.normalizationScheme hX)
    (hg : g ≫ X.normalization hX = i.1.2.ι ≫ f) :
    g = normalizationLiftOnIndex hX f hgeneric i := by
  let  : IsAffine i.1.2.toScheme := i.2.2.1
  let  : IsNormal i.1.2.toScheme := isNormal_open i.1.2
  exact affineLift_unique hX i.1.1 i.2.1 (i.1.2.ι ≫ f) (fun x ↦ i.2.2.2 x.2)
    (normalizationLiftChartHom f i)
    ((affineLiftToNormalization_fac hX i.1.1 i.2.1 (normalizationLiftChartHom f i)
      (normalizationLiftChartHom_comap_minimalPrimes f hgeneric i)).symm.trans
        (normalizationLiftOnIndex_fac hX f hgeneric i))
    (normalizationLiftChartHom_comap_minimalPrimes f hgeneric i) g hg

/-- Uniqueness of a lift to the normalization, for a reduced target. -/
private theorem normalization_lift_unique_of_isReduced {X Z : Scheme.{u}} [IsReduced X]
    [IsNormal Z]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X)
    (g₁ g₂ : Z ⟶ X.normalizationScheme hX)
    (h₁ : g₁ ≫ X.normalization hX = f) (h₂ : g₂ ≫ X.normalization hX = f) : g₁ = g₂ := by
  apply (normalizationLiftCover f).hom_ext
  intro i
  exact (normalizationLiftOnIndex_unique hX f hgeneric i (i.1.2.ι ≫ g₁)
    (by simp [Category.assoc, h₁])).trans
      (normalizationLiftOnIndex_unique hX f hgeneric i (i.1.2.ι ≫ g₂)
        (by simp [Category.assoc, h₂])).symm

/-- The universal property of the normalization, for a reduced target. -/
private theorem existsUnique_lift_normalization_of_isReduced {X Z : Scheme.{u}} [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) [IsNormal Z]
    (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X) :
    ∃! g : Z ⟶ X.normalizationScheme hX, g ≫ X.normalization hX = f := by
  let 𝒰 := normalizationLiftCover f
  let g := normalizationLiftOnIndex hX f hgeneric
  have hg (i : 𝒰.I₀) : g i ≫ X.normalization hX = 𝒰.f i ≫ f :=
    normalizationLiftOnIndex_fac hX f hgeneric i
  have hglue (i j : 𝒰.I₀) :
      Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    let a := Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have : IsNormal (Limits.pullback (𝒰.f i) (𝒰.f j)) := isNormal_of_isOpenImmersion a
    apply normalization_lift_unique_of_isReduced hX (a ≫ f)
    · intro η
      exact hgeneric ⟨a η.1,
        mem_genericPoints_of_generalizingMap a.isOpenEmbedding.generalizingMap η.2⟩
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ k) (hg i)).trans
          (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ k) (hg j)).trans
          (Limits.pullback.condition_assoc f).symm)
  have hfac : 𝒰.glueMorphisms g hglue ≫ X.normalization hX = f := by
    apply 𝒰.hom_ext
    intro i
    rw [← Category.assoc, 𝒰.ι_glueMorphisms g hglue i]
    exact hg i
  exact ⟨_, hfac, fun g' hg' ↦ normalization_lift_unique_of_isReduced hX f hgeneric _ _ hg' hfac⟩

/-! ### Normalization of the reduction -/

/-- A morphism whose underlying map is a homeomorphism with isomorphisms on all residue fields
induces an isomorphism of generic-point residue spectra over it. -/
private theorem exists_genericPointResidueSpectrum_iso {X X' : Scheme.{u}} (α : X' ⟶ X)
    (e : X' ≃ₜ X) (he : ∀ x, α x = e x) (hres : ∀ x, IsIso (α.residueFieldMap x)) :
    ∃ E : Scheme.genericPointResidueSpectrum X' ≅ Scheme.genericPointResidueSpectrum X,
      E.hom ≫ Scheme.fromGenericPointResidueFields X =
        Scheme.fromGenericPointResidueFields X' ≫ α := by
  classical
  let pointMap : genericPoints X' → genericPoints X := fun ξ =>
    ⟨e ξ.1, mem_genericPoints_of_generalizingMap e.isOpenEmbedding.generalizingMap ξ.2⟩
  have pointMap_bijective : Function.Bijective pointMap := by
    constructor
    · intro ξ ζ h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro η
      refine ⟨⟨e.symm η.1,
        mem_genericPoints_of_generalizingMap e.symm.isOpenEmbedding.generalizingMap η.2⟩, ?_⟩
      exact Subtype.ext (e.apply_symm_apply η.1)
  let pointsEquiv : genericPoints X' ≃ genericPoints X :=
    Equiv.ofBijective pointMap pointMap_bijective
  let sourceFamily := fun ξ : genericPoints X' => Spec (.of (X'.residueField ξ.1))
  let targetFamily := fun η : genericPoints X => Spec (.of (X.residueField η.1))
  let reindex : Discrete (genericPoints X') ⥤ Discrete (genericPoints X) :=
    (Discrete.equivalence pointsEquiv).functor
  let reindexPointVal (ξ : genericPoints X') : genericPoints X :=
    (reindex.obj (Discrete.mk ξ)).as
  have pointMap_reindex (ξ : genericPoints X') : α ξ.1 = (reindexPointVal ξ).1 := he ξ.1
  let residueIso (ξ : genericPoints X') :
      X.residueField (reindexPointVal ξ).1 ≅ X'.residueField ξ.1 := by
    letI : IsIso (α.residueFieldMap ξ.1) := hres ξ.1
    exact (X.residueFieldCongr (pointMap_reindex ξ)).symm ≪≫ asIso (α.residueFieldMap ξ.1)
  let targetReindexed := fun ξ : genericPoints X' => targetFamily (reindexPointVal ξ)
  let targetDiagram := Discrete.functor targetFamily
  let targetReindexedDiagram := Discrete.functor targetReindexed
  let reindexNatIso : targetReindexedDiagram ≅ reindex ⋙ targetDiagram :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  let componentIso (ξ : genericPoints X') : sourceFamily ξ ≅ targetReindexed ξ :=
    Scheme.Spec.mapIso (residueIso ξ).op
  let eComponents := Limits.Sigma.mapIso componentIso
  let eReindexCoproduct := Limits.HasColimit.isoOfNatIso reindexNatIso
  let eReindex := Functor.Final.colimitIso reindex targetDiagram
  let E : Scheme.genericPointResidueSpectrum X' ≅ Scheme.genericPointResidueSpectrum X := by
    change (∐ sourceFamily) ≅ (∐ targetFamily)
    exact eComponents ≪≫ eReindexCoproduct ≪≫ eReindex
  have residueIso_fromSpec (ξ : genericPoints X') :
      Spec.map (residueIso ξ).hom ≫ X.fromSpecResidueField (reindexPointVal ξ).1 =
      Spec.map (α.residueFieldMap ξ.1) ≫ X.fromSpecResidueField (α ξ.1) := by
    dsimp [residueIso]
    rw [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField (pointMap_reindex ξ).symm]
  have hcomm : E.hom ≫ Scheme.fromGenericPointResidueFields X =
      Scheme.fromGenericPointResidueFields X' ≫ α := by
    let cover : (∐ sourceFamily).OpenCover :=
      Scheme.Cover.copy
        (Scheme.IsLocallyDirected.openCover (Discrete.functor sourceFamily))
        (genericPoints X') sourceFamily (Limits.Sigma.ι sourceFamily)
        discreteEquiv.symm (fun _ => Iso.refl _) (by intro ξ; rfl)
    apply Scheme.Cover.hom_ext cover
    intro ξ
    dsimp only [cover] at ξ
    change genericPoints X' at ξ
    change Limits.Sigma.ι sourceFamily ξ ≫ E.hom ≫
        Scheme.fromGenericPointResidueFields X =
      Limits.Sigma.ι sourceFamily ξ ≫ Scheme.fromGenericPointResidueFields X' ≫ α
    dsimp [E, eComponents, Scheme.genericPointResidueSpectrum,
      Scheme.fromGenericPointResidueFields]
    simp only [Category.assoc]
    rw [Limits.Sigma.ι_mapIso_hom_assoc componentIso ξ
      (eReindexCoproduct.hom ≫ eReindex.hom ≫
        Limits.Sigma.desc (fun η : genericPoints X => X.fromSpecResidueField η.1))]
    rw [Limits.HasColimit.isoOfNatIso_ι_hom_assoc reindexNatIso (Discrete.mk ξ)
      (eReindex.hom ≫
        Limits.Sigma.desc (fun η : genericPoints X => X.fromSpecResidueField η.1))]
    rw [Functor.Final.ι_colimitIso_hom_assoc reindex targetDiagram (Discrete.mk ξ)
      (Limits.Sigma.desc (fun η : genericPoints X => X.fromSpecResidueField η.1))]
    have hreindex : reindexNatIso.hom.app (Discrete.mk ξ) = 𝟙 _ := by
      dsimp [reindexNatIso]
      rfl
    rw [hreindex, Category.id_comp, Limits.Sigma.ι_desc_assoc]
    simp only [componentIso, Functor.mapIso_hom, Scheme.Spec_map, Iso.op_hom, Opposite.unop_op]
    dsimp [targetDiagram]
    rw [Limits.Sigma.ι_desc, residueIso_fromSpec]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField α ξ.1
  exact ⟨E, hcomm⟩

/-- The closed immersion of the reduction of a scheme is a homeomorphism. -/
private theorem exists_homeomorph_nilradical_subschemeι (X : Scheme.{u}) :
    ∃ e : X.nilradical.subscheme ≃ₜ X, ∀ x, X.nilradical.subschemeι x = e x :=
  have hsurj : Function.Surjective X.nilradical.subschemeι := fun x ↦
    Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  ⟨X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj,
    fun _ ↦ rfl⟩

namespace Scheme

/-- **Stacks Project, Tag 035O.** The normalization of `X` is canonically the normalization of
the reduction of `X`: there is an isomorphism of normalizations over `X`. -/
theorem exists_normalizationScheme_iso_reduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ e : X.normalizationScheme hX ≅
        X.nilradical.subscheme.normalizationScheme (X.finite_irreducibleComponents_reduction hX),
      e.hom ≫ X.nilradical.subscheme.normalization
          (X.finite_irreducibleComponents_reduction hX) ≫ X.nilradical.subschemeι =
        X.normalization hX := by
  classical
  let I := X.nilradical
  let α := I.subschemeι
  obtain ⟨eX, heX⟩ := exists_homeomorph_nilradical_subschemeι X
  have hres (x : I.subscheme) : IsIso (α.residueFieldMap x) :=
    isIso_residueFieldMap_of_stalkMap_surjective α x (α.stalkMap_surjective x)
  obtain ⟨E, hE⟩ := exists_genericPointResidueSpectrum_iso α eX heX hres
  let hred := X.finite_irreducibleComponents_reduction hX
  let f := Scheme.fromGenericPointResidueFields X
  let f' := Scheme.fromGenericPointResidueFields I.subscheme
  have : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  have : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have : QuasiCompact f' :=
    Scheme.quasiCompactFromGenericPointResidueFields I.subscheme hred
  have : QuasiSeparated f' := Scheme.quasiSeparatedFromGenericPointResidueFields I.subscheme
  let g₀ : Scheme.genericPointResidueSpectrum X ⟶ I.subscheme := E.inv ≫ f'
  have hfactor : f = g₀ ≫ α := by
    calc
      f = E.inv ≫ (E.hom ≫ f) := by simp
      _ = E.inv ≫ (f' ≫ α) := by rw [hE]
      _ = g₀ ≫ α := by simp [g₀, Category.assoc]
  let g := f.normalizationDesc g₀ α hfactor
  have hgComp : g ≫ α = f.fromNormalization := f.normalizationDesc_comp g₀ α hfactor
  have hi : E.hom ≫ f.toNormalization ≫ g = f' := by
    rw [f.toNormalization_normalizationDesc g₀ α hfactor]
    dsimp [g₀]
    simp
  have hUP : ∀ (T : Scheme.{u}) (j : Scheme.genericPointResidueSpectrum I.subscheme ⟶ T)
      (q : T ⟶ I.subscheme), IsIntegralHom q → j ≫ q = f' →
        ∃! k : X.normalizationScheme hX ⟶ T,
          (E.hom ≫ f.toNormalization) ≫ k = j ∧ k ≫ q = g := by
    intro T j q hq hj
    let j₀ : Scheme.genericPointResidueSpectrum X ⟶ T := E.inv ≫ j
    have hj₀ : j₀ ≫ q = g₀ := by
      dsimp [j₀, g₀]
      rw [Category.assoc, hj]
    obtain ⟨k, hk, hku⟩ :=
      Scheme.Hom.normalizationDesc_universalProperty f g₀ α hfactor T j₀ q hq hj₀
    refine ⟨k, ⟨?_, hk.2⟩, ?_⟩
    · dsimp [j₀] at hk
      calc
        (E.hom ≫ f.toNormalization) ≫ k = E.hom ≫ j₀ := by
          calc
            (E.hom ≫ f.toNormalization) ≫ k =
                E.hom ≫ (f.toNormalization ≫ k) := by simp [Category.assoc]
            _ = E.hom ≫ j₀ := congrArg (fun t => E.hom ≫ t) hk.1
        _ = j := by simpa only [j₀] using Iso.hom_inv_id_assoc E j
    · intro k' hk'
      apply hku k'
      constructor
      · calc
          f.toNormalization ≫ k' = E.inv ≫ ((E.hom ≫ f.toNormalization) ≫ k') := by
            simp [Category.assoc]
          _ = E.inv ≫ j := congrArg (fun t => E.inv ≫ t) hk'.1
          _ = j₀ := rfl
      · exact hk'.2
  obtain ⟨e, he, -⟩ :=
    (Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso f'
      (E.hom ≫ f.toNormalization) g hi).1 hUP
  refine ⟨e, ?_⟩
  change (e.hom ≫ f'.fromNormalization) ≫ α = f.fromNormalization
  rw [he.2]
  exact hgComp

/-- **Stacks Project, Tag 035Q part (4).** A morphism to `X` from a normal scheme each of whose
irreducible components dominates an irreducible component of `X` factors uniquely through the
normalization of `X`. -/
@[stacks 035Q "normalization_universal_property",
  ega "II 6.3.9" "special case",
  ega "IV 8.12.11" "special case"]
theorem existsUnique_lift_normalization {X Z : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (f : Z ⟶ X) [IsNormal Z]
    (hgeneric : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X) :
    ∃! g : Z ⟶ X.normalizationScheme hX, g ≫ X.normalization hX = f := by
  let α := X.nilradical.subschemeι
  obtain ⟨eX, heX⟩ := exists_homeomorph_nilradical_subschemeι X
  obtain ⟨f', hf', -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι f
  have hf'generic :
      ∀ η : genericPoints Z, f' η.1 ∈ genericPoints X.nilradical.subscheme := by
    intro η
    have heX' : eX.symm (f η.1) = f' η.1 := by
      apply eX.injective
      rw [eX.apply_symm_apply, ← heX, ← Scheme.Hom.comp_apply, hf']
    rw [← heX']
    exact mem_genericPoints_of_generalizingMap
      eX.symm.isOpenEmbedding.generalizingMap (hgeneric η)
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  obtain ⟨g, hg, huniq⟩ := existsUnique_lift_normalization_of_isReduced
    (X.finite_irreducibleComponents_reduction hX) f' hf'generic
  refine ⟨g ≫ e.inv, ?_, ?_⟩
  · rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hg, hf']
  · intro g' hg'
    have hcomp : (g' ≫ e.hom) ≫ X.nilradical.subscheme.normalization
        (X.finite_irreducibleComponents_reduction hX) = f' := by
      apply (cancel_mono α).1
      simpa only [α, Category.assoc, he, hf'] using hg'
    calc
      g' = (g' ≫ e.hom) ≫ e.inv := by simp
      _ = g ≫ e.inv := by rw [huniq (g' ≫ e.hom) hcomp]

end Scheme

end AlgebraicGeometry

end
