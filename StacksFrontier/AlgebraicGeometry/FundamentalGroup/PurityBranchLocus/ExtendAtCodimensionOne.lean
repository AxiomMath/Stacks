module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.IntegralClosure.Pi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a cover unramified in codimension one over a codimension-one point

Let `X` be a locally Noetherian scheme, `U ⊆ X` a dense open and `f : Y ⟶ U` finite étale and
unramified over `X` in codimension one. At a point `x ∉ U` whose local ring `𝒪_{X, x}` is regular
of dimension one, the restriction of `Y` to the preimage of `U` in `Spec 𝒪_{X, x}` extends to a
finite étale cover of `Spec 𝒪_{X, x}`. This is the first stage of the proof of
[Stacks, Tag 0H2W].

## Main results

* `IsDiscreteValuationRing.etale_integralClosure_of_isUnramifiedWithRespectTo`: the integral
  closure of a discrete valuation ring in a finite separable extension of its fraction field
  which is unramified with respect to it is finite étale over it.
* `IsDiscreteValuationRing.module_finite_and_etale_integralClosure_of_forall_fieldFactor`: the
  same for a finite étale algebra over the fraction field all of whose field factors are
  unramified.
* `AlgebraicGeometry.exists_finiteEtale_extension_of_forall_fieldFactor`: a finite étale cover
  of the generic point of a discrete valuation ring all of whose field factors are unramified
  extends over the whole spectrum.
* `AlgebraicGeometry.exists_finiteEtale_extension_stalk_of_isUnramifiedInCodimensionOne`: the
  extension at a codimension-one point of the boundary.

## Implementation notes

The local ring `A = 𝒪_{X, x}` is a discrete valuation ring ([Stacks, Tag 00PD]), so `Spec A`
has two points. With `π` a uniformizer, the preimage of `U` in `Spec A` is the basic open `D(π)`:
the closed point maps to `x ∉ U`, while the generic point of an irreducible component of `X`
through `x` lies in the dense open `U` (a dense open of a locally Noetherian scheme contains all
generic points of irreducible components) and is the image of a point of `Spec A`, necessarily
the generic point. So the preimage is identified with `Spec K` for `K` the fraction field of `A`,
which is `A[1/π]`, and the restricted cover with a finite étale `K`-algebra `C`. A field factor
`C → L` gives a preimmersion `Spec L ⟶ Y`, and a preimmersion from the spectrum of a field
identifies that field with the residue field of its image point
(`AlgebraicGeometry.exists_ringEquiv_residueField_of_isPreimmersion`); this is exactly the
presentation of a field factor in `Stacks.FundamentalGroup.IsFieldFactorAt`, at the prime divisor
with generic point `x` (`Stacks.Divisors.PrimeDivisor.ofCoheightOne`). The hypothesis then says
each factor is unramified over `A`, so the integral closure of `A` in each factor is finite étale
over `A`; the integral closure `B` of `A` in `C` is the product of those, and `C` is its generic
fibre, being a localization of `B`. The cover is `Spec B`.

## References

* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Definition 09E9](https://stacks.math.columbia.edu/tag/09E9)
* [Stacks Project, Lemma 00PD](https://stacks.math.columbia.edu/tag/00PD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace IsDiscreteValuationRing

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The integral closure of a discrete valuation ring in an unramified extension is finite
étale.** Let `A` be a discrete valuation ring with fraction field `K` and `L / K` a finite
separable extension, unramified with respect to `A`. The integral closure `B` of `A` in `L` is
finite over `A` and torsion-free, hence flat; at each maximal ideal of `B` the ramification index
is one and the residue field extension is separable, so `B` is formally unramified. -/
@[ega "IV 18.10.10" "special case"]
theorem etale_integralClosure_of_isUnramifiedWithRespectTo
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra A L] [IsScalarTower A K L]
    (h : IsUnramifiedWithRespectTo A K L) :
    Module.Finite A (integralClosure A L) ∧ Algebra.Etale A (integralClosure A L) := by
  let B := integralClosure A L
  let p := IsLocalRing.maximalIdeal A
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val hxy)
  have hloc : ∀ (S : Type u) [CommRing S] [Algebra A S],
      (∀ (m : Ideal S) [m.IsMaximal], Algebra.IsUnramifiedAt A m) →
        Algebra.FormallyUnramified A S := by
    intro S _ _ hS
    rw [Algebra.formallyUnramified_iff]
    apply subsingleton_of_forall_eq 0
    intro y
    apply Module.eq_zero_of_localization_maximal
      (fun m _ => KaehlerDifferential A (Localization.AtPrime m))
      (fun m _ => KaehlerDifferential.map A A S (Localization.AtPrime m)) y
    intro m hm
    have := hS m
    exact Subsingleton.elim _ _
  have hfu : Algebra.FormallyUnramified A B := by
    refine hloc B fun m hm => ?_
    have hmp : m.LiesOver p := ⟨(IsLocalRing.eq_maximalIdeal ((hm.under A))).symm⟩
    let := Localization.AtPrime.algebraOfLiesOver p m
    obtain ⟨he, hs⟩ := h m hm hmp
    have := hs
    apply (Algebra.isUnramifiedAt_iff_map_eq A p m).mpr
    refine ⟨inferInstance, ?_⟩
    apply (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff ?_ ?_).mp he
    · intro hm0
      have hp0 : p = ⊥ := by simpa [hm0, Ideal.under_bot] using (m.over_def p)
      exact IsDiscreteValuationRing.not_a_field A hp0
    · exact Ideal.map_le_of_le_comap (m.over_def p).le
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, Algebra.Etale.of_formallyUnramified_of_flat⟩

/-- **The integral closure of a discrete valuation ring in a finite étale algebra over its
fraction field with unramified field factors is finite étale.** The algebra `C` is a finite
product of finite separable field extensions `L_i` of `K`, each a quotient of `C`; the integral
closure of `A` in `C` is the product of the integral closures of `A` in the `L_i`, each finite
étale over `A` by `etale_integralClosure_of_isUnramifiedWithRespectTo`. -/
theorem module_finite_and_etale_integralClosure_of_forall_fieldFactor
    (C : Type u) [CommRing C] [Algebra K C] [Algebra A C] [IsScalarTower A K C]
    [Algebra.Etale K C]
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra.IsSeparable K L] [Algebra A L] [IsScalarTower A K L],
      (∃ ψ : C →ₐ[K] L, Function.Surjective ψ) → IsUnramifiedWithRespectTo A K L) :
    Module.Finite A (integralClosure A C) ∧ Algebra.Etale A (integralClosure A C) := by
  classical
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K C).mp inferInstance
  let (i : I) : Algebra A (Ai i) := ((algebraMap K (Ai i)).comp (algebraMap A K)).toAlgebra
  have (i : I) : IsScalarTower A K (Ai i) := IsScalarTower.of_algebraMap_eq' rfl
  have hB (i : I) : Module.Finite A (integralClosure A (Ai i)) ∧
      Algebra.Etale A (integralClosure A (Ai i)) := by
    obtain ⟨h1, h2⟩ := hAi i
    exact etale_integralClosure_of_isUnramifiedWithRespectTo A K (Ai i)
      (h (Ai i) ⟨(Pi.evalAlgHom K Ai i).comp e.toAlgHom,
        (Function.surjective_eval i).comp e.surjective⟩)
  have (i : I) : Module.Finite A (integralClosure A (Ai i)) := (hB i).1
  have (i : I) : Algebra.Etale A (integralClosure A (Ai i)) := (hB i).2
  let e' : C ≃ₐ[A] (Π i, Ai i) := e.restrictScalars A
  let eB : integralClosure A C ≃ₐ[A] Π i, integralClosure A (Ai i) :=
    (((integralClosure A C).equivMapOfInjective e'.toAlgHom e'.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e'))).trans
      (integralClosurePiEquiv A Ai)
  exact ⟨Module.Finite.equiv eB.symm.toLinearEquiv, Algebra.Etale.of_equiv eB.symm⟩

end IsDiscreteValuationRing

namespace AlgebraicGeometry

/-- **A preimmersion from the spectrum of a field is a residue-field point.** If
`v : Spec L ⟶ Y` is a preimmersion, the induced map from the residue field of `Y` at the image of
the point to `L` is surjective on stalks, hence an isomorphism, and `v` is the canonical morphism
from the spectrum of that residue field, up to this isomorphism. -/
theorem exists_ringEquiv_residueField_of_isPreimmersion {Y : Scheme.{u}} {L : Type u} [Field L]
    (v : Spec (.of L) ⟶ Y) [IsPreimmersion v] :
    ∃ e : Y.residueField (v (IsLocalRing.closedPoint L)) ≃+* L,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Y.fromSpecResidueField (v (IsLocalRing.closedPoint L)) = v := by
  let c := Y.descResidueField (Scheme.stalkClosedPointTo v)
  have hsurj : Function.Surjective c := by
    have hto : Function.Surjective (Scheme.stalkClosedPointTo v) :=
      (ConcreteCategory.bijective_of_isIso
        (stalkClosedPointIso (CommRingCat.of L)).hom).2.comp
        (v.stalkMap_surjective (IsLocalRing.closedPoint L))
    intro l
    obtain ⟨s, rfl⟩ := hto l
    exact ⟨Y.residue _ s,
      congrArg (fun φ => φ.hom s) (Y.residue_descResidueField (Scheme.stalkClosedPointTo v))⟩
  exact ⟨RingEquiv.ofBijective c.hom ⟨c.hom.injective, hsurj⟩,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L Y v⟩

/-- Base change of finite étale covers along an isomorphism reflects isomorphism of objects:
base changing back along the inverse recovers the original covers. -/
private lemma nonempty_iso_of_iso_finiteEtaleBaseChange_obj {S T : Scheme.{u}} (φ : S ≅ T)
    {P Q : FiniteEtaleOver T}
    (e : (finiteEtaleBaseChange φ.hom).obj P ≅ (finiteEtaleBaseChange φ.hom).obj Q) :
    Nonempty (P ≅ Q) := by
  let c := finiteEtaleBaseChangeComp φ.inv φ.hom (𝟙 T) (by simp)
  exact ⟨(finiteEtaleBaseChangeId.app P).symm ≪≫ c.app P ≪≫
    (finiteEtaleBaseChange φ.inv).mapIso e ≪≫ (c.app Q).symm ≪≫ finiteEtaleBaseChangeId.app Q⟩

/-- **A finite étale cover of the generic point of a discrete valuation ring with unramified
field factors extends over the spectrum.** Let `R` be a discrete valuation ring with fraction
field `K` and `V` a finite étale cover of `Spec K`. If for every finite separable extension
`L / K` and every preimmersion `Spec L ⟶ V` over `Spec K` the extension `L` is unramified with
respect to `R`, then `V` is the generic fibre of a finite étale cover of `Spec R`: the spectrum
of the integral closure of `R` in the algebra of global sections of `V`. -/
theorem exists_finiteEtale_extension_of_forall_fieldFactor
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (V : FiniteEtaleOver (Spec (.of K)))
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra.IsSeparable K L] [Algebra R L] [IsScalarTower R K L]
      (v : Spec (.of L) ⟶ V.left), IsPreimmersion v →
        v ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        IsDiscreteValuationRing.IsUnramifiedWithRespectTo R K L) :
    ∃ F : FiniteEtaleOver (Spec (.of R)),
      Nonempty ((finiteEtaleBaseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj F ≅ V) := by
  have : IsAffine V.left := isAffine_left_of_finiteEtaleOver_spec K V
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  let C := Γ(V.left, ⊤)
  let φ : CommRingCat.of K ⟶ CommRingCat.of C := Spec.preimage (V.left.isoSpec.inv ≫ V.hom)
  let : Algebra K C := φ.hom.toAlgebra
  have : Module.Finite K C := by
    rw [← RingHom.finite_algebraMap]
    apply (IsFinite.SpecMap_iff φ).mp
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.Etale K C := by
    rw [← RingHom.etale_algebraMap]
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    infer_instance
  let eV : V ≅ finiteEtaleOverSpec K C := MorphismProperty.Over.isoMk V.left.isoSpec (by
    show V.left.isoSpec.hom ≫ Spec.map φ = V.hom
    rw [Spec.map_preimage]
    simp)
  let : Algebra R C := ((algebraMap K C).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hfin, heta⟩ :=
    IsDiscreteValuationRing.module_finite_and_etale_integralClosure_of_forall_fieldFactor R K C
      (by
        intro L _ _ _ _ _ _ ⟨ψ, hψ⟩
        have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
          IsClosedImmersion.spec_of_surjective _ hψ
        refine h L (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ V.left.isoSpec.inv)
          inferInstance ?_
        rw [Category.assoc, ← Spec.map_preimage (V.left.isoSpec.inv ≫ V.hom), ← Spec.map_comp]
        congr 1
        ext k
        exact ψ.commutes k)
  have := hfin
  have := heta
  let B := integralClosure R C
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) C :=
    isLocalization_integralClosure_fractionField R K C
  have : Algebra.IsPushout R B K C :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K B C
  have : Algebra.IsPushout R K B C := Algebra.IsPushout.symm inferInstance
  let eB : K ⊗[R] B ≃ₐ[K] C := Algebra.IsPushout.equiv R K B C
  let eY : finiteEtaleOverSpec K (K ⊗[R] B) ≅ finiteEtaleOverSpec K C :=
    MorphismProperty.Over.isoMk (specIsoOfAlgEquiv K eB) (specIsoOfAlgEquiv_hom_comp K eB)
  exact ⟨finiteEtaleOverSpec R B, ⟨finiteEtaleOverSpec_baseChangeIso R B K ≪≫ eY ≪≫ eV.symm⟩⟩

/-- The fraction field of a discrete valuation ring is obtained by inverting a uniformizer:
every nonzero element is a unit times a power of it, so divides a power of it. -/
private lemma isLocalization_away_fractionRing_of_irreducible {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing R) := by
  have hle : Submonoid.powers ϖ ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have : IsLocalization (nonZeroDivisors R) (Localization.Away ϖ) :=
    IsLocalization.of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors R) hle
      (fun n hn => by
        obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
          (nonZeroDivisors.ne_zero hn) hϖ
        exact ⟨ϖ ^ k, (⟨k, rfl⟩ : ϖ ^ k ∈ Submonoid.powers ϖ), Units.mul_left_dvd.mpr dvd_rfl⟩)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers ϖ)
    (IsLocalization.algEquiv (nonZeroDivisors R) (Localization.Away ϖ) (FractionRing R))

/-- Some point of `Spec 𝒪_{X, x}` maps into a dense open `U` of a locally Noetherian scheme `X`:
the generic point of an irreducible component of `X` through `x` lies in `U`. -/
theorem exists_fromSpecStalk_mem_of_dense {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens}
    (hdense' : Dense (U : Set X)) (x : X) :
    ∃ q : Spec (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  have hξx : (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).specializes_iff_mem.mpr
      (hxC (subset_closure (Set.mem_singleton x)))
  have hξU : (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) ∈ U :=
    scheme_genericPoints_mem_dense_open X U.isOpen hdense'
      (genericPoints.ofComponent (α := X) ⟨C, hC⟩).2
  obtain ⟨q, hq⟩ : (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) ∈
      Set.range (X.fromSpecStalk x) := by
    rwa [Scheme.range_fromSpecStalk]
  exact ⟨q, by rwa [hq]⟩

/-- If `𝒪_{X, x}` is a discrete valuation ring with uniformizer `ϖ` and `x` lies outside a dense
open `U`, the preimage of `U` in `Spec 𝒪_{X, x}` is `Spec K` for `K = 𝒪_{X, x}[1/ϖ]`. -/
theorem exists_iso_preimage_fromSpecStalk_of_isLocalizationAway
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense' : Dense (U : Set X)) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hxU : x ∉ U) (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ)
    (K : Type u) [CommRing K] [Algebra (X.presheaf.stalk x) K] [IsLocalization.Away ϖ K] :
    ∃ φ : Spec (.of K) ≅ ((X.fromSpecStalk x) ⁻¹ᵁ U).toScheme,
      φ.hom ≫ ((X.fromSpecStalk x) ⁻¹ᵁ U).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) := by
  classical
  let g := X.fromSpecStalk x
  let W := g ⁻¹ᵁ U
  let a : Spec (.of K) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization (R := X.presheaf.stalk x) (S := K) ϖ
  have hprime : ∀ p : Spec (X.presheaf.stalk x),
      p.asIdeal = ⊥ ∨ p = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro p
    by_cases hp : p.asIdeal = ⊥
    · exact Or.inl hp
    · have := p.2
      exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        (_root_.IsPrime.to_maximal_ideal hp)))
  obtain ⟨q, hqU⟩ := exists_fromSpecStalk_mem_of_dense hdense' x
  have hgclosed : g (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x :=
    Scheme.fromSpecStalk_closedPoint
  have hq' : q.asIdeal = ⊥ :=
    (hprime q).resolve_right fun h => hxU (by rwa [← hgclosed, ← h])
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hW : ∀ p : Spec (X.presheaf.stalk x), p ∈ W ↔ ϖ ∉ p.asIdeal := by
    refine fun p => ⟨fun hp hϖp => ?_, fun hϖp => ?_⟩
    · rcases hprime p with h | h
      · rw [h] at hϖp
        exact hϖ.ne_zero ((Submodule.mem_bot _).mp hϖp)
      · exact hxU (by rwa [← hgclosed, ← h])
    · rcases hprime p with h | h
      · rw [show p = q from PrimeSpectrum.ext (h.trans hq'.symm)]
        exact hqU
      · exact absurd (h ▸ hϖm) hϖp
  have hrange : Set.range a.base = Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    ext p
    show p ∈ Set.range (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) K)) ↔ p ∈ W
    rw [PrimeSpectrum.localization_away_comap_range K ϖ, hW]
    rfl
  exact ⟨IsOpenImmersion.isoOfRangeEq a W.ι hrange,
    IsOpenImmersion.isoOfRangeEq_hom_fac a W.ι hrange⟩

/-- The extension at a codimension-one boundary point, once the local ring is known to be a
discrete valuation ring and its fraction field is presented as the localization at a
uniformizer. -/
private lemma exists_finiteEtale_extension_stalk_of_isLocalization
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense' : Dense (U : Set X))
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f] (x : X)
    [hdom : IsDomain (X.presheaf.stalk x)] [hdvr : IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hunr : ∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk x) K]
        [IsFractionRing (X.presheaf.stalk x) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk x) L]
        [IsScalarTower (X.presheaf.stalk x) K L],
        Stacks.FundamentalGroup.IsFieldFactorAt U.ι f x K L →
          IsDiscreteValuationRing.IsUnramifiedWithRespectTo (X.presheaf.stalk x) K L)
    (hxU : x ∉ U) (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ)
    (K : Type u) [Field K] [Algebra (X.presheaf.stalk x) K] [IsFractionRing (X.presheaf.stalk x) K]
    [IsLocalization.Away ϖ K] :
    ∃ F : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U).ι).obj F ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U)).obj
          (MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩)) := by
  classical
  let g := X.fromSpecStalk x
  let W := g ⁻¹ᵁ U
  let a : Spec (.of K) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K))
  obtain ⟨φ, hfac⟩ : ∃ φ : Spec (.of K) ≅ W.toScheme, φ.hom ≫ W.ι = a :=
    exists_iso_preimage_fromSpecStalk_of_isLocalizationAway U hdense' x hxU ϖ hϖ K
  let b : Spec (.of K) ⟶ U.toScheme := φ.hom ≫ (g ∣_ U)
  have hb : b ≫ U.ι = a ≫ g := by
    simp only [b, Category.assoc, morphismRestrict_ι, ← hfac]
    rfl
  let E : FiniteEtaleOver U.toScheme :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩
  obtain ⟨F, ⟨iF⟩⟩ := exists_finiteEtale_extension_of_forall_fieldFactor
    (X.presheaf.stalk x) K ((finiteEtaleBaseChange b).obj E) (by
      intro L _ _ _ _ _ _ v hv hvV
      have : IsPreimmersion v := hv
      have : IsPreimmersion b := by
        show IsPreimmersion (φ.hom ≫ g ∣_ U)
        infer_instance
      have : IsPreimmersion (finiteEtaleBaseChangeProj b E) := by
        show IsPreimmersion (pullback.fst E.hom b)
        infer_instance
      let v' : Spec (.of L) ⟶ Y := v ≫ finiteEtaleBaseChangeProj b E
      have : IsPreimmersion v' := IsPreimmersion.comp v (finiteEtaleBaseChangeProj b E)
      have hv' : v' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b :=
        (Category.assoc v (finiteEtaleBaseChangeProj b E) E.hom).trans
          ((congrArg (v ≫ ·) (finiteEtaleBaseChangeProj_comp_hom b E)).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) hvV)))
      exact hunr K L
        ⟨b, v', hb, hv', exists_ringEquiv_residueField_of_isPreimmersion v'⟩)
  exact ⟨F, nonempty_iso_of_iso_finiteEtaleBaseChange_obj φ
    (((finiteEtaleBaseChangeComp φ.hom W.ι a hfac.symm).app F).symm ≪≫ iF ≪≫
      (finiteEtaleBaseChangeComp φ.hom (g ∣_ U) b rfl).app E)⟩

/-- The extension at a codimension-one boundary point, with the unramifiedness hypothesis
specialized to that point. -/
private lemma exists_finiteEtale_extension_stalk_of_forall_fieldFactorAt
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f] (x : X)
    (hunr : ∀ (hD : IsDomain (X.presheaf.stalk x))
      (hV : IsDiscreteValuationRing (X.presheaf.stalk x)),
      letI := hD
      letI := hV
      ∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk x) K]
        [IsFractionRing (X.presheaf.stalk x) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk x) L]
        [IsScalarTower (X.presheaf.stalk x) K L],
        Stacks.FundamentalGroup.IsFieldFactorAt U.ι f x K L →
          IsDiscreteValuationRing.IsUnramifiedWithRespectTo (X.presheaf.stalk x) K L)
    (hxU : x ∉ U) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ F : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U).ι).obj F ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U)).obj
          (MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩)) := by
  classical
  have htfae := (isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 3 1
  obtain ⟨hdom, hdvr⟩ := htfae.mp ⟨inferInstance, hdim⟩
  let := hdom
  let := hdvr
  have hdense' : Dense (U : Set X) := by rwa [DenseRange, Scheme.Opens.range_ι] at hdense
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have := isLocalization_away_fractionRing_of_irreducible hϖ
  exact exists_finiteEtale_extension_stalk_of_isLocalization U hdense' f x (hunr hdom hdvr) hxU ϖ hϖ
    (FractionRing (X.presheaf.stalk x))

/-- **The first stage of [Stacks, Tag 0H2W].** Let `X` be a locally Noetherian scheme, `U ⊆ X` a
dense open and `f : Y ⟶ U` finite étale and unramified over `X` in codimension one. If `x ∉ U`
and `𝒪_{X, x}` is regular of dimension one, the restriction of `Y` to the preimage of `U` in
`Spec 𝒪_{X, x}` extends to a finite étale cover of `Spec 𝒪_{X, x}`. -/
theorem exists_finiteEtale_extension_stalk_of_isUnramifiedInCodimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι f)
    (x : X) (hxU : x ∉ U) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ F : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U).ι).obj F ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U)).obj
          (MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩)) := by
  have hcoh : Order.coheight x = 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  obtain ⟨Z, rfl⟩ : ∃ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor
      X, Z.genericPoint = x :=
    ⟨⟨Stacks.Chow.integralComponentAt x, Stacks.Chow.isIntegral_integralComponentAt x,
      (Stacks.Divisors.PrimeDivisor.ofCoheightOne x hcoh).codimension_one⟩,
      Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne x hcoh⟩
  exact exists_finiteEtale_extension_stalk_of_forall_fieldFactorAt U hdense f _
    (hunr Z (by rwa [Scheme.Opens.range_ι])) hxU hdim

end AlgebraicGeometry

end
