module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# The strict henselization at a point with discrete valuation local ring

If the local ring `𝒪_{S,s}` of a scheme at the image of a geometric point `s` is a discrete
valuation ring and noetherian (for instance at a closed point of a regular curve), then the étale
local ring `𝒪^{sh}_{S,s}` is a discrete valuation ring: it is the strict henselization of
`𝒪_{S,s}` (`AlgebraicGeometry.etaleLocalRingEquivStrictHenselization`), and the discrete valuation
ring property ascends to strict henselizations (Stacks 0AP3,
`isDiscreteValuationRing_iff_henselizations`).

## Main results

* `AlgebraicGeometry.isDomain_and_isDiscreteValuationRing_etaleLocalRing` — the étale local ring
  at `s` is a domain and a discrete valuation ring.
-/

@[expose] public section

open IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The étale local ring at a point with discrete valuation local ring is a discrete valuation
ring** (Stacks 0AP3 read on the strict henselization of Stacks 04HX). -/
theorem isDomain_and_isDiscreteValuationRing_etaleLocalRing
    [IsNoetherianRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDomain ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDiscreteValuationRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))] :
    ∃ _ : IsDomain ↥(etaleLocalRing B S hS s),
      IsDiscreteValuationRing ↥(etaleLocalRing B S hS s) := by
  let T := geometricHenselizationTower S s
  obtain ⟨hdom, hdvr⟩ := (isDiscreteValuationRing_iff_henselizations
    ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) T.henselization
    T.strictHenselization
    (separableClosure
      (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField)).2.1 ⟨inferInstance, inferInstance⟩
  have e := etaleLocalRingEquivStrictHenselization B S hS s
  have : IsDomain ↥(etaleLocalRing B S hS s) := e.symm.toMulEquiv.isDomain _
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The map from the local ring at the image of a geometric point to the étale local ring is
injective: the strict henselization is faithfully flat over the local ring. -/
theorem structureSheafStalkFromLocalRing_injective :
    Function.Injective (structureSheafStalkFromLocalRing B S hS s) := by
  let T := geometricHenselizationTower S s
  have : Module.FaithfullyFlat ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      T.strictHenselization := IsHenselization.faithfullyFlat
        (L := separableClosure
          (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
          s.residueField)
  have : FaithfulSMul ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      T.strictHenselization := Module.FaithfullyFlat.faithfulSMul
  convert (etaleLocalRingAlgEquivStrictHenselization B S hS s).injective.comp
    (FaithfulSMul.algebraMap_injective ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      T.strictHenselization) using 1
  ext a
  exact ((etaleLocalRingAlgEquivStrictHenselization B S hS s).commutes a).symm

/-- **The generic point of the strict henselization lies over every nonempty open subset** of an
irreducible scheme: it maps to the generic point of `S`, because the local ring injects into the
étale local ring and the generic point of `Spec 𝒪_{S,x}` generizes a preimage of the generic
point of `S`. -/
theorem strictHenselizationToBase_bot_mem [IrreducibleSpace S]
    [IsDomain ↥(etaleLocalRing B S hS s)] (U : S.Opens) (hU : (U : Set S).Nonempty) :
    strictHenselizationToBase B S hS s (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _) ∈ U := by
  set x := s.hom (closedPoint s.residueField)
  have hinj := structureSheafStalkFromLocalRing_injective B S hS s
  have : IsDomain ↥(S.presheaf.stalk x) := hinj.isDomain _
  -- the generic point of `Spec 𝒪^{sh}` maps to the generic point of `Spec 𝒪_{S,x}`
  have h1 : Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s))
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _) =
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ↥(S.presheaf.stalk x)) :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  obtain ⟨w, hw⟩ : genericPoint S ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec S).specializes (Set.mem_univ x)
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ↥(S.presheaf.stalk x)) ⤳ w :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hsp' := hw ▸ hsp.map (S.fromSpecStalk x).continuous
  have hηU : genericPoint S ∈ U :=
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  change S.fromSpecStalk x (Spec.map (CommRingCat.ofHom
    (structureSheafStalkFromLocalRing B S hS s)) _) ∈ U
  rw [h1]
  exact hsp'.mem_open U.isOpen hηU

end AlgebraicGeometry
