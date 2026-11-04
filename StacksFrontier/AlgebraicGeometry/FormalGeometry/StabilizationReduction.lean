module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.Dualizing.Ubiquity

/-!
# The comparison map of Stacks 0EFI, and the reduction of that lemma to one existential

`Stacks.Algebraization.localCohomologyComparison` is the canonical map
`RΓ_{J₀}(K) → RΓ_{J'}(K)` attached to an inclusion `J' ≤ J₀` of support ideals. It is defined as
an adjunct, which says what it is but makes nothing about it immediately usable. This file proves
the one identity that characterizes it — its composite with the counit of `RΓ_{J'}` is the counit
of `RΓ_{J₀}` — and draws the two consequences that follow from that identity alone:

* the comparison for `J' = J₀` is the identity;
* the comparison is an isomorphism whenever `V(J') = V(J₀)`, i.e. local cohomology sees the
  support ideal only through its zero locus.

The second is the degenerate case of the comparison statement of Stacks 0EFI, and it is what makes
the conclusion of that lemma satisfiable: `isStabilizingData_bot` exhibits a pair with the
stabilization property of `Stacks.Algebraization.IsStabilizingData` for `I = ⊥` and arbitrary `J`,
so neither that predicate nor the hypotheses that feed it is vacuous.

Finally, the two cohomological statements of Stacks 0EFI are stated here verbatim, each with the
single extra hypothesis that *some* pair has the stabilization property. Together with
`Stacks.Algebraization.stabilizingIdeal_le` and
`Stacks.Algebraization.zeroLocus_stabilizingIdeal_inter`, which are unconditional, this reduces the
whole of Stacks 0EFI to `∃ p, IsStabilizingData I J s p` and nothing else.

## Main results

* `Stacks.Algebraization.localCohomologyComparison_comp_counit` — the characterizing identity.
* `Stacks.Algebraization.localCohomologyComparison_self` — the comparison for `J' = J₀` is `𝟙`.
* `Stacks.Algebraization.isIso_localCohomologyComparison_of_zeroLocus_eq` — the comparison is an
  isomorphism when `V(J') = V(J₀)`.
* `Stacks.Algebraization.isStabilizingData_bot` — `(J, 1)` has the stabilization property for
  `I = ⊥`, so `IsStabilizingData` is satisfiable.
* `Stacks.Algebraization.stabilizationHypotheses_bot` and
  `Stacks.Algebraization.exists_stabilizationHypotheses_and_isStabilizingData` — the hypotheses and
  the conclusion of Stacks 0EFI hold together at a field, with the module the ring itself.
* `Stacks.Algebraization.localCohomologyComparison_isIso_of_exists` and
  `Stacks.Algebraization.pow_mul_le_annihilator_localCohomology_of_exists` — the two cohomological
  statements of Stacks 0EFI, conditional on the existence of a stabilizing pair.

## Implementation notes

The comparison lands in `D(A)`, whereas the adjunction that defines it lives on the full
subcategory of objects with power-torsion cohomology. These are genuinely different hom types:
morphisms of an `InducedCategory` are a one-field structure, so a map of `D(A)` between the
underlying objects is *not* a morphism of the subcategory and must be wrapped by
`ObjectProperty.homMk`. All statements here are therefore phrased in `D(A)`, with the wrapping
confined to the proofs of `hom_ext_comp_localCohomologyCounit`.

A second, independent crossing: `Dualizing.localCohomologyFunctor` is by definition the first
component of `Dualizing.localCohomologyRightAdjoint`, which is the spelling the adjunction's unit
and counit carry. The two agree by `rfl` but not at the `implicit` transparency at which `rw`
builds its motive, so every proof here is in term mode rather than tactic mode.

`localCohomologyComparisonInv` is the comparison in the reverse direction when `V(J') = V(J₀)`.
It is not an instance of `localCohomologyComparison`, which needs an inclusion of ideals in the
other direction; it is the same adjunct construction with the roles exchanged, available because
`V(J') = V(J₀)` makes `RΓ_{J'}(K)` a `J₀`-power-torsion object.

## References

* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-! ### The characterizing identity -/

/-- A map into `RΓ_I(K)` out of an object with `I`-power-torsion cohomology is determined by its
composite with the counit `RΓ_I(K) → K`. -/
public theorem hom_ext_comp_localCohomologyCounit (I : Ideal A) (hI : I.FG)
    {K : DerivedCategory (ModuleCat.{v} A)}
    (X : Dualizing.PowerTorsionDerivedCategory.{u, v} A I hI)
    (u w : X.obj ⟶ ((Dualizing.localCohomologyFunctor A I hI).obj K).obj)
    (huw : u ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app K =
      w ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app K) : u = w :=
  congrArg (fun f => (Dualizing.derivedPowerTorsionProperty A I hI).ι.map f)
    (((Dualizing.localCohomologyAdjunction A I hI).homEquiv X K).symm.injective
      (((Adjunction.homEquiv_counit (Dualizing.localCohomologyAdjunction A I hI) X K
              (ObjectProperty.homMk u)).trans
          huw).trans
        (Adjunction.homEquiv_counit (Dualizing.localCohomologyAdjunction A I hI) X K
            (ObjectProperty.homMk w)).symm))

/-- The adjunct of a map `X → K` out of a power-torsion object, composed back with the counit of
`RΓ_I`, is the map itself. -/
public theorem map_localCohomologyHomEquiv_comp_counit (I : Ideal A) (hI : I.FG)
    (X : Dualizing.PowerTorsionDerivedCategory.{u, v} A I hI)
    (K : DerivedCategory (ModuleCat.{v} A)) (f : X.obj ⟶ K) :
    (Dualizing.derivedPowerTorsionProperty A I hI).ι.map
        ((Dualizing.localCohomologyAdjunction A I hI).homEquiv X K f) ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app K = f :=
  (Adjunction.homEquiv_counit (Dualizing.localCohomologyAdjunction A I hI) X K _).symm.trans
    (Equiv.symm_apply_apply _ _)

/-- **The identity that characterizes the comparison map.** Composing
`localCohomologyComparison : RΓ_{J₀}(K) → RΓ_{J'}(K)` with the counit of `RΓ_{J'}` gives the counit
of `RΓ_{J₀}`; by `hom_ext_comp_localCohomologyCounit` it is the only map that does so. -/
public theorem localCohomologyComparison_comp_counit (J₀ J' : Ideal A) (hJ₀ : J₀.FG) (hJ' : J'.FG)
    (h : J' ≤ J₀) (K : DerivedCategory (ModuleCat.{v} A)) :
    localCohomologyComparison A J₀ J' hJ₀ hJ' h K ≫
        (Dualizing.localCohomologyAdjunction A J' hJ').counit.app K =
      (Dualizing.localCohomologyAdjunction A J₀ hJ₀).counit.app K :=
  map_localCohomologyHomEquiv_comp_counit J' hJ' _ K _

/-- The comparison map for `J' = J₀` is the identity. -/
public theorem localCohomologyComparison_self (J₀ : Ideal A) (hJ₀ : J₀.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    localCohomologyComparison A J₀ J₀ hJ₀ hJ₀ le_rfl K = 𝟙 _ :=
  (congrArg (fun f => (Dualizing.derivedPowerTorsionProperty A J₀ hJ₀).ι.map f)
      ((Adjunction.homEquiv_unit (Dualizing.localCohomologyAdjunction A J₀ hJ₀) _ K _).trans
        (Adjunction.right_triangle_components
          (Dualizing.localCohomologyAdjunction A J₀ hJ₀) K))).trans
    (CategoryTheory.Functor.map_id (Dualizing.derivedPowerTorsionProperty A J₀ hJ₀).ι _)

/-! ### Local cohomology sees only the zero locus -/

/-- Power-torsion cohomology depends on the support ideal only through its zero locus: this is
Stacks 0953 applied degreewise. -/
public theorem derivedPowerTorsionProperty_of_zeroLocus_eq (J₀ J' : Ideal A) (hJ₀ : J₀.FG)
    (hJ' : J'.FG)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) = PrimeSpectrum.zeroLocus (J₀ : Set A))
    {X : DerivedCategory (ModuleCat.{v} A)}
    (hX : Dualizing.derivedPowerTorsionProperty A J' hJ' X) :
    Dualizing.derivedPowerTorsionProperty A J₀ hJ₀ X := by
  intro i
  rw [isIPowerTorsion_iff_support_subset _ _ _ hJ₀, ← hV]
  exact (isIPowerTorsion_iff_support_subset _ _ _ hJ').mp (hX i)

/-- The comparison map in the reverse direction, available when `V(J') = V(J₀)`: then `RΓ_{J'}(K)`
has `J₀`-power-torsion cohomology, so the counit of `RΓ_{J'}` has an `RΓ_{J₀}`-adjunct. -/
public noncomputable def localCohomologyComparisonInv (J₀ J' : Ideal A) (hJ₀ : J₀.FG) (hJ' : J'.FG)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) = PrimeSpectrum.zeroLocus (J₀ : Set A))
    (K : DerivedCategory (ModuleCat.{v} A)) :
    ((Dualizing.localCohomologyFunctor A J' hJ').obj K).obj ⟶
      ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj :=
  (Dualizing.derivedPowerTorsionProperty A J₀ hJ₀).ι.map
    ((Dualizing.localCohomologyAdjunction A J₀ hJ₀).homEquiv
      ⟨((Dualizing.localCohomologyFunctor A J' hJ').obj K).obj,
        derivedPowerTorsionProperty_of_zeroLocus_eq J₀ J' hJ₀ hJ' hV
          ((Dualizing.localCohomologyFunctor A J' hJ').obj K).property⟩
      K ((Dualizing.localCohomologyAdjunction A J' hJ').counit.app K))

/-- The reverse comparison satisfies the identity characterizing it. -/
public theorem localCohomologyComparisonInv_comp_counit (J₀ J' : Ideal A) (hJ₀ : J₀.FG)
    (hJ' : J'.FG)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) = PrimeSpectrum.zeroLocus (J₀ : Set A))
    (K : DerivedCategory (ModuleCat.{v} A)) :
    localCohomologyComparisonInv J₀ J' hJ₀ hJ' hV K ≫
        (Dualizing.localCohomologyAdjunction A J₀ hJ₀).counit.app K =
      (Dualizing.localCohomologyAdjunction A J' hJ').counit.app K :=
  map_localCohomologyHomEquiv_comp_counit J₀ hJ₀ _ K _

/-- An endomorphism of `RΓ_I(K)` that fixes the counit `RΓ_I(K) → K` is the identity. -/
private theorem eq_id_of_comp_counit (I : Ideal A) (hI : I.FG)
    {K : DerivedCategory (ModuleCat.{v} A)}
    (f : ((Dualizing.localCohomologyFunctor A I hI).obj K).obj ⟶
      ((Dualizing.localCohomologyFunctor A I hI).obj K).obj)
    (hf : f ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app K =
      (Dualizing.localCohomologyAdjunction A I hI).counit.app K) : f = 𝟙 _ :=
  hom_ext_comp_localCohomologyCounit I hI _ f (𝟙 _) (hf.trans (Category.id_comp _).symm)

/-- **Local cohomology sees the support ideal only through its zero locus.** If `J' ≤ J₀` and
`V(J') = V(J₀)` then the comparison `RΓ_{J₀}(K) → RΓ_{J'}(K)` is an isomorphism. -/
public theorem isIso_localCohomologyComparison_of_zeroLocus_eq (J₀ J' : Ideal A) (hJ₀ : J₀.FG)
    (hJ' : J'.FG) (h : J' ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) = PrimeSpectrum.zeroLocus (J₀ : Set A))
    (K : DerivedCategory (ModuleCat.{v} A)) :
    IsIso (localCohomologyComparison A J₀ J' hJ₀ hJ' h K) := by
  refine ⟨⟨localCohomologyComparisonInv J₀ J' hJ₀ hJ' hV K, ?_, ?_⟩⟩
  · exact eq_id_of_comp_counit J₀ hJ₀ _ ((Category.assoc _ _ _).trans
      ((congrArg (fun x => localCohomologyComparison A J₀ J' hJ₀ hJ' h K ≫ x)
          (localCohomologyComparisonInv_comp_counit J₀ J' hJ₀ hJ' hV K)).trans
        (localCohomologyComparison_comp_counit J₀ J' hJ₀ hJ' h K)))
  · exact eq_id_of_comp_counit J' hJ' _ ((Category.assoc _ _ _).trans
      ((congrArg (fun x => localCohomologyComparisonInv J₀ J' hJ₀ hJ' hV K ≫ x)
          (localCohomologyComparison_comp_counit J₀ J' hJ₀ hJ' h K)).trans
        (localCohomologyComparisonInv_comp_counit J₀ J' hJ₀ hJ' hV K)))

/-! ### The conclusion of Stacks 0EFI is satisfiable -/

/-- Every prime lies in `V(⊥)`. -/
private theorem mem_zeroLocus_bot (p : PrimeSpectrum A) :
    p ∈ PrimeSpectrum.zeroLocus ((⊥ : Ideal A) : Set A) := by
  rw [PrimeSpectrum.zeroLocus_bot]; exact Set.mem_univ p

section

variable [IsNoetherianRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **`IsStabilizingData` is satisfiable.** For `I = ⊥` the pair `(J, 1)` has the stabilization
property of Stacks 0EFI, for every `J` and every `s`.

Everything is forced: `V(⊥)` is all of `Spec A`, so an admissible shrinking `J' ≤ J` is one with
`V(J') = V(J)`, and then the comparison is an isomorphism by
`isIso_localCohomologyComparison_of_zeroLocus_eq`; and `J * ⊥ = ⊥` annihilates everything.

This is recorded because the predicate is the whole remaining content of Stacks 0EFI, and a
predicate that held for no pair would make the two cohomological statements of that lemma vacuous
rather than unproved. -/
public theorem isStabilizingData_bot (J : Ideal A) (s : ℤ) :
    IsStabilizingData (M := M) (⊥ : Ideal A) J s (J, 1) where
  le := le_rfl
  zeroLocus_inter := rfl
  isIso := by
    intro J' hJ' hVJ' i _
    have hV : PrimeSpectrum.zeroLocus (J' : Set A) = PrimeSpectrum.zeroLocus (J : Set A) := by
      simpa [PrimeSpectrum.zeroLocus_bot] using hVJ'
    have := isIso_localCohomologyComparison_of_zeroLocus_eq J J' J.fg_of_isNoetherianRing
      J'.fg_of_isNoetherianRing hJ' hV
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M))
    infer_instance
  pow_mul_le_annihilator := by
    intro J' _ _ i _
    have h : ((J, 1) : Ideal A × ℕ).1 * (⊥ : Ideal A) = ⊥ := by simp
    simp only [h, pow_one]
    exact bot_le

/-- **`StabilizationHypotheses` is satisfiable.** For `I = ⊥` the two quantified hypotheses of
Stacks 0EFI are vacuous — `V(⊥)` is all of `Spec A`, so no prime lies outside it — and the
hypotheses reduce to the existence of a dualizing complex. -/
public theorem stabilizationHypotheses_bot (J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) (h : Dualizing.IsDualizingComplex omega) :
    StabilizationHypotheses (M := M) (⊥ : Ideal A) J s d omega where
  dualizing := h
  dimensionBound p hp := absurd (mem_zeroLocus_bot p) hp
  depthOrDimensionBound p hp := absurd (mem_zeroLocus_bot p) hp

end

/-- **A concrete instance at which every hypothesis and the whole conclusion of Stacks 0EFI
hold simultaneously.** Take `A = k` a field — a Noetherian local ring — the module `M = k`, and
`I = ⊥`; then `k[0]` is a dualizing complex by Stacks 0BFR, the two quantified hypotheses are
vacuous, and `(J, 1)` is a stabilizing pair.

Nothing in the statement of Stacks 0EFI is therefore vacuous: the hypotheses have a model and
the conclusion holds in it. -/
public theorem exists_stabilizationHypotheses_and_isStabilizingData
    (k : Type u) [Field k] (J : Ideal k) (s d : ℤ) :
    ∃ omega : DerivedCategory (ModuleCat.{u} k),
      StabilizationHypotheses (M := k) (⊥ : Ideal k) J s d omega ∧
        ∃ p : Ideal k × ℕ, IsStabilizingData (M := k) (⊥ : Ideal k) J s p := by
  obtain ⟨omega, homega⟩ := Dualizing.exists_isDualizingComplex k
  exact ⟨omega, stabilizationHypotheses_bot J s d omega homega, ⟨(J, 1), isStabilizingData_bot J s⟩⟩

/-! ### The two cohomological statements of Stacks 0EFI -/

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I J : Ideal A) (s d : ℤ)
  (omega : DerivedCategory (ModuleCat.{w} A))
  (H : StabilizationHypotheses (M := M) I J s d omega)

/-- **Stacks 0EFI**, the comparison statement, conditional on the existence of a stabilizing pair.

The statement is that of the source: for every ideal `J'` below the stabilizing ideal whose zero
locus meets `V(I)` in the same set as `V(J)` does, the canonical comparison is an isomorphism on
cohomology in every degree `i ≤ s`. The hypothesis `hex` is the existence half of Stacks 0EFI, and
is the only thing this proof uses beyond the selection property of `stabilizingData`. -/
public theorem localCohomologyComparison_isIso_of_exists
    (hex : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p)
    (J' : Ideal A) (hJ' : J' ≤ stabilizingIdeal I J s d omega H)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))
    (i : ℤ) (hi : i ≤ s) :
    let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
      (ModuleCat.of A M)
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (localCohomologyComparison A (stabilizingIdeal I J s d omega H) J'
        (stabilizingIdeal I J s d omega H).fg_of_isNoetherianRing
        J'.fg_of_isNoetherianRing hJ' K)) :=
  (isStabilizingData_stabilizingData I J s d omega H hex).isIso J' hJ' hV i hi

/-- **Stacks 0EFI**, the uniform annihilation statement, conditional on the existence of a
stabilizing pair.

The statement is that of the source: one power of `J₀ I`, with the exponent
`stabilizingPower` chosen once and for all, annihilates the local cohomology of `M` supported in
every admissible `J'` in every degree `i ≤ s`. -/
public theorem pow_mul_le_annihilator_localCohomology_of_exists
    (hex : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p)
    (J' : Ideal A) (hJ' : J' ≤ stabilizingIdeal I J s d omega H)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))
    (i : ℤ) (hi : i ≤ s) :
    let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
      (ModuleCat.of A M)
    (stabilizingIdeal I J s d omega H * I) ^
        stabilizingPower I J s d omega H ≤
      Module.annihilator A ↥
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
          ((Dualizing.localCohomologyFunctor A J'
            J'.fg_of_isNoetherianRing).obj K).obj) :=
  (isStabilizingData_stabilizingData I J s d omega H hex).pow_mul_le_annihilator J' hJ' hV i hi

end

end Stacks.Algebraization
