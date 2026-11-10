module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralModification
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModifications
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Modifications of a surface singularity with normal punctured spectrum (Stacks 0AE3)

Let `(A, 𝔪, κ)` be a two-dimensional Noetherian local domain whose punctured spectrum
`U = Spec A ∖ {𝔪}` is a normal scheme. **Stacks 0AE3** says that every modification
`f : X → Spec A` (Stacks 0AD8: a proper birational morphism of algebraic spaces with `X`
integral) is an object of the category of Stacks 0AE2: `f` is proper and `f⁻¹(U) → U` is an
isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_yoneda_baseTerminal`: the spectrum of a domain is an
  integral algebraic space.
* `AlgebraicGeometry.Space.isNoetherian_yoneda_baseTerminal`: the spectrum of a Noetherian ring
  is a Noetherian algebraic space.
* `AlgebraicGeometry.Space.isProperModification_of_isIntegralModification`: **Stacks 0AE3**.

## The proof

The source's. Let `W ⊆ Spec A` be the largest open subspace over which `f` is an isomorphism
(Stacks 06R2). A prime `𝔭 ≠ 𝔪` of `A` has height `0` or `1`, because a chain of length two
below `𝔭` would make the height of `𝔪` at least three. So every point of `U` is either the
generic point, which lies in `W` by Stacks 0BBQ part (1), or a point of codimension one whose
local ring is normal (it is a local ring of the normal scheme `U`), which lies in `W` by
Stacks 0BBQ part (2). Hence `U ⊆ W`: a morphism `T → Spec A` landing in `U` has all its points
in `W`, so it factors through `W` (Stacks 03IE). The base change of an isomorphism `f⁻¹(W) → W`
to `U ⊆ W` is an isomorphism.

## Implementation notes

`Spec A` is the represented algebraic space `yoneda.obj (baseTerminal _ _ _)`; its points are
identified with the points of the scheme `Spec A` by `pointsToScheme`. The integrality of
`Spec A` that the definition of a modification asks for as context is supplied by
`isIntegralSpace_yoneda_baseTerminal`, so the statement carries no hypothesis beyond the
source's.

## References

* [Stacks Project, Tag 0AE3](https://stacks.math.columbia.edu/tag/0AE3)
* [Stacks Project, Tag 0BBQ](https://stacks.math.columbia.edu/tag/0BBQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A)))

omit [IsLocalRing A] in
/-- The spectrum of a domain, as the algebraic space it represents over itself, is integral:
reduced, decent and with irreducible space of points. -/
theorem isIntegralSpace_yoneda_baseTerminal [IsDomain A] :
    IsIntegralSpace B (Spec (.of A)) hS (yoneda.obj (baseTerminal B (Spec (.of A)) hS)) := by
  refine ⟨?_, isDecentSpace_yoneda B (Spec (.of A)) hS _, ?_⟩
  · exact hasEtaleLocalProperty_of_representable B (Spec (.of A)) hS _
      (fun T : Scheme.{u} => IsReduced T) (baseTerminal B (Spec (.of A)) hS) (Iso.refl _)
      (inferInstanceAs (IsReduced (Spec (.of A))))
  · have : IrreducibleSpace ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj
        (baseTerminal B (Spec (.of A)) hS)) :=
      inferInstanceAs (IrreducibleSpace (Spec (.of A)))
    exact (schemePointsHomeomorph B (Spec (.of A)) hS
      (baseTerminal B (Spec (.of A)) hS)).symm.surjective.irreducibleSpace
      (Homeomorph.continuous _)

omit [IsLocalRing A] in
/-- The spectrum of a Noetherian ring, as the algebraic space it represents over itself, is a
Noetherian algebraic space. -/
theorem isNoetherian_yoneda_baseTerminal [IsNoetherianRing A]
    (hS : B.Contains (Spec (.of A))) :
    IsNoetherian B (Spec (.of A)) hS B.contains_terminal
      (yoneda.obj (baseTerminal B (Spec (.of A)) hS)) :=
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hS _
      (inferInstanceAs (IsAffine (Spec (.of A)))),
    isAbsolutelyQuasiSeparated_yoneda_obj B (Spec (.of A)) hS B.contains_terminal _
      (inferInstanceAs (QuasiSeparatedSpace (Spec (.of A)))),
    hasEtaleLocalProperty_of_representable B (Spec (.of A)) hS _
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (baseTerminal B (Spec (.of A)) hS)
      (Iso.refl _) (inferInstanceAs (IsLocallyNoetherian (Spec (.of A))))⟩

/-- In a two-dimensional Noetherian local ring, a prime other than the maximal ideal has
height `0` or `1`. -/
theorem height_eq_zero_or_eq_one_of_ne_maximalIdeal [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (p : Ideal A) [p.IsPrime]
    (hp : p ≠ IsLocalRing.maximalIdeal A) : p.height = 0 ∨ p.height = 1 := by
  have hmax : (IsLocalRing.maximalIdeal A).height = 2 := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
    rfl
  have h := Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp)
  rw [hmax] at h
  exact Order.le_one_iff.mp (ENat.lt_two_iff.mp h)

omit [IsLocalRing A] in
/-- The dimension of the local ring of `Spec A`, as an algebraic space, at a point is the
height of the corresponding prime. -/
theorem localRingDimension_yoneda_baseTerminal
    (y : points B (Spec (.of A)) hS (yoneda.obj (baseTerminal B (Spec (.of A)) hS))) :
    (localRingDimension B (Spec (.of A)) hS y : WithBot ℕ∞) =
      ((pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
        y).asIdeal.height : WithBot ℕ∞) := by
  have hu := chartPoint_pointsToScheme B (Spec (.of A)) hS
    (baseTerminal B (Spec (.of A)) hS) (𝟙 _) y
  rw [pointsMap_id, id_eq] at hu
  rw [localRingDimension_eq_of_chartPoint B (Spec (.of A)) hS
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _) _ (𝟙 _)
    (presheaf_etale_of_iso B (Spec (.of A)) hS (Iso.refl _)) _ y hu]
  let q : PrimeSpectrum A :=
    pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS) y
  change ringKrullDim ((Spec (.of A)).presheaf.stalk q) = _
  let _ : Algebra A ((Spec (.of A)).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A q
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal _

/-- A ring isomorphic to a normal domain is a normal domain. -/
private theorem isNormalDomain_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsNormalDomain R] (e : R ≃+* R') : IsNormalDomain R' :=
  have : IsDomain R' := e.symm.injective.isDomain e.symm.toRingHom
  ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

/-- At a point of the punctured spectrum of `A`, the local ring of `Spec A`, as an algebraic
space, is normal when the punctured spectrum is a normal scheme. -/
theorem hasNormalLocalRingAtPoint_yoneda_baseTerminal
    [AlgebraicGeometry.IsNormal (Stacks.puncturedSpectrum A).toScheme]
    (y : points B (Spec (.of A)) hS (yoneda.obj (baseTerminal B (Spec (.of A)) hS)))
    (hy : pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS) y ≠
      IsLocalRing.closedPoint A) :
    HasNormalLocalRingAtPoint B (Spec (.of A)) hS _
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _) y := by
  induction y using Quot.inductionOn with
  | h p =>
    refine ⟨baseTerminal B (Spec (.of A)) hS, 𝟙 _,
      presheaf_etale_of_iso B (Spec (.of A)) hS (Iso.refl _), p, by rw [pointsMap_id, id_eq], ?_⟩
    let q : PrimeSpectrum A := schemePoint B (Spec (.of A)) hS _ p
    have hq : q ∈ Stacks.puncturedSpectrum A := hy
    change IsNormalDomain ((Spec (.of A)).presheaf.stalk q)
    have : IsNormalDomain ((Stacks.puncturedSpectrum A).toScheme.presheaf.stalk ⟨q, hq⟩) :=
      ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
    exact isNormalDomain_of_ringEquiv
      ((Stacks.puncturedSpectrum A).stalkIso ⟨q, hq⟩).commRingCatIsoToRingEquiv

/-- **Stacks 0AE3.** Let `(A, 𝔪, κ)` be a two-dimensional Noetherian local domain whose
punctured spectrum `U = Spec A ∖ {𝔪}` is a normal scheme. Then every modification
`f : X → Spec A` lies in the category of Stacks 0AE2: `f` is proper and its base change
`f⁻¹(U) → U` to the punctured spectrum is an isomorphism. -/
@[stacks 0AE3]
theorem isProperModification_of_isIntegralModification [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) [AlgebraicGeometry.IsNormal (Stacks.puncturedSpectrum A).toScheme]
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hS))
    (hf : IsIntegralModification B (Spec (.of A)) hS hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _)
      (isIntegralSpace_yoneda_baseTerminal A B hS) f) :
    IsProperModification B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
      (puncturedSpectrumSubfunctor A B hS) (Over.mk f) := by
  let Y := yoneda.obj (baseTerminal B (Spec (.of A)) hS)
  have hY : IsAlgebraicSpace B (Spec (.of A)) hS Y := isAlgebraicSpace_yoneda B _ hS _
  have hYint := isIntegralSpace_yoneda_baseTerminal A B hS
  have hXint := hf.isIntegralSpace B (Spec (.of A)) hS
  refine (isProperModification_iff B _ hS _ _ _).mpr ⟨hX, hf.isProper B _ hS, ?_⟩
  change IsIso (pullback.snd f (puncturedSpectrumSubfunctor A B hS).ι)
  -- The largest open subspace of `Spec A` over which `f` is an isomorphism.
  obtain ⟨W, hW⟩ := exists_isGreatest_isIso_pullback_snd B (Spec (.of A)) hS hX hY f
  have hBir : ∃ (hDY : IsDecentSpace B (Spec (.of A)) hS X)
      (hDX : IsDecentSpace B (Spec (.of A)) hS Y)
      (hCY : (irreducibleComponents (points B (Spec (.of A)) hS X)).Finite)
      (hCX : (irreducibleComponents (points B (Spec (.of A)) hS Y)).Finite),
      IsBirational B (Spec (.of A)) hS hX hY hDY hDX hCY hCX f :=
    ⟨_, _, _, _, hf.isBirational B _ hS⟩
  -- Every point of the punctured spectrum lies in `W`, by Stacks 0BBQ.
  have hpts : ∀ y : points B (Spec (.of A)) hS Y,
      pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS) y ≠
        IsLocalRing.closedPoint A →
      y ∈ Set.range (pointsMap B (Spec (.of A)) hS W.toFunctor W.ι) := by
    intro y hy
    let q : PrimeSpectrum A :=
      pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS) y
    have hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal A := fun h ↦
      hy (PrimeSpectrum.ext h)
    have hdimy := localRingDimension_yoneda_baseTerminal A B hS y
    have hdim' : ∀ n : ℕ∞, q.asIdeal.height = n → localRingDimension B (Spec (.of A)) hS y = n :=
      fun n h ↦ WithBot.coe_injective (hdimy.trans (congrArg _ h))
    rcases height_eq_zero_or_eq_one_of_ne_maximalIdeal A hdim q.asIdeal hqm with h0 | h1
    · have := hdim' 0 h0
      exact mem_isomorphismLocus_of_localRingDimension_eq_zero B (Spec (.of A)) hS
        B.contains_terminal hY hX (isNoetherian_yoneda_baseTerminal A B hS) f hBir
        (hf.isProper B _ hS) W hW y this
    · have := hdim' 1 h1
      exact mem_isomorphismLocus_of_localRingDimension_eq_one_of_normal B (Spec (.of A)) hS
        B.contains_terminal hY hX (isNoetherian_yoneda_baseTerminal A B hS) f hBir
        (hf.isProper B _ hS) hXint.hasEtaleLocalProperty_isReduced W hW y this
        (hasNormalLocalRingAtPoint_yoneda_baseTerminal A B hS y hy)
  -- Hence the punctured spectrum is contained in `W`, by Stacks 03IE.
  have hle : puncturedSpectrumSubfunctor A B hS ≤ W := by
    rintro T x ⟨g, hg⟩
    obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B (Spec (.of A)) hS hY
      (isAlgebraicSpace_yoneda B _ hS T.unop) W hW.1.1 (yoneda.map x)).mpr (by
        rintro _ ⟨t, rfl⟩
        apply hpts
        rw [pointsToScheme_pointsMap_yoneda, ← hg]
        intro hc
        rw [Scheme.Hom.comp_apply] at hc
        have hmem : (Stacks.puncturedSpectrum A).ι
            (g (pointsToScheme B (Spec (.of A)) hS T.unop t)) ∈ Stacks.puncturedSpectrum A := by
          have := Set.mem_range_self (f := ⇑(Stacks.puncturedSpectrum A).ι)
            (g (pointsToScheme B (Spec (.of A)) hS T.unop t))
          rwa [Scheme.Opens.range_ι] at this
        exact Stacks.notMem_puncturedSpectrum_closedPoint A (hc ▸ hmem))
    have hx : (W.ι.app T (k.app T (𝟙 T.unop))) = x := by
      rw [← NatTrans.comp_app_apply, hk]
      exact Category.id_comp x
    rw [← hx]
    exact (k.app T (𝟙 T.unop)).2
  exact isIso_pullback_snd_of_factor f (Subfunctor.homOfLe hle) (Subfunctor.homOfLe_ι hle)
    hW.1.2

end AlgebraicGeometry.Space

end
