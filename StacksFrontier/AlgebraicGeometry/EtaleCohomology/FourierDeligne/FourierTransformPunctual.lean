module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Dimension

/-!
# The Fourier transform of a punctual sheaf is concentrated in degree zero

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For
a sheaf `P` of `Λ`-modules on `𝔸¹_k` vanishing on a nonempty open `U` (a *punctual* sheaf),

`Hⁱ(Φ(P[0])) = 0` for `i ≠ 0`.

For `i < 0` this is the lower bound of the amplitude
(`Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_neg`). For `i > 0`, proper base
change reduces to a geometric fibre `X' ≅ 𝔸¹_Ω` of `pr₂`, where the integrand `G'` vanishes on the
preimage `U'` of `U`, which is a nonempty open since `X' ⟶ 𝔸¹_k` is the surjective base change of
`Spec Ω ⟶ Spec k`. The open-closed triangle of [Stacks, Tag 0GKP] for `U'` and its reduced closed
complement `Z'` identifies `Rf'_!(G'[0])` with `R(f'|_{Z'})_!(G'|_{Z'}[0])`, and `Z'` is a proper
closed subscheme of the irreducible curve `X'`, so it has dimension zero and its compactly
supported cohomology vanishes in positive degrees
(`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt`).

This is the amplitude part of the step (L5) of the single-level argument for the irreducibility
of the Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isZero_inverseImage_tensor_of_factors`.
* `Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_isZero_inverseImage`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
last statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
  AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Tensor

variable (Λ : Type) [CommRing Λ]

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal

/-- **`a⁻¹(p⁻¹ P ⊗ N) = 0` when `a ≫ p` factors through an open on which `P` vanishes**, for
`- ⊗ a⁻¹ N` additive: `a⁻¹(p⁻¹ P ⊗ N) ≅ (a ≫ p)⁻¹ P ⊗ a⁻¹ N` and `(a ≫ p)⁻¹ P ≅ t⁻¹(P|_W)`. -/
theorem isZero_inverseImage_tensor_of_factors {V Q Y W : Scheme.{u}} (a : V ⟶ Q) (p : Q ⟶ Y)
    (jW : W ⟶ Y) (t : V ⟶ W) (h : t ≫ jW = a ≫ p) (P : EtaleModules.{u, 0} Λ Y)
    (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ jW).obj P)) (N : EtaleModules.{u, 0} Λ Q)
    (hN : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ a).obj N)) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ a).obj
      ((etaleModuleInverseImage.{u, 0} Λ p).obj P ⊗ N)) := by
  have := hN.1
  have h₁ : IsZero ((etaleModuleInverseImage.{u, 0} Λ a).obj
      ((etaleModuleInverseImage.{u, 0} Λ p).obj P)) := by
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso Λ a p).app P).symm
    rw [← h]
    exact ((etaleModuleInverseImage.{u, 0} Λ t).map_isZero hP).of_iso
      ((etaleModuleInverseImageCompIso Λ t jW).app P)
  exact ((MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ a).obj N)).map_isZero
    h₁).of_iso ((etaleModuleInverseImageTensorRightIso Λ a N).app _)

end Tensor

/-- A dimension `d` with `d + 1 ≤ 1` satisfies `d ≤ 0`. -/
private theorem withBotENat_le_zero_of_add_one_le_one {d : WithBot ℕ∞}
    (h : d + 1 ≤ ((1 : ℕ) : WithBot ℕ∞)) : d ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have : d + 1 ≤ 1 := by exact_mod_cast this
      exact_mod_cast (by omega : d ≤ 0)

/-- The closed complement of a nonempty open `U` of a scheme is not all of it. -/
private theorem not_surjective_closedComplementι_of_nonempty {X : Scheme.{u}} (U : X.Opens)
    (hU : (U : Set X).Nonempty) : ¬ Function.Surjective (closedComplementι U.ι) := by
  intro hs
  obtain ⟨z, hz⟩ := hU
  have hz' : z ∈ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
  rw [range_eq_compl_range_closedComplementι U.ι] at hz'
  exact hz' (hs z)

/-- On an irreducible noetherian scheme of dimension at most one, the closed complement of a
nonempty open has dimension zero. -/
private theorem topologicalKrullDim_closedComplement_le_zero {X : Scheme.{u}} [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X] (hX : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    topologicalKrullDim (closedComplement U.ι) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
  withBotENat_le_zero_of_add_one_le_one <|
    (topologicalKrullDim_add_one_le_of_isClosedImmersion (closedComplementι U.ι)
      (not_surjective_closedComplementι_of_nonempty U hU)).trans hX

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

omit [Finite Λ] in
/-- `a⁻¹(p⁻¹ P ⊗ N)` vanishes on an open `W` that `a ≫ p` maps into an open on which `P`
vanishes, for `N` locally free. -/
private theorem isZero_restriction_inverseImage_tensor_of_range_subset {V Q Y U : Scheme.{u}}
    (a : V ⟶ Q) (p : Q ⟶ Y) (jU : U ⟶ Y) [IsOpenImmersion jU] (W : V.Opens)
    (hW : Set.range (W.ι ≫ a ≫ p) ⊆ Set.range jU) (P : EtaleModules.{u, 0} Λ Y)
    (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj P)) (N : EtaleModules.{u, 0} Λ Q)
    (hN : IsLocallyFreeEtaleModule Λ N) :
    IsZero ((etaleModuleRestriction.{u, 0} Λ W.ι).obj ((etaleModuleInverseImage.{u, 0} Λ a).obj
      ((etaleModuleInverseImage.{u, 0} Λ p).obj P ⊗ N))) :=
  ((isZero_inverseImage_tensor_of_factors Λ (W.ι ≫ a) p jU (IsOpenImmersion.lift jU _ hW)
      ((IsOpenImmersion.lift_fac jU _ hW).trans (Category.assoc _ _ _).symm) P hP N
      (isExactTensorRight_of_isLocallyFreeEtaleModule
        (isLocallyFreeEtaleModule_inverseImage Λ (W.ι ≫ a) hN))).of_iso
    ((etaleModuleInverseImageCompIso Λ W.ι a).app _).symm).of_iso
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ W.ι).app _).symm

/-- On an irreducible noetherian scheme of dimension at most one over a separably closed field,
a sheaf vanishing on a nonempty open has no compactly supported cohomology in positive degrees. -/
private theorem isZero_homology_derivedLowerShriek_of_isZero_restriction (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞)) (j : CompactificationOf (Over.mk f))
    (U : X.Opens) (hU : (U : Set X).Nonempty) (G : EtaleModules.{u, 0} Λ X)
    (hG : IsZero ((etaleModuleRestriction.{u, 0} Λ U.ι).obj G)) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  let iZ := closedComplementι U.ι
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ j U.ι iZ
    (range_eq_compl_range_closedComplementι U.ι) ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have : IsIso b := (Triangle.isZero₁_iff_isIso₂ _ hT).1
    ((derivedLowerShriek.{u, 0} (U.ι ≫ f) (j.restrictOpen U.ι) Λ).map_isZero
      (((DerivedCategory.Plus.singleFunctor _ 0).map_isZero hG).of_iso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (etaleModuleRestriction.{u, 0} Λ U.ι) 0).app G)))
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso (asIso b))
  exact (isZero_homology_derivedLowerShriek_of_two_mul_lt Λ Ω (iZ ≫ f) (j.restrictClosed iZ) 0
    (topologicalKrullDim_closedComplement_le_zero hX U hU) _ i (by omega)).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
        ((derivedLowerShriek.{u, 0} (iZ ≫ f) (j.restrictClosed iZ) Λ).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ iZ) 0).app G)))

omit [Fintype k] in
/-- On a geometric fibre of `pr₂ : 𝔸¹ × 𝔸¹ ⟶ 𝔸¹`, the integrand `pr₁⁻¹ P ⊗ N` of a sheaf `P`
vanishing on a nonempty open has no compactly supported cohomology in positive degrees. -/
private theorem isZero_homology_derivedLowerShriek_affineLineFibre
    (j : CompactificationOf (Over.mk 𝔸f))
    (P : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {U : Scheme.{u}}
    (jU : U ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jU] [Nonempty U]
    (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj P))
    (N : EtaleModules.{u, 0} Λ (pullback 𝔸f 𝔸f)) (hN : IsLocallyFreeEtaleModule Λ N)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial k)))
    (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (pullback.snd (pullback.snd 𝔸f 𝔸f) s)
        ((j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)).baseChange
          (IsPullback.of_hasPullback (pullback.snd 𝔸f 𝔸f) s)) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst (pullback.snd 𝔸f 𝔸f) s)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj P ⊗ N))))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let X' := pullback pr₂ s
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : Surjective (s ≫ 𝔸f) := ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim _ _⟩⟩
  have hw : Surjective (u' ≫ pr₁) := MorphismProperty.of_isPullback (P := @Surjective)
    ((IsPullback.of_hasPullback pr₂ s).paste_horiz (IsPullback.of_hasPullback 𝔸f 𝔸f)).flip
    inferInstance
  let U' : X'.Opens := (u' ≫ pr₁) ⁻¹ᵁ jU.opensRange
  have hU' : (U' : Set X').Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    obtain ⟨z, hz⟩ := hw.surj (jU x)
    exact ⟨z, show (u' ≫ pr₁) z ∈ Set.range jU from hz ▸ ⟨x, rfl⟩⟩
  obtain ⟨e, -⟩ := nonempty_affineLineFibre_iso k s
  have : IrreducibleSpace X' :=
    (Scheme.homeoOfIso e).irreducibleSpace_iff.mpr inferInstance
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f'
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : AlgebraicGeometry.IsNoetherian X' := ⟨⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
    ((derivedLowerShriek.{u, 0} f' ((j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)).baseChange
      (IsPullback.of_hasPullback pr₂ s)) Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app _)))
  exact isZero_homology_derivedLowerShriek_of_isZero_restriction Λ Ω f'
    (topologicalKrullDim_affineLineFibre_le_one k Ω s) _ U' hU' _
    (isZero_restriction_inverseImage_tensor_of_range_subset Λ u' pr₁ jU U'
      (by rintro _ ⟨z, rfl⟩; exact z.2) P hP N hN) i hi

/-- **(L5, amplitude) `Hⁱ(Φ(P[0])) = 0` for `i ≠ 0`**, for a sheaf `P` of `Λ`-modules on `𝔸¹_k`
vanishing on a nonempty open `U`: on a geometric fibre of `pr₂` the integrand is supported on a
closed subscheme of dimension zero. -/
theorem isZero_homology_fourierTransform_of_isZero_inverseImage
    (j : CompactificationOf (Over.mk 𝔸f)) (P : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    {U : Scheme.{u}} (jU : U ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jU] [Nonempty U]
    (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj P)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj P))) := by
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j P i hneg
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj P ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj P) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app P) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso eT)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  refine isZero_homology_derivedLowerShriek_of_geometricFibres Λ pr₂ jP _ (Nat.card Λ) Nat.card_pos
    ?_ i fun y => ?_
  · rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, natCard_nsmul_id_etaleModules Λ G, Functor.map_zero]
  exact isZero_homology_derivedLowerShriek_affineLineFibre k Λ j P jU hP 𝓛
    (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀) _ _ i hpos

end Stacks.EtaleCohomology

end
