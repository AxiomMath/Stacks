module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierNoPunctualSectionsDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportDegreeZeroNoPunctual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageNoPunctualSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.NoPunctualSectionsTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierKernelInverse
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# The Fourier transform of a sheaf without punctual sections has no `H⁰`

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a sheaf `H` on `𝔸¹_k` and a
nonempty open `j : V ⟶ 𝔸¹_k` with `j⁻¹ H` locally constant with finite values and
`H ⟶ j_* j⁻¹ H` a monomorphism, `H⁰(Φ(H[0])) = 0`
(`Stacks.EtaleCohomology.fourierNoPunctualSectionsDegreeZeroInput`).

By proper base change the vanishing is checked on the geometric fibres `X' ≅ 𝔸¹_Ω` of `pr₂`
(`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`), where the
integrand is `G' = u⁻¹(pr₁⁻¹ H ⊗ μ⁻¹ L)`, `u : X' ⟶ 𝔸¹ ×_k 𝔸¹` the fibre inclusion. Write
`g = u ≫ pr₁ : X' ⟶ 𝔸¹_k` (the base change of `Spec Ω ⟶ Spec k`, surjective) and `V' = g⁻¹ V`,
a nonempty, hence dense and connected, open of the irreducible `X'`. Then:

* `g⁻¹ H` has no sections supported off `V'`
  (`Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app_inverseImage`, a germ argument:
  `g` is not of finite presentation and Tag 0EYS does not apply);
* so has `G'`: the Fourier kernel has an étale-locally free inverse `L'`
  (`Stacks.EtaleCohomology.exists_fourierKernel_inverse`), `G' ⊗ u⁻¹ L' ≅ g⁻¹ H`, and the property
  descends along invertible twists
  (`Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app_of_tensor_iso`);
* `G'|_{V'}` is locally constant, as a tensor product of a locally constant and a locally free
  sheaf (`Stacks.EtaleCohomology.isLocallyConstantWith_tensor`).

Hence `H⁰_c(X', G') = 0`
(`Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_mono_unit`, `X'` being
connected and not proper over `Ω`).

This is the input (L1) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.fourierNoPunctualSectionsDegreeZeroInput`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits etaleModuleInverseImageSheafPullbackMonoidal
  hasSheafify_etaleModules_fourierKernel hasSheafify_over_etaleModules_locallyConstantSections

/-- A pullback of a nonempty scheme along a surjective morphism is nonempty. -/
theorem nonempty_pullback_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Nonempty X] [Surjective g] : Nonempty ↥(pullback f g) := by
  obtain ⟨v⟩ := ‹Nonempty X›
  obtain ⟨x', hx'⟩ := g.surjective (f v)
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v x' hx'.symm
  exact ⟨p⟩

/-- If `f⁻¹ N` is locally constant, so is the inverse image of `g⁻¹ N` along the base change
`pullback f g ⟶ Y` of `f`. -/
theorem isLocallyConstantWith_inverseImage_pullback_snd (Λ : Type) [CommRing Λ]
    (Q : ModuleCat.{u + 1} Λ → Prop) {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    {N : EtaleModules.{u, 0} Λ Z}
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ f).obj N)) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ (pullback f g).smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd f g)).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj N)) :=
  isLocallyConstantWith_of_iso Λ Q
    (((etaleModuleInverseImageCompIso.{u, 0} Λ (pullback.fst f g) f).app N).symm ≪≫
      eqToIso (congrArg (fun φ => (etaleModuleInverseImage.{u, 0} Λ φ).obj N)
        pullback.condition) ≪≫
      (etaleModuleInverseImageCompIso.{u, 0} Λ (pullback.snd f g) g).app N)
    (isLocallyConstantWith_inverseImage Λ Q (pullback.fst f g) hN)

section Fibre

variable (k : Type u) [Field k] [Fintype k]

local notation "𝔸f" => affineLineStructureMap k

/-- **The Fourier integrand pulled back along any `u : X ⟶ 𝔸¹ ×_k 𝔸¹`** inherits from
`(u ≫ pr₁)⁻¹ H` the absence of sections supported off `V' = (u ≫ pr₁)⁻¹ V`, and is locally
constant on `V'`. -/
theorem mono_unit_app_and_isLocallyConstantWith_fourierIntegrand (Λ : Type) [CommRing Λ]
    [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {V : Scheme.{u}}
    (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV]
    (hloc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj H))
    {X : Scheme.{u}} (u' : X ⟶ pullback 𝔸f 𝔸f)
    (hA : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ
      (pullback.snd jV (u' ≫ pullback.fst 𝔸f 𝔸f))).unit.app
        ((etaleModuleInverseImage.{u, 0} Λ (u' ≫ pullback.fst 𝔸f 𝔸f)).obj H))) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ
      (pullback.snd jV (u' ≫ pullback.fst 𝔸f 𝔸f))).unit.app
        ((etaleModuleInverseImage.{u, 0} Λ u').obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj H ⊗
            (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
              (affineLineArtinSchreierSheaf k Λ ψ B p₀)))) ∧
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ
      (pullback jV (u' ≫ pullback.fst 𝔸f 𝔸f)).smallEtaleTopology
      (fun E => ∃ E₁ E₂, (fun E : ModuleCat.{u + 1} Λ => Module.Finite Λ E) E₁ ∧
        (fun E : ModuleCat.{u + 1} Λ => Module.Free Λ E ∧ Module.Finite Λ E) E₂ ∧
          E = E₁ ⊗ E₂)
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd jV (u' ≫ pullback.fst 𝔸f 𝔸f))).obj
        ((etaleModuleInverseImage.{u, 0} Λ u').obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj H ⊗
            (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
              (affineLineArtinSchreierSheaf k Λ ψ B p₀)))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj H ⊗ 𝓛
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  obtain ⟨𝓛', h𝓛', ⟨e₁⟩, ⟨e₂⟩⟩ := exists_fourierKernel_inverse Λ k ψ B p₀
  let g := u' ≫ pr₁
  let i := pullback.snd jV g
  let I := etaleModuleInverseImage.{u, 0} Λ u'
  let J := etaleModuleInverseImage.{u, 0} Λ i
  obtain ⟨e⟩ := nonempty_inverseImage_tensor_iso_tensorUnit Λ u' e₂
  let a : I.obj G ⊗ I.obj 𝓛' ≅ (etaleModuleInverseImage.{u, 0} Λ g).obj H :=
    Functor.Monoidal.μIso I G 𝓛' ≪≫
      I.mapIso ((α_ _ _ _) ≪≫ whiskerLeftIso _ e₁ ≪≫ ρ_ _) ≪≫
      ((etaleModuleInverseImageCompIso.{u, 0} Λ u' pr₁).app H).symm
  have h𝓛u := isLocallyFreeEtaleModule_inverseImage Λ u' h𝓛
  refine ⟨mono_etaleModuleInverseImageAdj_unit_app_of_tensor_iso Λ i h𝓛u
      (isLocallyFreeEtaleModule_inverseImage Λ u' h𝓛') e a hA,
    isLocallyConstantWith_of_iso Λ _ ?_ (isLocallyConstantWith_tensor Λ _ _
      (isLocallyConstantWith_inverseImage_pullback_snd Λ _ jV g hloc)
      (isLocallyFreeEtaleModule_inverseImage Λ i h𝓛u))⟩
  -- `J (g⁻¹ H) ⊗ J (u'⁻¹ 𝓛) ≅ J (u'⁻¹ G)`
  exact Functor.Monoidal.μIso J _ _ ≪≫
    J.mapIso (whiskerRightIso a.symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ e ≪≫ ρ_ _)

/-- **The Fourier integrand has no `H⁰_c` on a geometric fibre of `pr₂`**, for a sheaf `H` on
`𝔸¹_k` without sections supported off a nonempty open on which it is locally constant with
finite values. -/
theorem isZero_homology_zero_derivedLowerShriek_fourierIntegrand_fibre (Λ : Type) [CommRing Λ]
    [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X))
    (j : CompactificationOf (Over.mk 𝔸f))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {V : Scheme.{u}}
    (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hloc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj H))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} (pullback.snd (pullback.snd 𝔸f 𝔸f) s)
        ((j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)).baseChange
          (IsPullback.of_hasPullback (pullback.snd 𝔸f 𝔸f) s)) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst (pullback.snd 𝔸f 𝔸f) s)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj H ⊗
              (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
                (affineLineArtinSchreierSheaf k Λ ψ B p₀)))))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj H ⊗
    (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  obtain ⟨_, hnp⟩ := connectedSpace_affineLineFibre_and_not_isProper k Ω s
  let j' := jP.baseChange (IsPullback.of_hasPullback pr₂ s)
  -- `g = u' ≫ pr₁` is the base change of `Spec Ω ⟶ Spec k`, hence surjective
  let g := u' ≫ pr₁
  have : Surjective (s ≫ 𝔸f) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Surjective g := MorphismProperty.of_isPullback (P := @Surjective)
    ((IsPullback.of_hasPullback pr₂ s).paste_horiz (IsPullback.of_hasPullback 𝔸f 𝔸f)).flip
    inferInstance
  -- the open `V' = g⁻¹ V` of the irreducible fibre
  let i := pullback.snd jV g
  have := nonempty_pullback_of_surjective jV g
  obtain ⟨eA, -⟩ := nonempty_affineLineFibre_iso k s
  have : IrreducibleSpace ↥(pullback pr₂ s) := by
    have : Nonempty ↥(pullback pr₂ s) := ⟨i (Classical.arbitrary _)⟩
    exact eA.hom.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace ↥(pullback jV g) := i.isOpenEmbedding.irreducibleSpace
  have hd : Dense (Set.range i) := i.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  -- `g⁻¹ H` has no sections supported off `V'`
  have : IsNormal (Spec (.of (Polynomial k))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed (Polynomial k))
  -- so has the integrand `u'⁻¹ G`
  -- `u'⁻¹ G` is locally constant on `V'`
  obtain ⟨hη', hG⟩ := mono_unit_app_and_isLocallyConstantWith_fourierIntegrand k Λ ψ B p₀ H jV
    hloc u' (mono_etaleModuleInverseImageAdj_unit_app_inverseImage Λ jV _ H hloc hη g hd)
  refine IsZero.of_iso (isZero_homology_zero_derivedLowerShriek_of_mono_unit Λ _ Ω f' j'
    (j'.not_isClosed_range_immersion_of_not_isProper hnp) i hd _ hG hη')
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app G)))

end Fibre

/-- **(L1) `H⁰(Φ(H[0])) = 0` for a sheaf `H` on `𝔸¹_k` without sections supported off a nonempty
open on which it is locally constant with finite values.** -/
theorem fourierNoPunctualSectionsDegreeZeroInput :
    FourierNoPunctualSectionsDegreeZeroInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ j H V jV _ _ hloc hη
  let 𝔸f := affineLineStructureMap k
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj H ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  -- `Φ(H[0]) ≅ R pr₂!(G[0])`
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app H) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso eT)
  -- finiteness and separation of `pr₂`
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  refine isZero_homology_derivedLowerShriek_of_geometricFibres Λ pr₂ jP _ (Nat.card Λ)
    Nat.card_pos ?_ 0 fun y => isZero_homology_zero_derivedLowerShriek_fourierIntegrand_fibre
      k Λ ψ B p₀ j H jV hloc hη _ (GeometricPoint.ofPoint (Spec (.of (Polynomial k))) y).hom
  rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
    ← Functor.map_nsmul, natCard_nsmul_id_etaleModules Λ G, Functor.map_zero]

end Stacks.EtaleCohomology

end
