module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierPointTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportDegreeZeroLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyFreeTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineUnitCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologyGeometricFibres
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic

/-!
# The Fourier transform of a locally free sheaf has no `H⁰`

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ`, `L = L_ψ(x)` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L)` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`, `μ(x, t) = xt`. For a sheaf `F` on `𝔸¹_k` which is étale-locally free of finite
rank, `H⁰(Φ(F[0])) = 0`.

## Main results

* `AlgebraicGeometry.CompactificationOf.not_isClosed_range_immersion_of_not_isProper`: a
  compactification of a non-proper `S`-scheme has non-closed interior.
* `Stacks.EtaleCohomology.isPullback_affineLineBaseChange_of_hom`: `𝔸¹_k ×_k T ≅ 𝔸¹_T`.
* `Stacks.EtaleCohomology.connectedSpace_affineLineFibre_and_not_isProper`: the geometric fibres
  of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` are connected and not proper.
* `Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule`:
  `H⁰(Φ(F[0])) = 0` for `F` étale-locally free of finite rank.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
last statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace AlgebraicGeometry.CompactificationOf

/-- **A compactification of a non-proper `S`-scheme has non-closed interior**: if `f : X ⟶ S` is
not proper, the image of `X` in any compactification of `f` is not closed. -/
theorem not_isClosed_range_immersion_of_not_isProper {S X : Scheme.{u}} {f : X ⟶ S}
    (J : CompactificationOf (Over.mk f)) (hf : ¬ IsProper f) :
    ¬ IsClosed (Set.range J.immersion) := by
  intro h
  have : IsClosedImmersion J.immersion := IsClosedImmersion.of_isPreimmersion J.immersion h
  have hw : J.immersion ≫ J.toBase = f := Over.w J.obj.hom
  exact hf (hw ▸ inferInstance)

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

section Geometry

/-- **The base change of `𝔸¹_k` along any `t : T ⟶ Spec k` is `𝔸¹_T`.** -/
theorem isPullback_affineLineBaseChange_of_hom {T : Scheme.{u}} (t : T ⟶ Spec (.of k)) :
    IsPullback (AffineSpace.map (ULift.{u} (Fin 1)) t ≫ (affineLineIsoAffineSpace k).inv)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) 𝔸f t := by
  have h := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) t
  have hsq : IsPullback (affineLineIsoAffineSpace k).inv
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) 𝔸f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, Iso.inv_comp_eq, affineLineIsoAffineSpace_hom_over]⟩
  simpa using h.paste_horiz hsq

/-- **The fibre of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` over `s : T ⟶ 𝔸¹_k` is `𝔸¹_T`**, over `T`. -/
theorem nonempty_affineLineFibre_iso {T : Scheme.{u}} (s : T ⟶ Spec (.of (Polynomial k))) :
    ∃ e : pullback (pullback.snd 𝔸f 𝔸f) s ≅ AffineSpace (ULift.{u} (Fin 1)) T,
      e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) = pullback.snd (pullback.snd 𝔸f 𝔸f) s := by
  have h₁ := IsPullback.of_hasPullback (pullback.snd 𝔸f 𝔸f) s
  have h₂ := IsPullback.of_hasPullback 𝔸f 𝔸f
  have h := h₁.paste_horiz h₂
  exact ⟨h.isoIsPullback _ _ (isPullback_affineLineBaseChange_of_hom k (s ≫ 𝔸f)),
    IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

/-- **The geometric fibres of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` are connected and not proper.** -/
theorem connectedSpace_affineLineFibre_and_not_isProper (Ω : Type u) [Field Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    ConnectedSpace ↥(pullback (pullback.snd 𝔸f 𝔸f) s) ∧
      ¬ IsProper (pullback.snd (pullback.snd 𝔸f 𝔸f) s) := by
  obtain ⟨e, he⟩ := nonempty_affineLineFibre_iso k s
  refine ⟨?_, fun hP => ?_⟩
  · let h := Scheme.homeoOfIso e.symm
    exact h.surjective.connectedSpace h.continuous
  · refine not_isProper_affineSpace Ω (ULift.{u} (Fin 1)) ?_
    rw [← (Iso.inv_comp_eq e).2 he.symm]
    infer_instance

end Geometry

section Transform

variable [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

omit [Finite Λ] in
/-- `#Λ` kills every sheaf of `Λ`-modules, for a finite ring `Λ`. -/
theorem natCard_nsmul_id_etaleModules {X : Scheme.{u}} (G : EtaleModules.{u, 0} Λ X) :
    Nat.card Λ • 𝟙 G = 0 := by
  apply Sheaf.hom_ext
  ext V x
  show Nat.card Λ • x = 0
  rw [← one_smul Λ x, ← smul_assoc, card_nsmul_eq_zero', zero_smul]

/-- **The Fourier transform of a locally free sheaf has no `H⁰`: `H⁰(Φ(F[0])) = 0` for `F`
étale-locally free of finite rank on `𝔸¹_k`.** -/
theorem isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule
    (j : CompactificationOf (Over.mk 𝔸f)) (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : IsLocallyFreeEtaleModule Λ F) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj L
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj F ⊗ 𝓛
  have hG : IsLocallyFreeEtaleModule Λ G :=
    isLocallyFreeEtaleModule_tensor Λ (isLocallyFreeEtaleModule_inverseImage Λ pr₁ hF) h𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app F) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso eT)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  refine isZero_homology_derivedLowerShriek_of_geometricFibres Λ pr₂ jP _ (Nat.card Λ)
    Nat.card_pos ?_ 0 fun y => ?_
  · rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, natCard_nsmul_id_etaleModules Λ G, Functor.map_zero]
  let s := (GeometricPoint.ofPoint (Spec (.of (Polynomial k))) y).hom
  let Ω := (GeometricPoint.ofPoint (Spec (.of (Polynomial k))) y).residueField
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  obtain ⟨_, hnp⟩ := connectedSpace_affineLineFibre_and_not_isProper k Ω s
  let j' := jP.baseChange (IsPullback.of_hasPullback pr₂ s)
  have hj : ¬ IsClosed (Set.range j'.immersion) :=
    j'.not_isClosed_range_immersion_of_not_isProper hnp
  have hG' := isLocallyFreeEtaleModule_inverseImage Λ u' hG
  refine IsZero.of_iso
    (isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith Λ _ Ω f' j' hj _ hG')
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app G)))

end Transform

end Stacks.EtaleCohomology

end
