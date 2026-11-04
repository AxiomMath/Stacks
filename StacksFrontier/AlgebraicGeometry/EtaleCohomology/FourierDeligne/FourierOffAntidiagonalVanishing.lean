module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeKernelVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierOffAntidiagonalCoordinates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.KernelSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The kernel of the composite of two Fourier transforms vanishes off the antidiagonal

On `Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u` with `q₁ = x`, `q₃ = u` and the kernel `𝓜 = s⁻¹ L_ψ`,
`s = t(x + u)`, the restriction of `q₁⁻¹ K ⊗ 𝓜` to `Q_U = {x + u ≠ 0}` has no compactly supported
cohomology along `q₃`:

`R(q₃|_{Q_U})_!((q₁⁻¹ K ⊗ 𝓜)|_{Q_U}) = 0`,

for `K` a sheaf on `𝔸¹` with finite geometric stalks. In the coordinates `t' = t(x + u)` of
`Stacks.EtaleCohomology.isPullback_fourierOffAntidiagonal`, `Q_U` is the affine line over
`W = Spec k[x, u]_{x+u}` with coordinate `s`, `q₃|_{Q_U}` factors as `Q_U ⟶ W ⟶ 𝔸¹_u` and
`(q₁⁻¹ K ⊗ 𝓜)|_{Q_U} = a⁻¹(x⁻¹ K) ⊗ s⁻¹ L`; by Tag 0F7J it suffices that
`R a_!(a⁻¹(x⁻¹ K) ⊗ s⁻¹ L) = 0`, which is
`isZero_derivedLowerShriek_inverseImage_tensor_affineLineArtinSchreierSheaf`. This is the
hypothesis `hU` of `nonempty_derivedLowerShriek_tensor_iso_closed_of_isZero_open`.

## Main results

* `Stacks.EtaleCohomology.isZero_derivedLowerShriek_of_eq`: the vanishing of `Rf_! N` does not
  depend on the presentation of `f` or on the compactification.
* `Stacks.EtaleCohomology.isZero_derivedLowerShriek_fourierOffAntidiagonal`:
  `R(q₃|_{Q_U})_!((q₁⁻¹ K ⊗ 𝓜)|_{Q_U}) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- `Rf_! N = 0` does not depend on the presentation of `f` or on the compactification, for `N`
with torsion cohomology sheaves (Tag 0F7I). -/
theorem isZero_derivedLowerShriek_of_eq (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] {f f' : X ⟶ Y} (h : f = f') [IsSeparated f'] [LocallyOfFiniteType f']
    [QuasiCompact f'] (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hN : isTorsionPlus.{u, 0} Λ X N)
    (H : IsZero ((derivedLowerShriek.{u, 0} f' j' Λ).obj N)) :
    IsZero ((derivedLowerShriek.{u, 0} f j Λ).obj N) := by
  subst h
  exact H.of_iso ((derivedLowerShriekCompactificationIso f j j' Λ).app ⟨N, hN⟩)

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

omit [Fintype k] in
/-- `k[x, u]_{x + u}` is of finite type over `k`. -/
theorem finiteType_fourierOffAntidiagonalBase :
    Algebra.FiniteType k (Localization.Away
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) :=
  have : Algebra.FiniteType (MvPolynomial (Fin 2) k)
      (Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) :=
    IsLocalization.finiteType_of_monoid_fg
      (Submonoid.powers (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) _
  Algebra.FiniteType.trans (S := MvPolynomial (Fin 2) k) inferInstance inferInstance

omit [Fintype k] in
/-- The coordinate `u : W ⟶ 𝔸¹_k` followed by the structure morphism of `𝔸¹_k` is the structure
morphism of `W = Spec k[x, u]_{x+u}`. -/
theorem fourierOffAntidiagonalBaseU_comp_structureMap :
    fourierOffAntidiagonalBaseU k ≫ 𝔸f = fourierOffAntidiagonalBaseStructure k := by
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  show Polynomial.aeval _ (algebraMap k (Polynomial k) c) = _
  rw [AlgHom.commutes]
  rfl

include ψ in
/-- **`R(q₃|_{Q_U})_!((q₁⁻¹ K ⊗ s⁻¹ L)|_{Q_U}) = 0`** for a sheaf `K` on `𝔸¹_k` with finite
geometric stalks: in the coordinates `t' = t(x + u)` it is the vanishing of the Fourier kernel on
the relative affine line `Q_U ⟶ W = Spec k[x, u]_{x+u}`, and `q₃` factors through `W` (Tag 0F7J).
-/
theorem isZero_derivedLowerShriek_fourierOffAntidiagonal (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ))
    [QuasiCompact (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)]
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (h𝓜 : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (fourierTripleKernelMap k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) :
    IsZero ((derivedLowerShriek.{u, 0}
        (fourierOffAntidiagonalι k ≫ tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)
        (jQ.restrictOpen (fourierOffAntidiagonalι k)) Λ).obj
      ((etaleModuleRestriction.{u, 0} Λ (fourierOffAntidiagonalι k)).mapDerivedCategoryPlus.obj
        ((etaleModuleDerivedTensorRight Λ _ h𝓜).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
            (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f)).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) := by
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let jU := fourierOffAntidiagonalι k
  let s := fourierTripleKernelMap k
  let q₁ := tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f
  let a := fourierOffAntidiagonalProj k
  let xW := fourierOffAntidiagonalBaseX k
  let uW := fourierOffAntidiagonalBaseU k
  let πW := fourierOffAntidiagonalBaseStructure k
  let 𝓜 := (etaleModuleInverseImage.{u, 0} Λ s).obj L
  let I := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => etaleModuleInverseImage.{u, 0} Λ f
  have sqP := isPullback_fourierOffAntidiagonal k
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType a :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqP inferInstance
  have : IsSeparated a := MorphismProperty.of_isPullback (P := @IsSeparated) sqP inferInstance
  have : QuasiCompact a := MorphismProperty.of_isPullback (P := @QuasiCompact) sqP inferInstance
  have : CompactSpace (fourierOffAntidiagonal k) := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace (fourierOffAntidiagonal k) := quasiSeparatedSpace_of_quasiSeparated a
  have : Algebra.FiniteType k _ := finiteType_fourierOffAntidiagonalBase k
  have : LocallyOfFiniteType πW := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (uW ≫ 𝔸f) := by
    rw [fourierOffAntidiagonalBaseU_comp_structureMap]
    infer_instance
  have : LocallyOfFiniteType uW :=
    LocallyOfFiniteType.of_comp (show LocallyOfFiniteType (uW ≫ 𝔸f) from inferInstance)
  have : QuasiCompact uW := quasiCompact_of_compactSpace uW
  let j : CompactificationOf (Over.mk 𝔸f) := (IsCofiltered.nonempty).some
  let ju : CompactificationOf (Over.mk uW) := (IsCofiltered.nonempty).some
  let jau : CompactificationOf (Over.mk (a ≫ uW)) := (IsCofiltered.nonempty).some
  let S := (I a).obj ((I xW).obj F) ⊗ (I (jU ≫ s)).obj L
  have hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (w : Spec (.of Ω) ⟶ fourierOffAntidiagonalBase k),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj ((I w).obj ((I xW).obj F))) :=
    fun Ω _ _ w => by
      have := hF Ω (w ≫ xW)
      exact Finite.of_equiv _ ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).mapIso
        ((etaleModuleInverseImageCompIso Λ w xW).app F)).toLinearEquiv.toEquiv
  have hK : IsZero ((derivedLowerShriek.{u, 0} a (j.baseChange sqP) Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj S)) :=
    isZero_derivedLowerShriek_inverseImage_tensor_affineLineArtinSchreierSheaf k Λ ψ B p₀ hψ hq j
      πW sqP _ hG
  have hcomp : IsZero ((derivedLowerShriek.{u, 0} (a ≫ uW) jau Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj S)) :=
    (Functor.map_isZero (derivedLowerShriek.{u, 0} uW ju Λ) hK).of_iso
      ((derivedLowerShriekCompIso Λ a uW (j.baseChange sqP) ju jau).app
        ⟨_, isTorsionPlus_of_finite Λ _ _⟩)
  have := h𝓜.1
  have := h𝓜.2.1
  have := h𝓜.2.2
  let eS : (etaleModuleRestriction.{u, 0} Λ jU).obj ((I q₁).obj F ⊗ 𝓜) ≅ S :=
    ((etaleModuleInverseImageRestrictionIso Λ jU).app _).symm ≪≫
      (Functor.Monoidal.μIso (I jU) _ _).symm ≪≫
      ((((etaleModuleInverseImageCompIso Λ jU q₁).app F).symm ≪≫
          eqToIso (by rw [fourierOffAntidiagonalι_comp_x]) ≪≫
          (etaleModuleInverseImageCompIso Λ a xW).app F) ⊗ᵢ
        ((etaleModuleInverseImageCompIso Λ jU s).app L).symm)
  let eN := (etaleModuleRestriction.{u, 0} Λ jU).mapDerivedCategoryPlus.mapIso
      ((etaleModuleDerivedTensorRight Λ _ h𝓜).mapIso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I q₁) 0).app F) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓜) 0).app _) ≪≫
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
      (etaleModuleRestriction.{u, 0} Λ jU) 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso eS
  exact isZero_derivedLowerShriek_of_eq Λ (fourierOffAntidiagonalι_comp_u k) _ jau _
    (isTorsionPlus_of_finite Λ _ _)
    (hcomp.of_iso ((derivedLowerShriek.{u, 0} (a ≫ uW) jau Λ).mapIso eN))

end Stacks.EtaleCohomology

end
