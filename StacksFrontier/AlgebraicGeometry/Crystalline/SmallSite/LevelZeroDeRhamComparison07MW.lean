module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelEnvelopeIdentification07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDeRhamNilpotentReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineDeRhamSectionsComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairConnection07J6
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH

/-!
# The de Rham complex of a crystal over a level `T(0)_e` is `M ⊗^∧_D Ω^*_D`

Fix a global crystalline situation with `X` and `S` affine, `p` nilpotent in `Γ(S, ⊤)`, a crystal
`ℱ` in quasi-coherent `𝒪_{X/S}`-modules and its pair `(M, ∇)` over the completed envelope `D` of
[Stacks, Lemma 60.17.3, Tag 07JG] (`...SmallSite.crystalPairConnModule`).  For every level `e` with
`p^{N+e} = 0` in the envelope `E(0)` (every large `e`), the reduction to the level is an
isomorphism, and this module proves that it identifies the completed de Rham complex
`M ⊗^∧_D Ω^*_D` with the complex of sections over `T(0)_e` of the de Rham complex
`ℱ ⊗ Ω^•_{X/S}` of [Stacks, Tag 07LM], differentials included:

`(crystalPairConnModule hp Fc).complex ≅ affineDeRhamSectionsComplex hF (levelAffineObject hp 0 e)`

(`...SmallSite.levelZeroDeRhamComplexIso`), the degree-`a` map being `m ⊗ ω ↦ m_e ⊗ ω_e`.

The differentials match because the connection of the pair is the canonical connection of
[Stacks, Tag 07J6] at the level (`...SmallSite.pairTensorLevel_crystalPairFunctor_nabla`), read
here in the spelling of the ring-level connection of the de Rham complex of sections
(`...SmallSite.reduceTensor_crystalPairConnModule_nabla`), and the comparison of forms
(`Crystalline.GlobalCrystallineSituation.formsHom`) respects the wedge and the de Rham
differential.  The abstract statement is `Crystalline.FormsData.ConnModule.reduceComplexHom`.

## Main results

* `...SmallSite.levelZeroFormsOneHom_crystalPairFormsEquiv` — the comparison of one-forms read on
  `Ω_D` is the reduction `Ω_D → Γ(T_e, Ω_{T_e/S,δ})` followed by [Stacks, Tag 07IY]/
  [Stacks, Tag 07J0].
* `...SmallSite.reduceTensor_crystalPairConnModule_nabla` — **the connection of the pair is the
  ring-level canonical connection at the level `T(0)_e`.**
* `...SmallSite.levelZeroDeRhamComplexIso` — **the isomorphism of complexes.**

## What is and is not proved

Everything stated is proved, for the default presentation of the system.  The morphism of
complexes exists for every level `e`; it is an isomorphism under the explicit hypothesis
`p^{N+e} = 0` in `E(0)`.  No tag attribute is placed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers Simplicial
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (hA : IsNilpotent (S.p : Γ(S.S.scheme, ⊤)))
  (Fc : QuasiCoherentCrystal S) {e : ℕ}
  (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
    wsEnvelope hp 0) = 0)

attribute [local instance] crysTopAlgebra wsEnvelopeTopAlgebra

instance isAffine_levelObj_target (n e : ℕ) :
    IsAffine (levelObj hp n e).obj.thickening.target.scheme :=
  isAffine_wholeSpaceSystem_target hp n e

/-- The ring map `D → Γ(T(0)_e, 𝒪)` of the comparison: the reduction, read on the completion. -/
abbrev levelZeroRingHom :
    (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring →+*
      GlobalCrystallineSituation.crysFormRing S (levelObj hp 0 e).obj :=
  formsRingHom (E := wsEnvelope hp 0) (exists_pow_eq_zero_wsEnvelope hp hA 0)
    (levelEnvelopeAlgHom hp 0 e)

/-- The ring map of the comparison is the reduction `pairLss` through which `D` acts on the
sections over the level. -/
theorem levelZeroRingHom_eq_pairLss (c : pairRing hp) :
    levelZeroRingHom hp hA (e := e) c = pairLss hp e c := by
  obtain ⟨y, rfl⟩ := (pAdicOfEquiv S.p (exists_pow_eq_zero_wsEnvelope hp hA 0)
    (wsEnvelope hp 0 : Type u)).surjective c
  rw [pAdicOfEquiv_apply]
  exact (formsRingHom_of _ _ y).trans (pairLss_pairOf hp e y).symm

/-- **The reduction `M → Γ(T(0)_e, ℱ)`**, as a map semilinear over `levelZeroRingHom`. -/
def levelZeroComponent :
    (crystalPairConnModule hp Fc).carrier →ₛₗ[levelZeroRingHom hp hA (e := e)]
      Fc.obj.val.obj (op (levelObj hp 0 e)) where
  toFun m := pairComponent hp Fc e m
  map_add' m m' := (pairComponent hp Fc e).map_add m m'
  map_smul' c m := by
    have h := (pairComponent hp Fc e).map_smul c m
    have h' := levelZeroRingHom_eq_pairLss hp hA (e := e) c
    exact h.trans (congrArg
      (fun r : GlobalCrystallineSituation.crysFormRing S (levelObj hp 0 e).obj ↦
        r • (id (pairComponent hp Fc e m) : Fc.obj.val.obj (op (levelObj hp 0 e)))) h'.symm)

/-- The reduction `M → Γ(T(0)_e, ℱ)` is the component of `M = lim_e Γ(T_e, ℱ)`. -/
theorem levelZeroComponent_apply (m : (crystalPairConnModule hp Fc).carrier) :
    levelZeroComponent hp hA Fc (e := e) m = pairComponent hp Fc e m :=
  rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
include hpe in
/-- `p^{N+e}` vanishes in `D` once it vanishes in `E(0)`. -/
theorem natCast_pow_eq_zero_pairRing :
    ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : pairRing hp) =
      0 := by
  have h := congrArg (pairOf hp) hpe
  rwa [map_natCast, map_zero] at h

include hpe in
/-- **The reduction `M → Γ(T(0)_e, ℱ)` is bijective** once `p^{N+e} = 0`: its kernel is
`p^{N+e} M`. -/
theorem bijective_levelZeroComponent :
    Function.Bijective (levelZeroComponent hp hA Fc (e := e)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm ↦ ?_, surjective_pairComponent hp Fc e⟩
  have hker : m ∈ LinearMap.ker (pairComponent hp Fc e) := hm
  have hbot : DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) = ⊥ := by
    rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, ← Nat.cast_pow,
      natCast_pow_eq_zero_pairRing hp hpe, Ideal.span_singleton_eq_bot]
  rw [ker_pairComponent, hbot, Submodule.bot_smul] at hker
  exact hker


/-- The comparison of one-forms `Ω̂¹_D → Ω_{X/S}(T(0)_e)` at the level `T(0)_e`. -/
abbrev levelZeroFormsOneHom :
    (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).Om 1
      →ₛₗ[levelZeroRingHom hp hA (e := e)]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op (levelObj hp 0 e).obj)) :=
  formsOneHom (exists_pow_eq_zero_wsEnvelope hp hA 0) (levelEnvelopeAlgHom hp 0 e)
    (isDPMorphism_levelEnvelopeAlgHom hp 0 e)

/-- The comparison of forms `Ω̂^a_D → Ω^a_{X/S}(T(0)_e)` in degree `a` at the level `T(0)_e`. -/
abbrev levelZeroFormsHom (a : ℕ) :
    (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).Om a
      →ₛₗ[levelZeroRingHom hp hA (e := e)]
      ⋀[GlobalCrystallineSituation.crysFormRing S (levelObj hp 0 e).obj]^a
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op (levelObj hp 0 e).obj)) :=
  formsHom (exists_pow_eq_zero_wsEnvelope hp hA 0) (levelEnvelopeAlgHom hp 0 e)
    (isDPMorphism_levelEnvelopeAlgHom hp 0 e) a

/-- **The comparison of one-forms, read on `Ω_D`, is the reduction to the level**: for every
`w ∈ Ω_D`, its image under `Ω_D ≃ Ω̂¹_D → Ω_{X/S}(T(0)_e)` is the image of its reduction
`Ω_D → Γ(T_e, Ω_{T_e/S,δ})` under [Stacks, Tag 07IY]/[Stacks, Tag 07J0], for any affine open `V`
of the base over which the level lies. -/
theorem levelZeroFormsOneHom_crystalPairFormsEquiv {V : S.S.scheme.Opens}
    (hVB : (⊤ : (levelObj hp 0 e).obj.thickening.target.scheme.Opens) ≤
      (levelObj hp 0 e).obj.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V) (w : pairForms hp) :
    levelZeroFormsOneHom hp hA (e := e) (crystalPairFormsEquiv hp w) =
      affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV (pairFormsLevel hp e w) := by
  let F : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u)
      (wsEnvelope hp 0).dividedPowers).Om 1 →+
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op (levelObj hp 0 e).obj)) :=
    (levelZeroFormsOneHom hp hA (e := e)).toAddMonoidHom
  let G : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u)
      (wsEnvelope hp 0).dividedPowers).Om 1 →+
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op (levelObj hp 0 e).obj)) :=
    ((affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV).toLinearMap.toAddMonoidHom.comp
      (pairFormsLevel hp e).toAddMonoidHom).comp
        (crystalPairFormsEquiv hp).symm.toLinearMap.toAddMonoidHom
  have hFG : F = G := by
    refine completedForms_addMonoidHom_ext S.p (exists_pow_eq_zero_wsEnvelope hp hA 0)
      (levelZeroRingHom hp hA (e := e)) F G
      (fun c x ↦ (levelZeroFormsOneHom hp hA (e := e)).map_smulₛₗ c x) (fun c x ↦ ?_) fun v ↦ ?_
    · refine (congrArg (fun w ↦ affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
        (pairFormsLevel hp e w)) ((crystalPairFormsEquiv hp).symm.map_smul c x)).trans ?_
      refine (congrArg (affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV)
        ((pairFormsLevel hp e).map_smul c ((crystalPairFormsEquiv hp).symm x))).trans ?_
      refine ((affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV).map_smul (pairLss hp e c)
        (pairFormsLevel hp e ((crystalPairFormsEquiv hp).symm x))).trans ?_
      exact congrArg (· • affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
        (pairFormsLevel hp e ((crystalPairFormsEquiv hp).symm x)))
        (levelZeroRingHom_eq_pairLss hp hA (e := e) c).symm
    · refine (congrArg (exteriorPower.oneEquiv _ _)
        (formsHom_ιMulti_d (exists_pow_eq_zero_wsEnvelope hp hA 0) (levelEnvelopeAlgHom hp 0 e)
          (isDPMorphism_levelEnvelopeAlgHom hp 0 e) 1 v)).trans ?_
      refine (exteriorPower.oneEquiv_ιMulti _).trans ?_
      have hι : letI := wsEnvelopeAlgebra hp;
          (exteriorPower.oneEquiv (wsEnvelope hp 0 : Type u)
            (dividedPowerDifferentials (A := ((affineSituation S hp).A : Type u))
              (wsEnvelope hp 0).dividedPowers)).symm
            (dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
              (wsEnvelope hp 0).dividedPowers (v 0)) =
          exteriorPower.ιMulti (wsEnvelope hp 0 : Type u) 1 fun j ↦
            dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
              (wsEnvelope hp 0).dividedPowers (v j) := by
        rw [LinearEquiv.symm_apply_eq, exteriorPower.oneEquiv_ιMulti]
      have hx := (tensorPowerDifferentialsFormsEquiv_of (affineSituation S hp)
        (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) 0
        (letI := wsEnvelopeAlgebra hp;
          dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
            (wsEnvelope hp 0).dividedPowers (v 0))).trans (congrArg (AdicCompletion.of _ _) hι)
      refine Eq.trans ?_ (congrArg (fun w ↦ affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
        (pairFormsLevel hp e ((crystalPairFormsEquiv hp).symm w))) hx)
      refine Eq.trans ?_ (congrArg (fun w ↦ affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
        (pairFormsLevel hp e w)) ((crystalPairFormsEquiv hp).symm_apply_apply _)).symm
      exact ((congrArg (affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV)
        ((pairFormsLevel_apply hp e _).trans ((pairFormsLevelFun_of hp e _).trans
          (envFormsLevel_dividedPowerDifferential hp e (v 0))))).trans
        (affineCrysOmegaEquiv_crysDerivation _ hVB hV _)).symm
  refine (DFunLike.congr_fun hFG (crystalPairFormsEquiv hp w)).trans ?_
  exact congrArg (fun w' ↦ affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
    (pairFormsLevel hp e w')) ((crystalPairFormsEquiv hp).symm_apply_apply w)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
include hA in
/-- `p` is nilpotent in the completed envelope `D`. -/
theorem exists_pow_eq_zero_presTowerRing :
    ∃ k, ((affineSituation S hp).p : (presTowerFormsData (affineSituation S hp)
      (wholeSpacePresentation S hp) 0).ring) ^ k = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_eq_zero_wsEnvelope hp hA 0
  refine ⟨k, ?_⟩
  have h := congrArg (algebraMap (wsEnvelope hp 0 : Type u)
    (AdicCompletion (pAdicIdeal (A := (wsEnvelope hp 0 : Type u)) S.p) (wsEnvelope hp 0))) hk
  rw [map_pow, map_natCast, map_zero] at h
  exact h

omit [IsAffine S.X] [IsAffine S.S.scheme] in
include hA in
/-- `p` is nilpotent in `D`, in the spelling of the pair of the crystal. -/
theorem exists_pow_eq_zero_pairRing : ∃ k, ((S.p : ℕ) : pairRing hp) ^ k = 0 :=
  exists_pow_eq_zero_presTowerRing hp hA

/-- **The connection of the pair of a crystal is the ring-level canonical connection at the level
`T(0)_e`**: for every `m ∈ M`, the canonical connection of [Stacks, Tag 07J6] over `T(0)_e`
(in the spelling of the de Rham complex of sections, `...SmallSite.AffineConnection.ringConnection`)
applied to the reduction of `m` is the reduction of `∇ m ∈ M ⊗^∧_D Ω̂¹_D`.  This is
`...SmallSite.pairTensorLevel_crystalPairFunctor_nabla` ([Stacks, Tag 07JG]) read through the
comparison of one-forms `levelZeroFormsOneHom_crystalPairFormsEquiv`. -/
theorem reduceTensor_crystalPairConnModule_nabla (m : (crystalPairConnModule hp Fc).carrier) :
    (ringConnection (levelAffineObject hp 0 e).top_le_preimage_baseOpen
        (levelAffineObject hp 0 e).isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine Fc.property.1
          (levelAffineObject hp 0 e))).toAddMonoidHom (levelZeroComponent hp hA Fc (e := e) m) =
      reduceTensor (levelZeroRingHom hp hA (e := e)) (exists_pow_eq_zero_presTowerRing hp hA)
        (levelZeroComponent hp hA Fc (e := e)) (levelZeroFormsOneHom hp hA (e := e))
        ((crystalPairConnModule hp Fc).nabla m) := by
  set hVB := (levelAffineObject hp 0 e).top_le_preimage_baseOpen
  set hV := (levelAffineObject hp 0 e).isAffineOpen_baseOpen
  have key : ∀ z : CompletedTensor S.p (pairRing hp) (pairForms hp)
      (wholeSpaceSections hp Fc ⦋0⦌),
      tensorFlipAdd Fc.obj (levelObj hp 0 e) hVB hV (pairTensorLevel hp Fc e z) =
      reduceTensor (levelZeroRingHom hp hA (e := e)) (exists_pow_eq_zero_presTowerRing hp hA)
        (levelZeroComponent hp hA Fc (e := e)) (levelZeroFormsOneHom hp hA (e := e))
        (CompletedConnection.completedTensorFormsMap (M := wholeSpaceSections hp Fc ⦋0⦌)
          (crystalPairFormsEquiv hp).toLinearMap z) := by
    intro z
    have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero (exists_pow_eq_zero_pairRing hp hA)
      (f := (tensorFlipAdd Fc.obj (levelObj hp 0 e) hVB hV).toAddMonoidHom.comp
        (pairTensorLevel hp Fc e).toAddMonoidHom)
      (g := (reduceTensor (levelZeroRingHom hp hA (e := e)) (exists_pow_eq_zero_presTowerRing hp hA)
        (levelZeroComponent hp hA Fc (e := e)) (levelZeroFormsOneHom hp hA (e := e))).comp
          (CompletedConnection.completedTensorFormsMap (M := wholeSpaceSections hp Fc ⦋0⦌)
            (crystalPairFormsEquiv hp).toLinearMap).toAddMonoidHom) fun m w ↦ ?_
    · exact DFunLike.congr_fun h z
    · have h1 : tensorFlipAdd Fc.obj (levelObj hp 0 e) hVB hV (pairTensorLevel hp Fc e
          (toCompletedTensor S.p (pairRing hp) (pairForms hp) _ (m ⊗ₜ w))) =
          levelZeroComponent hp hA Fc (e := e) m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S
            (levelObj hp 0 e).obj] affineCrysOmegaEquiv (levelObj hp 0 e).obj hVB hV
              (pairFormsLevel hp e w) :=
        congrArg (tensorFlipAdd Fc.obj (levelObj hp 0 e) hVB hV)
          (pairTensorLevel_toCompletedTensor_tmul hp Fc e m w)
      have h2 : CompletedConnection.completedTensorFormsMap (M := wholeSpaceSections hp Fc ⦋0⦌)
          (crystalPairFormsEquiv hp).toLinearMap
          (toCompletedTensor S.p (pairRing hp) (pairForms hp) _ (m ⊗ₜ w)) =
          toCompletedTensor S.p (pairRing hp) _ _ (m ⊗ₜ crystalPairFormsEquiv hp w) :=
        AdicCompletion.map_of _ _ _
      refine h1.trans (Eq.trans ?_ (congrArg (reduceTensor (levelZeroRingHom hp hA (e := e))
        (exists_pow_eq_zero_presTowerRing hp hA) (levelZeroComponent hp hA Fc (e := e))
        (levelZeroFormsOneHom hp hA (e := e))) h2).symm)
      refine Eq.trans ?_ (reduceTensor_of_tmul (levelZeroRingHom hp hA (e := e))
        (exists_pow_eq_zero_presTowerRing hp hA) (levelZeroComponent hp hA Fc (e := e))
        (levelZeroFormsOneHom hp hA (e := e)) m (crystalPairFormsEquiv hp w)).symm
      exact congrArg (fun y ↦ levelZeroComponent hp hA Fc (e := e) m ⊗ₜ[
        GlobalCrystallineSituation.crysFormRing S (levelObj hp 0 e).obj] y)
        (levelZeroFormsOneHom_crystalPairFormsEquiv hp hA hVB hV w).symm
  refine (congrArg (tensorFlipAdd Fc.obj (levelObj hp 0 e) hVB hV)
    (pairTensorLevel_crystalPairFunctor_nabla hp Fc e m).symm).trans ?_
  exact key _

/-- **The morphism of complexes `M ⊗^∧_D Ω^*_D → Γ(T(0)_e, ℱ ⊗ Ω^•_{X/S})`**, for every level
`e`: in degree `a` it is `m ⊗ ω ↦ m_e ⊗ ω_e`, and it commutes with the differentials.  It is an
isomorphism once `p^{N+e} = 0` in `E(0)` (`isIso_levelZeroDeRhamComplexHom`). -/
def levelZeroDeRhamComplexHom :
    (crystalPairConnModule hp Fc).complex ⟶
      affineDeRhamSectionsComplex Fc.property.1 (levelAffineObject hp 0 e) :=
  (crystalPairConnModule hp Fc).reduceComplexHom (levelZeroRingHom hp hA (e := e))
    (exists_pow_eq_zero_presTowerRing hp hA) (levelZeroFormsOneHom hp hA (e := e))
    (levelZeroFormsHom hp hA (e := e))
    (fun a ω η ↦ formsHom_wedge (exists_pow_eq_zero_wsEnvelope hp hA 0)
      (levelEnvelopeAlgHom hp 0 e) (isDPMorphism_levelEnvelopeAlgHom hp 0 e) a ω η)
    (fun a ↦ (crysDeRhamComplex S).differential a (levelObj hp 0 e).obj)
    (fun a ω ↦ formsHom_deRham (exists_pow_eq_zero_wsEnvelope hp hA 0)
      (levelEnvelopeAlgHom hp 0 e) (isDPMorphism_levelEnvelopeAlgHom hp 0 e) a ω)
    (levelZeroComponent hp hA Fc (e := e))
    (ringConnection (levelAffineObject hp 0 e).top_le_preimage_baseOpen
        (levelAffineObject hp 0 e).isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine Fc.property.1
          (levelAffineObject hp 0 e))).toAddMonoidHom
    (reduceTensor_crystalPairConnModule_nabla hp hA Fc)
    (fun a ↦ extDiff (levelAffineObject hp 0 e).top_le_preimage_baseOpen
      (levelAffineObject hp 0 e).isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine Fc.property.1 (levelAffineObject hp 0 e)) a)
    (fun a n ω ↦ extDiff_tmul _ _ _ a n ω)
    (fun a ↦ AddMonoidHom.ext fun x ↦ extDiff_comp_extDiff _ _ _
      (injective_crysSecondExtensionSectionsMap_affine Fc.property.1
        (levelAffineObject hp 0 e)) a x)

/-- The degree-`a` component of `levelZeroDeRhamComplexHom` is `m ⊗ ω ↦ m_e ⊗ ω_e`. -/
theorem levelZeroDeRhamComplexHom_f_of_tmul (a : ℕ) (m : (crystalPairConnModule hp Fc).carrier)
    (ω : (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).Om a) :
    ((levelZeroDeRhamComplexHom hp hA Fc (e := e)).f a).hom
        (toCompletedTensor (affineSituation S hp).p
          (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
          ((presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).Om a)
          (crystalPairConnModule hp Fc).carrier (m ⊗ₜ ω)) =
      levelZeroComponent hp hA Fc (e := e) m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S
        (levelObj hp 0 e).obj] levelZeroFormsHom hp hA (e := e) a ω :=
  reduceTensor_of_tmul (levelZeroRingHom hp hA (e := e)) (exists_pow_eq_zero_presTowerRing hp hA)
    (levelZeroComponent hp hA Fc (e := e)) (levelZeroFormsHom hp hA (e := e) a) m ω

include hpe in
/-- **The morphism of complexes `levelZeroDeRhamComplexHom` is an isomorphism** once
`p^{N+e} = 0` in `E(0)`: the ring map, the reduction `M → Γ(T(0)_e, ℱ)` and every comparison of
forms are bijective. -/
theorem isIso_levelZeroDeRhamComplexHom : IsIso (levelZeroDeRhamComplexHom hp hA Fc (e := e)) :=
  (crystalPairConnModule hp Fc).isIso_reduceComplexHom (levelZeroRingHom hp hA (e := e))
    (exists_pow_eq_zero_presTowerRing hp hA) _ _ _ _ _ _ _ _ _ _ _
    (formsRingHom_bijective (exists_pow_eq_zero_wsEnvelope hp hA 0) (levelEnvelopeAlgHom hp 0 e)
      (bijective_envLevelMap_of_pow_eq_zero hpe))
    (bijective_levelZeroComponent hp hA Fc hpe)
    (fun a ↦ formsHom_bijective (exists_pow_eq_zero_wsEnvelope hp hA 0)
      (levelEnvelopeAlgHom hp 0 e) (isDPMorphism_levelEnvelopeAlgHom hp 0 e)
      (levelEnvelopeAlgHomInv hpe) (isDPMorphism_levelEnvelopeAlgHomInv hpe)
      (levelEnvelopeAlgHomInv_comp hpe) (comp_levelEnvelopeAlgHomInv hpe) a)

/-- **The de Rham complex of a crystal over the level `T(0)_e` is `M ⊗^∧_D Ω^*_D`**, for a level
with `p^{N+e} = 0` in `E(0)`. -/
def levelZeroDeRhamComplexIso :
    (crystalPairConnModule hp Fc).complex ≅
      affineDeRhamSectionsComplex Fc.property.1 (levelAffineObject hp 0 e) :=
  haveI := isIso_levelZeroDeRhamComplexHom hp hA Fc hpe
  asIso (levelZeroDeRhamComplexHom hp hA Fc (e := e))

end Crystalline.GlobalCrystallineSituation.SmallSite

end
