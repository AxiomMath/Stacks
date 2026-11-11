module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingDeRhamComparison07MW

/-!
# The restriction of the de Rham complex of a crystal from a level to an affine smooth lifting

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`) with `X`, `S` and `Y` affine,
let `ℱ` be a crystal in quasi-coherent modules on `Cris(X/S)` with de Rham complex
`K = ℱ ⊗ Ω^•_{X/S}` of [Stacks, Tag 07LM] (`...SmallSite.crystalDeRhamSheafData`).  For every
large level `e` the chosen morphism `ψ : (X, Y, γ) ⟶ T(0)_e` (`...Situation07MW.levelHom`)
induces a quasi-isomorphism of sections `K^•(T(0)_e) → K^•(X, Y, γ)`
(`...Situation07MW.quasiIso_levelRestriction`).

The proof is the commutative square

`M ⊗^∧_D Ω^*_D ──≅──> Γ(T(0)_e, ℱ) ⊗ ⋀^• Ω_{X/S}(T(0)_e)`
`      │ base change along a                    │ restriction along ψ`
`M' ⊗^∧_{D'} Ω^*_{D'} ──≅──> Γ(Y, ℱ) ⊗ ⋀^• Ω_{X/S}(Y)`

(`...Situation07MW.levelZeroDeRhamComplexHom_comp_affineDeRhamSectionsMap`) whose horizontal maps
are isomorphisms (`...SmallSite.isIso_levelZeroDeRhamComplexHom`,
`...Situation07MW.isIso_liftingDeRhamComplexHom`) and whose left map is a quasi-isomorphism by
[Stacks, Lemma 60.21.4, Tag 07LH] (`...Situation07MW.quasiIso_baseChangeHom_levelEnvelopeMap`),
followed by the identification of the explicit complexes with the sections of `K`
(`...SmallSite.quasiIso_complex_restriction`).

## Main results

* `Situation07MW.quasiIso_affineDeRhamSectionsMap_levelAffineHom` — the restriction of the
  explicit complexes along `ψ` is a quasi-isomorphism.
* `Situation07MW.exists_levelBound_pow_eq_zero` — every large `e` is past `levelBound` and has
  `p^{N+e} = 0` in `E(0)`.
* `Situation07MW.quasiIso_levelRestriction`, `Situation07MW.exists_quasiIso_levelRestriction` —
  the restriction of the `ℤ`-indexed de Rham complex along `ψ` is a quasi-isomorphism.

## What is and is not proved

Everything stated is proved.  This is a step towards part (3) of [Stacks, Tag 07MW], which is not
proved here; no tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers Simplicial
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (T : Situation07MW S) [IsAffine T.Y]

attribute [local instance] crysTopAlgebra wsEnvelopeTopAlgebra tensorPowerEnvelopeAlgebraInstance
  presentationEnvelopeAlgebraInst Situation07MW.liftingAlgebra liftingEnvelopeTopAlgebra

variable (Fc : QuasiCoherentCrystal S)

/-- **The square of comparisons**: reducing `M ⊗^∧_D Ω^*_D` to the level `T(0)_e` and restricting
along `ψ` is base changing along `a` and reducing at the smooth lifting.  In degree `a`, on
`m ⊗ ω`, both sides are `ψ^*(m_e) ⊗ ψ^*(Θ_{T(0)_e}(ω))`, by the naturality of the comparison of
forms (`Crystalline.GlobalCrystallineSituation.formsHom_naturality`). -/
theorem levelZeroDeRhamComplexHom_comp_affineDeRhamSectionsMap (e : ℕ) (he : T.levelBound ≤ e) :
    levelZeroDeRhamComplexHom T.primeNilpotentX T.prime_nilpotent Fc (e := e) ≫
        affineDeRhamSectionsMap Fc.property.1 (T.levelAffineHom e he) =
      (crystalPairConnModule T.primeNilpotentX Fc).baseChangeHom (T.envelopeFormsHom e he) ≫
        T.liftingDeRhamComplexHom Fc e he := by
  let := T.envelopeFormsAlgebra e he
  refine HomologicalComplex.hom_ext _ _ fun a ↦ ?_
  refine AddCommGrpCat.ext fun z ↦ ?_
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero
    (exists_pow_eq_zero_presTowerRing T.primeNilpotentX T.prime_nilpotent)
    (f := ((levelZeroDeRhamComplexHom T.primeNilpotentX T.prime_nilpotent Fc (e := e) ≫
        affineDeRhamSectionsMap Fc.property.1 (T.levelAffineHom e he)).f a).hom)
    (g := (((crystalPairConnModule T.primeNilpotentX Fc).baseChangeHom (T.envelopeFormsHom e he) ≫
        T.liftingDeRhamComplexHom Fc e he).f a).hom) fun m ω ↦ ?_
  · exact DFunLike.congr_fun h z
  · change restrictForms Fc.obj (T.levelAffineHom e he).hom a
        (((levelZeroDeRhamComplexHom T.primeNilpotentX T.prime_nilpotent Fc (e := e)).f a).hom
          (toCompletedTensor _ _ _ _ (m ⊗ₜ ω))) =
      ((T.liftingDeRhamComplexHom Fc e he).f a).hom
        (CompletedDeRham.baseChangeTerm _ _ _ _ _ _ (T.envelopeFormsHom e he).psi a
          (toCompletedTensor _ _ _ _ (m ⊗ₜ ω)))
    refine (congrArg (restrictForms Fc.obj (T.levelAffineHom e he).hom a)
      (levelZeroDeRhamComplexHom_f_of_tmul _ _ _ a m ω)).trans ?_
    refine (restrictForms_tmul Fc.obj _ a _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((T.liftingDeRhamComplexHom Fc e he).f a).hom
      (CompletedDeRham.baseChangeTerm_of_tmul _ _ _ _ _ _ _ a m ω)).symm
    refine Eq.trans ?_ (T.liftingDeRhamComplexHom_f_of_tmul Fc e he a _ _).symm
    exact congrArg₂ (· ⊗ₜ ·) (T.liftingComponent_liftingInclusion Fc e he m).symm
      (formsHom_naturality T.exists_pow_eq_zero_liftingEnvelope T.liftingEnvelopeAlgHom
        T.isDPMorphism_liftingEnvelopeAlgHom
        (exists_pow_eq_zero_wsEnvelope T.primeNilpotentX T.prime_nilpotent 0)
        (levelEnvelopeAlgHom T.primeNilpotentX 0 e)
        (isDPMorphism_levelEnvelopeAlgHom T.primeNilpotentX 0 e) (T.levelHom e he).hom
        (T.envelopeFormsHom e he) (T.liftingRingHom_envelopeFormsHom e he)
        (T.envelopeFormsHom_psi_completedUnitZeroForm e he) a ω).symm

/-- **The restriction along `ψ : (X, Y, γ) ⟶ T(0)_e` of the explicit de Rham complexes of a
crystal in quasi-coherent modules is a quasi-isomorphism**, for `p^{N+e} = 0` in `E(0)`: in the
square of comparisons the reduction at `T(0)_e` and at `Y` are isomorphisms and the base change
along `a` is a quasi-isomorphism ([Stacks, Lemma 60.21.4, Tag 07LH]). -/
theorem quasiIso_affineDeRhamSectionsMap_levelAffineHom (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0) :
    QuasiIso (affineDeRhamSectionsMap Fc.property.1 (T.levelAffineHom e he)) := by
  have := isIso_levelZeroDeRhamComplexHom T.primeNilpotentX T.prime_nilpotent Fc hpe
  have := T.isIso_liftingDeRhamComplexHom Fc e he hpe
  have : QuasiIso ((crystalPairConnModule T.primeNilpotentX Fc).baseChangeHom
      (T.envelopeFormsHom e he)) := T.quasiIso_baseChangeHom_levelEnvelopeMap Fc e he
  have h : QuasiIso ((crystalPairConnModule T.primeNilpotentX Fc).baseChangeHom
      (T.envelopeFormsHom e he) ≫ T.liftingDeRhamComplexHom Fc e he) := inferInstance
  rw [← T.levelZeroDeRhamComplexHom_comp_affineDeRhamSectionsMap Fc e he] at h
  exact (quasiIso_iff_comp_left _ _).mp h

/-- **Every large level works**: there is `e₀` such that every `e ≥ e₀` is past `levelBound` and
has `p^{N+e} = 0` in `E(0)`, `p` being nilpotent there. -/
theorem exists_levelBound_pow_eq_zero :
    ∃ e₀, ∀ e ≥ e₀, T.levelBound ≤ e ∧
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) : ℕ) :
        wsEnvelope T.primeNilpotentX 0) = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_eq_zero_wsEnvelope T.primeNilpotentX T.prime_nilpotent 0
  refine ⟨max T.levelBound k, fun e he ↦ ⟨le_trans (le_max_left _ _) he, ?_⟩⟩
  rw [Nat.cast_pow]
  exact pow_eq_zero_of_le ((le_trans (le_max_right _ _) he).trans (Nat.le_add_left _ _)) hk

variable {F : SheafOfModules.{u} (structureSheaf S)}

/-- **The restriction `K^•(T(0)_e) → K^•(Y)` of the de Rham complex `K = ℱ ⊗ Ω^•_{X/S}` of a
crystal in quasi-coherent modules along `ψ : (X, Y, γ) ⟶ T(0)_e` is a quasi-isomorphism**, for
every level with `p^{N+e} = 0` in `E(0)`. -/
theorem quasiIso_levelRestriction (hF : F.IsQuasicoherentOnSite) (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0) :
    QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft
      (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
        ((evaluation _ _).map (T.levelHom e he).op)) (ComplexShape.up ℤ)).app
      (crystalDeRhamSheafData hF).complex) :=
  quasiIso_complex_restriction hF (T.levelAffineHom e he)
    (T.quasiIso_affineDeRhamSectionsMap_levelAffineHom
      ⟨F, hF, isSheafCrystal_of_isQuasicoherentOnSite F hF⟩ e he hpe)

/-- **For every large `e` there is a morphism `ψ : (X, Y, γ) ⟶ T(0)_e` along which the
restriction of the de Rham complex of a crystal in quasi-coherent modules is a
quasi-isomorphism.** -/
theorem exists_quasiIso_levelRestriction (hF : F.IsQuasicoherentOnSite) :
    ∃ e₀, ∀ e ≥ e₀, ∃ ψ : T.crystallineThickening ⟶ levelObj T.primeNilpotentX 0 e,
      QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft
        (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
          ((evaluation _ _).map ψ.op)) (ComplexShape.up ℤ)).app
        (crystalDeRhamSheafData hF).complex) := by
  obtain ⟨e₀, h⟩ := T.exists_levelBound_pow_eq_zero
  exact ⟨e₀, fun e he ↦ ⟨T.levelHom e (h e he).1,
    T.quasiIso_levelRestriction hF e (h e he).1 (h e he).2⟩⟩

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end
