module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TargetChange
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic

/-!
# The morphism of Tag 01O9 under an isomorphism of the invertible module

Let `f : X ⟶ S` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, with the
open `U(ψ)` and the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O9].  An isomorphism
`e : ℒ ≅ ℒ'` of invertible modules transports `ψ` to `ψ' = e ∘ ψ`
(`…RelativeProjQcohSheaf.Twisting.congrModule`).  This file proves that `U(ψ') = U(ψ)` and
`r_{ℒ',ψ'} = r_{ℒ,ψ}`.

## Main results

* `…RelativeProjInvertibleMorphism.GradedPowerMap.homOfLE_globalMorphism_of_valueIso`:
  two data of [Stacks, Tag 01O8] over the same morphism whose values correspond under
  isomorphisms of the tensor powers have the same open and the same morphism.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.coveringOpen_congrModule`:
  **`U(e ∘ ψ) = U(ψ)`**.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.lift_globalMorphism_congrModule`:
  **`r_{ℒ', e ∘ ψ} = r_{ℒ,ψ}`**, after a lift of an arbitrary morphism of schemes.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (pullPowSection restrictPowSection)

universe u

/-! ### Surjectivity of a component under the elementary transports of `ψ` -/

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

variable {T S S' : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- A component of the transport of `ψ` along an isomorphism of the invertible module is
surjective exactly when the component of `ψ` is. -/
theorem epi_congrModule_app_iff {f : T ⟶ S} (ψ : Twisting f A d L) (e : L ≅ L') (i : ℤ) :
    Epi ((ψ.congrModule e).app i) ↔ Epi (ψ.app i) :=
  epi_comp_iff_of_isIso (ψ.app i) (LaurentCongr.congrIso e i).hom

/-- Rereading `ψ` over an equal morphism to the base does not change its components. -/
theorem epi_congrBase_app_iff {f f' : T ⟶ S} (h : f = f') (ψ : Twisting f A d L) (i : ℤ) :
    Epi ((Twisting.congrBase h ψ).app i) ↔ Epi (ψ.app i) := by
  subst h
  rfl

/-- A component of the map of Tag 01NT read over `f'` is surjective exactly when the component
over `g ∘ f'` is. -/
theorem epi_baseChangeDown_app_iff (g : S' ⟶ S) (f' : T ⟶ S') (ψ : Twisting (f' ≫ g) A d L)
    (i : ℤ) : Epi ((ψ.baseChangeDown g f' A d).app i) ↔ Epi (ψ.app i) :=
  epi_comp_iff_of_epi (inv (compComparison f' g (A.piece (i * d)))) (ψ.app i)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Restricting an isomorphism of tensor powers to an open -/

section RestrictPow

variable {Z : Scheme.{u}} {M M' : Z.Modules} [Stacks.Ample.IsInvertibleModule Z M]
  [Stacks.Ample.IsInvertibleModule Z M']

/-- An isomorphism `M^{⊗ n} ≅ M'^{⊗ n}` of iterated tensor powers, read on an open `U`:
`(M|_U)^{⊗ n} ≅ (M'|_U)^{⊗ n}`, through the comparisons `ι^*(M^{⊗ n}) ≅ (ι^*M)^{⊗ n}`. -/
def restrictNatPowIso (U : Z.Opens) (n : ℕ) (N : natTensorPow M n ≅ natTensorPow M' n) :
    natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n ≅
      natTensorPow ((Scheme.Modules.pullback U.ι).obj M') n :=
  (powTransport U.ι M n).symm ≪≫ (Scheme.Modules.pullback U.ι).mapIso N ≪≫
    powTransport U.ι M' n

/-- **The restricted isomorphism carries the restriction of a section to the restriction of its
image.** -/
theorem restrictNatPowIso_hom_app_restrictPowSection (U : Z.Opens) (n : ℕ)
    (N : natTensorPow M n ≅ natTensorPow M' n) (x : Γ(natTensorPow M n, U)) :
    (restrictNatPowIso U n N).hom.app ⊤ (restrictPowSection M U n x) =
      restrictPowSection M' U n (N.hom.app U x) := by
  rw [restrictPowSection, restrictPowSection, pullPowSection_eq_powTransport,
    pullPowSection_eq_powTransport]
  have hn := ConcreteCategory.congr_hom
    ((restrictNatPowIso U n N).hom.mapPresheaf.naturality
      (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op)
    ((powTransport U.ι M n).hom.app (U.ι ⁻¹ᵁ U)
      (pullbackUnit (ringedSpaceHom U.ι) (natTensorPow M n : Z.Modules) (op U) x))
  refine hn.trans ?_
  refine congrArg (fun z => (natTensorPow ((Scheme.Modules.pullback U.ι).obj M') n).presheaf.map
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op
    ((powTransport U.ι M' n).hom.app (U.ι ⁻¹ᵁ U) z)) ?_
  have h1 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (powTransport U.ι M n).symm (U.ι ⁻¹ᵁ U)
    (pullbackUnit (ringedSpaceHom U.ι) (natTensorPow M n : Z.Modules) (op U) x)
  have h2 := pullbackUnit_naturality (f := ringedSpaceHom U.ι) N.hom (op U) x
  refine (congrArg (fun z => (((pullbackFunctor (ringedSpaceHom U.ι)).map N.hom).val.app _) z)
    h1).trans ?_
  exact h2

end RestrictPow

/-! ### Two data of Tag 01O8 with corresponding values -/

namespace GradedPowerMap

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P P' : GradedPowerMap A f) (N : ∀ n : ℕ, natTensorPow P.L n ≅ natTensorPow P'.L n)
  (hN : ∀ (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)),
    (N n).hom.app (f ⁻¹ᵁ V) (P.value n V a) = P'.value n V a)

include hN

/-- Over an open of the base, the induced data of [Stacks, Tag 01NK] correspond under the
restrictions of the isomorphisms of tensor powers. -/
theorem affineDatum_powIso (V : S.Opens) (n : ℕ) (a : A.grading V n) :
    (restrictNatPowIso (f ⁻¹ᵁ V) n (N n)).hom.app ⊤ ((P.affineDatum V).toFun n a) =
      (P'.affineDatum V).toFun n a := by
  rw [affineDatum_toFun_apply, affineDatum_toFun_apply,
    restrictNatPowIso_hom_app_restrictPowSection, hN]

/-- **The opens agree.** -/
theorem coveringOpen_eq_of_valueIso : P'.coveringOpen = P.coveringOpen := by
  refine P'.coveringOpen_congr fun p => ?_
  change Stacks.SectionPowerOpen.nonvanishingOpenOn (natTensorPow P'.L (p.deg + 1)) (f ⁻¹ᵁ p.base)
      (P'.value (p.deg + 1) p.base p.val) =
    Stacks.SectionPowerOpen.nonvanishingOpenOn (natTensorPow P.L (p.deg + 1)) (f ⁻¹ᵁ p.base)
      (P.value (p.deg + 1) p.base p.val)
  rw [← hN]
  exact TopologicalSpace.Opens.ext
    (Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr (N (p.deg + 1)) (f ⁻¹ᵁ p.base) _)

/-- **The morphisms agree**: the morphism of `P'` is that of `P` read on the equal open. -/
theorem homOfLE_globalMorphism_of_valueIso (rp : RelativeProjData A) :
    T.homOfLE (P.coveringOpen_eq_of_valueIso P' N hN).le ≫ P.globalMorphism rp =
      P'.globalMorphism rp := by
  refine P'.eq_globalMorphism_of_clauseThree rp fun V => ?_
  have hΦ := P.affineDatum_powIso P' N hN V.1
  have hcov := GradedSections.coveringOpen_eq_of_powIso (P.affineDatum V.1) (P'.affineDatum V.1)
    (fun n => restrictNatPowIso (f ⁻¹ᵁ V.1) n (N n)) hΦ
  have hgl := GradedSections.homOfLE_glued_eq_of_powIso (P.affineDatum V.1) (P'.affineDatum V.1)
    (fun n => restrictNatPowIso (f ⁻¹ᵁ V.1) n (N n)) hΦ
  have hinc : P'.affineDatumInclusion V ≫ T.homOfLE (P.coveringOpen_eq_of_valueIso P' N hN).le
      = (f ⁻¹ᵁ V.1).toScheme.homOfLE (le_of_eq hcov) ≫ P.affineDatumInclusion V := by
    rw [← cancel_mono P.coveringOpen.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
      P'.affineDatumInclusion_ι V, P.affineDatumInclusion_ι V, Scheme.homOfLE_ι_assoc]
  rw [reassoc_of% hinc, P.affineDatumInclusion_globalMorphism rp V, ← Category.assoc, hgl]

end GradedPowerMap

/-! ### Transport of `ψ` along an isomorphism of the invertible module -/

section CongrModule

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
  (ψ : Twisting f (situationAlgebra A) 1 L) (e : L ≅ L')

/-- The isomorphism `ℒ^{⊗ n} ≅ ℒ'^{⊗ n}` of iterated tensor powers induced by `e`, through the
integral tensor powers of [Stacks, Tag 01CU]. -/
def natPowCongr (n : ℕ) : natTensorPow L n ≅ natTensorPow L' n :=
  powCompare L n ≪≫ LaurentCongr.congrIso e (n : ℤ) ≪≫ (powCompare L' n).symm

/-- **The values of the transport `e ∘ ψ` are the values of `ψ` transported by `e`.** -/
theorem valueSec_congrModule (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    (natPowCongr e n).hom.app (f ⁻¹ᵁ V) (valueSec ψ n V a) = valueSec (ψ.congrModule e) n V a := by
  have h := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (powCompare L n) (f ⁻¹ᵁ V)
    (ψ.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a))
  exact congrArg (fun z => (powCompare L' n).inv.app (f ⁻¹ᵁ V)
    ((LaurentCongr.congrIso e (n : ℤ)).hom.val.app _ z)) h

/-- The pullback of the transport is surjective in a degree exactly when the pullback of `ψ`
is. -/
theorem epi_congrModule_pullback_iff {W : Scheme.{u}} (q : W ⟶ T) (i : ℤ) :
    Epi (((ψ.congrModule e).pullback q).app i) ↔ Epi ((ψ.pullback q).app i) := by
  have e1 : ((ψ.congrModule e).pullback q).app i =
      (compComparison q f ((situationAlgebra A).piece (i * 1)) ≫
        (pullbackFunctor (ringedSpaceHom q)).map (ψ.app i)) ≫
        ((pullbackFunctor (ringedSpaceHom q)).map (LaurentCongr.congrIso e i).hom ≫
          laurentPullback q L' i) := by
    change compComparison q f ((situationAlgebra A).piece (i * 1)) ≫
        (pullbackFunctor (ringedSpaceHom q)).map (ψ.app i ≫ (LaurentCongr.congrIso e i).hom) ≫
          laurentPullback q L' i = _
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
  have e2 : (ψ.pullback q).app i =
      (compComparison q f ((situationAlgebra A).piece (i * 1)) ≫
        (pullbackFunctor (ringedSpaceHom q)).map (ψ.app i)) ≫ laurentPullback q L i :=
    (Category.assoc _ _ _).symm
  have h1 : IsIso ((pullbackFunctor (ringedSpaceHom q)).map (LaurentCongr.congrIso e i).hom) :=
    inferInstance
  have h2 : IsIso (laurentPullback q L' i) := isIso_laurentPullback q L' i
  have h3 : IsIso (laurentPullback q L i) := isIso_laurentPullback q L i
  have h4 : IsIso ((pullbackFunctor (ringedSpaceHom q)).map (LaurentCongr.congrIso e i).hom ≫
      laurentPullback q L' i) := @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  rw [e1, e2]
  exact (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ h4).trans
    (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ h3).symm

/-- **The open `U(ψ)` does not change under an isomorphism of the invertible module.** -/
theorem coveringOpen_congrModule :
    (toGradedPowerMap (ψ.congrModule e)).coveringOpen = (toGradedPowerMap ψ).coveringOpen := by
  ext x
  simp only [SetLike.mem_coe, mem_coveringOpen_iff_exists_epi, epi_congrModule_pullback_iff]

/-- **The morphism of Tag 01O9 does not change under an isomorphism of the invertible module**:
`r_{ℒ', e ∘ ψ} = r_{ℒ,ψ}`, stated after a lift `W ⟶ U(ψ)` of an arbitrary morphism of schemes
`q : W ⟶ X`. -/
theorem lift_globalMorphism_congrModule {W : Scheme.{u}} (q : W ⟶ T)
    (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q (by rw [coveringOpen_congrModule]; exact hq) ≫
        (toGradedPowerMap (ψ.congrModule e)).globalMorphism (relativeProj A) =
      liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  have hN : ∀ (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)),
      (natPowCongr e n).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value n V a) =
        (toGradedPowerMap (ψ.congrModule e)).value n V a := fun n V a => by
    rw [toGradedPowerMap_value, toGradedPowerMap_value]
    exact valueSec_congrModule ψ e n V a
  have hg := GradedPowerMap.homOfLE_globalMorphism_of_valueIso (toGradedPowerMap ψ)
    (toGradedPowerMap (ψ.congrModule e)) (natPowCongr e) hN (relativeProj A)
  rw [← hg, ← Category.assoc, liftOfPreimageEqTop_homOfLE]

end CongrModule

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
