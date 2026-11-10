module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorKernelWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClassPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorChernClassCup
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.RealizationChernClass

/-!
# The Hodge first Chern class of a divisor dies with logarithmic poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by
`I`, with ideal sheaf `ℐ = 𝒪_X(-Y)`. Let `ι : Ω¹_{X/S} ⟶ Ω¹_{X/S}(log Y)` be the inclusion of
the forms with no pole into the forms with logarithmic poles along `Y`. This file proves that
the Hodge first Chern class of `𝒪_X(Y)` dies in `H¹(X, Ω¹_{X/S}(log Y))`:

`ι_* c₁^{Hodge}(𝒪_X(Y)) = 0`,

in the realization of `H¹(X, Ω¹_{X/S})` as the cohomology of the derived global sections of
`Ω¹_{X/S}[0]` as a sheaf of `f⁻¹𝒪_S`-modules, the one in which the cup product of Hodge
cohomology is taken. It is the vanishing which, along the pairing
`Stacks.HodgeWeil.kernelLogWedge`, kills `a ∪ c₁^{Hodge}(𝒪_X(Y))` for a Hodge class `a`
restricting to zero on `Y`, in the proof of axiom (A4) of Weil cohomology theories for Hodge
cohomology ([Stacks, Remark 0FWE]).

The proof is a Čech computation. Since `[𝒪_X(Y)] = -[ℐ]` in `Pic(X)`, it suffices to treat `ℐ`.
Cover `X` by opens `U_c` over which `ℐ` is trivial, with local equations `t_c`. The class of
`ℐ` in `H¹(X, 𝒪_X^*)` is the class of the transition cocycle `u_{c₀c₁}`, `t_{c₁} = u_{c₀c₁} t_{c₀}`
([Stacks, Tag 09NU]), and `c₁^{Hodge}(ℐ)` is the class of the cocycle `d log u_{c₀c₁}`
([Stacks, Section 0FLE]). In `Ω¹_{X/S}(log Y)` the logarithmic forms `d log t_c` are defined on
`U_c`, and `d log u_{c₀c₁} = d log t_{c₁} - d log t_{c₀}`: evaluated at the basis element
`b₀` of `ℐ` over `U_{c₀}`, both sides are `t_{c₀} u⁻¹ du`. So the image of the cocycle is a Čech
coboundary. The comparison of the cohomology of the underlying sheaves of abelian groups with
the cohomology computed in sheaves of modules ([Stacks, Tag 01F1]) is natural, and carries this
vanishing to the module realization.

## Main definitions

* `Stacks.HodgeWeil.generatorSectionsOfTrivialization`: the basis element of a sectionwise
  trivialization of a module, as a local generator.

## Main results

* `Stacks.HodgeWeil.logPolesFormsInclusion_logarithmicDifferential`: **`d log` of a transition
  function of local equations is the difference of the `d log` of the equations.**
* `Stacks.HodgeWeil.abelianCohomology_logarithmicDifferential_negativeTwist_eq_zero`: the image
  of the class of `ℐ` in `H¹(X, Ω¹_{X/S}(log Y))` vanishes, in the cohomology of abelian sheaves.
* `Stacks.HodgeWeil.cohomologyMap_single_hodgeComponentAbelianIso_eq_zero`: a class of
  `H^i(X, Ω^p)` killed by a morphism `Ω^p ⟶ G` in the cohomology of abelian sheaves is killed
  by it in the module realization.
* `Stacks.HodgeWeil.cohomologyMap_logPolesFormsBaseInclusion_hodgeFirstChernClassModule_eq_zero`:
  **`ι_* c₁^{Hodge}(𝒪_X(Y)) = 0`**, in the module realization.

## Implementation notes

The statement assumes only that `Y` is an effective Cartier divisor: the sheaf
`Ω¹_{X/S}(log Y)` of `AlgebraicGeometry.Scheme.Hom.logPolesForms`, the inclusion `ι` and the forms
`d log t` of `Stacks.Divisors.IdealTrivialization.dlogForm` are defined for any closed subscheme,
and the argument only evaluates forms with logarithmic poles at local sections of `ℐ`. The
condition of [Stacks, Tag 0FMV] that the de Rham complex of log poles be defined is not used;
accordingly the compatibility of `d log t` with restriction is proved here without it
(`Stacks.HodgeWeil.dlogForm_map`).

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

section Chart

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : Stacks.Divisors.IdealTrivialization I U)

/-- A form with logarithmic poles over an open inside a chart is determined by its value at the
basis element of the ideal sheaf. -/
theorem logPolesForms_ext_basisLE {W : X.Opens} (hW : W ≤ U) {p : ℕ}
    {φ ψ : (logPolesForms f I p).val.obj (op W)}
    (h : logEval f I φ (le_refl W) (e.basisLE hW) = logEval f I ψ (le_refl W) (e.basisLE hW)) :
    φ = ψ :=
  (e.logOfCoord_logEval_basisLE hW φ).symm.trans
    ((e.logOfCoord_congr hW h _ _).trans (e.logOfCoord_logEval_basisLE hW ψ))

/-- The exact one-form `dt` of the local equation is `d t`. -/
theorem chartDt_eq_exactOne {V : X.Opens} (hV : V ≤ U) :
    e.chartDt (f := f) hV =
      AlgebraicGeometry.SheafOfModules.exactOne (deRhamAlgebras f) (op V) (e.equationAt hV) :=
  totForm_injective 1 V (e.totForm_chartDt hV)

/-- The value of `dlog t` at a local section `a` of the ideal sheaf: `θ(a) dt`. -/
theorem logEval_dlogForm {W : X.Opens} (hW : W ≤ U) {W' : X.Opens} (h : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (e.dlogForm (f := f) hW) h a = e.coordLE (h.trans hW) a • e.chartDt (h.trans hW) :=
  (Stacks.Divisors.IdealTrivialization.logEval_logOfCoord e hW (e.chartDt hW) _ h a).trans
    (congrArg (e.coordLE (h.trans hW) a • ·) (e.chartDt_res hW h))

/-- `dlog t` restricts to `dlog t`. -/
theorem dlogForm_map {V V' : X.Opens} (hV : V ≤ U) (h : V' ≤ V) :
    (logPolesForms f I 1).val.map (homOfLE h).op (e.dlogForm hV) = e.dlogForm (h.trans hV) :=
  logEval_ext fun _ h' a =>
    (logEval_dlogForm e hV (h'.trans h) a).trans (logEval_dlogForm e (h.trans hV) h' a).symm

/-- `dlog t` restricts to `dlog t`, read in the presheaf of abelian groups underlying
`Ω¹_{X/S}(log Y)`, the presheaf of the Čech complex. -/
theorem restr_dlogForm {V V' : X.Opens} (hV : V ≤ U) (h : V' ≤ V) :
    CechCochains.restr (show TopCat.Sheaf AddCommGrpCat.{u} X.carrier from
        (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).obj (logPolesFormsBase f I 1)).presheaf
      h (e.dlogForm hV) = e.dlogForm (h.trans hV) :=
  dlogForm_map e hV h

end Chart

section Generator

variable {X : Scheme.{u}} {L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  {U : X.Opens}

/-- **The basis element of a sectionwise trivialization of a module generates it** over the
open of the trivialization: multiplication by its restriction to `V ≤ U` is the inverse of the
trivialization over `V`. -/
def generatorSectionsOfTrivialization
    (e : Stacks.SheafDescent.Trivialization X.toRingedSpace.presheaf L.val U) :
    Stacks.Cohomology.Generators.GeneratorSections X.toRingedSpace L U := by
  refine ⟨e.basis, fun V h => ⟨fun r r' hr => ?_,
    fun a => ⟨e.θ V (homOfLE h) a, (e.eq_smul_basisAt (homOfLE h) a).symm⟩⟩⟩
  have hθ := congrArg (e.θ V (homOfLE h)) hr
  change e.θ V (homOfLE h)
      ((show (structureSheafRing X.toRingedSpace).obj.obj (op V) from r) •
        e.basisAt (homOfLE h)) =
    e.θ V (homOfLE h)
      ((show (structureSheafRing X.toRingedSpace).obj.obj (op V) from r') •
        e.basisAt (homOfLE h)) at hθ
  rwa [map_smul, map_smul, e.θ_basisAt (homOfLE h), smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at hθ

/-- The generator attached to a trivialization is its basis element. -/
theorem generatorSectionsOfTrivialization_val
    (e : Stacks.SheafDescent.Trivialization X.toRingedSpace.presheaf L.val U) :
    (generatorSectionsOfTrivialization e).val = e.basis :=
  rfl

end Generator

section Transition

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

/-- The value of a difference of forms with logarithmic poles is the difference of the values. -/
theorem logEval_sub {p : ℕ} {W : X.Opens} (φ ψ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (φ - ψ) h a = logEval f I φ h a - logEval f I ψ h a :=
  eq_sub_of_add_eq ((logEval_add (φ - ψ) ψ h a).symm.trans
    (congrArg (fun χ => logEval f I χ h a) (sub_add_cancel φ ψ)))

/-- **`d log` of a transition function of the local equations is the difference of the `d log`
of the equations**: if the basis elements of two charts are related by `b₁ = u b₀` on `W`, then
`d log u = d log t₁ - d log t₀` as forms with logarithmic poles. -/
theorem logPolesFormsInclusion_logarithmicDifferential {U₀ U₁ W : X.Opens}
    (e₀ : Stacks.Divisors.IdealTrivialization I U₀) (e₁ : Stacks.Divisors.IdealTrivialization I U₁)
    (h₀ : W ≤ U₀) (h₁ : W ≤ U₁) (u : (Γ(X, W))ˣ)
    (hu : e₁.basisLE h₁ = toIdealScalar (u : Γ(X, W)) • e₀.basisLE h₀) :
    (logPolesFormsInclusion f I 1).val.app (op W)
        (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (deRhamAlgebras f) (op W) u) =
      e₁.dlogForm (f := f) h₁ - e₀.dlogForm (f := f) h₀ := by
  have ht : e₁.equationAt h₁ = (u : Γ(X, W)) * e₀.equationAt h₀ :=
    (congrArg idealFn hu).trans (idealFn_smul _ _)
  have hc : e₁.coordLE h₁ (e₀.basisLE h₀) = ((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) := by
    have h1 := congrArg (e₁.coordLE h₁) hu
    rw [Stacks.Divisors.IdealTrivialization.coordLE_basisLE,
      Stacks.Divisors.IdealTrivialization.coordLE_smul] at h1
    exact Units.eq_inv_of_mul_eq_one_left h1.symm
  refine logPolesForms_ext_basisLE e₀ h₀ ?_
  refine (logEval_logPolesFormsInclusion (f := f) (I := I) (p := 1)
    (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (deRhamAlgebras f) (op W) u :
      Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), W))
    (le_refl W) (e₀.basisLE h₀)).trans (Eq.trans ?_ (logEval_sub _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· - ·) (logEval_dlogForm e₁ h₁ (le_refl W) _).symm
    (logEval_dlogForm e₀ h₀ (le_refl W) _).symm)
  rw [Stacks.Divisors.IdealTrivialization.coordLE_basisLE, hc, chartDt_eq_exactOne,
    chartDt_eq_exactOne, ht]
  have hmul := AlgebraicGeometry.SheafOfModules.exactOne_mul (deRhamAlgebras f) (op W)
    (u : Γ(X, W)) (e₀.equationAt h₀)
  refine (congrArg (e₀.equationAt h₀ • ·) (ConcreteCategory.congr_hom
    ((relativeDifferentialForms f ((1 : ℕ) : ℤ)).presheaf.map_id (op W)) _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z : Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), W) =>
    ((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) • z - _) hmul).symm
  have key : ∀ {M : Type u} [AddCommGroup M] [Module Γ(X, W) M] (a b : M),
      e₀.equationAt h₀ • (((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) • b) =
        ((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) • ((u : Γ(X, W)) • a + e₀.equationAt h₀ • b) -
          (1 : Γ(X, W)) • a := by
    intro M _ _ a b
    rw [smul_add, smul_smul ((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) (u : Γ(X, W)), Units.inv_mul,
      one_smul, add_sub_cancel_left, smul_smul, smul_smul, mul_comm]
  exact key _ _

end Transition

section Cech

variable {X S : Scheme.{u}} (f : X ⟶ S) {I : X.IdealSheafData}
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)

open Stacks.Cohomology.LerayLowDegree (abelianCohomology) in
attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup in
/-- **`d log` of the class of the ideal sheaf vanishes in `H¹(X, Ω¹_{X/S}(log Y))`**, in the
cohomology of the underlying sheaf of abelian groups: on a covering by charts of the ideal sheaf,
the transition functions `u` of the local equations satisfy `d log u = d log t₁ - d log t₀`
(`Stacks.HodgeWeil.logPolesFormsInclusion_logarithmicDifferential`), so the image of the
transition cocycle is a Čech coboundary. -/
theorem abelianCohomology_logarithmicDifferential_negativeTwist_eq_zero :
    ((abelianCohomology.{u, u} _ ⊤ 1).map
        (AlgebraicGeometry.SheafOfModules.logarithmicDifferentialSheafHom (deRhamAlgebras f) ≫
          (_root_.SheafOfModules.toSheaf _).map (logPolesFormsBaseInclusion f I 1))).hom
      ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X.toRingedSpace).symm
        (Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
          (structureSheaf X.toRingedSpace.sheaf).property (Stacks.Divisors.negativeTwist' I)
          (haveI := hI; Stacks.Divisors.isTensorInvertible_negativeTwist I))) = 0 := by
  classical
  have := hI
  let Ui : (Σ U : X.Opens, Stacks.Divisors.IdealTrivialization I U) → Opens X.carrier :=
    fun c => c.1
  have hUi : (⊤ : Opens X.carrier) = ⨆ c, Ui c := by
    refine (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ?_).symm
    obtain ⟨U, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
    exact ⟨⟨U, e⟩, hxU⟩
  have hL := Stacks.Divisors.isTensorInvertible_negativeTwist I
  let F := Stacks.Cohomology.Generators.generatorTorsorOfInvertible X.toRingedSpace
    (Stacks.Divisors.negativeTwist' I) hL
  let s : ∀ c, F.toTorsor.F.obj (Ui c) := fun c =>
    (F.sectionsEquiv (Ui c)).symm (generatorSectionsOfTrivialization c.2)
  let z := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle F.toTorsor Ui s
  have hz : (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X.toRingedSpace).symm
      (Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (structureSheaf X.toRingedSpace.sheaf).property (Stacks.Divisors.negativeTwist' I) hL) =
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X.carrier ⊤ Ui hUi
        (Stacks.Cohomology.Generators.unitsSheaf X.toRingedSpace) (CechCochains.cls Ui _ z) :=
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf X.toRingedSpace
      _ hL).trans (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle
        _ _ F.toTorsor Ui hUi s z
        (Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec _ _ _))
  -- the transition units relate the basis elements of the charts
  have hrel : ∀ y : Fin 2 → (Σ U : X.Opens, Stacks.Divisors.IdealTrivialization I U),
      (y 1).2.basisLE (CechCochains.inter_le Ui y 1) =
        toIdealScalar ((Additive.toMul (z.val y) : (Γ(X, CechCochains.inter Ui y))ˣ) :
          Γ(X, CechCochains.inter Ui y)) • (y 0).2.basisLE (CechCochains.inter_le Ui y 0) := by
    intro y
    have h1 := F.sectionsEquiv_restrict (CechCochains.inter_le Ui y 1) (s (y 1))
    have h0 := F.sectionsEquiv_restrict (CechCochains.inter_le Ui y 0) (s (y 0))
    have hs := F.sectionsEquiv_smul (CechCochains.inter Ui y) (Additive.toMul (z.val y))
      (F.F.res (CechCochains.inter_le Ui y 0) (s (y 0)))
    have hspec := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec F.toTorsor Ui s y
    simp only [s, Equiv.apply_symm_apply] at h1 h0
    refine h1.symm.trans ((congrArg (fun a => (F.sectionsEquiv _ a).val) hspec.symm).trans
      (hs.trans ?_))
    exact congrArg (fun a : (Stacks.Divisors.negativeTwist' I).val.obj
        (op (CechCochains.inter Ui y)) =>
      toIdealScalar ((Additive.toMul (z.val y) : (Γ(X, CechCochains.inter Ui y))ˣ) :
          Γ(X, CechCochains.inter Ui y)) • a) h0
  -- the cocycle `d log u` of forms with logarithmic poles is the coboundary of the `d log t`
  let Φ := AlgebraicGeometry.SheafOfModules.logarithmicDifferentialSheafHom (deRhamAlgebras f) ≫
    (_root_.SheafOfModules.toSheaf _).map (logPolesFormsBaseInclusion f I 1)
  let z' : CechCochains.cocycles1 Ui
      (show TopCat.Sheaf AddCommGrpCat.{u} X.carrier from
        (_root_.SheafOfModules.toSheaf _).obj (logPolesFormsBase f I 1)).presheaf :=
    ⟨Stacks.Cohomology.CechOne.push Ui Φ.hom 1 z.val,
      Stacks.Cohomology.CechOne.cechD_push Ui _ 1 z.val z.2⟩
  let t : CechCochains.Cochain Ui
      (show TopCat.Sheaf AddCommGrpCat.{u} X.carrier from
        (_root_.SheafOfModules.toSheaf _).obj (logPolesFormsBase f I 1)).presheaf 0 :=
    fun i => (i 0).2.dlogForm (f := f) (CechCochains.inter_le Ui i 0)
  have ht : CechCochains.cechD Ui _ 0 t = z'.val := by
    funext y
    rw [CechCochains.cechD_apply, Fin.sum_univ_two]
    refine Eq.trans ?_ (logPolesFormsInclusion_logarithmicDifferential (y 0).2 (y 1).2
      (CechCochains.inter_le Ui y 0) (CechCochains.inter_le Ui y 1) _ (hrel y)).symm
    have e : ∀ j : Fin 2, CechCochains.restr _ (CechCochains.inter_le_omit Ui y j)
        (t (y ∘ Fin.succAbove j)) =
        (y (j.succAbove 0)).2.dlogForm (f := f) (CechCochains.inter_le Ui y (j.succAbove 0)) :=
      fun j => restr_dlogForm (f := f) (y (j.succAbove 0)).2
        (CechCochains.inter_le Ui (y ∘ Fin.succAbove j) 0) (CechCochains.inter_le_omit Ui y j)
    rw [e 0, e 1]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [sub_eq_add_neg]
    exact congrArg₂ (· + ·) (one_smul ℤ _) (neg_one_smul ℤ _)
  refine (congrArg ((abelianCohomology.{u, u} _ ⊤ 1).map Φ).hom hz).trans
    ((Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality.{u, u, u}
      X.carrier ⊤ Ui hUi Φ z z' (fun _ => rfl)).trans ?_)
  rw [(CechCochains.cls_eq_zero_iff Ui _ z').mpr ⟨t, ht⟩, map_zero]

end Cech

section Realization

open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap)
open Stacks.Cohomology.GlobalKunneth (baseSections)

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {Y : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} Y.carrier}
  {φ : A ⟶ Y.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology Y.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **A Hodge class killed in the cohomology of abelian sheaves is killed in the module
realization**: for a morphism `ψ : Ω^p ⟶ G` of sheaves of `A`-modules and a class
`y ∈ H^i(X, Ω^p)` of the underlying sheaf of abelian groups with `ψ_* y = 0`, the image of `y` in
the module realization `H^i(X, Ω^p[0])` under
`AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` is killed by `ψ[0]`. This is the
naturality of the comparison of [Stacks, Tag 01F1] along `ψ`. -/
theorem cohomologyMap_single_hodgeComponentAbelianIso_eq_zero (p i : ℕ)
    {G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (ψ : deRhamTerm B p ⟶ G)
    (y : ((sectionsFunctor Y.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p))
    (hy : (((sectionsFunctor Y.carrier ⊤).rightDerived i).map
      ((_root_.SheafOfModules.toSheaf _).map ψ)).hom y = 0) :
    (cohomologyMap (S := baseRingedSpace A)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ) i).hom
      (toHodgeComponentBase B ((hodgeComponentAbelianIso B D p i i rfl).hom.hom y)) = 0 := by
  rw [hodgeComponentAbelianIso_hom_apply]
  let T := _root_.SheafOfModules.toSheaf (structureSheafRing (baseRingedSpace A))
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)
  let R := (sectionsFunctor Y.carrier ⊤).rightDerivedFunctorPlus
  let N₂ : CochainComplex.Plus (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A))) :=
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G
  let a : moduleComplexPlus (X := Y) (A := A) (hodgeSingle B D p) ⟶ N₂ :=
    ObjectProperty.homMk ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((deRhamComplex B D).X p) 0 0 rfl).hom ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ)
  let m : (Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf Y.carrier) 0).obj (T.obj G) ⟶
      T.mapCochainComplexPlus.obj N₂ :=
    ObjectProperty.homMk
      ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app G)
  have hsq : (hodgeSingleUnderlyingIso B D p).hom ≫ T.mapCochainComplexPlus.map a =
      (Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf Y.carrier) 0).map (T.map ψ) ≫ m := by
    refine ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext ?_)
    change (hodgeSingleUnderlyingIso B D p).hom.hom.f 0 ≫
        T.map (((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          ((deRhamComplex B D).X p) 0 0 rfl).hom ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ).f 0) =
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (T.map ψ)).f 0 ≫
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app G).f 0
    rw [hodgeSingleUnderlyingIso_hom_f_zero, HomologicalComplex.comp_f]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((T.map_comp _ _).symm.trans (congrArg T.map
      (show _ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((deRhamComplex B D).X p)).inv ≫
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ).f 0 from ?_)))).trans ?_
    · have hβ : (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            ((deRhamComplex B D).X p) 0 0 rfl).hom.f 0 =
          ((hodgeSingle B D p).extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              ((deRhamComplex B D).X p)).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              ((deRhamComplex B D).X p)).inv :=
        HomologicalComplex.extendSingleIso_hom_f _ _ _ _ rfl
      refine (congrArg (fun g => _ ≫ g ≫ _) hβ).trans ?_
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    · refine Sheaf.hom_ext ?_
      ext U x
      rfl
  have hpsi := ConcreteCategory.congr_hom
    ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y.carrier ⊤) i).hom.naturality
      ((_root_.SheafOfModules.toSheaf _).map ψ)) y
  have hc : H.map (R.map (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso B D p).hom)) ≫
      H.map (R.map (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map a))) =
      H.map (R.map (DerivedCategory.Plus.Q.map
        ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf Y.carrier) 0).map (T.map ψ)))) ≫
      H.map (R.map (DerivedCategory.Plus.Q.map m)) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map ((R.map_comp _ _).symm.trans
      ((congrArg R.map ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Plus.Q.map hsq).trans
          (DerivedCategory.Plus.Q.map_comp _ _)))).trans (R.map_comp _ _)))).trans
      (H.map_comp _ _))
  have h2 := ConcreteCategory.congr_hom hc
    ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y.carrier ⊤) i).hom.app _ y)
  have h3 : (H.map (R.map (DerivedCategory.Plus.Q.map
        ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf Y.carrier) 0).map (T.map ψ))))).hom
        ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y.carrier ⊤) i).hom.app _ y) =
          0 :=
    hpsi.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans
      ((congrArg _ hy).trans (map_zero _)))
  have hN := ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.realizationUnbounded_naturality (baseRingedSpace A) a i)
    ((H.map (R.map (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso B D p).hom))).hom
      ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y.carrier ⊤) i).hom.app _ y))
  refine (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply
    (S := baseRingedSpace A) (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((deRhamComplex B D).X p) 0 0 rfl).hom
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ) i _).trans ?_
  simp only at hN
  change (cohomologyMap (S := baseRingedSpace A) a.hom i).hom _ = 0
  refine hN.symm.trans ?_
  simp only at h2
  refine (congrArg (Stacks.Cech.Hypercohomology.realizationUnbounded (baseRingedSpace A) N₂
    i).hom.hom h2).trans ?_
  exact (congrArg (Stacks.Cech.Hypercohomology.realizationUnbounded (baseRingedSpace A) N₂
    i).hom.hom ((congrArg (H.map (R.map (DerivedCategory.Plus.Q.map m))).hom h3).trans
      (map_zero _))).trans (map_zero _)

end Realization

section Divisor

open Stacks.Cohomology.LerayLowDegree (abelianCohomology)

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)

/-- **The Hodge first Chern class of `𝒪_X(Y)` dies in `H¹(X, Ω¹_{X/S}(log Y))`**: for an
effective Cartier divisor `Y ⊆ X`, the inclusion `ι : Ω¹_{X/S} ⟶ Ω¹_{X/S}(log Y)` kills
`c₁^{Hodge}(𝒪_X(Y))`, in the module realization of Hodge cohomology in which its cup product
is taken. -/
theorem cohomologyMap_logPolesFormsBaseInclusion_hodgeFirstChernClassModule_eq_zero :
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap
        (S := AlgebraicGeometry.SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (logPolesFormsBaseInclusion f I 1)) 1).hom
      (AlgebraicGeometry.SheafOfModules.toHodgeComponentBase _
        (hodgeFirstChernClassModule f
          (haveI := hI; Stacks.WeilCohomology.picardClassOf X (Stacks.Divisors.divisorSheaf I)
            (Stacks.Divisors.isInvertible_divisorSheaf I)))) = 0 := by
  have := hI
  let := Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.toRingedSpace.sheaf.obj
    (structureSheaf X.toRingedSpace.sheaf).property
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property
      (Stacks.Divisors.divisorSheaf I) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf X.ringCatIsSheaf _).mpr (Stacks.Divisors.isInvertible_divisorSheaf I)
  let y := (((sectionsFunctor X.carrier ⊤).rightDerived 1).map
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f)))).hom
    (Scheme.Hom.hodgeFirstChernClass f
      (Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) (Stacks.Divisors.divisorSheaf I) hL))
  have h1 := AlgebraicGeometry.SheafOfModules.rightDerived_logarithmicDifferential_classOf f
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f))
    (Stacks.Divisors.divisorSheaf I) hL
  have hneg : Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
      (structureSheaf X.toRingedSpace.sheaf).property (Stacks.Divisors.divisorSheaf I) hL =
      -Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (structureSheaf X.toRingedSpace.sheaf).property (Stacks.Divisors.negativeTwist' I)
        (Stacks.Divisors.isTensorInvertible_negativeTwist I) :=
    eq_neg_of_add_eq_zero_left (Stacks.Divisors.picardClassOf_invertibleSheaf_add_negativeTwist I)
  have hy : (((sectionsFunctor X.carrier ⊤).rightDerived 1).map
      ((_root_.SheafOfModules.toSheaf _).map (logPolesFormsBaseInclusion f I 1))).hom y = 0 := by
    refine (congrArg _ h1.symm).trans ?_
    refine ((ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (Functor.map_comp _ _ _).symm _)).trans ?_
    rw [hneg, map_neg]
    refine (map_neg (ConcreteCategory.hom (((sectionsFunctor X.carrier ⊤).rightDerived 1).map
      (AlgebraicGeometry.SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)) ≫
        (_root_.SheafOfModules.toSheaf _).map (logPolesFormsBaseInclusion f I 1)))) _).trans ?_
    exact neg_eq_zero.mpr (abelianCohomology_logarithmicDifferential_negativeTwist_eq_zero f hI)
  exact cohomologyMap_single_hodgeComponentAbelianIso_eq_zero (formsAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (formsAlgebras f)) 1 1
    (logPolesFormsBaseInclusion f I 1) y hy

end Divisor

end Stacks.HodgeWeil

end
