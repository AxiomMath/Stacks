module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.ProObject
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed.FiniteLevels

/-!
# The completed envelope as an inverse limit, and the finite levels generate

The completed divided power envelope of a presentation is the inverse limit of the finite-level
envelopes (`Crystalline.completedEnvelope_isLimit`, [Stacks, Tag 07KG] part (4)) and is an object
of the completed affine crystalline site (`Crystalline.completedCrystallineThickening`,
[Stacks, Tag 07KG] part (5)).  Every divided power thickening of `C/A` receives a morphism from
every sufficiently high finite level (`Crystalline.exists_forall_le_levelEnvelope_hom`,
`Crystalline.exists_levelEnvelope_hom`, [Stacks, Tag 07HP]).

## References

* [Stacks Project, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Crystalline

section FiniteLevelEnvelope

variable (s : AffineCrystallineSituation.{u, v})
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

universe u' v' w'

universe u_1

/-- The completed envelope is the inverse limit of the *envelopes* at large
finite levels. The cone and the transition maps are fixed by the presentation
maps; the universal property is for compatible divided-power morphisms. -/
@[stacks 07KG "part (4)"]
public noncomputable def completedEnvelope_isLimit
    (hf : Function.Surjective f) :
    let env := presentationEnvelope s f
    let D := env.object
    Σ' hp : IsNilpotent (Ideal.Quotient.mk D.ideal (s.p : D)),
      Σ' N : ℕ,
        Σ' hlevel : ∀ e, N ≤ e →
          (DividedPowers.pAdicIdeal (A := D) s.p ^ e ≤ D.ideal) ∧
            D.dividedPowers.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := D) s.p ^ e),
          let Dhat := AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D
          let δhat := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).1
          Σ' π : ∀ e, N ≤ e → DividedPowers.DPMorphism δhat
                (levelEnvelope s f e).object.dividedPowers,
              Σ' t : ∀ m e, N ≤ m → N ≤ e → m ≤ e →
                  DividedPowers.DPMorphism
                    (levelEnvelope s f e).object.dividedPowers
                    (levelEnvelope s f m).object.dividedPowers,
                DividedPowers.IsDividedPowerCompletionLimit D.ideal D.dividedPowers s.p hp
                    N hlevel ∧
                (∀ e (he : N ≤ e) (x : P),
                  (π e he).toRingHom
                    (algebraMap D Dhat (env.algebraMap.toRingHom x)) =
                      (levelEnvelope s f e).algebraMap.toRingHom
                        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e) x)) ∧
                (∀ m e (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) (x : P),
                  (t m e hm he hme).toRingHom
                    ((levelEnvelope s f e).algebraMap.toRingHom
                      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e) x)) =
                        (levelEnvelope s f m).algebraMap.toRingHom
                          (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ m) x)) ∧
                (∀ m e (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
                  (t m e hm he hme).comp (π e he) = π m hm) ∧
                (∀ e (he : N ≤ e),
                  t e e he he (le_refl e) =
                    DividedPowers.DPMorphism.id
                      (levelEnvelope s f e).object.dividedPowers) ∧
                (∀ l m e (hl : N ≤ l) (hm : N ≤ m) (he : N ≤ e)
                    (hlm : l ≤ m) (hme : m ≤ e),
                  (t l m hl hm hlm).comp (t m e hm he hme) =
                    t l e hl he (hlm.trans hme)) ∧
                (∀ {B : Type w} [CommRing B] (J : Ideal B)
                    (δ : DividedPowers J)
                    (cone : ∀ e, N ≤ e → DividedPowers.DPMorphism δ
                      (levelEnvelope s f e).object.dividedPowers),
                  (∀ m e (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
                    (t m e hm he hme).comp (cone e he) = cone m hm) →
                  ∃! g : DividedPowers.DPMorphism δ δhat,
                    ∀ e (he : N ≤ e), (π e he).comp g = cone e he) := by
  classical
  dsimp
  let env := presentationEnvelope s f
  let D := env.object
  let hp := presentationEnvelope_prime_nilpotent s f hf
  let pD := DividedPowers.pAdicIdeal (A := D) s.p
  let Dhat := AdicCompletion pD D
  let δhat := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).1
  letI : Algebra (DividedPowers.IntegersAtPrime s.p) D :=
    (((env.structureMap.toRingHom).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra)
  let hlimEx := DividedPowers.eventually_isDividedPowerCompletionLimit.{u, max u_1 w}
    (I := D.ideal) D.dividedPowers s.p hp
  let N := Classical.choose hlimEx
  let hlimData := Classical.choose_spec hlimEx
  let hlevel := Classical.choose hlimData
  have hlimit := Classical.choose_spec hlimData
  let hbound (e : ℕ) (he : N ≤ e) := hlevel e he
  let hφdata (e : ℕ) (he : N ≤ e) :=
    quotientEnvelopeEquiv s f e (hbound e he).1 (hbound e he).2
  let qD (e : ℕ) : D →+* D ⧸ pD ^ e := Ideal.Quotient.mk (pD ^ e)
  let qP (e : ℕ) : P →+* levelRing s (P := P) e :=
    Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e)
  let Q (e : ℕ) (he : N ≤ e) : DividedPowerRing :=
    ⟨D ⧸ pD ^ e, D.ideal.map (qD e),
      DividedPowers.quotientDividedPowers D.ideal D.dividedPowers s.p e
        (hbound e he).1 (hbound e he).2⟩
  have hqDP (e : ℕ) (he : N ≤ e) :
      D.dividedPowers.IsDPMorphism (Q e he).dividedPowers (qD e) := by
    have hInf : D.dividedPowers.IsSubDPIdeal (pD ^ e ⊓ D.ideal) := by
      rw [inf_eq_left.mpr (hbound e he).1]
      exact (hbound e he).2
    simpa [Q, DividedPowers.quotientDividedPowers, qD] using
      (DividedPowers.Quotient.isDPMorphism D.dividedPowers hInf)
  let qDP (e : ℕ) (he : N ≤ e) :
      DividedPowers.DPMorphism D.dividedPowers (Q e he).dividedPowers :=
    DividedPowers.DPMorphism.mk' (hqDP e he)
  let φ (e : ℕ) (he : N ≤ e) := (hφdata e he).1
  let φDP (e : ℕ) (he : N ≤ e) :
      DividedPowers.DPMorphism (Q e he).dividedPowers
        (levelEnvelope s f e).object.dividedPowers :=
    DividedPowers.DPMorphism.mk' ((hφdata e he).2.2.1)
  let φInvDP (e : ℕ) (he : N ≤ e) :
      DividedPowers.DPMorphism (levelEnvelope s f e).object.dividedPowers
        (Q e he).dividedPowers :=
    DividedPowers.DPMorphism.mk' ((hφdata e he).2.2.2)
  let evalDP (e : ℕ) (he : N ≤ e) :
      DividedPowers.DPMorphism δhat (Q e he).dividedPowers :=
    DividedPowers.DPMorphism.mk' (hlimit.1 e he)
  let factor (m e : ℕ) (hme : m ≤ e) :
      (D ⧸ pD ^ e) →+* (D ⧸ pD ^ m) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hme)
  have hfactorQ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (factor m e hme).comp (qD e) = qD m := by
    ext x
    simp [factor, qD]
  have hfactorIdeal (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (Q e he).ideal.map (factor m e hme) ≤ (Q m hm).ideal := by
    rw [show (Q e he).ideal = D.ideal.map (qD e) by rfl,
      show (Q m hm).ideal = D.ideal.map (qD m) by rfl, Ideal.map_map, hfactorQ m e hm he hme]
  have hfactorDP (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      DividedPowers.IsDPMorphism (Q e he).dividedPowers (Q m hm).dividedPowers
        (factor m e hme) := by
    have hcompDP : D.dividedPowers.IsDPMorphism (Q m hm).dividedPowers
        ((factor m e hme).comp (qD e)) := by
      rw [hfactorQ m e hm he hme]
      exact (qDP m hm).isDPMorphism
    exact DividedPowers.IsDPMorphism.of_comp D.dividedPowers
        (Q e he).dividedPowers (Q m hm).dividedPowers
        (qD e) (factor m e hme) (by rfl) (hqDP e he) hcompDP
  let factorDP (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :=
    DividedPowers.DPMorphism.mk' (hfactorDP m e hm he hme)
  let π (e : ℕ) (he : N ≤ e) :
      DividedPowers.DPMorphism δhat
        (levelEnvelope s f e).object.dividedPowers :=
    (φDP e he).comp (evalDP e he)
  let t (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      DividedPowers.DPMorphism (levelEnvelope s f e).object.dividedPowers
        (levelEnvelope s f m).object.dividedPowers :=
    (φDP m hm).comp ((factorDP m e hm he hme).comp (φInvDP e he))
  have hφDPMap (e : ℕ) (he : N ≤ e) :
      (φDP e he).toRingHom = (φ e he).toRingHom := rfl
  have hφInvDPMap (e : ℕ) (he : N ≤ e) :
      (φInvDP e he).toRingHom = (φ e he).symm.toRingHom := rfl
  have hfactorDPMap (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (factorDP m e hm he hme).toRingHom = factor m e hme := rfl
  have hevalDPMap (e : ℕ) (he : N ≤ e) :
      (evalDP e he).toRingHom = (AdicCompletion.evalₐ pD e).toRingHom := rfl
  have htMap (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (t m e hm he hme).toRingHom =
        (φ m hm).toRingHom.comp
          ((factor m e hme).comp (φ e he).symm.toRingHom) := by
    simp only [t, DividedPowers.DPMorphism.comp_toRingHom, hφDPMap,
      hfactorDPMap, hφInvDPMap]
  have hEvalFactor (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (factor m e hme).comp (AdicCompletion.evalₐ pD e).toRingHom =
        (AdicCompletion.evalₐ pD m).toRingHom := by
    ext x
    apply AdicCompletion.induction_on pD D x
    intro c
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right hme)
        (AdicCompletion.evalₐ pD e (AdicCompletion.mk pD D c)) =
      AdicCompletion.evalₐ pD m (AdicCompletion.mk pD D c)
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    have hcoord : c m - c e ∈ pD ^ m := by
      simpa [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (c.property hme)
    calc
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hme)
          (Ideal.Quotient.mk _ (c e)) = Ideal.Quotient.mk _ (c e) := rfl
      _ = Ideal.Quotient.mk _ (c m) := by
        apply (Submodule.Quotient.eq
          (p := (pD ^ m : Submodule D D))).mpr
        simpa [neg_sub] using pD ^ m |>.neg_mem hcoord
  have hπgen (e : ℕ) (he : N ≤ e) (x : P) :
      (π e he).toRingHom
          (algebraMap D Dhat (env.algebraMap.toRingHom x)) =
        (levelEnvelope s f e).algebraMap.toRingHom (qP e x) := by
    change (φ e he).toRingHom ((AdicCompletion.evalₐ pD e)
      (AdicCompletion.of pD D (env.algebraMap.toRingHom x))) = _
    rw [AdicCompletion.evalₐ_of]
    exact (hφdata e he).2.1 x
  have hφInvGen (e : ℕ) (he : N ≤ e) (x : P) :
      (φ e he).symm
          ((levelEnvelope s f e).algebraMap.toRingHom (qP e x)) =
        qD e (env.algebraMap.toRingHom x) := by
    apply (φ e he).injective
    rw [RingEquiv.apply_symm_apply]
    exact ((hφdata e he).2.1 x).symm
  have htgen (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e)
      (x : P) :
      (t m e hm he hme).toRingHom
          ((levelEnvelope s f e).algebraMap.toRingHom (qP e x)) =
        (levelEnvelope s f m).algebraMap.toRingHom (qP m x) := by
    simp only [t, DividedPowers.DPMorphism.comp_toRingHom, hφDPMap,
      hfactorDPMap, hφInvDPMap, RingHom.comp_apply]
    change (φ m hm) ((factor m e hme) ((φ e he).symm
      ((levelEnvelope s f e).algebraMap.toRingHom (qP e x)))) = _
    rw [hφInvGen e he x, show (factor m e hme) (qD e (env.algebraMap.toRingHom x)) =
      qD m (env.algebraMap.toRingHom x) from
        (RingHom.ext_iff.mp (hfactorQ m e hm he hme)) (env.algebraMap.toRingHom x)]
    exact (hφdata m hm).2.1 x
  have htπ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
      (t m e hm he hme).comp (π e he) = π m hm := by
    apply DividedPowers.DPMorphism.ext
    funext x
    simp only [t, π, DividedPowers.DPMorphism.comp_toRingHom,
      hφDPMap, hφInvDPMap, hfactorDPMap, hevalDPMap]
    change (φ m hm).toRingHom
      ((factor m e hme) ((φ e he).symm
        ((φ e he) ((AdicCompletion.evalₐ pD e).toRingHom x)))) =
        (φ m hm).toRingHom ((AdicCompletion.evalₐ pD m).toRingHom x)
    calc
      _ = (φ m hm).toRingHom
          ((factor m e hme) ((AdicCompletion.evalₐ pD e).toRingHom x)) := by simp
      _ = (φ m hm).toRingHom ((AdicCompletion.evalₐ pD m).toRingHom x) := by
        congr 1
        exact (RingHom.ext_iff.mp (hEvalFactor m e hm he hme)) x
  have htId (e : ℕ) (he : N ≤ e) :
      t e e he he (le_refl e) = DividedPowers.DPMorphism.id
        (levelEnvelope s f e).object.dividedPowers := by
    apply DividedPowers.DPMorphism.ext
    funext x
    simp only [t, DividedPowers.DPMorphism.comp_toRingHom,
      hφDPMap, hφInvDPMap, hfactorDPMap]
    change (φ e he) ((factor e e (le_refl e)) ((φ e he).symm x)) = x
    have hfactorId : factor e e (le_refl e) = RingHom.id _ := by
      ext z
      simp [factor]
    rw [hfactorId]
    simp
  have htTrans (l m e : ℕ) (hl : N ≤ l) (hm : N ≤ m) (he : N ≤ e)
      (hlm : l ≤ m) (hme : m ≤ e) :
      (t l m hl hm hlm).comp (t m e hm he hme) =
        t l e hl he (hlm.trans hme) := by
    apply DividedPowers.DPMorphism.ext
    funext x
    simp only [t, DividedPowers.DPMorphism.comp_toRingHom,
      hφDPMap, hφInvDPMap, hfactorDPMap]
    change (φ l hl) ((factor l m hlm) ((φ m hm).symm
      ((φ m hm) ((factor m e hme) ((φ e he).symm x))))) =
        (φ l hl) ((factor l e (hlm.trans hme)) ((φ e he).symm x))
    simp only [RingEquiv.symm_apply_apply]
    have hfactorComp : (factor l m hlm).comp (factor m e hme) =
        factor l e (hlm.trans hme) :=
      Ideal.Quotient.factor_comp (Ideal.pow_le_pow_right hme)
        (Ideal.pow_le_pow_right hlm)
    have hx := congrArg (fun k : (D ⧸ pD ^ e) →+* (D ⧸ pD ^ l) =>
      (φ l hl).toRingHom (k ((φ e he).symm x))) hfactorComp
    simpa [RingHom.comp_apply] using hx
  have hlimitOut : DividedPowers.IsDividedPowerCompletionLimit.{u, u_1}
      D.ideal D.dividedPowers s.p hp N hlevel := by
    change (∀ e (he : N ≤ e), δhat.IsDPMorphism
      (DividedPowers.quotientDividedPowers D.ideal D.dividedPowers s.p e
        (hlevel e he).1 (hlevel e he).2)
      (AdicCompletion.evalₐ pD e).toRingHom) ∧ _
    refine ⟨hlimit.1, ?_⟩
    intro B _ J δ cone hcone
    exact completionLimitUniversal_down.{u, u_1, w}
      D.ideal D.dividedPowers s.p hp N hlevel hlimit J δ cone hcone
  refine ⟨hp, N, hlevel, ?_⟩
  refine ⟨π, t, ?_⟩
  refine ⟨hlimitOut, hπgen, htgen, htπ, htId, htTrans, ?_⟩
  · intro B _ J δ cone hcone
    let coneQ (e : ℕ) (he : N ≤ e) :
        DividedPowers.DPMorphism δ (Q e he).dividedPowers :=
      (φInvDP e he).comp (cone e he)
    have hconeQ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
        (factorDP m e hm he hme).comp (coneQ e he) = coneQ m hm := by
      apply DividedPowers.DPMorphism.ext
      funext b
      simp only [DividedPowers.DPMorphism.comp_toRingHom, hfactorDPMap,
        hφInvDPMap, coneQ]
      apply (φ m hm).injective
      have h := (RingHom.ext_iff.mp
        (congrArg DividedPowers.DPMorphism.toRingHom
          (hcone m e hm he hme))) b
      have h' : (φ m hm).toRingHom
          ((factor m e hme) ((φ e he).symm.toRingHom ((cone e he).toRingHom b))) =
          (cone m hm).toRingHom b := by
        simpa only [htMap, DividedPowers.DPMorphism.comp_toRingHom,
          RingHom.comp_apply] using h
      calc
        _ = (cone m hm).toRingHom b := h'
        _ = (φ m hm).toRingHom
            ((φ m hm).symm ((cone m hm).toRingHom b)) := by simp
    have hconeQRing (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e) :
        (factor m e hme).comp (coneQ e he).toRingHom =
          (coneQ m hm).toRingHom := by
      simpa only [DividedPowers.DPMorphism.comp_toRingHom, hfactorDPMap] using
        congrArg DividedPowers.DPMorphism.toRingHom (hconeQ m e hm he hme)
    obtain ⟨g, hg, huniq⟩ := completionLimitUniversal_down.{u, w, u_1}
      D.ideal D.dividedPowers s.p hp N hlevel hlimit J δ coneQ hconeQRing
    refine ⟨g, ?_, ?_⟩
    · intro e he
      apply DividedPowers.DPMorphism.ext
      funext b
      have hge := (RingHom.ext_iff.mp (hg e he)) b
      simp only [π, DividedPowers.DPMorphism.comp_toRingHom, hφDPMap,
        hevalDPMap]
      have hge' : (AdicCompletion.evalₐ pD e).toRingHom (g.toRingHom b) =
          (φ e he).symm ((cone e he).toRingHom b) := by
        simpa [coneQ, DividedPowers.DPMorphism.comp_toRingHom,
          hφInvDPMap, RingHom.comp_apply] using hge
      calc
        _ = (φ e he).toRingHom
            ((φ e he).symm ((cone e he).toRingHom b)) :=
              congrArg (φ e he).toRingHom hge'
        _ = (cone e he).toRingHom b := by simp
    · intro g' hg'
      apply huniq g'
      intro e he
      refine RingHom.ext fun b => (φ e he).injective ?_
      have h := (RingHom.ext_iff.mp
        (congrArg DividedPowers.DPMorphism.toRingHom (hg' e he))) b
      change (φ e he).toRingHom
        ((AdicCompletion.evalₐ pD e).toRingHom (g'.toRingHom b)) =
          (cone e he).toRingHom b at h
      calc
        _ = (cone e he).toRingHom b := h
        _ = (φ e he).toRingHom
            ((φ e he).symm ((cone e he).toRingHom b)) := by simp

/-- The canonical completed divided power envelope is an object of the
completed affine crystalline site. -/
@[stacks 07KG "part (5)"]
public noncomputable def completedCrystallineThickening
    (hf : Function.Surjective f) :
    let env := presentationEnvelope s f
    let D := env.object
    Σ' hp : IsNilpotent (Ideal.Quotient.mk D.ideal (s.p : D)),
      {X : CompletedCrystallineThickening.{u, v, u} s //
        X.ring = DividedPowerRing.of
          (AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D)
          (DividedPowers.completionIdeal D.ideal s.p hp)
          (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).1 ∧
        HEq X.fromBase.toRingHom
          ((algebraMap D (AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D)).comp
            env.structureMap.toRingHom) ∧
        ∀ x : P, HEq (X.toQuotient (f x))
          (Ideal.Quotient.mk (DividedPowers.completionIdeal D.ideal s.p hp)
            (algebraMap D (AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D)
              (env.algebraMap.toRingHom x)))} := by
  classical
  dsimp
  let env := presentationEnvelope s f
  let D := env.object
  let hp := presentationEnvelope_prime_nilpotent s f hf
  let pD := DividedPowers.pAdicIdeal (A := D) s.p
  let Dhat := AdicCompletion pD D
  let Ihat := DividedPowers.completionIdeal D.ideal s.p hp
  let γhat := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).1
  have hbaseIdeal : s.A.ideal.map (algebraMap s.A P) ≤ presentationKernel s f := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change f (algebraMap s.A P x) = 0
    rw [f.commutes, ← Ideal.mem_bot, ← s.ideal_map_eq_bot]
    exact Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
  let eEnvData := envelopeQuotientEquiv (algebraMap s.A P)
    (presentationKernel s f) hbaseIdeal env
  let eC : (D ⧸ D.ideal) ≃+* s.C :=
    eEnvData.1.trans
      (RingHom.quotientKerEquivOfSurjective
        (f := f.toRingHom) hf)
  let evalQ := DividedPowers.completionToQuotient D.ideal s.p hp
  let evalEquiv : (Dhat ⧸ Ihat) ≃+* (D ⧸ D.ideal) :=
    RingHom.quotientKerEquivOfSurjective (f := evalQ)
      (DividedPowers.completionToQuotient_surjective D.ideal s.p hp)
  let eTotal : (Dhat ⧸ Ihat) ≃+* s.C := evalEquiv.trans eC
  have hevalMk (z : Dhat) : evalEquiv (Ideal.Quotient.mk Ihat z) = evalQ z := by
    change (RingHom.quotientKerEquivOfSurjective (f := evalQ)
      (DividedPowers.completionToQuotient_surjective D.ideal s.p hp))
      (Ideal.Quotient.mk (RingHom.ker evalQ) z) = evalQ z
    exact RingHom.quotientKerEquivOfSurjective_apply_mk
      (f := evalQ) (DividedPowers.completionToQuotient_surjective D.ideal s.p hp) z
  have hEvalAlg : evalQ.comp (algebraMap D Dhat) =
      Ideal.Quotient.mk D.ideal := by
    ext x
    change (Ideal.Quotient.factor
      (DividedPowers.pAdicIdeal_pow_nilpotencyExponent_le D.ideal s.p hp))
      (AdicCompletion.evalₐ pD (DividedPowers.nilpotencyExponent D.ideal s.p hp)
        (AdicCompletion.of pD D x)) = _
    rw [AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.factor_mk _ x
  have hgen (x : P) :
      eTotal (Ideal.Quotient.mk Ihat
        (algebraMap D Dhat (env.algebraMap.toRingHom x))) = f x := by
    change eC (evalEquiv (Ideal.Quotient.mk Ihat
      (algebraMap D Dhat (env.algebraMap.toRingHom x)))) = f x
    rw [hevalMk, show evalQ (algebraMap D Dhat (env.algebraMap.toRingHom x)) =
      Ideal.Quotient.mk D.ideal (env.algebraMap.toRingHom x) from
        (RingHom.ext_iff.mp hEvalAlg) (env.algebraMap.toRingHom x)]
    change (RingHom.quotientKerEquivOfSurjective
      (f := f.toRingHom) hf)
      (eEnvData.1 (Ideal.Quotient.mk D.ideal (env.algebraMap.toRingHom x))) = f x
    rw [eEnvData.2 x]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk
      (f := f.toRingHom) hf x
  let toC : s.C →+* Dhat ⧸ Ihat := eTotal.symm.toRingHom
  let α : D →+* Dhat := algebraMap D Dhat
  have hαIdeal : D.ideal.map α ≤ Ihat := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change evalQ (α x) = 0
    rw [← RingHom.comp_apply, hEvalAlg]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hα : D.dividedPowers.IsDPMorphism γhat α := by
    refine ⟨hαIdeal, ?_⟩
    intro n x hx
    let xhat : Ihat := ⟨α x, hαIdeal (Ideal.mem_map_of_mem α hx)⟩
    have hd := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).2
      n x hx xhat rfl
    simpa [xhat, α] using hd
  let αDP : DividedPowers.DPMorphism D.dividedPowers γhat :=
    DividedPowers.DPMorphism.mk' hα
  let baseDP := αDP.comp env.structureMap
  have hcommute :
      (Ideal.Quotient.mk Ihat).comp baseDP.toRingHom =
        toC.comp (algebraMap s.A s.C) := by
    refine RingHom.ext fun a => eTotal.injective ?_
    calc
      eTotal (Ideal.Quotient.mk Ihat (baseDP.toRingHom a)) =
          eTotal (Ideal.Quotient.mk Ihat
            (α (env.algebraMap.toRingHom (algebraMap s.A P a)))) := by
        congr 2
        change α (env.structureMap.toRingHom a) = _
        exact congrArg α ((RingHom.ext_iff.mp env.algebraMap_comp) a).symm
      _ = f (algebraMap s.A P a) := hgen (algebraMap s.A P a)
      _ = algebraMap s.A s.C a := by rw [f.commutes]
      _ = eTotal (toC (algebraMap s.A s.C a)) := by simp [toC]
  have hPfg : pD.FG := by
    refine ⟨{(s.p : D)}, ?_⟩
    simp [pD, DividedPowers.pAdicIdeal]
  have hspan : pD.map (algebraMap D Dhat) = Ideal.span {(s.p : Dhat)} := by
    change (Ideal.span {(s.p : D)}).map (algebraMap D Dhat) = _
    rw [Ideal.map_span]
    simp
  have hcomplete : IsAdicComplete (Ideal.span {(s.p : Dhat)}) Dhat := by
    rw [← hspan]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
      (AdicCompletion.isAdicComplete hPfg)
  let X : CompletedCrystallineThickening s :=
    ⟨DividedPowerRing.of Dhat Ihat γhat, baseDP, hcomplete, toC,
      hcommute, eTotal.symm.bijective⟩
  refine ⟨hp, X, rfl, heq_of_eq rfl, fun x => heq_of_eq ?_⟩
  have hEq : toC (f x) = Ideal.Quotient.mk Ihat (α (env.algebraMap.toRingHom x)) :=
    eTotal.injective ((eTotal.apply_symm_apply (f x)).trans (hgen x).symm)
  exact hEq

end FiniteLevelEnvelope

section Generators

/-- **Every sufficiently high finite-level divided power envelope maps to a given affine divided
power thickening.**  The level above which this holds is the larger of the cutoff of
`Crystalline.levelCrystallineThickening` and the nilpotency exponent of `p` in `B`, and the
exponent enters the construction only through those two facts: that it is a level, and that
`(p)^e` vanishes in `B`.

`Crystalline.exists_levelEnvelope_hom` is this at the cutoff itself.  The uniform form is what
lets the morphism be produced at a level chosen for some other reason — for instance at a level
past the cutoffs of the two halves of [Stacks, Tag 07KG] part (2), where
`Crystalline.levelFamilyIso` identifies this family of levels with the finite levels of the
completed envelope. -/
@[stacks 07HP "for every sufficiently large level"]
public theorem exists_forall_le_levelEnvelope_hom
    (s : AffineCrystallineSituation.{u, v})
    {P : Type u} [CommRing P] [Algebra s.A P]
    (hP : ∃ (σ : Type u), Nonempty (MvPolynomial σ s.A ≃ₐ[s.A] P))
    (f : P →ₐ[s.A] s.C) (hf : Function.Surjective f)
    (B : DividedPowerThickening.{u, v, u} s) :
    ∃ N : ℕ, ∀ e, N ≤ e →
      ∃ he : (levelCrystallineThickening s f hf).1 ≤ e,
        Nonempty (((levelCrystallineThickening s f hf).2 e he).1 ⟶ B) := by
  classical
  obtain ⟨σ, ⟨E⟩⟩ := hP
  let n := Classical.choose B.prime_nilpotent
  have hn : (s.p : B.ring) ^ n = 0 := Classical.choose_spec B.prime_nilpotent
  let N := (levelCrystallineThickening s f hf).1
  refine ⟨max N n, ?_⟩
  intro e hNne
  have heN : N ≤ e := (le_max_left _ _).trans hNne
  have hen : n ≤ e := (le_max_right _ _).trans hNne
  have hpn : (s.p : B.ring) ^ e = 0 := by
    rw [← Nat.add_sub_of_le hen, pow_add, hn, zero_mul]
  refine ⟨heN, ?_⟩
  let qB : B.ring →+* B.ring ⧸ B.ring.ideal := Ideal.Quotient.mk _
  choose lifts hlifts using fun i : σ =>
    Ideal.Quotient.mk_surjective (B.toQuotient (f (E (MvPolynomial.X i))))
  let coeff : s.A →+* B.ring := B.fromBase.toRingHom
  let eval : MvPolynomial σ s.A →+* B.ring := MvPolynomial.eval₂Hom coeff lifts
  let g : P →+* B.ring := eval.comp E.symm.toRingHom
  let target : MvPolynomial σ s.A →+* B.ring ⧸ B.ring.ideal :=
    (B.toQuotient.comp f.toRingHom).comp E.toRingEquiv.toRingHom
  have hcoeff : qB.comp coeff = target.comp MvPolynomial.C := by
    ext a
    calc
      qB (coeff a) = B.toQuotient (algebraMap s.A s.C a) :=
        congrFun (congrArg DFunLike.coe B.commutes) a
      _ = target (MvPolynomial.C a) := by
        show B.toQuotient (algebraMap s.A s.C a) =
          B.toQuotient (f (E (algebraMap s.A (MvPolynomial σ s.A) a)))
        rw [E.commutes, f.commutes]
  have hvars : (fun i => qB (lifts i)) = fun i => target (MvPolynomial.X i) := funext hlifts
  have hpoly : qB.comp eval = target := by
    have heval : qB.comp eval = MvPolynomial.eval₂Hom
        (qB.comp coeff) (fun i => qB (lifts i)) := by
      simp [eval, MvPolynomial.comp_eval₂Hom]
    have hrepr : target =
        MvPolynomial.eval₂Hom
          (target.comp MvPolynomial.C) (fun i => target (MvPolynomial.X i)) := by
      ext <;> simp
    rw [heval, hcoeff, hvars]
    exact hrepr.symm
  have hdesc : qB.comp g = B.toQuotient.comp f.toRingHom := by
    refine RingHom.ext fun x => ?_
    simpa [g, target, RingHom.comp_apply, AlgEquiv.apply_symm_apply] using
      DFunLike.congr_fun hpoly (E.symm x)
  have hJ : (presentationKernel s f).map g ≤ B.ring.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show g x ∈ B.ring.ideal
    have hxval : qB (g x) = B.toQuotient (f.toRingHom x) := DFunLike.congr_fun hdesc x
    rw [RingHom.mem_ker.mp hx, map_zero] at hxval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxval
  let pI := DividedPowers.pAdicIdeal (A := P) s.p ^ e
  have hkill : pI ≤ RingHom.ker g := by
    show DividedPowers.pAdicIdeal (A := P) s.p ^ e ≤ RingHom.ker g
    rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    apply RingHom.mem_ker.mpr
    simp [g, eval, coeff, RingHom.comp_apply, hpn]
  let qP : P →+* P ⧸ pI := Ideal.Quotient.mk pI
  let lift : P ⧸ pI →+* B.ring := Ideal.Quotient.lift pI g hkill
  have hlift : lift.comp qP = g := Ideal.Quotient.lift_comp_mk pI g hkill
  have hlevelJ : (levelKernel s f e).map lift ≤ B.ring.ideal := by
    show ((presentationKernel s f).map qP).map lift ≤ B.ring.ideal
    rw [Ideal.map_map, hlift]
    exact hJ
  let env := levelEnvelope s f e
  let ψ : IdealPair.Hom (levelKernel s f e) B.ring.ideal :=
    IdealPair.Hom.ofRingHom lift hlevelJ
  have hbase : lift.comp (qP.comp (algebraMap s.A P)) = B.fromBase.toRingHom := by
    calc
      lift.comp (qP.comp (algebraMap s.A P)) =
          (lift.comp qP).comp (algebraMap s.A P) := by ext a; rfl
      _ = g.comp (algebraMap s.A P) := by rw [hlift]
      _ = B.fromBase.toRingHom := by
        ext a
        simp [g, eval, coeff, RingHom.comp_apply, MvPolynomial.eval₂Hom_C,
          AlgEquiv.commutes]
  have hbaseideal : s.A.ideal.map (qP.comp (algebraMap s.A P)) ≤ levelKernel s f e := by
    rw [← Ideal.map_map]
    apply Ideal.map_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show f (algebraMap s.A P x) = 0
    rw [f.commutes, ← Ideal.mem_bot, ← s.ideal_map_eq_bot]
    exact Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
  have hbasePair : IdealPair.Hom.comp ψ
      (IdealPair.Hom.ofRingHom
        (qP.comp (algebraMap s.A P)) hbaseideal) =
      IdealPair.Hom.ofDPMorphism B.fromBase := by
    refine IdealPair.Hom.ext_toRingHom _ _ ?_
    simpa [ψ, IdealPair.Hom.comp, IdealPair.Hom.ofRingHom,
      IdealPair.Hom.ofDPMorphism] using hbase
  let q := (env.homEquiv B.ring B.fromBase).symm ⟨ψ, hbasePair⟩
  have hrestrict :
      IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism q.1) env.algebraMap = ψ :=
    (env.homEquiv_apply B.ring B.fromBase q).symm.trans
      (congrArg Subtype.val ((env.homEquiv B.ring B.fromBase).apply_symm_apply ⟨ψ, hbasePair⟩))
  obtain ⟨⟨Xring, XfromBase, XprimeNilpotent, XtoQuotient, Xcommutes⟩,
    hXcrys, hXring, hXfrom, hXquot⟩ :=
    (levelCrystallineThickening s f hf).2 e heN
  cases hXring
  let X : DividedPowerThickening s :=
    ⟨env.object, XfromBase, XprimeNilpotent, XtoQuotient, Xcommutes⟩
  have hfromRing : X.fromBase.toRingHom = env.structureMap.toRingHom := eq_of_heq hXfrom
  refine ⟨⟨q.1, ?_, ?_⟩⟩
  · apply DividedPowers.DPMorphism.ext
    have hcmp : q.1.toRingHom.comp XfromBase.toRingHom = B.fromBase.toRingHom := by
      rw [hfromRing]
      exact congrArg DividedPowers.DPMorphism.toRingHom q.2
    exact congrArg (fun f : s.A →+* B.ring => f.toFun) hcmp
  · refine RingHom.ext fun c => ?_
    obtain ⟨x, rfl⟩ := hf c
    have hquotx : X.toQuotient (f x) =
        Ideal.Quotient.mk X.ring.ideal
          (env.algebraMap.toRingHom (qP x)) := eq_of_heq (hXquot x)
    have hres : q.1.toRingHom.comp env.algebraMap.toRingHom = lift := by
      simpa [ψ, IdealPair.Hom.ofRingHom, IdealPair.Hom.comp,
        IdealPair.Hom.ofDPMorphism] using congrArg IdealPair.Hom.toRingHom hrestrict
    calc
      (DividedPowerRing.quotientRingHom q.1) (X.toQuotient (f x)) =
          Ideal.Quotient.mk B.ring.ideal
            (q.1.toRingHom (env.algebraMap.toRingHom (qP x))) := by
        rw [hquotx]
        rfl
      _ = Ideal.Quotient.mk B.ring.ideal (lift (qP x)) := by
        congr 1
        exact DFunLike.congr_fun hres (qP x)
      _ = Ideal.Quotient.mk B.ring.ideal (g x) := by rw [Ideal.Quotient.lift_mk pI g hkill]
      _ = B.toQuotient (f x) := DFunLike.congr_fun hdesc x

/-- A sufficiently high finite-level divided power envelope maps to any affine
divided power thickening. -/
@[stacks 07HP]
public theorem exists_levelEnvelope_hom
    (s : AffineCrystallineSituation.{u, v})
    {P : Type u} [CommRing P] [Algebra s.A P]
    (hP : ∃ (σ : Type u), Nonempty (MvPolynomial σ s.A ≃ₐ[s.A] P))
    (f : P →ₐ[s.A] s.C) (hf : Function.Surjective f)
    (B : DividedPowerThickening.{u, v, u} s) :
    ∃ e : ℕ,
      ∃ he : (levelCrystallineThickening s f hf).1 ≤ e,
        Nonempty (((levelCrystallineThickening s f hf).2 e he).1 ⟶ B) := by
  obtain ⟨N, hN⟩ := exists_forall_le_levelEnvelope_hom s hP f hf B
  exact ⟨N, hN N le_rfl⟩

end Generators

end Crystalline
