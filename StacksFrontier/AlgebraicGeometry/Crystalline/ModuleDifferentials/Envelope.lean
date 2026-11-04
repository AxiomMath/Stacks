module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FirstOrderExtension

/-!
# Differentials of a divided power envelope

Let `(A, I, γ)` be a divided power ring, let `f : A → B` be a ring homomorphism, let `J ⊆ B` be
an ideal containing `f(I)` and let `D` be the divided power envelope of `J`.  The module of
divided power differentials of `D` over `A` is then the base change to `D` of the ordinary
Kähler differentials of `B` over `A`:

`Ω_{D/A, δ} = D ⊗_B Ω_{B/A}`.

Both sides are characterized by a universal property — the left by divided power derivations of
`D`, the right by derivations of `B` — and the comparison is produced by exhibiting the maps in
both directions and recognizing each composite as the identity.  The identification of a
composite with the identity uses the universal property of the envelope twice: a divided power
derivation of `D` into a module is the same thing as a section of the first-order thickening by
that module, and two such sections which agree on the image of `B` agree.

## Main results

* `Crystalline.dividedPowerEnvelopeDifferentialsEquiv` is the canonical `D`-linear equivalence
  between the two modules of differentials, together with its value on the universal divided
  power differential of an element of `B`.

## Implementation notes

The tensor factors are written in the order `D ⊗_B Ω_{B/A}`, canonically symmetric to the order
in the source, so that Mathlib supplies the `D`-module structure on the base change directly.
The conclusion is a subtype rather than a bare equivalence: the defining equation, which records
the value of the equivalence on the universal divided power differentials of elements of `B`, is
what pins the equivalence down, and carrying it in the type keeps the two inseparable.

The scalar towers between `A`, `B` and `D` are supplied locally from the compatibility of the
structure map of the envelope with its map from `B`, since the envelope's algebra structures come
from its structural divided power morphisms rather than from a declared instance.

## References

* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

/-- The divided power differentials of a divided power envelope are canonically the
base change of the ordinary Kähler differentials of the original algebra.  The
displayed equation identifies the canonical equivalence on universal differentials. -/
@[stacks 07HW]
public noncomputable def dividedPowerEnvelopeDifferentialsEquiv
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (E : DividedPowerEnvelope A f J hJ) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B E.object := E.algebraMap.toRingHom.toAlgebra
    letI : Algebra A E.object := E.structureMap.toRingHom.toAlgebra
    { e : dividedPowerDifferentials
          (A := A) E.object.dividedPowers ≃ₗ[E.object]
          TensorProduct B E.object (KaehlerDifferential A B) //
      ∀ b : B,
        e (dividedPowerDifferential
            (A := A) E.object.dividedPowers (E.algebraMap.toRingHom b)) =
          (1 : E.object) ⊗ₜ[B] KaehlerDifferential.D A B b } := by
  classical
  let D := E.object
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B D := E.algebraMap.toRingHom.toAlgebra
  let M := TensorProduct B D (KaehlerDifferential A B)
  letI : IsScalarTower B D M := inferInstance
  letI instAM : Module A M := Module.compHom M (algebraMap A B)
  letI instABM : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Algebra A D := E.structureMap.toRingHom.toAlgebra
  have hcomp : (algebraMap B D).comp (algebraMap A B) = algebraMap A D := by
    change E.algebraMap.toRingHom.comp f = E.structureMap.toRingHom
    exact E.algebraMap_comp
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let dB : Derivation A B M :=
    Derivation.llcomp
      (TensorProduct.AlgebraTensorModule.mk B D D
        (KaehlerDifferential A B) 1)
      (KaehlerDifferential.D A B)
  let T := firstOrderExtension D M
  have hExt := firstOrderExtension_dividedPowers D M
  let δ := Classical.choose hExt
  have hcoords := (Classical.choose_spec hExt).1
  have hbase := (Classical.choose_spec hExt).2
  let pfun : B → T := fun b => (E.algebraMap.toRingHom b, dB b)
  let p : B →+* T := {
    toFun := pfun
    map_one' := by
      apply TrivSqZeroExt.ext
      · change E.algebraMap.toRingHom 1 = 1
        simp
      · change dB 1 = 0
        exact dB.map_one_eq_zero
    map_mul' := by
      intro b b'
      apply TrivSqZeroExt.ext
      · change E.algebraMap.toRingHom (b * b') =
          E.algebraMap.toRingHom b * E.algebraMap.toRingHom b'
        exact E.algebraMap.toRingHom.map_mul b b'
      · change TrivSqZeroExt.snd (pfun (b * b')) = TrivSqZeroExt.snd (pfun b * pfun b')
        rw [TrivSqZeroExt.snd_mul]
        change dB (b * b') = _
        rw [dB.leibniz]
        simp only [pfun, TrivSqZeroExt.fst, TrivSqZeroExt.snd, op_smul_eq_smul]
        change b • dB b' + b' • dB b =
          algebraMap B D b • dB b' + algebraMap B D b' • dB b
        rw [IsScalarTower.algebraMap_smul (R := B) (A := D) (M := M) b (dB b'),
          IsScalarTower.algebraMap_smul (R := B) (A := D) (M := M) b' (dB b)]
    map_zero' := by
      apply TrivSqZeroExt.ext
      · change E.algebraMap.toRingHom 0 = 0
        simp
      · change dB 0 = 0
        exact dB.map_zero
    map_add' := by
      intro b b'
      apply TrivSqZeroExt.ext
      · change E.algebraMap.toRingHom (b + b') =
          E.algebraMap.toRingHom b + E.algebraMap.toRingHom b'
        exact E.algebraMap.toRingHom.map_add b b'
      · change dB (b + b') = dB b + dB b'
        exact dB.map_add b b'
  }
  let C : DividedPowerRing := ⟨T, firstOrderExtensionIdeal D M, δ⟩
  have hp : J.map p ≤ C.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change (p b).1 ∈ D.ideal
    apply E.algebraMap.ideal_comp
    exact Ideal.mem_map_of_mem E.algebraMap.toRingHom hb
  let pPair : IdealPair.Hom J C.ideal := IdealPair.Hom.ofRingHom p hp
  let a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers :=
    (DividedPowers.DPMorphism.mk' hbase).comp E.structureMap
  have hpOver : IdealPair.Hom.comp pPair (IdealPair.Hom.ofRingHom f hJ) =
      IdealPair.Hom.ofDPMorphism a := by
    rw [IdealPair.Hom.mk.injEq]
    ext x
    · change E.algebraMap.toRingHom (f x) =
        TrivSqZeroExt.fst (algebraMap D T (E.structureMap.toRingHom x))
      rw [← E.algebraMap_comp]
      rfl
    · change dB (f x) = 0
      exact dB.map_algebraMap x
  let pOver : IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ)
      (IdealPair.Hom.ofDPMorphism a) := ⟨pPair, hpOver⟩
  let qData := (E.homEquiv C a).symm pOver
  let q : DividedPowers.DPMorphism D.dividedPowers C.dividedPowers := qData.1
  have hqB : q.toRingHom.comp E.algebraMap.toRingHom = p := by
    have hh := E.homEquiv_apply C a qData
    have hval : (E.homEquiv C a qData).1 = pPair := by
      change ((E.homEquiv C a) ((E.homEquiv C a).symm pOver)).1 = pPair
      exact congrArg Subtype.val (Equiv.apply_symm_apply (E.homEquiv C a) pOver)
    have hpairs :
        IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism q) E.algebraMap = pPair :=
      hh.symm.trans hval
    have hr := congrArg IdealPair.Hom.toRingHom hpairs
    change q.toRingHom.comp E.algebraMap.toRingHom = p at hr
    exact hr
  let pr : T →+* D := TrivSqZeroExt.fstHom D D M
  have hpr : DividedPowers.IsDPMorphism C.dividedPowers D.dividedPowers pr := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact hx
    · intro n x hx
      have hxD : pr x ∈ D.ideal := hx
      by_cases hn0 : n = 0
      · subst n
        rw [D.dividedPowers.dpow_zero hxD, C.dividedPowers.dpow_zero hx]
        exact pr.map_one.symm
      · by_cases hn1 : n = 1
        · subst n
          rw [D.dividedPowers.dpow_one hxD, C.dividedPowers.dpow_one hx]
        · have hn : 2 ≤ n := by omega
          have hc := hcoords n x hn hx
          exact hc.1.symm
  let prDP := DividedPowers.DPMorphism.mk' hpr
  let qpr := prDP.comp q
  have hqprA : qpr.comp E.structureMap = E.structureMap := by
    have hqA := congrArg DividedPowers.DPMorphism.toRingHom qData.2
    change q.toRingHom.comp E.structureMap.toRingHom = a.toRingHom at hqA
    apply DividedPowers.DPMorphism.ext
    ext x
    change pr ((q.toRingHom.comp E.structureMap.toRingHom) x) =
      E.structureMap.toRingHom x
    have hxA := congrArg (fun g : A →+* T => g x) hqA
    rw [hxA]
    change TrivSqZeroExt.fst (algebraMap D T (E.structureMap.toRingHom x)) = _
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    rfl
  let qprData : { r : DividedPowers.DPMorphism D.dividedPowers D.dividedPowers //
      r.comp E.structureMap = E.structureMap } := ⟨qpr, hqprA⟩
  let idData : { r : DividedPowers.DPMorphism D.dividedPowers D.dividedPowers //
      r.comp E.structureMap = E.structureMap } :=
    ⟨DividedPowers.DPMorphism.id D.dividedPowers, by
      apply DividedPowers.DPMorphism.ext
      ext x
      rfl⟩
  have hrestr : E.homEquiv D E.structureMap qprData =
      E.homEquiv D E.structureMap idData := by
    apply Subtype.ext
    rw [E.homEquiv_apply, E.homEquiv_apply]
    rw [IdealPair.Hom.mk.injEq]
    ext b
    change pr ((q.toRingHom.comp E.algebraMap.toRingHom) b) = E.algebraMap.toRingHom b
    rw [hqB]
    rfl
  have hqfst : (prDP.comp q).toRingHom = RingHom.id D := by
    have heq := (E.homEquiv D E.structureMap).injective hrestr
    have hqpr : qpr = DividedPowers.DPMorphism.id D.dividedPowers :=
      congrArg Subtype.val heq
    exact congrArg DividedPowers.DPMorphism.toRingHom hqpr
  have hfst (x : D) : TrivSqZeroExt.fst (q.toRingHom x) = x := by
    change pr (q.toRingHom x) = x
    exact congrArg (fun g : D →+* D => g x) hqfst
  have hqA : q.toRingHom.comp E.structureMap.toRingHom = a.toRingHom := by
    have h := congrArg DividedPowers.DPMorphism.toRingHom qData.2
    change q.toRingHom.comp E.structureMap.toRingHom = a.toRingHom at h
    exact h
  let dQ : DividedPowerDerivation A D E.structureMap.toRingHom M := {
    toDerivation := Derivation.mk' {
      toFun := fun x => TrivSqZeroExt.snd (q.toRingHom x)
      map_add' := by
        intro x y
        change TrivSqZeroExt.snd (q.toRingHom (x + y)) = _
        rw [q.toRingHom.map_add, TrivSqZeroExt.snd_add]
      map_smul' := by
        intro z x
        change TrivSqZeroExt.snd (q.toRingHom (z • x)) = _
        rw [map_zsmul, TrivSqZeroExt.snd_smul]
        rfl
    } (by
      intro x y
      change TrivSqZeroExt.snd (q.toRingHom (x * y)) = _
      rw [q.toRingHom.map_mul, TrivSqZeroExt.snd_mul]
      rw [hfst x, hfst y, op_smul_eq_smul]
      rfl)
    map_ringHom' := by
      intro x
      have h := congrArg (fun g : A →+* T => g x) hqA
      change q.toRingHom (E.structureMap.toRingHom x) = a.toRingHom x at h
      change TrivSqZeroExt.snd (q.toRingHom (E.structureMap.toRingHom x)) = 0
      rw [h]
      change TrivSqZeroExt.snd (algebraMap D T (E.structureMap.toRingHom x)) = 0
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      simp
    map_dpow' := by
      intro n hn x hx
      change TrivSqZeroExt.snd (q.toRingHom (D.dividedPowers.dpow n x)) = _
      by_cases hn1 : n = 1
      · subst n
        rw [D.dividedPowers.dpow_one hx, D.dividedPowers.dpow_zero hx]
        simp
      · have hn2 : 2 ≤ n := by omega
        have hxq : q.toRingHom x ∈ C.ideal :=
          q.ideal_comp (Ideal.mem_map_of_mem q.toRingHom hx)
        have hdp := q.dpow_comp (n := n) x hx
        rw [← hdp]
        rw [(hcoords n (q.toRingHom x) hn2 hxq).2, hfst]
        rfl
  }
  let Q := dividedPowerDifferentials
    (A := A) D.dividedPowers
  let rel := dividedPowerDifferentialRelations
    (A := A) D.dividedPowers
  let dCanon : DividedPowerDerivation A D E.structureMap.toRingHom Q := {
    toDerivation := Derivation.llcomp rel.mkQ
      (Derivation.restrictScalars ℤ (KaehlerDifferential.D A D))
    map_ringHom' := by
      intro x
      change rel.mkQ (KaehlerDifferential.D A D (E.structureMap.toRingHom x)) = 0
      exact congrArg rel.mkQ ((KaehlerDifferential.D A D).map_algebraMap x)
    map_dpow' := by
      intro n hn x hx
      change rel.mkQ (KaehlerDifferential.D A D (D.dividedPowers.dpow n x)) = _
      have hn' : n = (n - 1) + 1 := by omega
      rw [hn']
      exact dividedPowerDifferential_dpow
        (A := A) D.dividedPowers ⟨x, hx⟩ (n - 1)
  }
  have hdCanon (x : D) : dCanon x =
      dividedPowerDifferential
        (A := A) D.dividedPowers x := by
    change rel.mkQ (KaehlerDifferential.D A D x) =
      rel.mkQ (KaehlerDifferential.D A D x)
    rfl
  letI instModuleAQ : Module A Q := Module.compHom Q E.structureMap.toRingHom
  letI instTowerAQB : IsScalarTower A B Q := IsScalarTower.of_algebraMap_smul (fun a z => by
    change algebraMap B D (algebraMap A B a) • z = algebraMap A D a • z
    exact congrArg (fun r : D => r • z)
      (congrArg (fun k : A →+* D => k a) hcomp))
  letI instTowerBDQ : IsScalarTower B D Q := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  letI : Module Dᵐᵒᵖ Q :=
    Module.compHom Q (RingEquiv.toOpposite D).symm.toRingHom
  letI : IsCentralScalar D Q := ⟨by
    intro r z
    change (RingEquiv.toOpposite D).symm (MulOpposite.op r) • z = r • z
    simp [RingEquiv.toOpposite_symm_apply]⟩
  let dBQ : Derivation A B Q := {
    toFun := fun b => dCanon (E.algebraMap.toRingHom b)
    map_add' := by
      intro b b'
      change dCanon (E.algebraMap.toRingHom (b + b')) = _
      rw [map_add, dCanon.map_add]
    map_smul' := by
      intro a b
      change dCanon (E.algebraMap.toRingHom (algebraMap A B a * b)) = _
      rw [map_mul, dCanon.leibniz]
      have hmap : E.algebraMap.toRingHom (algebraMap A B a) =
          E.structureMap.toRingHom a := congrArg (fun k : A →+* D => k a)
            E.algebraMap_comp
      rw [hmap, dCanon.map_ringHom, smul_zero, add_zero]
      change E.structureMap.toRingHom a • dCanon (E.algebraMap.toRingHom b) =
        E.structureMap.toRingHom a • dCanon (E.algebraMap.toRingHom b)
      rfl
    map_one_eq_zero' := by
      change dCanon (E.algebraMap.toRingHom 1) = 0
      rw [map_one]
      exact dCanon.toDerivation.map_one_eq_zero
    leibniz' := by
      intro b b'
      change dCanon (E.algebraMap.toRingHom (b * b')) = _
      rw [map_mul, dCanon.leibniz]
      change algebraMap B D b • dCanon (E.algebraMap.toRingHom b') +
        algebraMap B D b' • dCanon (E.algebraMap.toRingHom b) = _
      rw [IsScalarTower.algebraMap_smul (R := B) (A := D) (M := Q) b,
        IsScalarTower.algebraMap_smul (R := B) (A := D) (M := Q) b']
      change b • dCanon (E.algebraMap.toRingHom b') +
        b' • dCanon (E.algebraMap.toRingHom b) =
        b • dCanon (E.algebraMap.toRingHom b') +
        b' • dCanon (E.algebraMap.toRingHom b)
      rfl
  }
  have hspanQ : Submodule.span D (Set.range (dCanon : D → Q)) = ⊤ := by
    change Submodule.span D (Set.range fun x : D => rel.mkQ
      (KaehlerDifferential.D A D x)) = ⊤
    have h := congrArg (Submodule.map rel.mkQ)
      (KaehlerDifferential.span_range_derivation A D)
    simpa only [LinearMap.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_mkQ] using h
  have hLift : ∃! lift : Q →ₗ[D] M,
      ∀ x : D,
        lift (dividedPowerDifferential
          (A := A) D.dividedPowers x) = dQ x := by
    let rel := dividedPowerDifferentialRelations
      (A := A) D.dividedPowers
    let : SMul A M := instAM.toDistribMulAction.toDistribSMul.toSMul
    let : IsScalarTower A D M := IsScalarTower.of_algebraMap_smul (fun a z => by
      have hmaps : algebraMap A D a = algebraMap B D (algebraMap A B a) :=
        congrArg (fun k : A →+* D => k a) hcomp.symm
      change algebraMap A D a • z = a • z
      rw [hmaps, IsScalarTower.algebraMap_smul (R := B) (A := D) (M := M)]
      exact IsScalarTower.algebraMap_smul (R := A) (A := B) (M := M) a z)
    let dA : Derivation A D M :=
      { toFun := dQ
        map_add' := dQ.map_add
        map_smul' := by
          intro a x
          rw [Algebra.smul_def, dQ.leibniz]
          have hz : dQ (algebraMap A D a) = 0 := by
            change dQ (E.structureMap.toRingHom a) = 0
            exact dQ.map_ringHom a
          rw [hz, smul_zero, add_zero]
          exact IsScalarTower.algebraMap_smul (R := A) (A := D) (M := M) a (dQ x)
        map_one_eq_zero' := dQ.map_one_eq_zero
        leibniz' := dQ.leibniz }
    let f : KaehlerDifferential A D →ₗ[D] M :=
      dA.liftKaehlerDifferential
    have hrel : rel ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, n⟩, rfl⟩
      change f (dividedPowerDifferentialRelation
        (A := A) D.dividedPowers x n) = 0
      simp only [dividedPowerDifferentialRelation,
        map_sub, map_smul]
      change dA.liftKaehlerDifferential
          (KaehlerDifferential.D A D (D.dividedPowers.dpow (n + 1) x)) -
        D.dividedPowers.dpow n x • dA.liftKaehlerDifferential
          (KaehlerDifferential.D A D x) = 0
      rw [dA.liftKaehlerDifferential_comp_D, dA.liftKaehlerDifferential_comp_D]
      change dQ (D.dividedPowers.dpow (n + 1) x) -
        D.dividedPowers.dpow n x • dQ x = 0
      rw [dQ.map_dpow (n + 1) (by omega) x x.property]
      simp
    let lift : Q →ₗ[D] M := rel.liftQ f hrel
    have hlift (x : D) :
        lift (dividedPowerDifferential
          (A := A) D.dividedPowers x) = dQ x := by
      change (rel.liftQ f hrel) (rel.mkQ (KaehlerDifferential.D A D x)) = dQ x
      rw [← LinearMap.comp_apply, rel.liftQ_mkQ]
      exact dA.liftKaehlerDifferential_comp_D x
    refine ⟨lift, hlift, ?_⟩
    intro g hg
    apply LinearMap.ext_on hspanQ
    rintro _ ⟨x, rfl⟩
    change g (dividedPowerDifferential (A := A) D.dividedPowers x) =
      lift (dividedPowerDifferential (A := A) D.dividedPowers x)
    rw [hg x, hlift x]
  let F := Classical.choose hLift.exists
  have hF := Classical.choose_spec hLift.exists
  let l : KaehlerDifferential A B →ₗ[B] Q :=
    @Derivation.liftKaehlerDifferential A B _ _ _ Q _ instModuleAQ
      (inferInstance : Module B Q) instTowerAQB dBQ
  have hlD (b : B) : l (KaehlerDifferential.D A B b) = dBQ b :=
    @Derivation.liftKaehlerDifferential_comp_D A B _ _ _ Q _ instModuleAQ
      (inferInstance : Module B Q) instTowerAQB dBQ b
  let g : M →ₗ[D] Q := l.liftBaseChange D
  have hdQB (b : B) : dQ (E.algebraMap.toRingHom b) = dB b := by
    change TrivSqZeroExt.snd (q.toRingHom (E.algebraMap.toRingHom b)) =
      TrivSqZeroExt.snd (p b)
    have hh := congrArg (fun k : B →+* T => k b) hqB
    change q.toRingHom (E.algebraMap.toRingHom b) = p b at hh
    exact congrArg (fun z : T => TrivSqZeroExt.snd z) hh
  have hgB (b : B) : g (dB b) = dCanon (E.algebraMap.toRingHom b) := by
    change l.liftBaseChange D
      (1 ⊗ₜ[B] KaehlerDifferential.D A B b) = _
    rw [LinearMap.liftBaseChange_one_tmul]
    rw [hlD]
    rfl
  have hFg_on_D (b : B) : F (dCanon (E.algebraMap.toRingHom b)) = dB b := by
    rw [hdCanon]
    rw [hF]
    exact hdQB b
  have hFg_one (w : KaehlerDifferential A B) :
      F (g (TensorProduct.AlgebraTensorModule.mk B D D
        (KaehlerDifferential A B) 1 w)) =
        TensorProduct.AlgebraTensorModule.mk B D D (KaehlerDifferential A B) 1 w := by
    let m : KaehlerDifferential A B →ₗ[B] M :=
      TensorProduct.AlgebraTensorModule.mk B D D (KaehlerDifferential A B) 1
    have hmaps : ((F.comp g).restrictScalars B).comp m = m := by
      apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
      rintro _ ⟨b, rfl⟩
      change F (g (dB b)) = dB b
      rw [hgB, hFg_on_D]
    exact congrArg (fun k : KaehlerDifferential A B →ₗ[B] M => k w) hmaps
  have hFG : F.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add, hx, hy, LinearMap.id_apply]
    | tmul d w =>
        change F (g (d ⊗ₜ[B] w)) = d ⊗ₜ[B] w
        rw [TensorProduct.tmul_eq_smul_one_tmul (R := B) (S := D) d w]
        simp only [map_smul]
        change d • F (g (TensorProduct.AlgebraTensorModule.mk B D D
          (KaehlerDifferential A B) 1 w)) =
          d • TensorProduct.AlgebraTensorModule.mk B D D
            (KaehlerDifferential A B) 1 w
        exact congrArg (fun z : M => d • z) (hFg_one w)
  let dGF : DividedPowerDerivation A D E.structureMap.toRingHom Q := {
    toDerivation := Derivation.llcomp (g.comp F) dCanon.toDerivation
    map_ringHom' := by
      intro a
      change (g.comp F) (dCanon (E.structureMap.toRingHom a)) = 0
      rw [dCanon.map_ringHom]
      simp
    map_dpow' := by
      intro n hn x hx
      change (g.comp F) (dCanon (D.dividedPowers.dpow n x)) =
        D.dividedPowers.dpow (n - 1) x • (g.comp F) (dCanon x)
      rw [dCanon.map_dpow n hn x hx, LinearMap.map_smul_of_tower]
  }
  have hdGF_B (b : B) : dGF (E.algebraMap.toRingHom b) =
      dCanon (E.algebraMap.toRingHom b) := by
    change g (F (dCanon (E.algebraMap.toRingHom b))) = _
    rw [hFg_on_D, hgB]
  have hdGF : dGF = dCanon := by
    let M := Q
    let T := firstOrderExtension D M
    have hExt := firstOrderExtension_dividedPowers D M
    let δ := Classical.choose hExt
    have hcoords := (Classical.choose_spec hExt).1
    have hbase := (Classical.choose_spec hExt).2
    let C : DividedPowerRing := ⟨T, firstOrderExtensionIdeal D M, δ⟩
    let baseDP : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers :=
      (DividedPowers.DPMorphism.mk' hbase).comp E.structureMap
    let rpfun (d : DividedPowerDerivation A D
        E.structureMap.toRingHom M) : D → TrivSqZeroExt D M := fun x => (x, d x)
    let rfun (d : DividedPowerDerivation A D
        E.structureMap.toRingHom M) : D →+* TrivSqZeroExt D M := {
      toFun := rpfun d
      map_one' := by
        apply TrivSqZeroExt.ext
        · rfl
        · exact d.map_one_eq_zero
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · rfl
        · change TrivSqZeroExt.snd (rpfun d (x * y)) =
            TrivSqZeroExt.snd (rpfun d x * rpfun d y)
          rw [TrivSqZeroExt.snd_mul]
          change d (x * y) = _
          rw [d.leibniz]
          simp only [rpfun, TrivSqZeroExt.fst, TrivSqZeroExt.snd, op_smul_eq_smul]
      map_zero' := by
        apply TrivSqZeroExt.ext
        · rfl
        · exact d.map_zero
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · rfl
        · change d (x + y) = d x + d y
          exact d.map_add x y
    }
    let r (d : DividedPowerDerivation A D
        E.structureMap.toRingHom M) : DividedPowers.DPMorphism D.dividedPowers C.dividedPowers :=
      DividedPowers.DPMorphism.mk' (f := rfun d) (by
        refine ⟨?_, ?_⟩
        · rw [Ideal.map_le_iff_le_comap]
          intro x hx
          exact hx
        · intro n x hx
          have hxT : rfun d x ∈ C.ideal := hx
          by_cases hn0 : n = 0
          · subst n
            rw [C.dividedPowers.dpow_zero hxT, D.dividedPowers.dpow_zero hx]
            apply TrivSqZeroExt.ext
            · rfl
            · simp
          · by_cases hn1 : n = 1
            · subst n
              rw [C.dividedPowers.dpow_one hxT, D.dividedPowers.dpow_one hx]
            · have hn2 : 2 ≤ n := by omega
              have hc := hcoords n (rfun d x) hn2 hxT
              have hfst : TrivSqZeroExt.fst (rfun d x) = x := rfl
              have hsnd : TrivSqZeroExt.snd (rfun d x) = d x := rfl
              apply TrivSqZeroExt.ext
              · change TrivSqZeroExt.fst (δ.dpow n (rfun d x)) =
                  D.dividedPowers.dpow n x
                simpa only [hfst] using hc.1
              · rw [show TrivSqZeroExt.snd (δ.dpow n (rfun d x)) =
                  D.dividedPowers.dpow (n - 1) x • d x by
                    simpa only [hfst, hsnd] using hc.2]
                change D.dividedPowers.dpow (n - 1) x • d x =
                  d (D.dividedPowers.dpow n x)
                exact (d.map_dpow n (by omega) x hx).symm)
    let r₁ := r dGF
    let r₂ := r dCanon
    have hrA (d : DividedPowerDerivation A D
        E.structureMap.toRingHom M) : (r d).comp E.structureMap = baseDP := by
      apply DividedPowers.DPMorphism.ext
      ext x
      · change E.structureMap.toRingHom x =
          TrivSqZeroExt.fst (algebraMap D T (E.structureMap.toRingHom x))
        rw [TrivSqZeroExt.algebraMap_eq_inl]
        rfl
      · change d (E.structureMap.toRingHom x) = 0
        exact d.map_ringHom x
    let r₁Data : { r : DividedPowers.DPMorphism D.dividedPowers C.dividedPowers //
        r.comp E.structureMap = baseDP } := ⟨r dGF, hrA dGF⟩
    let r₂Data : { r : DividedPowers.DPMorphism D.dividedPowers C.dividedPowers //
        r.comp E.structureMap = baseDP } := ⟨r dCanon, hrA dCanon⟩
    have hrestr : E.homEquiv C baseDP r₁Data = E.homEquiv C baseDP r₂Data := by
      apply Subtype.ext
      rw [E.homEquiv_apply, E.homEquiv_apply]
      apply IdealPair.Hom.ext_toRingHom
      ext b
      · rfl
      · exact hdGF_B b
    have heq := (E.homEquiv C baseDP).injective hrestr
    have hr : r₁.toRingHom = r₂.toRingHom :=
      congrArg DividedPowers.DPMorphism.toRingHom (congrArg Subtype.val heq)
    apply DividedPowerDerivation.ext
    intro x
    exact congrArg TrivSqZeroExt.snd (congrArg (fun g : D →+* T => g x) hr)
  have hGF : g.comp F = LinearMap.id := by
    apply LinearMap.ext_on hspanQ
    rintro _ ⟨x, rfl⟩
    exact congrArg (fun k : D → Q => k x) (congrArg
      (fun e : DividedPowerDerivation A D E.structureMap.toRingHom Q =>
        (e : D → Q)) hdGF)
  let e : Q ≃ₗ[D] M := LinearEquiv.ofLinearMap F g hFG hGF
  refine ⟨e, ?_⟩
  intro b
  rw [← hdCanon]
  change F (dCanon (E.algebraMap.toRingHom b)) =
    TensorProduct.AlgebraTensorModule.mk B D D (KaehlerDifferential A B) 1
      (KaehlerDifferential.D A B b)
  rw [hFg_on_D]
  rfl

end Crystalline

end
