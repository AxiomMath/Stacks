module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FirstOrderExtension

/-!
# The cosimplicial module of completed divided power differentials is homotopic to zero

Work in an affine crystalline situation `(A, I, γ)` with target `C`, write `X = Spec(C)` and
`S = Spec(A)`, choose a polynomial algebra `P = A[x_i]` over `A` and a surjection `P → C`.  For
`n ≥ 0` let `J(n)` be the kernel of the induced surjection `P ⊗_A ⋯ ⊗_A P → C` from the
`(n + 1)`-fold tensor power and let `D(n)` be the `p`-adic completion of the divided power
envelope of `J(n)`.  The rings `D(0), D(1), D(2), …` form a cosimplicial ring `D(*)`, and the
`p`-adically completed modules of divided power differentials `Ω_{D(n)}`, with their derivations
`d : D(n) → Ω_{D(n)}`, form a cosimplicial module `Ω_{D(*)}` over `D(*)`.

This file proves that the complex `Ω_{D(0)} → Ω_{D(1)} → Ω_{D(2)} → ⋯` is homotopic to zero as a
`D(*)`-cosimplicial module.  The reason is that `Ω_{D(n)}` is the completion of a free module on
the differentials of the variables `x_i(e)`, one copy of the module on the vertices of the
simplex for each variable `x_i`, and the structure maps permute those generators exactly as the
maps of finite ordinals permute the vertices.  The contracting homotopy of the module on the
vertices therefore carries over, generator by generator.

## Main definitions

* `Crystalline.CosimplicialEnvelope` — the cosimplicial ring `D(*)` of completed divided power
  envelopes of a polynomial presentation together with the cosimplicial module `Ω_{D(*)}` of
  completed divided power differentials over it.

## Main results

* `Crystalline.id_cosimplicialEnvelopeDifferentials_homotopic_zero` — the identity endomorphism
  of `Ω_{D(*)}` is homotopic to its zero endomorphism.

## Implementation notes

The cosimplicial data are recorded as a structure rather than constructed: its fields identify
the degrees with the completed envelopes and the completed differentials, say that the
cosimplicial ring maps are the ones induced by the reindexings of the variables and are divided
power morphisms, and say that the module's structure maps are the semilinear adically continuous
maps compatible with the derivations.  Those conditions determine the data, because the image of
the derivation generates the completed differentials `p`-adically.

`CosimplicialEnvelope` carries no tag of its own.  It is the notation attached to the displayed
equations for `D` and `D(n)`, which assert nothing, and it is deliberately not tagged with the
proposition whose statement uses that notation: that proposition computes the derived global
sections of a sheaf on the crystalline site by the associated complex, and nothing of that is
proved here.

The homotopy is written on the free basis of the divided power differentials of the envelope of
`J(n)` over the variables `x_i(e)`, then completed.  That basis comes from the identification of
the divided power differentials of a divided power envelope with the base change of the ordinary
Kähler differentials, which is `Crystalline.dividedPowerEnvelopeDifferentialsEquiv`.  That
statement requires the algebra and the base divided power ring to share a universe, which the
polynomial algebra on a family of variables indexed by an arbitrary type does not; the version
proved here, `envelopeDifferentialsBaseChangeEquiv`, keeps the two universes apart and is
otherwise the same result, so it is left untagged.

Two elaboration costs are worth recording.  Separating the universes makes the proof of the
base change identification exceed the default heartbeat budget; extracting from it the
statement that two divided power derivations out of an envelope agreeing on the image of the
original algebra are equal brings both pieces back inside the default budget.  And the
universal derivation of `D(n)` must be given an explicit type as a `def` rather than being left
as a reducible `abbrev` for the projection out of the universal differential of the completed
envelope: as an `abbrev` its projection forces whole-term reduction through that declaration's
`let`-chain type every time a field of `CosimplicialEnvelope` mentions it, which is what makes
elaborating the structure expensive.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07L9](https://stacks.math.columbia.edu/tag/07L9)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Equation 60.21.1, Tag 07L0](https://stacks.math.columbia.edu/tag/07L0)
* [Stacks Project, Lemma 60.6.6, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped TensorProduct

universe u v w

namespace Crystalline

/-- Two divided power morphisms out of a divided power envelope `D` of `(B, J)` over `A` which
agree on `A` and on the image of `B` are equal, by the universal property of the envelope. -/
private lemma dpMorphism_eq_of_eq_on_image
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
    (E : DividedPowerEnvelope A f J hJ) {C : DividedPowerRing.{max u v}}
    {r₁ r₂ : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers}
    (hA : r₁.comp E.structureMap = r₂.comp E.structureMap)
    (hB : ∀ b : B, r₁.toRingHom (E.algebraMap.toRingHom b) =
      r₂.toRingHom (E.algebraMap.toRingHom b)) :
    r₁ = r₂ := by
  have h := (E.homEquiv C (r₂.comp E.structureMap)).injective
    (a₁ := ⟨r₁, hA⟩) (a₂ := ⟨r₂, rfl⟩) (by
      apply Subtype.ext
      rw [E.homEquiv_apply, E.homEquiv_apply]
      apply IdealPair.Hom.ext_toRingHom
      ext b
      exact hB b)
  exact congrArg Subtype.val h

/-- Two divided power derivations out of a divided power envelope `D` of `(B, J)` over `A`
which agree on the image of `B` are equal.  Indeed a derivation into a `D`-module `M` is the
same thing as a divided power morphism from `D` to the first-order thickening `D ⊕ M` over `A`
which is the identity in the first coordinate, and such morphisms are determined by their
restriction along `B → D` by the universal property of the envelope. -/
private lemma dividedPowerDerivation_eq_of_eq_on_image
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
    (E : DividedPowerEnvelope A f J hJ) {M : Type (max u v)} [AddCommGroup M]
    [Module E.object M] [Module E.objectᵐᵒᵖ M] [IsCentralScalar E.object M]
    {d₁ d₂ : DividedPowerDerivation A E.object E.structureMap.toRingHom M}
    (h : ∀ b : B, d₁ (E.algebraMap.toRingHom b) = d₂ (E.algebraMap.toRingHom b)) :
    d₁ = d₂ := by
  classical
  let D := E.object
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
  have hr : (r d₁).toRingHom = (r d₂).toRingHom := by
    refine congrArg DividedPowers.DPMorphism.toRingHom
      (dpMorphism_eq_of_eq_on_image E ((hrA d₁).trans (hrA d₂).symm) fun b => ?_)
    apply TrivSqZeroExt.ext
    · rfl
    · exact h b
  apply DividedPowerDerivation.ext
  intro x
  have hh := congrArg (fun g : D →+* T => g x) hr
  exact congrArg TrivSqZeroExt.snd hh

/-- The divided power differentials of a divided power envelope are canonically the base change
of the ordinary Kähler differentials of the original algebra, and the displayed equation pins the
equivalence down on universal differentials.

This is `Crystalline.dividedPowerEnvelopeDifferentialsEquiv` for an algebra whose underlying
type may live in a universe other than that of the base divided power ring, as happens for a
polynomial algebra on a family of variables indexed by an arbitrary type; that declaration is
stated only when the two universes agree, so it does not apply here.  Being a generalization of
an already tagged result it carries no tag of its own. -/
private noncomputable def envelopeDifferentialsBaseChangeEquiv
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] [Algebra A B]
    (J : Ideal B) (hJ : A.ideal.map (algebraMap A B) ≤ J)
    (E : DividedPowerEnvelope A (algebraMap A B) J hJ) :
    letI : Algebra B E.object := E.algebraMap.toRingHom.toAlgebra
    letI : Algebra A E.object := E.structureMap.toRingHom.toAlgebra
    { e : dividedPowerDifferentials
          (A := A) E.object.dividedPowers ≃ₗ[E.object]
          TensorProduct B E.object (KaehlerDifferential A B) //
      ∀ b : B,
        e (dividedPowerDifferential
            (A := A) E.object.dividedPowers (E.algebraMap.toRingHom b)) =
          (1 : E.object) ⊗ₜ[B] KaehlerDifferential.D A B b } := by
  let D := E.object
  let : Algebra B D := E.algebraMap.toRingHom.toAlgebra
  let M := TensorProduct B D (KaehlerDifferential A B)
  let : IsScalarTower B D M := inferInstance
  let instAM : Module A M := Module.compHom M (algebraMap A B)
  let instABM : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Algebra A D := E.structureMap.toRingHom.toAlgebra
  have hcomp : (algebraMap B D).comp (algebraMap A B) = algebraMap A D := by
    change E.algebraMap.toRingHom.comp (algebraMap A B) = E.structureMap.toRingHom
    exact E.algebraMap_comp
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' (by
    exact hcomp.symm)
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
  have hpOver : IdealPair.Hom.comp pPair (IdealPair.Hom.ofRingHom (algebraMap A B) hJ) =
      IdealPair.Hom.ofDPMorphism a := by
    rw [IdealPair.Hom.mk.injEq]
    ext x
    · change E.algebraMap.toRingHom (algebraMap A B x) =
        TrivSqZeroExt.fst (algebraMap D T (E.structureMap.toRingHom x))
      rw [← E.algebraMap_comp]
      rfl
    · change dB (algebraMap A B x) = 0
      exact dB.map_algebraMap x
  let pOver : IdealPair.HomOver (IdealPair.Hom.ofRingHom (algebraMap A B) hJ)
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
  have hqfst : (prDP.comp q).toRingHom = RingHom.id D :=
    congrArg DividedPowers.DPMorphism.toRingHom
      (dpMorphism_eq_of_eq_on_image E (r₂ := DividedPowers.DPMorphism.id D.dividedPowers)
        hqprA fun b => by
          change pr ((q.toRingHom.comp E.algebraMap.toRingHom) b) = E.algebraMap.toRingHom b
          rw [hqB]
          rfl)
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
  let instModuleAQ : Module A Q := Module.compHom Q E.structureMap.toRingHom
  let instTowerAQB : IsScalarTower A B Q := IsScalarTower.of_algebraMap_smul (fun a z => by
    change algebraMap B D (algebraMap A B a) • z = algebraMap A D a • z
    exact congrArg (fun r : D => r • z)
      (congrArg (fun k : A →+* D => k a) hcomp))
  let instTowerBDQ : IsScalarTower B D Q := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  let : Module Dᵐᵒᵖ Q :=
    Module.compHom Q (RingEquiv.toOpposite D).symm.toRingHom
  let : IsCentralScalar D Q := ⟨by
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
      rw [Algebra.smul_def]
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
    induction x using TensorProduct.inductionOn with
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
  have hdGF : dGF = dCanon := dividedPowerDerivation_eq_of_eq_on_image E hdGF_B
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

/-! ### The cosimplicial ring `D(*)` and the cosimplicial module `Ω_{D(*)}` -/

/-- The reindexing of the variables of an `(n + 1)`-fold tensor power of a polynomial algebra
induced by a map of finite ordinals: the variable `x_i(e)` of the factor of index `e` is sent to
the variable `x_i(φ(e))`. -/
public def tensorPowerVariableMap {ι : Type w} {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    Fin (m + 1) × ι → Fin (n + 1) × ι :=
  fun q ↦ (φ.toOrderHom q.1, q.2)

section CosimplicialEnvelope

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- The divided power envelope of the kernel `J(n)` of the surjection onto `C` from the
`(n + 1)`-fold tensor power `P ⊗_A ⋯ ⊗_A P` of a polynomial presentation `P → C`.  Its `p`-adic
completion is the ring `D(n)`. -/
public noncomputable abbrev tensorPowerEnvelope (n : ℕ) :=
  polynomialDividedPowerEnvelope s (tensorPowerPresentation s f n)

/-- The canonical ring map `P ⊗_A ⋯ ⊗_A P → D(n)`: the map to the divided power envelope of
`J(n)` followed by the map to its `p`-adic completion. -/
public noncomputable abbrev tensorPowerEnvelopeMap (n : ℕ) :
    MvPolynomial (Fin (n + 1) × ι) s.A →+* pAdicCompletedTensorPowerEnvelope s f hf n :=
  toPAdicCompletedDividedPowerEnvelope s (tensorPowerPresentation s f n)
    (tensorPowerPresentation_surjective s f hf n)

/-- The module `Ω_{D(n)}`: the `p`-adic completion of the module of divided power differentials
of the divided power envelope of `J(n)`. -/
public noncomputable abbrev completedTensorPowerDifferentials (n : ℕ) : Type (max u w) :=
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  AdicCompletion
    (DividedPowers.pAdicIdeal (A := (tensorPowerEnvelope s f n).object) s.p)
    (dividedPowerDifferentials (A := (s.A : Type u))
      (tensorPowerEnvelope s f n).object.dividedPowers)

/-- The divided powers of `D(n)` together with the universal derivation
`d : D(n) → Ω_{D(n)}`, obtained from the universal divided power differential of the completed
envelope of the presentation of `C` by the `(n + 1)`-fold tensor power. -/
public noncomputable abbrev completedTensorPowerDifferential (n : ℕ) :=
  completedDividedPowerDifferential s (tensorPowerPresentation s f n)
    (tensorPowerPresentation_surjective s f hf n)

/-- The ring `D(n)` as a divided power ring: its divided power ideal is `J̄(n)` and its divided
powers are `γ̄(n)`, the extensions to the completion of the divided powers of the envelope of
`J(n)`. -/
public noncomputable abbrev completedTensorPowerDividedPowerRing (n : ℕ) :
    DividedPowerRing.{max u w} :=
  DividedPowerRing.of (pAdicCompletedTensorPowerEnvelope s f hf n)
    (DividedPowers.completionIdeal (tensorPowerEnvelope s f n).object.ideal s.p
      (completedTensorPowerDifferential s f hf n).1)
    (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
      (tensorPowerEnvelope s f n).object.dividedPowers s.p
      (completedTensorPowerDifferential s f hf n).1).1

/-- The universal derivation `d : D(n) → Ω_{D(n)}`, a divided power `A`-derivation of the
divided power ring `(D(n), J̄(n), γ̄(n))`. -/
public noncomputable def tensorPowerDerivation (n : ℕ) :
    DividedPowerDerivation (s.A : Type u) (completedTensorPowerDividedPowerRing s f hf n)
      (algebraMap (s.A : Type u) (pAdicCompletedTensorPowerEnvelope s f hf n))
      (completedTensorPowerDifferentials s f n) :=
  (completedTensorPowerDifferential s f hf n).2.1

/-- The cosimplicial ring `D(0), D(1), D(2), …` of `p`-adically completed divided power
envelopes of a polynomial presentation of `C`, whose structure maps are induced by the
reindexings of the variables, together with the cosimplicial module `Ω_{D(*)}` of completed
divided power differentials over it, whose structure maps are compatible with the universal
derivations. -/
public structure CosimplicialEnvelope where
  /-- The cosimplicial ring `D(*)`. -/
  ring : CosimplicialObject CommRingCat.{max u w}
  /-- Its degree `n` is the `p`-adically completed divided power envelope `D(n)` of `J(n)`. -/
  ringEquiv (n : ℕ) : ring.obj ⦋n⦌ ≃+* pAdicCompletedTensorPowerEnvelope s f hf n
  /-- The cosimplicial structure maps are induced by the reindexings of the variables: a map
  `φ : ⦋m⦌ ⟶ ⦋n⦌` sends the variable of the factor of index `e` to the variable of the factor
  of index `φ(e)`. -/
  ringEquiv_naturality {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
      (q : MvPolynomial (Fin (m + 1) × ι) s.A) :
    ringEquiv n (ring.map φ ((ringEquiv m).symm (tensorPowerEnvelopeMap s f hf m q))) =
      tensorPowerEnvelopeMap s f hf n
        (MvPolynomial.rename (tensorPowerVariableMap φ) q)
  /-- Every cosimplicial structure map is a divided power morphism of the completed divided
  power envelopes, not merely a ring map agreeing on the image of the polynomial algebra. -/
  ringEquiv_dp_naturality {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    DividedPowers.IsDPMorphism
      (completedTensorPowerDividedPowerRing s f hf m).dividedPowers
      (completedTensorPowerDividedPowerRing s f hf n).dividedPowers
      ((ringEquiv n).toRingHom.comp ((ring.map φ).hom.comp (ringEquiv m).symm.toRingHom))
  /-- The cosimplicial module `Ω_{D(*)}` over `D(*)`. -/
  differentials : CosimplicialModule ring
  /-- Its degree `n` is the completed module of divided power differentials `Ω_{D(n)}`. -/
  differentialsEquiv (n : ℕ) :
    differentials.obj (op (op ⦋n⦌)) ≃+ completedTensorPowerDifferentials s f n
  /-- The identification in degree `n` is linear over the identification of the rings. -/
  differentialsEquiv_smul (n : ℕ) (r : ring.obj ⦋n⦌) (x : differentials.obj (op (op ⦋n⦌))) :
    differentialsEquiv n (r • x) = ringEquiv n r • differentialsEquiv n x
  /-- The cosimplicial structure maps of `Ω_{D(*)}` are compatible with the universal
  derivations `d : D(n) → Ω_{D(n)}`. -/
  differentialsEquiv_naturality {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
      (x : ring.obj ⦋m⦌) :
    differentialsEquiv n (differentials.map φ.op.op
        ((differentialsEquiv m).symm
          (tensorPowerDerivation s f hf m (ringEquiv m x)))) =
      tensorPowerDerivation s f hf n (ringEquiv n (ring.map φ x))
  /-- The cosimplicial structure maps of `Ω_{D(*)}` are adically continuous.  Together with the
  previous equation and their semilinearity this determines them, because the image of the
  universal derivation generates `Ω_{D(n)}` `p`-adically. -/
  differentialsEquiv_adicContinuous {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    SemilinearCosimplicialModule.AdicContinuous
      (DividedPowers.pAdicIdeal (A := (tensorPowerEnvelope s f m).object) s.p)
      (DividedPowers.pAdicIdeal (A := (tensorPowerEnvelope s f n).object) s.p)
      (fun x ↦ differentialsEquiv n
        (differentials.map φ.op.op ((differentialsEquiv m).symm x)))

end CosimplicialEnvelope

/-! ### The free basis of the divided power differentials of the envelope of `J(n)` -/

section Basis

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The divided power differentials of the divided power envelope of `J(n)` are the base change
to that envelope of the Kähler differentials of the polynomial algebra
`P ⊗_A ⋯ ⊗_A P = A[x_i(e)]`. -/
private noncomputable def tensorPowerDifferentialsToTensor (n : ℕ) :
    let B := MvPolynomial (Fin (n + 1) × ι) s.A
    let D := (tensorPowerEnvelope s f n).object
    letI : Algebra (s.A : Type u) D :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    letI : Algebra B D := (tensorPowerEnvelope s f n).algebraMap.toRingHom.toAlgebra
    dividedPowerDifferentials (A := (s.A : Type u)) D.dividedPowers ≃ₗ[D]
      TensorProduct B D (KaehlerDifferential (s.A : Type u) B) := by
  let B := MvPolynomial (Fin (n + 1) × ι) s.A
  let env := tensorPowerEnvelope s f n
  let : Algebra (s.A : Type u) env.object := env.structureMap.toRingHom.toAlgebra
  let : Algebra B env.object := env.algebraMap.toRingHom.toAlgebra
  simpa [B, env, tensorPowerEnvelope] using
    (envelopeDifferentialsBaseChangeEquiv s.A _ _ env).1

/-- The divided power differentials of the divided power envelope of `J(n)` are free on the
differentials of the variables `x_i(e)` of the `(n + 1)`-fold tensor power. -/
@[no_expose] public noncomputable def tensorPowerDifferentialsBasis (n : ℕ) :
    let D := (tensorPowerEnvelope s f n).object
    letI : Algebra (s.A : Type u) D :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    Module.Basis (Fin (n + 1) × ι) D
      (dividedPowerDifferentials (A := (s.A : Type u)) D.dividedPowers) := by
  let B := MvPolynomial (Fin (n + 1) × ι) s.A
  let D := (tensorPowerEnvelope s f n).object
  let : Algebra (s.A : Type u) D := (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  let : Algebra B D := (tensorPowerEnvelope s f n).algebraMap.toRingHom.toAlgebra
  exact ((KaehlerDifferential.mvPolynomialBasis (s.A : Type u) (Fin (n + 1) × ι)).baseChange D).map
    (tensorPowerDifferentialsToTensor s f n).symm

/-- The basis vector of index `k` is the universal divided power differential of the variable
`x_k` of the `(n + 1)`-fold tensor power. -/
public lemma tensorPowerDifferentialsBasis_apply (n : ℕ) (k : Fin (n + 1) × ι) :
    let env := tensorPowerEnvelope s f n
    letI : Algebra (s.A : Type u) env.object := env.structureMap.toRingHom.toAlgebra
    tensorPowerDifferentialsBasis s f n k = dividedPowerDifferential env.object.dividedPowers
      (env.algebraMap.toRingHom (MvPolynomial.X k)) := by
  let B := MvPolynomial (Fin (n + 1) × ι) s.A
  let env := tensorPowerEnvelope s f n
  let : Algebra (s.A : Type u) env.object := env.structureMap.toRingHom.toAlgebra
  let : Algebra B env.object := env.algebraMap.toRingHom.toAlgebra
  apply (tensorPowerDifferentialsToTensor s f n).injective
  simp only [tensorPowerDifferentialsBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, LinearEquiv.apply_symm_apply]
  exact ((envelopeDifferentialsBaseChangeEquiv s.A _ _ env).2 (MvPolynomial.X k)).symm

end Basis

/-! ### The contracting homotopy of `Ω_{D(*)}` -/

section Homotopy

/-- Two adically continuous additive maps out of the completion of a free module agree as soon
as they agree on the completed basis vectors and their difference is compatible with the
scalars of the completed ring. -/
private lemma adicCompletion_ext_basis
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    {M N κ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (b : Module.Basis κ R M) {F G : AdicCompletion I M →+ AdicCompletion J N}
    (hF : SemilinearCosimplicialModule.AdicContinuous I J F)
    (hG : SemilinearCosimplicialModule.AdicContinuous I J G)
    (hsmul : ∀ (r : AdicCompletion I R) x, F x = G x → F (r • x) = G (r • x))
    (hgen : ∀ k, F (AdicCompletion.of I M (b k)) = G (AdicCompletion.of I M (b k))) :
    F = G := by
  apply adicContinuous_ext I J F G hF hG
  intro x
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hgen k
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    simpa only [map_smul, IsScalarTower.algebraMap_smul] using
      hsmul (algebraMap R (AdicCompletion I R) r) (AdicCompletion.of I M x) hx

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The component of the contracting homotopy on the divided power differentials of the envelope
of `J(n)`: at a simplex `α` of `Δ[1]` it fixes the basis vector `dx_i(e)` when `α` vanishes at
the vertex `e`, and sends it to zero in the other case. -/
private noncomputable def tensorPowerHomotopyMap (n : ℕ)
    (α : (Δ[1] : SSet.{0}).obj (op ⦋n⦌)) :
    let B := MvPolynomial (Fin (n + 1) × ι) s.A
    let D := (tensorPowerEnvelope s f n).object
    letI : Algebra (s.A : Type u) D :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    letI : Algebra B D := (tensorPowerEnvelope s f n).algebraMap.toRingHom.toAlgebra
    dividedPowerDifferentials (A := (s.A : Type u)) D.dividedPowers →ₗ[D]
      dividedPowerDifferentials (A := (s.A : Type u)) D.dividedPowers := by
  classical
  exact (tensorPowerDifferentialsBasis s f n).constr (tensorPowerEnvelope s f n).object (fun k =>
    if (SSet.stdSimplex.objEquiv α).toOrderHom k.1 = 0 then
      tensorPowerDifferentialsBasis s f n k else 0)

variable (hf : Function.Surjective f)

/-- The completed basis vector `dx_k` of `Ω_{D(n)}`. -/
private noncomputable abbrev completedGenerator (n : ℕ) (k : Fin (n + 1) × ι) :
    completedTensorPowerDifferentials s f n :=
  AdicCompletion.of _ _ (tensorPowerDifferentialsBasis s f n k)

/-- The universal derivation of `D(n)` takes the variable `x_k` to the completed basis vector
`dx_k`. -/
private lemma tensorPowerDerivation_variable (n : ℕ) (k : Fin (n + 1) × ι) :
    tensorPowerDerivation s f hf n (tensorPowerEnvelopeMap s f hf n (MvPolynomial.X k)) =
      completedGenerator s f n k := by
  rw [completedGenerator, tensorPowerDifferentialsBasis_apply]
  exact (completedTensorPowerDifferential s f hf n).2.2 _

/-- The component of the contracting homotopy on `Ω_{D(n)}`, the completion of the component on
the divided power differentials of the envelope of `J(n)`. -/
private noncomputable abbrev completedHomotopyLinearMap (n : ℕ)
    (α : (Δ[1] : SSet.{0}).obj (op ⦋n⦌)) :
    completedTensorPowerDifferentials s f n →ₗ[pAdicCompletedTensorPowerEnvelope s f hf n]
      completedTensorPowerDifferentials s f n :=
  AdicCompletion.map _ (tensorPowerHomotopyMap s f n α)

/-- The component of the contracting homotopy fixes the completed basis vector `dx_k` when the
simplex vanishes at the vertex of `k`, and sends it to zero in the other case. -/
private lemma completedHomotopyLinearMap_generator (n : ℕ)
    (α : (Δ[1] : SSet.{0}).obj (op ⦋n⦌)) (k : Fin (n + 1) × ι) :
    completedHomotopyLinearMap s f hf n α (completedGenerator s f n k) =
      if (SSet.stdSimplex.objEquiv α).toOrderHom k.1 = 0 then
        completedGenerator s f n k else 0 := by
  classical
  simp only [completedHomotopyLinearMap, completedGenerator, AdicCompletion.map_of,
    tensorPowerHomotopyMap, Module.Basis.constr_basis]
  split_ifs <;> simp

/-- At the constant simplex `0` the component of the contracting homotopy is the identity. -/
private lemma completedHomotopyLinearMap_zero (n : ℕ) :
    completedHomotopyLinearMap s f hf n (SSet.stdSimplex.const 1 0 (op ⦋n⦌)) =
      LinearMap.id := by
  have h : tensorPowerHomotopyMap s f n (SSet.stdSimplex.const 1 0 (op ⦋n⦌)) = LinearMap.id := by
    apply (tensorPowerDifferentialsBasis s f n).ext
    intro k
    simp only [tensorPowerHomotopyMap, Module.Basis.constr_basis]
    simp [SSet.stdSimplex.const]
  simp only [completedHomotopyLinearMap, h, AdicCompletion.map_id]

/-- At the constant simplex `1` the component of the contracting homotopy is zero. -/
private lemma completedHomotopyLinearMap_one (n : ℕ) :
    completedHomotopyLinearMap s f hf n (SSet.stdSimplex.const 1 1 (op ⦋n⦌)) = 0 := by
  have h : tensorPowerHomotopyMap s f n (SSet.stdSimplex.const 1 1 (op ⦋n⦌)) = 0 := by
    apply (tensorPowerDifferentialsBasis s f n).ext
    intro k
    simp only [tensorPowerHomotopyMap, Module.Basis.constr_basis]
    simp [SSet.stdSimplex.const]
  simp only [completedHomotopyLinearMap, h, AdicCompletion.map_zero]

end Homotopy



/-! ### The homotopy between the identity and zero -/

section CosimplicialHomotopy

variable {s : AffineCrystallineSituation.{u, v}} {ι : Type w}
  {f : MvPolynomial ι s.A →ₐ[s.A] s.C} {hf : Function.Surjective f}

/-- The structure map of `Ω_{D(*)}` along `φ`, read through the identifications of the degrees
with the completed modules of divided power differentials. -/
private noncomputable def completedTransition (E : CosimplicialEnvelope s f hf) {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    completedTensorPowerDifferentials s f m →+ completedTensorPowerDifferentials s f n :=
  (E.differentialsEquiv n).toAddMonoidHom.comp
    ((E.differentials.map φ.op.op).hom.toAddMonoidHom.comp
      (E.differentialsEquiv m).symm.toAddMonoidHom)

/-- The structure maps of `Ω_{D(*)}` are semilinear over those of `D(*)`. -/
private lemma completedTransition_smul (E : CosimplicialEnvelope s f hf) {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (r : pAdicCompletedTensorPowerEnvelope s f hf m)
    (x : completedTensorPowerDifferentials s f m) :
    completedTransition E φ (r • x) =
      E.ringEquiv n (E.ring.map φ ((E.ringEquiv m).symm r)) • completedTransition E φ x := by
  obtain ⟨r, rfl⟩ := (E.ringEquiv m).surjective r
  obtain ⟨x, rfl⟩ := (E.differentialsEquiv m).surjective x
  change E.differentialsEquiv n (E.differentials.map φ.op.op
      ((E.differentialsEquiv m).symm (E.ringEquiv m r • E.differentialsEquiv m x))) =
    E.ringEquiv n (E.ring.map φ ((E.ringEquiv m).symm (E.ringEquiv m r))) •
      E.differentialsEquiv n (E.differentials.map φ.op.op
        ((E.differentialsEquiv m).symm (E.differentialsEquiv m x)))
  rw [← E.differentialsEquiv_smul, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  rw [map_smul]
  exact E.differentialsEquiv_smul n _ _

/-- The structure maps of `Ω_{D(*)}` send the completed basis vector `dx_k` to the completed
basis vector of the reindexed variable. -/
private lemma completedTransition_generator (E : CosimplicialEnvelope s f hf) {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (k : Fin (m + 1) × ι) :
    completedTransition E φ (completedGenerator s f m k) =
      completedGenerator s f n (tensorPowerVariableMap φ k) := by
  rw [← tensorPowerDerivation_variable s f hf]
  change E.differentialsEquiv n (E.differentials.map φ.op.op
    ((E.differentialsEquiv m).symm _)) = _
  rw [← (E.ringEquiv m).apply_symm_apply (tensorPowerEnvelopeMap s f hf m (MvPolynomial.X k))]
  rw [E.differentialsEquiv_naturality, E.ringEquiv_naturality, MvPolynomial.rename_X,
    tensorPowerDerivation_variable]

/-- The components of the contracting homotopy commute with the structure maps of `Ω_{D(*)}`:
both sides are adically continuous, semilinear in the completed scalars, and agree on the
completed basis vectors, where the comparison is the compatibility of the reindexing of the
variables with the simplices of `Δ[1]`. -/
private lemma completedHomotopyLinearMap_naturality (E : CosimplicialEnvelope s f hf) {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (α : (Δ[1] : SSet.{0}).obj (op ⦋n⦌)) (x : completedTensorPowerDifferentials s f m) :
    completedHomotopyLinearMap s f hf n α (completedTransition E φ x) =
      completedTransition E φ
        (completedHomotopyLinearMap s f hf m ((Δ[1] : SSet.{0}).map φ.op α) x) := by
  let Hn := completedHomotopyLinearMap s f hf n α
  let Hm := completedHomotopyLinearMap s f hf m ((Δ[1] : SSet.{0}).map φ.op α)
  have heq : Hn.toAddMonoidHom.comp (completedTransition E φ) =
      (completedTransition E φ).comp Hm.toAddMonoidHom := by
    apply adicCompletion_ext_basis _ _ (tensorPowerDifferentialsBasis s f m)
    · exact SemilinearCosimplicialModule.AdicContinuous.comp _ _ _
        (f := completedTransition E φ) (g := Hn)
        (E.differentialsEquiv_adicContinuous φ) (adicContinuous_adicCompletionMap _ _)
    · exact SemilinearCosimplicialModule.AdicContinuous.comp _ _ _
        (f := Hm) (g := completedTransition E φ)
        (adicContinuous_adicCompletionMap _ _) (E.differentialsEquiv_adicContinuous φ)
    · intro r y hy
      change Hn (completedTransition E φ (r • y)) = completedTransition E φ (Hm (r • y))
      rw [completedTransition_smul, map_smul, map_smul, completedTransition_smul]
      exact congrArg (_ • ·) hy
    · intro k
      change Hn (completedTransition E φ (completedGenerator s f m k)) =
        completedTransition E φ (Hm (completedGenerator s f m k))
      dsimp only [Hn, Hm]
      rw [completedTransition_generator, completedHomotopyLinearMap_generator,
        completedHomotopyLinearMap_generator]
      have hc : (SSet.stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map φ.op α)).toOrderHom k.1 =
          (SSet.stdSimplex.objEquiv α).toOrderHom (tensorPowerVariableMap φ k).1 := rfl
      rw [hc]
      split_ifs <;> simp only [completedTransition_generator, map_zero]
  exact DFunLike.congr_fun heq x

/-- The component in degree `n` of the contracting homotopy of `Ω_{D(*)}`, transported to the
degree of the cosimplicial module. -/
private noncomputable def completedHomotopyComponent (E : CosimplicialEnvelope s f hf) (n : ℕ)
    (α : (Δ[1] : SSet.{0}).obj (op ⦋n⦌)) :
    E.differentials.obj (op (op ⦋n⦌)) →ₗ[E.ring.obj ⦋n⦌]
      E.differentials.obj (op (op ⦋n⦌)) := by
  refine {
    toFun := fun x => (E.differentialsEquiv n).symm
      (completedHomotopyLinearMap s f hf n α (E.differentialsEquiv n x))
    map_add' := by simp
    map_smul' := by
      intro r x
      apply (E.differentialsEquiv n).injective
      rw [E.differentialsEquiv_smul, map_smul, E.differentialsEquiv_smul]
      simp }

/-- **Stacks Project, Tag 07L9.** With the notation of equation (07L0), the complex

`Ω_{D(0)} → Ω_{D(1)} → Ω_{D(2)} → ⋯`

of `p`-adically completed modules of divided power differentials is homotopic to zero as a
`D(*)`-cosimplicial module: the identity endomorphism of the cosimplicial module `Ω_{D(*)}` over
the cosimplicial ring `D(*)` is homotopic to its zero endomorphism. -/
@[stacks 07L9]
public theorem id_cosimplicialEnvelopeDifferentials_homotopic_zero
    (E : CosimplicialEnvelope s f hf) :
    Homotopic (𝟙 E.differentials) 0 := by
  apply Relation.EqvGen.rel
  refine ⟨{ app := fun n α => ModuleCat.ofHom (completedHomotopyComponent E n.len α)
            naturality := ?_, app_zero := ?_, app_one := ?_ }⟩
  · intro m n φ α
    ext x
    apply (E.differentialsEquiv n.len).injective
    change E.differentialsEquiv n.len
        (completedHomotopyComponent E n.len α (E.differentials.map φ.op.op x)) =
      E.differentialsEquiv n.len (E.differentials.map φ.op.op
        (completedHomotopyComponent E m.len ((Δ[1] : SSet.{0}).map φ.op α) x))
    simp only [completedHomotopyComponent, LinearMap.coe_mk, AddHom.coe_mk,
      AddEquiv.apply_symm_apply]
    have h := completedHomotopyLinearMap_naturality E φ α (E.differentialsEquiv m.len x)
    change completedHomotopyLinearMap s f hf n.len α
        (E.differentialsEquiv n.len (E.differentials.map φ.op.op
          ((E.differentialsEquiv m.len).symm (E.differentialsEquiv m.len x)))) = _ at h
    rw [AddEquiv.symm_apply_apply] at h
    exact h
  · intro n
    ext x
    change completedHomotopyComponent E n.len
      (SSet.stdSimplex.const 1 0 (op n)) x = x
    change (E.differentialsEquiv n.len).symm
      (completedHomotopyLinearMap s f hf n.len _ (E.differentialsEquiv n.len x)) = x
    rw [completedHomotopyLinearMap_zero, LinearMap.id_apply, AddEquiv.symm_apply_apply]
  · intro n
    ext x
    change completedHomotopyComponent E n.len
      (SSet.stdSimplex.const 1 1 (op n)) x = 0
    change (E.differentialsEquiv n.len).symm
      (completedHomotopyLinearMap s f hf n.len _ (E.differentialsEquiv n.len x)) = 0
    rw [completedHomotopyLinearMap_one, LinearMap.zero_apply, map_zero]

end CosimplicialHomotopy

end Crystalline

end
