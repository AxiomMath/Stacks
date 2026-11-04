module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.CategoryTheory.Limits.Finite.NonemptyColimits
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Coequalizers in the affine crystalline site

A parallel pair of morphisms in `CRIS(C/A)` has a coequalizer, built from the coequalizer of the
underlying rings followed by the divided power envelope of the image of the divided power ideal;
its image under the quotient functor is a coequalizer of `C`-algebras.

## Main results

* `Crystalline.exists_coequalizer_with_quotient` — a coequalizer in `CRIS(C/A)` whose image
  under the quotient functor is a coequalizer of `C`-algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Crystalline

section Coequalizer

open WalkingParallelPairHom
open DividedPowerThickening

/-- Any parallel pair in `CRIS(C/A)` has a coequalizer, and the quotient of the chosen
coequalizer is a coequalizer of the induced parallel pair of `C`-algebras. -/
public lemma exists_coequalizer_with_quotient
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S} (f g : X ⟶ Y) :
    ∃ (Q : DividedPowerThickening.{u, v, w} S) (q : Y ⟶ Q)
      (hq : f ≫ q = g ≫ q),
      Nonempty (IsColimit (Cofork.ofπ q hq)) ∧
        Nonempty (IsColimit
          ((quotientFunctor S).mapCocone (Cofork.ofπ q hq))) := by
  let fR : CommRingCat.of X.ring ⟶ CommRingCat.of Y.ring := CommRingCat.ofHom f.hom.toRingHom
  let gR : CommRingCat.of X.ring ⟶ CommRingCat.of Y.ring := CommRingCat.ofHom g.hom.toRingHom
  let R : CommRingCat := coequalizer fR gR
  let π : Y.ring →+* R := (coequalizer.π fR gR).hom'
  let J : Ideal R := Ideal.map π Y.ring.ideal
  let hJ : Y.ring.ideal.map π ≤ J := le_rfl
  let E := dividedPowerEnvelope Y.ring π J hJ
  let qe : Y.ring ⧸ Y.ring.ideal →+* E.object ⧸ E.object.ideal :=
    Ideal.quotientMap E.object.ideal E.structureMap.toRingHom
      (Ideal.map_le_iff_le_comap.mp E.structureMap.ideal_comp)
  let Q : DividedPowerThickening S := {
    ring := E.object
    fromBase := E.structureMap.comp Y.fromBase
    prime_nilpotent := by simpa using Y.prime_nilpotent.map E.structureMap.toRingHom
    toQuotient := qe.comp Y.toQuotient
    commutes := by
      apply RingHom.ext
      intro a
      calc
        Ideal.Quotient.mk E.object.ideal
            (E.structureMap.toRingHom (Y.fromBase.toRingHom a)) =
            qe (Ideal.Quotient.mk Y.ring.ideal (Y.fromBase.toRingHom a)) := by
              simp [qe, Ideal.quotientMap_mk]
        _ = qe (Y.toQuotient (algebraMap S.A S.C a)) := by
          congr 1
          exact DFunLike.congr_fun Y.commutes a
  }
  let q : Y ⟶ Q := {
    hom := E.structureMap
    fromBase_comp := rfl
    toQuotient_comp := rfl
  }
  have hq : f ≫ q = g ≫ q := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    have hx := congrArg (fun k : CommRingCat.of X.ring ⟶ CommRingCat.of R => k x)
      (coequalizer.condition fR gR)
    change π (f.hom.toRingHom x) = π (g.hom.toRingHom x) at hx
    show E.structureMap.toRingHom (f.hom.toRingHom x) =
      E.structureMap.toRingHom (g.hom.toRingHom x)
    rw [← E.algebraMap_comp]
    show E.algebraMap.toRingHom (π (f.hom.toRingHom x)) =
      E.algebraMap.toRingHom (π (g.hom.toRingHom x))
    exact congrArg E.algebraMap.toRingHom hx
  have hcoeq : ∀ {T : Type w} [CommRing T] (g₁ g₂ : R →+* T),
      g₁.comp π = g₂.comp π → g₁ = g₂ := fun g₁ g₂ h =>
    congrArg CommRingCat.Hom.hom'
      (coequalizer.hom_ext (CommRingCat.hom_ext h) :
        CommRingCat.ofHom g₁ = CommRingCat.ofHom g₂)
  let envDesc : ∀ (C : DividedPowerRing.{w})
      (a : DividedPowers.DPMorphism Y.ring.dividedPowers C.dividedPowers),
      (∀ x, a.toRingHom (f.hom.toRingHom x) = a.toRingHom (g.hom.toRingHom x)) →
      {m : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers //
        m.comp E.structureMap = a} := fun C a ha => by
    have hring : fR ≫ CommRingCat.ofHom a.toRingHom = gR ≫ CommRingCat.ofHom a.toRingHom :=
      CommRingCat.hom_ext (RingHom.ext ha)
    let dR : R →+* C := (coequalizer.desc (CommRingCat.ofHom a.toRingHom) hring).hom'
    have hdR : dR.comp π = a.toRingHom :=
      congrArg CommRingCat.Hom.hom' (coequalizer.π_desc _ hring)
    let pair : IdealPair.Hom J C.ideal := {
      toRingHom := dR
      ideal_comp := by
        show Ideal.map dR (Ideal.map π Y.ring.ideal) ≤ C.ideal
        rw [Ideal.map_map, hdR]
        exact a.ideal_comp
    }
    exact (E.homEquiv C a).symm ⟨pair, IdealPair.Hom.ext_toRingHom _ _ hdR⟩
  have envExt : ∀ (C : DividedPowerRing.{w})
      (a : DividedPowers.DPMorphism Y.ring.dividedPowers C.dividedPowers)
      (m₁ m₂ : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers),
      m₁.comp E.structureMap = a → m₂.comp E.structureMap = a → m₁ = m₂ := by
    intro C a m₁ m₂ h₁ h₂
    have h : ∀ m : {m : DividedPowers.DPMorphism E.object.dividedPowers C.dividedPowers //
        m.comp E.structureMap = a}, (E.homEquiv C a m).1.toRingHom.comp π = a.toRingHom :=
      fun m => congrArg IdealPair.Hom.toRingHom (E.homEquiv C a m).2
    exact congrArg Subtype.val ((E.homEquiv C a).injective (Subtype.ext
      (IdealPair.Hom.ext_toRingHom _ _
        (hcoeq _ _ ((h ⟨m₁, h₁⟩).trans (h ⟨m₂, h₂⟩).symm)))))
  let envLift (s : Cofork f g) := envDesc s.pt.ring s.π.hom fun x =>
    congrArg (fun z : X ⟶ s.pt => z.hom.toRingHom x) s.condition
  let lift : ∀ s : Cofork f g, Q ⟶ s.pt := fun s => by
    let envHom := envLift s
    let qEnv : E.object ⧸ E.object.ideal →+* s.pt.ring ⧸ s.pt.ring.ideal :=
      Ideal.quotientMap s.pt.ring.ideal envHom.1.toRingHom
        (Ideal.map_le_iff_le_comap.mp envHom.1.ideal_comp)
    let qSrc : Y.ring ⧸ Y.ring.ideal →+* s.pt.ring ⧸ s.pt.ring.ideal :=
      Ideal.quotientMap s.pt.ring.ideal s.π.hom.toRingHom
        (Ideal.map_le_iff_le_comap.mp s.π.hom.ideal_comp)
    have hquot :
        qEnv.comp qe = qSrc := by
      apply RingHom.ext
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hv := congrArg DividedPowers.DPMorphism.toRingHom envHom.2
      change envHom.1.toRingHom.comp E.structureMap.toRingHom = s.π.hom.toRingHom at hv
      have hvy := congrArg (fun m : Y.ring →+* s.pt.ring => m y) hv
      simp only [qEnv, qSrc, qe, Ideal.quotientMap_mk]
      exact congrArg (Ideal.Quotient.mk s.pt.ring.ideal) hvy
    refine {
      hom := envHom.1
      fromBase_comp := ?_
      toQuotient_comp := ?_
    }
    · dsimp [Q]
      apply DividedPowers.DPMorphism.ext
      funext a
      have hv := congrArg DividedPowers.DPMorphism.toRingHom envHom.2
      change envHom.1.toRingHom.comp E.structureMap.toRingHom = s.π.hom.toRingHom at hv
      have hbase := congrArg DividedPowers.DPMorphism.toRingHom s.π.fromBase_comp
      change s.π.hom.toRingHom.comp Y.fromBase.toRingHom = s.pt.fromBase.toRingHom at hbase
      calc
        envHom.1.toRingHom (E.structureMap.toRingHom (Y.fromBase.toRingHom a)) =
            s.π.hom.toRingHom (Y.fromBase.toRingHom a) :=
              congrArg (fun m : Y.ring →+* s.pt.ring => m (Y.fromBase.toRingHom a)) hv
        _ = s.pt.fromBase.toRingHom a := DFunLike.congr_fun hbase a
    · show qEnv.comp
        (qe.comp Y.toQuotient) = s.pt.toQuotient
      rw [← RingHom.comp_assoc, hquot]
      exact s.π.toQuotient_comp
  have lift_fac (s : Cofork f g) : q ≫ lift s = s.π := by
    apply DividedPowerThickening.Hom.ext
    show (lift s).hom.comp q.hom = s.π.hom
    dsimp [q, lift]
    exact (envLift s).2
  let F := quotientFunctor S
  let qF := F.map q
  let algLift : ∀ t : Cofork (F.map f) (F.map g),
      {d : F.obj Q ⟶ t.pt // F.map q ≫ d = t.π ∧
        ∀ m : F.obj Q ⟶ t.pt, F.map q ≫ m = t.π → m = d} := by
    intro t
    let Tdp : DividedPowerRing.{w} := {
      carrier := t.pt
      ideal := ⊥
      dividedPowers := dividedPowersBot t.pt
    }
    let k : Y.ring →+* t.pt := t.π.hom.toRingHom.comp (Ideal.Quotient.mk Y.ring.ideal)
    have hkilled : Y.ring.ideal ≤ RingHom.ker k := by
      intro y hy
      show t.π.hom.toRingHom (Ideal.Quotient.mk Y.ring.ideal y) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact map_zero _
    let a : DividedPowers.DPMorphism Y.ring.dividedPowers (dividedPowersBot t.pt) :=
      dpMorphismToBot Y.ring.dividedPowers k fun y hy => RingHom.mem_ker.mp (hkilled hy)
    let envHom := envDesc Tdp a fun x => by
      have ht := congrArg
        (fun z : F.obj X ⟶ t.pt => z.hom (Ideal.Quotient.mk X.ring.ideal x)) t.condition
      exact ht
    let : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    let : Algebra S.C (Q.ring ⧸ Q.ring.ideal) := Q.toQuotient.toAlgebra
    let dE : F.obj Q →+* t.pt := Ideal.Quotient.lift Q.ring.ideal
      envHom.1.toRingHom fun x hx =>
        Ideal.mem_bot.mp ((Ideal.map_le_iff_le_comap.mp envHom.1.ideal_comp) hx)
    have hmk (y : Y.ring) :
        qF.hom (Ideal.Quotient.mk Y.ring.ideal y : F.obj Y) =
          (Ideal.Quotient.mk Q.ring.ideal (E.structureMap.toRingHom y) : F.obj Q) := by
      show DividedPowerRing.quotientRingHom q.hom
        (Ideal.Quotient.mk Y.ring.ideal y) = _
      rw [DividedPowerRing.quotientRingHom_mk]
      show Ideal.Quotient.mk Q.ring.ideal (E.structureMap.toRingHom y) = _
      rfl
    have hmkSurj : Function.Surjective (fun y : Y.ring =>
        (Ideal.Quotient.mk Y.ring.ideal y : F.obj Y)) := fun z =>
      Ideal.Quotient.mk_surjective z
    have hfacRing : dE.comp qF.hom.toRingHom = t.π.hom.toRingHom := by
      apply RingHom.ext
      intro z
      obtain ⟨y, hy⟩ := hmkSurj z
      rw [← hy]
      show dE (qF.hom (Ideal.Quotient.mk Y.ring.ideal y : F.obj Y)) =
        t.π.hom.toRingHom (Ideal.Quotient.mk Y.ring.ideal y : F.obj Y)
      rw [hmk y]
      simp only [dE]
      show envHom.1.toRingHom (E.structureMap.toRingHom y) =
        t.π.hom.toRingHom (Ideal.Quotient.mk Y.ring.ideal y)
      have hv := congrArg DividedPowers.DPMorphism.toRingHom envHom.2
      change envHom.1.toRingHom.comp E.structureMap.toRingHom = k at hv
      have hvy := DFunLike.congr_fun hv y
      rwa [RingHom.comp_apply] at hvy
    let dAlg : F.obj Q ⟶ t.pt := CommAlgCat.ofHom {
      toRingHom := dE
      commutes' := by
        intro c
        have hc := (qF.hom).commutes c
        calc
          dE (algebraMap S.C (F.obj Q) c) =
              dE (qF.hom (algebraMap S.C (F.obj Y) c)) := congrArg dE hc.symm
          _ = t.π.hom.toRingHom (algebraMap S.C (F.obj Y) c) :=
            DFunLike.congr_fun hfacRing (algebraMap S.C (F.obj Y) c)
          _ = algebraMap S.C t.pt c := t.π.hom.commutes c
    }
    have hfac : F.map q ≫ dAlg = t.π := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      show dE (qF.hom z) = t.π.hom.toRingHom z
      exact DFunLike.congr_fun hfacRing z
    refine ⟨dAlg, hfac, fun m hm => ?_⟩
    let mkE : E.object →+* Q.ring ⧸ Q.ring.ideal := Ideal.Quotient.mk Q.ring.ideal
    let mRing : E.object →+* t.pt := m.hom.toRingHom.comp mkE
    have hmkE : E.object.ideal ≤ RingHom.ker mRing := by
      intro x hx
      show m.hom.toRingHom (Ideal.Quotient.mk E.object.ideal x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact map_zero _
    let mDP : DividedPowers.DPMorphism E.object.dividedPowers (dividedPowersBot t.pt) :=
      dpMorphismToBot E.object.dividedPowers mRing fun x hx => RingHom.mem_ker.mp (hmkE hx)
    have hmRestr : mDP.comp E.structureMap = a := by
      apply DividedPowers.DPMorphism.ext
      funext y
      have hmEval := congrArg
        (fun z : F.obj Y ⟶ t.pt => z.hom (Ideal.Quotient.mk Y.ring.ideal y)) hm
      change m.hom.toRingHom (qF.hom (Ideal.Quotient.mk Y.ring.ideal y : F.obj Y)) =
        t.π.hom.toRingHom (Ideal.Quotient.mk Y.ring.ideal y) at hmEval
      rw [hmk y] at hmEval
      show m.hom.toRingHom (Ideal.Quotient.mk Q.ring.ideal
          (E.structureMap.toRingHom y)) =
        t.π.hom.toRingHom (Ideal.Quotient.mk Y.ring.ideal y)
      exact hmEval
    have hDP : mDP = envHom.1 := envExt Tdp a _ _ hmRestr envHom.2
    have hMaps : m.hom.toRingHom = dE := by
      apply RingHom.ext
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      show m.hom.toRingHom (Ideal.Quotient.mk Q.ring.ideal x) =
        dE (Ideal.Quotient.mk Q.ring.ideal x)
      have hval : mDP.toRingHom x = envHom.1.toRingHom x := congrArg (·.toRingHom x) hDP
      calc
        m.hom.toRingHom (Ideal.Quotient.mk Q.ring.ideal x) = mDP.toRingHom x := rfl
        _ = envHom.1.toRingHom x := hval
        _ = dE (Ideal.Quotient.mk Q.ring.ideal x) := by
          let H : ∀ y ∈ Q.ring.ideal, envHom.1.toRingHom y = 0 := fun y hy =>
            Ideal.mem_bot.mp ((Ideal.map_le_iff_le_comap.mp envHom.1.ideal_comp) hy)
          exact (Ideal.Quotient.lift_mk Q.ring.ideal envHom.1.toRingHom H (a := x)).symm
    exact CommAlgCat.hom_ext (AlgHom.ext fun z => DFunLike.congr_fun hMaps z)
  refine ⟨Q, q, hq, ?_, ?_⟩
  · refine ⟨Cofork.IsColimit.mk (Cofork.ofπ q hq) lift lift_fac fun s m hm => ?_⟩
    · have hmRestr : m.hom.comp E.structureMap = s.π.hom :=
        congrArg (fun z : Y ⟶ s.pt => z.hom) hm
      have hSub : m.hom = (envLift s).1 := envExt _ _ _ _ hmRestr (envLift s).2
      apply DividedPowerThickening.Hom.ext
      dsimp [lift]
      exact hSub
  · let mkCofork (t : Cocone (parallelPair f g ⋙ F)) : Cofork (F.map f) (F.map g) :=
      Cofork.ofπ (t.ι.app WalkingParallelPair.one)
        (by simpa using (t.w left).trans (t.w right).symm)
    refine ⟨IsColimit.mk (fun t => (algLift (mkCofork t)).1) ?_ ?_⟩
    · intro t j
      cases j with
      | zero =>
        let c := Cofork.ofπ q hq
        let d := (algLift (mkCofork t)).1
        have hd := (algLift (mkCofork t)).2.1
        calc
          ((F).mapCocone c).ι.app WalkingParallelPair.zero ≫ d =
              F.map f ≫ (F.map q ≫ d) := by
                rw [Functor.mapCocone_ι_app, Cofork.app_zero_eq_comp_π_left,
                  Cofork.π_ofπ, F.map_comp, Category.assoc]
          _ = F.map f ≫ t.ι.app WalkingParallelPair.one :=
            congrArg (fun z => F.map f ≫ z) hd
          _ = t.ι.app WalkingParallelPair.zero := by
            simpa using t.w left
      | one =>
        simpa [mkCofork, Functor.mapCocone_ι_app, Cofork.app_one_eq_π, Cofork.π_ofπ]
          using (algLift (mkCofork t)).2.1
    · intro t m hm
      have hmOne : F.map q ≫ m = t.ι.app WalkingParallelPair.one := by
        simpa [Functor.mapCocone_ι_app, Cofork.app_one_eq_π, Cofork.π_ofπ] using
          hm WalkingParallelPair.one
      exact (algLift (mkCofork t)).2.2 m hmOne

end Coequalizer

end Crystalline
