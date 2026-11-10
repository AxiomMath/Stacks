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

/-!
# Divided power envelopes of a presentation and the completed affine crystalline site

Fix an affine crystalline situation `(A, I, γ) → C` with residue characteristic `p`, and a
surjective presentation `f : P → C` of `C` by a polynomial `A`-algebra `P`.  Let `D` be the
divided power envelope of `ker f` relative to `(A, I, γ)`.  This file compares `D`, its
reductions `D/(p)^e`, the envelopes of the reduced presentations `P/(p)^e → C`, and the
`p`-adic completion of `D`.

For all large `e` the ideal `(p)^e` of `D` is contained in the divided power ideal of `D` and
is stable under its divided powers, so `D/(p)^e` again carries divided powers; the same holds
in the completion.  At those levels `D/(p)^e` is canonically the divided power envelope of the
reduced presentation, the completion has the same finite quotients as `D`, each finite level
is an object of the little crystalline category `Cris(C/A)`, the completion is an object of
the completed affine crystalline site, and the completion is the inverse limit of the finite
levels.  Finally the finite levels generate: every divided power thickening of `C/A` receives
a morphism from a sufficiently high level.

The file also records the quotient functor on `CRIS(C/A)`, which sends a divided power
thickening `(B, J, δ)` to the `C`-algebra `B/J`.

## Main definitions

* `Crystalline.quotientFunctor` — the functor `CRIS(C/A) ⥤ CommAlgCat C`, `(B, J, δ) ↦ B/J`.
* `Crystalline.presentationEnvelope` — the divided power envelope of `ker f`.
* `Crystalline.levelEnvelope` — the divided power envelope of the presentation reduced
  modulo `(p)^e`.
* `Crystalline.levelCrystallineThickening` — the finite levels as objects of `Cris(C/A)`.
* `Crystalline.completedCrystallineThickening` — the completed envelope as an object of the
  completed affine crystalline site.

## Main results

* `Crystalline.eventually_pAdicIdeal_isSubDPIdeal`,
  `Crystalline.eventually_completed_pAdicIdeal_isSubDPIdeal` — eventual containment and
  divided-power stability of `(p)^e` in the envelope and in its completion.
* `Crystalline.eventually_quotient_envelope_equiv`,
  `Crystalline.eventually_completed_quotient_equiv` — the two comparison isomorphisms of
  finite levels.
* `Crystalline.completedEnvelope_isLimit` — the completed envelope is the inverse limit of
  the finite-level envelopes.
* `Crystalline.exists_forall_le_levelEnvelope_hom` — *every* sufficiently high finite level maps
  to a given divided power thickening, the bound being the larger of the cutoff of
  `Crystalline.levelCrystallineThickening` and the nilpotency exponent of `p` in the target.
* `Crystalline.exists_levelEnvelope_hom` — a sufficiently high finite level maps to any
  divided power thickening.  This is the previous result at the bound itself; the uniform form is
  what lets the level be chosen for an independent reason, as in
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyIdentification.lean`.

## References

* [Stacks Project, Tag 07KF](https://stacks.math.columbia.edu/tag/07KF)
* [Stacks Project, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Crystalline

section QuotientFunctor

open DividedPowerThickening

/-- **Stacks Project, Tag 07KF.** The functor sending a divided power thickening
`(B, J, δ)` in `CRIS(C/A)` to the `C`-algebra `B/J`. -/
@[stacks 07KF]
public def quotientFunctor (S : AffineCrystallineSituation.{u, v}) :
    DividedPowerThickening.{u, v, w} S ⥤ CommAlgCat.{w, v} S.C where
  obj X := by
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    exact CommAlgCat.of S.C (X.ring ⧸ X.ring.ideal)
  map {X Y} f := by
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    exact CommAlgCat.ofHom
      { toRingHom := DividedPowerRing.quotientRingHom f.hom
        commutes' := DFunLike.congr_fun f.toQuotient_comp }
  map_id X := by
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    ext x
    change DividedPowerRing.quotientRingHom (𝟙 X.ring) x = x
    simp [DividedPowerRing.quotientRingHom_id]
  map_comp {X Y Z} f g := by
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    let _ : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
    ext x
    change DividedPowerRing.quotientRingHom (f.hom ≫ g.hom) x =
      DividedPowerRing.quotientRingHom g.hom (DividedPowerRing.quotientRingHom f.hom x)
    simp [DividedPowerRing.quotientRingHom_comp]

end QuotientFunctor

section FiniteLevelEnvelope

variable (s : AffineCrystallineSituation.{u, v})
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

/-- The underlying ring homomorphism of a composite of morphisms of ring--ideal pairs. -/
public theorem idealPairHom_comp_toRingHom
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (g : IdealPair.Hom J K) (f : IdealPair.Hom I J) :
    (IdealPair.Hom.comp g f).toRingHom = g.toRingHom.comp f.toRingHom := rfl

/-- The underlying ring homomorphism of `IdealPair.Hom.ofRingHom f hf` is `f`. -/
public theorem idealPairHom_ofRingHom_toRingHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f : R →+* S) (hf : I.map f ≤ J) :
    (IdealPair.Hom.ofRingHom f hf).toRingHom = f := rfl

/-- Forgetting divided powers does not change the underlying ring homomorphism. -/
public theorem idealPairHom_ofDPMorphism_toRingHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} {hI : DividedPowers I} {hJ : DividedPowers J}
    (f : DividedPowers.DPMorphism hI hJ) :
  (IdealPair.Hom.ofDPMorphism f).toRingHom = f.toRingHom := rfl

/-- A ring homomorphism killing `I` is a divided power morphism from any divided powers on `I`
to the trivial divided powers on the zero ideal of the target. -/
private theorem isDPMorphism_dividedPowersBot_of_forall_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {I : Ideal A} (δ : DividedPowers I) (g : A →+* B) (hg : ∀ x ∈ I, g x = 0) :
    DividedPowers.IsDPMorphism δ (_root_.dividedPowersBot B) g := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => by simpa using hg x hx, fun {n} x hx => ?_⟩
  by_cases hn : n = 0
  · subst n
    rw [δ.dpow_zero hx, map_one]
    simp [_root_.dividedPowersBot, hg x hx]
  · simp [_root_.dividedPowersBot, hn, hg _ hx, hg _ (δ.dpow_mem hn hx)]

/-- A ring homomorphism carrying `I` into `J` is a divided power morphism from any divided
powers on `I` to the trivial divided powers on the zero ideal of `B ⧸ J`. -/
public theorem dpMap_to_quotientBot
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (I : Ideal A) (δ : DividedPowers I) (f : A →+* B) (J : Ideal B)
    (hIJ : I.map f ≤ J) :
    DividedPowers.IsDPMorphism δ
      (_root_.dividedPowersBot (B ⧸ J))
      ((Ideal.Quotient.mk J).comp f) :=
  isDPMorphism_dividedPowersBot_of_forall_eq_zero δ _ fun _ hx =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ (Ideal.mem_map_of_mem f hx))

/-- A ring homomorphism killing `I` is a divided power morphism from any divided powers on `I`
to the trivial divided powers on the zero ideal of the target. -/
public theorem dpMap_to_bot
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (I : Ideal A) (δ : DividedPowers I) (f : A →+* B)
    (hI : I.map f ≤ ⊥) :
    DividedPowers.IsDPMorphism δ (_root_.dividedPowersBot B) f :=
  isDPMorphism_dividedPowersBot_of_forall_eq_zero δ f fun _ hx =>
    Ideal.mem_bot.mp (hI (Ideal.mem_map_of_mem f hx))

/-- The quotient of a divided power envelope of `J ⊆ B` by its divided power ideal is
canonically `B ⧸ J`, compatibly with the canonical map from `B`. -/
public noncomputable def envelopeQuotientEquiv
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    (b : A →+* B) (J : Ideal B) (hJ : A.ideal.map b ≤ J)
    (env : DividedPowerEnvelope A b J hJ) :
    {φ : env.object ⧸ env.object.ideal ≃+* B ⧸ J //
      ∀ x : B, φ (Ideal.Quotient.mk env.object.ideal
        (env.algebraMap.toRingHom x)) = Ideal.Quotient.mk J x} := by
  classical
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  let Q : DividedPowerRing.{u} :=
    ⟨B ⧸ J, ⊥, _root_.dividedPowersBot (B ⧸ J)⟩
  let a : DividedPowers.DPMorphism A.dividedPowers Q.dividedPowers :=
    DividedPowers.DPMorphism.mk'
      (dpMap_to_quotientBot A.ideal A.dividedPowers b J hJ)
  have hJbot : J.map qB ≤ Q.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change qB x ∈ (⊥ : Ideal (B ⧸ J))
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let pair : IdealPair.Hom J Q.ideal := IdealPair.Hom.ofRingHom qB hJbot
  have hOver : IdealPair.Hom.comp pair (IdealPair.Hom.ofRingHom b hJ) =
      IdealPair.Hom.ofDPMorphism a := by
    refine IdealPair.Hom.ext_toRingHom _ _ ?_
    rw [idealPairHom_comp_toRingHom, idealPairHom_ofRingHom_toRingHom,
      idealPairHom_ofDPMorphism_toRingHom]
    rfl
  let gData := (env.homEquiv Q a).symm ⟨pair, hOver⟩
  let g := gData.1
  have hgAlg : g.toRingHom.comp env.algebraMap.toRingHom = qB := by
    have hpair : pair =
        IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism g) env.algebraMap :=
      (congrArg Subtype.val ((env.homEquiv Q a).apply_symm_apply ⟨pair, hOver⟩)).symm.trans
        (env.homEquiv_apply Q a gData)
    have hring := congrArg IdealPair.Hom.toRingHom hpair.symm
    rw [show pair.toRingHom = qB from rfl] at hring
    simpa [IdealPair.Hom.comp, IdealPair.Hom.ofDPMorphism] using hring
  let qE : env.object →+* env.object ⧸ env.object.ideal :=
    Ideal.Quotient.mk env.object.ideal
  let U : DividedPowerRing.{u} :=
    ⟨env.object ⧸ env.object.ideal, ⊥,
      _root_.dividedPowersBot (env.object ⧸ env.object.ideal)⟩
  have hEbot : env.object.ideal.map qE ≤ ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change qE x ∈ (⊥ : Ideal (env.object ⧸ env.object.ideal))
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let qEDP : DividedPowers.DPMorphism env.object.dividedPowers U.dividedPowers :=
    DividedPowers.DPMorphism.mk'
      (dpMap_to_bot env.object.ideal env.object.dividedPowers qE hEbot)
  have hJkill : J ≤ RingHom.ker (qE.comp env.algebraMap.toRingHom) := by
    intro x hx
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk env.object.ideal
      (env.algebraMap.toRingHom x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (env.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hx))
  let ψ : B ⧸ J →+* env.object ⧸ env.object.ideal :=
    Ideal.Quotient.lift J (qE.comp env.algebraMap.toRingHom) hJkill
  have hψqB : ψ.comp qB = qE.comp env.algebraMap.toRingHom :=
    Ideal.Quotient.lift_comp_mk J _ _
  let ψDP : DividedPowers.DPMorphism Q.dividedPowers U.dividedPowers :=
    DividedPowers.DPMorphism.mk'
      (dpMap_to_bot Q.ideal Q.dividedPowers ψ (by simp [Q]))
  have hψbase : ψ.comp a.toRingHom = qE.comp env.structureMap.toRingHom := by
    calc
      ψ.comp a.toRingHom = ψ.comp (qB.comp b) := rfl
      _ = (ψ.comp qB).comp b := by ext x; rfl
      _ = (qE.comp env.algebraMap.toRingHom).comp b := by rw [hψqB]
      _ = qE.comp env.structureMap.toRingHom := by
        rw [RingHom.comp_assoc, env.algebraMap_comp]
  let H := env.homEquiv U (qEDP.comp env.structureMap)
  have hrestr : (ψDP.comp g).toRingHom.comp env.algebraMap.toRingHom =
      qEDP.toRingHom.comp env.algebraMap.toRingHom := by
    calc
      (ψDP.comp g).toRingHom.comp env.algebraMap.toRingHom =
          ψ.comp (g.toRingHom.comp env.algebraMap.toRingHom) := by
            ext x
            rfl
      _ = ψ.comp qB := by rw [hgAlg]
      _ = qE.comp env.algebraMap.toRingHom := hψqB
      _ = qEDP.toRingHom.comp env.algebraMap.toRingHom := rfl
  have hψgBase : (ψDP.comp g).comp env.structureMap = qEDP.comp env.structureMap := by
    apply DividedPowers.DPMorphism.ext
    funext x
    have hg := (RingHom.ext_iff.mp
      (congrArg DividedPowers.DPMorphism.toRingHom gData.2)) x
    change ψ (g.toRingHom (env.structureMap.toRingHom x)) =
      qE (env.structureMap.toRingHom x)
    change g.toRingHom (env.structureMap.toRingHom x) = a.toRingHom x at hg
    rw [hg]
    exact (RingHom.ext_iff.mp hψbase) x
  have hdata : H ⟨ψDP.comp g, hψgBase⟩ = H ⟨qEDP, rfl⟩ := by
    apply Subtype.ext
    rw [env.homEquiv_apply U (qEDP.comp env.structureMap) ⟨ψDP.comp g, hψgBase⟩,
      env.homEquiv_apply U (qEDP.comp env.structureMap) ⟨qEDP, rfl⟩]
    exact IdealPair.Hom.ext_toRingHom _ _ hrestr
  have hψg : ψDP.comp g = qEDP := congrArg Subtype.val (H.injective hdata)
  have hψgRing : ψ.comp g.toRingHom = qE :=
    congrArg DividedPowers.DPMorphism.toRingHom hψg
  let φ : env.object ⧸ env.object.ideal →+* B ⧸ J :=
    Ideal.Quotient.lift env.object.ideal g.toRingHom fun x hx =>
      Ideal.mem_bot.mp (by simpa [Q] using g.ideal_comp (Ideal.mem_map_of_mem g.toRingHom hx))
  have hφqE : φ.comp qE = g.toRingHom :=
    Ideal.Quotient.lift_comp_mk env.object.ideal _ _
  have hφψ : φ.comp ψ = RingHom.id (B ⧸ J) := by
    ext y
    change φ (ψ (qB y)) = qB y
    calc
      φ (ψ (qB y)) = φ (qE (env.algebraMap.toRingHom y)) :=
        congrArg φ ((RingHom.ext_iff.mp hψqB) y)
      _ = g.toRingHom (env.algebraMap.toRingHom y) :=
        (RingHom.ext_iff.mp hφqE) (env.algebraMap.toRingHom y)
      _ = qB y := (RingHom.ext_iff.mp hgAlg) y
  have hψφ : ψ.comp φ = RingHom.id (env.object ⧸ env.object.ideal) := by
    ext y
    change ψ (φ (qE y)) = qE y
    calc
      ψ (φ (qE y)) = ψ (g.toRingHom y) :=
        congrArg ψ ((RingHom.ext_iff.mp hφqE) y)
      _ = qE y := (RingHom.ext_iff.mp hψgRing) y
  have hbij : Function.Bijective φ :=
    ⟨Function.LeftInverse.injective (g := ⇑ψ) (RingHom.ext_iff.mp hψφ),
      Function.RightInverse.surjective (g := ⇑ψ) (RingHom.ext_iff.mp hφψ)⟩
  let φEquiv := RingEquiv.ofBijective φ hbij
  refine ⟨φEquiv, fun x => ?_⟩
  change φ (qE (env.algebraMap.toRingHom x)) = qB x
  exact ((RingHom.ext_iff.mp hφqE) _).trans ((RingHom.ext_iff.mp hgAlg) x)

/-- The kernel of the chosen surjective algebra presentation. -/
public abbrev presentationKernel : Ideal P := RingHom.ker f.toRingHom

/-- The divided power envelope of the kernel of a surjective presentation. -/
public noncomputable def presentationEnvelope :
    DividedPowerEnvelope s.A (algebraMap s.A P) (presentationKernel s f)
      (by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change f (algebraMap s.A P x) = 0
        rw [f.commutes]
        have hx' : algebraMap s.A s.C x ∈
            s.A.ideal.map (algebraMap s.A s.C) :=
          Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
        rw [s.ideal_map_eq_bot] at hx'
        exact hx') :=
  dividedPowerEnvelope s.A (algebraMap s.A P) (presentationKernel s f) _

/-- The quotient of the presentation by the `e`-th power of `(p)`. -/
public abbrev levelRing (e : ℕ) : Type u :=
  P ⧸ (DividedPowers.pAdicIdeal (A := P) s.p ^ e)

/-- The image of the presentation kernel at level `e`. -/
public abbrev levelKernel (e : ℕ) : Ideal (levelRing s (P := P) e) :=
  (presentationKernel s f).map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e))

/-- The divided power envelope of the reduced presentation. -/
public noncomputable def levelEnvelope (e : ℕ) :
    DividedPowerEnvelope s.A
      ((Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e)).comp
        (algebraMap s.A P))
      (levelKernel s f e)
      (by
        rw [← Ideal.map_map]
        exact Ideal.map_mono
          (show s.A.ideal.map (algebraMap s.A P) ≤ presentationKernel s f from
            by
              rw [Ideal.map_le_iff_le_comap]
              intro x hx
              change f (algebraMap s.A P x) = 0
              rw [f.commutes]
              have hx' : algebraMap s.A s.C x ∈
                  s.A.ideal.map (algebraMap s.A s.C) :=
                Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
              rw [s.ideal_map_eq_bot] at hx'
              exact hx')) :=
  dividedPowerEnvelope s.A _ (levelKernel s f e) _

/-- In the envelope of the kernel of a surjective presentation, the image of the prime is
nilpotent modulo the divided power ideal. -/
public theorem presentationEnvelope_prime_nilpotent
    (_hf : Function.Surjective f) :
    IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s f).object.ideal
      (s.p : (presentationEnvelope s f).object)) := by
  let D := (presentationEnvelope s f).object
  obtain ⟨n, hn⟩ := s.prime_nilpotent
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk D.ideal ((s.p : D) ^ n) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hkernel : ((s.p : P) ^ n) ∈ presentationKernel s f := by
    change f ((s.p : P) ^ n) = 0
    rw [map_pow, map_natCast, hn]
  have hmap : (presentationEnvelope s f).algebraMap.toRingHom
      ((s.p : P) ^ n) ∈ D.ideal :=
    (presentationEnvelope s f).algebraMap.ideal_comp
      (Ideal.mem_map_of_mem _ hkernel)
  simpa [D, map_pow] using hmap

/-- Nilpotence of the prime modulo an ideal passes to the `p`-adic completion. -/
public theorem completionIdeal_prime_nilpotent
    {A : Type u} [CommRing A] (I : Ideal A) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) :
    IsNilpotent (Ideal.Quotient.mk (DividedPowers.completionIdeal I p hp)
      (p : AdicCompletion (DividedPowers.pAdicIdeal (A := A) p) A)) := by
  obtain ⟨n, hn⟩ := hp
  let hp' : IsNilpotent (Ideal.Quotient.mk I (p : A)) := ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk (DividedPowers.completionIdeal I p hp')
    ((p : AdicCompletion (DividedPowers.pAdicIdeal (A := A) p) A) ^ n) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change _ ∈ RingHom.ker (DividedPowers.completionToQuotient I p hp')
  have hmap : DividedPowers.completionToQuotient I p hp'
      (p : AdicCompletion (DividedPowers.pAdicIdeal (A := A) p) A) =
      Ideal.Quotient.mk I (p : A) := by
    simp [DividedPowers.completionToQuotient]
  rw [RingHom.mem_ker, map_pow, hmap, hn]

/-- Eventually the powers of `(p)` lie in the envelope ideal and are preserved
by its divided powers. This is the uncompleted assertion of part (1). -/
@[stacks 07KG "part (1), envelope"]
public theorem eventually_pAdicIdeal_isSubDPIdeal
    (hf : Function.Surjective f) :
    let D := (presentationEnvelope s f).object
    ∃ N : ℕ, ∀ e, N ≤ e →
      (DividedPowers.pAdicIdeal (A := D) s.p ^ e ≤ D.ideal) ∧
        D.dividedPowers.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := D) s.p ^ e) := by
  dsimp
  let D := (presentationEnvelope s f).object
  let _ : Algebra (DividedPowers.IntegersAtPrime s.p) D :=
    (((presentationEnvelope s f).structureMap.toRingHom).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  obtain ⟨N, hlevel, _⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u}
      D.ideal D.dividedPowers s.p (presentationEnvelope_prime_nilpotent s f hf)
  exact ⟨N, hlevel⟩

/-- The corresponding eventual stability in the completed envelope. -/
@[stacks 07KG "part (1), completion"]
public theorem eventually_completed_pAdicIdeal_isSubDPIdeal
    (hf : Function.Surjective f) :
    let D := (presentationEnvelope s f).object
    ∃ hp : IsNilpotent (Ideal.Quotient.mk D.ideal (s.p : D)),
      ∃ N : ℕ, ∀ e, N ≤ e →
        let I := DividedPowers.completionIdeal D.ideal s.p hp
        let γ := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hp).1
        (DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D)
          s.p ^ e ≤ I) ∧
          γ.IsSubDPIdeal
            (DividedPowers.pAdicIdeal
              (A := AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D)
              s.p ^ e) := by
  dsimp
  let D := (presentationEnvelope s f).object
  let _ : Algebra (DividedPowers.IntegersAtPrime s.p) D :=
    (((presentationEnvelope s f).structureMap.toRingHom).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  have hnil := presentationEnvelope_prime_nilpotent s f hf
  let Dhat := AdicCompletion (DividedPowers.pAdicIdeal (A := D) s.p) D
  let Ihat := DividedPowers.completionIdeal D.ideal s.p hnil
  let γhat := (DividedPowers.completedDividedPowers D.ideal D.dividedPowers s.p hnil).1
  have hpHat := completionIdeal_prime_nilpotent D.ideal s.p hnil
  let _ : Algebra (DividedPowers.IntegersAtPrime s.p) Dhat :=
    (((algebraMap D Dhat).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) D)).toAlgebra)
  obtain ⟨N, hlevel, _⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u}
      Ihat γhat s.p hpHat
  exact ⟨hnil, N, hlevel⟩

/-- At a level `e` where `(p)^e` is contained in the divided power ideal of the envelope and is
stable under its divided powers, the reduction of the envelope modulo `(p)^e` is canonically
the divided power envelope of the presentation reduced modulo `(p)^e`, in both directions as a
morphism of divided power rings. -/
public noncomputable def quotientEnvelopeEquiv (e : ℕ)
    (hcontained : DividedPowers.pAdicIdeal (A := (presentationEnvelope s f).object) s.p ^ e ≤
      (presentationEnvelope s f).object.ideal)
    (hstable : (presentationEnvelope s f).object.dividedPowers.IsSubDPIdeal
      (DividedPowers.pAdicIdeal (A := (presentationEnvelope s f).object) s.p ^ e)) :
    let D := (presentationEnvelope s f).object
    let E := (levelEnvelope s f e).object
    { φ : (D ⧸ DividedPowers.pAdicIdeal (A := D) s.p ^ e) ≃+* E //
      (∀ x : P, φ (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := D) s.p ^ e)
        ((presentationEnvelope s f).algebraMap.toRingHom x)) =
          (levelEnvelope s f e).algebraMap.toRingHom
            (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e) x)) ∧
      (DividedPowers.quotientDividedPowers D.ideal D.dividedPowers s.p e hcontained
          hstable).IsDPMorphism
        E.dividedPowers φ.toRingHom ∧
      E.dividedPowers.IsDPMorphism
        (DividedPowers.quotientDividedPowers D.ideal D.dividedPowers s.p e hcontained hstable)
        φ.symm.toRingHom } := by
  classical
  dsimp
  let env := presentationEnvelope s f
  let D := env.object
  let E := (levelEnvelope s f e).object
  let pD := DividedPowers.pAdicIdeal (A := D) s.p ^ e
  let pP := DividedPowers.pAdicIdeal (A := P) s.p ^ e
  let qP : P →+* levelRing s (P := P) e := Ideal.Quotient.mk pP
  let qD : D →+* D ⧸ pD := Ideal.Quotient.mk pD
  have hstableInf : D.dividedPowers.IsSubDPIdeal (pD ⊓ D.ideal) := by
    rw [inf_eq_left.mpr hcontained]
    exact hstable
  let Q : DividedPowerRing :=
    ⟨D ⧸ pD, D.ideal.map qD,
      DividedPowers.Quotient.dividedPowers D.dividedPowers hstableInf⟩
  have hqD : D.dividedPowers.IsDPMorphism Q.dividedPowers qD := by
    simpa [Q, qD, DividedPowers.quotientDividedPowers, pD,
      inf_eq_left.mpr hcontained] using
      (DividedPowers.Quotient.isDPMorphism D.dividedPowers hstableInf)
  let qDdp : DividedPowers.DPMorphism D.dividedPowers Q.dividedPowers :=
    DividedPowers.DPMorphism.mk' hqD
  have hqDideal : Q.ideal = D.ideal.map qD := rfl
  let lvl := levelEnvelope s f e
  let envToE : P →+* E := lvl.algebraMap.toRingHom.comp qP
  have hEnvPairIdeal : (presentationKernel s f).map envToE ≤ E.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change x ∈ presentationKernel s f at hx
    change lvl.algebraMap.toRingHom (qP x) ∈ E.ideal
    have hx' : qP x ∈ levelKernel s f e := Ideal.mem_map_of_mem qP hx
    exact lvl.algebraMap.ideal_comp (Ideal.mem_map_of_mem lvl.algebraMap.toRingHom hx')
  let hEnvPair : IdealPair.Hom (presentationKernel s f) E.ideal :=
    IdealPair.Hom.ofRingHom envToE hEnvPairIdeal
  have hBaseIdeal : s.A.ideal.map (algebraMap s.A P) ≤ presentationKernel s f := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change f (algebraMap s.A P x) = 0
    rw [f.commutes, ← Ideal.mem_bot, ← s.ideal_map_eq_bot]
    exact Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
  have hEnvOver : IdealPair.Hom.comp hEnvPair
      (IdealPair.Hom.ofRingHom (algebraMap s.A P) hBaseIdeal) =
        IdealPair.Hom.ofDPMorphism lvl.structureMap := by
    refine IdealPair.Hom.ext_toRingHom _ _ ?_
    rw [idealPairHom_comp_toRingHom, idealPairHom_ofRingHom_toRingHom,
      idealPairHom_ofDPMorphism_toRingHom]
    change hEnvPair.toRingHom.comp (algebraMap s.A P) = lvl.structureMap.toRingHom
    have hpair : hEnvPair.toRingHom = envToE := by
      simp [hEnvPair, IdealPair.Hom.ofRingHom]
    rw [hpair, RingHom.comp_assoc, lvl.algebraMap_comp]
  let gData := (env.homEquiv E lvl.structureMap).symm
    ⟨hEnvPair, hEnvOver⟩
  let g := gData.1
  have hgBase : g.comp env.structureMap = lvl.structureMap := gData.2
  have hgAlg : g.toRingHom.comp env.algebraMap.toRingHom = envToE := by
    have hpair : hEnvPair =
        IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism g) env.algebraMap :=
      (congrArg Subtype.val
        ((env.homEquiv E lvl.structureMap).apply_symm_apply ⟨hEnvPair, hEnvOver⟩)).symm.trans
        (env.homEquiv_apply E lvl.structureMap gData)
    have hring := congrArg IdealPair.Hom.toRingHom hpair.symm
    have hpairRing : hEnvPair.toRingHom = envToE := by
      simp [hEnvPair, IdealPair.Hom.ofRingHom]
    rw [hpairRing] at hring
    simpa [IdealPair.Hom.comp, IdealPair.Hom.ofDPMorphism] using hring
  have hpPzero : qP (s.p : P) ^ e = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    change (s.p : P) ^ e ∈ pP
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) e
  have hpDzero : qD (s.p : D) ^ e = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    change (s.p : D) ^ e ∈ pD
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) e
  have hgKill : pD ≤ RingHom.ker g.toRingHom := by
    change Ideal.span {(s.p : D)} ^ e ≤ RingHom.ker g.toRingHom
    rw [Ideal.span_singleton_pow, Ideal.span_le,
      Set.singleton_subset_iff]
    apply RingHom.mem_ker.mpr
    rw [map_pow]
    have hgp : g.toRingHom (s.p : D) = lvl.algebraMap.toRingHom (qP (s.p : P)) := by
      simp
    rw [hgp, ← map_pow, hpPzero]
    simp
  let φRing : D ⧸ pD →+* E := Ideal.Quotient.lift pD g.toRingHom
    (fun x hx => RingHom.mem_ker.mp (hgKill hx))
  have hφRing : φRing.comp qD = g.toRingHom := Ideal.Quotient.lift_comp_mk pD _ _
  have hφDP : Q.dividedPowers.IsDPMorphism E.dividedPowers φRing :=
    DividedPowers.IsDPMorphism.of_comp D.dividedPowers Q.dividedPowers E.dividedPowers
      qD φRing hqDideal hqD (by
        rw [hφRing]
        exact g.isDPMorphism)
  let φ : DividedPowers.DPMorphism Q.dividedPowers E.dividedPowers :=
    DividedPowers.DPMorphism.mk' hφDP
  let envToQ : P →+* Q := qD.comp env.algebraMap.toRingHom
  have hKillPresentation : pP ≤ RingHom.ker envToQ := by
    change Ideal.span {(s.p : P)} ^ e ≤ RingHom.ker envToQ
    rw [Ideal.span_singleton_pow, Ideal.span_le,
      Set.singleton_subset_iff]
    apply RingHom.mem_ker.mpr
    rw [map_pow, RingHom.comp_apply]
    simpa [RingHom.comp_apply] using hpDzero
  let envToQbar : levelRing s (P := P) e →+* Q :=
    Ideal.Quotient.lift pP envToQ (fun x hx => RingHom.mem_ker.mp (hKillPresentation hx))
  have hEnvToQbar : envToQbar.comp qP = envToQ :=
    Ideal.Quotient.lift_comp_mk pP _ _
  have hLevelPairIdeal :
      (levelKernel s f e).map envToQbar ≤ Q.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective qP Ideal.Quotient.mk_surjective).mp hx
    change envToQbar (qP y) ∈ Q.ideal
    have hEval : envToQbar (qP y) = envToQ y :=
      RingHom.ext_iff.mp hEnvToQbar y
    rw [hEval]
    exact qDdp.ideal_comp
      (Ideal.mem_map_of_mem qD (env.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hy)))
  let hLevelPair : IdealPair.Hom (levelKernel s f e) Q.ideal :=
    IdealPair.Hom.ofRingHom envToQbar hLevelPairIdeal
  let aQ : DividedPowers.DPMorphism s.A.dividedPowers Q.dividedPowers :=
    qDdp.comp env.structureMap
  have hBaseIdealLevel : s.A.ideal.map ((Ideal.Quotient.mk pP).comp
      (algebraMap s.A P)) ≤ levelKernel s f e := by
    rw [← Ideal.map_map]
    exact Ideal.map_mono hBaseIdeal
  have hLevelOver : IdealPair.Hom.comp hLevelPair
      (IdealPair.Hom.ofRingHom
        ((Ideal.Quotient.mk pP).comp (algebraMap s.A P))
        hBaseIdealLevel) = IdealPair.Hom.ofDPMorphism aQ := by
    refine IdealPair.Hom.ext_toRingHom _ _ ?_
    rw [idealPairHom_comp_toRingHom, idealPairHom_ofRingHom_toRingHom,
      idealPairHom_ofDPMorphism_toRingHom]
    refine RingHom.ext fun a => ?_
    change envToQbar (qP (algebraMap s.A P a)) = qD (env.structureMap.toRingHom a)
    calc
      _ = envToQ (algebraMap s.A P a) :=
        (RingHom.ext_iff.mp hEnvToQbar) (algebraMap s.A P a)
      _ = qD (env.structureMap.toRingHom a) :=
        congrArg qD ((RingHom.ext_iff.mp env.algebraMap_comp) a)
  let ψData := (lvl.homEquiv Q aQ).symm ⟨hLevelPair, hLevelOver⟩
  let ψ := ψData.1
  have hψBase : ψ.comp lvl.structureMap = aQ := ψData.2
  have hψAlg : ψ.toRingHom.comp lvl.algebraMap.toRingHom = envToQbar := by
    have hpair : hLevelPair =
        IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism ψ) lvl.algebraMap :=
      (congrArg Subtype.val
        ((lvl.homEquiv Q aQ).apply_symm_apply ⟨hLevelPair, hLevelOver⟩)).symm.trans
        (lvl.homEquiv_apply Q aQ ψData)
    exact congrArg IdealPair.Hom.toRingHom hpair.symm
  have hg' (a : s.A) :
      g.toRingHom (env.structureMap.toRingHom a) = lvl.structureMap.toRingHom a := by
    simpa using (RingHom.ext_iff.mp (congrArg DividedPowers.DPMorphism.toRingHom hgBase)) a
  have hψ' (a : s.A) : ψ.toRingHom (lvl.structureMap.toRingHom a) =
      qDdp.toRingHom (env.structureMap.toRingHom a) := by
    simpa [aQ] using (RingHom.ext_iff.mp (congrArg DividedPowers.DPMorphism.toRingHom hψBase)) a
  have hbaseComp : (ψ.comp g).comp env.structureMap = qDdp.comp env.structureMap := by
    apply DividedPowers.DPMorphism.ext
    funext a
    change ψ.toRingHom (g.toRingHom (env.structureMap.toRingHom a)) =
      qDdp.toRingHom (env.structureMap.toRingHom a)
    rw [hg', hψ']
  have halgebraComp :
      (ψ.comp g).toRingHom.comp env.algebraMap.toRingHom =
        qDdp.toRingHom.comp env.algebraMap.toRingHom := by
    calc
      _ = ψ.toRingHom.comp (g.toRingHom.comp env.algebraMap.toRingHom) := by
        ext x
        rfl
      _ = ψ.toRingHom.comp envToE := by rw [hgAlg]
      _ = (ψ.toRingHom.comp lvl.algebraMap.toRingHom).comp qP := by
        ext x
        rfl
      _ = envToQbar.comp qP := by rw [hψAlg]
      _ = envToQ := by rw [hEnvToQbar]
      _ = qDdp.toRingHom.comp env.algebraMap.toRingHom := rfl
  have hψg : ψ.comp g = qDdp := by
    let H := env.homEquiv Q aQ
    have hdata : H ⟨ψ.comp g, hbaseComp⟩ = H ⟨qDdp, rfl⟩ := by
      apply Subtype.ext
      rw [env.homEquiv_apply Q aQ ⟨ψ.comp g, hbaseComp⟩, env.homEquiv_apply Q aQ ⟨qDdp, rfl⟩]
      exact IdealPair.Hom.ext_toRingHom _ _ halgebraComp
    exact congrArg Subtype.val (H.injective hdata)
  have hψφ : ψ.toRingHom.comp φRing = RingHom.id Q := by
    ext x
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (I := pD) x
    calc
      ψ.toRingHom (φRing x) = ψ.toRingHom (φRing (qD d)) := by rw [hd]
      _ = ψ.toRingHom (g.toRingHom d) := by
        simpa [RingHom.comp_apply] using congrArg ψ.toRingHom ((RingHom.ext_iff.mp hφRing) d)
      _ = qD d := (RingHom.ext_iff.mp
        (congrArg DividedPowers.DPMorphism.toRingHom hψg)) d
      _ = x := hd
  have hφψBase : (φ.comp ψ).comp lvl.structureMap = lvl.structureMap := by
    apply DividedPowers.DPMorphism.ext
    funext a
    change φRing (ψ.toRingHom (lvl.structureMap.toRingHom a)) = lvl.structureMap.toRingHom a
    rw [hψ']
    exact ((RingHom.ext_iff.mp hφRing) (env.structureMap.toRingHom a)).trans (hg' a)
  have hφψAlg : (φ.comp ψ).toRingHom.comp lvl.algebraMap.toRingHom =
      lvl.algebraMap.toRingHom := by
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := pP) x
    calc
      φRing (ψ.toRingHom (lvl.algebraMap.toRingHom (qP y))) =
          φRing (envToQbar (qP y)) :=
        congrArg φRing ((RingHom.ext_iff.mp hψAlg) (qP y))
      _ = φRing (envToQ y) := congrArg φRing ((RingHom.ext_iff.mp hEnvToQbar) y)
      _ = φRing (qD (env.algebraMap.toRingHom y)) := rfl
      _ = g.toRingHom (env.algebraMap.toRingHom y) :=
        (RingHom.ext_iff.mp hφRing) (env.algebraMap.toRingHom y)
      _ = lvl.algebraMap.toRingHom (qP y) := by simpa [envToE] using (RingHom.ext_iff.mp hgAlg) y
  have hφψ : φ.comp ψ = DividedPowers.DPMorphism.id E.dividedPowers := by
    let H := lvl.homEquiv E lvl.structureMap
    have hdata : H ⟨φ.comp ψ, hφψBase⟩ =
        H ⟨DividedPowers.DPMorphism.id E.dividedPowers, by rfl⟩ := by
      apply Subtype.ext
      rw [lvl.homEquiv_apply E lvl.structureMap ⟨φ.comp ψ, hφψBase⟩,
        lvl.homEquiv_apply E lvl.structureMap
          ⟨DividedPowers.DPMorphism.id E.dividedPowers, by rfl⟩]
      exact IdealPair.Hom.ext_toRingHom _ _ hφψAlg
    exact congrArg Subtype.val (H.injective hdata)
  have hbij : Function.Bijective φRing :=
    ⟨Function.LeftInverse.injective (g := ⇑ψ.toRingHom) (RingHom.ext_iff.mp hψφ),
      Function.RightInverse.surjective (g := ⇑ψ.toRingHom)
        (RingHom.ext_iff.mp (congrArg DividedPowers.DPMorphism.toRingHom hφψ))⟩
  let φEquiv := RingEquiv.ofBijective φRing hbij
  refine ⟨φEquiv, fun x => ?_, hφDP, ?_⟩
  · change φRing (qD (env.algebraMap.toRingHom x)) = lvl.algebraMap.toRingHom (qP x)
    rw [← RingHom.comp_apply, hφRing]
    simpa [envToE, RingHom.comp_apply] using RingHom.ext_iff.mp hgAlg x
  · have hsymm : φEquiv.symm.toRingHom = ψ.toRingHom := by
      refine RingHom.ext fun x => φEquiv.injective ?_
      have hx := (RingHom.ext_iff.mp
        (congrArg DividedPowers.DPMorphism.toRingHom hφψ)) x
      change φRing (ψ.toRingHom x) = (RingHom.id E) x at hx
      exact (φEquiv.apply_symm_apply x).trans hx.symm
    change lvl.object.dividedPowers.IsDPMorphism Q.dividedPowers
      φEquiv.symm.toRingHom
    rw [hsymm]
    exact ψ.isDPMorphism

end FiniteLevelEnvelope

end Crystalline
