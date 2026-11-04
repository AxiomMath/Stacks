module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# The tower `F / Iⁿ F` of a module `F ≅ M̃|_U`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a module
on `U` with an isomorphism `e : F ≅ M̃|_U` for an `A`-module `M`. The tower
`Stacks.Algebraization.quotientSystemNearVanishing` of sheaf quotients `F / Iⁿ F`, through which
the formal sections of Stacks 0EG2 and Stacks 0EIF are defined, is then the image of the tower
`n ↦ M / IⁿM` of `Stacks.LocalCohomology.idealPowerQuotientTower` under `N ↦ Ñ|_U`, by an
isomorphism of towers under which the quotient projections of `F` are the images of those of
`M`, precomposed with `e`.

This is the step of the proof of Stacks 0EIF that reads the formal sections of `F` as formal
sections of the module `M` of Stacks 0BK0.

## Main results

* `Stacks.Algebraization.idealOnOpen_eq_baseIdealSheaf` — the ideal sheaf `I𝒪_U` of an
  algebraization situation is `Stacks.Algebraization.idealSheafNearVanishing`.
* `Stacks.Algebraization.quotientSystemNearVanishingTildeIso` — the isomorphism of towers
  `(F / Iⁿ F)ₙ ≅ ((M / IⁿM)~|_U)ₙ`.
* `Stacks.Algebraization.adicProj_quotientSystemNearVanishingTildeIso_hom` — under it the
  projection `F ⟶ F / Iⁿ F` is `e` followed by the image of `M ⟶ M / IⁿM`.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- The ideal sheaf `I𝒪_U` of an algebraization situation is the extension of `I` along the open
immersion `U ⟶ Spec(A)`, which is the spelling `Stacks.Algebraization.idealSheafNearVanishing`
— and so `Stacks.Algebraization.formalSections` — is indexed by. -/
public theorem idealOnOpen_eq_baseIdealSheaf (S : AlgebraizationSituation.{u}) :
    idealOnOpen S = Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι := by
  rw [idealOnOpen, Stacks.AlgebraicGeometry.comap_ofIdealTop, Ideal.map_map,
    Stacks.Cohomology.FormalFunctions.baseIdealSheaf,
    Stacks.Cohomology.FormalFunctions.baseIdeal, CommRingCat.hom_comp]

/-- **On `U = Spec(A) ∖ V(𝔞)` the ideals `I` and `I ∩ 𝔞` generate the same ideal sheaf.** The
ideal `𝔞` generates the unit ideal sheaf on `U`, so `I𝒪_U = (I𝔞)𝒪_U ⊆ (I ∩ 𝔞)𝒪_U ⊆ I𝒪_U`. -/
public theorem idealSheafNearVanishing_inf_eq {A : Type u} [CommRing A] (I a : Ideal A) :
    idealSheafNearVanishing A (I ⊓ a) a = idealSheafNearVanishing A I a := by
  have htop : Stacks.Cohomology.FormalFunctions.baseIdealSheaf A a
      (complementZeroLocus A a).ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact x.2 ((PrimeSpectrum.mem_zeroLocus _ _).2 (support_baseIdealSheaf_le a _ hx))
  refine le_antisymm (Stacks.Cohomology.FormalFunctions.baseIdealSheaf_mono _ _ _ _
    inf_le_left) ?_
  calc idealSheafNearVanishing A I a
      = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (complementZeroLocus A a).ι *
          Stacks.Cohomology.FormalFunctions.baseIdealSheaf A a (complementZeroLocus A a).ι := by
        rw [htop]
        exact Scheme.IdealSheafData.ext (funext fun U => by
          rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_top,
            Pi.top_apply, Ideal.mul_top])
    _ = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (I * a)
          (complementZeroLocus A a).ι :=
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf_mul _ _ _ _).symm
    _ ≤ idealSheafNearVanishing A (I ⊓ a) a :=
        Stacks.Cohomology.FormalFunctions.baseIdealSheaf_mono _ _ _ _ Ideal.mul_le_inf

/-- The kernel of `M / (I ∩ 𝔞)ⁿM ⟶ M / IⁿM` is `𝔞`-power torsion, because
`𝔞ⁿIⁿ ⊆ (I ∩ 𝔞)ⁿ`. -/
private theorem isIPowerTorsion_ker_mapQ_inf {A : Type u} [CommRing A] (I a : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ)
    (h : (I ⊓ a) ^ n • (⊤ : Submodule A M) ≤ (I ^ n • ⊤ : Submodule A M).comap LinearMap.id) :
    IsIPowerTorsion A (Submodule.mapQ _ _ LinearMap.id h).ker a := by
  rintro ⟨x, hx⟩
  refine ⟨n + 1, Nat.succ_pos n, fun b hb => ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hm : m ∈ (I ^ n • ⊤ : Submodule A M) := by
    simpa [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] using hx
  have hbm : b • m ∈ ((I ⊓ a) ^ n • ⊤ : Submodule A M) := by
    have h1 : b • m ∈ (a ^ n * I ^ n) • (⊤ : Submodule A M) := by
      rw [mul_smul]
      exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hb) hm
    refine Submodule.smul_mono_left ?_ h1
    rw [← mul_pow]
    exact Ideal.pow_right_mono (Ideal.mul_le_inf.trans (by rw [inf_comm])) n
  ext
  simp only [Submodule.coe_smul, ZeroMemClass.coe_zero]
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  (e : F ≅ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
    ((tilde.functor (CommRingCat.of A)).obj M))

/-- The quotient map `M ⟶ M / IⁿM`, as a morphism into the `n`-th term of
`Stacks.LocalCohomology.idealPowerQuotientTower`. -/
private abbrev towerProj (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    M ⟶ (idealPowerQuotientTower.{u, u} I M).obj (op n) :=
  ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ

/-- **The sheaf quotient `F / Iⁿ F` is `(M / IⁿM)~|_U`**, by an isomorphism under which the
quotient projection of `F` is `e` followed by the image of `M ⟶ M / IⁿM`.

The source's standing assumption `I ⊆ 𝔞` is not needed. The construction for
`I ∩ 𝔞 ⊆ 𝔞` applies, the ideal sheaves of `I` and `I ∩ 𝔞` on `U` agree
(`Stacks.Algebraization.idealSheafNearVanishing_inf_eq`), and `M / (I ∩ 𝔞)ⁿM ⟶ M / IⁿM` is
surjective with `𝔞`-power torsion kernel, hence an isomorphism after `N ↦ Ñ|_U`. -/
public theorem exists_quotientSystemNearVanishing_iso (n : ℕ) :
    ∃ i : (quotientSystemNearVanishing A I a F).obj (op n) ≅
        (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
          ((tilde.functor (CommRingCat.of A)).obj
            (ModuleCat.of A (M ⧸ I ^ n • (⊤ : Submodule A M)))),
      (adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op n) ≫ i.hom =
        e.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          ((tilde.functor (CommRingCat.of A)).map
            (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ)) := by
  let S : AlgebraizationSituation.{u} := ⟨A, I ⊓ a, a, inf_le_right⟩
  let T := tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι
  have hS : idealOnOpen S = idealSheafNearVanishing A I a :=
    (idealOnOpen_eq_baseIdealSheaf S).trans (idealSheafNearVanishing_inf_eq I a)
  obtain ⟨i, hi⟩ : ∃ i : (quotientSystemNearVanishing A I a F).obj (op n) ≅
      T.obj (ModuleCat.of A (M ⧸ (I ⊓ a) ^ n • (⊤ : Submodule A M))),
      (adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op n) ≫ i.hom =
        e.hom ≫ T.map (ModuleCat.ofHom ((I ⊓ a) ^ n • (⊤ : Submodule A M)).mkQ) := by
    have h := exists_idealPowerQuotient_iso_restrictedTilde S M n (F := F) e
    rwa [hS] at h
  have hle : (I ⊓ a) ^ n • (⊤ : Submodule A M) ≤
      (I ^ n • ⊤ : Submodule A M).comap LinearMap.id :=
    Submodule.smul_mono_left (Ideal.pow_right_mono inf_le_left n)
  let q : ModuleCat.of A (M ⧸ (I ⊓ a) ^ n • (⊤ : Submodule A M)) ⟶
      ModuleCat.of A (M ⧸ I ^ n • (⊤ : Submodule A M)) :=
    ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id hle)
  have hq : IsIso (T.map q) := by
    refine (restrictedTilde_map_isIso_iff S _ _ q).2
      ⟨isIPowerTorsion_ker_mapQ_inf I a M n hle, fun x => ⟨1, one_pos, fun b _ => ?_⟩⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk (b • m), rfl⟩
  refine ⟨i ≪≫ asIso (T.map q), ?_⟩
  rw [Iso.trans_hom, asIso_hom, ← Category.assoc, hi]
  exact (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) (T.map_comp _ _).symm)

/-- **The isomorphism of towers `(F / Iⁿ F)ₙ ≅ ((M / IⁿM)~|_U)ₙ`**, its component at `n` being the
one of `Stacks.Algebraization.exists_quotientSystemNearVanishing_iso`. -/
public def quotientSystemNearVanishingTildeIso :
    quotientSystemNearVanishing A I a F ≅
      idealPowerQuotientTower.{u, u} I M ⋙ tilde.functor (CommRingCat.of A) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι :=
  NatIso.ofComponents
    (fun n => (exists_quotientSystemNearVanishing_iso (I := I) e n.unop).choose)
    (fun {m n} g => by
      induction m using Opposite.rec with | op m => ?_
      induction n using Opposite.rec with | op n => ?_
      have : Epi ((adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op m)) :=
        coequalizer.π_epi
      refine (cancel_epi ((adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op m))).1 ?_
      have hm := (exists_quotientSystemNearVanishing_iso (I := I) e m).choose_spec
      have hn := (exists_quotientSystemNearVanishing_iso (I := I) e n).choose_spec
      have hc : (adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op m) ≫
          (quotientSystemNearVanishing A I a F).map g =
          (adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op n) := by
        simp
      have hc' : towerProj I M m ≫ (idealPowerQuotientTower.{u, u} I M).map g =
          towerProj I M n := by
        ext x
        rfl
      rw [← Category.assoc, hc]
      refine hn.trans ?_
      rw [← Category.assoc]
      refine Eq.trans ?_ (congrArg (fun k => k ≫ _) hm).symm
      change e.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          ((tilde.functor (CommRingCat.of A)).map (towerProj I M n)) =
        (e.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          ((tilde.functor (CommRingCat.of A)).map (towerProj I M m))) ≫
          (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
            ((tilde.functor (CommRingCat.of A)).map ((idealPowerQuotientTower.{u, u} I M).map g))
      rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hc'])

/-- **Under `quotientSystemNearVanishingTildeIso` the projection `F ⟶ F / Iⁿ F` is `e` followed by
the image of the quotient map `M ⟶ M / IⁿM`.** -/
public theorem adicProj_quotientSystemNearVanishingTildeIso_hom (n : ℕ) :
    (adicQuotientCone (idealSheafNearVanishing A I a) F).π.app (op n) ≫
        (quotientSystemNearVanishingTildeIso e).hom.app (op n) =
      e.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        ((tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ)) :=
  (exists_quotientSystemNearVanishing_iso (I := I) e n).choose_spec

end Stacks.Algebraization

end
