module

public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.AdicFiltrationFunctor
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.GenericFibreRank
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.IsoNearSpecialFibre
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.SectionLifting
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.ThickeningQuotient

/-!
# Freeness of a vector bundle from its generic fibre and one thickening of its special fibre

This file proves [Stacks, Tag 0EXF] with no hypothesis beyond those of the source.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `stalkTorsionBounded_of_isFiniteLocallyFree`: the stalks of a finite locally free module
  inherit the torsion exponent of the local rings.
* `finrank_cohomology_adicFiltration_zero`: `H⁰(X, πᵏ F)` and `H⁰(X, F)` have the same rank.
* `exists_sections_lift`: sections of `F / πⁿ⁺ᵉ F`, reduced modulo `πⁿ`, lift to `F`.
* `adicProj_comp_adicQuotientIsoOfLE_hom`: the lowered isomorphism `F / πʲ F ≅ G / πʲ G` is
  the reduction of `F / πⁿ F ≅ G / πⁿ G`.
* `exists_thickening_exponent_free`: **[Stacks, Tag 0EXF].**

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization Stacks.ModuleSkyscraper

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {X : Scheme.{u}}

/-- **The stalks of a finite locally free module inherit the torsion exponent of the local
rings**, being free. -/
theorem stalkTorsionBounded_of_isFiniteLocallyFree {t : Γ(X, ⊤)} {k : ℕ}
    (hk : ∀ (x : X) (a : X.presheaf.stalk x) (j : ℕ),
      (X.presheaf.Γgerm x).hom t ^ j * a = 0 → (X.presheaf.Γgerm x).hom t ^ k * a = 0)
    (E : X.Modules) (hE : E.IsFiniteLocallyFree) : StalkTorsionBounded E t k := fun x v j hv =>
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).mp hE
  have : Module.Free (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj E) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E x).1
  pow_smul_eq_zero_of_free (hk x) v j hv

variable {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A)) (π : A)

/-- **`H⁰(X, πᵏ F)` and `H⁰(X, F)` have the same rank** over a domain, for `π ≠ 0`: the first
injects into the second, and the cokernel is killed by `πᵏ`, multiplication by `πᵏ` on `F`
factoring through `πᵏ F`. -/
theorem finrank_cohomology_adicFiltration_zero [IsDomain A] (hπ : π ≠ 0) (F : X.Modules)
    (k : ℕ) :
    Module.finrank A
        (cohomologyOver A f 0 (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules) =
      Module.finrank A (cohomologyOver A f 0 F) := by
  let g := cohomologyMap A f 0 ((adicFiltration f (Ideal.span {π}) k F).ι :
    ((adicFiltration f (Ideal.span {π}) k F).toSheafOfModules : X.Modules) ⟶ F)
  have hinj : Function.Injective g := (ModuleCat.mono_iff_injective
    (((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).functor 0).map
      (idealPowerQuotientShortComplex (baseIdeal f (Ideal.span {π})) k F).f)).1
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).mono_map_f
      (idealPowerQuotientShortComplex_shortExact (baseIdeal f (Ideal.span {π})) k F))
  have hrange : ∀ y, π ^ k • y ∈ LinearMap.range g := fun y =>
    ⟨cohomologyMap A f 0 (adicLift f π F k) y,
      (LinearMap.congr_fun (cohomologyMap_comp A f 0 (adicLift f π F k)
        ((adicFiltration f (Ideal.span {π}) k F).ι :
          ((adicFiltration f (Ideal.span {π}) k F).toSheafOfModules : X.Modules) ⟶ F)) y).symm.trans
        ((congrArg (fun φ => cohomologyMap A f 0 φ y)
        (adicLift_comp_ι f π F k)).trans
        (LinearMap.congr_fun (cohomologyMap_globalSmul A f 0 π k F) y))⟩
  have htors : Module.rank A (cohomologyOver A f 0 F ⧸ LinearMap.range g) = 0 := by
    have hle : (⊤ : Submodule A (cohomologyOver A f 0 F ⧸ LinearMap.range g)) ≤
        Submodule.torsion A (cohomologyOver A f 0 F ⧸ LinearMap.range g) := by
      intro z _
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      refine ⟨⟨π ^ k, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k hπ)⟩, ?_⟩
      show π ^ k • (Submodule.Quotient.mk y : cohomologyOver A f 0 F ⧸ LinearMap.range g) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hrange y
    rw [← rank_quotient_eq_of_le_torsion hle]
    exact rank_subsingleton' A _
  have h := rank_quotient_add_rank_of_isDomain (R := A) (LinearMap.range g)
  rw [htors, zero_add, (LinearEquiv.ofInjective g hinj).rank_eq.symm] at h
  exact congrArg Cardinal.toNat h

/-- **Lifting global sections modulo `πⁿ`**, on global sections: `exists_cohomology_lift` read
through `H⁰(X, -) = Γ(X, -)`. -/
theorem exists_sections_lift (F : X.Modules) [F.IsQuasicoherent] {k e : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap f π) k)
    (he : ∀ (c : cohomologyOver A f 1 (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules)
      (i : ℕ), π ^ i • c = 0 → π ^ e • c = 0)
    {n : ℕ} (hn : k ≤ n) (s : Γ(adicQuotient f (Ideal.span {π}) (n + e) F, ⊤)) :
    ∃ t : Γ(F, ⊤), (adicProj f (Ideal.span {π}) n F).app ⊤ t =
      (idealPowerQuotientDrop (baseIdeal f (Ideal.span {π})) (Nat.le_add_right n e) F).app ⊤ s := by
  let ζ := (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedZeroIsoSelf
  obtain ⟨t', ht'⟩ := exists_cohomology_lift f π F hk he hn
    ((ζ.app (adicQuotient f (Ideal.span {π}) (n + e) F)).inv s)
  refine ⟨(ζ.app F).hom t', ?_⟩
  have h₁ := ConcreteCategory.congr_hom (ζ.hom.naturality (adicProj f (Ideal.span {π}) n F)) t'
  have h₂ := ConcreteCategory.congr_hom (ζ.hom.naturality
    (idealPowerQuotientDrop (baseIdeal f (Ideal.span {π})) (Nat.le_add_right n e) F))
    ((ζ.app (adicQuotient f (Ideal.span {π}) (n + e) F)).inv s)
  exact h₁.symm.trans ((congrArg (ζ.app _).hom ht').trans
    (h₂.trans (congrArg _ (Iso.inv_hom_id_apply (ζ.app _) s))))

variable {π} in
/-- **The lowered isomorphism is the reduction of the given one**: for
`φ : F / πⁿ F ≅ G / πⁿ G` and `j ≤ n`, the composite of `F ⟶ F / πʲ F` with the lowered
isomorphism is `F ⟶ F / πⁿ F ≅ G / πⁿ G ⟶ G / πʲ G`. -/
theorem adicProj_comp_adicQuotientIsoOfLE_hom {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] {j n : ℕ} (h : j ≤ n)
    (φ : adicQuotient f (Ideal.span {π}) n F ≅ adicQuotient f (Ideal.span {π}) n G) :
    adicProj f (Ideal.span {π}) j F ≫ (adicQuotientIsoOfLE h φ).hom =
      adicProj f (Ideal.span {π}) n F ≫ φ.hom ≫
        idealPowerQuotientDrop (baseIdeal f (Ideal.span {π})) h G := by
  have key : cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdeal f (Ideal.span {π})) j
      (adicQuotient f (Ideal.span {π}) n G)).ι =
      idealPowerQuotientDrop (baseIdeal f (Ideal.span {π})) h G ≫
        idealPowerQuotientMap _ _ j j le_rfl (adicProj f (Ideal.span {π}) n G) := by
    refine (cancel_epi (adicProj f (Ideal.span {π}) n G)).1 ?_
    rw [idealPowerQuotientDrop_π_assoc, idealPowerQuotientMap_π]
  simp only [adicQuotientIsoOfLE, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [idealPowerQuotientMap_π_assoc]
  have := isIso_idealPowerQuotientMap_cokernel_π (baseIdeal f (Ideal.span {π}))
    (baseIdeal f (Ideal.span {π})) j n (Scheme.IdealSheafData.pow_le_pow_of_le _ h) G
  exact congrArg (fun g => adicProj f (Ideal.span {π}) n F ≫ φ.hom ≫ g)
    ((IsIso.comp_inv_eq _).2 key)

/-- A torsion bound at one exponent bounds all the `π`-power torsion: if `πᵉ` kills the
`πᵉ⁺¹`-torsion of `M`, it kills every element killed by a power of `π`. -/
theorem pow_smul_eq_zero_of_torsionBy_succ {M : Type*} [AddCommGroup M] [Module A M] {e : ℕ}
    (h : Ideal.span {π} ^ e • Submodule.torsionBy A M (π ^ (e + 1)) = ⊥) :
    ∀ (i : ℕ) (c : M), π ^ i • c = 0 → π ^ e • c = 0 := by
  intro i
  induction i with
  | zero =>
    intro c hc
    simp_all
  | succ i ih =>
    intro c hc
    have h₁ : π ^ i • (π • c) = 0 := by rwa [← mul_smul, ← pow_succ]
    exact pow_smul_torsionBy_eq_bot_iff.1 h c (by simpa only [pow_succ, mul_smul] using ih _ h₁)

/-- A free module of finite rank is finite locally free. -/
theorem isFiniteLocallyFree_free (r : ℕ) :
    (Scheme.Modules.free X (ULift.{u} (Fin r))).IsFiniteLocallyFree :=
  fun _ => ⟨⊤, trivial, ULift.{u} (Fin r), inferInstance,
    ⟨(Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app _ ≪≫
      Scheme.Modules.pullbackFreeIso _ _⟩⟩

/-- A finite locally free module on a locally Noetherian scheme is coherent. -/
private theorem isCoherent_of_isFiniteLocallyFree' [IsLocallyNoetherian X] (E : X.Modules)
    (hE : E.IsFiniteLocallyFree) : E.IsCoherent :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).mp hE
  Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree _ E

/-- **Stacks, Tag 0EXF.** Let `f : X ⟶ S` be a proper morphism where `S = Spec A` is the
spectrum of a discrete valuation ring. Denote `η ∈ S` the generic point and `Xₙ ⊆ X` the closed
subscheme cut out by the `n`-th power of a uniformizer. Then there exists an integer `n` such
that any finite locally free `𝒪_X`-module `𝓔` such that `𝓔|_{X_η}` and `𝓔|_{Xₙ}` are free, is
free.

The integer is `n = k + 1 + e`. Here `k` bounds the `π`-power torsion of the local rings of `X`
(`exists_forall_germ_pow_mul_eq_zero`), and `e` bounds the `π`-power torsion of
`H¹(X, πᵏ 𝒪_X^r)` for every rank `r` at once (`exists_pow_smul_cohomology_adicSub_free_eq_zero`).
Comparing the lengths of `H⁰(X, πᵏ (𝓔 / πᵏ⁺ᵐ 𝓔))` and `H⁰(X, πᵏ (𝒪_X^r / πᵏ⁺ᵐ 𝒪_X^r))` at
`m = e` and `m = e + 1`, which agree because `𝓔 / πⁿ 𝓔 ≅ 𝒪_X^r / πⁿ 𝒪_X^r`, transfers that
bound to `H¹(X, πᵏ 𝓔)` (`torsionBy_cohomology_eq_bot_of_adicQuotientIso`); the free ranks of the
two `H⁰` agree by the generic fibre. The basis sections of `𝒪_X^r / πⁿ 𝒪_X^r` then lift, modulo
`πᵏ⁺¹`, to global sections of `𝓔` (`exists_sections_lift`), and the resulting
`𝒪_X^r ⟶ 𝓔` is an isomorphism modulo `πᵏ⁺¹`, hence an isomorphism since `f` is proper over a
local base (`isIso_of_comp_adicProj`).

The source's hypothesis that the fibres of `f` be geometrically connected is not used: the
source needs it only to reduce to the case where `f` has a section, and the argument above does
not pass through a section. -/
@[stacks 0EXF "without the hypothesis that the fibres are geometrically connected, which the \
proof does not use"]
theorem exists_thickening_exponent_free (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∃ n : ℕ, 0 < n ∧ ∀ E : X.Modules, E.IsFiniteLocallyFree →
      IsFreeOfFiniteRank (genericFibreRestrict A f E) →
      IsFreeOfFiniteRank (thickeningRestrict A f n E) →
      IsFreeOfFiniteRank E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {π} := hπ.maximalIdeal_eq
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  have : IsNoetherian X := { }
  obtain ⟨k, hk⟩ := exists_forall_germ_pow_mul_eq_zero (baseScalarMap f π)
  obtain ⟨e, he⟩ := exists_pow_smul_cohomology_adicSub_free_eq_zero f π k
  refine ⟨k + 1 + e, by omega, fun E hE ⟨r', ⟨eη⟩⟩ ⟨r, ⟨en⟩⟩ => ?_⟩
  have hO := isFiniteLocallyFree_free (X := X) r
  have : E.IsCoherent := isCoherent_of_isFiniteLocallyFree' E hE
  have : (Scheme.Modules.free X (ULift.{u} (Fin r))).IsCoherent :=
    isCoherent_of_isFiniteLocallyFree' _ hO
  have : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  have : (Scheme.Modules.free X (ULift.{u} (Fin r))).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hEk := stalkTorsionBounded_of_isFiniteLocallyFree hk E hE
  let φ := adicQuotientIsoFreeOfThickening A f hmax (k + 1 + e) en
  obtain ⟨eη'⟩ := nonempty_genericFibreRestrict_iso_free A f E hE (n := k + 1 + e) (by omega) eη en
  have hrank : Module.finrank A (cohomologyOver A f 0
        (adicFiltration f (Ideal.span {π}) k E).toSheafOfModules ⧸
      Submodule.torsion A (cohomologyOver A f 0
        (adicFiltration f (Ideal.span {π}) k E).toSheafOfModules)) =
      Module.finrank A (cohomologyOver A f 0 (adicFiltration f (Ideal.span {π}) k
          (Scheme.Modules.free X (ULift.{u} (Fin r)))).toSheafOfModules ⧸
        Submodule.torsion A (cohomologyOver A f 0 (adicFiltration f (Ideal.span {π}) k
          (Scheme.Modules.free X (ULift.{u} (Fin r)))).toSheafOfModules)) := by
    rw [finrank_quotient_eq_of_le_torsion le_rfl, finrank_quotient_eq_of_le_torsion le_rfl,
      finrank_cohomology_adicFiltration_zero f π hπ.ne_zero E k,
      finrank_cohomology_adicFiltration_zero f π hπ.ne_zero _ k]
    exact finrank_cohomologyOver_zero_eq_of_genericFibre_iso A f eη'
  have hE₁ := torsionBy_cohomology_eq_bot_of_adicQuotientIso A f π hπ hEk
    (stalkTorsionBounded_of_isFiniteLocallyFree hk _ hO) (by omega) φ hrank
    (pow_smul_torsionBy_eq_bot_iff.2 fun c hc => he r c (e + 1) hc)
  -- The sections of `𝓔 / πⁿ 𝓔` corresponding to the basis of `𝒪_X^r / πⁿ 𝒪_X^r`.
  let s : Fin r → Γ(adicQuotient f (Ideal.span {π}) (k + 1 + e) E, ⊤) := fun j =>
    φ.inv.app ⊤ ((adicProj f (Ideal.span {π}) (k + 1 + e)
      (Scheme.Modules.free X (ULift.{u} (Fin r)))).app ⊤ (freeSectionsBasis X r j))
  choose t ht using fun j => exists_sections_lift f π E hEk
    (fun c i => pow_smul_eq_zero_of_torsionBy_succ (A := A) π hE₁ i c) (n := k + 1)
    (by omega) (s j)
  let α := Scheme.Modules.freeHomOfSections E t
  let ψ := adicQuotientIsoOfLE (Nat.le_add_right (k + 1) e) φ.symm
  have hα : α ≫ adicProj f (Ideal.span {π}) (k + 1) E =
      adicProj f (Ideal.span {π}) (k + 1)
        (Scheme.Modules.free X (ULift.{u} (Fin r))) ≫ ψ.hom := by
    rw [adicProj_comp_adicQuotientIsoOfLE_hom]
    refine Scheme.Modules.free_hom_ext fun j => ?_
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.freeHomOfSections_app_freeSectionsBasis, ht j]
    rfl
  have := isIso_of_comp_adicProj f (hmax ▸ Ideal.mem_span_singleton_self π) hO hE α (by omega)
    ψ hα
  exact ⟨r, ⟨(asIso α).symm⟩⟩

end Stacks.AlgebraicGeometry.FreenessOverDVR
