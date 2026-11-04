module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Flatness.ClosedFibreFlatCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# Flatness at a point from flatness at the associated points of its fibre

Let `f : X → S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type and let `x ∈ X` with image `s ∈ S`. This file proves Stacks 05UA: `F` is flat over `S` at
`x` if and only if `F` is flat over `S` at every associated point of the fibre `F_s` on `X_s`
which specializes to `x`.

## Main results

* `AlgebraicGeometry.exists_specializes_comap_maximalIdeal_eq`: every prime `p` of `𝒪_{X, x}` is
  the contraction of the maximal ideal of `𝒪_{X, w}` for a generalization `w` of `x`.
* `AlgebraicGeometry.eq_of_comap_maximalIdeal_stalkSpecializes`: a specialization `a ⤳ b` whose
  map of local rings pulls back the maximal ideal to the maximal ideal is an equality.
* `AlgebraicGeometry.bijective_stalkSpecializes_of_eq`: the specialization map between the local
  rings at two equal points is bijective.
* `AlgebraicGeometry.isFlatOverAt_of_forall_isAssociatedPoint_specializes`: the implication
  (2) ⟹ (1) of Stacks 05UA.
* `AlgebraicGeometry.isFlatOverAt_iff_forall_isAssociatedPoint_specializes`: Stacks 05UA.

## Implementation notes

The proof is the one in the source. With `R = 𝒪_{S, s}`, `B = 𝒪_{X, x}` and `N = F_x`, the
commutative algebra — `N` is flat over `R` once `N_p` is flat over `R` at every associated prime
`p` of the closed fibre `N / 𝔪_R N`, by Stacks 05DE and Stacks 0AT4 — is
`Stacks.Flatness.flat_of_forall_flat_atPrime_assStacks_closedFibre`. This file supplies the
dictionary between such a prime and a point of the fibre.

Given `p`, the point `w` is the image of `p` under `Spec 𝒪_{X, x} → X`
(`exists_specializes_comap_maximalIdeal_eq`), so that `𝒪_{X, w}` and `F_w` are the localizations
of `B` and `N` at `p` (`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`,
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes`). Since `p`
contains `𝔪_R B`, the map `𝒪_{S, s} → 𝒪_{S, f w}` pulls the maximal ideal back to `𝔪_R`, so
`f w = s` by `eq_of_comap_maximalIdeal_stalkSpecializes` and `w` lies in the fibre. The quotient
`F_w / 𝔪_{S, f w} F_w` is then the localization of `N / 𝔪_R N` at `p`
(`IsLocalizedModule.toLocalizedQuotient'`, once `Submodule.localized'_smul` and the naturality
`Scheme.Hom.stalkSpecializes_stalkMap` identify the two submodules), and an element of
`N / 𝔪_R N` with annihilator `p` maps to an element with annihilator `𝔪_{X, w}`. By the fibre
dictionary `Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq` this says that `w` is an
associated point of `F_s`, and flatness of `F_w` over `𝒪_{S, f w}` is flatness of `N_p` over
`R` through the bijection `𝒪_{S, s} → 𝒪_{S, f w}`.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 0AT4](https://stacks.math.columbia.edu/tag/0AT4)
* [Stacks Project, Tag 05DE](https://stacks.math.columbia.edu/tag/05DE)
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The image of the closed point of `Spec 𝒪_{X, a}` in `Spec 𝒪_{X, b}` under the specialization
map, followed by `Spec 𝒪_{X, b} → X`, is `a`. -/
private theorem fromSpecStalk_comap_closedPoint {X : Scheme.{u}} {a b : X} (h : a ⤳ b) :
    X.fromSpecStalk b (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
      (closedPoint (X.presheaf.stalk a))) = a := by
  show (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk b) (closedPoint _) = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.fromSpecStalk_closedPoint]

/-- Every prime ideal `p` of the local ring `𝒪_{X, x}` is the contraction of the maximal ideal of
`𝒪_{X, w}` along the specialization map, for some generalization `w` of `x`: the point `w` is the
image of `p` under `Spec 𝒪_{X, x} → X`. -/
theorem exists_specializes_comap_maximalIdeal_eq {X : Scheme.{u}} (x : X)
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ (w : X) (h : w ⤳ x),
      (maximalIdeal (X.presheaf.stalk w)).comap (X.presheaf.stalkSpecializes h).hom = p := by
  let q : PrimeSpectrum (X.presheaf.stalk x) := ⟨p, inferInstance⟩
  have hw : X.fromSpecStalk x q ⤳ x := by
    have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  refine ⟨X.fromSpecStalk x q, hw, ?_⟩
  have h : PrimeSpectrum.comap (X.presheaf.stalkSpecializes hw).hom
      (closedPoint (X.presheaf.stalk (X.fromSpecStalk x q))) = q := by
    apply (X.fromSpecStalk x).isEmbedding.injective
    rw [fromSpecStalk_comap_closedPoint]
  exact congrArg PrimeSpectrum.asIdeal h

/-- A specialization `a ⤳ b` whose specialization map of local rings pulls the maximal ideal back
to the maximal ideal is trivial: both points are the image of the closed point of
`Spec 𝒪_{X, b}`. -/
theorem eq_of_comap_maximalIdeal_stalkSpecializes {X : Scheme.{u}} {a b : X} (h : a ⤳ b)
    (hm : (maximalIdeal (X.presheaf.stalk a)).comap (X.presheaf.stalkSpecializes h).hom =
      maximalIdeal (X.presheaf.stalk b)) : a = b := by
  have hpt : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
      (closedPoint (X.presheaf.stalk a)) = closedPoint (X.presheaf.stalk b) :=
    PrimeSpectrum.ext hm
  have e := fromSpecStalk_comap_closedPoint h
  rw [hpt, Scheme.fromSpecStalk_closedPoint] at e
  exact e.symm

/-- The specialization map between the local rings at two equal points is bijective. -/
theorem bijective_stalkSpecializes_of_eq {X : Scheme.{u}} {a b : X} (h : a ⤳ b) (e : a = b) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- **Stacks 05UA, the implication (2) ⟹ (1).** Let `f : X ⟶ S` be locally of finite type, let
`F` be a quasi-coherent `𝒪_X`-module of finite type and let `x ∈ X`. If `F` is flat over `S` at
every associated point of the restriction of `F` to the fibre over `f x` which specializes to
`x`, then `F` is flat over `S` at `x`. -/
theorem isFlatOverAt_of_forall_isAssociatedPoint_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (h : ∀ x' : f.fiber (f x),
      x' ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) →
        f.fiberι (f x) x' ⤳ x → IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) x')) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  let B := X.presheaf.stalk x
  let R := S.presheaf.stalk (f.base x)
  let N := F.presheaf.stalk x
  let : Module B N := Stacks.ModuleStalkSpecialization.stalkModule F x
  let : Algebra R B := (f.stalkMap x).hom.toAlgebra
  let : Module R N := Module.compHom _ (f.stalkMap x).hom
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalHom (algebraMap R B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType R B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Module.Finite B N := SheafOfModules.finite_stalk X.sheaf F x
  have : IsNoetherianRing (R ⧸ maximalIdeal R) :=
    isNoetherianRing_of_ringEquiv (ResidueField R) (RingEquiv.refl _)
  have : IsNoetherianRing (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R)) :=
    Algebra.EssFiniteType.isNoetherianRing (R ⧸ maximalIdeal R) _
  have : Module.Finite (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
      (N ⧸ Ideal.map (algebraMap R B) (maximalIdeal R) • (⊤ : Submodule B N)) := by
    have : Module.Finite B (N ⧸ Ideal.map (algebraMap R B) (maximalIdeal R) •
        (⊤ : Submodule B N)) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
    exact Module.Finite.of_restrictScalars_finite B _ _
  show Module.Flat R N
  refine Stacks.Flatness.flat_of_forall_flat_atPrime_assStacks_closedFibre
    (R := R) (S := B) (N := N) fun p hp hass => ?_
  set I : Ideal B := Ideal.map (algebraMap R B) (maximalIdeal R) with hI
  obtain ⟨-, n₀, hn₀⟩ := hass
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule B N)) n₀
  -- `r ∈ p` exactly when `r` kills the class of `n` in the closed fibre.
  have key : ∀ r : B, r ∈ p ↔ r • (I • (⊤ : Submodule B N)).mkQ n = 0 := fun r => by
    rw [← hn₀, Submodule.colon_span, Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hIp : I ≤ p := fun i hi => (key i).mpr (by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hi trivial)
  -- The generalization `w` of `x` corresponding to `p`.
  obtain ⟨w, hw, hpw⟩ := exists_specializes_comap_maximalIdeal_eq x p
  let C := X.presheaf.stalk w
  let φX : B →+* C := (X.presheaf.stalkSpecializes hw).hom
  have hw' : f.base w ⤳ f.base x := f.base.hom.map_specializes hw
  let φS : R →+* S.presheaf.stalk (f.base w) := (S.presheaf.stalkSpecializes hw').hom
  have hnat : (f.stalkMap w).hom.comp φS = φX.comp (f.stalkMap x).hom := by
    have := congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkSpecializes_stalkMap f w x hw)
    simpa only [CommRingCat.hom_comp] using this
  -- The point `w` lies in the fibre of `x`.
  have hcomapS : (maximalIdeal (S.presheaf.stalk (f.base w))).comap φS = maximalIdeal R := by
    refine ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      fun r hr => ?_).symm
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : (f.stalkMap x).hom r ∈ p := hIp (Ideal.mem_map_of_mem _ hr)
    rw [← hpw, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at h1
    apply h1
    have := hu.map (f.stalkMap w).hom
    rwa [← RingHom.comp_apply, hnat] at this
  have hfw : f.base w = f.base x := eq_of_comap_maximalIdeal_stalkSpecializes hw' hcomapS
  have hbijS : Function.Bijective φS := bijective_stalkSpecializes_of_eq hw' hfw
  have hmapS : Ideal.map φS (maximalIdeal R) = maximalIdeal (S.presheaf.stalk (f.base w)) := by
    rw [← hcomapS, Ideal.map_comap_of_surjective _ hbijS.2]
  obtain ⟨x', hx'⟩ : w ∈ Set.range (f.fiberι (f x)) := by
    rw [Scheme.Hom.range_fiberι]
    exact hfw
  -- Localization data at `w`.
  let : Algebra B C := φX.toAlgebra
  have : IsLocalization.AtPrime C p :=
    Stacks.StalkSpecialization.isLocalization_atPrime_of_eq hpw
      (Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hw)
  let : Module C (F.presheaf.stalk w) := Stacks.ModuleStalkSpecialization.stalkModule F w
  let : Module B (F.presheaf.stalk w) :=
    Stacks.ModuleStalkSpecialization.stalkSpecializesModule F hw
  have : IsScalarTower B C (F.presheaf.stalk w) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ := Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F hw
  have : IsLocalizedModule p.primeCompl φ := by
    have hφ := Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F hw
    have he : ((maximalIdeal C).under B).primeCompl = p.primeCompl := by
      ext a
      show a ∉ _ ↔ a ∉ _
      rw [← hpw]
      rfl
    change IsLocalizedModule ((maximalIdeal C).under B).primeCompl φ at hφ
    rwa [he] at hφ
  -- The closed fibre localizes to the fibre module at `w`.
  have hJ : Ideal.map (f.stalkMap w).hom (maximalIdeal (S.presheaf.stalk (f.base w))) =
      Ideal.map (algebraMap B C) I := by
    rw [← hmapS, Ideal.map_map, hnat, hI, Ideal.map_map]
    rfl
  have hL : (I • (⊤ : Submodule B N)).localized' C p.primeCompl φ =
      Ideal.map (f.stalkMap w).hom (maximalIdeal (S.presheaf.stalk (f.base w))) •
        (⊤ : Submodule C (F.presheaf.stalk w)) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top, hJ]
  let ψ := (I • (⊤ : Submodule B N)).toLocalizedQuotient' C p.primeCompl φ
  have hass' : IsAssociatedPrimeStacks C
      (F.presheaf.stalk w ⧸ (I • (⊤ : Submodule B N)).localized' C p.primeCompl φ)
      (maximalIdeal C) := by
    refine ⟨inferInstance, ψ ((I • (⊤ : Submodule B N)).mkQ n), ?_⟩
    ext a
    rw [Submodule.colon_span, Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
    simp only
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff C p b t,
      ← IsLocalizedModule.mk'_one p.primeCompl ψ, IsLocalizedModule.mk'_smul_mk', mul_one,
      IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun ⟨c, hc⟩ => ?_, fun hb => ⟨1, by rw [one_smul, ← key]; exact hb⟩⟩
    rw [Submonoid.smul_def, smul_smul, ← key] at hc
    exact (Ideal.IsPrime.mem_or_mem inferInstance hc).resolve_left c.2
  rw [hL] at hass'
  have hassw : x' ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) :=
    (Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq f F x' hx').mpr hass'
  have hflw : IsFlatOverAt f.toLRSHom.toShHom F w := hx' ▸ h x' hassw (hx' ▸ hw)
  -- Flatness at `w` is flatness of the localization `N_p`.
  let : Module (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w) :=
    Module.compHom _ (f.stalkMap w).hom
  have hflw' : Module.Flat (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w) := hflw
  let : Module R (F.presheaf.stalk w) := Module.compHom _ (algebraMap R B)
  have : IsScalarTower R B (F.presheaf.stalk w) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Algebra R (S.presheaf.stalk (f.base w)) := φS.toAlgebra
  have : IsScalarTower R (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w) := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    show (f.stalkMap w).hom (φS r) • m = φX ((f.stalkMap x).hom r) • m
    rw [← RingHom.comp_apply, hnat, RingHom.comp_apply]
  have : Module.Flat R (S.presheaf.stalk (f.base w)) := by
    let e : R ≃ₗ[R] S.presheaf.stalk (f.base w) :=
      LinearEquiv.ofBijective (Algebra.linearMap R (S.presheaf.stalk (f.base w))) hbijS
    have : Module.Flat R R := Module.Flat.self
    exact Module.Flat.of_linearEquiv e.symm
  have : Module.Flat R (F.presheaf.stalk w) :=
    Module.Flat.trans R (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w)
  exact Module.Flat.of_linearEquiv ((IsLocalizedModule.iso p.primeCompl φ).restrictScalars R)

/-- **Stacks 05UA.** Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `x ∈ X`. Then `F` is flat over `S` at `x` if and only if `F`
is flat over `S` at every associated point of the restriction of `F` to the fibre over `f x`
which specializes to `x`. -/
@[stacks 05UA "`Ass_{X_s}(F_s)` is `Stacks.Divisors.associatedPoints` of the pullback of `F` to
the scheme-theoretic fibre `f.fiber (f x)`, and flatness at a point is `IsFlatOverAt`."]
theorem isFlatOverAt_iff_forall_isAssociatedPoint_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      ∀ x' : f.fiber (f x),
        x' ∈ Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) →
          f.fiberι (f x) x' ⤳ x → IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) x') := by
  refine ⟨fun hflat x' _ hsp => ?_,
    isFlatOverAt_of_forall_isAssociatedPoint_specializes f F x⟩
  have hbase : f.base (f.fiberι (f x) x') = f.base x := by
    have : f.fiberι (f x) x' ∈ f.base ⁻¹' {f x} := by
      rw [← Scheme.Hom.range_fiberι]
      exact Set.mem_range_self x'
    simpa using this
  exact isFlatOverAt_of_specializes f F hsp hbase hflat

end AlgebraicGeometry

end
