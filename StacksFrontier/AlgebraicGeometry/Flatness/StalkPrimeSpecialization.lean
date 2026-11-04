module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk

/-!
# The point of a scheme cut out by a prime of a local ring

Let `X` be a scheme, let `x` be a point of `X` and let `p` be a prime ideal of the local ring
`𝒪_{X, x}`. Then there is a point `z` of `X` generalizing `x` whose local ring is the
localization of `𝒪_{X, x}` at `p`; and for a quasi-coherent `𝒪_X`-module `F` the stalk `F_z` is
the localization of `F_x` at `p` over that identification.

This is the converse of `AlgebraicGeometry.exists_isLocalizedModule_stalkSpecializes`, which
localizes the stalk of a module along a given generalization: here the generalization is
*produced* from a prime of the local ring at `x`. It is the dictionary through which a statement
quantified over the primes of the local ring `𝒪_{X, x}` — as the commutative algebra of the
converse implication of Stacks 05UA is, see
`Stacks.Flatness.flat_of_forall_flat_atPrime_assStacks_closedFibre` — is read as a statement
quantified over the points of `X` generalizing `x`.

## Main results

* `AlgebraicGeometry.exists_specializes_isLocalization_isLocalizedModule_stalk`: the point `z`,
  together with the two localization statements.

## Implementation notes

Everything happens on one affine open `U ∋ x`. There the prime `p` of `𝒪_{X, x} = Γ(X, U)_{𝔮ₓ}`
contracts to a prime `𝔮 ⊆ 𝔮ₓ` of `Γ(X, U)`, and `z` is the point of `U` that `𝔮` names, namely
`IsAffineOpen.fromSpec` of it. Both local rings and both stalks of `F` are localizations of
`Γ(X, U)` and of `Γ(F, U)` at those two primes, by `IsAffineOpen.isLocalization_stalk` and
`AlgebraicGeometry.affineGerm_isLocalized`, so the comparison maps are
`IsLocalization.isLocalization_of_submonoid_le` and `IsLocalizedModule.liftOfLE`.

Both comparisons are first obtained at the image in `𝒪_{X, x}` of the multiplicative set
`Γ(X, U) ∖ 𝔮`, which is smaller than `𝒪_{X, x} ∖ p`. The ring statement is moved to the larger
set by `IsLocalization.of_le`, every element of `𝒪_{X, x} ∖ p` being invertible in `𝒪_{X, z}`
because it is a fraction of two elements of `Γ(X, U) ∖ 𝔮`. The module statement is moved by
`isLocalizedModule_iff_isBaseChange` in both directions: being a localization at either set is
being the base change along `𝒪_{X, x} → 𝒪_{X, z}`, which mentions neither set.

The module structure on the stalk of an `𝒪_X`-module over the stalk of the structure sheaf is
`AlgebraicGeometry.Scheme.Modules.moduleStalk`, and over the sections on an affine open it is
`AlgebraicGeometry.affineStalkModule`; neither is found by typeclass resolution for the spelling
`F.presheaf.stalk x`, so both are supplied by hand, as in
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/AffineLocalization.lean`.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace IsLocalization

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] (S : Submonoid R) [IsLocalization S A]
  (p : Ideal A) [p.IsPrime]

/-- The contraction to `R` of a prime of a localization `S⁻¹R` is disjoint from `S`. -/
theorem le_primeCompl_under : S ≤ (p.under R).primeCompl := fun m hm hmp =>
  ‹p.IsPrime›.ne_top (p.eq_top_of_isUnit_mem (Ideal.mem_comap.mp hmp) (map_units A ⟨m, hm⟩))

include S in
/-- If `B` is an `S⁻¹R`-algebra which is the localization of `R` at the contraction of a prime `p`
of `S⁻¹R`, then `B` is the localization of `S⁻¹R` at `p`. -/
theorem isLocalization_primeCompl_of_under [IsLocalization.AtPrime B (p.under R)] :
    IsLocalization p.primeCompl B := by
  have := isLocalization_of_submonoid_le A B S (p.under R).primeCompl (le_primeCompl_under S p)
  refine of_le ((p.under R).primeCompl.map (algebraMap R A)) p.primeCompl ?_ ?_
  · rintro b ⟨r, hr, rfl⟩
    exact hr
  · intro b hb
    obtain ⟨⟨r, t⟩, rfl⟩ := mk'_surjective S b
    have hspec : mk' A r t * algebraMap R A t = algebraMap R A r := mk'_spec _ _ _
    have hr : r ∈ (p.under R).primeCompl := fun hr => by
      have hmem : mk' A r t * algebraMap R A t ∈ p := hspec ▸ hr
      rcases ‹p.IsPrime›.mul_mem_iff_mem_or_mem.mp hmem with h | h
      · exact hb h
      · exact ‹p.IsPrime›.ne_top (p.eq_top_of_isUnit_mem h (map_units A t))
    have hur : IsUnit (algebraMap R B r) := map_units B (⟨r, hr⟩ : (p.under R).primeCompl)
    have hmap := congrArg (algebraMap A B) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hmap
    rw [← hmap] at hur
    exact (IsUnit.mul_iff.mp hur).1

end IsLocalization

namespace IsLocalizedModule

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] (S : Submonoid R) [IsLocalization S A]
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B (p.under R)]
  {M Mₐ Mᵦ : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Mₐ] [Module R Mₐ]
  [Module A Mₐ] [IsScalarTower R A Mₐ] [AddCommMonoid Mᵦ] [Module R Mᵦ] [Module A Mᵦ]
  [Module B Mᵦ] [IsScalarTower R A Mᵦ] [IsScalarTower A B Mᵦ]

include B in
/-- The module counterpart of `IsLocalization.isLocalization_primeCompl_of_under`: if `Mₐ` is the
localization of `M` at `S` and `Mᵦ` is the localization of `M` at the contraction of a prime `p`
of `S⁻¹R`, then `Mᵦ` is a localization of `Mₐ` at `p`. -/
theorem exists_isLocalizedModule_primeCompl_of_under (f : M →ₗ[R] Mₐ) [IsLocalizedModule S f]
    (g : M →ₗ[R] Mᵦ) [IsLocalizedModule (p.under R).primeCompl g] :
    ∃ h : Mₐ →ₗ[A] Mᵦ, IsLocalizedModule p.primeCompl h := by
  have hle := IsLocalization.le_primeCompl_under S p
  have := IsLocalization.isLocalization_of_submonoid_le A B S (p.under R).primeCompl hle
  have : IsLocalization (Algebra.algebraMapSubmonoid A (p.under R).primeCompl) B := this
  have := IsLocalization.isLocalization_primeCompl_of_under (B := B) S p
  set g₀ := liftOfLE S (p.under R).primeCompl hle f g
  have : IsLocalizedModule (p.under R).primeCompl
      ((g₀.extendScalarsOfIsLocalization S A).restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule _ g₀)
  refine ⟨g₀.extendScalarsOfIsLocalization S A, ?_⟩
  have hbase : IsLocalizedModule (Algebra.algebraMapSubmonoid A (p.under R).primeCompl)
      (g₀.extendScalarsOfIsLocalization S A) :=
    of_restrictScalars _ _
  exact (isLocalizedModule_iff_isBaseChange p.primeCompl B _).mpr
    ((isLocalizedModule_iff_isBaseChange _ B _).mp hbase)

end IsLocalizedModule

namespace AlgebraicGeometry

/-- On an affine open `U ∋ x`, a prime of `Γ(X, U)` contained in the prime naming `x` names a
point of `U` generalizing `x`. -/
theorem IsAffineOpen.exists_primeIdealOf_eq_of_le {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) (q : PrimeSpectrum Γ(X, U))
    (hq : q ≤ hU.primeIdealOf ⟨x, hxU⟩) :
    ∃ (z : X) (hzU : z ∈ U), hU.primeIdealOf ⟨z, hzU⟩ = q ∧ z ⤳ x := by
  have := hU.isOpenImmersion_fromSpec
  have hzU : hU.fromSpec q ∈ U := by
    have hmem : hU.fromSpec q ∈ Set.range hU.fromSpec := Set.mem_range_self _
    rwa [hU.range_fromSpec] at hmem
  refine ⟨_, hzU, hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hzU⟩), ?_⟩
  have h := ((PrimeSpectrum.le_iff_specializes _ _).mp hq).map hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at h

/-- The specialization map of stalks carries the germ at `t` of a section to its germ at `s`. -/
private theorem stalkSpecializes_germ_apply {X : Scheme.{u}} {s t : X} (h : s ⤳ t)
    {V : X.Opens} (ht : t ∈ V) (hs : s ∈ V) (r : Γ(X, V)) :
    (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ V t ht).hom r) =
      (X.presheaf.germ V s hs).hom r := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

/-- **A prime of the local ring at a point names a generalization of that point.** For a
quasi-coherent `𝒪_X`-module `F`, a point `x` of `X` and a prime `p` of `𝒪_{X, x}`, there is a
point `z` generalizing `x` such that `𝒪_{X, z}` is the localization of `𝒪_{X, x}` at `p` and
`F_z` is the localization of `F_x` at `p`. -/
theorem exists_specializes_isLocalization_isLocalizedModule_stalk
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ (z : X) (h : z ⤳ x),
      letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
        (X.presheaf.stalkSpecializes h).hom.toAlgebra
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
      letI : Module (X.presheaf.stalk z) (F.presheaf.stalk z) := Scheme.Modules.moduleStalk F z
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk z) :=
        Module.compHom _ (X.presheaf.stalkSpecializes h).hom
      IsLocalization p.primeCompl (X.presheaf.stalk z) ∧
        ∃ g : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk z,
          IsLocalizedModule p.primeCompl g := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hqp : (Ideal.under Γ(X, U) p).IsPrime := inferInstance
  have hqqx : Ideal.under Γ(X, U) p ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    calc Ideal.under Γ(X, U) p
        ≤ Ideal.under Γ(X, U) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹p.IsPrime›))
      _ = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := IsLocalization.AtPrime.under_maximalIdeal _ _
  obtain ⟨z, hzU, hprime, hzx⟩ :=
    hU.exists_primeIdealOf_eq_of_le hxU ⟨Ideal.under Γ(X, U) p, hqp⟩ hqqx
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    (X.presheaf.stalkSpecializes hzx).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hzU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk z) (Ideal.under Γ(X, U) p) := by
    have h := hU.isLocalization_stalk ⟨z, hzU⟩
    rwa [hprime] at h
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun r => (stalkSpecializes_germ_apply hzx hxU hzU r).symm
  refine ⟨z, hzx, IsLocalization.isLocalization_primeCompl_of_under
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl p, ?_⟩
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
  let : Module (X.presheaf.stalk z) (F.presheaf.stalk z) := Scheme.Modules.moduleStalk F z
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk z) :=
    Module.compHom _ (X.presheaf.stalkSpecializes hzx).hom
  let : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hxU
  let : Module Γ(X, U) (F.presheaf.stalk z) := affineStalkModule F U z hzU
  have : IsLocalizedModule (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (affineGerm F U x hxU) := affineGerm_isLocalized F U hU x hxU
  have : IsLocalizedModule (Ideal.under Γ(X, U) p).primeCompl (affineGerm F U z hzU) := by
    have h := affineGerm_isLocalized F U hU z hzU
    rwa [hprime] at h
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_smul fun r m =>
      congrArg (· • m) (stalkSpecializes_germ_apply hzx hxU hzU r)
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk z) (F.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact IsLocalizedModule.exists_isLocalizedModule_primeCompl_of_under (B := X.presheaf.stalk z)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl p (affineGerm F U x hxU) (affineGerm F U z hzU)

/-- Two points `s ⤳ t` of a scheme are equal as soon as the specialization map
`𝒪_{S, t} → 𝒪_{S, s}` pulls the maximal ideal back to the maximal ideal. -/
theorem Scheme.eq_of_specializes_of_comap_maximalIdeal {S : Scheme.{u}} {s t : S} (h : s ⤳ t)
    (hcomap : Ideal.comap (S.presheaf.stalkSpecializes h).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) =
      IsLocalRing.maximalIdeal (S.presheaf.stalk t)) :
    s = t := by
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
  have hsV : s ∈ V := h.mem_open V.2 htV
  let : Algebra Γ(S, V) (S.presheaf.stalk t) := S.presheaf.algebra_section_stalk ⟨t, htV⟩
  let : Algebra Γ(S, V) (S.presheaf.stalk s) := S.presheaf.algebra_section_stalk ⟨s, hsV⟩
  have : IsLocalization.AtPrime (S.presheaf.stalk t) (hV.primeIdealOf ⟨t, htV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨t, htV⟩
  have : IsLocalization.AtPrime (S.presheaf.stalk s) (hV.primeIdealOf ⟨s, hsV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨s, hsV⟩
  have hunder : Ideal.under Γ(S, V) (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) =
      Ideal.under Γ(S, V) (IsLocalRing.maximalIdeal (S.presheaf.stalk t)) := by
    refine Ideal.ext fun r => ?_
    change (S.presheaf.germ V s hsV).hom r ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) ↔
        (S.presheaf.germ V t htV).hom r ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk t)
    rw [← stalkSpecializes_germ_apply h htV hsV, ← hcomap]
    exact Iff.rfl
  have key : hV.primeIdealOf ⟨s, hsV⟩ = hV.primeIdealOf ⟨t, htV⟩ := by
    refine PrimeSpectrum.ext ?_
    rw [← IsLocalization.AtPrime.under_maximalIdeal (S.presheaf.stalk s)
        (hV.primeIdealOf ⟨s, hsV⟩).asIdeal,
      ← IsLocalization.AtPrime.under_maximalIdeal (S.presheaf.stalk t)
        (hV.primeIdealOf ⟨t, htV⟩).asIdeal]
    exact hunder
  calc s = hV.fromSpec (hV.primeIdealOf ⟨s, hsV⟩) := (hV.fromSpec_primeIdealOf ⟨s, hsV⟩).symm
    _ = hV.fromSpec (hV.primeIdealOf ⟨t, htV⟩) := by rw [key]
    _ = t := hV.fromSpec_primeIdealOf ⟨t, htV⟩

/-- **A prime containing the extended maximal ideal of the base names a point of the same
fibre.** If `𝒪_{X, z}` is the localization of `𝒪_{X, x}` at a prime `p` which contains the ideal
generated by the image of `𝔪_{S, f x}`, then `z` has the same image under `f` as `x` does.

The composite `𝒪_{S, f x} → 𝒪_{X, x} → 𝒪_{X, z}` carries `𝔪_{S, f x}` into `p · 𝒪_{X, z}`, the
maximal ideal of the localization; it factors through the local homomorphism
`𝒪_{S, f z} → 𝒪_{X, z}` by `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`, so the
specialization map `𝒪_{S, f x} → 𝒪_{S, f z}` is local. On an affine open `V ∋ f x`, which also
contains `f z`, the prime of `Γ(S, V)` naming a point is the contraction of the maximal ideal of
its local ring, and the two contractions therefore agree. -/
theorem apply_eq_of_specializes_of_map_maximalIdeal_le {X S : Scheme.{u}} (f : X ⟶ S) {x z : X}
    (h : z ⤳ x) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hloc : letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
        (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization p.primeCompl (X.presheaf.stalk z))
    (hm : Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) ≤ p) :
    f z = f x := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsLocalization p.primeCompl (X.presheaf.stalk z) := hloc
  have hfzx : f z ⤳ f x := f.base.hom.map_specializes h
  have hcomap : Ideal.comap (S.presheaf.stalkSpecializes hfzx).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f z))) =
      IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)) := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      fun a ha => ?_
    have h1 : (f.stalkMap x).hom a ∈ p := hm (Ideal.mem_map_of_mem _ ha)
    have h2 : algebraMap (X.presheaf.stalk x) (X.presheaf.stalk z) ((f.stalkMap x).hom a) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) p _).mpr h1
    have h3 : (f.stalkMap z).hom ((S.presheaf.stalkSpecializes hfzx).hom a) =
        algebraMap (X.presheaf.stalk x) (X.presheaf.stalk z) ((f.stalkMap x).hom a) :=
      congrArg (fun φ : S.presheaf.stalk (f x) ⟶ X.presheaf.stalk z => φ.hom a)
        (Scheme.Hom.stalkSpecializes_stalkMap f z x h)
    rw [← h3] at h2
    exact (IsLocalRing.maximalIdeal_comap (f.stalkMap z).hom) ▸ h2
  exact Scheme.eq_of_specializes_of_comap_maximalIdeal hfzx hcomap

end AlgebraicGeometry

end

end
