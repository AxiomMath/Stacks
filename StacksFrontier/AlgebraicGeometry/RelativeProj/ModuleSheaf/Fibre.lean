module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Degreewise
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Fibre

/-!
# Module fibres of a degreewise localization of graded modules

Let `φ : 𝒜 →+*ᵍ ℬ` be a degreewise localization away from a degree-zero element `g`
(`Stacks.GradedLocalization.IsAwayDegreewise`), and let `f : M → N` be a `φ`-semilinear map which
is, in each degree, the localization away from `g`
(`Stacks.GradedLocalization.IsAwayDegreewiseModule`). This file proves that the comparison of
localized modules at a prime `J` of `B` and its preimage `I = φ⁻¹ J` is a bijection, and deduces
the same for the comparison of module fibres `Stacks.ProjModuleComparison.fibreMap` at every
point of `Proj ℬ`.

Geometrically: inverting `g` does not change the fibre of a module at a point where `g` is
invertible, and every point of `Proj ℬ` is such a point. This is the fibrewise input to the
comparison of the sheaves attached to graded modules across `AlgebraicGeometry.Proj.map φ`, and
it is the module companion of
`Stacks.GradedLocalization.IsAwayDegreewise.bijective_localRingHom`.

## Main definitions

* `Stacks.ProjModuleComparison.localizedDenomMap` and
  `Stacks.ProjModuleComparison.localizedModuleMap`: the comparison of localized modules at a
  prime and its preimage, indexed by the two ideals and an equation between them rather than by a
  point of `Proj ℬ`.

## Main results

* `Stacks.ProjModuleComparison.bijective_localizedModuleMap`: that comparison is bijective.
* `Stacks.ProjModuleComparison.bijective_fibreMap`: the comparison of module fibres is bijective.

## Implementation notes

The comparison is indexed by the pair of ideals, with the equation `I = φ⁻¹ J` as an argument, as
`Localization.localRingHom` is in the ring case. That is what makes the statements usable at a
point of `Proj 𝒜` reached through an *equation* of points rather than definitionally: a statement
about `Stacks.ProjModuleComparison.fibreMap` at a point `y` lives in a type depending on the
point below `y`, so relating it to a fibre at a point known only to be equal to that one would
need a transport. The point version is recovered by
`Stacks.ProjModuleComparison.fibreMap_eq_localizedModuleMap`, which holds definitionally.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

variable {A B M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  (φ : 𝒜 →+*ᵍ ℬ) (f : M →ₛₗ[φ.toRingHom] N) {g : A}

/-! ### The comparison of localized modules -/

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- A denominator stays a denominator: an element of `A` avoiding `I = φ⁻¹ J` has image avoiding
`J`. -/
public theorem map_notMem_of_comap_eq {I : Ideal A} {J : Ideal B}
    (hIJ : I = J.comap φ.toRingHom) {s : A} (hs : s ∉ I) : φ s ∉ J := by
  subst hIJ
  exact hs

variable (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]

/-- The multiplicative map on denominators: an element of `A` avoiding `I = φ⁻¹ J` goes to its
image in `B`, which avoids `J`. -/
public def localizedDenomMap (hIJ : I = J.comap φ.toRingHom) : I.primeCompl →* J.primeCompl where
  toFun s := ⟨φ s, map_notMem_of_comap_eq φ hIJ s.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' _ _ := Subtype.ext (map_mul φ _ _)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The underlying element of a transported denominator is the image of the denominator. -/
@[simp] public theorem coe_localizedDenomMap (hIJ : I = J.comap φ.toRingHom)
    (s : I.primeCompl) : (localizedDenomMap φ I J hIJ s : B) = φ s := rfl

/-- **The comparison of localized modules** at a prime `J` of `B` and its preimage `I`: the
fraction `m / s` goes to `f m / φ s`. -/
public def localizedModuleMap (hIJ : I = J.comap φ.toRingHom)
    (z : LocalizedModule I.primeCompl M) : LocalizedModule J.primeCompl N :=
  LocalizedModule.liftOn z
    (fun p => LocalizedModule.mk (f p.1) (localizedDenomMap φ I J hIJ p.2)) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      refine LocalizedModule.mk_eq.mpr ⟨localizedDenomMap φ I J hIJ u, ?_⟩
      simpa only [Submonoid.smul_def, coe_localizedDenomMap, map_smulₛₗ,
        GradedRingHom.coe_toRingHom] using congrArg f hu)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The comparison on a fraction: apply `f` to the numerator and `φ` to the denominator. -/
@[simp] public theorem localizedModuleMap_mk (hIJ : I = J.comap φ.toRingHom) (m : M)
    (s : I.primeCompl) :
    localizedModuleMap φ f I J hIJ (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) (localizedDenomMap φ I J hIJ s) :=
  LocalizedModule.liftOn_mk _ m s

omit [AddSubgroupClass σ A] [AddSubgroupClass μ M] [GradedRing 𝒜] [DirectSum.Decomposition 𝒨] in
/-- **The comparison of localized modules is surjective.** -/
public theorem surjective_localizedModuleMap (h : IsAwayDegreewise φ g)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (hIJ : I = J.comap φ.toRingHom) :
    Function.Surjective (localizedModuleMap φ f I J hIJ) := by
  intro z
  induction z using LocalizedModule.induction_on with
  | h b t =>
    obtain ⟨k, a, hak⟩ := hmod.exists_pow_smul_eq_map b
    obtain ⟨m, s, hms⟩ := h.exists_pow_mul_eq_map (t : B)
    have hs : s ∈ I.primeCompl := h.mem_primeCompl_of_map_eq I J hIJ t.2 hms
    have hg : g ∈ I.primeCompl := h.mem_primeCompl I J hIJ
    have hfa : f (g ^ m • a) = φ g ^ m • (φ g ^ k • b) := by
      rw [map_smulₛₗ, hak]
      simp only [GradedRingHom.coe_toRingHom, map_pow]
    refine ⟨LocalizedModule.mk (g ^ m • a)
      ⟨s * g ^ k, Submonoid.mul_mem _ hs (Submonoid.pow_mem _ hg k)⟩, ?_⟩
    rw [localizedModuleMap_mk]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, coe_localizedDenomMap, map_mul, map_pow, hfa,
      smul_smul, hms]
    refine congrArg (fun c : B => c • b) ?_
    ring

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The comparison of localized modules is injective.** -/
public theorem injective_localizedModuleMap (h : IsAwayDegreewise φ g)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (hIJ : I = J.comap φ.toRingHom) :
    Function.Injective (localizedModuleMap φ f I J hIJ) := by
  have key : ∀ (a a' : M) (p p' : I.primeCompl),
      localizedModuleMap φ f I J hIJ (LocalizedModule.mk a p) =
        localizedModuleMap φ f I J hIJ (LocalizedModule.mk a' p') →
      (LocalizedModule.mk a p : LocalizedModule I.primeCompl M) = LocalizedModule.mk a' p' := by
    intro a a' p p' hzw
    rw [localizedModuleMap_mk, localizedModuleMap_mk, LocalizedModule.mk_eq] at hzw
    obtain ⟨c, hc⟩ := hzw
    obtain ⟨m, s, hms⟩ := h.exists_pow_mul_eq_map (c : B)
    have hs : s ∈ I.primeCompl := h.mem_primeCompl_of_map_eq I J hIJ c.2 hms
    have hg : g ∈ I.primeCompl := h.mem_primeCompl I J hIJ
    have hc' : (c : B) • (φ (p' : A) • f a) = (c : B) • (φ (p : A) • f a') := by
      simpa only [Submonoid.smul_def, coe_localizedDenomMap,
        GradedRingHom.coe_toRingHom] using hc
    have hexp : f (s • ((p' : A) • a - (p : A) • a')) =
        φ g ^ m • ((c : B) • (φ (p' : A) • f a) - (c : B) • (φ (p : A) • f a')) := by
      simp only [map_smulₛₗ, map_sub, GradedRingHom.coe_toRingHom, map_mul, hms, smul_sub,
        smul_smul, mul_assoc]
    rw [hc', sub_self, smul_zero] at hexp
    obtain ⟨j, hj⟩ := hmod.exists_pow_smul_eq_zero hexp
    refine LocalizedModule.mk_eq.mpr
      ⟨⟨g ^ j * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ hg j) hs⟩, ?_⟩
    have hj' : (g ^ j * s) • ((p' : A) • a) - (g ^ j * s) • ((p : A) • a') = 0 := by
      rw [← smul_sub, mul_smul]
      exact hj
    simpa only [Submonoid.smul_def] using sub_eq_zero.mp hj'
  intro z w
  induction z using LocalizedModule.induction_on with
  | h a p =>
    induction w using LocalizedModule.induction_on with
    | h a' p' => exact key a a' p p'

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The localized modules of a degreewise localization agree with those of its source.** For a
prime `J` of `ℬ` and `I = φ⁻¹ J`, the comparison `M_I ⟶ N_J` is bijective. -/
public theorem bijective_localizedModuleMap (h : IsAwayDegreewise φ g)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (hIJ : I = J.comap φ.toRingHom) :
    Function.Bijective (localizedModuleMap φ f I J hIJ) :=
  ⟨injective_localizedModuleMap φ f I J h hmod hIJ,
    surjective_localizedModuleMap φ f I J h hmod hIJ⟩

/-! ### The comparison of module fibres -/

/-- The comparison of module fibres at a point of `Proj ℬ` is the comparison of localized modules
at the homogeneous prime there and the homogeneous prime below it. -/
public theorem fibreMap_eq_localizedModuleMap (hφ : ℬ₊ ≤ 𝒜₊.map φ) (y : ProjectiveSpectrum ℬ)
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ f y z =
      localizedModuleMap φ f (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal
        y.asHomogeneousIdeal.toIdeal (comapFun_toIdeal φ hφ y) z := rfl

/-- **The module fibres of a degreewise localization agree with those of its source.** At every
point of `Proj ℬ`, the comparison of the fibre of `M` at the homogeneous prime below it with the
fibre of `N` at it is bijective. -/
public theorem bijective_fibreMap (hφ : ℬ₊ ≤ 𝒜₊.map φ) (h : IsAwayDegreewise φ g)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (y : ProjectiveSpectrum ℬ) :
    Function.Bijective (fibreMap φ hφ f y) :=
  bijective_localizedModuleMap φ f _ y.asHomogeneousIdeal.toIdeal h hmod
    (comapFun_toIdeal φ hφ y)

end Stacks.ProjModuleComparison

end
