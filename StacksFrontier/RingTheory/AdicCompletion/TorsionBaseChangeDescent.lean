module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Images and kernels of power-torsion modules descend along the adic completion

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `B = R^∧_I` its `I`-adic completion. The
extension `R → B` is **not** faithfully flat in general — for `R = ℤ`, `I = (p)` and `B = ℤ_p`
the module `ℤ/q` dies for every prime `q ≠ p`. So the usual descent of a submodule inclusion
along `R → B` is unavailable.

**It is available on modules annihilated by a power of `I`, and nothing beyond flatness is
needed.** On such a module the unit `Z → B ⊗_R Z` is *bijective*: that is
`IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective` read through
`AdicCompletion.quotientMap_bijective`, which says `R ⧸ Iⁿ → B ⧸ IⁿB` is an isomorphism. The
counterexample above is no counterexample here, because `ℤ/q` is not `(p)`-power torsion.

This is what the route of [Stacks, Tag 0EHK] needs over a chart `D(f)` of the punctured
spectrum. There the statement about transition images is proved over
`B = (A_f)^∧_{I A_f}`, where the vertex of the cocone is a finite module, and has to be read
back over `A_f`, where the ideal `I A_f` need not lie in the Jacobson radical — the closed point
having been removed — so that `A_f → B` is flat and not faithfully flat. Every term of the
system of that route is annihilated by a power of `I`
(`Stacks.Algebraization.smul_top_dualizingExtSystem_eq_bot`), hence so is every subquotient of a
term, and the descent below applies to each.

## Main results

* `Stacks.eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion` — the unit is injective on a power
  torsion module.
* `Stacks.range_le_range_of_baseChange_of_isIPowerTorsion`,
  `Stacks.range_eq_range_of_baseChange_of_isIPowerTorsion` — an inclusion, and an equality, of
  images of maps into a power torsion module descends.
* `Stacks.ker_le_ker_of_baseChange_of_isIPowerTorsion` — the kernel inclusion descends; this is
  `Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` with faithful flatness traded for power
  torsion of the target of the second map.
* `Stacks.range_eq_range_of_baseChange_adicCompletion`,
  `Stacks.ker_le_ker_of_baseChange_adicCompletion` — the two at `B = R^∧_I`, where the two
  hypotheses on the extension are discharged.

## Implementation notes

**No flatness of `B` is used in the descent steps themselves, and none is needed**, exactly as
in the implementation notes of
`StacksDraft.RingTheory.Flat.FaithfullyFlat.KernelInclusionDescent`: the argument only pushes an
element forward. For `x` with `u x = 0` the element `1 ⊗ x` lies in `ker (B ⊗ u)` whatever `B`
is; for `x : X₁` the element `1 ⊗ u x` lies in `im (B ⊗ u)`. Flatness enters only inside
`IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective`, where it is a hypothesis of that
lemma, and it is flatness of `B` over `R` and not faithful flatness.

The image descent is run through the quotient `Y ⧸ im v` rather than through a comparison of
`im (B ⊗ v)` with `B ⊗ im v`: the latter identification needs flatness, while the former needs
only that `(B ⊗ mkQ) ∘ (B ⊗ v) = B ⊗ (mkQ ∘ v) = 0`. That is why the hypothesis is power torsion
of `Y` and not of the two sources.

The hypothesis is `IsIPowerTorsion`, while the systems of [Stacks, Tag 0EHK] carry their
annihilation in the shape `Iᵏ • ⊤ = ⊥`. That conversion is *not* restated here: it is
`Stacks.Algebraization.isIPowerTorsion_of_smul_top_eq_bot` at `S = R`, which is stated for an
extension `S` of the base and whose `S = R` case is this one, `Ideal.map` along the identity
being the identity.

All the modules and both rings live in one universe. The modules of the application are the
terms of a system of modules over the chart ring, so they are in its universe; the free
universes of `Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat`, which exist there because the
vertex of the cocone lives over a larger ring, are not available here because
`IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective` quantifies over modules in
`Type (max u v w)`.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
* [Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6), power torsion modules.
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB), flatness of the
  completion.
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-- **The unit of a base change is injective on a power torsion module**, as soon as the
extension is flat and an isomorphism modulo the ideal. If `1 ⊗ x = 0` in `S ⊗_R Z` and `Z` is
`I`-power torsion then `x = 0`.

This is `IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective`, which gives *bijectivity*
of the unit on every `I`-power torsion module, read through `IPowerTorsion.one_tmul_bijective` to
put the ring on the left. Only injectivity is used below. -/
theorem eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion (S : Type u) [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    {Z : Type u} [AddCommGroup Z] [Module R Z] (hZ : IsIPowerTorsion R Z I)
    {x : Z} (h : (1 : S) ⊗ₜ[R] x = 0) : x = 0 := by
  have hb := IPowerTorsion.one_tmul_bijective
    ((IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective R S I hflat).mpr hq Z hZ)
  refine hb.1 ?_
  show (1 : S) ⊗ₜ[R] x = (1 : S) ⊗ₜ[R] (0 : Z)
  rw [tmul_zero]
  exact h

/-- A quotient of an `I`-power torsion module is `I`-power torsion: a representative is
annihilated by a power of `I`, and the quotient map is linear. -/
private theorem isIPowerTorsion_quotient (I : Ideal R) {Y : Type u} [AddCommGroup Y] [Module R Y]
    (N : Submodule R Y) (hY : IsIPowerTorsion R Y I) : IsIPowerTorsion R (Y ⧸ N) I := by
  intro y
  obtain ⟨z, rfl⟩ := N.mkQ_surjective y
  obtain ⟨n, hn, hz⟩ := hY z
  exact ⟨n, hn, fun a ha => by rw [← map_smul, hz a ha, map_zero]⟩

/-- **An inclusion of images descends to a power torsion target.** If the base changes of
`u : X₁ → Y` and `v : X₂ → Y` to `S` satisfy `im (S ⊗ u) ≤ im (S ⊗ v)`, the extension `S` is
flat and an isomorphism modulo `I`, and `Y` is `I`-power torsion, then `im u ≤ im v`.

*Argument.* Let `x : X₁`. Then `1 ⊗ u x = (S ⊗ u)(1 ⊗ x)` lies in `im (S ⊗ v)`, say it is
`(S ⊗ v) ξ`. Apply `S ⊗ mkQ` for `mkQ : Y → Y ⧸ im v`: the right-hand side becomes
`(S ⊗ (mkQ ∘ v)) ξ = 0`, and the left-hand side is `1 ⊗ mkQ (u x)`. The quotient `Y ⧸ im v` is
`I`-power torsion, so `Stacks.eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion` gives
`mkQ (u x) = 0`, that is `u x ∈ im v`. -/
theorem range_le_range_of_baseChange_of_isIPowerTorsion (S : Type u) [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    {X₁ X₂ Y : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y] [Module R Y] (hY : IsIPowerTorsion R Y I)
    (u : X₁ →ₗ[R] Y) (v : X₂ →ₗ[R] Y)
    (h : LinearMap.range (u.baseChange S) ≤ LinearMap.range (v.baseChange S)) :
    LinearMap.range u ≤ LinearMap.range v := by
  rintro - ⟨x, rfl⟩
  obtain ⟨ξ, hξ⟩ : (1 : S) ⊗ₜ[R] u x ∈ LinearMap.range (v.baseChange S) :=
    h ⟨(1 : S) ⊗ₜ[R] x, LinearMap.baseChange_tmul _ _ _⟩
  have hcomp : (LinearMap.range v).mkQ ∘ₗ v = 0 := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.zero_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  have h1 : ((LinearMap.range v).mkQ.baseChange S) ((1 : S) ⊗ₜ[R] u x) =
      (1 : S) ⊗ₜ[R] ((LinearMap.range v).mkQ (u x)) := LinearMap.baseChange_tmul _ _ _
  have hzero : (1 : S) ⊗ₜ[R] ((LinearMap.range v).mkQ (u x)) = 0 := by
    rw [← h1, ← hξ, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hmk := eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion S I hflat hq
    (isIPowerTorsion_quotient I (LinearMap.range v) hY) hzero
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
  exact hmk

/-- **An equality of images descends to a power torsion target.**
`Stacks.range_le_range_of_baseChange_of_isIPowerTorsion` in both directions. This is the shape in
which the route of [Stacks, Tag 0EHK] reads a statement about transition images proved over
`B = (A_f)^∧_I` back over the chart ring `A_f`. -/
theorem range_eq_range_of_baseChange_of_isIPowerTorsion (S : Type u) [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    {X₁ X₂ Y : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y] [Module R Y] (hY : IsIPowerTorsion R Y I)
    (u : X₁ →ₗ[R] Y) (v : X₂ →ₗ[R] Y)
    (h : LinearMap.range (u.baseChange S) = LinearMap.range (v.baseChange S)) :
    LinearMap.range u = LinearMap.range v :=
  le_antisymm
    (range_le_range_of_baseChange_of_isIPowerTorsion S I hflat hq hY u v h.le)
    (range_le_range_of_baseChange_of_isIPowerTorsion S I hflat hq hY v u h.ge)

/-- **An inclusion of kernels descends when the target of the second map is power torsion.**
`Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` with faithful flatness of `S` replaced by
`I`-power torsion of `Z`, which is what the route of [Stacks, Tag 0EHK] has: the hypothesis
`hzero` of `Stacks.exists_range_transitionMap_eq_of_forall_prime` says that `ker (β n)` dies in
a later term of the system, and the later term is annihilated by a power of `I`.

*Argument.* For `x ∈ ker u` the element `1 ⊗ x` lies in `ker (S ⊗ u)`, hence in `ker (S ⊗ v)`,
so `1 ⊗ v x = 0` and `v x = 0` by
`Stacks.eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion`. -/
theorem ker_le_ker_of_baseChange_of_isIPowerTorsion (S : Type u) [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    {X Y Z : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (hZ : IsIPowerTorsion R Z I)
    (u : X →ₗ[R] Y) (v : X →ₗ[R] Z)
    (h : LinearMap.ker (u.baseChange S) ≤ LinearMap.ker (v.baseChange S)) :
    LinearMap.ker u ≤ LinearMap.ker v := by
  intro x hx
  have hmem : (1 : S) ⊗ₜ[R] x ∈ LinearMap.ker (u.baseChange S) := by
    rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hx, tmul_zero]
  have hv : (1 : S) ⊗ₜ[R] v x = 0 := by
    have hker := LinearMap.mem_ker.mp (h hmem)
    rwa [LinearMap.baseChange_tmul] at hker
  exact LinearMap.mem_ker.mpr
    (eq_zero_of_one_tmul_eq_zero_of_isIPowerTorsion S I hflat hq hZ hv)

/-! ### At the adic completion -/

/-- **An equality of images descends along the `I`-adic completion of a Noetherian ring, for a
power torsion target.** `Stacks.range_eq_range_of_baseChange_of_isIPowerTorsion` at
`S = R^∧_I`, whose two hypotheses on the extension are
`AdicCompletion.flat_of_isNoetherian` and `AdicCompletion.quotientMap_bijective`.

**Faithful flatness of `R → R^∧_I` is not needed and is not assumed**; see the module
docstring. -/
theorem range_eq_range_of_baseChange_adicCompletion [IsNoetherianRing R] (I : Ideal R)
    {X₁ X₂ Y : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y] [Module R Y] (hY : IsIPowerTorsion R Y I)
    (u : X₁ →ₗ[R] Y) (v : X₂ →ₗ[R] Y)
    (h : LinearMap.range (u.baseChange (AdicCompletion I R)) =
      LinearMap.range (v.baseChange (AdicCompletion I R))) :
    LinearMap.range u = LinearMap.range v :=
  range_eq_range_of_baseChange_of_isIPowerTorsion (AdicCompletion I R) I inferInstance
    (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) hY u v h

/-- **An inclusion of kernels descends along the `I`-adic completion of a Noetherian ring, when
the target of the second map is power torsion.**
`Stacks.ker_le_ker_of_baseChange_of_isIPowerTorsion` at `S = R^∧_I`. -/
theorem ker_le_ker_of_baseChange_adicCompletion [IsNoetherianRing R] (I : Ideal R)
    {X Y Z : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (hZ : IsIPowerTorsion R Z I)
    (u : X →ₗ[R] Y) (v : X →ₗ[R] Z)
    (h : LinearMap.ker (u.baseChange (AdicCompletion I R)) ≤
      LinearMap.ker (v.baseChange (AdicCompletion I R))) :
    LinearMap.ker u ≤ LinearMap.ker v :=
  ker_le_ker_of_baseChange_of_isIPowerTorsion (AdicCompletion I R) I inferInstance
    (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) hZ u v h

end Stacks

end
