module

public import StacksFrontier.Deformation.Examples.Geometric.LocalizationTowerInjective
public import StacksFrontier.RingTheory.Henselian.Pair.NilpotentFactorization
public import StacksFrontier.RingTheory.Henselian.Pair.Operations

/-!
# Restriction of first-order extensions along a henselization is injective

Let `k → B` be a ring map, let `J ⊆ B` be an ideal and let `(Bʰ, Jʰ)` be the henselization of
the pair `(B, J)`.  For a `Bʰ`-module `N` the restriction map of **Stacks 0GPV**

`Ext¹_{Bʰ}(NL_{Bʰ/k}, N) → Ext¹_B(NL_{B/k}, N)`

is injective.

The argument is the one `Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_isLocalization`
runs for a localization.  A class whose restriction along `B → Bʰ` vanishes is, by
**Stacks 0GPV**, represented by a square-zero extension `0 → N → Y → Bʰ → 0` whose middle ring
receives a `k`-algebra map `σ` from `B` splitting it over `B`.  The surjection `Y → Bʰ` has
square-zero kernel, so `Y` is a henselian pair along the inverse image of `Jʰ`; the universal
property of the henselization therefore extends `σ` to `τ : Bʰ → Y`, and the *uniqueness* half
of that universal property, applied with target `(Bʰ, Jʰ)` itself, says that `Y → Bʰ` composed
with `τ` is the identity — so `τ` is a section.  A section splits the extension, so the class is
zero by `Stacks.Deformation.classEquiv_eq_zero_of_isSection`.

## Main results

* `Stacks.Deformation.henselianPair_comap_of_surjective_of_isNilpotent_ker`: a surjection with
  nilpotent kernel onto a henselian pair is a henselian pair along the inverse image.
* `Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization`: the injectivity.

## Implementation notes

As for the localization, nothing is restricted to the coefficients a deformation problem
produces: `N` is an arbitrary `Bʰ`-module whose `B`-module structure is the restriction of its
`Bʰ`-module structure, and no finiteness, smoothness or Noetherian hypothesis enters.  The
henselization is described by the henselian-pair condition together with its universal property,
as in Stacks 0DZC and Stacks 0DZB, rather than by a chosen model.

`Stacks.Deformation.henselianPair_comap_of_surjective_of_isNilpotent_ker` is the step
`Deformation.exists_algHom_henselization_of_algebraLift` performs inline on the reduction of a
flat algebra lift; it is isolated here because the extension `Y → Bʰ` is not a reduction of a
flat lift.

## References

* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)
-/

@[expose] public noncomputable section

universe w

namespace Stacks.Deformation

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-- **A surjection with nilpotent kernel onto a henselian pair is a henselian pair along the
inverse image.**  The kernel is contained in the nilradical, hence henselian by **Stacks 0ALI**;
the quotient by it is the target, which is henselian along the given ideal; and **Stacks 0DYD**
assembles the two. -/
public theorem henselianPair_comap_of_surjective_of_isNilpotent_ker
    {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S) (hsurj : Function.Surjective f)
    (hnil : IsNilpotent (RingHom.ker f)) (I : Ideal S) (hI : HenselianPair S I) :
    HenselianPair R (I.comap f) := by
  have hkerle : RingHom.ker f ≤ I.comap f := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
    exact I.zero_mem
  have hnilrad : RingHom.ker f ≤ nilradical R := by
    obtain ⟨n, hn⟩ := hnil
    intro x hx
    refine mem_nilradical.mpr ⟨n, ?_⟩
    have hmem : x ^ n ∈ RingHom.ker f ^ n := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem
  set eρ : (R ⧸ RingHom.ker f) ≃+* S := RingHom.quotientKerEquivOfSurjective hsurj with heρdef
  let : Algebra S (R ⧸ RingHom.ker f) := eρ.symm.toRingHom.toAlgebra
  have hsymmsurj : Function.Surjective (algebraMap S (R ⧸ RingHom.ker f)) := eρ.symm.surjective
  have : Algebra.IsIntegral S (R ⧸ RingHom.ker f) :=
    Algebra.isIntegral_of_surjective hsymmsurj
  have hquothens : HenselianPair (R ⧸ RingHom.ker f)
      (I.map (algebraMap S (R ⧸ RingHom.ker f))) :=
    henselianPair_map_of_isIntegral I hI
  have hmapeq : I.map (algebraMap S (R ⧸ RingHom.ker f)) =
      (I.comap f).map (Ideal.Quotient.mk (RingHom.ker f)) := by
    have hcomp : (eρ : (R ⧸ RingHom.ker f) →+* S).comp
        (Ideal.Quotient.mk (RingHom.ker f)) = f :=
      RingHom.ext fun x => rfl
    have h1 : I.comap f = Ideal.comap (Ideal.Quotient.mk (RingHom.ker f))
        (Ideal.comap (eρ : (R ⧸ RingHom.ker f) →+* S) I) := by
      rw [Ideal.comap_comap, hcomp]
    rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap]
      change eρ (eρ.symm x) ∈ I
      rw [eρ.apply_symm_apply]
      exact hx
    · rw [Ideal.mem_comap] at hy
      have hyval : y = algebraMap S (R ⧸ RingHom.ker f) (eρ y) := by
        change y = eρ.symm (eρ y)
        rw [eρ.symm_apply_apply]
      rw [hyval]
      exact Ideal.mem_map_of_mem _ hy
  exact (henselianPair_iff_of_le hkerle).mp
    ⟨henselianPair_of_le_nilradical _ hnilrad, hmapeq ▸ hquothens⟩

/-- **Restriction along a henselization is injective on first-order extension classes.**  For
the henselization `(Bʰ, Jʰ)` of a pair `(B, J)` and a `Bʰ`-module `N`, the restriction map
`Ext¹_{Bʰ}(NL_{Bʰ/k}, N) → Ext¹_B(NL_{B/k}, N)` of **Stacks 0GPV** is injective.

This is the henselization analogue of
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_isLocalization`, and it holds with no
hypothesis on `B`, `J` or `N`. -/
public theorem injective_naiveCotangentExtOneTowerMap_henselization
    (k B : Type w) [CommRing k] [CommRing B] [Algebra k B] (J : Ideal B)
    (Bh : Type w) [CommRing Bh] [Algebra k Bh] [Algebra B Bh] [IsScalarTower k B Bh]
    (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
    (huniv : ∀ (C : Type w) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : B →+* C, J ≤ JC.comap f →
        ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
          J.map (algebraMap B Bh) ≤ JC.comap g)
    (N : Type w) [AddCommGroup N] [Module B N] [Module Bh N] [IsScalarTower B Bh N] :
    Function.Injective (naiveCotangentExtOneTowerMap k B Bh (N := N)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun ζ hζ => ?_
  obtain ⟨Y, hY⟩ := Quotient.exists_rep
    ((squareZeroAlgebraExtensionClassesEquivExtOne k Bh N).symm ζ)
  have hYζ : squareZeroAlgebraExtensionClassesEquivExtOne k Bh N ⟦Y⟧ = ζ := by
    rw [hY]
    exact (squareZeroAlgebraExtensionClassesEquivExtOne k Bh N).apply_symm_apply ζ
  -- restricted along `B → Bʰ` the extension `Y` is split, so it has a section over `B`
  obtain ⟨h, hhB, -⟩ := (exists_compatible_algebraMap_iff k B Bh
      (LinearMap.id : N →ₗ[B] N) (splitAlgebraExtension k B N) Y).mpr (by
        rw [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, map_zero, hYζ, hζ])
  let σ : B →ₐ[k] Y.B' := h.comp (splitInlAlgHom k B N)
  have hσ : ∀ p : B, Y.toB (σ p) = algebraMap B Bh p := by
    intro p
    have hp := hhB (splitInlAlgHom k B N p)
    rwa [toB_splitInlAlgHom] at hp
  -- the middle ring is henselian along the inverse image of `Jʰ`
  set cY : Ideal Y.B' := (J.map (algebraMap B Bh)).comap Y.toB.toRingHom with hcY
  have hnilY : IsNilpotent (RingHom.ker Y.toB.toRingHom) := ⟨2, Y.sq_zero⟩
  have hhensY : HenselianPair Y.B' cY :=
    henselianPair_comap_of_surjective_of_isNilpotent_ker Y.toB.toRingHom Y.surjective hnilY
      (J.map (algebraMap B Bh)) hhens
  -- the section extends across the henselization
  have hJcY : J ≤ cY.comap (σ : B →+* Y.B') := by
    intro x hx
    rw [Ideal.mem_comap, hcY, Ideal.mem_comap]
    change Y.toB (σ x) ∈ J.map (algebraMap B Bh)
    rw [hσ x]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨τ, ⟨hτ1, hτ2⟩, -⟩ :=
    huniv Y.B' inferInstance cY hhensY (σ : B →+* Y.B') hJcY
  have hτ : ∀ p : B, τ (algebraMap B Bh p) = σ p := fun p => RingHom.congr_fun hτ1 p
  -- it is a section, by the uniqueness half of the universal property
  have hsec : ∀ c : Bh, Y.toB (τ c) = c := by
    obtain ⟨g₀, -, huq⟩ := huniv Bh inferInstance (J.map (algebraMap B Bh)) hhens
      (algebraMap B Bh) (fun x hx => Ideal.mem_map_of_mem _ hx)
    have hcomp : Y.toB.toRingHom.comp τ = RingHom.id Bh := by
      refine (huq (Y.toB.toRingHom.comp τ) ⟨RingHom.ext fun p => ?_, fun x hx => ?_⟩).trans
        (huq (RingHom.id Bh) ⟨RingHom.ext fun p => rfl, fun x hx => hx⟩).symm
      · change Y.toB (τ (algebraMap B Bh p)) = algebraMap B Bh p
        rw [hτ, hσ]
      · rw [Ideal.mem_comap]
        change Y.toB (τ x) ∈ J.map (algebraMap B Bh)
        have hx' : τ x ∈ cY := hτ2 hx
        rwa [hcY, Ideal.mem_comap] at hx'
    intro c
    exact RingHom.congr_fun hcomp c
  let τA : Bh →ₐ[k] Y.B' :=
    { τ with
      commutes' := fun a => by
        change τ (algebraMap k Bh a) = algebraMap k Y.B' a
        rw [IsScalarTower.algebraMap_apply k B Bh a, hτ]
        exact σ.commutes a }
  rw [← hYζ]
  exact classEquiv_eq_zero_of_isSection k Bh N Y τA hsec

end Stacks.Deformation

end
