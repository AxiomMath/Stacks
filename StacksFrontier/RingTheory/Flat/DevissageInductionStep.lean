module

public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed fibre of a dévissage stage algebra after an arbitrary base change

The induction step of Stacks Tag 05PG applies Stacks Tag 05I3 not over the base `A` but over an
arbitrary local `A`-algebra `R`, with the stage algebra `B` of a complete dévissage replaced by
`B ⊗[A] R`. Stacks Tag 05I3 asks for two things about that algebra which are not formal: that
the extension of the maximal ideal of `R` to it is prime — the generic point of its closed fibre
— and that the stage map stays an isomorphism over the residue field there.

`StacksFrontier.RingTheory.Flat.DevissageQuotientBase` supplies both for a *surjection* `A → A ⧸ J`
of the base, which is the base change the induction step performs after the fact; its module
docstring sketches, but does not prove, the case of a general ring map. This file proves the
first of the two in that generality, for the base change of the stage algebra along an arbitrary
`A`-algebra `R`.

The argument is the one the source takes for granted: `Spec(B ⊗[A] R) → Spec R` is the base
change of `Spec B → Spec A` along `Spec R → Spec A`, and geometric integrality of a morphism of
schemes is stable under base change (`AlgebraicGeometry.GeometricallyIntegral` is a `universally`
property). So the fibres of `Spec(B ⊗[A] R) → Spec R` are again geometrically integral, and
`Algebra.closedFiberIdeal_isPrime` applies verbatim over `R`.

## Main definitions

* `Stacks.Flatness.tensorCommRight`: the commutativity of the tensor product, as an equivalence
  of modules over the right factor. Mathlib's base-change statements are all for `R ⊗[A] B` with
  its standard left algebra structure, while the flatness condition of Stacks Tag 05ML presents
  the base change as `B ⊗[A] R` over `R`; this is the bridge.
* `Stacks.Flatness.closedFiberResidueFieldMap`: the extension of residue fields at the generic
  points of the two closed fibres, which the contraction below produces.

## Main results

* `Stacks.Flatness.flat_tensorProduct_right` and
  `Stacks.Flatness.projective_tensorProduct_right`: flatness and projectivity of a dévissage
  stage algebra over the base survive a base change of the base, in that orientation. These are
  two of the three hypotheses of `Module.flat_localizedModule_tfae_of_projective'` over the new
  base.

* `Stacks.Flatness.bijective_baseChange_baseChange_iff` and
  `Stacks.Flatness.bijective_baseChange_of_tower`: base changing in one step or in two gives the
  same bijectivity, so the fibre condition of a dévissage stage survives an extension of the
  fibre field.
* `Stacks.Flatness.geometricallyIntegral_tensorProduct_right`: geometric integrality of
  `Spec B → Spec A` passes to `Spec (B ⊗[A] R) → Spec R`.
* `Stacks.Flatness.closedFiberIdeal_tensorProduct_isPrime`: consequently the extension of the
  maximal ideal of a local `A`-algebra `R` to `B ⊗[A] R` is prime.
* `Stacks.Flatness.isGeometricallyIntegral_fiber_tensorProduct_right`: the fibre of
  `B ⊗[A] R` over a prime of `R` is a geometrically integral algebra over its residue field,
  which is the hypothesis of Stacks Tag 05FT and so supplies the projectivity Stacks Tag 05I3
  runs on.
* `Stacks.Flatness.injective_tmul_one`: a module over a field injects into its base change along
  a nonzero extension, the tensor product being taken over a ring mapping onto the field.
* `Stacks.Flatness.comap_closedFiberIdeal_tensorProduct`: along `b ↦ b ⊗ₜ 1` the generic point
  of the closed fibre of `B ⊗[A] R` over `R` contracts to the generic point of the closed fibre
  of `B` over `A`. This is what produces the extension of residue fields along which the fibre
  condition of a dévissage stage transports, and unlike the three statements above it needs no
  hypothesis on the fibres of `B`.

## Implementation notes

The `R`-algebra structure on `B ⊗[A] R` is `Algebra.TensorProduct.rightAlgebra`, introduced by a
`letI` in the statements exactly as `Module.IsFlatAtPrimesOver` introduces it; its structure map
is `Algebra.TensorProduct.includeRight`, which is what makes the square of
`CommRingCat.isPushout_tensorProduct` the one to apply `Spec` to.

Everything is in a single universe. That is not a convenience: `Algebra.closedFiberIdeal_isPrime`
and `AlgebraicGeometry.GeometricallyIntegral` fix the base and the algebra in one universe, so
the statements below cannot be read with `B` in the universe of the dévissage and `R` in a larger
one. The consequence for Stacks Tag 05PG is recorded in the module docstring of
`StacksFrontier.RingTheory.Flat.FlatteningQuotientBridge`.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

open scoped TensorProduct

universe u v w

namespace Stacks.Flatness

/-- **Base changing in one step or in two gives the same bijectivity.** For an `A`-algebra `A'`
and an `A'`-algebra `L`, a map `α` of `A`-modules is bijective after tensoring with `L` over `A`
exactly when its base change to `A'` is bijective after tensoring with `L` over `A'`.

The two composites differ by the canonical identifications of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which `LinearMap.baseChange_baseChange`
records. -/
theorem bijective_baseChange_baseChange_iff {A : Type u} [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] (L : Type u) [CommRing L] [Algebra A L] [Algebra A' L] [IsScalarTower A A' L]
    {P : Type v} [AddCommGroup P] [Module A P] {N : Type w} [AddCommGroup N] [Module A N]
    (α : P →ₗ[A] N) :
    Function.Bijective ((α.baseChange A').baseChange L) ↔
      Function.Bijective (α.baseChange L) := by
  rw [LinearMap.baseChange_baseChange (A := A') (B := L) α]
  change Function.Bijective
    (⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L N).symm ∘
      ⇑(α.baseChange L) ∘
        ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L P)) ↔ _
  rw [EquivLike.comp_bijective _ (TensorProduct.AlgebraTensorModule.cancelBaseChange
      A A' L L N).symm,
    EquivLike.bijective_comp (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L P)]

/-- **The fibre condition of a dévissage stage transports along an extension of the fibre
field.** If `α` becomes bijective after base change to an `A`-algebra `A'`, it stays bijective
after base change to any `A'`-algebra `L`.

In the source `A'` is the residue field `κ(𝔪_A B)` of the generic point of the closed fibre of a
dévissage stage algebra and `L` is the residue field `κ(𝔪_R (B ⊗[A] R))` of the generic point of
the closed fibre after a base change of the base, which is an extension of it by
`Stacks.Flatness.comap_closedFiberIdeal_tensorProduct`. So this is the half of the
general-base-change fibre data that `Module.flat_localizedModule_tfae_of_projective'` consumes as
`halpha`. -/
theorem bijective_baseChange_of_tower {A : Type u} [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] (L : Type u) [CommRing L] [Algebra A L] [Algebra A' L] [IsScalarTower A A' L]
    {P : Type v} [AddCommGroup P] [Module A P] {N : Type w} [AddCommGroup N] [Module A N]
    (α : P →ₗ[A] N) (h : Function.Bijective (α.baseChange A')) :
    Function.Bijective (α.baseChange L) := by
  refine (bijective_baseChange_baseChange_iff A' L α).mp ?_
  have h' : Function.Bijective
      (LinearMap.lTensor L (LinearEquiv.ofBijective (α.baseChange A') h).toLinearMap) :=
    (LinearEquiv.lTensor L (LinearEquiv.ofBijective (α.baseChange A') h)).bijective
  rwa [LinearMap.baseChange_eq_lTensor]

/-- **The commutativity of the tensor product, as an equivalence of modules over the right
factor.** For the `R`-algebra structure `Algebra.TensorProduct.rightAlgebra` on `B ⊗[A] R`, the
swap `b ⊗ₜ s ↦ s ⊗ₜ b` is `R`-linear: on the left the `R`-action is multiplication in the right
factor, on the right it is multiplication in the left factor.

Every base-change statement in Mathlib — `Module.Flat.baseChange`,
`Module.Projective.tensorProduct` — is stated for `R ⊗[A] B` with its standard left algebra
structure, while the flatness condition of Stacks Tag 05ML presents the base change of a
dévissage stage algebra as `B ⊗[A] R` over `R`. This is the bridge between the two
orientations. -/
def tensorCommRight (A B R : Type u) [CommRing A] [CommRing B] [CommRing R] [Algebra A B]
    [Algebra A R] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (B ⊗[A] R) ≃ₗ[R] R ⊗[A] B :=
  letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  AddEquiv.toLinearEquiv (TensorProduct.comm A B R).toAddEquiv fun r x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul b s =>
        change (TensorProduct.comm A B R) ((1 ⊗ₜ[A] r) * (b ⊗ₜ[A] s)) =
          r • (TensorProduct.comm A B R) (b ⊗ₜ[A] s)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- **Flatness of a dévissage stage algebra survives a base change of the base**, in the
orientation the flatness condition of Stacks Tag 05ML uses. `Module.Flat.baseChange` gives
flatness of `R ⊗[A] B` over `R`, and `Stacks.Flatness.tensorCommRight` carries it to
`B ⊗[A] R`. -/
theorem flat_tensorProduct_right (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.Flat A B] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    Module.Flat R (B ⊗[A] R) := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact Module.Flat.of_linearEquiv (tensorCommRight A B R)

/-- **Projectivity of a dévissage stage algebra survives a base change of the base**, in the
orientation the flatness condition of Stacks Tag 05ML uses. `Module.Projective.tensorProduct`
gives projectivity of `R ⊗[A] B` over `R`, and `Stacks.Flatness.tensorCommRight` carries it to
`B ⊗[A] R`.

Together with `Stacks.Flatness.flat_tensorProduct_right` and
`Stacks.Flatness.closedFiberIdeal_tensorProduct_isPrime` these are the three hypotheses of
`Module.flat_localizedModule_tfae_of_projective'` over the new base. The projectivity of `B` over
`A` that this consumes is `Module.CompleteDevissage.projective_lowerAlgebra`, Stacks Tag 05FT. -/
@[ega "IV 7.5.5" "partial"]
theorem projective_tensorProduct_right (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.Projective A B] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    Module.Projective R (B ⊗[A] R) := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact Module.Projective.of_equiv (tensorCommRight A B R).symm

/-- **Geometric integrality of the fibres is stable under base change of the base.** If the
fibres of `Spec B → Spec A` are geometrically integral then so are those of
`Spec (B ⊗[A] R) → Spec R`, for any `A`-algebra `R`.

`Spec (B ⊗[A] R)` is the fibre product of `Spec B` and `Spec R` over `Spec A`, by
`CommRingCat.isPushout_tensorProduct` and
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`, and
`AlgebraicGeometry.GeometricallyIntegral` is stable under base change. -/
theorem geometricallyIntegral_tensorProduct_right (A B R : Type u) [CommRing A] [CommRing B]
    [CommRing R] [Algebra A B] [Algebra A R]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    GeometricallyIntegral (Spec.map (ofHom (algebraMap R (B ⊗[A] R)))) := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @GeometricallyIntegral)
    (AlgebraicGeometry.isPullback_SpecMap_of_isPushout (ofHom (algebraMap A B))
      (ofHom (algebraMap A R))
      (ofHom (S := CommRingCat.of (B ⊗[A] R)) Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := CommRingCat.of (B ⊗[A] R))
        Algebra.TensorProduct.includeRight.toRingHom)
      (CommRingCat.isPushout_tensorProduct A B R))
    ‹_›

/-- **The generic point of the closed fibre survives an arbitrary base change of the base.** Let
`A` be a ring, let `B` be an `A`-algebra whose fibres are geometrically integral and let `R` be a
local `A`-algebra. Then the extension of the maximal ideal of `R` to `B ⊗[A] R` is prime.

This is `Algebra.closedFiberIdeal_isPrime` over `R`, its hypothesis supplied by
`Stacks.Flatness.geometricallyIntegral_tensorProduct_right`. It is the general-base-change form
of `Stacks.Flatness.isPrime_map_algebraMap_of_surjective`, and it is what lets Stacks Tag 05I3 be
applied to a dévissage stage over a varying local `A`-algebra. -/
theorem closedFiberIdeal_tensorProduct_isPrime (A B R : Type u) [CommRing A] [CommRing B]
    [CommRing R] [IsLocalRing R] [Algebra A B] [Algebra A R]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (Algebra.closedFiberIdeal R (B ⊗[A] R)).IsPrime := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  have : GeometricallyIntegral (Spec.map (ofHom (algebraMap R (B ⊗[A] R)))) :=
    geometricallyIntegral_tensorProduct_right A B R
  exact Algebra.closedFiberIdeal_isPrime R (B ⊗[A] R)

/-- **The fibres of the base-changed stage algebra are geometrically integral algebras.** For a
prime `p` of `R`, the fibre of `B ⊗[A] R` at `p` is geometrically integral over the residue field
of `p`.

This is `Algebra.isGeometricallyIntegral_tensorProduct_residueField` over `R`. It is the
hypothesis of Stacks Tag 05FT, so it discharges the `Module.Projective R (B ⊗[A] R)` hypothesis
of `Module.flat_localizedModule_tfae_of_projective'` over the new base. -/
theorem isGeometricallyIntegral_fiber_tensorProduct_right (A B R : Type u) [CommRing A]
    [CommRing B] [CommRing R] [Algebra A B] [Algebra A R]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))] (p : Ideal R) [p.IsPrime] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra p.ResidueField ((B ⊗[A] R) ⊗[R] p.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyIntegral p.ResidueField ((B ⊗[A] R) ⊗[R] p.ResidueField) := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  have : GeometricallyIntegral (Spec.map (ofHom (algebraMap R (B ⊗[A] R)))) :=
    geometricallyIntegral_tensorProduct_right A B R
  exact Algebra.isGeometricallyIntegral_tensorProduct_residueField R (B ⊗[A] R) p

/-- **A module over a field injects into its base change along a nonzero extension**, the tensor
product being taken over a ring mapping onto the field.

Let `k` be a field, let `K` be a nontrivial `k`-algebra and let `M` be a `k`-module; read both
over a ring `A` mapping to `k`. Then `m ↦ m ⊗ₜ[A] 1` is injective. A `k`-linear retraction
`φ : K → k` of the structure map exists because `k` is a field, and `m ⊗ₜ x ↦ φ x • m` is an
`A`-bilinear left inverse.

The tensor product is over `A` and not over `k` because that is the form in which the base change
of a dévissage stage algebra presents it: `B ⊗[A] R` is a tensor product over `A`, and its closed
fibre is read through the quotients of `A` and of `R` by their maximal ideals. -/
theorem injective_tmul_one {A : Type u} [CommRing A] {k : Type u} [Field k] [Algebra A k]
    {K : Type u} [CommRing K] [Nontrivial K] [Algebra A K] [Algebra k K] [IsScalarTower A k K]
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower A k M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[A] (1 : K)) := by
  obtain ⟨φ, hφ⟩ := (Algebra.linearMap k K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  have hφ1 : φ (1 : K) = 1 := by
    have h := congrArg (fun f : k →ₗ[k] k ↦ f (1 : k)) hφ
    simpa using h
  let bil : M →ₗ[A] K →ₗ[A] M :=
    LinearMap.mk₂ A (fun m x ↦ φ x • m)
      (fun m₁ m₂ x ↦ by simp [smul_add])
      (fun a m x ↦ by
        rw [← IsScalarTower.algebraMap_smul k a m, smul_comm, IsScalarTower.algebraMap_smul])
      (fun m x₁ x₂ ↦ by simp [add_smul])
      (fun a m x ↦ by
        rw [← IsScalarTower.algebraMap_smul k a x, map_smul, smul_assoc,
          IsScalarTower.algebraMap_smul])
  intro m m' h
  have h' := congrArg (TensorProduct.lift bil) h
  simp only [TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hφ1, one_smul] at h'
  exact h'

/-- **The generic point of the closed fibre of a base change contracts to the generic point of
the closed fibre.** Let `A → R` be a local homomorphism of local rings and let `B` be an
`A`-algebra. The extension of the maximal ideal of `R` to `B ⊗[A] R` contracts along
`b ↦ b ⊗ₜ 1` to the extension of the maximal ideal of `A` to `B`.

One containment is the computation `algebraMap A B a ⊗ₜ 1 = 1 ⊗ₜ algebraMap A R a` together with
locality of `A → R`. The other is the observation that `B ⊗[A] R → (B ⧸ 𝔪_A B) ⊗[A] (R ⧸ 𝔪_R)`
kills the extension of `𝔪_R`, so an element `b` whose image `b ⊗ₜ 1` lies in it has `b̄ ⊗ₜ 1 = 0`,
and `Stacks.Flatness.injective_tmul_one` — the residue field of `R` being a nonzero vector space
over the residue field of `A` — forces `b̄ = 0`.

This is the general-base-change form of
`Stacks.Flatness.map_algebraMap_eq_comap_of_surjective`, and it is what produces the extension of
residue fields `κ(𝔪_A B) → κ(𝔪_R (B ⊗[A] R))` along which the fibre condition of a dévissage
stage transports. No hypothesis on the fibres of `B` is needed. -/
theorem comap_closedFiberIdeal_tensorProduct (A B R : Type u) [CommRing A] [CommRing B]
    [CommRing R] [IsLocalRing A] [IsLocalRing R] [Algebra A B] [Algebra A R]
    [IsLocalHom (algebraMap A R)] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (Algebra.closedFiberIdeal R (B ⊗[A] R)).comap
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] R) =
      Algebra.closedFiberIdeal A B := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  have : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  have : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hle : IsLocalRing.maximalIdeal A ≤
      (IsLocalRing.maximalIdeal R).comap (algebraMap A R) := fun a ha ↦ by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal]
    exact fun h ↦ (IsLocalRing.mem_maximalIdeal a).mp ha (IsLocalHom.map_nonunit a h)
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  have : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A) (R ⧸ IsLocalRing.maximalIdeal R) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Algebra.closedFiberIdeal A B) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
      (B ⧸ Algebra.closedFiberIdeal A B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set Ψ : (B ⊗[A] R) →ₐ[A]
      (B ⧸ Algebra.closedFiberIdeal A B) ⊗[A] (R ⧸ IsLocalRing.maximalIdeal R) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A (Algebra.closedFiberIdeal A B))
      (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal R)) with hΨ
  have hker : Algebra.closedFiberIdeal R (B ⊗[A] R) ≤ RingHom.ker Ψ.toRingHom := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ψ ((1 : B) ⊗ₜ[A] x) = 0
    rw [hΨ, Algebra.TensorProduct.map_tmul,
      show (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal R)) x = 0 from
        (Ideal.Quotient.eq_zero_iff_mem).mpr hx, TensorProduct.tmul_zero]
  refine le_antisymm (fun b hb ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
  · have h0 : Ψ (b ⊗ₜ[A] (1 : R)) = 0 := RingHom.mem_ker.mp (hker hb)
    rw [hΨ, Algebra.TensorProduct.map_tmul] at h0
    have h1 : (Ideal.Quotient.mk (Algebra.closedFiberIdeal A B) b) ⊗ₜ[A]
        (1 : R ⧸ IsLocalRing.maximalIdeal R) =
          (0 : B ⧸ Algebra.closedFiberIdeal A B) ⊗ₜ[A]
            (1 : R ⧸ IsLocalRing.maximalIdeal R) := by
      simpa using h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp
      (injective_tmul_one (A := A) (k := A ⧸ IsLocalRing.maximalIdeal A)
        (K := R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ Algebra.closedFiberIdeal A B) h1)
  · have hx : (algebraMap A B a) ⊗ₜ[A] (1 : R) =
        algebraMap R (B ⊗[A] R) (algebraMap A R a) := by
      change (algebraMap A B a) ⊗ₜ[A] (1 : R) = (1 : B) ⊗ₜ[A] (algebraMap A R a)
      rw [Algebra.algebraMap_eq_smul_one (R := A) (A := B),
        Algebra.algebraMap_eq_smul_one (R := A) (A := R)]
      exact TensorProduct.smul_tmul _ _ _
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change (algebraMap A B a) ⊗ₜ[A] (1 : R) ∈ Algebra.closedFiberIdeal R (B ⊗[A] R)
    rw [hx]
    exact Ideal.mem_map_of_mem _ (hle ha)

/-- **The extension of residue fields at the generic points of the closed fibres.** The
contraction of `Stacks.Flatness.comap_closedFiberIdeal_tensorProduct` makes the residue field of
the generic point of the closed fibre of `B ⊗[A] R` over `R` an extension of the residue field of
the generic point of the closed fibre of `B` over `A`.

Composed with `Stacks.Flatness.bijective_baseChange_of_tower` this transports the fibre condition
`halpha` of a dévissage stage from the base `A` to an arbitrary local `A`-algebra `R`, which is
the second of the two things `Module.flat_localizedModule_tfae_of_projective'` needs over the new
base; `Stacks.Flatness.closedFiberIdeal_tensorProduct_isPrime` is the first. -/
noncomputable def closedFiberResidueFieldMap (A B R : Type u) [CommRing A] [CommRing B]
    [CommRing R] [IsLocalRing A] [IsLocalRing R] [Algebra A B] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [(Algebra.closedFiberIdeal A B).IsPrime]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    haveI : (Algebra.closedFiberIdeal R (B ⊗[A] R)).IsPrime :=
      closedFiberIdeal_tensorProduct_isPrime A B R
    (Algebra.closedFiberIdeal A B).ResidueField →+*
      (Algebra.closedFiberIdeal R (B ⊗[A] R)).ResidueField :=
  letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  haveI : (Algebra.closedFiberIdeal R (B ⊗[A] R)).IsPrime :=
    closedFiberIdeal_tensorProduct_isPrime A B R
  Ideal.ResidueField.map (Algebra.closedFiberIdeal A B)
    (Algebra.closedFiberIdeal R (B ⊗[A] R))
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] R)
    (comap_closedFiberIdeal_tensorProduct A B R).symm

end Stacks.Flatness

end
