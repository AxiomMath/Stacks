module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection

/-!
# Clause (2) of Tag 02NC: the comparison of twists on homogeneous sections

Let `R` be a commutative ring, `𝒜` a graded `R`-algebra, `𝓛` a family of tensor powers of an
invertible `R`-module `ℒ = 𝓛 1` inside a commutative ring `T`, and `ℬ` the twist of `𝒜` by `𝓛`,
so that `ℬ d` is `𝒜 d ⊗_R 𝓛 d`. Clause (2) of [Stacks, Tag 02NC] asserts that for every open
`V` of the base the square

```
𝒜_n(V) ⊗ ℒ^{⊗ n}(V) ---- multiplication ----> ℬ_n(V)
        |                                        |
        | ψ_𝒜                                    | ψ_ℬ
        v                                        v
Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}) <---- θ_n ---- Γ(π'^{-1}V, 𝒪_{P'}(n))
```

commutes, where `ψ` is the map attaching to a homogeneous section the corresponding section of
the twisting sheaf and `θ_n` is the comparison map of clause (1).

This file proves that square in the **absolute** case — `V` the whole of the base `Spec R`, so
that the sections of `ℒ^{⊗ n}` are the elements of `𝓛 n` — for the comparison attached to a
degree-one element `ℓ ∈ 𝓛 1` and the section `ℓ ^ n` of `ℒ^{⊗ n}`. The multiplication map of
the top row is then the structure map `𝒜 n ⊗_R 𝓛 n → ℬ n` of the twist, and the composite
`a ↦ a ⊗ ℓ ^ n ↦ mult` is `Stacks.GradedRing.InvertibleTwist.pieceMap`.

## Main results

* `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_pieceMap`: **clause (2) of Tag
  02NC**, in the absolute case and for the section `ℓ ^ n` of `ℒ^{⊗ n}`.
* `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece`: **the same square at an
  arbitrary section** `l ∈ 𝓛 n` of `ℒ^{⊗ n}` that the trivializing section divides,
  `l = c • ℓ ^ n`, where the left column is the section of `𝒪_P(n)` attached to `c • a`.
* `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece_of_generator`: for a generator
  `ℓ` every section of `ℒ^{⊗ n}` is such a multiple, so the square holds at **every** section.
* `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece_smul_pow`: with **no**
  generation hypothesis, the square at `(μ ℓ) ^ n • l` for an arbitrary `l` and an arbitrary
  functional `μ`, the factor `(μ ℓ) ^ n` being a unit exactly where `ℓ` trivializes `𝓛 1`.

## The route

There is nothing to do beyond naming the right instance. Clause (2) of Tag 02NC is clause (1) of
[Stacks, Tag 01MY] — "the comparison map on the `n`-th twist carries the global section attached
to a homogeneous `a` to the global section attached to `ψ a`" — specialized at the graded ring
homomorphism `ψ = x ↦ x ⊗ ℓ ^ d` of
`Stacks.GradedRing.InvertibleTwist.twistHomOf`, and that clause is proved as
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection`. What remains is to recognise
`ψ a` as the image of `a ⊗ ℓ ^ n` under the twist's multiplication map, which is
`Stacks.GradedRing.InvertibleTwist.twistHomOf_coe`.

So clause (2) needs no new mathematics, only a declaration stating it.

## Scope, and what is not covered

* **The base is `Spec R`.** Tag 02NC is stated over an arbitrary base scheme `S`, and the
  square is asserted for every open `V ⊆ S`. Everything here is the absolute case, as in the
  companion file; the relative statement is not in this library.
* **The section of `ℒ^{⊗ n}` is arbitrary, but the trivialization is still `ℓ ^ n`.** One
  might expect the section to have to be `ℓ ^ n`, a general element of `𝓛 n` being a sum of
  products of `n` *different* degree-one elements, for which there is no single such
  homomorphism. It need not be: the homomorphism is not what carries
  the section: `θ_n` is attached to `twistHomOf ℓ` whatever the section is, and the section
  enters only through the left column, where the trivialization of `π^*ℒ^{⊗ n}` by `ℓ ^ n`
  turns `a ⊗ l` into the section of `𝒪_P(n)` attached to `c • a` as soon as `l = c • ℓ ^ n`.
  That is `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece`, and every section
  is of that form after multiplying by `(μ ℓ) ^ n`
  (`Stacks.GradedRing.IsTensorPowerFamily.smul_pow_eq_dualPow_smul`), or outright when `ℓ`
  generates. What is genuinely out of reach at this shape is not the section but the **object**
  `𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` itself, in which the left column of the source's square lands: see
  below.
* **No generation hypothesis is needed**, exactly as for `twistHomOf` itself: the statement
  holds for every `ℓ ∈ 𝓛 1`. It is therefore available on each member of the family of
  degree-one elements out of which
  `Stacks.GradedRing.InvertibleTwist.projTwistGlued` is glued. It is *not* transported to that
  glued morphism, for the reason the companion file records against a *single* global `θ_n`: no
  twist-comparison bundle for a glued morphism is available, since
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` is attached to a homomorphism of
  graded rings and `projTwistGlued` is not `Proj` of one. Clause (1) itself is proved over the
  cover `{U(ψ_ℓ)}` with no generation hypothesis, by
  `Stacks.GradedRing.InvertibleTwist.isIso_twistMap_twistHomOf` in
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistClauseOne.lean`; the square
  below sits over the same cover.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open scoped TensorProduct

universe u

namespace Stacks.GradedRing

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]

namespace InvertibleTwist

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T}

/-- **Clause (2) of Stacks Tag 02NC, in the absolute case.** For a degree-one element
`ℓ ∈ 𝓛 1` and a homogeneous `a ∈ 𝒜 n`, the comparison map on the `n`-th twist carries the
global section of `𝒪_{Proj 𝒜}(n)` attached to `a` to the global section of `𝒪_{Proj ℬ}(n)`
attached to the product `a ⊗ ℓ ^ n` of `a` with the `n`-th power of `ℓ` in the twisted algebra.
Both sections are read through the unit of the pullback--pushforward adjunction, which is the
form in which a global section of a twist is compared with one of the pullback of that twist.

This is the square of clause (2) with `V` the whole base, the multiplication
`𝒜_n ⊗_R ℒ^{⊗ n} → ℬ_n` of the top row being the twist's own structure map `tw.piece n` and the
section of `ℒ^{⊗ n}` being `ℓ ^ n`; see the module docstring for what that leaves out. No
generation hypothesis on `ℓ` is used. -/
theorem twistMap_degreeSection_pieceMap (hℓ : ℓ ∈ 𝓛 1) (n : ℕ) (a : 𝒜 n) :
    ((projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤) (degreeSection 𝒜 n a))
      = ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n (tw.pieceMap h𝓛 hℓ n a)) :=
  (Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection 𝒜 ℬ
      (tw.twistHomOf h𝓛 hℓ) n a).trans
    (congrArg
      (fun b : ℬ n => ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤) (degreeSection ℬ n b))
      (Subtype.ext (tw.twistHomOf_coe h𝓛 hℓ n a)))

/-! ### Clause (2) at an arbitrary section of the `n`-th power

The square above is at the section `ℓ ^ n` of `ℒ^{⊗ n}`. An arbitrary section is an arbitrary
element `l` of `𝓛 n`, and the top row of clause (2) sends `a ⊗ l` to the product
`tw.piece n (a ⊗ l)` in `ℬ n`. Whenever `l` is a multiple of `ℓ ^ n` — which, after inverting
the value of a functional at `ℓ`, every element of `𝓛 n` is, and which for a generator `ℓ`
every element of `𝓛 n` already is — the square at `l` is the square at `ℓ ^ n` read at a
rescaled `a`, because the comparison of pieces is `R`-linear and `a ⊗ c • ℓ ^ n = (c • a) ⊗ ℓ^n`.
-/

/-- **Clause (2) of Stacks Tag 02NC at an arbitrary section of `ℒ^{⊗ n}` divisible by the
trivializing one.** For `ℓ ∈ 𝓛 1`, a section `l ∈ 𝓛 n` of the `n`-th power with
`l = c • ℓ ^ n`, and a homogeneous `a ∈ 𝒜 n`, the comparison map on the `n`-th twist carries the
global section of `𝒪_{Proj 𝒜}(n)` attached to `c • a` — which is the section of
`𝒪_{Proj 𝒜}(n) ⊗ π^*ℒ^{⊗ n}` attached to `a ⊗ l` read through the trivialization of
`π^*ℒ^{⊗ n}` by `ℓ ^ n` — to the global section of `𝒪_{Proj ℬ}(n)` attached to the product
`a ⊗ l` in the twisted algebra.

`Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_pieceMap` is the case `l = ℓ ^ n`,
`c = 1`. No generation hypothesis on `ℓ` is used, and no hypothesis relating `c` to `l` beyond
the displayed one. -/
theorem twistMap_degreeSection_piece (hℓ : ℓ ∈ 𝓛 1) (n : ℕ) (a : 𝒜 n) (c : R) (l : 𝓛 n)
    (hl : (l : T) = c • ℓ ^ n) :
    ((projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤) (degreeSection 𝒜 n (c • a)))
      = ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n (tw.piece n (a ⊗ₜ[R] l))) := by
  have hl' : l = c • (⟨ℓ ^ n, h𝓛.pow_mem hℓ n⟩ : 𝓛 n) := Subtype.ext hl
  have hkey : tw.pieceMap h𝓛 hℓ n (c • a) = tw.piece n (a ⊗ₜ[R] l) := by
    rw [tw.pieceMap_apply h𝓛 hℓ n (c • a), hl', TensorProduct.tmul_smul,
      ← TensorProduct.smul_tmul']
  rw [← hkey]
  exact tw.twistMap_degreeSection_pieceMap h𝓛 hℓ n (c • a)

/-- **Clause (2) of Stacks Tag 02NC at an arbitrary section of `ℒ^{⊗ n}`, for a twisting module
with a global generator.** When `ℓ` generates `𝓛 1` the power `ℓ ^ n` generates `𝓛 n`
(`Stacks.GradedRing.IsTensorPowerFamily.bijective_toSpanSingleton_pow`), so *every* section
`l ∈ 𝓛 n` is a multiple of it and the square of
`Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece` holds at every section, with
the coordinate of `l` in the basis `ℓ ^ n` as the scalar. -/
theorem twistMap_degreeSection_piece_of_generator (hℓ : ℓ ∈ 𝓛 1)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩)) (n : ℕ)
    (a : 𝒜 n) (l : 𝓛 n) :
    ((projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤)
          (degreeSection 𝒜 n
            ((LinearEquiv.ofBijective _
              (h𝓛.bijective_toSpanSingleton_pow hℓ hgen n)).symm l • a)))
      = ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n (tw.piece n (a ⊗ₜ[R] l))) := by
  refine tw.twistMap_degreeSection_piece h𝓛 hℓ n a _ l ?_
  exact congrArg Subtype.val ((LinearEquiv.ofBijective _
    (h𝓛.bijective_toSpanSingleton_pow hℓ hgen n)).apply_symm_apply l).symm

/-- **Clause (2) of Stacks Tag 02NC at an arbitrary section of `ℒ^{⊗ n}`, with no generation
hypothesis.** For every functional `μ` on `𝓛 1` and every section `l ∈ 𝓛 n`, the section
`(μ ℓ) ^ n • l` is the multiple of `ℓ ^ n` by the value of the `n`-th tensor power of `μ` at `l`
(`Stacks.GradedRing.IsTensorPowerFamily.smul_pow_eq_dualPow_smul`), so the square of
`Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_piece` holds at it with an explicit
scalar. The factor `(μ ℓ) ^ n` is invertible exactly on the locus where `ℓ` trivializes `𝓛 1`,
which by `Stacks.GradedRing.InvertibleTwist.exists_dual_notMem` contains every point of
`U(ψ_ℓ)` for a suitable `μ`; so this is the square at `l` itself wherever clause (1) has
anything to say, read through a trivialization. -/
theorem twistMap_degreeSection_piece_smul_pow (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1)
    (n : ℕ) (a : 𝒜 n) (l : 𝓛 n) :
    ((projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (projMapData 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤)
          (degreeSection 𝒜 n (IsTensorPowerFamily.dualPow h𝓛 μ n l • a)))
      = ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n (tw.piece n (a ⊗ₜ[R] ((μ ⟨ℓ, hℓ⟩) ^ n • l)))) :=
  tw.twistMap_degreeSection_piece h𝓛 hℓ n a _ ((μ ⟨ℓ, hℓ⟩) ^ n • l)
    (h𝓛.smul_pow_eq_dualPow_smul μ hℓ n l)

end InvertibleTwist

end Stacks.GradedRing

end
