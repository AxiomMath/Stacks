module

public import Mathlib.RingTheory.Length
public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.RingTheory.LocalRing.ResidueFieldCardinality
public import StacksFrontier.RingTheory.Noetherian.NilpotentKernel

/-!
# The thickening of Stacks 07YL, as a deformation situation in the site

Stacks 07YL produces, from a morphism `ξ : E ⟶ NL_{A/Λ}` of `D⁻(A)` whose derived fibre at a
prime `𝔭` is not surjective in degree `-1`, a surjection `A' → A` of `Λ`-algebras with
square-zero kernel `I ≅ κ(𝔭)` killing `ξ`. Condition (iii) of Stacks 07YX, which is hypothesis
(i) of Stacks 07YM, speaks instead of a *deformation situation* — the datum
`Deformation.Artin.SquareZeroThickening`, which carries the extension together with its
presentation in the chosen big fppf site. This file crosses that gap: it turns the output of
Stacks 07YL into a deformation situation, and records that `A'` is again Noetherian.

Both additions are derived, not assumed. The spectrum of `A'` lies in the site because a
surjection onto `A` with kernel a copy of `κ(𝔭)` cannot escape the size bound
(`Deformation.Artin.contains_spec_of_surjective_of_mk_ker_le`, with
`Cardinal.mk_residueField_le_max`), and `A'` is Noetherian because its kernel is a finitely
generated nilpotent ideal (`isNoetherianRing_of_surjective_fg_nilpotent_ker`). The finite
generation is itself derived: `I` is a finite module over `A` because `κ(𝔭)` is, and the
`A`-action on `I` is induced by the surjection `A' → A`, so an `A`-spanning set generates `I`
as an ideal of `A'`.

## Main results

* `Ideal.fg_of_module_finite_quotient` — an ideal of `A'` finite as a module over a quotient
  `A` of `A'`, through the action the quotient map induces, is finitely generated as an ideal
  of `A'`.
* `isNoetherianRing_of_squareZero_module_finite_ker` — such a square-zero thickening of a
  Noetherian ring is Noetherian.
* `Deformation.Artin.squareZeroThickeningOfMkLe` — **the deformation situation**: a
  surjection `A' → A` of `Λ`-algebras with square-zero kernel of cardinality at most
  `max ℵ₀ #A` carries a `Deformation.Artin.SquareZeroThickening` whose surjection is
  `algebraMap A' A`.
* `Deformation.Artin.module_finite_ker_of_linearEquiv_residueField` and
  `Deformation.Artin.mk_ker_le_max_of_linearEquiv_residueField` — the two properties of the
  kernel that the previous two results consume, read off the identification of the kernel with
  a residue field that Stacks 07YL supplies.
* `Deformation.Artin.isSimpleModule_residueField` — the residue field at a maximal ideal is a
  simple module over the ring.
* `Deformation.Artin.length_ker_eq_one_of_linearEquiv_residueField` and
  `Deformation.Artin.mul_ker_eq_bot_of_linearEquiv_residueField` — the two further properties
  of the kernel that the small-extension step consumes: it has length one over `A'`, and it is
  annihilated by the prime `𝔭'` of `A'` over `𝔭`.

## Implementation notes

The results are kept separate rather than composed into one existential over the output of
Stacks 07YL. Restating that output costs a re-elaboration of
`Deformation.Artin.differentialsBaseChangeMap Λ A' A κ(𝔭)` against the local algebra instances
the quantifier introduces, which does not fit in the heartbeat budget; applied in sequence
inside the proof that destructured Stacks 07YL, each of them is cheap. Nothing is lost: the
hypotheses of each are exactly components of the conclusion of Stacks 07YL.

Closedness of the point does not appear here. It enters the chain only through the two facts of
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint` — the prime is maximal, and the
residue field is of finite type over `A` — and those are what Stacks 07YL and
`Deformation.Artin.module_finite_ker_of_linearEquiv_residueField` ask for. The source's remark
that this step "fails if `u₀` is not closed" is exactly the failure of these two. The size
bound, by contrast, needs only primality.

The `Λ`-algebra structure of `A'` and the scalar tower `Λ → A' → A` are part of the output of
Stacks 07YL and are what the structure morphism of `Spec A'` is built from; no further
compatibility is imposed, and in particular the base map `Spec Λ ⟶ S` and its factorization of
`toS` are the ones Stacks 07YM already carries.

## References

* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-! ### Finite generation of an ideal through a quotient action -/

/-- An ideal `I = Ker(A' → A)` of `A'` which is a finite module over `A` for the action induced
by the surjection `A' → A` is finitely generated as an ideal of `A'`.

An `A`-spanning set of `I` already generates it over `A'`: every scalar of `A` is the image of
a scalar of `A'`, and the two actions agree. -/
public theorem Ideal.fg_of_module_finite_quotient {A' A : Type u} [CommRing A'] [CommRing A]
    [Algebra A' A] (hsurj : Function.Surjective (algebraMap A' A))
    [Module A (RingHom.ker (algebraMap A' A))]
    (hcomp : ∀ (a' : A') (x : RingHom.ker (algebraMap A' A)),
      (algebraMap A' A a') • x = a' • x)
    [hfin : Module.Finite A (RingHom.ker (algebraMap A' A))] :
    (RingHom.ker (algebraMap A' A)).FG := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image Subtype.val, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact x.2
  · have key : ∀ z : RingHom.ker (algebraMap A' A),
        (z : A') ∈ Ideal.span (↑(s.image Subtype.val) : Set A') := by
      intro z
      have hmem : z ∈ Submodule.span A (↑s : Set (RingHom.ker (algebraMap A' A))) := by
        rw [hs]; exact Submodule.mem_top
      induction hmem using Submodule.span_induction with
      | mem x hx =>
        refine Ideal.subset_span ?_
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨x, hx, rfl⟩
      | zero => simp
      | add u v _ _ hu hv =>
        have hval : ((u + v : RingHom.ker (algebraMap A' A)) : A') = (u : A') + (v : A') := rfl
        rw [hval]
        exact Ideal.add_mem _ hu hv
      | smul a u _ hu =>
        obtain ⟨a', rfl⟩ := hsurj a
        rw [hcomp a' u]
        exact Ideal.mul_mem_left _ _ hu
    intro y hy
    exact key ⟨y, hy⟩

/-- A square-zero thickening of a Noetherian ring whose kernel is a finite module over the
quotient is again Noetherian: the kernel is finitely generated by
`Ideal.fg_of_module_finite_quotient` and nilpotent because its square vanishes. -/
public theorem isNoetherianRing_of_squareZero_module_finite_ker {A' A : Type u} [CommRing A']
    [CommRing A] [IsNoetherianRing A] [Algebra A' A]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Module A (RingHom.ker (algebraMap A' A))]
    (hcomp : ∀ (a' : A') (x : RingHom.ker (algebraMap A' A)),
      (algebraMap A' A a') • x = a' • x)
    [Module.Finite A (RingHom.ker (algebraMap A' A))] : IsNoetherianRing A' :=
  isNoetherianRing_of_surjective_fg_nilpotent_ker (algebraMap A' A) hsurj
    (Ideal.fg_of_module_finite_quotient hsurj hcomp) ⟨2, hsq⟩

namespace Deformation.Artin

/-! ### An algebraic square-zero extension of small kernel, as a deformation situation -/

section Site

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

variable (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]

include hbase in
/-- **The deformation situation of a small square-zero extension.** A surjection `A' → A` of
`Λ`-algebras with square-zero kernel of cardinality at most `max ℵ₀ #A` is a deformation
situation in the sense of Stacks 07YX: the size bound puts `Spec A'` in the site
(`Deformation.Artin.contains_spec_of_surjective_of_mk_ker_le`) and
`Deformation.Artin.squareZeroThickeningOfTower` assembles the datum.

This is a definition rather than an existential statement on purpose. The thickening is used
by applying condition (iii) of Stacks 07YX to it, so what a consumer needs is the datum itself;
an existential `∃ D, D.q = algebraMap A' A` would have to be re-elaborated under the
quantifier over `A'` that Stacks 07YL's conclusion is written with, which is expensive, and
would say nothing the definitional equality `squareZeroThickeningOfMkLe_q` does not. -/
public def squareZeroThickeningOfMkLe
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (hmk : Cardinal.mk (RingHom.ker (algebraMap A' A)) ≤
      max Cardinal.aleph0 (Cardinal.mk A)) :
    SquareZeroThickening A B S hS toS hA A' :=
  squareZeroThickeningOfTower Λ A B S hS toS hA baseMap hbase A'
    (contains_spec_of_surjective_of_mk_ker_le B hA A' (algebraMap A' A) hsurj hmk) hsurj hsq

include hbase in
/-- The surjection of `Deformation.Artin.squareZeroThickeningOfMkLe` is the structure map of
`A` over `A'`. -/
@[simp] public theorem squareZeroThickeningOfMkLe_q
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (hmk : Cardinal.mk (RingHom.ker (algebraMap A' A)) ≤
      max Cardinal.aleph0 (Cardinal.mk A)) :
    (squareZeroThickeningOfMkLe Λ A B S hS toS hA baseMap hbase A' hsurj hsq hmk).q =
      algebraMap A' A := rfl

end Site


/-! ### The kernel of the thickening of Stacks 07YL -/

section Kernel

variable {A' A : Type u} [CommRing A'] [CommRing A] [Algebra A' A]
  [Module A (RingHom.ker (algebraMap A' A))]

/-- The kernel of the thickening of Stacks 07YL is a finite `A`-module: it is a copy of the
residue field at a maximal ideal, which is the quotient by that ideal. -/
public theorem module_finite_ker_of_linearEquiv_residueField (p : Ideal A) [p.IsMaximal]
    (e : RingHom.ker (algebraMap A' A) ≃ₗ[A] p.ResidueField) :
    Module.Finite A (RingHom.ker (algebraMap A' A)) :=
  Module.Finite.equiv e.symm

/-- The kernel of the thickening of Stacks 07YL is no larger than `max ℵ₀ #A`: it is a copy of
the residue field at a prime of `A`, which `Cardinal.mk_residueField_le_max` bounds. This is
the size estimate `Deformation.Artin.squareZeroThickeningOfMkLe` consumes. -/
public theorem mk_ker_le_max_of_linearEquiv_residueField (p : Ideal A) [p.IsPrime]
    (e : RingHom.ker (algebraMap A' A) ≃ₗ[A] p.ResidueField) :
    Cardinal.mk (RingHom.ker (algebraMap A' A)) ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
  rw [Cardinal.mk_congr e.toEquiv]
  exact Cardinal.mk_residueField_le_max p

/-- The residue field at a **maximal** ideal is a simple module over the ring: the structure
map `A ⟶ κ(𝔭)` is surjective (`Ideal.algebraMap_residueField_surjective`), so the `A`-submodules
of `κ(𝔭)` are its `κ(𝔭)`-subspaces, and a field is a simple module over itself.

Maximality is essential and is where the closedness of the point of [Stacks, Tag 07YM] enters
the length computation: over `A = ℤ` at the prime `0` the residue field is `ℚ`, whose
`ℤ`-submodules include `ℤ`. -/
public theorem isSimpleModule_residueField {A : Type*} [CommRing A] (p : Ideal A)
    [p.IsMaximal] : IsSimpleModule A p.ResidueField :=
  (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (R := A) (S := p.ResidueField) (M := p.ResidueField)
    p.algebraMap_residueField_surjective).mpr inferInstance

variable (hsurj : Function.Surjective (algebraMap A' A))
  (hcomp : ∀ (a' : A') (x : RingHom.ker (algebraMap A' A)),
    (algebraMap A' A a') • x = a' • x)

include hsurj hcomp in
/-- **The length-one hypothesis of
`Deformation.ArtinianLocalAlgCat.isSmallExtension_powQuotientMap`.** The kernel of the
thickening of [Stacks, Tag 07YL] has length one over `A'`: it is a copy of the residue field
at a maximal ideal of `A`, hence a simple `A`-module
(`Deformation.Artin.isSimpleModule_residueField`), and the `A'`-submodules of it are its
`A`-submodules because the two actions agree through the surjection `A' → A`
(`isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective`). -/
@[stacks 07YM "the kernel `I` of `A' → A` has length one over `A'`"]
public theorem length_ker_eq_one_of_linearEquiv_residueField
    (p : Ideal A) [p.IsMaximal]
    (e : RingHom.ker (algebraMap A' A) ≃ₗ[A] p.ResidueField) :
    Module.length A' (RingHom.ker (algebraMap A' A)) = 1 := by
  have : IsScalarTower A' A (RingHom.ker (algebraMap A' A)) :=
    IsScalarTower.of_algebraMap_smul fun a' x => hcomp a' x
  have : IsSimpleModule A (RingHom.ker (algebraMap A' A)) :=
    e.isSimpleModule_iff.mpr (isSimpleModule_residueField p)
  have : IsSimpleModule A' (RingHom.ker (algebraMap A' A)) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj).mpr ‹_›
  exact Module.length_eq_one A' (RingHom.ker (algebraMap A' A))

include hcomp in
/-- **The Artin–Rees input of [Stacks, Tag 07YM].** An ideal of `A'` carried by the surjection
`A' → A` into the kernel of `A ⟶ κ(𝔭)` annihilates the kernel `I` of that surjection: the two
actions on `I` agree, and `I` is a copy of `κ(𝔭)`, on which `𝔭` acts by zero.

Applied with `q = Ker(A' ⟶ κ(𝔭))` this is the hypothesis `𝔭' · I = 0` of
`Deformation.Artin.exists_pow_inf_eq_bot_of_mul_eq_bot`, which produces the exponent `n > 1`
with `(𝔭') ^ n ⊓ I = 0`. Only primality of `𝔭` is used. -/
@[stacks 07YM "𝔭' annihilates the kernel I of A' → A"]
public theorem mul_ker_eq_bot_of_linearEquiv_residueField
    (p : Ideal A) [p.IsPrime]
    (e : RingHom.ker (algebraMap A' A) ≃ₗ[A] p.ResidueField)
    (q : Ideal A')
    (hq : ∀ a' ∈ q, algebraMap A' A a' ∈ RingHom.ker (algebraMap A p.ResidueField)) :
    q * RingHom.ker (algebraMap A' A) = ⊥ := by
  refine le_antisymm (Ideal.mul_le.mpr fun a' ha' i hi => ?_) bot_le
  have hzero : a' • (⟨i, hi⟩ : RingHom.ker (algebraMap A' A)) = 0 := by
    refine e.injective ?_
    rw [← hcomp a' ⟨i, hi⟩, map_smul, map_zero, Algebra.smul_def,
      RingHom.mem_ker.mp (hq a' ha'), zero_mul]
  exact Ideal.mem_bot.mpr (congrArg Subtype.val hzero)

end Kernel

end Deformation.Artin
