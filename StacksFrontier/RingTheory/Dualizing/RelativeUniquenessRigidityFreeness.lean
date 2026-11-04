module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessRigidity
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The freeness half of the rigidity step, from the rigidity hypothesis itself

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessRigidity` reads the one-sided local
computation of the duality route to [stacks 0E2D] on `P` itself and gets two things:
`P` lies in `D^{≤ 0}`, and `H⁰(P) ⊗_A A / m ≅ A / m` at every maximal ideal — so `H⁰(P)` needs
**one generator** at every maximal ideal.  Its module documentation records that what the
perfection chain still consumes is the *lower* bound `(P ⊗ᴸ_A κ(m)).IsGE 0`, equivalently
`τ^{≤ -1}P = 0` together with `H⁰(P)` locally free of rank one, and that by [stacks 068V] no
window count on the fibre can produce it.

**This file closes the second of those two conjuncts**, and it closes it from the rigidity
hypothesis rather than from any count.  The input is the hypothesis the whole uniqueness argument
is about — `RHom_A(P, A) ≅ A`, equivalently `P ⊗ᴸ_A ω ≅ ω` — read in degree zero, and the
conclusion is that `H⁰(P)` is free of rank one over a local ring.  Nothing here is a length or a
degree count, and nothing here goes through [stacks 068V].

## The argument

Three steps, of which only the first touches the derived category.

* **Degree zero of the rigidity hypothesis is a statement about the `A`-dual of `H⁰(P)`.**  For
  `P` in `D^{≤ 0}` and `N` a module, [stacks 06XS] at `n = a = a' = b = 0` identifies
  `Ext⁰_A(P, N[0])` with `Hom_A(H⁰(P), N)`; that is
  `Dualizing.extZeroLinearEquivDualHomologyZero`, built from the `A`-linear form of the tag
  already in the library, `Dualizing.extremalExtLinearEquiv`.  At `N = A` the rigidity
  hypothesis, read in degree zero, therefore says exactly

  `Hom_A(H⁰(P), A)` is free of rank one.

* **A module with one generator whose `A`-dual is free of rank one is free of rank one.**  This is
  `Dualizing.bijective_of_dual_linearEquiv_self_of_surjective`, and it uses **no** finiteness, no
  Noetherian hypothesis and no local hypothesis.  Let `M = A · μ` and let `g` generate
  `Hom_A(M, A)` freely.  Freeness of the dual says `a · g = 0` only for `a = 0`; since every
  element of `M` is `b · μ`, the map `a · g` vanishes exactly when `a · g(μ) = 0`, so
  `a · g(μ) = 0` forces `a = 0`.  Now if `a · μ = 0` then `a · g(μ) = g(a · μ) = 0`, so `a = 0`:
  the surjection `A → M`, `a ↦ a · μ`, is injective as well.

* **Over a local ring the one-generator conclusion is cyclicity.**  `Dualizing`'s
  `exists_span_singleton_eq_top_of_tensor_residue` turns
  `M ⊗_A A / m ≅ A / m` for `M` finite over a local ring into a single generator of `M`, by
  Nakayama in the form `IsLocalRing.map_mkQ_eq_top` ([stacks 00DV]).

## Why the dual, and not a module-level count

The rigidity equation also has a *top-degree* reading, obtained by making the extremal
nonvanishing degrees add as the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` describes: for `ω` in `D^{≤ b}` with
`H^b(ω) ≠ 0` that device would give `H⁰(P) ⊗_A H^b(ω) ≅ H^b(ω)` — **a reading, not a declaration
in the library.  And it is not enough, which a witness shows**: over
`A = k[x]/(x²)` take `M = N = A / (x)`; then `M ⊗_A N ≅ N` and `M ⊗_A A / (x) ≅ A / (x)`, so `M`
satisfies both the module-level rigidity equation and the one-generator conclusion, while `M` is
not free.  The dual form rejects that witness, because `Hom_A(A / (x), A) = (x) ≅ k` is not free
of rank one.  So it is the `Hom_A(-, A)` reading of the hypothesis, and not its tensor reading,
that carries the freeness — which is why this file consumes `Ext⁰_A(P, A[0])` and not a count.

## What is **not** closed

Four things, stated exactly.  **[stacks 0E2D] is not closed by this file and no registration or
caveat anywhere in the library is changed by it.**

1. **The degree-zero reading is assumed, not derived.**  The route's hypothesis is an
   isomorphism of *objects*, `RHom_A(P, A) ≅ A` in `D(A)`; what the theorems below consume is the
   `A`-linear statement `Ext⁰_A(P, A[0]) ≅ A`.  Passing from the first to the second is the
   adjunction `- ⊗ᴸ_A P ⊣ RHom_A(P, -)` evaluated at the tensor unit, together with `A`-linearity
   of its hom-equivalence — the enriched adjunction of
   `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction` is the relevant
   ingredient.  **No declaration in the library states the composite and this file does not prove
   it.**  It is bookkeeping rather than a mathematical obstruction, but it is not done here.

2. **The statements are local.**  `H⁰(P)` is shown free of rank one over a *local* ring, because
   that is where one generator at the maximal ideal is cyclicity.  The one-generator
   conclusion is a statement about the global `A` at each of its maximal ideals, so a global
   reading needs `Hom_A(-, A)` and `H⁰` to commute with localization at a maximal ideal — true
   for a finitely presented module over a Noetherian ring, and **not assembled here**.

3. **Freeness is only one of the two conjuncts, and the other is independent.**  The remaining
   obligation of the perfection chain is `(P ⊗ᴸ_A κ(m)).IsGE 0`, which is `τ^{≤ -1}P = 0` *and*
   `H⁰(P)` locally free of rank one.  The first conjunct does **not** follow from the second:
   `P.IsLE 0` together with `H⁰(P) ⊗_A κ(m) ≅ κ(m)` bounds `P` above and says nothing below, and
   once `H⁰(P)` is free the triangle `τ^{≤ -1}P → P → H⁰(P)[0]` tensored with `κ(m)` identifies
   `H^{-1}(P ⊗ᴸ_A κ(m))` with `H^{-1}(P) ⊗_A κ(m)` — so the lower bound on the fibre and
   `P.IsGE 0` are the same statement, and neither is available.  **This reading is recorded as a
   reading; it is not a theorem in the library.**

4. **Where the remaining conjunct now sits.**  Reading the rigidity hypothesis on that same
   triangle rather than on its degree-zero part: with `H⁰(P)` free of rank one, `RHom_A(-, A)`
   applied to `τ^{≤ -1}P → P → H⁰(P)[0]` has `RHom_A(H⁰(P), A)` concentrated in degree zero and
   `RHom_A(τ^{≤ -1}P, A)` in degrees `≥ 1`, so `RHom_A(P, A) ≅ A` forces
   `RHom_A(τ^{≤ -1}P, A) ≅ 0`.  For a pseudo-coherent `τ^{≤ -1}P` over a Noetherian ring that is
   the `A`-dual of a bounded-above complex of finite free modules being acyclic, and concluding
   `τ^{≤ -1}P ≅ 0` from it is the statement that a bounded-below acyclic complex of finite free
   `A`-modules is contractible — **the same kind of condition on the ring at which the diagonal
   route stalls**, recorded in the module documentation of
   `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`.  So after this file what remains of
   the duality route is neither a count nor freeness; it is that contractibility
   statement, plus the standing hypothesis that `ω` be a dualizing complex for `A`, which the
   source of [stacks 0E2D] does not assume and which is unconditional only over a field.
   **This derivation is prose: it is not formalized here, and no declaration below states any
   part of it.**

## Main results

* `Dualizing.bijective_of_dual_linearEquiv_self_of_surjective` — a cyclic module whose `A`-dual
  is free of rank one is free of rank one; no hypothesis on the ring or the module.
* `Dualizing.exists_span_singleton_eq_top_of_tensor_residue` — over a local ring, a finite module
  with `M ⊗_A A / m ≅ A / m` has a single generator.
* `Dualizing.extZeroLinearEquivDualHomologyZero` — `Ext⁰_A(P, N[0]) ≅ Hom_A(H⁰(P), N)` for `P` in
  `D^{≤ 0}`, the degree-zero reading of a derived Hom out of `P`.
* `Dualizing.free_homology_zero_of_ext_zero_of_nonempty_tensor_homology_iso` — the freeness half
  of the rigidity step, assembled against the conclusion of
  `Dualizing.nonempty_tensor_homology_zero_iso_quotient`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section Cyclic

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- An `A`-linear map out of `A` is determined by its value at `1`: `f a = a • f 1`. -/
private theorem apply_eq_smul_apply_one {F : Type*} [FunLike F A M] [LinearMapClass F A A M]
    (f : F) (a : A) : f a = a • f 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

/-- **A cyclic module whose `A`-dual is free of rank one is free of rank one.**  If `π : A → M`
is a surjection of `A`-modules and `Hom_A(M, A)` is free of rank one, then `π` is bijective.

This is the step that turns the rigidity hypothesis of the duality route to [stacks 0E2D] into
freeness of `H⁰(P)`.  Writing `g` for a free generator of `Hom_A(M, A)` and `μ = π 1`: freeness
of the dual says `a • g = 0` only for `a = 0`, and since every element of `M` is `b • μ` the map
`a • g` vanishes exactly when `a * g μ = 0`; so `g μ` has zero annihilator, and `π a = 0` gives
`a * g μ = g (π a) = 0` and hence `a = 0`.

**No finiteness, no Noetherian hypothesis and no local hypothesis is used**, and no degree or
length count enters. -/
theorem bijective_of_dual_linearEquiv_self_of_surjective
    (π : A →ₗ[A] M) (hπ : Function.Surjective π) (e : (M →ₗ[A] A) ≃ₗ[A] A) :
    Function.Bijective π := by
  have hzero : ∀ a : A, a * e.symm 1 (π 1) = 0 → a = 0 := by
    intro a ha
    have h0 : a • e.symm 1 = 0 := by
      ext m
      obtain ⟨b, rfl⟩ := hπ m
      rw [LinearMap.smul_apply, apply_eq_smul_apply_one π b, map_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, mul_comm a b, mul_assoc, ha, mul_zero]
      simp
    rwa [← apply_eq_smul_apply_one e.symm a, LinearEquiv.map_eq_zero_iff] at h0
  refine ⟨fun a b hab => sub_eq_zero.mp (hzero _ ?_), hπ⟩
  rw [← smul_eq_mul, ← map_smul, ← apply_eq_smul_apply_one π, map_sub, hab, sub_self, map_zero]

/-- **The same statement with the generator named.**  A module generated by a single element and
whose `A`-dual is free of rank one is free of rank one, the isomorphism being `a ↦ a • μ`. -/
theorem nonempty_linearEquiv_of_dual_linearEquiv_of_span_eq_top
    (μ : M) (hμ : Submodule.span A ({μ} : Set M) = ⊤) (e : (M →ₗ[A] A) ≃ₗ[A] A) :
    Nonempty (A ≃ₗ[A] M) := by
  refine ⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M μ)
    (bijective_of_dual_linearEquiv_self_of_surjective _ ?_ e)⟩
  rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hμ]

end Cyclic

section LocalCyclic

variable {A : Type u} [CommRing A] [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- **One generator at the maximal ideal is cyclicity, over a local ring.**  A finite module over
a local ring whose residue tensor `M ⊗_A A / m` is `A / m` is generated by a single element.

This is Nakayama's lemma ([stacks 00DV]) in the form `IsLocalRing.map_mkQ_eq_top`: the
isomorphism identifies `M / m M` with `A / m`, whose `A`-span of the class of `1` is everything,
so the class of a preimage of that class spans `M / m M`, and Nakayama lifts that to `M`.

It is what makes the conclusion of `Dualizing.nonempty_tensor_homology_zero_iso_quotient` usable:
globally a finite module with one-dimensional residue tensors everywhere need not be cyclic, so
the local hypothesis here is not cosmetic. -/
@[ega "IV 2.5.8.8" "special case"]
theorem exists_span_singleton_eq_top_of_tensor_residue [Module.Finite A M]
    (e : TensorProduct A M (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A]
      (A ⧸ IsLocalRing.maximalIdeal A)) :
    ∃ μ : M, Submodule.span A ({μ} : Set M) = ⊤ := by
  let E : (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) ≃ₗ[A]
      (A ⧸ IsLocalRing.maximalIdeal A) :=
    (TensorProduct.tensorQuotEquivQuotSMul M (IsLocalRing.maximalIdeal A)).symm.trans e
  set m1 : A ⧸ IsLocalRing.maximalIdeal A := (IsLocalRing.maximalIdeal A).mkQ 1 with hm1
  obtain ⟨μ, hμ⟩ := Submodule.mkQ_surjective
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) (E.symm m1)
  refine ⟨μ, ?_⟩
  have h1 : Submodule.span A ({m1} : Set (A ⧸ IsLocalRing.maximalIdeal A)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (IsLocalRing.maximalIdeal A) x
    rw [apply_eq_smul_apply_one (IsLocalRing.maximalIdeal A).mkQ a]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h2 : Submodule.span A ({E.symm m1} :
      Set (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)))) = ⊤ := by
    have himg : ({E.symm m1} : Set (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
        = E.symm.toLinearMap '' ({m1} : Set (A ⧸ IsLocalRing.maximalIdeal A)) := by simp
    rw [himg, Submodule.span_image, h1, Submodule.map_top]
    exact LinearMap.range_eq_top.2 E.symm.surjective
  rwa [← IsLocalRing.map_mkQ_eq_top, Submodule.map_span, Set.image_singleton, hμ]

/-- **The rigidity step for a module, over a local ring.**  A finite module over a local ring
whose `A`-dual is free of rank one and whose residue tensor is the residue field is free of rank
one.

The two hypotheses are, respectively, the rigidity hypothesis of the duality route to
[stacks 0E2D] read in degree zero and the one-generator conclusion of
`Dualizing.nonempty_tensor_homology_zero_iso_quotient`; neither is a degree or length count. -/
theorem nonempty_linearEquiv_of_dual_linearEquiv_of_tensor_residue [Module.Finite A M]
    (hdual : Nonempty ((M →ₗ[A] A) ≃ₗ[A] A))
    (hone : Nonempty (TensorProduct A M (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A]
      (A ⧸ IsLocalRing.maximalIdeal A))) :
    Nonempty (A ≃ₗ[A] M) := by
  obtain ⟨e⟩ := hdual
  obtain ⟨f⟩ := hone
  obtain ⟨μ, hμ⟩ := exists_span_singleton_eq_top_of_tensor_residue f
  exact nonempty_linearEquiv_of_dual_linearEquiv_of_span_eq_top μ hμ e

/-- `Dualizing.nonempty_linearEquiv_of_dual_linearEquiv_of_tensor_residue` as freeness. -/
theorem free_of_dual_linearEquiv_of_tensor_residue [Module.Finite A M]
    (hdual : Nonempty ((M →ₗ[A] A) ≃ₗ[A] A))
    (hone : Nonempty (TensorProduct A M (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A]
      (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.Free A M := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_dual_linearEquiv_of_tensor_residue hdual hone
  exact Module.Free.of_equiv e

end LocalCyclic

section Derived

variable (A : Type u) [CommRing A]

/-- **Degree zero of a derived Hom out of `D^{≤ 0}` is a dual of the top cohomology.**  For `P` in
`D^{≤ 0}(A)` and a module `N`,

`Ext⁰_A(P, N[0]) ≅ Hom_A(H⁰(P), N)` ,

`A`-linearly.  This is [stacks 06XS] at `n = a = a' = b = 0` — both bounds are the degree-zero
ones, `P` is in `D^{≤ 0}` and `N[0]` is in `D^{≥ 0}` — in the `A`-linear form the library already
has, `Dualizing.extremalExtLinearEquiv`, composed with
`DerivedCategory.singleFunctorCompHomologyFunctorIso` to strip `H⁰` off the single complex.

At `N = A` this is the reading of the rigidity hypothesis `RHom_A(P, A) ≅ A` that the freeness
half of the rigidity step consumes.  **No hypothesis on `A` is used, and `P` is not assumed
bounded below.** -/
noncomputable def extZeroLinearEquivDualHomologyZero
    (P : DerivedCategory (ModuleCat.{u} A)) [P.IsLE 0] (N : ModuleCat.{u} A) :
    DerivedCategory.Ext P ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 0 ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P →ₗ[A] N) :=
  (extremalExtLinearEquiv P ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
      0 0 0 0 (by norm_num) le_rfl).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl A _)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
        N).toLinearEquiv)

/-- **`H⁰(P)` is free of rank one, from the rigidity hypothesis read in degree zero.**  Let `A` be
local, let `P` lie in `D^{≤ 0}(A)` with finite `H⁰(P)`, and suppose

* `Ext⁰_A(P, A[0]) ≅ A` — the degree-zero reading of `RHom_A(P, A) ≅ A`, and
* `H⁰(P) ⊗_A A / m ≅ A / m` — the conclusion of
  `Dualizing.nonempty_tensor_homology_zero_iso_quotient`.

Then `A ≅ H⁰(P)`.

This is the freeness half of the rigidity step of the duality route to [stacks 0E2D].  See the
module documentation for the four things it does not close — in particular that the first
hypothesis is the *degree-zero reading* of the route's object-level hypothesis and that the
passage between them is not in the library, and that `τ^{≤ -1}P = 0` is an independent conjunct
which this does not touch. -/
theorem nonempty_linearEquiv_homology_zero_of_ext_zero_of_tensor_residue [IsLocalRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) [P.IsLE 0]
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)]
    (hext : Nonempty (DerivedCategory.Ext P
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0 ≃ₗ[A] A))
    (hone : Nonempty (TensorProduct A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)
      (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A))) :
    Nonempty (A ≃ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)) :=
  nonempty_linearEquiv_of_dual_linearEquiv_of_tensor_residue
    (hext.map (extZeroLinearEquivDualHomologyZero A P (ModuleCat.of A A)).symm.trans) hone

/-- `Dualizing.nonempty_linearEquiv_homology_zero_of_ext_zero_of_tensor_residue` as freeness of
`H⁰(P)`. -/
theorem free_homology_zero_of_ext_zero_of_tensor_residue [IsLocalRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) [P.IsLE 0]
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)]
    (hext : Nonempty (DerivedCategory.Ext P
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0 ≃ₗ[A] A))
    (hone : Nonempty (TensorProduct A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)
      (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_zero_of_ext_zero_of_tensor_residue A P hext hone
  exact Module.Free.of_equiv e

/-- **The freeness half of the rigidity step, against the library's one-generator conclusion.**  The
second hypothesis is verbatim the conclusion of
`Dualizing.nonempty_tensor_homology_zero_iso_quotient` at the maximal ideal of a local ring: an
isomorphism of `A`-modules in `ModuleCat`, rather than a `LinearEquiv`.  Everything else is
`Dualizing.free_homology_zero_of_ext_zero_of_tensor_residue`. -/
theorem free_homology_zero_of_ext_zero_of_nonempty_tensor_homology_iso [IsLocalRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) [P.IsLE 0]
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)]
    (hext : Nonempty (DerivedCategory.Ext P
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0 ≃ₗ[A] A))
    (hone : Nonempty (ModuleCat.of A (TensorProduct A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)
      (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))) ≅
      ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P) :=
  free_homology_zero_of_ext_zero_of_tensor_residue A P hext (hone.map fun f => f.toLinearEquiv)

end Derived

end Dualizing

end
