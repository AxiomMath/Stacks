module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The two-term product presentation of inverse limits of abelian groups

Let `A` be an inverse system of abelian groups indexed by the natural numbers, that is, a functor
`ℕᵒᵖ ⥤ Ab`. Its inverse limit and its first derived inverse limit are the kernel and the cokernel
of the endomorphism `1 - shift` of the product `∏ₙ Aₙ`, whose `n`-th component sends `(x_m)` to
`x_n - f_{n+1}(x_{n+1})`. This file sets up that presentation: the product, the shift, the
difference map, the canonical inclusion of the limit into the product, the first derived limit as
a cokernel, and the identification of the limit with the kernel.

These are the objects through which the derived inverse limit of an inverse system of abelian
groups is computed, so they are shared by everything in this directory that mentions `R¹lim`.

## Main definitions

* `Rlim.InvSystemAb`: inverse systems of abelian groups indexed by the natural numbers.
* `Rlim.product`, `Rlim.shift`: the product of the terms of a system, and the endomorphism of it
  induced by the transition maps.
* `Rlim.delta`: the difference map `1 - shift` on the product.
* `Rlim.limitToProduct`: the canonical map from the inverse limit into the product of the terms.
* `Rlim.firstDerivedLimit`: the cokernel of `Rlim.delta`, together with the quotient map
  `Rlim.productToFirstDerivedLimit` onto it.

## Main results

* `Rlim.delta_eq_lift`, `Rlim.delta_comp_π`: the componentwise description of `Rlim.delta`.
* `Rlim.limitToProduct_mono`, `Rlim.limitToProduct_comp_delta`: the inclusion of the limit is a
  monomorphism killed by `Rlim.delta`.
* `Rlim.limit_kernel_iso`: the inverse limit is the kernel of `Rlim.delta`, compatibly with the
  limit projections.

## Implementation notes

The product differential is characterized through the product projections rather than by a
formula on elements, so that the statements remain available in the categorical form in which
the derived-limit triangle uses them.

## References

* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace Rlim

universe u

/-- The abelian category of inverse systems of abelian groups indexed by `ℕ`. -/
public abbrev InvSystemAb := ℕᵒᵖ ⥤ Ab.{u}

/-- The product of the terms of a sequential inverse system.

This is reducible: every consumer composes it with Mathlib's product projections and with
`piComparison`, which are stated for the chosen product `∏ᶜ`. -/
public noncomputable abbrev product (A : InvSystemAb.{u}) : Ab.{u} :=
  ∏ᶜ fun n : ℕ ↦ A.obj (Opposite.op n)

/-- The shift on the product induced by the transition maps. -/
public noncomputable def shift (A : InvSystemAb.{u}) : product A ⟶ product A :=
  Pi.lift fun n ↦
    Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) (n + 1) ≫
      A.map (homOfLE (Nat.le_succ n)).op

/-- The differential in the two-term complex computing the derived inverse limit. -/
public noncomputable def delta (A : InvSystemAb.{u}) : product A ⟶ product A :=
  𝟙 (product A) - shift A

/-- The map from the inverse limit into the product, given by all limit projections. -/
public noncomputable def limitToProduct (A : InvSystemAb.{u}) : limit A ⟶ product A :=
  Pi.lift fun n ↦ limit.π A (Opposite.op n)

/-- The first derived inverse limit, written using its two-term product presentation. -/
public noncomputable def firstDerivedLimit (A : InvSystemAb.{u}) : Ab.{u} :=
  cokernel (delta A)

/-- The quotient map from the degree-one term of the product presentation. -/
public noncomputable def productToFirstDerivedLimit (A : InvSystemAb.{u}) :
    product A ⟶ firstDerivedLimit A :=
  cokernel.π (delta A)

-- `product A` is only reducible-transparency defeq to the chosen product `∏ᶜ`, which the
-- product-projection calculus below works with directly.
set_option backward.isDefEq.respectTransparency false

/-- The `n`-th component of the product differential is `x_n - f_{n+1}(x_{n+1})`. -/
public theorem delta_comp_π (A : InvSystemAb.{u}) (n : ℕ) :
    delta A ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n =
      Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op := by
  dsimp only [delta, shift, product]
  show (𝟙 (∏ᶜ fun n : ℕ ↦ A.obj (Opposite.op n)) -
      Pi.lift fun n ↦ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op) ≫
      Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n = _
  rw [Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π]

/-- The product differential written as a single `Pi.lift`. -/
public theorem delta_eq_lift (A : InvSystemAb.{u}) :
    delta A = Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op :=
  Pi.hom_ext _ _ fun n ↦ by rw [delta_comp_π, Pi.lift_comp_π]

/-- The `n`-th projection of the canonical map from the limit to the product is the `n`-th limit
projection. -/
@[simp]
public theorem limitToProduct_comp_π (A : InvSystemAb.{u}) (n : ℕ) :
    limitToProduct A ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n = limit.π A (Opposite.op n) :=
  Pi.lift_comp_π _ n

/-- The canonical map from the inverse limit into the product of the terms is a monomorphism. -/
public theorem limitToProduct_mono (A : InvSystemAb.{u}) : Mono (limitToProduct A) where
  right_cancellation {X} f g h := limit.hom_ext fun j ↦ by
    simpa only [Category.assoc, limitToProduct_comp_π, op_unop] using
      congrArg (· ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) j.unop) h

attribute [local instance] limitToProduct_mono

/-- The composite of the inclusion of the inverse limit with the product differential is zero. -/
public theorem limitToProduct_comp_delta (A : InvSystemAb.{u}) :
    limitToProduct A ≫ delta A = 0 := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, delta_comp_π, Preadditive.comp_sub, limitToProduct_comp_π,
    ← Category.assoc, limitToProduct_comp_π, limit.w, sub_self, zero_comp]

/-- The inverse limit is the kernel of the product differential, with its inclusion into the
product being the canonical one.

This is the `Rlim.delta` form of the general statement
`CategoryTheory.Limits.inverseSystemLimitKernelForkIsLimit`. It is reproved here rather than
imported from it: that module's closure contains `Mathlib.Combinatorics.Quiver.ReflQuiver`, whose
`catToReflQuiver` instance would be the one used for the `⟶` in the type of `Rlim.delta`, and the
resulting `Quiver Ab` instance path does not match the one in Mathlib's `piComparison`, which
every consumer of `Rlim.delta` in this directory composes with. -/
public theorem exists_limit_iso_kernel_delta (A : InvSystemAb.{u}) :
    ∃ e : limit A ≅ kernel (delta A), e.hom ≫ kernel.ι (delta A) = limitToProduct A := by
  have hπ (n : ℕ) : kernel.ι (delta A) ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n =
      kernel.ι (delta A) ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op := by
    have h := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n)
      (kernel.condition (delta A))
    simpa only [Category.assoc, delta_eq_lift, Pi.lift_comp_π, Preadditive.comp_sub,
      zero_comp, sub_eq_zero] using h
  let c : Cone A :=
    ⟨kernel (delta A), NatTrans.ofOpSequence
      (fun n ↦ kernel.ι (delta A) ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n)
      (by
        intro n
        simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Category.assoc] using hπ n)⟩
  let j := limit.lift A c
  have hj : j ≫ limitToProduct A = kernel.ι (delta A) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [j, c]
  refine ⟨⟨kernel.lift (delta A) (limitToProduct A) (limitToProduct_comp_delta A), j, ?_, ?_⟩,
    kernel.lift_ι _ _ _⟩
  · rw [← cancel_mono (limitToProduct A), Category.assoc, hj, Category.id_comp, kernel.lift_ι]
  · rw [← cancel_mono (kernel.ι (delta A)), Category.assoc, Category.id_comp, kernel.lift_ι, hj]

/-- The inverse limit is the kernel of `1 - shift`, with its usual projections. -/
public theorem limit_kernel_iso (A : InvSystemAb.{u}) :
    ∃ e : limit A ≅ kernel (delta A),
      ∀ n : ℕ, e.hom ≫ kernel.ι (delta A) ≫
        Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n =
          limit.π A (Opposite.op n) := by
  obtain ⟨e, he⟩ := exists_limit_iso_kernel_delta A
  exact ⟨e, fun n ↦ by rw [← Category.assoc, he, limitToProduct_comp_π]⟩

end Rlim

end
