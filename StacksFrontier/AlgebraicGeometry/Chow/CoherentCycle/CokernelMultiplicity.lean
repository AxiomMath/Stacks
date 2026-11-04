module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport

/-!
# The multiplicity of a cokernel as a stalk quotient

Let `a : F ⟶ G` be a morphism of modules on a scheme `X` and let `x` be a point. Taking stalks
at `x` is exact, so the stalk of `cokernel a` at `x` is the quotient of the stalk of `G` by the
image of the stalk map of `a`. Reading lengths through that identification expresses the
multiplicity `Stacks.Chow.sheafMultiplicity (cokernel a) x` of Stacks 02QX part (1) as the
length of a quotient of the stalk of `G`, which is the form in which the multiplicities of the
denominator quotients of Stacks 02SW are computed.

## Main results

* `LinearMap.range_eq_ker_of_forall_mem_iff` and
  `Module.length_eq_length_quotient_range_of_surjective` — the two module-theoretic steps,
  stated over an abstract ring.
* `AlgebraicGeometry.Scheme.Modules.range_stalkLinearMap_eq_ker_cokernelπ` — the stalk map of
  `a` has image the kernel of the stalk map of `cokernel.π a`.
* `AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_cokernelπ` — the stalk map of
  `cokernel.π a` is surjective.
* `AlgebraicGeometry.Scheme.Modules.length_stalk_cokernel` — the length of the stalk of
  `cokernel a`, as the length of a quotient of the stalk of `G`.
* `Stacks.Chow.sheafMultiplicity_cokernel` — the same for the multiplicity of Stacks 02QX
  part (1).

## Implementation notes

`Stacks.Chow.sheafMultiplicity` measures lengths over the stalk `X.presheaf.stalk x` of the
structure sheaf taken in `CommRingCat`, while `AlgebraicGeometry.SheafOfModules.stalkFunctor`
lands in modules over the stalk `TopCat.Presheaf.stalk X.ringCatSheaf.obj x` taken in `RingCat`.
These are two different colimits, and the carriers are not interchangeable even at the default
transparency level, so the exactness supplied by the categorical stalk functor cannot be
rewritten into a statement about `AlgebraicGeometry.stalkLinearMap`, which is linear over the
first ring.

The two rings are therefore never compared. The categorical input is used only in the form
`LinearMap.range _ = LinearMap.ker _` over the second ring, and that equation is transported to
the first ring through `LinearMap.range_eq_ker_of_forall_mem_iff`, whose hypothesis mentions
only elements and so is insensitive to which ring the maps are linear over: the two readings of
a stalk map have the same underlying function. Both module-theoretic steps are stated over an
abstract ring, so no term of the scheme-level vocabulary is ever in the goal of a rewrite.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- A linear map has image the kernel of a second one as soon as the two agree elementwise:
an element is in the image of the first exactly when the second kills it. The hypothesis
mentions no submodule, so it may be supplied by a pair of maps linear over a different ring
with the same underlying functions. -/
theorem LinearMap.range_eq_ker_of_forall_mem_iff {R M N P : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (u : M →ₗ[R] N)
    (p : N →ₗ[R] P) (h : ∀ n : N, (∃ m, u m = n) ↔ p n = 0) :
    LinearMap.range u = LinearMap.ker p :=
  SetLike.ext fun n => LinearMap.mem_range.trans ((h n).trans LinearMap.mem_ker.symm)

/-- The target of a surjective linear map whose kernel is the image of a second map has the
length of the quotient by that image. -/
theorem Module.length_eq_length_quotient_range_of_surjective {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (u : M →ₗ[R] N) (p : N →ₗ[R] P) (hp : Function.Surjective p)
    (h : LinearMap.range u = LinearMap.ker p) :
    Module.length R P = Module.length R (N ⧸ LinearMap.range u) :=
  (((Submodule.quotEquivOfEq _ _ h).trans (p.quotKerEquivOfSurjective hp)).length_eq).symm

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F G : X.Modules} (a : F ⟶ G) (x : X)

/-- **The stalk sequence of a cokernel is exact.** The image of the stalk map of `a` is the
kernel of the stalk map of the projection to `cokernel a`.

Exactness is read off the categorical stalk functor, whose modules are taken over the stalk of
the structure sheaf in `RingCat`; the elementwise hypothesis of
`LinearMap.range_eq_ker_of_forall_mem_iff` carries it over to
`AlgebraicGeometry.stalkLinearMap`, which is linear over the stalk in `CommRingCat`. -/
theorem range_stalkLinearMap_eq_ker_cokernelπ :
    LinearMap.range (stalkLinearMap F G a x) =
      LinearMap.ker (stalkLinearMap G (cokernel a) (cokernel.π a) x) := by
  have hS : (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) a (cokernel.π a)
      (cokernel.condition a)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel a)
  have hRK := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).mp hS x)
  exact LinearMap.range_eq_ker_of_forall_mem_iff _ _ fun n =>
    ⟨fun ⟨m, hm⟩ => hRK.le ⟨m, hm⟩, fun hn => hRK.ge hn⟩

/-- The stalk map of the projection to a cokernel is surjective: the projection is an
epimorphism, and epimorphy of sheaves of modules is surjectivity on every stalk. -/
theorem surjective_stalkLinearMap_cokernelπ :
    Function.Surjective (stalkLinearMap G (cokernel a) (cokernel.π a) x) :=
  (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := X.ringCatSheaf) (cokernel.π a)).mp (epi_sheafOfModules (cokernel.π a)) x

/-- **The stalk of a cokernel is a quotient of the stalk.** Its length over the local ring is
the length of the quotient of the stalk of the target by the image of the stalk map. -/
theorem length_stalk_cokernel :
    Module.length (X.presheaf.stalk x) ((cokernel a).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x)
        (G.presheaf.stalk x ⧸ LinearMap.range (stalkLinearMap F G a x)) :=
  Module.length_eq_length_quotient_range_of_surjective _ _
    (surjective_stalkLinearMap_cokernelπ a x) (range_stalkLinearMap_eq_ker_cokernelπ a x)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

/-- **The multiplicity of a cokernel.** The multiplicity of `cokernel a` at `x` is the length
of the quotient of the stalk of the target of `a` by the image of the stalk map of `a`. -/
theorem sheafMultiplicity_cokernel {X : Scheme.{u}} {F G : X.Modules} (a : F ⟶ G) (x : X) :
    sheafMultiplicity (cokernel a) x =
      (Module.length (X.presheaf.stalk x)
        (G.presheaf.stalk x ⧸ LinearMap.range (stalkLinearMap F G a x))).toNat := by
  rw [sheafMultiplicity]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (Scheme.Modules.length_stalk_cokernel a x)

end Stacks.Chow
