/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Basic
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# Base change of a quotient of a module on `ℙⁿ_T`

For `g : T' ⟶ T`, a module `G` on `ℙⁿ_T`, a module `G'` on `ℙⁿ_{T'}` identified with the inverse
image of `G` along `ℙⁿ_{T'} ⟶ ℙⁿ_T` by `e : G' ≅ g^* G`, and a submodule `K ⊆ G`, the base change
of the quotient `G ⟶ G / K` (Stacks 09TR) is the quotient `G' ≅ g^* G ⟶ g^*(G / K)`; it is recorded
by its kernel, a submodule of `G'`.  This is `AlgebraicGeometry.ProjectiveQuot.baseChange` for an
arbitrary module in place of `𝒪^{⊕ r}` and an arbitrary identification `e`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.subobjectPullback g e K`: the base change of `K`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.subobjectPullbackCokernelIso`: its quotient is the
  inverse image of `G / K`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {n : ℕ} {T' T : Scheme.{u}} (g : T' ⟶ T) {G : (projectiveSpaceOver n T).Modules}
  {G' : (projectiveSpaceOver n T').Modules}
  (e : G' ≅ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G) (K : Subobject G)

/-- The pulled-back quotient map `G' ≅ g^* G ⟶ g^*(G / K)`. -/
abbrev subobjectPullbackProjection :
    G' ⟶ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (cokernel K.arrow) :=
  e.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (cokernel.π K.arrow)

/-- The pulled-back quotient map `G' ⟶ g^*(G / K)` is an epimorphism. -/
instance epi_subobjectPullbackProjection : Epi (subobjectPullbackProjection g e K) := by
  unfold subobjectPullbackProjection
  infer_instance

/-- **The base change of a submodule `K ⊆ G` along `ℙⁿ_{T'} ⟶ ℙⁿ_T`, read on `G' ≅ g^* G`**: the
kernel of `G' ≅ g^* G ⟶ g^*(G / K)`. -/
def subobjectPullback : Subobject G' :=
  kernelSubobject (e.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
    (cokernel.π K.arrow))

/-- **The quotient by the base change is the inverse image of the quotient**:
`G' / K' ≅ g^*(G/K)`. -/
def subobjectPullbackCokernelIso :
    cokernel (subobjectPullback g e K).arrow ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (cokernel K.arrow) :=
  Abelian.cokernelKernelSubobjectIso (subobjectPullbackProjection g e K)

/-- The projection onto the quotient by the base change is the pulled-back quotient map, read
through `AlgebraicGeometry.ProjectiveQuotOverSpace.subobjectPullbackCokernelIso`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_subobjectPullbackCokernelIso_hom :
    cokernel.π (subobjectPullback g e K).arrow ≫ (subobjectPullbackCokernelIso g e K).hom =
      e.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (cokernel.π K.arrow) := by
  dsimp only [subobjectPullbackCokernelIso, subobjectPullback]
  rw [← Abelian.cokernelKernelSubobjectIso_inv_comp (subobjectPullbackProjection g e K)]
  simp

/-- The base change does not depend on the identification beyond its value: equal maps
`G' ⟶ g^*(G / K)` give equal kernels. -/
theorem subobjectPullback_eq_kernelSubobject {Q : (projectiveSpaceOver n T').Modules}
    (p : G' ⟶ Q)
    (i : (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (cokernel K.arrow) ⟶ Q)
    [Mono i] (h : subobjectPullbackProjection g e K ≫ i = p) :
    subobjectPullback g e K = kernelSubobject p :=
  (kernelSubobject_eq_of_comp_mono _ p i h).symm

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
