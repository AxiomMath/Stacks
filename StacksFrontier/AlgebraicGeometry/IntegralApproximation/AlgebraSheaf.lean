module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral algebra sheaves

An algebra sheaf `A` over a scheme `X`, in the sense of
`Stacks.RelativeSpec.AlgebraSheaf`, is *integral* when its structural ring map
`Γ(X, U) → A(U)` is integral for every affine open `U` of `X`.  This is the hypothesis of
[Stacks, Tag 0817].

The file records the definition and the one elementary consequence of it that the approximation
theorem of tag 0817 uses: on an affine open, integral sections which are of finite type over the
structure sheaf are already module-finite.  That is the sectionwise form of [Stacks, Tag 02JJ],
and is what makes "finite type quasi-coherent subalgebra" and "finite quasi-coherent subalgebra"
the same condition for an integral algebra sheaf.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral`: integrality of an algebra sheaf, tested on
  affine opens.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.finite_app_of_finiteType`: integral plus finite
  type implies finite, on the sections over an affine open.
* `Stacks.RelativeSpec.AlgebraSheaf.isIntegral_app_of_injective` and
  `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.of_injective`: an algebra sheaf mapping into an
  integral algebra sheaf injectively on sections is itself integral.
* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.finite_app_of_finiteType_of_injective`:
  consequently a subalgebra of an integral algebra sheaf which is of finite type is finite,
  which is the step the proof of [Stacks, Tag 0817] (1) takes before invoking the directed
  colimit decomposition of [Stacks, Tag 05JT].

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
-/

@[expose] public section

open AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-- An algebra sheaf is *integral* when its structural ring map is integral on the sections over
every affine open. -/
def IsIntegral (A : AlgebraSheaf X) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → RingHom.IsIntegral (A.hom.hom.app (op U)).hom

/-- On the sections over an affine open, an integral structural ring map which is of finite type
is module-finite.  This is [Stacks, Tag 02JJ] applied to the sections of an integral algebra
sheaf. -/
theorem IsIntegral.finite_app_of_finiteType {A : AlgebraSheaf X} (hA : A.IsIntegral)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : RingHom.FiniteType (A.hom.hom.app (op U)).hom) :
    RingHom.Finite (A.hom.hom.app (op U)).hom :=
  (hA U hU).to_finite h

/-- The structure morphism of an algebra sheaf factors the structure morphism of any algebra
sheaf it maps to: for `φ : B ⟶ A` the triangle of ring maps
`Γ(X, U) → B(U) → A(U)` composes to the structure map of `A` at `U`. -/
theorem app_comp_app {A B : AlgebraSheaf X} (φ : B ⟶ A) (U : X.Opens) :
    (φ.right.hom.app (op U)).hom.comp (B.hom.hom.app (op U)).hom =
      (A.hom.hom.app (op U)).hom := by
  have heq := congrArg (fun k : X.sheaf ⟶ A.right => (k.hom.app (op U)).hom) φ.w
  exact heq

/-- An algebra sheaf which maps into an integral algebra sheaf by a map that is injective on
the sections over `U` has integral structure map on the sections over `U`.

This is the step the proof of [Stacks, Tag 0817] (1) takes before applying [Stacks, Tag 02JJ]:
a subalgebra of an integral algebra is integral. -/
theorem isIntegral_app_of_injective {A B : AlgebraSheaf X} (φ : B ⟶ A) (U : X.Opens)
    (hinj : Function.Injective (φ.right.hom.app (op U)).hom)
    (hA : RingHom.IsIntegral (A.hom.hom.app (op U)).hom) :
    RingHom.IsIntegral (B.hom.hom.app (op U)).hom :=
  RingHom.IsIntegral.tower_bot _ _ hinj (by rw [app_comp_app]; exact hA)

/-- An algebra sheaf which maps into an integral algebra sheaf by a map that is injective on
sections over every open is itself integral. -/
theorem IsIntegral.of_injective {A B : AlgebraSheaf X} (hA : A.IsIntegral) (φ : B ⟶ A)
    (hinj : ∀ U : X.Opens, Function.Injective (φ.right.hom.app (op U)).hom) :
    B.IsIntegral :=
  fun U hU => isIntegral_app_of_injective φ U (hinj U) (hA U hU)

/-- A subalgebra of an integral algebra sheaf which is of finite type over the structure sheaf
is finite over it, on the sections over an affine open.  Together with the directed colimit
decomposition of [Stacks, Tag 05JT] this is what makes [Stacks, Tag 0817] (1) say that an
integral quasi-coherent algebra is the directed colimit of its *finite* quasi-coherent
subalgebras rather than of its finite type ones. -/
theorem IsIntegral.finite_app_of_finiteType_of_injective {A B : AlgebraSheaf X}
    (hA : A.IsIntegral) (φ : B ⟶ A) {U : X.Opens} (hU : IsAffineOpen U)
    (hinj : Function.Injective (φ.right.hom.app (op U)).hom)
    (h : RingHom.FiniteType (B.hom.hom.app (op U)).hom) :
    RingHom.Finite (B.hom.hom.app (op U)).hom :=
  (isIntegral_app_of_injective φ U hinj (hA U hU)).to_finite h

end Stacks.RelativeSpec.AlgebraSheaf
