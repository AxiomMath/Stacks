module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of locally constant sheaves of modules on the small étale site

Let `X` be a scheme and let `Λ` be a commutative ring. The tensor product of two locally
constant sheaves of `Λ`-modules on `X_étale` is again a locally constant sheaf of `Λ`-modules.
This is Stacks 095D, and it is the small étale site instance of the statement for an arbitrary
site, Stacks 093V; the source proves it exactly that way.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstant_tensor_smallEtale` — Stacks 095D.

## Implementation notes

A sheaf of `Λ`-modules on `X_étale` is an object of
`Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{w} Λ)`, as everywhere else in this library
(compare the three parts of Tag 093Q and Tag 095C), and local constancy is the site-level
predicate `Stacks.ConstantSheaf.IsLocallyConstant` of Tag 093Q (2): every object of the small
étale site admits an étale covering on each member of which the restricted sheaf is constant.
The source imposes no finiteness and no freeness condition on the local values here, and none
is imposed below. The tensor product is the one of `CategoryTheory.Sheaf.monoidalCategory`,
which Mathlib does not make an instance, so it is activated as a local instance as in the
general-site statement.

Three hypotheses appear which the source does not state, and all three are already carried by
the general-site Tag 093V: sheafification on `X_étale` and on its slice sites, which is what
makes the tensor product and the local constancy predicate expressible at all, and the size
condition `UnivLE.{u + 1, w}` relating the coefficient universe to the universe of the site —
the general statement's `UnivLE.{max u v, w}` for a site in `Type (u + 1)` with morphisms in
`Type u`. The abelian part of Tag 095C carries the same size condition for the same reason.

The two sheafification hypotheses are kept as hypotheses, as in Tag 095C, rather than resolved
by the two theorems below, so that the statement applies to whichever sheafification a caller has
in scope. That they are satisfiable — so that the statement is not vacuous — is
`hasSheafify_smallEtale_moduleCat` and `hasSheafify_smallEtale_over_moduleCat`, which discharge
both of them from the size condition alone. They are deliberately not instances, so as not to
compete with the sheafification instances the small étale site already carries at the diagonal
universe.

## References

* [Stacks Project, Tag 095D](https://stacks.math.columbia.edu/tag/095D)
* [Stacks Project, Tag 093V](https://stacks.math.columbia.edu/tag/093V)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.ConstantSheaf

attribute [local instance] Sheaf.monoidalCategory

/-- **Stacks 095D.** The tensor product of two locally constant sheaves of `Λ`-modules on the
small étale site of a scheme is a locally constant sheaf of `Λ`-modules. -/
@[stacks 095D, sga "5 VI 1.4.5" "locally constant claim"]
theorem isLocallyConstant_tensor_smallEtale {X : Scheme.{u}} (Λ : Type w) [CommRing Λ]
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (smallEtaleTopology X) (ModuleCat.{w} Λ)]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{w} Λ)]
    (F G : Sheaf (smallEtaleTopology X) (ModuleCat.{w} Λ))
    [IsLocallyConstant (smallEtaleTopology X) F]
    [IsLocallyConstant (smallEtaleTopology X) G] :
    IsLocallyConstant (smallEtaleTopology X) (F ⊗ G) :=
  isLocallyConstant_tensor (smallEtaleTopology X) Λ F G

/-- The size condition of `isLocallyConstant_tensor_smallEtale` already provides sheafification
of presheaves of `Λ`-modules on the small étale site of a scheme. -/
theorem hasSheafify_smallEtale_moduleCat (X : Scheme.{u}) (Λ : Type w) [CommRing Λ]
    [UnivLE.{u + 1, w}] : HasSheafify (smallEtaleTopology X) (ModuleCat.{w} Λ) :=
  hasSheafify_moduleCat_of_univLE.{u + 1, u, w, w} (smallEtaleTopology X) Λ

/-- The same on each slice of the small étale site of a scheme. -/
theorem hasSheafify_smallEtale_over_moduleCat (X : Scheme.{u}) (Λ : Type w) [CommRing Λ]
    [UnivLE.{u + 1, w}] (U : X.Etale) :
    HasSheafify ((smallEtaleTopology X).over U) (ModuleCat.{w} Λ) :=
  hasSheafify_moduleCat_of_univLE.{u + 1, u, w, w} ((smallEtaleTopology X).over U) Λ

end Stacks.ConstantSheaf

end
