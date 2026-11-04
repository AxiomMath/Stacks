module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Pseudofunctor
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StackReduction
public import StacksFrontier.CategoryTheory.Sites.Descent.SubPseudofunctorDescentData
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Stacks 023T as a single stack condition on the quasi-coherent sub-pseudofunctor

Stacks 023T says that for an fpqc covering family `f i : X i ⟶ S` of a scheme, every
quasi-coherent descent datum is effective and the canonical descent functor from the
quasi-coherent modules on `S` is fully faithful.  Both halves are assertions about
`AlgebraicGeometry.canonicalDescentFunctor`, a functor between *full subcategories*: the
quasi-coherent modules inside all sheaves of modules, and the quasi-coherent descent data inside
all descent data for `AlgebraicGeometry.modulePullbackPseudofunctor`.

This file identifies that functor with the canonical descent functor of a pseudofunctor in its
own right — the sub-pseudofunctor of `AlgebraicGeometry.modulePullbackPseudofunctor` on the
quasi-coherent objects — and so turns both halves of 023T into consequences of the single
condition that this sub-pseudofunctor is a stack for the fpqc topology.

The two objects the reduction is phrased in are taken from elsewhere in the library:
`Stacks.Descent.quasicoherentProperty`, quasi-coherence as a property of objects of
`AlgebraicGeometry.modulePullbackPseudofunctor`, and `Stacks.Descent.qcohPseudofunctor`, the
sub-pseudofunctor it cuts out, which sends a scheme to its category of quasi-coherent modules and
a morphism of schemes to pullback.

## Main results

* `Stacks.Descent.quasicoherentDescentData_eq`: the quasi-coherent descent data of Stacks 023B
  are exactly the descent data of `AlgebraicGeometry.modulePullbackPseudofunctor` with
  quasi-coherent components, in the sense of
  `Stacks.Descent.subDescentDataProp`.
* `Stacks.Descent.toDescentData_comp_eq_canonicalDescentFunctor`: the canonical descent functor
  of `Stacks.Descent.qcohPseudofunctor`, read through that identification, is the canonical
  descent functor of Stacks 023D.
* `Stacks.Descent.isEquivalence_canonicalDescentFunctor_of_isStack`: if
  `Stacks.Descent.qcohPseudofunctor` is an fpqc stack, then for an fpqc covering family the
  canonical descent functor is an equivalence.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isStack` is the full
  faithfulness half of Stacks 023T under that hypothesis; the effectivity half is
  `Stacks.Descent.isEffective_of_isStack`.
* `Stacks.Descent.isStack_qcohPseudofunctor_of_isStackFor` of
  `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Pseudofunctor`, imported here, reduces the
  hypothesis from covering
  sieves to the presieves of `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

## Implementation notes

The sub-pseudofunctor is Mathlib's
`CategoryTheory.Pseudofunctor.ObjectProperty.fullsubcategory`, and the comparison of its descent
data with the quasi-coherent descent data of Stacks 023B is
`Stacks.Descent.subDescentDataFunctor`, an isomorphism of categories.  Both identifications in
this file hold by `rfl`, but only one of them may be *written* as `rfl`: see the implementation
notes of `StacksFrontier.CategoryTheory.Sites.Descent.SubPseudofunctorDescentData`.  Concretely,
`quasicoherentDescentData_eq` is an equality of types and is cheap, whereas
`toDescentData_comp_eq_canonicalDescentFunctor` is an equality of functors between categories of
`AlgebraicGeometry.Scheme.Modules`, and proving it by `rfl` here exhausts the kernel's heartbeat
budget; it is obtained instead by instantiating the generic
`Stacks.Descent.toDescentData_comp_subDescentDataFunctor`, which costs nothing.

Routing 023T through the quasi-coherent sub-pseudofunctor rather than through
`AlgebraicGeometry.modulePullbackPseudofunctor` itself is what removes the extra hypothesis
carried by `Stacks.Descent.isEffective_of_essImage`, namely that quasi-coherence descends along
the family.  Essential surjectivity of the canonical descent functor *of the sub-pseudofunctor*
produces a quasi-coherent module on the base directly, so no such hypothesis is needed — which
matters, because Stacks 023T does not have one.  It also avoids asking for descent of arbitrary
sheaves of modules along an fpqc covering, which is a strictly stronger assertion than 023T.

No Stacks tag is claimed.  The hypothesis
`CategoryTheory.Pseudofunctor.IsStack Stacks.Descent.qcohPseudofunctor
AlgebraicGeometry.Scheme.fpqcTopology` is not proved here and is the whole mathematical content
of 023T; tagging a theorem that assumes it would be tagging the reduction, not the result.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Bicategory CategoryTheory.Pseudofunctor

universe v u

namespace Stacks.Descent

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- The quasi-coherent descent data of Stacks 023B are the descent data for
`AlgebraicGeometry.modulePullbackPseudofunctor` all of whose components are quasi-coherent. -/
theorem quasicoherentDescentData_eq :
    QuasicoherentDescentData f = (subDescentDataProp quasicoherentProperty f).FullSubcategory := rfl

/-- **The canonical descent functor of the quasi-coherent sub-pseudofunctor is the canonical
descent functor of Stacks 023D.**  Composing
`CategoryTheory.Pseudofunctor.toDescentData` for `Stacks.Descent.qcohPseudofunctor` with the
comparison of `StacksFrontier.CategoryTheory.Sites.Descent.SubPseudofunctorDescentData` gives
`AlgebraicGeometry.canonicalDescentFunctor`. -/
theorem toDescentData_comp_eq_canonicalDescentFunctor :
    (qcohPseudofunctor.{u}).toDescentData f ⋙ subDescentDataFunctor (quasicoherentProperty.{u}) f =
      canonicalDescentFunctor f :=
  toDescentData_comp_subDescentDataFunctor quasicoherentProperty f

/-- **The canonical descent functor is an equivalence along an fpqc covering, granted that the
quasi-coherent sub-pseudofunctor is an fpqc stack.**  This is both halves of Stacks 023T at
once: full faithfulness is `CategoryTheory.Functor.Full` together with
`CategoryTheory.Functor.Faithful`, and effectivity of every datum is
`CategoryTheory.Functor.EssSurj`. -/
theorem isEquivalence_canonicalDescentFunctor_of_isStack
    [(qcohPseudofunctor.{u}).IsStack Scheme.fpqcTopology.{u}]
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (canonicalDescentFunctor f).IsEquivalence := by
  have h : ((qcohPseudofunctor.{u}).toDescentData f).IsEquivalence :=
    (qcohPseudofunctor.{u}).isEquivalence_toDescentData f
      (sieve_ofArrows_mem_fpqcTopology hfpqc)
  rw [← toDescentData_comp_eq_canonicalDescentFunctor f]
  exact (((qcohPseudofunctor.{u}).toDescentData f).asEquivalence.trans
    (subDescentDataEquivalence (quasicoherentProperty.{u}) f)).isEquivalence_functor

/-- **The full-faithfulness half of Stacks 023T, granted the fpqc stack condition on the
quasi-coherent sub-pseudofunctor.**  For an fpqc covering family the canonical descent functor
from the quasi-coherent modules on the base to the quasi-coherent descent data is fully
faithful. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_isStack
    [(qcohPseudofunctor.{u}).IsStack Scheme.fpqcTopology.{u}]
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful := by
  have := isEquivalence_canonicalDescentFunctor_of_isStack f hfpqc
  exact ⟨.ofFullyFaithful _⟩

end Stacks.Descent

end
