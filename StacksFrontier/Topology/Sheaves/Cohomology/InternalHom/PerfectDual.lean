module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a perfect object on a ringed space

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of the derived category
`D(O_X)` of sheaves of `O_X`-modules. The **dual** of `K` is `K^∨ = RSheafHom(K, O_X)`
(`Stacks.SheafOfModules.derivedDual`), the derived internal Hom into the structure sheaf placed
in degree zero. This file proves that `K^∨` is again perfect.

A topological space with a sheaf of commutative rings *is* a ringed site, namely its site of
opens with the open-cover topology, so the statement is the ringed-site one read off along
`Stacks.SheafOfModules.ringedSite`, exactly as the dual itself and the canonical map
`M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)` are in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual`.

## Main results

* `Stacks.SheafOfModules.isPerfect_derivedDual`: the dual of a perfect object of `D(O_X)` is
  perfect.
* `Stacks.SheafOfModules.isStrictlyPerfect_sheafHomComplex_structureSheaf`: the underlying
  computation, that the internal Hom complex `SheafHom(E, O_X[0])` of a strictly perfect complex
  of `O_X`-modules is again strictly perfect.
* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_dual`: the dual `Hom_{O_X}(M, O_X)` of a
  direct summand of a finite free `O_X`-module is again a direct summand of a finite free
  module.
* `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap`: whenever the
  canonical map `M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)` of Stacks 08I1 is invertible, the induced
  map `H⁰(X, M ⊗^L_{O_X} K^∨) ⟶ Hom_{D(O_X)}(K, M)` is bijective.

## Implementation notes

Perfectness is `AlgebraicGeometry.RingedSite.IsPerfect` at the site of opens, which is the
open-cover condition of the source: every open admits a covering over each member of which the
restriction of a representative is quasi-isomorphic to a strictly perfect complex.

`bijective_derivedTensorDualGlobalSectionsMap` takes the invertibility of the canonical map as a
hypothesis `h` rather than an instance, and hands it over positionally: the global-sections
functor is a functor out of
`DerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Rc))`, i.e. out of the
`Tensor.ringSheaf` spelling, while `h` is stated at `StructureSheafModules Rc`, i.e. the
`structureSheaf` one. The two agree only after unfolding `CategoryTheory.sheafCompose`, a plain
`def`: elaboration unfolds it, so `.map` accepts the morphism, but instance synthesis does not, so
a bare `Functor.map_isIso _ _` cannot find `h` in the local context. Calling it as
`@Functor.map_isIso _ _ _ _ _ _ _ _ h` puts `h` in the instance slot itself, where the check is a
defeq one at default transparency and the gap closes. The functor applied second needs no such
care: its argument is the `let`-bound `g`, so the `IsIso g` just proved is at the spelling asked
for.

The space, its rings and the sections of its modules lie on the diagonal at a free universe
`u`, which is the pin of the ringed-site statement being read off here and the one the other
three assertions of the tag are stated at: the derived internal Hom cluster forces the module
universe to be the universe of the sections of the internal Hom sheaf, and the perfectness
cluster forces it to be the universe of the sections of the structure sheaf, so all three
coincide — but at no particular value.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual of a direct summand of a finite free module is again one.** If `M` is a retract
of `O_X^{⊕n}`, applying the contravariant functor `Hom_{O_X}(-, O_X)` makes `Hom_{O_X}(M, O_X)`
a retract of `Hom_{O_X}(O_X^{⊕n}, O_X) ≅ O_X^{⊕n}`. -/
theorem isDirectSummandOfFiniteFree_dual (M : StructureSheafModules Rc)
    (hM : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Rc) M) :
    IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Rc)
      (RingedSite.internalHomSheaf (ringedSite Rc) M
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc))) :=
  RingedSite.isDirectSummandOfFiniteFree_internalHomSheaf_unit (ringedSite Rc) M hM

/-- **The dual of a strictly perfect complex is strictly perfect.** The internal Hom complex
`SheafHom(E, O_X[0])` of a strictly perfect complex `E` of `O_X`-modules into the structure
sheaf placed in degree zero is again strictly perfect: its degree-`n` term is the dual of
`E^{-n}`. -/
theorem isStrictlyPerfect_sheafHomComplex_structureSheaf
    (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Rc) E) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Rc)
      (RingedSite.sheafHomComplex (ringedSite Rc) E
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj :=
  RingedSite.isStrictlyPerfect_sheafHomComplex_structureSheaf (ringedSite Rc) E hE

section GlobalSections

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- Whenever the canonical map `M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)` of Stacks 08I1 is invertible,
the induced map of abelian groups `H⁰(X, M ⊗^L_{O_X} K^∨) ⟶ Hom_{D(O_X)}(K, M)` is bijective:
the induced map is the degree-zero global hypercohomology of the canonical map followed by the
identification `H⁰(X, RSheafHom(K, M)) ≅ Hom_{D(O_X)}(K, M)`, and both factors are then
bijections. -/
theorem bijective_derivedTensorDualGlobalSectionsMap
    (K M : DerivedCategory (StructureSheafModules Rc))
    (h : IsIso (derivedTensorDualToSheafHom Rc K M)) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap Rc K M) := by
  let g := (derivedModuleGlobalSections (ringedSite Rc)).map (derivedTensorDualToSheafHom Rc K M)
  have : IsIso g := @Functor.map_isIso _ _ _ _ _ _ _ _ h
  let z := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map g
  have : IsIso z := Functor.map_isIso _ _
  have hz : Function.Bijective (fun w => z w) := ConcreteCategory.bijective_of_isIso z
  exact (derivedSheafHomGlobalSectionsEquiv Rc K M).bijective.comp hz

end GlobalSections

variable
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X,
    ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 08DQ, first assertion.** Let `(X, O_X)` be a ringed space and let `K` be a perfect
object of `D(O_X)`. Then the dual `K^∨ = RSheafHom(K, O_X)` is perfect as well.

Perfectness is local, so it is enough to model `K^∨` above a covering of each open. Over a
member `V` on which `K` is modelled by a strictly perfect complex `E`, the restriction of `K^∨`
is `RSheafHom(K|_V, O_V)`, which is the class of the internal Hom complex `SheafHom(E, O_V)`;
and that complex is strictly perfect because the dual of a direct summand of a finite free
module is again one. -/
@[stacks 08DQ "the dual of a perfect object is perfect"]
theorem isPerfect_derivedDual (K : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    (ringedSite Rc).IsPerfect (derivedDual Rc K) :=
  RingedSite.isPerfect_derivedDual (ringedSite Rc) K hK

end Stacks.SheafOfModules

end
