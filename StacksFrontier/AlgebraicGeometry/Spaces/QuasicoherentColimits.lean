module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Arbitrary colimits of quasi-coherent modules, reduced to direct sums and cokernels

Stacks 03M1 asserts six closure properties of the quasi-coherent modules on an algebraic space
inside all modules.  This file proves that the *second* of them, closure under arbitrary
colimits, is a formal consequence of the *first* and the cokernel half of the *third*: a
colimit is a cokernel of a map between two direct sums of the terms of the diagram, so an
object property closed under direct sums and under cokernels is closed under colimits of every
shape.

No geometry is used, and the reduction is carried out for an arbitrary property of objects of
an arbitrary preadditive category; the geometric statements are instantiations of it.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_small`: a property of objects
  of a preadditive category with cokernels, closed under isomorphisms, under cokernels and
  under the two relevant coproducts, is closed under colimits of a given *small* shape.
* `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_coproducts`: the same with the
  shape category's objects and morphisms in independent universes.
* `SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_coproducts`:
  quasi-coherence of sheaves of modules on a site is closed under colimits of a given shape as
  soon as it is closed under direct sums and under cokernels.
* `SheafOfModules.IsQuasicoherentOnSite.colimit`: the same conclusion stated for one diagram.
* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves` and
  `AlgebraicGeometry.Space.isQuasicoherent_colimit`: **the colimit clause of Stacks 03M1 for an
  algebraic space, reduced to its direct-sum clause and its cokernel clause.**

## Implementation notes

The colimit of `D : K ⥤ C` is the coequalizer of the two canonical maps

`∐_{(f : j ⟶ k)} D j ⟶ ∐_k D k`,

which is Mathlib's `CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproduct`; in a
preadditive category that coequalizer is the cokernel of the difference of the two maps, by
`CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork`.  So both coproducts and one
cokernel suffice, and nothing about the shape `K` beyond the existence of those coproducts is
needed.

Mathlib's construction is stated for a `CategoryTheory.SmallCategory` shape, that is, for a
shape whose morphisms live in the universe of its objects.  The shape of the colimit clause of
Stacks 03M1 has independent universes, so the general statement is obtained from the small one
by transporting along `CategoryTheory.AsSmall.equiv`, which replaces `K` by an equivalent
small category with objects and morphisms in `Type (max w w')`.  The index types of the two
coproducts then also live in `Type (max w w')`, which is why the direct-sum hypothesis is
asked for every index type of that universe: an arbitrary direct sum is exactly what Stacks
03M1(1) provides, and no refinement of coverings is involved here.

The existence of the coproducts and of the cokernels is a hypothesis, not a theorem: the
category of sheaves of modules on a site has them only when presheaves of abelian groups in
the module universe can be sheafified, which for the small étale site of an algebraic space
over `Scheme.{u}` happens at the module universe `u` and at every module universe at least
`u + 1`, by `AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat` and
`AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`.  The
module universe itself stays free throughout.

No `@[stacks 03M1]` attribute is carried.  Every statement about quasi-coherence below is
conditional on the direct-sum and cokernel clauses of that same tag, neither of which is
available in either tree: the cokernel clause exists only as the undischarged typeclass
hypothesis `(SheafOfModules.isQuasicoherentOnSite _).IsClosedUnderCokernels` of
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure`, and the direct-sum clause
is not proved anywhere — `AlgebraicGeometry.Space.isClosedUnderFiniteProducts_quasicoherentSheaves`
reaches only *finite* direct sums, and only conditionally.  What is new here is that the colimit
clause needs nothing beyond those two.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 002P](https://stacks.math.columbia.edu/tag/002P)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v r m w w'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]

/-- A property of objects of a preadditive category with cokernels, closed under isomorphisms,
under cokernels, and under the coproducts indexed by the objects and by the morphisms of a
small category `K`, is closed under colimits of shape `K`.

The colimit of a diagram is the coequalizer of the two canonical maps from the coproduct over
the morphisms to the coproduct over the objects, and in a preadditive category that
coequalizer is the cokernel of their difference. -/
theorem isClosedUnderColimitsOfShape_of_small (K : Type w) [SmallCategory K]
    [HasColimitsOfShape (Discrete K) C]
    [HasColimitsOfShape (Discrete (Σ p : K × K, p.1 ⟶ p.2)) C]
    [P.IsClosedUnderColimitsOfShape (Discrete K)]
    [P.IsClosedUnderColimitsOfShape (Discrete (Σ p : K × K, p.1 ⟶ p.2))] :
    P.IsClosedUnderColimitsOfShape K := by
  have : HasCoequalizers C := hasCoequalizers_of_hasCokernels
  refine IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨D, hD⟩
  have h1 : P (∐ fun f : Σ p : K × K, p.1 ⟶ p.2 => D.obj f.1.1) :=
    P.prop_colimit (Discrete.functor _) fun _ ↦ hD _
  have h2 : P (∐ fun k ↦ D.obj k) := P.prop_colimit (Discrete.functor _) fun _ ↦ hD _
  set s : (∐ fun f : Σ p : K × K, p.1 ⟶ p.2 => D.obj f.1.1) ⟶ (∐ fun k ↦ D.obj k) :=
    Sigma.desc fun f ↦ D.map f.2 ≫ colimit.ι (Discrete.functor D.obj) ⟨f.1.2⟩ with hsdef
  set t : (∐ fun f : Σ p : K × K, p.1 ⟶ p.2 => D.obj f.1.1) ⟶ (∐ fun k ↦ D.obj k) :=
    Sigma.desc fun f ↦ colimit.ι (Discrete.functor D.obj) ⟨f.1.1⟩ with htdef
  have h3 : P (cokernel (s - t)) := P.prop_cokernel _ h1 h2
  have e1 : colimit D ≅ coequalizer s t :=
    colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct D)
  have e2 : coequalizer s t ≅ cokernel (s - t) :=
    IsColimit.coconePointUniqueUpToIso (coequalizerIsCoequalizer s t)
      (isColimitCoforkOfCokernelCofork (cokernelIsCokernel (s - t)))
  exact P.prop_of_iso (e1.trans e2).symm h3

/-- A property of objects of a preadditive category with cokernels, closed under isomorphisms,
under cokernels and under arbitrary coproducts, is closed under colimits of any shape whose
objects and morphisms live in the universes of the coproducts.

The shape is replaced by the equivalent small category `CategoryTheory.AsSmall`, for which
`CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_small` applies. -/
theorem isClosedUnderColimitsOfShape_of_coproducts (K : Type w) [Category.{w'} K]
    [HasCoproducts.{max w w'} C]
    (hsum : ∀ I : Type (max w w'), P.IsClosedUnderColimitsOfShape (Discrete I)) :
    P.IsClosedUnderColimitsOfShape K := by
  have h1 := hsum (AsSmall.{w} K)
  have h2 := hsum (Σ p : AsSmall.{w} K × AsSmall.{w} K, p.1 ⟶ p.2)
  have h3 := isClosedUnderColimitsOfShape_of_small P (AsSmall.{w} K)
  exact IsClosedUnderColimitsOfShape.of_equivalence (AsSmall.equiv.symm (C := K))

end CategoryTheory.ObjectProperty

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

variable (R) in
/-- **The colimit clause of Stacks 03M1 on a site, reduced to its direct-sum clause and its
cokernel clause.**  Quasi-coherence of sheaves of modules on a site is closed under colimits
of a given shape as soon as it is closed under arbitrary direct sums and under cokernels.

The hypotheses are closure properties of quasi-coherence itself, which is what distinguishes
this from `SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer`: that one is
Stacks 0GNC and asks instead for the quasi-coherent modules to be the essential image of a
colimit-preserving fully faithful functor. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_coproducts
    (K : Type w) [Category.{w'} K]
    [HasCoproducts.{max w w'} (SheafOfModules.{m} R)]
    (hsum : ∀ I : Type (max w w'),
      (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape (Discrete I))
    (hcoker : (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape K :=
  have := hcoker
  ObjectProperty.isClosedUnderColimitsOfShape_of_coproducts _ K hsum

/-- **The colimit clause of Stacks 03M1 on a site, for one diagram.**  A colimit of
quasi-coherent sheaves of modules on a site is quasi-coherent, as soon as quasi-coherence is
closed under arbitrary direct sums and under cokernels. -/
theorem IsQuasicoherentOnSite.colimit {K : Type w} [Category.{w'} K]
    [HasCoproducts.{max w w'} (SheafOfModules.{m} R)]
    (hsum : ∀ I : Type (max w w'),
      (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape (Discrete I))
    (hcoker : (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels)
    (D : K ⥤ SheafOfModules.{m} R) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (Limits.colimit D).IsQuasicoherentOnSite :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_coproducts R K hsum hcoker
  ObjectProperty.prop_colimit _ D hD

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section Colimits

variable [HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
  [((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 03M1, colimits, on an algebraic space, reduced to the direct-sum and cokernel
clauses of the same tag.**  Quasi-coherence of `𝒪_F`-modules is closed under colimits of a
given shape as soon as it is closed under arbitrary direct sums and under cokernels.

This is the `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure`
hypothesis `hfc`, for an arbitrary shape rather than only a filtered one. -/
theorem isClosedUnderColimitsOfShape_quasicoherentSheaves (K : Type w) [Category.{w'} K]
    [HasCoproducts.{max w w'} (Modules.{u, m} B S hS F hF)]
    (hsum : ∀ I : Type (max w w'),
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape (Discrete I))
    (hcoker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape K :=
  SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite_of_coproducts _ K hsum
    hcoker

/-- **Stacks 03M1, colimits, on an algebraic space, reduced to the direct-sum and cokernel
clauses of the same tag.**  A colimit of quasi-coherent `𝒪_F`-modules is quasi-coherent, as
soon as quasi-coherence of `𝒪_F`-modules is closed under arbitrary direct sums and under
cokernels.

The module universe is free; the shape of the diagram has its objects and its morphisms in
independent universes, as in the source. -/
theorem isQuasicoherent_colimit {K : Type w} [Category.{w'} K]
    [HasCoproducts.{max w w'} (Modules.{u, m} B S hS F hF)]
    (hsum : ∀ I : Type (max w w'),
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape (Discrete I))
    (hcoker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels)
    (D : K ⥤ Modules.{u, m} B S hS F hF) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (Limits.colimit D).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.colimit hsum hcoker D hD

end Colimits

end AlgebraicGeometry.Space

end
