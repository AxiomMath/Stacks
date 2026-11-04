module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseMorphism
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseTransition

/-!
# The classified morphism is constant along the weight transitions

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `Y` a scheme. [Stacks, Tag 01N8] attaches to a triple
`(d, L, ψ)` over `Y` a morphism `Y ⟶ Proj(A)`, and
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv` says that
morphism is unchanged by strict equivalence, so it is a map
`F_d(Y) ⟶ Mor(Y, Proj(A))` on the set of classes
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd`.

This file assembles that map and proves it **constant along the weight transitions**
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veronese`: the triple
`(kd, L^{⊗ k}, ψ|_{A^{(kd)}})` classifies the same morphism as `(d, L, ψ)`. The maps `F_d(Y) ⟶
Mor(Y, Proj(A))` therefore form a cone on the diagram of the `F_d` along divisibility, which is
what a map out of the colimit `F(Y)` of Section 27.12 is. That map out of the colimit is
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fcolim.classifyingMorphism`; that it is a
bijection is the representability of `F` by `Proj(A)`, [Stacks, Tag 01NC].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.DegreeTriple.toTriple`: a weight-`d` triple,
  read as a `Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple` by making the weight a field
  again.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism`: **the map
  `F_d(Y) ⟶ Mor(Y, Proj(A))`** of [Stacks, Tag 01N8] on strict equivalence classes.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism_veronese`: **the
  classified morphism is unchanged by the weight transition `F_d → F_{kd}`.**

## Implementation notes

The weight transition is the Veronese restriction, and that it does not change the classified
morphism is
`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.classifyingMorphism_veroneseRestrict`,
already proved for the bundled `Triple`. All this file does is transport it across the bundling:
`DegreeTriple.toTriple` carries `DegreeTriple.veronese` to `Triple.veroneseRestrict` by `rfl`,
the two weight-positivity hypotheses being propositions.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (Triple classifyingHom
  classifyingHom_eq_of_sectionsEquiv)
open Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism (classifyingMorphism_veroneseRestrict)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d k : ℕ}

/-- **A weight-`d` triple, read as a `Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple`**:
the weight becomes a field again, and the positivity it carries is supplied. -/
def DegreeTriple.toTriple (hd : 0 < d) (t : DegreeTriple 𝒜 d Y) : Triple 𝒜 Y :=
  ⟨d, hd, t.module, t.isInvertible, t.psi, t.generated⟩

/-- The Veronese restriction of a weight-`d` triple is the Veronese restriction of the bundled
triple: the two constructions agree field by field, the weight-positivity hypotheses being
propositions. -/
theorem DegreeTriple.toTriple_veronese (hd : 0 < d) (hk : 0 < k) (t : DegreeTriple 𝒜 d Y) :
    DegreeTriple.toTriple 𝒜 (Nat.mul_pos hk hd) (DegreeTriple.veronese 𝒜 t k)
      = (DegreeTriple.toTriple 𝒜 hd t).veroneseRestrict k hk :=
  rfl

/-- **The map `F_d(Y) ⟶ Mor(Y, Proj(A))` of [Stacks, Tag 01N8] on strict equivalence classes**:
a class of weight-`d` triples goes to the morphism `Y ⟶ Proj(A)` any of its representatives
classifies.

It is well defined because strictly equivalent triples classify the same morphism,
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv`. -/
def Fd.classifyingMorphism (hd : 0 < d) : Fd 𝒜 d Y → (Y ⟶ AlgebraicGeometry.Proj 𝒜) :=
  Quotient.lift (fun t => (DegreeTriple.toTriple 𝒜 hd t).classifyingMorphism)
    fun t t' htt' => by
      have := t.isInvertible
      have := t'.isInvertible
      exact congrArg (fun φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme => toProj 𝒜 φ)
        (classifyingHom_eq_of_sectionsEquiv 𝒜 hd t.generated t'.generated htt')

/-- The classifying morphism of the class of a weight-`d` triple `t` is the morphism classified
by `t`. -/
@[simp] theorem Fd.classifyingMorphism_mk (hd : 0 < d) (t : DegreeTriple 𝒜 d Y) :
    Fd.classifyingMorphism 𝒜 hd (Fd.mk 𝒜 t) = (DegreeTriple.toTriple 𝒜 hd t).classifyingMorphism :=
  rfl

/-- **The classified morphism is unchanged by the weight transition `F_d → F_{kd}`.** This is
`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.classifyingMorphism_veroneseRestrict` read on
the classes, and it says that the maps `F_d(Y) ⟶ Mor(Y, Proj(A))` form a cone on the diagram of
the `F_d` along divisibility — so that they induce one map out of the colimit `F(Y)` of Section
27.12. -/
theorem Fd.classifyingMorphism_veronese (hd : 0 < d) (hk : 0 < k) (ξ : Fd 𝒜 d Y) :
    Fd.classifyingMorphism 𝒜 (Nat.mul_pos hk hd) (Fd.veronese 𝒜 k ξ)
      = Fd.classifyingMorphism 𝒜 hd ξ := by
  induction ξ using Quotient.ind with
  | _ t =>
      exact (congrArg Triple.classifyingMorphism
        (DegreeTriple.toTriple_veronese 𝒜 hd hk t)).trans
          (classifyingMorphism_veroneseRestrict 𝒜 (DegreeTriple.toTriple 𝒜 hd t) k hk)

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
