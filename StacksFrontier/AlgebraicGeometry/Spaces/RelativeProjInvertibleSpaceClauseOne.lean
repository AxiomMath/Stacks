module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraOfProj
public import StacksFrontier.AlgebraicGeometry.Spaces.PointFamilyDescent

/-!
# The square of clause (1) of Stacks 0D2Z on the algebraic space `U(ψ)`

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, clause (1) of [Stacks, Tag 0D2Z] asserts, for every étale `V ⟶ Y` and
`d ≥ 0`, that a section `a` of `𝒜_d` over `V` has the same image in `Γ(V ×_Y U(ψ), ℒ^{⊗ d})`
along `ψ` followed by restriction as along `ψ_P` followed by `θ`.

Both legs of that square are maps out of one module on `U(ψ)`, the inverse image
`π_{U(ψ)}^*𝒜_d` of `𝒜_d` along `π_{U(ψ)} = f ∘ ι` (`clauseOneSource`): the `ψ_P` leg is the
degree-`d` component `ψ_{P,d}` of [Stacks, Tag 084D] pulled back along `r_{ℒ,ψ}`
(`clauseOneProjLeg`), and the `ψ` leg is `ψ_d` pulled back along the inclusion
`ι : U(ψ) ⟶ X` (`clauseOnePsiLeg`).  So the clause has a morphism form
(`ClauseOneHom`) — the two legs agree after `θ` — and the section form the tag states
(`ClauseOneSections`), and the first implies the second
(`clauseOneSections_of_clauseOneHom`): an equality of morphisms of sheaves of modules gives the
square on sections over every object of the site, in particular over the base changes of the
étale `V ⟶ Y`.

The morphism form is what the descent of `θ` along a presentation of `U(ψ)` delivers:
`AlgebraicGeometry.Space.comp_pointFamilyDescendedHom_eq` concludes exactly
`clauseOneProjLeg ≫ θ = clauseOnePsiLeg` from the same equation at every scheme point of
`U(ψ)`, which is why `clauseOneSource` is shown quasi-coherent here
(`isQuasicoherentOnSite_clauseOneSource`, [Stacks, Tag 03GA]) — that lemma requires it.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction.locusToBase`:
  the structure morphism `π_{U(ψ)} : U(ψ) ⟶ Y`.
* `…clauseOneSource`: the common source `π_{U(ψ)}^*𝒜_d` of the two legs.
* `…clauseOneProjLeg` and `…clauseOnePsiLeg`: the two legs.
* `…ClauseOneHom` and `…ClauseOneSections`: the morphism form and the section form of clause (1).

## Main results

* `…invertibleSpaceMorphism_comp_relativeProjSpaceHom`: `r_{ℒ,ψ} ≫ π = π_{U(ψ)}`.
* `…isQuasicoherentOnSite_clauseOneSource`: `π_{U(ψ)}^*𝒜_d` is quasi-coherent.
* `…clauseOneSections_of_clauseOneHom`: **the morphism form of clause (1) implies the section
  form over étale `V ⟶ Y`.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))

/-- The structure morphism `π_{U(ψ)} = f ∘ ι : U(ψ) ⟶ Y` of the locus over the base. -/
abbrev locusToBase : locusSpaceOfUnitalHom s f L ψ ⟶ s.shrink.space :=
  locusInclusionOfUnitalHom s f L ψ ≫ f

/-- `r_{ℒ,ψ}` is a morphism over `Y`, in the spelling `r ≫ π = π_{U(ψ)}`. -/
theorem invertibleSpaceMorphism_comp_relativeProjSpaceHom :
    (ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property ≫ s.relativeProjSpaceHom =
      locusToBase s f L ψ :=
  ObjectProperty.hom_ext _ (ofUnitalHom s f L ψ).invertibleMorphism_comp_π

/-- The inverse image `π_{U(ψ)}^*𝒜_d` of the degree-`d` piece of `𝒜` along `π_{U(ψ)}`: the
common source of the two legs of the square of clause (1). -/
abbrev clauseOneSource (d : ℤ) :
    Modules.{u, u} s.shrink.site s.shrink.base s.shrink.containsBase
      (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property :=
  (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
    (locusToBase s f L ψ)).obj (s.shrink.algebra.piece d)

/-- `π_{U(ψ)}^*𝒜_d` is quasi-coherent ([Stacks, Tag 03GA]). -/
theorem isQuasicoherentOnSite_clauseOneSource (d : ℤ) :
    (clauseOneSource s f L ψ d).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite _ _ _ (locusToBase s f L ψ)
    (s.shrink.algebra.piece d) (s.shrink.isQuasicoherent d)

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The `ψ_P` leg of the square of clause (1)**: the degree-`d` component `ψ_{P,d}` of
[Stacks, Tag 084D] pulled back along `r_{ℒ,ψ}`, read as a map
`π_{U(ψ)}^*𝒜_d ≅ r^*(π^*𝒜_d) ⟶ r^*𝒪_{Proj_Y(𝒜)}(d)`. -/
def clauseOneProjLeg (d : ℕ) :
    clauseOneSource s f L ψ (d : ℤ) ⟶ (thetaSourceOfUnitalHom s f L ψ Px (d : ℤ)).obj :=
  eqToHom (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        k).obj (s.shrink.algebra.piece (d : ℤ)))
      (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm) ≫
    ((modulePullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv ≫
    (modulePullback s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)).map (s.psiTwistHom Px d)

/-- **The `ψ` leg of the square of clause (1)**: the degree-`d` component of `ψ` pulled back
along the inclusion `ι : U(ψ) ⟶ X`, read as a map
`π_{U(ψ)}^*𝒜_d ≅ ι^*(f^*𝒜_d) ⟶ ℒ^{⊗ d}|_{U(ψ)}`. -/
def clauseOnePsiLeg (d : ℕ) :
    clauseOneSource s f L ψ (d : ℤ) ⟶ (thetaTarget s f L ψ (d : ℤ)).obj :=
  ((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
      (locusInclusionOfUnitalHom s f L ψ) f).app (s.shrink.algebra.piece (d : ℤ))).inv ≫
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
      (locusInclusionOfUnitalHom s f L ψ)).map (ψ.app (d : ℤ))

/-- **Clause (1) of [Stacks, Tag 0D2Z], in morphism form**: in every degree `d ≥ 0` the `ψ_P`
leg followed by `θ` is the `ψ` leg. -/
def ClauseOneHom
    (θ : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj) :
    Prop :=
  ∀ d : ℕ, clauseOneProjLeg s f L ψ Px d ≫ θ (d : ℤ) = clauseOnePsiLeg s f L ψ d

/-- **Clause (1) of [Stacks, Tag 0D2Z], in the section form the tag states**: for every étale
`V ⟶ Y`, every `d ≥ 0` and every section `a` of `𝒜_d` over `V`, the images of `a` in
`Γ(V ×_Y U(ψ), ℒ^{⊗ d})` along the two legs agree, the `ψ_P` leg being followed by `θ`. -/
def ClauseOneSections
    (θ : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj) :
    Prop :=
  ∀ (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ) (d : ℕ)
      (a : (s.shrink.algebra.piece (d : ℤ)).val.obj V),
    (((modulePullbackAdjunction s.shrink.site s.shrink.base s.shrink.containsBase
          (locusToBase s f L ψ)).homEquiv (s.shrink.algebra.piece (d : ℤ))
          (thetaTarget s f L ψ (d : ℤ)).obj)
        (clauseOneProjLeg s f L ψ Px d ≫ θ (d : ℤ))).val.app V a =
      (((modulePullbackAdjunction s.shrink.site s.shrink.base s.shrink.containsBase
          (locusToBase s f L ψ)).homEquiv (s.shrink.algebra.piece (d : ℤ))
          (thetaTarget s f L ψ (d : ℤ)).obj)
        (clauseOnePsiLeg s f L ψ d)).val.app V a

/-- **The morphism form of clause (1) implies the section form over étale `V ⟶ Y`.** -/
theorem clauseOneSections_of_clauseOneHom
    (θ : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj)
    (h : ClauseOneHom s f L ψ Px θ) : ClauseOneSections s f L ψ Px θ := by
  intro V d a
  rw [h d]

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction
