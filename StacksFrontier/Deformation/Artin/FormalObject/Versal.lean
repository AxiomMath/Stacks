module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Smooth.Versal

/-!
# Versal formal objects of a category fibred in groupoids over a scheme

Let `S` be a locally Noetherian scheme, let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in
groupoids and let `ξ = (R, ξ_n, f_n)` be a formal object of `p`: a Noetherian complete local
ring `R` over `S` together with objects `ξ_n` of `𝒳` over the infinitesimal thickenings of the
closed point of `Spec R` and transitions between them. Write `k = R / 𝔪` for the residue field
and `x₀ = ξ_0` for the closed fibre, and fix a ring `Λ` through which the structure morphism
`Spec R ⟶ S` factors. Then `ξ` is the same data as a formal object of the predeformation
category `𝓕_{𝒳,k,x₀}` over `𝒞_Λ`, with the same levels, the same transitions and the same
complete local base. The formal object `ξ` is *versal* when that formal object of the
predeformation category is versal, that is, when its associated morphism from the functor
represented by the complete local base is smooth.

## Main definitions

* `Deformation.Artin.FormalObject.predeformationFormalObject` is `ξ` read as a formal object of
  the predeformation category of its closed fibre.
* `Deformation.Artin.FormalObject.IsVersal`: **Stacks 0CXJ**.

## Main results

* `Deformation.Artin.FormalObject.exists_versalPredeformationFormalObject`: a versal formal
  object exhibits its complete local base as the base of a versal formal object of the
  predeformation category of its closed fibre.

## Implementation notes

Versality of a formal object over `𝒞_Λ` is the abstract predicate `Deformation.IsVersal`
(**Stacks 06HR**), whose data is a functor to `𝒞_Λ` together with a formal object of it. The
predicate defined here is the transport of that one along the passage from a formal object over
the big fppf site to a formal object of the predeformation category (**Stacks 0CXH**), and it
is a separate declaration because it speaks about different data: neither the big fppf site
`B`, nor the base scheme `S`, nor the closed fibre `x₀`, nor the chosen factorization
`Λ → R` of the structure morphism occurs in the signature of the abstract predicate, and no
composite of the two is available until the predeformation category has been built from them.

The predeformation category is produced by a tactic-mode definition, so its carrier does not
reduce at reducible transparency and its category structure is supplied by a local instance
rather than left to instance search. Making `CategoryTheory.BasedCategory.ofFunctor` locally
reducible is what lets the cofibration witness of **Stacks 07T5** be used at the type
`Deformation.IsVersal` expects.

The universe levels are forced rather than chosen: the predeformation construction places its
Artinian and complete local algebras at `{u, u, u}` over a `u`-scheme, while the fibred
category over the big fppf site keeps its own object and morphism universes.

## References

* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
* [Stacks Project, Tag 0CXH](https://stacks.math.columbia.edu/tag/0CXH)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- The category structure on the carrier of a predeformation category, made available to
instance search for the formal objects of its projection.

Published rather than sealed: five downstream modules re-declared this verbatim precisely
because it was `local` here, three of them saying so in their own docstrings. Consumers that
only need it registered locally can write
`attribute [local instance] Deformation.Artin.versal_predeformationCategory_category`. -/
public instance versal_predeformationCategory_category
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
    {X : Type v} [Category.{w} X] (iΛ : Spec (.of Λ) ⟶ S) (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    Category.{max u w} (predeformationCategory iΛ q x₀ hx₀).carrier :=
  (predeformationCategory iΛ q x₀ hx₀).category

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- A formal object of a category over the big fppf site of `S`, read as a formal object of the
predeformation category of its closed fibre: the same complete local base, the level `n` being
the deformation `ξ.level 0 ⟶ ξ.level n`, and the transitions being those of `ξ` read as
reversed arrows of deformations. -/
def FormalObject.predeformationFormalObject (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS) :
    Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
        (ξ.basePoint Λ iΛ hR)).projection where
  base := ξ.completeLocalBase Λ
  level n := ξ.predeformationLevel Λ iΛ hR n
  level_eq _ := rfl
  transition n := ξ.predeformationTransition Λ iΛ hR n
  transition_lift n := isHomLift_of_map_eq
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint Λ iΛ hR)).projection
    (ξ.predeformationTransition Λ iΛ hR n) rfl

end

/-! ### Stacks 0CXJ -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- A formal object `ξ` of a category fibred in groupoids over the big fppf site of `S` is
versal, relative to a ring `Λ` through which the structure morphism of its complete local base
factors, when the formal object of the predeformation category of its closed fibre determined
by `ξ` is versal. -/
@[stacks 0CXJ]
def FormalObject.IsVersal (hp : p.IsFiberedInGroupoids) (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS) : Prop :=
  Deformation.IsVersal
    (predeformationCategory_isPredeformationCategory B hS iΛ p (ξ.level 0)
      (ξ.basePoint Λ iΛ hR) hp).cofibered
    (ξ.predeformationFormalObject Λ iΛ hR)

/-- Versality of `ξ` is versality, in the sense of **Stacks 06HR**, of the formal object of the
predeformation category of its closed fibre that `ξ` determines. -/
theorem FormalObject.isVersal_iff (hp : p.IsFiberedInGroupoids) (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS) :
    FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR ↔
      Deformation.IsVersal
        (predeformationCategory_isPredeformationCategory B hS iΛ p (ξ.level 0)
          (ξ.basePoint Λ iΛ hR) hp).cofibered
        (ξ.predeformationFormalObject Λ iΛ hR) :=
  Iff.rfl

/-- A versal formal object exhibits its complete local base as the base of a versal formal
object of the predeformation category of its closed fibre. -/
theorem FormalObject.exists_versalPredeformationFormalObject
    (hp : p.IsFiberedInGroupoids) (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR) :
    ∃ η : Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
          (ξ.basePoint Λ iΛ hR)).projection,
      η.base = ξ.completeLocalBase Λ ∧
        Deformation.IsVersal
          (predeformationCategory_isPredeformationCategory B hS iΛ p (ξ.level 0)
            (ξ.basePoint Λ iΛ hR) hp).cofibered η :=
  ⟨ξ.predeformationFormalObject Λ iΛ hR, rfl, hversal⟩

end

end Deformation.Artin

end
