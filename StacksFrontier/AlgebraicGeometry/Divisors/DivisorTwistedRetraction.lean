module

public import StacksFrontier.AlgebraicGeometry.Divisors.TwistedRetraction

/-!
# The twisted retraction of a submodule containing a divisor multiple of its ambient module

Let `X` be a scheme, let `D ⊆ X` be an effective Cartier divisor with ideal sheaf `ℐ_D` and
invertible sheaf `𝒪_X(D)`, and let `λ : F ⟶ G` be a monomorphism of `𝒪_X`-modules with
`ℐ_D · G ⊆ F`.  Then there is a morphism

`ψ : G ⟶ F ⊗_{𝒪_X} 𝒪_X(D)`

whose composite with `λ` is multiplication by the canonical section `1_D`, that is, the map
induced by the inclusion `𝒪_X ⊆ 𝒪_X(D)`.

This is the geometric instantiation of `Stacks.Monoidal.comp_invertibleTwistedRetraction`, the
mechanism behind the second canonical map of [Stacks, Tag 0G5G]: the containment `ℐ_D · G ⊆ F`
is the pole bound, and `ψ` is the second canonical map.

## Main definitions

* `Stacks.Divisors.twistedRetraction`: the morphism `ψ : G ⟶ F ⊗_{𝒪_X} 𝒪_X(D)`.

## Main results

* `Stacks.Divisors.comp_twistedRetraction`: **`λ ≫ ψ` is multiplication by `1_D`**, i.e.
  `Stacks.Divisors.tensorCanonicalSection`.

Uniqueness of `ψ` is not proved here; it is not part of the assertion of [Stacks, Tag 0G5G],
which asks for the two morphisms and for the value of their composite.

## Implementation notes

The containment `ℐ_D · G ⊆ F` is spelled as the vanishing of the composite of the action
`Stacks.Divisors.idealAction` with `cokernel.π λ`, which is what
`Stacks.Divisors.idealActionFactor` consumes; for a monomorphism `λ` that is exactly the
containment.

The monoidal structure on `X.Modules` is the one of [Stacks, Tag 05NA] with the constraints of
[Stacks, Tag 01CU]; against it `AlgebraicGeometry.Scheme.Modules.tensorRightMap`, `tensorLeftMap`
and `tensorRightUnitor` are `▷`, `◁` and `ρ_` by `rfl`, which is what lets the generic statement
apply to the morphisms as they are spelled elsewhere in the library. It is not declared here:
`Stacks.Divisors.schemeModulesMonoidal`, `Stacks.Divisors.schemeModulesSymmetric` and
`Stacks.Divisors.stacksIsInvertible_negativeTwist'` come from
`StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing`, and are re-activated here with
`attribute [local instance]`. Their `instance` attribute is `local` to that file, but the
declarations themselves are ordinary imported definitions, so there is no need to restate them.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory

universe u

namespace Stacks.Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]

/-- **The twisted retraction attached to a trivialising pairing**, as a morphism rather than as
the composite displayed in `Stacks.Monoidal.comp_invertibleTwistedRetraction`: for
`ev : L ⊗ I ≅ 𝟙` and `nu : I ⊗ G ⟶ F`, the morphism `G ⟶ F ⊗ L` that inverts a morphism
`F ⟶ G` restricting `nu` to multiplication, at the cost of one factor of `L`. -/
def invertibleTwistedRetraction {I L F G : C} (ev : L ⊗ I ≅ 𝟙_ C) (nu : I ⊗ G ⟶ F) :
    G ⟶ F ⊗ L :=
  (λ_ G).inv ≫ ev.inv ▷ G ≫ (α_ L I G).hom ≫ L ◁ nu ≫ (β_ L F).hom

/-- `Stacks.Monoidal.comp_invertibleTwistedRetraction`, stated for the named morphism
`Stacks.Monoidal.invertibleTwistedRetraction`. -/
theorem comp_invertibleTwistedRetraction' {I L F G : C} (ev : L ⊗ I ≅ 𝟙_ C) (iota : I ⟶ 𝟙_ C)
    (c : 𝟙_ C ⟶ L) (hpair : L ◁ iota ≫ (ρ_ L).hom = ev.hom ≫ c)
    (lam : F ⟶ G) (nu : I ⊗ G ⟶ F) (hnu : I ◁ lam ≫ nu = iota ▷ F ≫ (λ_ F).hom) :
    lam ≫ invertibleTwistedRetraction ev nu = (ρ_ F).inv ≫ F ◁ c :=
  comp_invertibleTwistedRetraction ev iota c hpair lam nu hnu

end Stacks.Monoidal

namespace Stacks.Divisors

attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric
  stacksIsInvertible_negativeTwist'

variable {X : Scheme.{u}}

/-- **The twisted retraction attached to a submodule containing `ℐ_D · G`.** For a monomorphism
`λ : F ⟶ G` of `𝒪_X`-modules with `ℐ_D · G ⊆ F`, this is the morphism

`ψ : G ⟶ F ⊗_{𝒪_X} 𝒪_X(D)`

obtained by writing `𝒪_X` as `𝒪_X(D) ⊗ ℐ_D` through the evaluation pairing and letting `ℐ_D`
act on `G` through `Stacks.Divisors.idealActionFactor`. -/
noncomputable def twistedRetraction (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    {F G : X.Modules} (lam : F ⟶ G) [Mono lam]
    (hlam : idealAction D G ≫ cokernel.π lam = 0) :
    G ⟶ Scheme.Modules.tensorObj F (invertibleSheaf' D) :=
  Stacks.Monoidal.invertibleTwistedRetraction (C := X.Modules)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))
    (idealActionFactor D lam hlam)

/-- **The composite of a monomorphism with its twisted retraction is multiplication by the
canonical section `1_D`**, that is, the map `F ⟶ F ⊗_{𝒪_X} 𝒪_X(D)` induced by the inclusion
`𝒪_X ⊆ 𝒪_X(D)`.

This is `Stacks.Monoidal.comp_invertibleTwistedRetraction` instantiated at the evaluation
pairing of `𝒪_X(D)` with `ℐ_D`, with `Stacks.Divisors.canonicalSectionHom` as the section
paired with the ideal inclusion by
`Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`. -/
theorem comp_twistedRetraction (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    {F G : X.Modules} (lam : F ⟶ G) [Mono lam]
    (hlam : idealAction D G ≫ cokernel.π lam = 0) :
    lam ≫ twistedRetraction D lam hlam = tensorCanonicalSection D F := by
  have hnu : Scheme.Modules.tensorLeftMap (negativeTwist' D) lam ≫
      idealActionFactor D lam hlam = idealAction D F := by
    rw [← cancel_mono lam, Category.assoc, idealActionFactor_comp]
    exact Stacks.Monoidal.whiskerLeft_comp_unitAction (C := X.Modules)
      (I := negativeTwist' D) (G := F) (G' := G) (idealSheafInclusion D) lam
  let evIso : MonoidalCategory.tensorObj (C := X.Modules) (invertibleSheaf' D)
      (negativeTwist' D) ≅ 𝟙_ X.Modules :=
    Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D)
  exact Stacks.Monoidal.comp_invertibleTwistedRetraction' (C := X.Modules)
    (I := negativeTwist' D) (L := invertibleSheaf' D) (F := F) (G := G) evIso
    (idealSheafInclusion D) (canonicalSectionHom D)
    (tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor D) lam
    (idealActionFactor D lam hlam) hnu

end Stacks.Divisors

end
