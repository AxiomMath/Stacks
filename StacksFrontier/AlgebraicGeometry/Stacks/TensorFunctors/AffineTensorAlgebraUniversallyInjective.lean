module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineUnitRetractions
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentFilteredColimitNoetherian

/-!
# Stacks 0GRL: the algebra `C = F(g_{QCoh,*}𝒪_U)` is universally injective over `B`

Let `𝒳` be a Noetherian algebraic stack with affine diagonal, `B` a ring,
`F : QCoh(𝒪_𝒳) ⥤ Mod_B` a right exact tensor functor which commutes with direct sums, and
`g : U ⟶ 𝒳` a flat and surjective morphism from an affine scheme `U`.  With
`C = F(g_{QCoh,*}𝒪_U)` the commutative `B`-algebra of Stacks 0GRK, **Stacks 0GRL** says that
`B ⟶ C` is universally injective.

The argument is
`AlgebraicGeometry.Stack.universallyInjective_affineTensorAlgebra_of_coherentGeneration`; its one
input, that every quasi-coherent module on a Noetherian algebraic stack is a filtered colimit of
coherent modules (Stacks 0GRF,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`), is
`AlgebraicGeometry.Stack.ind_coherentQuasicoherent`.

## Main results

* `AlgebraicGeometry.Stack.universallyInjective_affineTensorAlgebra`: **Stacks 0GRL**.

## References

* [Stacks Project, Tag 0GRL](https://stacks.math.columbia.edu/tag/0GRL)
* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0GRL.**  Let `𝒳` be a Noetherian algebraic stack with affine diagonal, `R` a ring and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor (additive, preserving finite colimits,
symmetric monoidal) which commutes with direct sums.  Let `g : U ⟶ 𝒳` be a flat and surjective
morphism from an affine scheme `U`.  Then `g` is affine, and the structure map `R ⟶ C` of the
commutative `R`-algebra `C = F(g_{QCoh,*}𝒪_U)` of Stacks 0GRK
(`AlgebraicGeometry.Stack.affineTensorAlgebra`) is universally injective.

"Affine diagonal" is absolute, as in Stacks 0GRK: the diagonal of the view of `𝒳` over the
terminal scheme `Spec ℤ` (`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`).  The proof
is `AlgebraicGeometry.Stack.universallyInjective_affineTensorAlgebra_of_coherentGeneration` with
Stacks 0GRF (`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`,
in the form `AlgebraicGeometry.Stack.ind_coherentQuasicoherent`) as its input. -/
@[stacks 0GRL]
theorem universallyInjective_affineTensorAlgebra
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) (hUaff : IsAffineOver B S hS U)
    {R : Type u} [CommRing R]
    (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided]
    [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hsurj : IsSurjective B S hS g) :
    ∃ hg : AlgebraicStacks.IsAffineHom B S hS g,
      Algebra.UniversallyInjective R (affineTensorAlgebra g hg F) :=
  universallyInjective_affineTensorAlgebra_of_coherentGeneration hΔ h𝒳 hUaff F g hflat hsurj
    (fun M ↦ ind_coherentQuasicoherent B S hS 𝒳 h𝒳 M)

end AlgebraicGeometry.Stack

end
