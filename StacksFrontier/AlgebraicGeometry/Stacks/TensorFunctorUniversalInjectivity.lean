module

public import StacksFrontier.CategoryTheory.Monoidal.TensorFunctorUniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctorExtension
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Universal injectivity of `B → F(G)` for a tensor functor on a Noetherian algebraic stack

Let `𝒳` be a Noetherian algebraic stack and `F : QCoh(𝒪_𝒳) ⥤ Mod_B` a right exact tensor functor
commuting with direct sums.  For a commutative algebra object `G` of `QCoh(𝒪_𝒳)` the module
`C = F(G)` is a commutative `B`-algebra.  This file proves the argument of Stacks 0GRL that
`B → C` is universally injective, from its two inputs on `𝒳`:

* every quasi-coherent module is a filtered colimit of coherent ones (Stacks 0GRF), and
* for every coherent `𝓕` and every factorization `𝒪_𝒳 → 𝓕 → G` of the unit of `G`, the first map
  `s` admits an evaluation `ev : 𝓕 ⊗ 𝓓 → 𝒪_𝒳` whose evaluation at `s` is an epimorphism.  In the
  source `𝓓 = 𝓕^∨ = hom(𝓕, 𝒪_𝒳)` (Stacks 0GQN) and the epimorphism is obtained, for
  `G = g_{QCoh,*}𝒪_U` with `g : U → 𝒳` flat and surjective, by pulling back to `U` (Stacks 0GQS).

What is proved here is the rest: the unit `𝒪_𝒳` is coherent, hence a compact object of
`QCoh(𝒪_𝒳)` (Stacks 0GQZ), so the unit of `G` factors through a member of the filtered colimit;
a right exact functor commuting with direct sums commutes with all colimits (Stacks 002P) and
preserves epimorphisms; and the formal argument of
`CategoryTheory.Functor.universallyInjective_algebraMap_tensorFunctor_of_ind`.

## Main results

* `AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

universe u w w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules

/-- **The argument of Stacks 0GRL on a Noetherian algebraic stack.**  Let `𝒳` be a Noetherian
algebraic stack, `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a braided monoidal functor which is right exact and
commutes with direct sums, and `G` a commutative algebra object of `QCoh(𝒪_𝒳)`.  Assume that
every quasi-coherent module is a filtered colimit of coherent ones (`hgen`, Stacks 0GRF), and that
for every coherent `𝓕` and factorization `𝒪_𝒳 → 𝓕 → G` of the unit of `G` the first map admits
an evaluation `𝓕 ⊗ 𝓓 → 𝒪_𝒳` whose evaluation at it is an epimorphism (`hdual`; in the source the
evaluation of `𝓕^∨`, Stacks 0GQN and 0GQS).  Then the structure map `R → F(G)` of the
commutative `R`-algebra `F(G)` is universally injective. -/
theorem universallyInjective_algebraMap_tensorFunctor_of_coherentGeneration
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    [BraidedCategory (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)]
    {R : Type u} [CommRing R]
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ ModuleCat.{u} R) [F.Braided]
    [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) [MonObj G] [IsCommMonObj G]
    (hgen : ∀ M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids, (coherentQuasicoherent B S hS 𝒳).ind.{u} M)
    (hdual : ∀ 𝓕 : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids, coherentQuasicoherent B S hS 𝒳 𝓕 →
      ∀ (s : 𝟙_ _ ⟶ 𝓕) (i : 𝓕 ⟶ G), s ≫ i = η[G] →
        ∃ (𝓓 : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids) (ev : 𝓕 ⊗ 𝓓 ⟶ 𝟙_ _),
          Epi ((λ_ 𝓓).inv ≫ s ▷ 𝓓 ≫ ev)) :
    letI := Functor.tensorFunctorCommRing F G
    letI := Functor.tensorFunctorAlgebraStr F G
    Algebra.UniversallyInjective R (F.obj G) := by
  have := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have : HasFiniteColimits (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasFiniteColimits_of_hasColimitsOfSize _
  have : HasCoproducts.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := fun J ↦ HasColimitsOfSize.has_colimits_of_shape _
  have : HasCoequalizers (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := HasFiniteColimits.out WalkingParallelPair
  have : PreservesColimitsOfShape WalkingParallelPair F :=
    PreservesFiniteColimits.preservesFiniteColimits WalkingParallelPair
  have : PreservesColimitsOfSize.{u, u} F :=
    preservesColimits_of_preservesCoequalizers_and_coproducts F
  have : PreservesColimitsOfShape WalkingSpan F :=
    PreservesFiniteColimits.preservesFiniteColimits WalkingSpan
  have : F.PreservesEpimorphisms := preservesEpimorphisms_of_preservesColimitsOfShape F
  have := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
  exact Functor.universallyInjective_algebraMap_tensorFunctor_of_ind F
    (coherentQuasicoherent B S hS 𝒳) G
    (isFinitelyPresentable_of_isCoherent B S hS 𝒳 h𝒳 _
      ((coherentQuasicoherent B S hS 𝒳).prop_unit))
    (hgen G) hdual

end AlgebraicGeometry.Stack

end
