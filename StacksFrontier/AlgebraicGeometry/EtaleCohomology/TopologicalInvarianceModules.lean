module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# Topological invariance of the étale topos, with module coefficients

Let `f : X ⟶ Y` be a universal homeomorphism of schemes and `Λ` a ring. [Stacks, Tag 03SI]
part (2) says that the small étale topoi of `X` and `Y` are equivalent; in this development it is
`Stacks.EtaleCohomology.smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism`, for
sheaves of types, with a version for abelian sheaves. The argument is that base change along `f`
exhibits the small étale site of `Y` as a dense subsite of that of `X`
(`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`), so restriction of sheaves
along it is an equivalence whatever the coefficients. This file records the consequence for
sheaves of `Λ`-modules: direct image and inverse image along `f` are mutually inverse
equivalences, and in particular both are exact.

For the base change `π̄ : X̄_k̄ ⟶ X̄_k̄` of the geometric Frobenius, which is a universal
homeomorphism (`Stacks.Frobenius.universalHomeomorphism_geometricFrobeniusBaseChange`), this is
the exactness of `π̄_*` used in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) to read the canonical Frobenius on `Ext`.

## Main results

* `etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism`:
  `f_*` on sheaves of modules is an equivalence.
* `etaleModuleInverseImage_isEquivalence_of_universalHomeomorphism`:
  `f^{-1}` on sheaves of modules is an equivalence.
* `etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism`:
  `f_*` is right exact, hence exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- **Direct image of sheaves of modules along a universal homeomorphism is an equivalence**: it is
restriction along base change, which exhibits the small étale site of the target as a dense
subsite of that of the source. -/
theorem etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism :
    (etaleModuleDirectImage.{u, r} Λ f).IsEquivalence :=
  have := isDenseSubsite_of_universalHomeomorphism f
  inferInstanceAs ((smallEtaleBaseChange f).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology).IsEquivalence

/-- **Inverse image of sheaves of modules along a universal homeomorphism is an equivalence**: it
is left adjoint to direct image, which is one. -/
theorem etaleModuleInverseImage_isEquivalence_of_universalHomeomorphism :
    (etaleModuleInverseImage.{u, r} Λ f).IsEquivalence :=
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ f
  (etaleModuleInverseImageAdj.{u, r} Λ f).isEquivalence_left_of_isEquivalence_right

/-- Direct image of sheaves of modules along a universal homeomorphism is right exact, being an
equivalence. -/
theorem etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ f) :=
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ f
  inferInstance

end Stacks.EtaleCohomology

end
