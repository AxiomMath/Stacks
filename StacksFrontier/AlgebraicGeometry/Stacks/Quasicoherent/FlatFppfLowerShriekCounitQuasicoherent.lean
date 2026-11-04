module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleLowerShriekLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsoOfFlatRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# The counit `g_! g^* 𝓜 ⟶ 𝓜` on quasi-coherent modules

Let `𝒳` be an algebraic stack and `g_! ⊣ g^*` the lower shriek and the restriction of modules for
the flat-fppf site (**Stacks 0789** (2)), at module universe `u + 1`.  **Stacks 07B1** (2)(a)
asserts that `g_! g^* 𝓜 ⟶ 𝓜` is an isomorphism for every quasi-coherent `𝓜`.  This file proves it
from its two inputs as the source uses them:

* `g^* 𝓜` is quasi-coherent on the flat-fppf site (**Stacks 03DO**, pullback along a morphism of
  ringed topoi preserves quasi-coherence), and
* `g_!` carries quasi-coherent modules on the flat-fppf site to quasi-coherent modules on `𝒳`
  (**Stacks 07B0** (2)),

so that the counit is a morphism of quasi-coherent modules; it is an isomorphism over every flat
object, `g^*` inverting it because `g^* g_! = id`, hence an isomorphism
(`AlgebraicGeometry.Stack.FlatFppf.isIso_of_isIso_moduleInverseImage_map`).  The first input is
`isQuasicoherentOnSite_moduleInverseImage`; the second is the hypothesis `hshriek`.  With
**Stacks 07B1** (2)(b) (`g^* 𝓕` quasi-coherent for `𝓕` in `LQCoh^fbc(𝒪_𝒳)`), `hshriek` also gives
that `g_! g^* 𝓕` is quasi-coherent for such `𝓕`.

## Main results

* `isQuasicoherentOnSite_moduleInverseImage`: `g^*` preserves quasi-coherence (**Stacks 03DO**).
* `isIso_moduleLowerShriekSuccAdjunction_counit_app`: **Stacks 07B1** (2)(a), given `hshriek`.
* `isQuasicoherentOnSite_moduleLowerShriekSucc_moduleInverseImage`: `g_! g^* 𝓕` is quasi-coherent
  whenever `g^* 𝓕` is, given `hshriek`.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- **`g^*` preserves quasi-coherence** at module universe `u + 1` (**Stacks 03DO** for the
morphism of ringed topoi `g` of **Stacks 0788** (2)): restriction along the continuous and
cocontinuous inclusion of the flat objects, whose slice functors are continuous, carries
quasi-coherent modules to quasi-coherent modules. -/
theorem isQuasicoherentOnSite_moduleInverseImage (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (hM : M.IsQuasicoherentOnSite) :
    ((moduleInverseImage B S hS 𝒳).obj M).IsQuasicoherentOnSite :=
  have : ∀ X : FlatFppf B S hS 𝒳, (Over.post (X := X) (objectProperty B S hS 𝒳).ι).IsContinuous
      ((topology B S hS 𝒳).over X)
      ((associatedTopology B S hS 𝒳.val.val.p B.topology).over
        ((objectProperty B S hS 𝒳).ι.obj X)) := fun X =>
    CategoryTheory.Functor.isContinuous_overPost _ _ _ X
  Stacks.SheafOfModules.isQuasicoherentOnSite_restriction (objectProperty B S hS 𝒳).ι
    (ambientRingStructureSheaf B S hS 𝒳) M hM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (hshriek : ∀ H : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳),
    H.IsQuasicoherentOnSite → ((moduleLowerShriekSucc B S hS 𝒳).obj H).IsQuasicoherentOnSite)

include hshriek in
/-- **Stacks 07B1 (2)(a)**, over its input `hshriek` (**Stacks 07B0** (2)): `g_! g^* 𝓜 ⟶ 𝓜` is
an isomorphism for every quasi-coherent `𝓜`. -/
theorem isIso_moduleLowerShriekSuccAdjunction_counit_app
    (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((moduleLowerShriekSuccAdjunction B S hS 𝒳).counit.app M) :=
  isIso_of_isIso_moduleInverseImage_map B S hS 𝒳
    (hshriek _ (isQuasicoherentOnSite_moduleInverseImage B S hS 𝒳 M hM)) hM _
    (ObjectProperty.isIso_map_counit_of_isIso_unit (moduleLowerShriekSuccAdjunction B S hS 𝒳) M)

include hshriek in
/-- `g_! g^* 𝓕` is quasi-coherent for every `𝓕` satisfying `L` whose pullback `g^* 𝓕` is
quasi-coherent (`hflat`; **Stacks 07B1** (2)(b) for `L = LQCoh^fbc(𝒪_𝒳)`), given `hshriek`
(**Stacks 07B0** (2)). -/
theorem isQuasicoherentOnSite_moduleLowerShriekSucc_moduleInverseImage
    {L : ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (hflat : ∀ F, L F → ((moduleInverseImage B S hS 𝒳).obj F).IsQuasicoherentOnSite)
    (F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) (hF : L F) :
    ((moduleLowerShriekSucc B S hS 𝒳).obj
      ((moduleInverseImage B S hS 𝒳).obj F)).IsQuasicoherentOnSite :=
  hshriek _ (hflat F hF)

end AlgebraicGeometry.Stack.FlatFppf
