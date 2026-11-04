module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMapFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnit
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 04G0: `𝓕 ⊗_𝒜 f_*𝓖 = f_*(f^*𝓕 ⊗_ℬ 𝓖)` for a closed immersion of algebraic spaces

Let `S` be a scheme, `i : Z ⟶ X` a closed immersion of algebraic spaces over `S`, `𝒜` a sheaf of
rings on `X_étale`, `ℬ` a sheaf of rings on `Z_étale` and `φ : 𝒜 ⟶ i_{small,*}ℬ` a homomorphism of
sheaves of rings, so that `(i, φ)` is a morphism of ringed topoi

`f : (Sh(Z_étale), ℬ) ⟶ (Sh(X_étale), 𝒜)`.

**Stacks 04G0** says that for every sheaf of `𝒜`-modules `𝓕` and every sheaf of `ℬ`-modules `𝓖`
the canonical map

`𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`

is an isomorphism. Nothing is assumed about `φ`, and nothing about `𝓕` or `𝓖`.

## Main results

* `AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion`: **Stacks 04G0.**

## The route

The canonical map is the projection-formula map of the adjunction of Stacks 03D7, and that
adjunction is the composite of the adjunction of Stacks 03D4 — inverse image against direct
image — with the adjunction of Stacks 03CZ between extension and restriction of scalars along
`f♯`. `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isIso_inverseImageProjectionMap`
discharges the change-of-rings factor once and for all, so only the inverse-image factor is left,
and `Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd` reduces that to three conditions:

* the comparison of Stacks 03D2 for a tensor product,
  `Stacks.SheafOfModules.inverseImageTensorIso`, is invertible — it is an isomorphism by
  construction;
* the counit of Stacks 03D4 is invertible at `𝓖|_{i⁻¹𝒜}`, which holds because the direct image on
  sheaves of sets along a closed immersion of algebraic spaces is fully faithful (part (1) of
  Stacks 04E5) and
  `Stacks.Sheaves.RingedToposModules.isIso_inverseImageAdjDirectImageModules_counit` carries that
  to sheaves of modules over any sheaf of rings;
* the unit of Stacks 03D4 is invertible at `𝓕 ⊗_𝒜 f_*𝓖`, which is
  `AlgebraicGeometry.Space.isIso_inverseImageAdjDirectImageModules_unit_of_subsingleton_sections`:
  a direct image along `i` has only the zero section over an étale chart of `X` whose base change
  along `i` is empty, hence so does a tensor product one of whose factors is such a direct image.

In particular no hypothesis on `φ` is used, and neither is the closed-immersion condition of
Stacks 08M0 for the morphism of small étale topoi. Both are needed by the route through
Stacks 08M3 and the two adjunction conditions of
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap`, and that route cannot drop `φ`'s local
surjectivity, because those two conditions can fail while the canonical map is invertible.
Take `i = 𝟙` (an identity is a closed immersion), `𝒜` and
`ℬ` the constant sheaves `ℤ` and `ℤ[t]`, and `φ` the inclusion. For `𝓖 = ℬ` the counit
`f^*f_*𝓖 = ℤ[t] ⊗_ℤ ℤ[t] ⟶ ℤ[t]` of the composite adjunction is not injective, yet the canonical
map is the base-change identity `𝓕 ⊗_𝒜 𝓖 = (𝓕 ⊗_𝒜 ℬ) ⊗_ℬ 𝓖`. The route taken here splits the
canonical map first, and the example is no obstruction to it: the counit that fails there is the
counit of the *composite* adjunction, whereas what is used here is the counit of its
inverse-image factor alone, which a closed immersion makes invertible whatever `φ` is.

## References

* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Z X : AlgebraicSpaces B S hS}

/-- **The unit of the adjunction of Stacks 03D4 is invertible at `𝓕 ⊗_𝒜 f_*𝓖`.** The second
factor is a direct image along `i`, which has only the zero section over an étale chart of `X`
whose base change along `i` is empty, and so therefore has the tensor product. -/
theorem isIso_inverseImageUnit_app_tensorPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (𝓕 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS Z ℬ).O)) :
    IsIso ((inverseImageAdjDirectImageModules (smallToposMorphismTypeU B S hS i)
        (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)).unit.app
      (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜))).obj
        (𝓕, (pushforwardModules (smallEtaleRingedToposHomOfSharp B S hS i φ)).obj 𝓖))) := by
  refine isIso_inverseImageAdjDirectImageModules_unit_of_subsingleton_sections B S hS i hi 𝒜 _
    fun W hW ↦ ?_
  refine Stacks.SheafOfModules.subsingleton_tensorSheafBifunctor_obj_of_subsingleton_sections
    (SmallEtale.topology B S hS X.1) 𝓕 _ (op W) fun V g ↦ ?_
  exact subsingleton_sections_directImageModules_of_chartPreimage_eq_empty B S hS i hi.rep _ _
    V.unop (chartPreimage_eq_empty_of_hom B S hS i g.unop hW)

/-- **Stacks 04G0.** Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `S`, let `𝒜`
be a sheaf of rings on `X_étale`, `ℬ` a sheaf of rings on `Z_étale` and
`φ : 𝒜 ⟶ i_{small,*}ℬ` a homomorphism of sheaves of rings, giving a morphism of ringed topoi
`f : (Sh(Z_étale), ℬ) ⟶ (Sh(X_étale), 𝒜)`. Then for every sheaf of `𝒜`-modules `𝓕` and every
sheaf of `ℬ`-modules `𝓖` the canonical map

`𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`

is an isomorphism.

The canonical map is split into its inverse-image factor and its change-of-rings factor; the
second is always invertible and the first is invertible because the inverse-image adjunction of a
closed immersion has an invertible counit and a unit that is invertible at a tensor product with
a direct image. -/
@[stacks 04G0]
theorem isIso_tensorPushforwardMap_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (𝓕 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS Z ℬ).O)) :
    IsIso (tensorPushforwardMap B S hS i φ 𝓕 𝓖) := by
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi
  have := hff.full
  have := hff.faithful
  have hcounit := isIso_inverseImageAdjDirectImageModules_counit
    (smallToposMorphismTypeU B S hS i) (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)
  exact Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isIso_inverseImageProjectionMap
    (smallEtaleRingedToposHomOfSharp B S hS i φ) 𝓕 𝓖
    (Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd _ _ _ _ 𝓕 _ inferInstance
      (NatIso.isIso_app_of_isIso
        (inverseImageAdjDirectImageModules (smallToposMorphismTypeU B S hS i)
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)).counit _)
      (isIso_inverseImageUnit_app_tensorPushforward B S hS i hi φ 𝓕 𝓖))

end AlgebraicGeometry.Space

end
