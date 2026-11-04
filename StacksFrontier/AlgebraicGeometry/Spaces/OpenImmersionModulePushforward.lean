module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero

/-!
# Direct image of modules along an open immersion of algebraic spaces

Let `j : U ⟶ X` be an open immersion of algebraic spaces over a scheme `S`. Restriction of
`𝒪`-modules to the open subspace is a left inverse of the direct image: the counit
`j^*j_*G ⟶ G` of the adjunction of Stacks 03LU is an isomorphism for every `𝒪_U`-module `G`.
Equivalently — the counit of an adjunction is an isomorphism exactly when the right adjoint is
fully faithful — the direct image `j_* : Mod(𝒪_U) ⥤ Mod(𝒪_X)` is fully faithful.

## Main definitions

* `AlgebraicGeometry.Space.fullyFaithfulModulePushforwardOfIsOpenImmersion`: direct image of
  `𝒪`-modules along an open immersion is fully faithful.
* `AlgebraicGeometry.Space.etaleModulePullbackCounitIso`: the resulting natural isomorphism
  `j_* ⋙ j^* ≅ 𝟭`.

## Main results

* `AlgebraicGeometry.Space.isIso_etaleModulePullbackAdjunction_counit`: the counit
  `j^*j_*G ⟶ G` is an isomorphism for every `𝒪_U`-module `G`.

## Implementation notes

The closed-immersion statement, Stacks 04CJ part (2)
(`AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit`), is deduced from full
faithfulness of the direct image on sheaves of sets *together with* local surjectivity of the
structure map `𝒪_X ⟶ f_*𝒪_Z`, through
`Stacks.ToposBridge.fullyFaithfulPushforwardModules`. That route is unavailable here: for an
open immersion the structure map is not locally surjective — on `X = 𝐀^1` and
`U = X \setminus \{0\}` the section `1/t` of `j_*𝒪_U` over `X` does not lift to `𝒪_X` after any
étale covering of a point of the origin.

What replaces it is `AlgebraicGeometry.RingedToposHom.fullyFaithfulPushforwardModules`, which
asks instead that the structure map become invertible after inverse image — that is Stacks 03LV
for an étale morphism, `AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale` — and
that the direct
image of sheaves of sets have invertible counit, which is
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsOpenImmersion`. No local
surjectivity enters.

The counit is taken for the adjunction
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`, whose left adjoint is étale
restriction; since that adjunction has the same right adjoint as
`AlgebraicGeometry.Space.modulePullbackAdjunction`, full faithfulness of the direct image makes
the counits of both invertible.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-- Direct image of `𝒪`-modules along an open immersion `j : U ⟶ X` of algebraic spaces is
fully faithful.

The two inputs of `AlgebraicGeometry.RingedToposHom.fullyFaithfulPushforwardModules` are
Stacks 03LV for the étale morphism `j`,
`AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale`, and full faithfulness of the
direct image
of sheaves of sets,
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsOpenImmersion`. -/
def fullyFaithfulModulePushforwardOfIsOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) : (modulePushforward B S hS j).FullyFaithful :=
  have h := fullyFaithfulSmallEtalePushforwardOfIsOpenImmersion B S hS j hj
  have _ : (smallEtaleRingedToposHom B S hS j).toToposHom.pushforward.Full := h.full
  have _ : (smallEtaleRingedToposHom B S hS j).toToposHom.pushforward.Faithful := h.faithful
  have _ :=
    isIso_fSharpInverseImage_of_isEtale B S hS j (isEtale_of_isOpenImmersion B S hS hj)
  pushforwardModules_eq_modulePushforward B S hS j ▸
    (smallEtaleRingedToposHom B S hS j).fullyFaithfulPushforwardModules

/-- For an open immersion `j : U ⟶ X` of algebraic spaces and any sheaf of `𝒪_U`-modules `G`,
the adjunction map `j^*j_*G ⟶ G` is an isomorphism: restriction to the open subspace is a left
inverse of the direct image.

This is full faithfulness of the direct image read through the adjunction of Stacks 03LU: the
counit of an adjunction is an isomorphism exactly when its right adjoint is fully faithful. -/
theorem isIso_etaleModulePullbackAdjunction_counit (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (G : Modules.{u, u} B S hS U.1 U.2) :
    IsIso ((etaleModulePullbackAdjunction B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).counit.app G) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).faithful
  inferInstance

/-- Functorially: restriction of `𝒪`-modules along an open immersion of algebraic spaces is a
left inverse of the direct image, the counit of the adjunction of Stacks 03LU being a natural
isomorphism `j_* ⋙ j^* ≅ 𝟭`. This is the functorial form of
`AlgebraicGeometry.Space.isIso_etaleModulePullbackAdjunction_counit`. -/
def etaleModulePullbackCounitIso (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom) :
    modulePushforward B S hS j ⋙
        etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj) ≅
      𝟭 (Modules.{u, u} B S hS U.1 U.2) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).faithful
  asIso (etaleModulePullbackAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)).counit

end AlgebraicGeometry.Space

end
