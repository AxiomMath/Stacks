module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureDirectImage

/-!
# The two sides of the displayed formula (07MK)

[Stacks, Tag 07MJ] states, without proof, the displayed equation (07MK)

`(Rf_{cris, *}F)_{T'} = R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`

in the derived category of abelian sheaves on the small Zariski site of the ambient scheme `T'` of
an object `(U', T', δ')` of `Cris(X'/S')`. This file defines the restriction `G ↦ G_{T'}` of
[Stacks, Tag 07IQ] on abelian sheaves and its right derived functor, the two sides of the equation,
and the equation itself, as a type of data and as a proposition.

For an object `A = (U, T, δ)` of `Cris(X/S)` the restriction `G ↦ G_T` is restriction along the
functor `T_Zar ⥤ Cris(X/S)` of restrictions of `A` to the opens of `T`,
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`, which
is continuous and cocontinuous. It is exact.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystallineThickening.abelianAmbientRestriction`: `G ↦ G_T` on abelian sheaves, the restriction
  of [Stacks, Tag 07IQ] at the coefficients `AddCommGrpCat.{u + 1}`, with
  `CrystallineThickening.abelianAmbientExtension` its right adjoint and
  `CrystallineThickening.abelianAmbientRestrictionAdjunction` the adjunction.
* `CrystallineThickening.derivedAbelianAmbientRestrictionFunctor`: its right derived functor
  `D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(T_Zar))`.
* `pullbackAbelianSheaf`: the pullback `F ↦ F_U : Ab(Cris(X/S)) ⥤ Ab(Cris(U/T))`.
* `leftSide07MK` and `rightSide07MK`: the two sides of (07MK), as functors
  `Ab(Cris(X/S)) ⥤ D⁺(Ab(T'_Zar))`.
* `Formula07MK`: the displayed equation (07MK) of [Stacks, Tag 07MJ], as a type of data: an
  isomorphism of functors between the two sides, for a fixed object `(U', T', δ')`.
* `Computes07MK`: the statement of (07MK), as a proposition: `Formula07MK` is inhabited for every
  object `(U', T', δ')` of `Cris(X'/S')`.

## Main results

* `CrystallineThickening.abelianAmbientRestriction_obj_obj`: the presheaf underlying `G_T` is
  `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restriction`.
* `CrystallineThickening.preservesFiniteLimits_abelianAmbientRestriction` and
  `CrystallineThickening.preservesFiniteColimits_abelianAmbientRestriction`: `G ↦ G_T` is exact.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

attribute [local instance] restrictOpenFunctor_isContinuous restrictOpenFunctor_isCocontinuous

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-! ### The restriction `G ↦ G_T` on abelian sheaves -/

/-- **The restriction `G ↦ G_T : Ab(Cris(X/S)) ⥤ Ab(T_Zar)`** of an abelian sheaf on the small
crystalline site to the small Zariski site of the ambient scheme of an object `A = (U, T, δ)`,
[Stacks, Tag 07IQ] at the coefficients `AddCommGrpCat.{u + 1}`. On sections it is
`G_T(W) = G(A|_W)`. -/
def abelianAmbientRestriction :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        AddCommGrpCat.{u + 1} :=
  (restrictOpenFunctor A).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)

/-- **The presheaf underlying `G_T` is the restriction presheaf of
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restriction`.** -/
theorem abelianAmbientRestriction_obj_obj
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((abelianAmbientRestriction A).obj G).obj = CohomologyRestriction.restriction G.obj A :=
  rfl

/-- The sections of `G_T` over an open `W` of `T` are the sections of `G` over the restriction
`A|_W`. -/
theorem abelianAmbientRestriction_obj_obj_obj
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (W : A.obj.thickening.target.scheme.Opens) :
    ((abelianAmbientRestriction A).obj G).obj.obj (op W) = G.obj.obj (op (A.restrictOpen W)) :=
  rfl

/-- **The right adjoint of `G ↦ G_T`**, the sheaf pushforward along the *cocontinuous*
`restrictOpenFunctor A`. -/
def abelianAmbientExtension :
    Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (restrictOpenFunctor A).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)

/-- **The adjunction between `G ↦ G_T` and its right adjoint `abelianAmbientExtension A`.** -/
def abelianAmbientRestrictionAdjunction :
    abelianAmbientRestriction A ⊣ abelianAmbientExtension A :=
  (restrictOpenFunctor A).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)

/-- **`G ↦ G_T` preserves every colimit that exists.** -/
instance preservesColimitsOfSize_abelianAmbientRestriction :
    PreservesColimitsOfSize.{w, w'} (abelianAmbientRestriction A) :=
  (abelianAmbientRestrictionAdjunction A).leftAdjoint_preservesColimits

/-- **`G ↦ G_T` is left exact.** -/
instance preservesFiniteLimits_abelianAmbientRestriction :
    PreservesFiniteLimits (abelianAmbientRestriction A) :=
  inferInstanceAs (PreservesFiniteLimits
    ((restrictOpenFunctor A).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)))

/-- **`G ↦ G_T` is right exact.** -/
instance preservesFiniteColimits_abelianAmbientRestriction :
    PreservesFiniteColimits (abelianAmbientRestriction A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- `G ↦ G_T` is additive. -/
instance additive_abelianAmbientRestriction : (abelianAmbientRestriction A).Additive where
  map_add := by intros; rfl

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    AddCommGrpCat.{u + 1})]

/-- **The derived restriction `D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(T_Zar))`**, the right derived functor of
`G ↦ G_T`. -/
def derivedAbelianAmbientRestrictionFunctor :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf
        (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}) :=
  (abelianAmbientRestriction A).rightDerivedFunctorPlus

/-- **`R^j(G ↦ G_T) = 0` for `j ≠ 0` on an injective abelian sheaf.** -/
theorem isZero_rightDerivedPlus_abelianAmbientRestriction_of_injective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective G] (j : ℤ) (hj : j ≠ 0) :
    IsZero (((abelianAmbientRestriction A).rightDerivedPlus j).obj G) :=
  Functor.isZero_rightDerivedPlus_obj_injective (abelianAmbientRestriction A) j hj G

/-- **`R^0(G ↦ G_T) ≅ (G ↦ G_T)`.** -/
def rightDerivedPlusZeroIsoAbelianAmbientRestriction :
    (abelianAmbientRestriction A).rightDerivedPlus 0 ≅ abelianAmbientRestriction A :=
  haveI : PreservesFiniteLimits (abelianAmbientRestriction A) := inferInstance
  (Stacks.DerivedIndexing.rightDerivedIso (abelianAmbientRestriction A) 0).symm ≪≫
    (abelianAmbientRestriction A).rightDerivedZeroIsoSelf

end Derived

end CrystallineThickening

/-! ### The displayed equation (07MK) -/

section Formula

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The abelian pullback `F ↦ F_U : Ab(Cris(X/S)) ⥤ Ab(Cris(U/T))`** of [Stacks, Tag 07MJ], along
the morphism of small crystalline topoi `(U/T)_cris ⟶ (X/S)_cris` whose set-valued form is
`Crystalline.GlobalCrystallineSituation.pullbackCrisMorphism`. It is
`Crystalline.GlobalCrystallineSituation.SmallSite.crisInverseImage` for that morphism. -/
def pullbackAbelianSheaf (A' : CrystallineThickening S') :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} :=
  crisInverseImage (pullbackSituation S S' fS fX hf A') S (pullback.fst fS A'.obj.toBase)
    (pullback.fst fX A'.obj.toX) (pullbackSituation_comm S S' fS fX hf A')

section Statement

variable (A' : CrystallineThickening S')
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology (pullbackSituation S S' fS fX hf A'))
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
    (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
    A'.obj.thickening.target.scheme.carrier) AddCommGrpCat.{u + 1})]

/-- **The left-hand side of the displayed equation (07MK)**, `F ↦ (Rf_{cris, *}F)_{T'}`: the
derived direct image along `f_cris` of [Stacks, Tag 07IK], followed by the derived restriction to
the small Zariski site of the ambient scheme `T'` of `(U', T', δ')`. -/
def leftSide07MK :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf
        (Opens.grothendieckTopology A'.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}) :=
  derivedCrisDirectImage S S' fS fX hf ⋙
    CrystallineThickening.derivedAbelianAmbientRestrictionFunctor A'

/-- **The right-hand side of the displayed equation (07MK)**,
`F ↦ R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`: pull `F` back to `Cris(U/T)`, push it down to `T_Zar` along the
structure morphism `τ_{U/T}` of [Stacks, Tag 07MJ], and push that along `T = S ×_{S'} T' ⟶ T'`. -/
def rightSide07MK :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf
        (Opens.grothendieckTopology A'.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}) :=
  pullbackAbelianSheaf S S' fS fX hf A' ⋙
    derivedPullbackTauDirectImage S S' fS fX hf A' ⋙
      derivedPullbackBaseZariskiPushforwardFunctor S S' fS A'

/-- **The displayed equation (07MK) of [Stacks, Tag 07MJ] at one object `(U', T', δ')`, as a type
of data**: an isomorphism

`(Rf_{cris, *}F)_{T'} ≅ R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`,

natural in the abelian sheaf `F` on `Cris(X/S)`. -/
abbrev Formula07MK : Type _ :=
  leftSide07MK S S' fS fX hf A' ≅ rightSide07MK S S' fS fX hf A'

end Statement

/-- **The statement of the displayed equation (07MK) of [Stacks, Tag 07MJ]**: for every object
`(U', T', δ')` of `Cris(X'/S')` the two sides of the equation are isomorphic as functors of the
abelian sheaf `F` on `Cris(X/S)`. -/
def Computes07MK
    [HasDerivedCategory.{u + 2} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 2} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})] : Prop :=
  ∀ A' : CrystallineThickening S',
    haveI := hasDerivedCategorySheaf (pullbackSituation S S' fS fX hf A')
    haveI := instHasSheafifyOpensSpaceAddCommGrpCat
      (pullbackBase S S' fS A').scheme.carrier
    haveI := hasDerivedCategorySpaceZariskiSheaf (pullbackBase S S' fS A').scheme.carrier
    haveI := hasDerivedCategorySpaceZariskiSheaf A'.obj.thickening.target.scheme.carrier
    Nonempty (Formula07MK.{u + 2, u + 2} S S' fS fX hf A')

end Formula

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
