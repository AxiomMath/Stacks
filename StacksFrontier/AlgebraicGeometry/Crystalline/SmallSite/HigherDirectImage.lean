module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ToposFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiToposMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness

/-!
# Higher direct images along a morphism of small crystalline topoi

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes over `ℤ_(p)` and let
`f : X ⟶ X'` be a morphism of schemes over the closed fibres `S₀ ⟶ S'₀`, with `p` locally
nilpotent on `X` and `X'`.  The derived direct image of an `O_{X/S}`-module along `f_cris` is
computed thickening by thickening: an object `(U', T', δ')` of `Cris(X'/S')` gives
`U = X ×_{X'} U'`, an open subscheme of `X`, and the divided power scheme `T = S ×_{S'} T'`, and
`U/T` is again a global crystalline situation receiving a morphism `(U/T)_cris ⟶ (X/S)_cris`.

This file constructs that situation, that morphism, the structure morphism
`τ_{U/T} : (U/T)_cris ⟶ Sh(T_Zar)` and the pullback `F ↦ F_U`, which are the data the remark's
recipe is assembled from.  The displayed equation of the remark,
`(Rf_{cris, *} F)_{T'} = R(T ⟶ T')_* (R τ_{U/T, *} F_U)`, is not proved here: the Stacks project
states it without proof and gives only hints.

## Main definitions

* `Crystalline.SchemeThickening.toClosedFiber` — the identification of the thickened scheme of a
  divided power thickening with the closed fibre of its ambient divided power scheme.
* `Crystalline.GlobalCrystallineSituation.pullbackSituation` — the crystalline situation `U/T`
  attached to an object `(U', T', δ')` of `Cris(X'/S')`.
* `Crystalline.GlobalCrystallineSituation.pullbackCrisMorphism` — the morphism of small
  crystalline topoi `(U/T)_cris ⟶ (X/S)_cris`.
* `Crystalline.GlobalCrystallineSituation.structureToposMorphism` — the structure morphism
  `τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)`, and
  `Crystalline.GlobalCrystallineSituation.pullbackStructureToposMorphism` its instance
  `τ_{U/T}` for the situation `U/T`.
* `Crystalline.GlobalCrystallineSituation.pullbackSheaf` — the pullback `F_U` of a sheaf `F` on
  `Cris(X/S)` along that morphism.

## Main results

* `Crystalline.GlobalCrystallineSituation.isOpenImmersion_pullbackSituationToX` and
  `Crystalline.GlobalCrystallineSituation.range_pullbackSituationToX` — `U` is the open
  subscheme `f⁻¹(U')` of `X`.
* `Crystalline.GlobalCrystallineSituation.pullbackSituation_isPullback` — the square with `T`,
  `T'`, `S` and `S'` is cartesian in divided power schemes.
* `Crystalline.GlobalCrystallineSituation.pullbackToClosedFiber_comp_fst` and
  `..._comp_snd` — the induced morphism `U ⟶ T₀` has the two expected projections.

## Implementation notes

The divided power fibre product `T = S ×_{S'} T'` is the one supplied by [Stacks, Tag 07ME], and
`U = X ×_{X'} U'` is the scheme-theoretic fibre product; that `U ⟶ X` is an open immersion with
image `f⁻¹(U')` is base change of the open immersion `U' ⟶ X'`.  The induced morphism `U ⟶ T₀` is
built from the identification `T₀ = S₀ ×_{S'₀} T'₀` of [Stacks, Tag 07ME] together with
`SchemeThickening.toClosedFiber`, which identifies `U'` with `T'₀`: the thickened scheme of a
divided power thickening is a presentation of the closed fibre of its ambient scheme, because the
ideal of its closed immersion is the divided power ideal.

The morphism `(U/T)_cris ⟶ (X/S)_cris` is the one of [Stacks, Tag 07IK], which is unconditional:
left exactness of `i_!` for `X/S` is
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`.
The structure morphism `τ_{X/S}` is the composite of [Stacks, Tag 07IM]; the small Zariski half of
it is the morphism of topoi of [Stacks, Tag 00X2] at the sheaf universe of the crystalline topos,
whose left exactness comes from representable flatness of `Opens.map g` through the
universe-general Kan extension exactness of
`CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace StacksZariskiSite

/-- The morphism of small Zariski topoi `Sh(X_Zar) ⟶ Sh(Y_Zar)` induced by a continuous map
`g : X ⟶ Y`, for sheaves of sets one universe above that of the spaces.  Its direct image is the
topological `g_*` and its inverse image the topological `g⁻¹`, which is left exact because
`Opens.map g` is representably flat, [Stacks, Tag 00X2]. -/
def opensMapMorphismOfTopoi {X Y : TopCat.{u}} (g : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (Opens.grothendieckTopology X) (Type (u + 1)))
      (Sheaf (Opens.grothendieckTopology Y) (Type (u + 1))) :=
  haveI : PreservesFiniteLimits ((Opens.map g).op.lan :
      ((Opens Y)ᵒᵖ ⥤ Type (u + 1)) ⥤ (Opens X)ᵒᵖ ⥤ Type (u + 1)) :=
    lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u, u} (Opens.map g)
  { pushforward := (Opens.map g).sheafPushforwardContinuous (Type (u + 1))
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    inverseImage := (Opens.map g).sheafPullback (Type (u + 1))
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    adj := (Opens.map g).sheafAdjunctionContinuous (Type (u + 1))
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    preservesFiniteLimits :=
      Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _ }

end StacksZariskiSite

namespace Crystalline

namespace SchemeThickening

variable (D : SchemeThickening.{u})

/-- **The thickened scheme of a divided power thickening presents the closed fibre of its ambient
divided power scheme.**  The immersion is a closed immersion whose ideal is, on affine opens, the
divided power ideal of the ambient scheme. -/
def closedFiberPresentation : DividedPowerScheme.ClosedFiberPresentation D.target where
  carrier := D.source
  ι := D.immersion
  isClosedImmersion := inferInstance
  app_eq_zero_of_mem V s hs := D.immersion_app_eq_zero_of_mem V s hs
  mem_of_app_eq_zero V s hs := by
    have h : s ∈ D.immersion.ker.ideal V := by
      rw [Scheme.Hom.ker_apply]
      exact RingHom.mem_ker.2 hs
    rw [← D.ideal_eq_ker V] at h
    exact h

/-- The identification of the thickened scheme `U` of a divided power thickening `U ↪ T` with the
closed fibre `T₀` of the ambient divided power scheme. -/
def toClosedFiber : D.source ⟶ DividedPowerScheme.closedFiber D.target :=
  (D.closedFiberPresentation.isoOfPresentations
    (DividedPowerScheme.closedFiberPresentation D.target)).hom

/-- The identification of `U` with `T₀` is compatible with the two closed immersions into `T`. -/
@[reassoc (attr := simp)]
theorem toClosedFiber_comp_closedFiberι :
    D.toClosedFiber ≫ DividedPowerScheme.closedFiberι D.target = D.immersion :=
  DividedPowerScheme.ClosedFiberPresentation.isoOfPresentations_hom_comp_ι _ _

/-- The identification of `U` with `T₀` is an isomorphism, two presentations of a closed fibre
being canonically isomorphic. -/
instance isIso_toClosedFiber : IsIso D.toClosedFiber :=
  Iso.isIso_hom _

end SchemeThickening

namespace GlobalCrystallineSituation

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

/-- The divided power scheme `T = S ×_{S'} T'` of [Stacks, Tag 07MJ], the fibre product of the
divided power base `S` and the ambient divided power scheme of `(U', T', δ')` over `S'`. -/
abbrev pullbackBase : DividedPowerScheme.{u} := pullback fS A'.obj.toBase

/-- The scheme `U = X ×_{X'} U'` of [Stacks, Tag 07MJ]. -/
abbrev pullbackSource : Scheme.{u} := pullback fX A'.obj.toX

/-- The structure morphism `U ⟶ S₀` of `U` over the closed fibre of `S`, through `U ⟶ X`. -/
abbrev pullbackSourceToClosedFiber : pullbackSource S S' fX A' ⟶ closedFiber S.S :=
  pullback.fst fX A'.obj.toX ≫ S.toClosedFiber

/-- The identification of the thickened scheme `U'` of `(U', T', δ')` with the closed fibre `T'₀`
carries the structure morphism `T'₀ ⟶ S'₀` to the structure morphism `U' ⟶ X' ⟶ S'₀`. -/
theorem toClosedFiber_comp_closedFiberMap_toBase :
    A'.obj.thickening.toClosedFiber ≫ closedFiberMap A'.obj.toBase =
      A'.obj.toX ≫ S'.toClosedFiber := by
  rw [← cancel_mono (closedFiberι S'.S), Category.assoc, Category.assoc,
    closedFiberMap_comp_closedFiberι, SchemeThickening.toClosedFiber_comp_closedFiberι_assoc]
  exact A'.obj.over_base

include hf in
/-- The two morphisms `U ⟶ S₀` and `U ⟶ T'₀` agree over `S'₀`. -/
theorem pullbackSource_closedFiber_condition :
    pullbackSourceToClosedFiber S S' fX A' ≫ closedFiberMap fS =
      (pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.toClosedFiber) ≫
        closedFiberMap A'.obj.toBase := by
  simp only [pullbackSourceToClosedFiber, Category.assoc, hf,
    toClosedFiber_comp_closedFiberMap_toBase]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- **Stacks Project, Tag 07MJ.**  The induced morphism `U ⟶ T₀` of the remark: the closed fibre
of `T = S ×_{S'} T'` is `S₀ ×_{S'₀} T'₀` by [Stacks, Tag 07ME], and `U = X ×_{X'} U'` maps to `S₀`
through `X` and to `T'₀ = U'` through `U'`. -/
@[stacks 07MJ "the induced morphism U ⟶ T₀, for T = S ×_{S'} T' and U = X ×_{X'} U'"]
def pullbackToClosedFiber : pullbackSource S S' fX A' ⟶ closedFiber (pullbackBase S S' fS A') :=
  haveI := closedFiberPullbackComparison_isIso fS A'.obj.toBase
  pullback.lift (pullbackSourceToClosedFiber S S' fX A')
      (pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.toClosedFiber)
      (pullbackSource_closedFiber_condition S S' fS fX hf A') ≫
    inv (closedFiberPullbackComparison fS A'.obj.toBase)

/-- The induced morphism `U ⟶ T₀`, followed by `T₀ ⟶ S₀`, is the structure morphism of `U` over
`S₀` through `U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem pullbackToClosedFiber_comp_fst :
    pullbackToClosedFiber S S' fS fX hf A' ≫ closedFiberMap (pullback.fst fS A'.obj.toBase) =
      pullbackSourceToClosedFiber S S' fX A' := by
  have := closedFiberPullbackComparison_isIso fS A'.obj.toBase
  rw [pullbackToClosedFiber, Category.assoc, ← closedFiberPullbackComparison_fst,
    IsIso.inv_hom_id_assoc, pullback.lift_fst]

/-- The induced morphism `U ⟶ T₀`, followed by `T₀ ⟶ T'₀`, is `U ⟶ U' = T'₀`. -/
@[reassoc (attr := simp)]
theorem pullbackToClosedFiber_comp_snd :
    pullbackToClosedFiber S S' fS fX hf A' ≫ closedFiberMap (pullback.snd fS A'.obj.toBase) =
      pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.toClosedFiber := by
  have := closedFiberPullbackComparison_isIso fS A'.obj.toBase
  rw [pullbackToClosedFiber, Category.assoc, ← closedFiberPullbackComparison_snd,
    IsIso.inv_hom_id_assoc, pullback.lift_snd]

/-- **Stacks Project, Tag 07MJ.**  The crystalline situation `U/T` of the remark attached to an
object `(U', T', δ')` of `Cris(X'/S')`: the divided power base is the fibre product
`T = S ×_{S'} T'` of [Stacks, Tag 07ME], the scheme is `U = X ×_{X'} U'`, and the structure
morphism to `T₀` is `pullbackToClosedFiber`.  The prime `p` is locally nilpotent on `U` because it
is on `X` and `U ⟶ X` induces maps on local rings. -/
@[stacks 07MJ "the crystalline situation U/T attached to an object (U', T', δ') of Cris(X'/S')"]
def pullbackSituation : GlobalCrystallineSituation.{u} where
  p := S.p
  S := pullbackBase S S' fS A'
  algebraAtPrime :=
    (((pullback.fst fS A'.obj.toBase).hom.appTop).hom.comp
      (algebraMap (DividedPowers.IntegersAtPrime S.p) Γ(S.S.scheme, ⊤))).toAlgebra
  X := pullbackSource S S' fX A'
  toClosedFiber := pullbackToClosedFiber S S' fS fX hf A'
  prime_locallyNilpotent x := by
    have h := S.prime_locallyNilpotent ((pullback.fst fX A'.obj.toX).base x)
    simpa using h.map ((pullback.fst fX A'.obj.toX).stalkMap x).hom

/-- The situation `U/T` has the same prime as `X/S`. -/
@[simp]
theorem pullbackSituation_p : (pullbackSituation S S' fS fX hf A').p = S.p := rfl

/-- The divided power base of the situation `U/T` is `T = S ×_{S'} T'`. -/
@[simp]
theorem pullbackSituation_S :
    (pullbackSituation S S' fS fX hf A').S = pullbackBase S S' fS A' := rfl

/-- The scheme of the situation `U/T` is `U = X ×_{X'} U'`. -/
@[simp]
theorem pullbackSituation_X :
    (pullbackSituation S S' fS fX hf A').X = pullbackSource S S' fX A' := rfl

/-- The structure morphism of the situation `U/T` to the closed fibre `T₀` is the induced
morphism `U ⟶ T₀`. -/
@[simp]
theorem pullbackSituation_toClosedFiber :
    (pullbackSituation S S' fS fX hf A').toClosedFiber =
      pullbackToClosedFiber S S' fS fX hf A' := rfl

/-- The square with `T ⟶ T'`, `T ⟶ S`, `S ⟶ S'` and `T' ⟶ S'` is cartesian in the category of
divided power schemes, `T` being defined as that fibre product. -/
theorem pullbackSituation_isPullback :
    IsPullback (pullback.fst fS A'.obj.toBase) (pullback.snd fS A'.obj.toBase) fS
      A'.obj.toBase :=
  IsPullback.of_hasPullback fS A'.obj.toBase

/-- **Stacks Project, Tag 07MJ.**  `U = X ×_{X'} U'` is an open subscheme of `X`, the morphism
`U' ⟶ X'` of an object of the small crystalline site being an open immersion. -/
@[stacks 07MJ "U = X ×_{X'} U' is an open subscheme of X"]
theorem isOpenImmersion_pullbackSituationToX :
    IsOpenImmersion (pullback.fst fX A'.obj.toX) :=
  have : IsOpenImmersion A'.obj.toX := A'.property
  inferInstance

/-- **Stacks Project, Tag 07MJ.**  The open subscheme `U = X ×_{X'} U'` of `X` is `f⁻¹(U')`: its
image in `X` is the preimage under `f` of the image of `U'` in `X'`. -/
@[stacks 07MJ "U = X ×_{X'} U' is f⁻¹(U')"]
theorem range_pullbackSituationToX :
    Set.range (pullback.fst fX A'.obj.toX) = fX ⁻¹' Set.range A'.obj.toX :=
  Scheme.Pullback.range_fst fX A'.obj.toX

/-- The structure morphism `U ⟶ X` is a morphism over the closed fibres: this is the compatibility
required to form the morphism of small crystalline topoi `(U/T)_cris ⟶ (X/S)_cris`. -/
theorem pullbackSituation_comm :
    (pullbackSituation S S' fS fX hf A').toClosedFiber ≫
        closedFiberMap (pullback.fst fS A'.obj.toBase) =
      pullback.fst fX A'.obj.toX ≫ S.toClosedFiber :=
  pullbackToClosedFiber_comp_fst S S' fS fX hf A'

/-- The morphism of small crystalline topoi `(U/T)_cris ⟶ (X/S)_cris` induced by `U ⟶ X` over
`T ⟶ S`, [Stacks, Tag 07IK]. It is unconditional, left exactness of `i_!` for `X/S` being
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`.
-/
@[stacks 07MJ "the morphism (U/T)_cris ⟶ (X/S)_cris"]
def pullbackCrisMorphism :
    MorphismOfTopoi (smallTopos (pullbackSituation S S' fS fX hf A')) (smallTopos S) :=
  crisMorphism (pullbackSituation S S' fS fX hf A') S (pullback.fst fS A'.obj.toBase)
    (pullback.fst fX A'.obj.toX) (pullbackSituation_comm S S' fS fX hf A')

/-- **Stacks Project, Tag 07IM.**  The structure morphism
`τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)`: the comparison `u_{X/S}` of [Stacks, Tag 07IL] followed by the
small Zariski morphism along the structure morphism `X ⟶ S`.  This is the lower route of the
remark's diagram, so it is defined whether or not `p` is locally nilpotent on the closed fibre
`S₀ = V(I)`. -/
@[stacks 07IM "the structure morphism τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar), taken along the lower
  route of the diagram, so defined whether or not p is locally nilpotent on S₀"]
def structureToposMorphism (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (smallTopos S)
      (Sheaf (Opens.grothendieckTopology S.S.scheme.carrier) (Type (u + 1))) :=
  (StacksZariskiSite.opensMapMorphismOfTopoi (sourceToBase S).base).comp
    (zariskiToposMorphism S)

/-- **Stacks Project, Tag 07MJ.**  The structure morphism `τ_{U/T} : (U/T)_cris ⟶ Sh(T_Zar)` of
the remark. -/
@[stacks 07MJ "the structure morphism τ_{U/T} : (U/T)_cris ⟶ Sh(T_Zar)"]
def pullbackStructureToposMorphism :
    MorphismOfTopoi (smallTopos (pullbackSituation S S' fS fX hf A'))
      (Sheaf (Opens.grothendieckTopology (pullbackBase S S' fS A').scheme.carrier)
        (Type (u + 1))) :=
  structureToposMorphism (pullbackSituation S S' fS fX hf A')

/-- **Stacks Project, Tag 07MJ.**  The pullback `F_U` to `Cris(U/T)` of a sheaf `F` on
`Cris(X/S)`. -/
@[stacks 07MJ "the pullback F_U of a sheaf on Cris(X/S) to Cris(U/T); the displayed equation
  (07MK) is Crystalline.GlobalCrystallineSituation.SmallSite.computes07MK"]
def pullbackSheaf (F : smallTopos S) : smallTopos (pullbackSituation S S' fS fX hf A') :=
  (pullbackCrisMorphism S S' fS fX hf A').inverseImage.obj F

end GlobalCrystallineSituation

end Crystalline

end
