module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalarsConverse
import StacksCore.Tactic.StacksAttribute

/-!
# The Milnor condition descends along a conservative direct image

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, `V` an object of `𝒞` and `g` a
section of `𝒪` over `V`. The forward implication
`AlgebraicGeometry.RingedSite.isDerivedCompleteAt_derivedPushforward_overFunctor` of
[Stacks, Tag 099J] reads the Milnor condition `T((Rf_*K)|_V, g) = 0` off
`T(K|_{u(V)}, f^♯g) = 0`. This file proves the converse implication, for a morphism whose direct
image on the slice at `V` reflects isomorphisms.

Both directions rest on the same two facts, and the proofs run in parallel: the restriction of
`Rf_*K` to the slice at `V` is the direct image along the localized morphism of the restriction
of `K` to the slice at `u(V)` ([Stacks, Tag 0D6G]), and that direct image is additive, preserves
the countable power and carries multiplication by `f^♯g` to multiplication by `g`. The Milnor
condition is the invertibility of `1 - g·shift`; a functor with those three properties carries
the Milnor difference at `f^♯g` to the Milnor difference at `g`, so the forward direction is that
it preserves isomorphisms and this one is that it reflects them.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedCompleteAtSection_of_derivedPushforward`: if the
  localized derived direct image at `V` reflects isomorphisms, then `T((Rf_*K)|_V, g) = 0`
  forces `T(K|_{u(V)}, f^♯g) = 0`.

## Implementation notes

The hypothesis is carried as an explicit argument rather than an instance binder: the functor
`Stacks.Cohomology.Localization.derivedLocalizedPushforward` is a reducible abbreviation over a
total right derived functor, and instance search does not key on that shape. It is discharged for
the restriction along a dense subsite in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/DenseSubsiteDescent.lean`.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.Localization
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

-- The slice data of [Stacks, Tag 0999], as it is set up in
-- `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Pushforward.lean`:
-- commutativity of the rings of sections in both spellings of a localized structure sheaf,
-- continuity, additivity and exactness of the functors in play, the linear structure the Milnor
-- condition is stated at, and the countable products of the derived category of a slice.
attribute [local instance] isMulComm isMulCommLocalized isContinuous_localized
  Stacks.Cohomology.Localization.additive_localizedPushforward
  overFunctorPreservesFiniteLimits overFunctorPreservesFiniteColimits overLinear
  overHasProductsOfShapeNat

/-- **The Milnor condition descends along a conservative direct image.** If the derived direct
image along the morphism of ringed sites localized at `V` reflects isomorphisms and
`T((Rf_*K)|_V, g) = 0`, then `T(K|_{u(V)}, f^♯g) = 0`.

By [Stacks, Tag 0D6G] the restriction of `Rf_*K` to the slice at `V` is the localized direct
image of the restriction of `K` to the slice at `u(V)`; that direct image is a right adjoint, by
[Stacks, Tag 07A6] and [Stacks, Tag 05VD], hence additive and preserving of the countable power,
and it carries multiplication by `f^♯g` to multiplication by `g`. So it carries the Milnor
difference at `f^♯g` to the Milnor difference at `g`, and a functor reflecting isomorphisms
returns the invertibility of the first from that of the second. -/
theorem isDerivedCompleteAt_of_derivedPushforward_overFunctor
    (hrefl : (derivedLocalizedPushforward f V).ReflectsIsomorphisms)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V))
    (hKV : IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          V).mapDerivedCategory.obj
        ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K))
      (idealScalar Y V g)) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (f.u.obj V)).mapDerivedCategory.obj K)
      (idealScalar X (f.u.obj V) (fSharpSection f V g)) := by
  let := hrefl
  -- the slice data of [Stacks, Tag 0999] on the target, in both spellings
  let RV := ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).over V
  let AV := SheafOfModules.{u} RV
  let : Linear (CatCenter AV) AV := Linear.ofRingMorphism (RingHom.id (CatCenter AV))
  let : ∀ W : (Over V)ᵒᵖ, IsMulCommutative (RV.obj.obj W) := fun W ↦ by
    show IsMulCommutative (Y.O.obj.obj (op W.unop.left))
    infer_instance
  have hProdV : HasProductsOfShape ℕ (DerivedCategory AV) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, u, u} Y V
  let := hProdV
  -- the same on the source
  let RU := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (f.u.obj V)
  let AU := SheafOfModules.{u} RU
  let : Linear (CatCenter AU) AU := Linear.ofRingMorphism (RingHom.id (CatCenter AU))
  let : ∀ W : (Over (f.u.obj V))ᵒᵖ, IsMulCommutative (RU.obj.obj W) := fun W ↦ by
    show IsMulCommutative (X.O.obj.obj (op W.unop.left))
    infer_instance
  have hProdU : HasProductsOfShape ℕ (DerivedCategory AU) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, u, u} X (f.u.obj V)
  let := hProdU
  let AU' := SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (f.u.obj V)).ringedTopos.O))
  let : Linear (CatCenter AU) AU' := Linear.ofRingMorphism (RingHom.id (CatCenter AU))
  let AV' := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Y.over V).ringedTopos.O))
  let : Linear (CatCenter AV) AV' := Linear.ofRingMorphism (RingHom.id (CatCenter AV))
  -- `Rf_*` on the slices is a right adjoint, by Tags 07A6 and 05VD, hence additive and
  -- product-preserving
  have hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u} :=
    AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv.{u}
  have hmos := (f.localized V).isMorphismOfSites
  have hlfd := pullbackOnHomotopy_hasLeftDerivedFunctor_of_flatPullback
    (f.localized V).toRingedToposSiteHom hmos hpf
  let := hlfd
  have adj := derivedPullbackPushforwardAdjunctionOfFlatPullback
    (f.localized V).toRingedToposSiteHom hmos hpf
  have hpl0 : PreservesLimitsOfSize.{0, 0} (derivedLocalizedPushforward f V) :=
    adj.rightAdjoint_preservesLimits
  let := hpl0
  have hbp : PreservesLimitsOfShape (Discrete WalkingPair) (derivedLocalizedPushforward f V) :=
    hpl0.preservesLimitsOfShape
  let := hbp
  have hadd : (derivedLocalizedPushforward f V).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  let := hadd
  have hnat : PreservesLimitsOfShape (Discrete ℕ) (derivedLocalizedPushforward f V) :=
    hpl0.preservesLimitsOfShape
  let := hnat
  -- read the hypothesis on the localized direct image, through [Stacks, Tag 0D6G]
  replace hKV : IsDerivedCompleteAt
      ((derivedLocalizedPushforward f V).obj
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (f.u.obj V)).mapDerivedCategory.obj K))
      (idealScalar Y V g) :=
    (isDerivedCompleteAt_iff_of_iso
      ((Stacks.Cohomology.Localization.derivedRestrictionIso Y V).app
          ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ≪≫
        (derivedPushforwardOverFunctorIso f V).app K ≪≫
        (derivedLocalizedPushforward f V).mapIso
          ((Stacks.Cohomology.Localization.derivedRestrictionIso X (f.u.obj V)).app K).symm)
      (idealScalar Y V g)).mp hKV
  refine isDerivedCompleteAt_of_map_of_smul_id (derivedLocalizedPushforward f V) ?_ hKV
  -- the localized direct image intertwines multiplication by `f^♯ g` with multiplication by `g`
  have hadd0 : (f.localized V).toRingedToposSiteHom.pushforwardTopos.Additive :=
    RingedToposSiteHom.pushforwardTopos_additive.{u} _
  let := hadd0
  refine Stacks.SemilinearFunctor.map_smul_id_rightDerived
    (derivedPushforward.{u} (f.localized V).toRingedToposSiteHom)
    (derivedPushforwardUnit.{u} (f.localized V).toRingedToposSiteHom)
    (HomotopyCategory.quasiIso AU' (ComplexShape.up ℤ)) _ _
    (fun M => Stacks.SemilinearFunctor.map_smul_id_comp _ DerivedCategory.Qh _ _
      (Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory _ _ _ (fun N => ?_)
        (ComplexShape.up ℤ)) M) _
  exact Eq.trans
    (congrArg (fun h => (f.localized V).toRingedToposSiteHom.pushforwardTopos.map h)
      (Category.comp_id ((idealScalar X (f.u.obj V) (fSharpSection f V g)).app N)))
    ((localizedPushforward_map_idealScalar f V g N).trans (Category.comp_id _).symm)

/-- **The sectionwise form of the descent.** If the derived direct image along the morphism of
ringed sites localized at `V` reflects isomorphisms, then the Milnor condition for `Rf_*K` at a
section `g` of `𝒪` over `V` forces the Milnor condition for `K` at `f^♯g` over `u(V)`. -/
theorem isDerivedCompleteAtSection_of_derivedPushforward
    (hrefl : (derivedLocalizedPushforward f V).ReflectsIsomorphisms)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V))
    (hKV : IsDerivedCompleteAtSection Y
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) V g) :
    IsDerivedCompleteAtSection X K (f.u.obj V) (fSharpSection f V g) :=
  isDerivedCompleteAt_of_derivedPushforward_overFunctor f V hrefl K g hKV

/-- **The sectionwise form of [Stacks, Tag 099J] for a morphism of ringed sites.** The Milnor
condition for `K` at `f^♯g` over `u(V)` gives the Milnor condition for `Rf_*K` at `g` over `V`.
This is `isDerivedCompleteAt_derivedPushforward_overFunctor` read through the definition of
`IsDerivedCompleteAtSection`. -/
theorem isDerivedCompleteAtSection_derivedPushforward
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V))
    (hKU : IsDerivedCompleteAtSection X K (f.u.obj V) (fSharpSection f V g)) :
    IsDerivedCompleteAtSection Y
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) V g :=
  isDerivedCompleteAt_derivedPushforward_overFunctor f V K g hKU

end AlgebraicGeometry.RingedSite

end
