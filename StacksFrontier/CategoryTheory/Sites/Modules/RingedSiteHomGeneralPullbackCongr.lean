module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSiteGeneral

/-!
# Pullback of modules along isomorphic morphisms of ringed sites

Two morphisms of ringed sites `g₁ g₂ : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` whose underlying continuous functors
are isomorphic, by an isomorphism `e : g₁.u ≅ g₂.u` that carries the structure map of `g₂` to
that of `g₁`, induce isomorphic pullbacks of sheaves of modules, `g₁^* ≅ g₂^*`.

The two pushforwards are isomorphic — pushforward is restriction along the continuous functor,
transported along `e`, with the module structures matched by the compatibility of the two
structure maps — and the pullbacks are their left adjoints.

This is the form in which the remark of Topologies, Section 03FE that "the composition of two of
the morphisms of sites above is the corresponding morphism of sites" is used on modules: two
composites of morphisms of ringed sites with the same source and target are in general not
equal, only isomorphic in this sense, and together with Modules on Sites, Lemma 03D8
(`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralCompIso`) it identifies their
pullbacks.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso`: the isomorphism
  `g₁^* ≅ g₂^*`.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.fSharpRing_comp_sheafPushforwardContinuousNatTrans`:
  the compatibility of the structure maps, read on sheaves of not necessarily commutative rings.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The compatibility of the structure maps of two morphisms of ringed sites with an isomorphism
`e` of their underlying functors, read on the underlying sheaves of not necessarily commutative
rings.  Forgetting commutativity is applied componentwise, so this is the image of the
compatibility under `forget₂ CommRingCat RingCat`. -/
public theorem HomGeneral.fSharpRing_comp_sheafPushforwardContinuousNatTrans
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (g₁ g₂ : HomGeneral X Y) (e : g₁.u ≅ g₂.u)
    (he : g₂.fsharp ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom CommRingCat.{w}
      Y.J X.J).app X.O = g₁.fsharp) :
    g₂.toRingedToposSiteHom.fSharpRing ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom
      RingCat.{w} Y.J X.J).app (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) =
      g₁.toRingedToposSiteHom.fSharpRing := by
  ext U : 3
  exact ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
    (congrArg (fun φ => (forget₂ CommRingCat RingCat).map (φ.hom.app U)) he)

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Isomorphic morphisms of ringed sites have isomorphic pullbacks.**  If the underlying
functors of `g₁ g₂ : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` are isomorphic by `e`, and `e` carries the structure
map `𝒪_Y ⟶ g₂_*𝒪_X` to `𝒪_Y ⟶ g₁_*𝒪_X`, then `g₁^* ≅ g₂^*` on sheaves of modules.

Both are left adjoints, of `g₁_*` and `g₂_*`, and those are isomorphic by
`SheafOfModules.pushforwardCongr₂`; uniqueness of left adjoints finishes. -/
public def HomGeneral.pullbackModulesGeneralIsoOfIso (g₁ g₂ : HomGeneral X Y)
    (e : g₁.u ≅ g₂.u)
    (he : g₂.fsharp ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom CommRingCat.{w}
      Y.J X.J).app X.O = g₁.fsharp) :
    g₁.pullbackModulesGeneral ≅ g₂.pullbackModulesGeneral :=
  haveI := g₁.toRingedToposSiteHom.isContinuous
  haveI := g₂.toRingedToposSiteHom.isContinuous
  g₁.pullbackAdjPushforwardModulesGeneral.leftAdjointUniq
    (g₂.pullbackAdjPushforwardModulesGeneral.ofNatIsoRight
      (SheafOfModules.pushforwardCongr₂ _ e
        (g₁.fSharpRing_comp_sheafPushforwardContinuousNatTrans g₂ e he)))

end AlgebraicGeometry.RingedSite

end
