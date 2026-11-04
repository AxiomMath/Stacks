module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall

/-!
# The pullback of modules on the total Zariski site, read off the morphism of sites

`AlgebraicGeometry.SimplicialScheme.modulePullback` is the pullback `f^*` of sheaves of modules
along the morphism of Zariski ringed topoi
`AlgebraicGeometry.SimplicialScheme.zariskiRingedToposHom` of a morphism of simplicial schemes,
taken in the four-field presentation of Stacks 03D6 over which the module structures of
Stacks 03D1/03D2/03D3 are built. The same morphism is presented by the degreewise inverse image
of opens together with `f♯`, and over *that* presentation Stacks 03D6 part (2) is Mathlib's
`SheafOfModules.pullback`, a chosen left adjoint of `SheafOfModules.pushforward`.

This file identifies the two. `AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso` is the
same comparison, but it is stated for a `AlgebraicGeometry.RingedSite.Hom`, hence only for two
sites whose objects and morphisms share a universe; the total Zariski site has its objects in
`Type u` and its morphisms in `Type 0`, so it is not an endpoint of one. The pullback at
independent universes is `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, whose
hypotheses the total Zariski site satisfies: it is essentially small in the universe of the
schemes, and locally small.

The comparison is made on the pushforward and then transported to the pullback by uniqueness of
left adjoints, exactly as in the equi-universe case. On the pushforward both sides have the
direct image of the underlying sheaf of sets as their underlying sheaf, and the comparison is
the identity there; what is checked is that the transported addition and scalar action of the
topos-theoretic pushforward are the restricted ones of Mathlib's, which holds because the
direct image followed by the sections over `Z` *is* the sections over `f⁻¹Z`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.zariskiRingedToposSiteHom`: the morphism of Zariski
  ringed topoi of a morphism of simplicial schemes, presented by the degreewise inverse image
  of opens.
* `AlgebraicGeometry.SimplicialScheme.zariskiPushforwardSectionsComparison`: the sections of the
  direct image over `Z` are the sections over `f⁻¹Z`.
* `AlgebraicGeometry.SimplicialScheme.modulePullbackToposGeneralIso`: **the two pullbacks of
  sheaves of modules on the total Zariski site agree.**

## Main results

* `AlgebraicGeometry.SimplicialScheme.zariskiPushforwardToposObjIso` and
  `AlgebraicGeometry.SimplicialScheme.zariskiPushforwardToposIso`: the two pushforwards of
  sheaves of modules on the total Zariski site agree.

## Implementation notes

Every site in this file is spelled as the projection `(zariskiRingedTopos X).J` rather than as
`zariskiTopology X`. The two are definitionally equal, but `zariskiRingedTopos` is not unfolded
by instance search, so the two spellings carry different — definitionally equal — category
instances on `Sheaf _ (Type u)`, and a composite written with one spelling on the left and the
other on the right loses the `Limits.PreservesFiniteProducts` instance that
`CategoryTheory.Sheaf.app_moduleAddObj` consumes.

The universe arguments of `Stacks.Sheaves.RingedToposModules.ofSheafHom` and
`.hom_ext_moduleSheafFunctor` are given explicitly as `.{u, 0, u}`: the site has its objects in
`Type u`, its morphisms in `Type 0` and its module sections in `Type u`, and with the two sides
of the comparison spelled over different projections of the ring sheaf the elaborator does not
propagate the module universe into the binders of the additivity and the scalar clauses.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 09VN](https://stacks.math.columbia.edu/tag/09VN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- **The morphism of Zariski ringed topoi of a morphism of simplicial schemes, presented by
the morphism of the underlying sites.** The functor is the degreewise inverse image of opens
and the structure map is `f♯`; the same two data as
`AlgebraicGeometry.SimplicialScheme.zariskiRingedToposHom`, with the geometric morphism kept in
its site presentation rather than replaced by the adjoint pair it induces. -/
public def zariskiRingedToposSiteHom (f : V ⟶ U) :
    AlgebraicGeometry.RingedToposSiteHom (zariskiRingedTopos V) (zariskiRingedTopos U) where
  u := zariskiPullback f
  isContinuous := zariskiPullback_isContinuous f
  fSharp := zariskiSharp f

/-- The sections over `Z` of the direct image of a sheaf of sets along a morphism of simplicial
schemes are the sections over the degreewise inverse image `f⁻¹Z`: the direct image is
restriction along `f⁻¹`, so the composite of the direct image with the sections functor at `Z`
is the sections functor at `f⁻¹Z`, on the nose. The transformation is the identity on
sections. -/
public def zariskiPushforwardSectionsComparison (f : V ⟶ U) (Z : (zariskiRingedTopos U).Cᵒᵖ) :
    ((zariskiRingedToposHom f).toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor (zariskiRingedTopos U).J Z) ⟶
      Sheaf.sectionsFunctor (zariskiRingedTopos V).J ((zariskiPullback f).op.obj Z) where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- **The two pushforwards of a sheaf of modules on the total Zariski site agree**, at one
module. The underlying sheaf of sets is the direct image on both sides and the comparison is
the identity there; the transported addition and scalar action of the topos-theoretic
pushforward are the restricted ones of Mathlib's pushforward because the direct image followed
by the sections over `Z` is the sections over `f⁻¹Z`. -/
public def zariskiPushforwardToposObjIso (f : V ⟶ U)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos V).O)) :
    (zariskiRingedToposHom f).pushforwardModules.obj F ≅
      (zariskiRingedToposSiteHom f).pushforwardTopos.obj F where
  hom := ofSheafHom.{u, 0, u} (𝟙 _)
    (fun Z x y ↦
      Sheaf.app_moduleAddObj _ F (zariskiPushforwardSectionsComparison f Z) x y)
    (fun Z _ x ↦
      Sheaf.app_moduleSMulObj _ F (zariskiPushforwardSectionsComparison f Z) _ x)
  inv := ofSheafHom.{u, 0, u} (𝟙 _)
    (fun Z x y ↦
      (Sheaf.app_moduleAddObj _ F (zariskiPushforwardSectionsComparison f Z) x y).symm)
    (fun Z _ x ↦
      (Sheaf.app_moduleSMulObj _ F (zariskiPushforwardSectionsComparison f Z) _ x).symm)
  hom_inv_id := hom_ext_moduleSheafFunctor.{u, 0, u} rfl
  inv_hom_id := hom_ext_moduleSheafFunctor.{u, 0, u} rfl

/-- **Stacks 03D6 part (1) on the total Zariski site is independent of the presentation of the
morphism of ringed topoi.** The components are
`AlgebraicGeometry.SimplicialScheme.zariskiPushforwardToposObjIso` and naturality holds on
underlying sheaves of sets, where both functors are the direct image. -/
public def zariskiPushforwardToposIso (f : V ⟶ U) :
    (zariskiRingedToposHom f).pushforwardModules ≅
      (zariskiRingedToposSiteHom f).pushforwardTopos :=
  NatIso.ofComponents (fun F ↦ zariskiPushforwardToposObjIso f F)
    fun _ ↦ hom_ext_moduleSheafFunctor.{u, 0, u} rfl

/-- **Stacks 03D6 part (2) on the total Zariski site is independent of the presentation of the
morphism of ringed topoi.** The pullback `f^*` of
`AlgebraicGeometry.SimplicialScheme.modulePullback`, built over the four-field morphism of
ringed topoi, is Mathlib's pullback along the degreewise inverse image of opens.

Both are left adjoints of the two pushforwards, which agree by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` followed by
`AlgebraicGeometry.SimplicialScheme.zariskiPushforwardToposIso`, so this is uniqueness of left
adjoints. -/
public def modulePullbackToposGeneralIso (f : V ⟶ U) :
    modulePullback f ≅ (zariskiRingedToposSiteHom f).pullbackToposGeneral :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules
        (zariskiRingedToposHom f).toRingedToposModulesHom).ofNatIsoRight
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesIso (zariskiRingedToposHom f) ≪≫
        zariskiPushforwardToposIso f))
    (zariskiRingedToposSiteHom f).pullbackPushforwardAdjunctionToposGeneral

end AlgebraicGeometry.SimplicialScheme

end
