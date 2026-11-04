module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# The two pullbacks of sheaves of modules along a morphism of ringed sites agree

A morphism of ringed sites `f : X ⟶ Y` of Stacks 03AD part (2) gives rise to two morphisms of
ringed topoi, and Stacks 03D6 attaches a pushforward and a pullback of sheaves of modules to
each of them:

* `AlgebraicGeometry.RingedSite.Hom.ringedToposHom` records the geometric morphism as an
  adjoint pair of functors between the topoi, and
  `Stacks.Sheaves.RingedToposModules.pushforwardModules` transports the module structure along
  the direct image `f_*` of sheaves of sets;
* `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` keeps the presentation by the functor
  `u` of the underlying sites, and `AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos` is
  Mathlib's `SheafOfModules.pushforward` along `u`, which restricts scalars with no transport.

The derived development — the derived pullback of Stacks 06YY and everything above it — is
stated over the second; the Stacks 03D1/03D2/03D3 development of the module structures, and
with it the localization squares, over the first. This file identifies the two, first on the
pushforward and then, by uniqueness of left adjoints, on the pullback.

Both pushforwards have the same underlying sheaf of sets, namely the direct image `f_*` of the
underlying sheaf of sets of the module, and the identification is the identity there; what has
to be checked is that the transported addition and scalar action agree with the restricted
ones. Both checks reduce, on sections over an object `Z` of the target site, to the fact that
the composite of `f_*` with the sections functor at `Z` *is* the sections functor at `u(Z)`:
that is `AlgebraicGeometry.RingedSite.Hom.sectionsComparison`, and `app_moduleAddObj` and
`app_moduleSMulObj` below read the transported operations through it.

## Main definitions

* `CategoryTheory.Sheaf.app_moduleAddObj` and `CategoryTheory.Sheaf.app_moduleSMulObj`: an
  operation transported along a functor to types which maps to a sections functor is the
  original operation on sections.
* `AlgebraicGeometry.RingedSite.Hom.sectionsComparison`: the sections functor at `Z` of the
  direct image is the sections functor at `u(Z)`.
* `AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso`: the two pushforwards of sheaves of
  modules agree.
* `AlgebraicGeometry.RingedSite.Hom.pushforwardModulesToposIso`: the same comparison starting
  from the four-field morphism of ringed topoi of the modules development.
* `AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`: the two pullbacks of sheaves of
  modules agree.
* `AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom`: a site-presented morphism of ringed
  topoi whose underlying functor is a morphism of sites, read as a morphism of ringed sites.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (G : SheafOfModules.{w} R)
  {P : Sheaf J (Type w) ⥤ Type w} [Limits.PreservesFiniteProducts P] {W : Cᵒᵖ}
  (θ : P ⟶ Sheaf.sectionsFunctor J W)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Addition transported along a functor `P` to types, read through a transformation from `P`
to the sections functor at `W`, is the addition of the sections over `W`. -/
theorem app_moduleAddObj (x y : P.obj (Sheaf.moduleSheaf R G)) :
    θ.app _ (Sheaf.moduleAddObj R G P x y) = θ.app _ x + θ.app _ y :=
  (Sheaf.moduleAddObj_naturality R G θ x y).trans
    (Sheaf.sectionsFunctor_map_moduleAddHom R G W _ _)

/-- Scalar multiplication transported along a functor `P` to types, read through a
transformation from `P` to the sections functor at `W`, is the scalar multiplication of the
sections over `W`. -/
theorem app_moduleSMulObj (r : P.obj (Sheaf.ringSheaf R))
    (x : P.obj (Sheaf.moduleSheaf R G)) :
    θ.app _ (Sheaf.moduleSMulObj R G P r x) = θ.app _ r • θ.app _ x :=
  (Sheaf.moduleSMulObj_naturality R G θ r x).trans
    (Sheaf.sectionsFunctor_map_moduleSMulHom R G W _ _)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The sections over `Z` of the direct image of a sheaf of sets along a morphism of ringed
sites are the sections over `u(Z)`: the direct image is restriction along `u`, so the composite
of the direct image with the sections functor at `Z` is the sections functor at `u(Z)`, on the
nose. -/
def Hom.sectionsComparison (Z : Y.Cᵒᵖ) :
    (f.toposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z) ⟶
      Sheaf.sectionsFunctor X.J (f.u.op.obj Z) where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- **The two pushforwards of a sheaf of modules along a morphism of ringed sites agree.** The
underlying sheaf of sets is the direct image on both sides and the comparison is the identity
there; the transported addition and scalar action of the topos-theoretic pushforward are the
restricted ones of Mathlib's pushforward because the direct image followed by sections over `Z`
is sections over `u(Z)`.

That the scalars are restricted along the same morphism of sheaves of rings is definitional:
the structure map of `ringedToposHom` is `f♯` composed with the identification of the inverse
image of a sheaf of commutative rings with its restriction along `u`, and that identification
is the identity on sections. -/
def Hom.pushforwardToposObjIso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)) :
    f.ringedToposHom.pushforwardModules.obj F ≅
      f.toRingedToposSiteHom.pushforwardTopos.obj F where
  hom := ofSheafHom.{u, u, u} (𝟙 _)
    (fun Z x y ↦ Sheaf.app_moduleAddObj _ F (f.sectionsComparison Z) x y)
    (fun Z _ x ↦ Sheaf.app_moduleSMulObj _ F (f.sectionsComparison Z) _ x)
  inv := ofSheafHom.{u, u, u} (𝟙 _)
    (fun Z x y ↦ (Sheaf.app_moduleAddObj _ F (f.sectionsComparison Z) x y).symm)
    (fun Z _ x ↦ (Sheaf.app_moduleSMulObj _ F (f.sectionsComparison Z) _ x).symm)
  hom_inv_id := hom_ext_moduleSheafFunctor.{u, u, u} rfl
  inv_hom_id := hom_ext_moduleSheafFunctor.{u, u, u} rfl

/-- **Stacks 03D6 part (1) is independent of the presentation of the morphism of ringed
topoi.** The pushforward of sheaves of modules built from the adjoint-pair presentation of the
geometric morphism of a morphism of ringed sites is the pushforward built from its presentation
by the functor of the underlying sites. The components are
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposObjIso` and naturality holds on underlying
sheaves of sets, where both functors are the direct image. -/
def Hom.pushforwardToposIso :
    f.ringedToposHom.pushforwardModules ≅ f.toRingedToposSiteHom.pushforwardTopos :=
  NatIso.ofComponents (fun F ↦ f.pushforwardToposObjIso F)
    fun _ ↦ hom_ext_moduleSheafFunctor.{u, u, u} rfl

/-- The pushforward of sheaves of modules of the modules development, taken along the four-field
morphism of ringed topoi attached to a morphism of ringed sites, is Mathlib's pushforward along
the functor of the underlying sites.

This composes `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`, which compares the
four-field and the two-field presentations, with
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso`. -/
def Hom.pushforwardModulesToposIso :
    pushforwardModules (X := ringedTopos X) (Y := ringedTopos Y)
        f.ringedToposHom.toRingedToposModulesHom ≅
      f.toRingedToposSiteHom.pushforwardTopos :=
  AlgebraicGeometry.RingedToposHom.pushforwardModulesIso f.ringedToposHom ≪≫
    f.pushforwardToposIso

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 03D6 part (2) is independent of the presentation of the morphism of ringed
topoi.** The pullback of sheaves of modules of the modules development, taken along the
four-field morphism of ringed topoi attached to a morphism of ringed sites, is Mathlib's
pullback along the functor of the underlying sites.

Both are left adjoints of the two pushforwards, which agree by
`AlgebraicGeometry.RingedSite.Hom.pushforwardModulesToposIso`, so this is uniqueness of left
adjoints. -/
def Hom.pullbackModulesToposIso :
    f.ringedToposHom.toRingedToposModulesHom.pullbackModules ≅
      f.toRingedToposSiteHom.pullbackTopos :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules f.ringedToposHom.toRingedToposModulesHom).ofNatIsoRight
      f.pushforwardModulesToposIso)
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- A site-presented morphism of ringed topoi whose underlying functor is a morphism of sites
is a morphism of the associated ringed sites: a `RingedToposSiteHom` asks only for continuity
of `u`, and a morphism of ringed sites is the same two data together with the stronger
property. -/
def Hom.ofRingedToposSiteHom {X' Y' : AlgebraicGeometry.RingedTopos.{u, u, u}}
    (g : AlgebraicGeometry.RingedToposSiteHom X' Y')
    (hmos : g.u.IsMorphismOfSites Y'.J X'.J) :
    RingedSite.Hom X'.toRingedSite Y'.toRingedSite where
  u := g.u
  isMorphismOfSites := hmos
  fsharp := g.fSharp

/-- The site-presented morphism of ringed topoi attached to
`AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom g hmos` is `g`. -/
@[simp]
theorem Hom.toRingedToposSiteHom_ofRingedToposSiteHom
    {X' Y' : AlgebraicGeometry.RingedTopos.{u, u, u}}
    (g : AlgebraicGeometry.RingedToposSiteHom X' Y')
    (hmos : g.u.IsMorphismOfSites Y'.J X'.J) :
    (Hom.ofRingedToposSiteHom g hmos).toRingedToposSiteHom = g :=
  rfl

end AlgebraicGeometry.RingedSite

end
