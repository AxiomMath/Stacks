module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction

/-!
# The internal Hom of `𝒪_F`-modules on an algebraic space

Clause (6) of Stacks 03M1 asserts that the internal Hom
`𝓗om_{𝒪_F}(G, G')` of two quasi-coherent `𝒪_F`-modules on an algebraic space is
quasi-coherent when `G` is of finite presentation.  This file supplies the sheaf that clause is
about — the internal Hom of `𝒪_F`-modules on the small étale ringed site — and the step of the
source proof that reduces the clause to a computation on étale charts: restriction to a slice
of the small étale site carries the internal Hom to the internal Hom of the restrictions.

That step is the source's "restriction is a localization (Section 04LX, formula 04M1) and
formation of internal hom commutes with localization (Modules on Sites, Lemma 0E8H)".  Nothing
of the quasi-coherence clause itself is proved here.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHom`: **the internal Hom sheaf of `𝒪_F`-modules**
  on the small étale ringed site of an algebraic space.
* `AlgebraicGeometry.Space.smallEtaleInternalHomOver`: the internal Hom of the restrictions of
  two `𝒪_F`-modules to a slice of the small étale site, as a sheaf of modules on that slice.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso`: **Stacks 0E8H on the small étale
  ringed site of an algebraic space.**  The restriction of the internal Hom to a slice is the
  internal Hom of the restrictions.
* `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso_hom_app`: on sections that isomorphism
  is restriction of a local morphism along the iterated-slice functor.  This pins it down
  rather than merely asserting that some isomorphism exists.

## Implementation notes

The underlying presheaf is `internalHom` of Stacks 04TT and the sheaf condition is
`internalHom_isSheaf`, Stacks 03EM; neither is restated.  Both leave the module universe free,
so `AlgebraicGeometry.Space.smallEtaleInternalHom` is defined for `𝒪_F`-modules in an arbitrary
module universe `m`.  Its own module universe is `max (u + 1) m`, not `m`: a section over an
étale chart `U` is a morphism of modules on the slice of the small étale site at `U`, and that
site has its objects in `Type (u + 1)`, so such a morphism is a priori only
`Type (u + 1)`-small.

`AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` is stated at a **free** module universe
`m`, like the internal Hom itself.  It used to be stated at the module universe `u` of the
schemes, because Stacks 0E8H in `StacksDraft.Ch18.Sec27.InternalHomRestriction` bound the
module universe of its two arguments to the universe of the coefficient rings of the ringed
site, which here is `u`.  That bound was an artifact of the binder of
`Stacks.SheafOfModules.InternalHom.internalHomOverIso` and of nothing else: the three
declarations that proof is assembled from — `sliceModulesEquiv`, `internalHomOverSection` and
`internalHomOverSectionEquiv` — were already stated at a free module universe, and relaxing
the binder of `internalHomOverIsoHom` and `internalHomOverIso` leaves both bodies unchanged
token for token.  The pin mattered because
`AlgebraicGeometry.Space.smallEtaleInternalHom` of two modules in module universe `m` lands in
`max (u + 1) m`, so the restriction of an internal Hom could never be compared with the
internal Hom of the restrictions at the universe at which the rest of clause (6) is proved.

Restriction `SheafOfModules.over` and Stacks 03EM's `restrFun` agree on underlying presheaves
of modules by `rfl`, so the isomorphism of sheaves of modules is the preimage of the
isomorphism of presheaves of modules under the fully faithful forgetful functor, with no
transport.  The four universe arguments of
`Stacks.SheafOfModules.InternalHom.internalHomOverIso` are written out at its use: the module
universe is not determined by the expected type, since only `max (u + 1) m` is visible there.

Two universe facts about the remaining work:

* the *second*-variable internal-Hom functor on sheaves of modules and its left exactness
  (`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_exact`, Stacks 0GMY(2)) *do*
  apply to the small étale ringed site, at the module universe `max (u + 1) m`, which is
  exactly the module universe of `AlgebraicGeometry.Space.smallEtaleInternalHom`;
* the *first*-variable half of Stacks 0GMY(1) at the sheaf level *does* apply to this site, as
  `Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomObjMapLeft_mono_of_epi` and
  `..._exact_of_exact_epi` of
  `StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariableLeftExact`, whose ring
  universe is free; it is stated over
  `Stacks.SheafOfModules.InternalHom.sheafInternalHomObj`, the internal Hom sheaf at the
  ring-sheaf spelling `AlgebraicGeometry.RingedSite.ringSheaf` reduces to.  The versions over
  `siteSheafInternalHom`
  (`Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_mono_of_epi` and
  `..._exact_of_exact_epi` of
  `StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`)
  are still restricted to a `RingedSite.{u, v, max u v}` and so do not apply here;
* what remains missing for the quasi-coherence clause is therefore not 0GMY(1) itself but the
  step that feeds it — internal Hom carrying a finite presentation of `G` to a kernel of a
  finite product of copies of `G'`.  The monoidal-closed bridge that would supply it,
  `Stacks.SheafOfModules.InternalHom.ihomIsoInternalHom`, is stated for a structure sheaf in
  `CommRingCat.{max u v}` of a site with objects in `Type u` and morphisms in `Type v`, so it
  does not accept the structure sheaf of the small étale ringed site, which is
  `CommRingCat.{u}` on a site with objects in `Type (u + 1)`.  The presheaf-level first-variable
  functor `Stacks.PresheafOfModules.InternalHom.internalHomFunctor` does exist, but only at the
  module universe `max u v`, which for this site is `u + 1`.

No `@[stacks 03M1]` attribute is carried: no part of the quasi-coherence clause is proved here.
No `@[stacks 0E8H]` attribute is carried either — that tag sits on the general statement in
`StacksDraft.Ch18.Sec27.InternalHomRestriction`, and the declarations below are its
instantiation at one ringed site, not a second proof of it.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 04M1](https://stacks.math.columbia.edu/tag/04M1)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The internal Hom sheaf `𝓗om_{𝒪_F}(G, G')` of two `𝒪_F`-modules on an algebraic space: the
internal Hom presheaf of Stacks 04TT on the small étale ringed site, which is a sheaf by
Stacks 03EM because `G'` is.

Its sections over an étale chart `U` are the morphisms `G|_U ⟶ G'|_U` of modules on the slice
of the small étale site at `U`, so its module universe is `max (u + 1) m` rather than `m`. -/
noncomputable def smallEtaleInternalHom (G G' : Modules.{u, m} B S hS F hF) :
    Modules.{u, max (u + 1) m} B S hS F hF where
  val := internalHom (smallEtaleRingedSite B S hS F hF).O.obj G.val G'.val
  isSheaf := internalHom_isSheaf
    (smallEtaleRingedSite B S hS F hF).O.obj G.val G'.val G'.isSheaf

/-- The internal Hom of the restrictions of two `𝒪_F`-modules to the slice of the small étale
site at an étale chart `U`, as a sheaf of modules on that slice over the restricted structure
sheaf `𝒪_F|_U`. -/
noncomputable def smallEtaleInternalHomOver (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over U) where
  val := internalHom ((smallEtaleRingedSite B S hS F hF).O.over U).obj
    (G.over U).val (G'.over U).val
  isSheaf := internalHom_isSheaf _ _ _ (G'.over U).isSheaf

/-- **Stacks 0E8H on the small étale ringed site of an algebraic space.**  The restriction of
the internal Hom of two `𝒪_F`-modules to the slice at an étale chart `U` is the internal Hom of
their restrictions:

`𝓗om_{𝒪_F}(G, G')|_U ≅ 𝓗om_{𝒪_F|_U}(G|_U, G'|_U)`.

This is the step of the source proof of Stacks 03M1(6) which says that restriction to an étale
chart is a localization (Stacks 04LX, formula 04M1) and that formation of internal Hom commutes
with localization (Stacks 0E8H). -/
noncomputable def smallEtaleInternalHomOverIso (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (smallEtaleInternalHom B S hS F hF G G').over U ≅
      smallEtaleInternalHomOver B S hS F hF G G' U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Stacks.SheafOfModules.InternalHom.internalHomOverIso.{u + 1, u, u, m}
      (smallEtaleRingedSite B S hS F hF) U G G')

/-- At a chart `V ⟶ U`, the isomorphism of
`AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` restricts a local morphism along the
iterated-slice functor of the small étale site.  This pins the isomorphism down. -/
theorem smallEtaleInternalHomOverIso_hom_app (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (V : (Over U)ᵒᵖ)
    (α : ((smallEtaleInternalHom B S hS F hF G G').over U).val.obj V)
    (W : (Over V.unop)ᵒᵖ)
    (x : ((restrFun ((smallEtaleRingedSite B S hS F hF).O.over U).obj V.unop).obj
      (G.over U).val).obj W) :
    ((((smallEtaleInternalHomOverIso B S hS F hF G G' U).hom.val.app V).hom α).app W).hom x =
      (α.app ((Over.iteratedSliceForward V.unop).op.obj W)).hom x :=
  rfl

end AlgebraicGeometry.Space

end
