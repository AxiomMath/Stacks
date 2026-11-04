module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ExtensionByZeroFormula
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of modules along the localization of a ringed topos at a sheaf

Let `X` be a ringed topos presented by a site `(C, J)`, let `F` be a sheaf of sets on `C` and
let `j : X_F ⟶ X` be the localization of `X` at `F` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/ToposLocalization.lean`, built on the
site of elements of `F`. This file identifies the two module functors of `j` that Stacks 04IE
parts (2) and (4) describe:

* the pullback `j^*` of sheaves of modules — "inverse image, then extend scalars along `j♯`" —
  is simply **restriction to the site of elements**, because `j♯` is an isomorphism;
* consequently the lower shriek `j_!` on modules, Mathlib's `SheafOfModules.pullback` along the
  structure map, is **left adjoint to `j^*`**.

## Main definitions

* `AlgebraicGeometry.RingedTopos.localizationModulePullbackIso`: pullback of sheaves of modules
  along the localization morphism is restriction to the site of elements.
* `AlgebraicGeometry.RingedTopos.extensionByZeroModules_adjunction`: the lower shriek on
  modules is left adjoint to that pullback.

## Implementation notes

Both are data and are produced as such: the comparison is assembled from the two isomorphisms it
is made of and the adjunction is transported along it, so a consumer that needs the comparison
itself — and not merely its existence — can use it.

The construction of the first has two halves, and both are results of the library used as they
stand. The inverse-image half is
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`: for a continuous functor of sites the
inverse image of a sheaf of modules along the induced restriction functor *is* its restriction,
the two differing only by the transport of the module structure, which is compared along
`Stacks.Sheaves.ToposPullback.restrictionRingIso`. The extension-of-scalars half is formal: the
structure map of a localization is an isomorphism of sheaves of rings, so restriction of scalars
along it is fully faithful and the counit of extension ⊣ restriction is an isomorphism, which
cancels the restriction of scalars left over from the first half. That is the argument of
`AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction_exists` for the slice site, and
it is reproduced here for the site of elements; `restrictScalarsFullyFaithful` is imported from
there rather than repeated.

What has to be supplied for the site of elements is the identification of the structure map with
the restriction comparison at the level of sheaves of *rings*,
`ringFsharpInverseImage_localizationMorphism`. It is the library's
`AlgebraicGeometry.RingedTopos.localization_fSharp_inverseImage`, which gives it for sheaves of
commutative rings, carried along `forget₂ CommRingCat RingCat`; the two restriction comparisons
agree on the nose by
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_restrictionCommRingIso_hom`, so no
comparison isomorphism intervenes and `congrArg` suffices.

Pullback of sheaves of modules is stated over the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which stores both forms of the structure map
at the level of sheaves of rings; the localization morphism is the two-field
`AlgebraicGeometry.RingedToposHom` of Stacks 01D3 part (2), and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` is the passage between them.

Sheafification of presheaves of abelian groups on the site of elements is not an instance in
Mathlib for a site of this shape, and `pullbackModules` needs it; the two instances below derive
it from `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` and
`.site_wEqualsLocallyBijective_addCommGrp`, which hold for any site in the universe of its
objects and morphisms. They are instances rather than hypotheses of the statements, so neither
statement below carries an assumption the source does not make.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- Presheaves of abelian groups on the site of elements of `F` admit sheafification: the site
lives in the universe of its own objects and morphisms, so
`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` applies. -/
noncomputable instance elementTopologyHasSheafify :
    HasSheafify (elementTopology X F) AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
    (J := elementTopology X F)

/-- Sheafification on the site of elements of `F` inverts exactly the locally bijective maps of
presheaves of abelian groups. -/
noncomputable instance elementTopologyWEqualsLocallyBijective :
    (elementTopology X F).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
    (J := elementTopology X F)

/-- Restriction of presheaves of modules to the site of elements has a left adjoint. This is
Mathlib's existence instance, restated at the spelling `elementModuleRingPresheafHom` so that
instance search can find it. -/
noncomputable instance elementPresheafModulePushforwardIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (elementModuleRingPresheafHom X F)).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- Restriction of sheaves of modules to the site of elements has a left adjoint, namely the
lower shriek `SheafOfModules.pullback` of Stacks 04IE part (4). -/
noncomputable instance elementSheafModulePushforwardIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (elementModuleRingHom X F)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction (elementModuleRingHom X F)).isRightAdjoint

/-- The structure map of the localization, in inverse-image form and at the level of sheaves of
rings, is the comparison of the inverse image of the ring sheaf of `X` with its restriction to
the site of elements. -/
theorem ringFsharpInverseImage_localizationMorphism :
    (localizationMorphism X F).ringFsharpInverseImage =
      (restrictionRingIso (elementTopology X F) X.J (elementProjection X F)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom :=
  congrArg ((sheafCompose (elementTopology X F)
    (forget₂ CommRingCat.{u} RingCat.{u})).map) (localization_fSharp_inverseImage X F)

/-- **Stacks 04IE, part (2): the inverse image on modules.** Pullback of sheaves of modules
along the localization morphism — the inverse image of Stacks 03D2 followed by extension of
scalars along the structure map — is restriction to the site of elements of `F`. -/
@[stacks 04IE "part (2): inverse image on modules"]
noncomputable def localizationModulePullbackIso :
    (localizationMorphism X F).toRingedToposModulesHom.pullbackModules ≅
      SheafOfModules.pushforward (F := elementProjection X F)
        (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F) :=
  let f := (localizationMorphism X F).toRingedToposModulesHom
  let k := (restrictionRingIso (elementTopology X F) X.J (elementProjection X F)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom
  let Q := restrictionModules (elementTopology X F) X.J (elementProjection X F)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let E := extendScalarsFSharp (X := localizedRingedTopos X F) (Y := X) f
  let R := SheafOfModules.restrictScalars.{u} k
  let ff := AlgebraicGeometry.RingedSite.restrictScalarsFullyFaithful k
  have hk : (SheafOfModules.restrictScalars.{u}
      (commRingSheafMap (elementTopology X F) (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (localizedRingedTopos X F).O).property)) = R :=
    congrArg SheafOfModules.restrictScalars
      ((commRingSheafMap_fSharpCommRing f).trans
        (ringFsharpInverseImage_localizationMorphism X F))
  let adj : E ⊣ R :=
    Adjunction.ofNatIsoRight
      (extendRestrictScalarsAdjunction (elementTopology X F) (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (localizedRingedTopos X F).O).property)
      (eqToIso hk)
  have hc : IsIso adj.counit :=
    @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ E R adj ff.full ff.faithful
  let counitIso : R ⋙ E ≅ 𝟭 _ := @asIso _ _ _ _ adj.counit hc
  Functor.isoWhiskerRight
      (restrictionModuleIso (elementTopology X F) X.J (elementProjection X F)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) E ≪≫
    Functor.associator Q R E ≪≫
    Functor.isoWhiskerLeft Q counitIso ≪≫ Functor.rightUnitor Q

/-- **Stacks 04IE, parts (2) and (4): the module adjunction.** On sheaves of modules the lower
shriek of the localization is left adjoint to pullback along the localization morphism. -/
@[stacks 04IE "part (2) and part (4): module adjunction"]
noncomputable def extensionByZeroModules_adjunction :
    SheafOfModules.pullback.{u}
      (F := elementProjection X F) (J := elementTopology X F) (K := X.J)
      (elementModuleRingHom X F) ⊣
      (localizationMorphism X F).toRingedToposModulesHom.pullbackModules :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (elementModuleRingHom X F)).ofNatIsoRight (localizationModulePullbackIso X F).symm

end AlgebraicGeometry.RingedTopos

add_to_stacks 04IE "part (2): restriction of modules" SheafOfModules.pushforward
add_to_sga "4 IV 11.2.2" "more general" SheafOfModules.pushforward
add_to_sga "4 IV 13.2.1" "special case" SheafOfModules.pushforward
add_to_sga "4 Vbis 1.3.6" "special case" SheafOfModules.pushforward
add_to_ega "0 4.2.1" "more general" SheafOfModules.pushforward
add_to_ega "0 5.3.12" SheafOfModules.pushforward
add_to_ega "II 1.1.1" "more general" SheafOfModules.pushforward
add_to_ega "II 1.1.2" "partial" SheafOfModules.pushforward
add_to_ega "IV 21.13.3" SheafOfModules.pushforward
add_to_stacks 04IE "part (4): lower shriek on modules" SheafOfModules.pullback
add_to_stacks 04IE "part (4): sheafification" SheafOfModules.pullbackIso

end
