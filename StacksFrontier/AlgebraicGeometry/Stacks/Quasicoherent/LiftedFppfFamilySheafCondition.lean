module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationPullbackSheafCondition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PullbackCompatibleTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore

/-!
# The sheaf condition along a family lying over an fppf covering (Stacks 076T, the last step)

This file assembles the step of the proof of **Stacks 076T** that
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean` carries as
the hypothesis `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`: for a presheaf of modules
`F` which is locally quasi-coherent (**Stacks 06WJ**) and whose comparison map `c_φ` of
**Stacks 06WC** is an isomorphism along every arrow lying over a flat morphism locally of finite
presentation, the sheaf condition holds along every family of arrows of `𝒳` which generates a
covering sieve of the inherited fppf topology and lies over an fppf covering of schemes.

The source's proof is one sentence: the sheaf condition for `F` and `{x_i → x}` *is* the sheaf
condition for `𝒢^a` on `(Sch/U)_{fppf}` and `{U_i → U}`, which is Descent, **Stacks 03DT**. What
is assembled here is the word "is": a map, at each object the reduced sheaf condition mentions,
from the sections of `F` upstairs to the sections of `𝒢^a` downstairs, and the transport of the
sheaf condition along it.

## The identification, factor by factor

Let `x` be an object of `𝒳` lying over a scheme `U` and let `𝓕` be the quasi-coherent
`𝒪_U`-module with `𝓕^a ≅ F|_{U_ét}` produced by
`AlgebraicGeometry.Stack.exists_associatedModule_iso_restrictModuleToSmallEtale`. For an arrow
`φ : z ⟶ x` lying over a morphism `g : W ⟶ U` which is flat and locally of finite presentation,
`AlgebraicGeometry.Stack.liftedSectionsIso` identifies `F(z)` with the sections `Γ(W, g^*𝓕)` of
the presheaf of **Stacks 03DS** of `𝓕` over `g`, which are the sections of `𝒢^a` over `W / U`.
It is the composite of five identifications, each of them already available:

1. `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso`: `F(z) = Γ(W_ét, F|_{W_ét})`,
   the small étale site of `W` having `W / W` as its final object;
2. the comparison map `c_φ` of **Stacks 06WC**
   (`AlgebraicGeometry.Stack.restrictModulePullbackComparison`), an isomorphism by hypothesis
   (b) because `g` is flat and locally of finite presentation, together with the identification
   `𝓕^a ≅ F|_{U_ét}` of hypothesis (a): these present `F|_{W_ét}` as the Stacks 06WC pullback of
   `𝓕^a` along `φ`;
3. `AlgebraicGeometry.SmallEtale.isIso_sheafificationAdjunction_unit_app`: `F|_{W_ét}` is a sheaf
   on the small étale site of `W`, so the sheafification unit at it is invertible and the
   pullback of 2 may be sheafified without loss;
4. `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`: the sheafified
   Stacks 06WC pullback of `𝓕^a` is `(g^*𝓕)^a`;
5. `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` and
   `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`: the sections of `(g^*𝓕)^a` over the final
   object of the small étale site of `W` are `Γ(W, g^*𝓕)`, and those are the sections of the
   presheaf of Stacks 03DS of `𝓕` over `g`.

Factors 1, 3 and 5 carry no hypothesis; factor 2 is exactly hypotheses (a) and (b) of
Stacks 076T, used at an arrow lying over a flat morphism locally of finite presentation and
nowhere else.

## What the assembly still carries, and what it does not

The identification above is a map at one object. To transport the sheaf condition it must
commute with the restriction maps between the objects the reduced sheaf condition mentions, and
that is the one thing not assembled here: it is carried as the explicitly-named hypothesis
`AlgebraicGeometry.Stack.LiftedSectionsCocycle`, the statement that
`AlgebraicGeometry.Stack.liftedSectionsIso` is compatible with composition of arrows of `𝒳`.
Factor 1 of that compatibility is
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison`, factor 2 is
**Stacks 075D (1)** (`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_comp`) and
factor 5 is `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality` and
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module` — naturality in
the arrow of the site and naturality in the module — together with the naturality of
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`.

The compatibility of factor 4 with composition *is* stated, twice and unconditionally, at the
level of sheaves of modules on the small étale site:
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp` for factor 4 alone and
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp` for factors 2, 3 and 4 together.  Reading
those laws on *sections at one object* is a separate matter, the Stacks 06WC pullback of
presheaves of modules being a left adjoint with no formula for its sections;
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor` does it for factors 3
and 4.  What nothing states is a compatibility on sections between the base-change identification
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` of **Stacks 03LC (1)** and
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` of **Stacks 03DS**.  That is the gap
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleAssembly.lean` carries
as `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn`.

What the assembly does *not* carry, and this is the point of the file, is any identification of
the two presheaves over the whole slice `𝒳/x`. Such an identification would ask the comparison
map `c_φ` to be an isomorphism along every arrow of the slice, which is clause (b) of
**Stacks 06WK** and is strictly stronger than hypothesis (b) of Stacks 076T. The reduced sheaf
condition of
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPostTransport` mentions
only the objects `U_i / U` and `(U_i ×_U U_j) / U`, all of which lie over a flat morphism
locally of finite presentation by `AlgebraicGeometry.Stack.flat_hom_pullback_overPost` and
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost`, and
`CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps` transports the sheaf condition
along maps given at those objects alone.

## Main definitions

* `AlgebraicGeometry.Stack.liftedSmallEtaleIso`: the restriction `F|_{W_ét}` is `(g^*𝓕)^a`.
* `AlgebraicGeometry.Stack.liftedSectionsIso`: **the identification of `F(z)` with the sections
  of the presheaf of Stacks 03DS of `𝓕` over `g`.**
* `AlgebraicGeometry.Stack.overPostSectionsIso`: the same at an object of the big fppf site of
  `U`, read through the localization equivalence of **Stacks 06W0**.
* `AlgebraicGeometry.Stack.overPostSectionsMap`: the same, read as a map between the two
  presheaves of sets the reduced sheaf condition is about —
  `AlgebraicGeometry.Stack.overPostTransportSections` and
  `AlgebraicGeometry.Stack.overPostSectionsTypes` — which is the shape
  `CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps` consumes.
* `AlgebraicGeometry.Stack.LiftedSectionsCocycle`: the compatibility of
  `AlgebraicGeometry.Stack.liftedSectionsIso` with composition — the one hypothesis carried.

## Main results

* `AlgebraicGeometry.Stack.flat_overPostLift`,
  `AlgebraicGeometry.Stack.locallyOfFinitePresentation_overPostLift`: an object of the big fppf
  site of `U` lying over a flat morphism locally of finite presentation is the image of an arrow
  of `𝒳` of the same kind, so hypothesis (b) applies to it.
* `AlgebraicGeometry.Stack.overPostSectionsIso_naturality` and
  `AlgebraicGeometry.Stack.overPostSectionsMap_naturality`: **over the carried cocycle, the
  identification commutes with the restriction maps of the big fppf site of `U`** — the input
  `CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps` asks for at the arrows of a
  covering family and at the projections of its fibre products.
* `AlgebraicGeometry.Stack.overPostSectionsMap_bijective`: the identification is a bijection, so
  it also supplies the bijection over the object the family covers.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The objects of the big fppf site of `U` as images of arrows of `𝒳` -/

/-- The object of `𝒳` which the localization equivalence of **Stacks 06W0** produces over an
object of the big fppf site of the scheme `U` below `x`. -/
noncomputable abbrev overPostLiftObj (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x)) : 𝒳 :=
  ((overPostEquivalence B S hS p hp x).inverse.obj V).left

/-- The arrow of `𝒳` to `x` which the localization equivalence of **Stacks 06W0** produces over
an object of the big fppf site of the scheme `U` below `x`. -/
noncomputable abbrev overPostLiftHom (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x)) :
    overPostLiftObj B S hS p hp x V ⟶ x :=
  ((overPostEquivalence B S hS p hp x).inverse.obj V).hom

/-- **The counit of the localization equivalence of Stacks 06W0**, at the spelling of its source
which the identification of the sections lands in: the image of the arrow of `𝒳` produced over
an object of the big fppf site of `U` is that object.

The declared type pins the source to `Over.mk` of the image of
`AlgebraicGeometry.Stack.overPostLiftHom`, which is the object the restriction maps of
`AlgebraicGeometry.Stack.overPostSectionsPresheaf` are compared at; the counit's own spelling of
it, through the composite of the two functors of the equivalence, is the same object but not the
same expression. -/
noncomputable def overPostLiftIso (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x)) :
    Over.mk ((p ⋙ Over.forget (B.obj hS)).map (overPostLiftHom B S hS p hp x V)) ≅ V :=
  (overPostEquivalence B S hS p hp x).counitIso.app V

/-- **The counit of Stacks 06W0 is natural**, in the spelling of
`AlgebraicGeometry.Stack.overPostLiftIso`: an arrow of the big fppf site of `U` whose image
under the two functors of the equivalence it is, is carried across. The arrow upstairs is given
by its left component, which is all the consumer knows about it. -/
theorem overPostLiftIso_naturality (x : 𝒳)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (m : Over.mk ((p ⋙ Over.forget (B.obj hS)).map (overPostLiftHom B S hS p hp x V')) ⟶
      Over.mk ((p ⋙ Over.forget (B.obj hS)).map (overPostLiftHom B S hS p hp x V)))
    (hm : m.left = (p ⋙ Over.forget (B.obj hS)).map
      (((overPostEquivalence B S hS p hp x).inverse.map r).left)) :
    m ≫ (overPostLiftIso B S hS p hp x V).hom =
      (overPostLiftIso B S hS p hp x V').hom ≫ r := by
  rw [show m = ((overPostEquivalence B S hS p hp x).inverse ⋙
    (overPostEquivalence B S hS p hp x).functor).map r from Over.OverMorphism.ext hm]
  exact (overPostEquivalence B S hS p hp x).counitIso.hom.naturality r

/-- **The arrow of `𝒳` over an object of the big fppf site of `U` lies over a morphism in the
same class of morphisms of schemes.** The counit of the localization equivalence of
**Stacks 06W0** identifies the image of that arrow with the object, so the two structure
morphisms to `U` differ by an isomorphism. -/
theorem prop_overPostLift (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hV : P (B.inclusion.map V.hom)) :
    P (B.inclusion.map (p.map (overPostLiftHom B S hS p hp x V)).left) := by
  have hw : ((overPostEquivalence B S hS p hp x).counitIso.app V).hom.left ≫ V.hom =
      (p.map (overPostLiftHom B S hS p hp x V)).left :=
    Over.w _
  have hiso : IsIso (((overPostEquivalence B S hS p hp x).counitIso.app V).hom.left) :=
    ((Over.forget _).mapIso ((overPostEquivalence B S hS p hp x).counitIso.app V)).isIso_hom
  have key : P (B.inclusion.map (((overPostEquivalence B S hS p hp x).counitIso.app V).hom.left) ≫
      B.inclusion.map V.hom) := by
    rw [P.cancel_left_of_respectsIso]
    exact hV
  rwa [← B.inclusion.map_comp, hw] at key

/-- **The arrow of `𝒳` over an object of the big fppf site of `U` lies over a flat
morphism** as soon as the object does. -/
theorem flat_overPostLift (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hV : Flat (B.inclusion.map V.hom)) :
    Flat (B.inclusion.map (p.map (overPostLiftHom B S hS p hp x V)).left) :=
  prop_overPostLift B S hS p hp _ x V hV

/-- **The arrow of `𝒳` over an object of the big fppf site of `U` lies over a morphism locally
of finite presentation** as soon as the object does. -/
theorem locallyOfFinitePresentation_overPostLift (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    LocallyOfFinitePresentation (B.inclusion.map (p.map (overPostLiftHom B S hS p hp x V)).left) :=
  prop_overPostLift B S hS p hp _ x V hV

/-- The presheaf `𝒢^a` of the proof of **Stacks 076T** on the big fppf site of the scheme `U`
below `x`: the pullback-sections presheaf of **Stacks 03DS** of a quasi-coherent `𝒪_U`-module,
read on `Over U` as the localization equivalence of **Stacks 06W0** presents that site.

Only the spelling of the site differs from
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`; naming it keeps every isomorphism of
this file in one category, so that the arrows produced by the localization equivalence and the
restriction maps of `𝒢^a` are comparable without transport. -/
noncomputable def overPostSectionsPresheaf (x : 𝒳) (𝓕 : (p.obj x).left.1.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent) :
    (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (@BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕).presheaf

/-! ### The identification of the sections -/

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- **The restriction `F|_{W_ét}` is the associated module of `g^*𝓕`.** For an arrow
`φ : z ⟶ x` of `𝒳` lying over a morphism of schemes `g : W ⟶ U` along which the comparison map
`c_φ` of **Stacks 06WC** is an isomorphism, and for a quasi-coherent `𝒪_U`-module `𝓕` with
`𝓕^a ≅ F|_{U_ét}`, the restriction of `F` to the small étale site of `W` is `(g^*𝓕)^a`.

The comparison map presents `F|_{W_ét}` as the Stacks 06WC pullback of `𝓕^a`; local
quasi-coherence makes `F|_{W_ét}` a sheaf, so the sheafification unit at that pullback is
invertible; and `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` identifies
the sheafified pullback with `(g^*𝓕)^a`. -/
noncomputable def liftedSmallEtaleIso {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (_h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf ≅
      ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val.presheaf := by
  have hunit : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj)).unit.app
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F)) :=
    SmallEtale.isIso_sheafificationAdjunction_unit_app E (p.obj z).left.1
      (contains_base B E h S hS p z) _ (hlqc.2 z).choose
  have ζ : (PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).obj
        ((SmallEtale.associatedModule E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj 𝓕).val ≅
      restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F :=
    (PresheafOfModules.pullback.{u} _).mapIso ((SheafOfModules.forget _).mapIso eU) ≪≫
      @asIso _ _ _ _ _ hiso
  exact (PresheafOfModules.toPresheaf _).mapIso
    (@asIso _ _ _ _ _ hunit ≪≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
        (((PresheafOfModules.sheafification (𝟙 _)).mapIso ζ).symm ≪≫
          associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) φ 𝓕))

/-- **The identification of the sections of `F` at `z` with the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`.** For an arrow `φ : z ⟶ x` lying over `g : W ⟶ U` along which the
comparison map of **Stacks 06WC** is an isomorphism, `F(z) = Γ(W, g^*𝓕)`.

`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso` reads `F(z)` as the sections of
`F|_{W_ét}` over the final object of the small étale site of `W`,
`AlgebraicGeometry.Stack.liftedSmallEtaleIso` identifies that restriction with `(g^*𝓕)^a`,
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` reads the latter's sections as the
sections of the presheaf of Stacks 03DS of `g^*𝓕`, and
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` reads those as the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`. -/
noncomputable def liftedSectionsIso {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    F.presheaf.obj (op z) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj
        (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) := by
  letI := h𝓕
  refine (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).symm ≪≫
    (liftedSmallEtaleIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).app
      (op (smallEtaleFinal B E h S hS p z)) ≪≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).app
      (op (smallEtaleFinal B E h S hS p z)) ≪≫
    ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
        (Over.mk (B.inclusion.map (p.map φ).left))).app
      (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z)))).symm ≪≫
    (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).mapIso
      (Iso.op (Over.isoMk (Iso.refl _) ?_))
  simp [smallEtaleFinal, SmallEtale.final, Over.post]

/-- **The identification of the sections, at an object of the big fppf site of `U`.**
`AlgebraicGeometry.Stack.liftedSectionsIso` at the arrow of `𝒳` which the localization
equivalence of **Stacks 06W0** produces over the object, followed by the restriction map along
the counit of that equivalence. -/
noncomputable def overPostSectionsIso (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    F.presheaf.obj (op (overPostLiftObj B S hS p hp x V)) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj (op V) :=
  liftedSectionsIso B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V) 𝓕 h𝓕 hMx eU hiso ≪≫
    (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).mapIso
      (Iso.op (overPostLiftIso B S hS p hp x V).symm)

/-! ### The compatibility with composition which is carried -/

/-- **The one hypothesis carried: `AlgebraicGeometry.Stack.liftedSectionsIso` is compatible with
composition of arrows of `𝒳`.**

This is a *stand-in*, not a result. It is the cocycle condition for the composite identification
of `AlgebraicGeometry.Stack.liftedSectionsIso`, stated in the only form the assembly of this
file consumes: at a composable pair of arrows both of which lie over a morphism of schemes along
which the comparison map of **Stacks 06WC** is an isomorphism. Four of its five factors are
available — see the discussion at the head of this file — and the fifth, the compatibility of
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` with composition of arrows,
is what nothing in this development states. No Stacks tag may be registered on anything which
carries it. -/
def LiftedSectionsCocycle : Prop :=
  ∀ (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (hφ' : φ' = ψ ≫ φ)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp φ' (etaleTopology B)
      (etaleTopology_le_topology B) F)),
    F.presheaf.map ψ.op ≫
        (liftedSectionsIso B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map ψ)
            (by simp [hφ']) :
            Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ') ⟶
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)).op

/-- **Over the carried cocycle, the identification commutes with the restriction maps of the big
fppf site of `U`.** For an arrow `r : V' ⟶ V` of the big fppf site of the scheme below `x`,
restricting along `r` after identifying is identifying after restricting along the arrow of `𝒳`
which the localization equivalence of **Stacks 06W0** produces over `r`.

The cocycle supplies the square for `AlgebraicGeometry.Stack.liftedSectionsIso`; what is added
here is the bookkeeping of the counit of the localization equivalence, which is its naturality
pushed forward along the inclusion of the big fppf site into the schemes over `U`. -/
theorem overPostSectionsIso_naturality (hcoc : LiftedSectionsCocycle B E h S hS p hp) (x : 𝒳)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V') (etaleTopology B) (etaleTopology_le_topology B) F)) :
    F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op ≫
        (overPostSectionsIso B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
      (overPostSectionsIso B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op := by
  have hφ' : overPostLiftHom B S hS p hp x V' =
      ((overPostEquivalence B S hS p hp x).inverse.map r).left ≫
        overPostLiftHom B S hS p hp x V :=
    (Over.w ((overPostEquivalence B S hS p hp x).inverse.map r)).symm
  have hcell := hcoc F hlqc 𝓕 h𝓕 hMx eU
    (((overPostEquivalence B S hS p hp x).inverse.map r).left)
    (overPostLiftHom B S hS p hp x V) (overPostLiftHom B S hS p hp x V') hφ' hiso hiso'
  have htail : ∀ (m : Over.mk ((p ⋙ Over.forget (B.obj hS)).map
        (overPostLiftHom B S hS p hp x V')) ⟶
      Over.mk ((p ⋙ Over.forget (B.obj hS)).map (overPostLiftHom B S hS p hp x V))),
      m.left = (p ⋙ Over.forget (B.obj hS)).map
          (((overPostEquivalence B S hS p hp x).inverse.map r).left) →
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map m.op ≫
          (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
            (Iso.op (overPostLiftIso B S hS p hp x V').symm).hom =
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
            (Iso.op (overPostLiftIso B S hS p hp x V).symm).hom ≫
          (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op := by
    intro m hm
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map (Quiver.Hom.unop_inj ?_)
    simp only [unop_comp, Iso.op, Iso.symm_hom, Quiver.Hom.unop_op]
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact overPostLiftIso_naturality B S hS p hp x r m hm
  simp only [overPostSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcell, Category.assoc, htail _ rfl, Category.assoc]


/-! ### The step of Stacks 076T -/

/-- The presheaf of sets the reduced sheaf condition for `F` is about: the transport across the
localization equivalence of **Stacks 06W0** of `F` followed by `Hom(M, -)`.

Naming the two presheaves of the reduced condition keeps every comparison this section makes
between terms whose heads agree, which is what lets the specialization of
`CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps` elaborate. -/
noncomputable def overPostTransportSections (x : 𝒳) (M : AddCommGrpCat.{u}) :
    (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ Type u :=
  overPostTransport B S hS p hp x (F.presheaf ⋙ coyoneda.obj (op M))

/-- The presheaf of sets the sheaf condition for `𝒢^a` of **Stacks 03DT** is about: `𝒢^a`
followed by `Hom(M, -)`. -/
noncomputable def overPostSectionsTypes (x : 𝒳) (𝓕 : (p.obj x).left.1.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent) (M : AddCommGrpCat.{u}) :
    (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ Type u :=
  overPostSectionsPresheaf B S hS p x 𝓕 h𝓕 ⋙ coyoneda.obj (op M)

/-- The identification of `AlgebraicGeometry.Stack.overPostSectionsIso` read as a map between
the sections of the two presheaves the reduced sheaf condition is about. -/
noncomputable def overPostSectionsMap
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).obj (op V) :=
  fun s => ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIso B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).hom s

/-- **`AlgebraicGeometry.Stack.overPostSectionsMap` is a bijection**, the identification it comes
from being an isomorphism. -/
theorem overPostSectionsMap_bijective
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (overPostSectionsMap B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso M) :=
  ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIso B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).toEquiv.bijective

include hlqc in
/-- **Over the carried cocycle, `AlgebraicGeometry.Stack.overPostSectionsMap` commutes with the
restriction maps of the big fppf site of `U`.**
`AlgebraicGeometry.Stack.overPostSectionsIso_naturality` on a section. -/
theorem overPostSectionsMap_naturality (hcoc : LiftedSectionsCocycle B E h S hS p hp)
    (x : 𝒳) {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V') (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    overPostSectionsMap B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso' M
        ((overPostTransportSections B S hS p hp F x M).map r.op s) =
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).map r.op
        (overPostSectionsMap B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso M s) := by
  have key := overPostSectionsIso_naturality B E h S hS p hp F hlqc hcoc x r 𝓕 h𝓕 hMx eU hiso hiso'
  change (s ≫ F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op) ≫
      (overPostSectionsIso B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
    (s ≫ (overPostSectionsIso B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom) ≫
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => s ≫ t) key).trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Stack

end
