module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalSheafComparison

/-!
# The conormal module of a representable algebraic space, as the scheme-level conormal sheaf

Let `B` be a big fppf site containing a scheme `S`.  Two conormal objects are attached to a closed
subspace `Z ⊆ yoneda.obj T` of a representable algebraic space:

* `AlgebraicGeometry.Space.conormalModule` of Stacks 04CN, an `𝒪`-module on the **small étale
  site** of `yoneda.obj T`;
* `Stacks.Thickenings.schemeConormalSheaf` of the representing closed immersion of schemes, and —
  when that immersion presents a universal first-order thickening —
  `Stacks.Thickenings.universalConormalSheaf` of Stacks 04F4 of the morphism of schemes thickened,
  both of them modules on the **Zariski site** of the representing scheme.

This file identifies the first with the transport of the second **as objects**.  That is item 2 of
the list of carried hypotheses in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/ConormalShortExact.lean` under
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`, and it
is what the section *What this leaves owed* of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedUniversalThickeningConormal.lean` records as the
assembly not done there.

## Main definitions

* `Stacks.Thickenings.schemeConormalSheafIsoPushforwardUniversalConormalSheaf`: for a universal
  first-order thickening `t` of a formally unramified morphism `h` of schemes whose inclusion
  factors as an isomorphism `e : Z ≅ R` followed by `j : R ⟶ t.ambient`, the conormal sheaf of `j`
  is the direct image along `e` of the conormal sheaf `𝒞_{Z/X}` of Stacks 04F4.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeConormalSheafIso`: the scheme-level
  comparison of the Zariski pullback of the defining ideal sheaf with
  `Stacks.Thickenings.schemeConormalSheaf`, read in the category of quasi-coherent modules.
* `AlgebraicGeometry.Space.conormalModuleIsoRepresentedSchemeConormalSheaf`: **the conormal module
  of a closed subspace of a representable algebraic space is the `𝒪`-module that
  `Stacks.Thickenings.schemeConormalSheaf` of the representing closed immersion of schemes
  becomes**, with nothing assumed.
* `AlgebraicGeometry.Space.conormalModuleIsoRepresentedUniversalConormalSheaf`: **the
  identification with `Stacks.Thickenings.universalConormalSheaf`**, for a closed immersion of the
  site presenting a scheme-level universal first-order thickening.
* `AlgebraicGeometry.Space.nonempty_conormalSheafIsoRepresentedUniversalConormalSheaf`: the same
  read at the space-level conormal sheaf `𝒞_{V/U}` of Stacks 0607 of a universal first-order
  thickening of a morphism of representable algebraic spaces — the form in which the
  identification is consumed.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_schemeConormalSheaf_representingHom` and
  `AlgebraicGeometry.Space.isQuasicoherent_pushforward_universalConormalSheaf`: the
  quasi-coherence the transport of each object asks for.

## How the identification is assembled

The property-level chain exists in the library but is **not** reused here: what
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_representable` composes is a
sequence of *transports of finite local freeness*, and an object isomorphism does not come out of
it.  What is composed here are the isomorphisms those transports were read off, in the same order:

1. `AlgebraicGeometry.Space.conormalModuleIsoRepresentedQuasicoherent` of
   `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedDefiningIdealSheafObject.lean` presents the
   conormal module, pulled back along `AlgebraicGeometry.Space.representedSubspaceIso`, as the
   transport of the Zariski pullback of
   `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the representing closed
   immersion.
2. `Stacks.Thickenings.schemeConormalSheafIsoPullbackDefiningIdealOfHom` turns that Zariski
   pullback into `Stacks.Thickenings.schemeConormalSheaf` of the same immersion.  The transport
   `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` is an equivalence of the
   *quasi-coherent* modules, so the isomorphism has to be read inside that full subcategory
   first; `CategoryTheory.Functor.preimageIso` of `CategoryTheory.ObjectProperty.ι` does that, the
   inclusion of a full subcategory being fully faithful, and the quasi-coherence of the target is
   carried across the isomorphism by `CategoryTheory.ObjectProperty.prop_of_iso`.
3. `Stacks.Thickenings.universalConormalSheafIsoThickening` and
   `Stacks.Thickenings.pushforwardSchemeConormalSheafIso` of
   `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedConormalSheafComparison.lean` identify
   `Stacks.Thickenings.schemeConormalSheaf` of the representing immersion with the direct image,
   along the isomorphism `AlgebraicGeometry.Space.representingObjIso` of the two sources, of
   `Stacks.Thickenings.universalConormalSheaf` of the morphism of schemes.

The direct image in the conclusion is not avoidable: the source of the closed immersion of the
site and `AlgebraicGeometry.Space.representingObj` of the closed subspace its Yoneda image cuts
out are two isomorphic objects and not one, so the two conormal objects live on two isomorphic
schemes.

## Implementation notes

**Why step 3 is stated at variable schemes.**  `Stacks.Thickenings.schemeConormalSheaf` of a
concrete representing immersion is an inverse image of a kernel of a structure map of a morphism
of the site, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedConormalSheafComparison.lean` record what
deciding one spelling of such an object against another costs.  Stated at variable schemes with
the factorisation `e.hom ≫ j = t.inclusion` as a hypothesis, step 3 is instantiated by
unification and the factorisation is discharged by `subst` inside the existing bridges.

**Why the three spellings of the representing morphism of schemes may be used
interchangeably.**  `AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) a`,
`B.inclusion.map a` and `(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map` of the morphism of
the site are equal by `rfl`, the first being an `abbrev` for the second.  The statements below
spell the representing morphism the way
`AlgebraicGeometry.Space.conormalModuleIsoRepresentedQuasicoherent` spells it, so that the
composition in step 2 has nothing to unify, and the proofs pass the `toScheme` spelling where the
bridges produce it.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-! ### The conormal sheaf of a thickening across an isomorphism of the source -/

variable {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h]

/-- **The conormal sheaf of a factored thickening inclusion is the direct image of the conormal
sheaf of Stacks 04F4.**  Let `h : Z ⟶ X` be a formally unramified morphism of schemes, `t` a
universal first-order thickening of `h`, and let the inclusion of `t` factor as an isomorphism
`e : Z ≅ R` followed by `j : R ⟶ t.ambient`.  Then `Stacks.Thickenings.schemeConormalSheaf` of `j`
is the direct image along `e` of `Stacks.Thickenings.universalConormalSheaf` of `h`.

This is `Stacks.Thickenings.universalConormalSheafIsoThickening`, which replaces the thickening
`Stacks.Thickenings.universalFirstOrderThickening` chooses by `t`, followed by
`Stacks.Thickenings.pushforwardSchemeConormalSheafIso`, which crosses the isomorphism of the
source; it is the object-level form of the transport
`Stacks.Thickenings.isFiniteLocallyFree_pullback_definingIdealOfHom`. -/
noncomputable def schemeConormalSheafIsoPushforwardUniversalConormalSheaf
    (t : UniversalFirstOrderThickening h) {R : Scheme.{u}} (e : Z ≅ R) (j : R ⟶ t.ambient)
    (hfac : e.hom ≫ j = t.inclusion) :
    schemeConormalSheaf j ≅
      (RingedSpaceModuleAdjunction.modulePushforward
        (RingedSpace.ringedSpaceIso e).hom).obj (universalConormalSheaf h) :=
  (pushforwardSchemeConormalSheafIso e j t.inclusion hfac).symm ≪≫
    (RingedSpaceModuleAdjunction.modulePushforward
      (RingedSpace.ringedSpaceIso e).hom).mapIso (universalConormalSheafIsoThickening h t).symm

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The scheme-level conormal sheaf of the representing closed immersion -/

variable (T : BigFppfOver B S hS) (Z : ClosedSubspaces B S hS (yoneda.obj T))

/-- **The conormal sheaf of the representing closed immersion of schemes is quasi-coherent.**  It
is isomorphic to the Zariski pullback of the defining ideal sheaf of that immersion, which is
quasi-coherent by `AlgebraicGeometry.Space.representedQuasicoherentSchemePullback`. -/
theorem isQuasicoherent_schemeConormalSheaf_representingHom :
    SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (representingObj B S hS T Z)).ringCatSheaf
      (Stacks.Thickenings.schemeConormalSheaf
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (representingHom B S hS T Z).left)) :=
  have := isClosedImmersion_schemeHom_representingHom B S hS T Z
  (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (representingObj B S hS T Z)).ringCatSheaf).prop_of_iso
    (Stacks.Thickenings.schemeConormalSheafIsoPullbackDefiningIdealOfHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z).left))
    (representedQuasicoherentSchemePullback B S hS (representingHom B S hS T Z)
      ⟨(Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z).left)).toSheafOfModules,
        isQuasicoherent_definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z).left)⟩).property

/-- `Stacks.Thickenings.schemeConormalSheafIsoPullbackDefiningIdealOfHom` at the representing
closed immersion, read in the category of **quasi-coherent** modules on the representing scheme:
that is where `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` can carry it to
the small étale site of the algebraic space.

The inclusion of a full subcategory is fully faithful, so the isomorphism of the underlying
modules is the image of a unique isomorphism there. -/
noncomputable def representedQuasicoherentSchemeConormalSheafIso :
    representedQuasicoherentSchemePullback B S hS (representingHom B S hS T Z)
        ⟨(Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left)).toSheafOfModules,
          letI := isClosedImmersion_schemeHom_representingHom B S hS T Z
          isQuasicoherent_definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left)⟩ ≅
      (⟨Stacks.Thickenings.schemeConormalSheaf
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left),
          isQuasicoherent_schemeConormalSheaf_representingHom B S hS T Z⟩ :
        (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj
            (representingObj B S hS T Z)).ringCatSheaf).FullSubcategory) :=
  (ObjectProperty.ι _).preimageIso
    (Stacks.Thickenings.schemeConormalSheafIsoPullbackDefiningIdealOfHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z).left))

/-- **The conormal module of a closed subspace of a representable algebraic space is the
`𝒪`-module that the scheme-level conormal sheaf of the representing closed immersion becomes.**
Pulled back along `AlgebraicGeometry.Space.representedSubspaceIso`, the conormal module of
Stacks 04CN of `Z ⊆ yoneda.obj T` is the image of
`Stacks.Thickenings.schemeConormalSheaf` of the representing closed immersion of schemes under
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  Nothing is assumed.

This is `AlgebraicGeometry.Space.conormalModuleIsoRepresentedQuasicoherent` followed by the
transport of `AlgebraicGeometry.Space.representedQuasicoherentSchemeConormalSheafIso` across the
equivalence. -/
noncomputable def conormalModuleIsoRepresentedSchemeConormalSheaf :
    (modulePullback B S hS (representedSubspaceIso B S hS T Z).hom).obj
        (conormalModule B S hS (schemeSpace T) Z) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS
          (representingObj B S hS T Z)).functor.obj
        ⟨Stacks.Thickenings.schemeConormalSheaf
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left),
          isQuasicoherent_schemeConormalSheaf_representingHom B S hS T Z⟩).obj :=
  conormalModuleIsoRepresentedQuasicoherent B S hS T Z ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS
          (representingObj B S hS T Z)).functor.mapIso
        (representedQuasicoherentSchemeConormalSheafIso B S hS T Z))

/-! ### The identification with the conormal sheaf of Stacks 04F4 -/

section Thickening

variable {V₀ W U₀ : BigFppfOver B S hS} (i : V₀ ⟶ W) (p : W ⟶ U₀)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)))
    (h : (BigFppfOver.toScheme B S hS).obj V₀ ⟶ (BigFppfOver.toScheme B S hS).obj U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified h]
    (huS : Stacks.Thickenings.IsUniversalFirstOrderThickening h
      ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map p))

/-- **The conormal sheaf of the representing closed immersion is the direct image of the conormal
sheaf of Stacks 04F4.**  For a closed immersion `i : V₀ ⟶ W` of the site whose scheme image
presents a universal first-order thickening of `h : V₀ ⟶ U₀` over `U₀`, the conormal sheaf of the
closed immersion representing the subspace `Subfunctor.range (yoneda.map i)` is the direct image,
along the isomorphism `AlgebraicGeometry.Space.representingObjIso` of the two sources, of
`Stacks.Thickenings.universalConormalSheaf` of `h`.

This is `Stacks.Thickenings.schemeConormalSheafIsoPushforwardUniversalConormalSheaf` at the
thickening `V₀ ⊂ W ⟶ U₀` and the factorisation
`AlgebraicGeometry.Space.representingObjIso_hom_comp_representingHom`. -/
noncomputable def schemeConormalSheafRepresentingHomIsoPushforward :
    Stacks.Thickenings.schemeConormalSheaf
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (representingHom B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).left) ≅
      (RingedSpaceModuleAdjunction.modulePushforward
          (RingedSpace.ringedSpaceIso ((BigFppfOver.toScheme B S hS).mapIso
            (representingObjIso B S hS i hci hcs))).hom).obj
        (Stacks.Thickenings.universalConormalSheaf h) :=
  Stacks.Thickenings.schemeConormalSheafIsoPushforwardUniversalConormalSheaf h
    { ambient := (BigFppfOver.toScheme B S hS).obj W
      inclusion := (BigFppfOver.toScheme B S hS).map i
      toBase := (BigFppfOver.toScheme B S hS).map p
      isUniversal := huS }
    ((BigFppfOver.toScheme B S hS).mapIso (representingObjIso B S hS i hci hcs))
    ((BigFppfOver.toScheme B S hS).map
      (representingHom B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩))
    (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map
        (representingObjIso_hom_comp_representingHom B S hS i hci hcs)))

include p huS in
/-- The direct image of `Stacks.Thickenings.universalConormalSheaf` along the isomorphism of the
two sources is quasi-coherent, being isomorphic to the conormal sheaf of the representing closed
immersion. -/
theorem isQuasicoherent_pushforward_universalConormalSheaf :
    SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj
        (representingObj B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩)).ringCatSheaf
      ((RingedSpaceModuleAdjunction.modulePushforward
          (RingedSpace.ringedSpaceIso ((BigFppfOver.toScheme B S hS).mapIso
            (representingObjIso B S hS i hci hcs))).hom).obj
        (Stacks.Thickenings.universalConormalSheaf h)) :=
  (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj
        (representingObj B S hS W
          ⟨Subfunctor.range (yoneda.map i), hcs⟩)).ringCatSheaf).prop_of_iso
    (schemeConormalSheafRepresentingHomIsoPushforward B S hS i p hci hcs h huS)
    (isQuasicoherent_schemeConormalSheaf_representingHom B S hS W
      ⟨Subfunctor.range (yoneda.map i), hcs⟩)

/-- `AlgebraicGeometry.Space.schemeConormalSheafRepresentingHomIsoPushforward` read in the
category of **quasi-coherent** modules on the representing scheme, where
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` can carry it. -/
noncomputable def representedQuasicoherentPushforwardUniversalConormalSheafIso :
    (⟨Stacks.Thickenings.schemeConormalSheaf
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).left),
          isQuasicoherent_schemeConormalSheaf_representingHom B S hS W
            ⟨Subfunctor.range (yoneda.map i), hcs⟩⟩ :
        (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj
            (representingObj B S hS W
              ⟨Subfunctor.range (yoneda.map i), hcs⟩)).ringCatSheaf).FullSubcategory) ≅
      ⟨(RingedSpaceModuleAdjunction.modulePushforward
              (RingedSpace.ringedSpaceIso ((BigFppfOver.toScheme B S hS).mapIso
                (representingObjIso B S hS i hci hcs))).hom).obj
            (Stacks.Thickenings.universalConormalSheaf h),
          isQuasicoherent_pushforward_universalConormalSheaf B S hS i p hci hcs h huS⟩ :=
  (ObjectProperty.ι _).preimageIso
    (schemeConormalSheafRepresentingHomIsoPushforward B S hS i p hci hcs h huS)

/-- **The identification of item 2: the conormal module of Stacks 04CN of the closed subspace cut
out by a closed immersion of the site is the `𝒪`-module that the conormal sheaf of Stacks 04F4 of
the thickened morphism of schemes becomes.**

Let `i : V₀ ⟶ W` and `p : W ⟶ U₀` be morphisms of the big fppf category over `S` whose scheme
images make `V₀ ⊂ W` a universal first-order thickening of the formally unramified morphism
`h : V₀ ⟶ U₀` of schemes (Stacks 04F3), and let `Z = Subfunctor.range (yoneda.map i)` be the
closed subspace of `yoneda.obj W` that `i` cuts out.  Then the conormal module of Stacks 04CN of
`Z`, pulled back along `AlgebraicGeometry.Space.representedSubspaceIso`, is the image under
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` of the direct image, along
`AlgebraicGeometry.Space.representingObjIso`, of
`Stacks.Thickenings.universalConormalSheaf h`.

Nothing is assumed beyond the thickening datum.  The section *How the identification is
assembled* of this file says out of what it is composed, and why the direct image cannot be
removed. -/
noncomputable def conormalModuleIsoRepresentedUniversalConormalSheaf :
    (modulePullback B S hS
          (representedSubspaceIso B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).hom).obj
        (conormalModule B S hS (schemeSpace W) ⟨Subfunctor.range (yoneda.map i), hcs⟩) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS
          (representingObj B S hS W
            ⟨Subfunctor.range (yoneda.map i), hcs⟩)).functor.obj
        ⟨(RingedSpaceModuleAdjunction.modulePushforward
              (RingedSpace.ringedSpaceIso ((BigFppfOver.toScheme B S hS).mapIso
                (representingObjIso B S hS i hci hcs))).hom).obj
            (Stacks.Thickenings.universalConormalSheaf h),
          isQuasicoherent_pushforward_universalConormalSheaf B S hS i p hci hcs h huS⟩).obj :=
  conormalModuleIsoRepresentedSchemeConormalSheaf B S hS W
      ⟨Subfunctor.range (yoneda.map i), hcs⟩ ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS
          (representingObj B S hS W
            ⟨Subfunctor.range (yoneda.map i), hcs⟩)).functor.mapIso
        (representedQuasicoherentPushforwardUniversalConormalSheafIso
          B S hS i p hci hcs h huS))

end Thickening

/-! ### The identification at the space-level conormal sheaf -/

/-- **The identification read at the conormal sheaf of Stacks 0607.**  For a morphism `g : V ⟶ U`
of algebraic spaces over `S` whose source and target are representable and a space-level universal
first-order thickening `s` of `g`, the conormal sheaf `𝒞_{V/U}` of `s` is the inverse image, along
a morphism of `V` into the algebraic space the representing scheme represents, of the `𝒪`-module
that `Stacks.Thickenings.universalConormalSheaf` of the corresponding morphism of schemes becomes.

The object `W` and the closed immersion `i : V₀ ⟶ W` of the site are produced by
`AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable`, which also
presents `𝒞_{V/U}` as the conormal module of Stacks 04CN of the closed subspace that `i` cuts out;
`AlgebraicGeometry.Space.conormalModuleIsoRepresentedUniversalConormalSheaf` identifies that
conormal module, and the two inverse images are merged by
`AlgebraicGeometry.Space.modulePullbackObjIsoOfComp`.

This is the form in which the identification of item 2 of the list of carried hypotheses
in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/ConormalShortExact.lean` is consumed. -/
theorem nonempty_conormalSheafIsoRepresentedUniversalConormalSheaf
    {V U : AlgebraicSpaces B S hS} [V.obj.IsRepresentable] [U.obj.IsRepresentable]
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))] :
    ∃ (W : BigFppfOver B S hS) (i : V.obj.reprX ⟶ W) (p : W ⟶ U.obj.reprX)
        (hci : _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map i))
        (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)))
        (huS : Stacks.Thickenings.IsUniversalFirstOrderThickening
          ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))
          ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map p)),
      i ≫ p = yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv) ∧
      Nonempty (conormalSheaf B S hS s ≅
        (modulePullback B S hS
            ((ObjectProperty.homMk (V.obj.reprW.inv ≫ Subfunctor.toRange (yoneda.map i)) :
                V ⟶ (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ :
                  AlgebraicSpaces B S hS)) ≫
              (representedSubspaceIso B S hS W
                ⟨Subfunctor.range (yoneda.map i), hcs⟩).inv)).obj
          ((representedQuasicoherentSchemeEquivalence B S hS
              (representingObj B S hS W
                ⟨Subfunctor.range (yoneda.map i), hcs⟩)).functor.obj
            ⟨(RingedSpaceModuleAdjunction.modulePushforward
                  (RingedSpace.ringedSpaceIso ((BigFppfOver.toScheme B S hS).mapIso
                    (representingObjIso B S hS i hci hcs))).hom).obj
                (Stacks.Thickenings.universalConormalSheaf
                  ((BigFppfOver.toScheme B S hS).map
                    (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))),
              isQuasicoherent_pushforward_universalConormalSheaf B S hS i p hci hcs
                ((BigFppfOver.toScheme B S hS).map
                  (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))
                huS⟩).obj) := by
  obtain ⟨W, i, p, hcs, hcomp, huS, ⟨eiso⟩⟩ :=
    exists_schemeThickening_conormalSheafIso_of_isRepresentable B S hS s
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    huS.isFirstOrderThickening.1
  refine ⟨W, i, p, hci, hcs, huS, hcomp, ⟨eiso ≪≫ ?_⟩⟩
  refine modulePullbackObjIsoOfComp B S hS _ _ _ (by rw [Category.assoc, Iso.inv_hom_id,
      Category.comp_id]) _ ≪≫
    (modulePullback B S hS _).mapIso
      (conormalModuleIsoRepresentedUniversalConormalSheaf B S hS i p hci hcs
        ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv))) huS)

end AlgebraicGeometry.Space

end
