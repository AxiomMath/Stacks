module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedBaseEffectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare

/-!
# Inverse images of the modules attached to quasi-coherent modules on a scheme chart

Let `U` be an object of the big fppf site over `S`.  A quasi-coherent module `M` on the scheme
underlying `U` is an `𝒪`-module on the representable algebraic space `yoneda.obj U` through
Stacks 03DX (2), `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  The descent
of Stacks 084D starts from such modules: the twists of Stacks 01NR live on the scheme of the
chart `P_U = U ×_X Proj_X(𝒜)`, and descent data are formed from their inverse images along
morphisms of representable algebraic spaces.  This file identifies those inverse images.

For a morphism `g : V ⟶ U` of the site, the inverse image of Stacks 03LU along the morphism of
representable algebraic spaces `g` induces of the `𝒪`-module attached to `M` is the `𝒪`-module
attached to the pullback `g^*M` of `M` along the underlying morphism of schemes.  The isomorphism
is reflected from the scheme side by
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedModuleIsoOfSchemeIso`, and its reading on
the scheme underlying `V` is the composite of the comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` with the pullback of the base
identification `AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso`, followed
by the inverse of that identification at `g^*M`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`: **the inverse image along
  `g` of the `𝒪`-module attached to `M` is the `𝒪`-module attached to `g^*M`.**
* `AlgebraicGeometry.Space.quasicoherentPullbackCompIso`: the contraction `h^*(g^*M) ≅ (h ≫ g)^*M`
  of two pullbacks, as an isomorphism of quasi-coherent modules.

## Main results

* `AlgebraicGeometry.Space.representedZariski_map_modulePullbackRepresentedQuasicoherentIso`: its
  reading on the scheme underlying `V`, the form in which a comparison of descent data on the
  underlying schemes consumes it, and `…_mapIso_…` the same as an equality of isomorphisms.
* `AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso_naturality` and `…_iso`:
  the base identification of Stacks 03DX (2) on a representable algebraic space is natural.
* `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_comp`: **the identification
  composes** — along `h ≫ g` it is the identification along `g` pulled back along `h`, followed by
  the one along `h` and the contraction of the two pullbacks.  This is the coherence a cocycle
  condition of descent data built from these identifications is reduced with.

## Implementation notes

The composition law is reflected from the underlying scheme and computed there as an equality of
**isomorphisms**, with the iso-level restatements
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_iso` and
`…_naturality_iso` of the base; the morphisms of the pullbacks of modules are taken along
`AlgebraicGeometry.SmallEtale.schemeHom`, the spelling those restatements use, so that the
cancellations are syntactic.  The naturality of the base identification is proved without
inverting the unit of `𝓕 ↦ 𝓕^a`, and every composite there is formed with the functor of its
factors given explicitly, since a rewrite with `CategoryTheory.Functor.map_comp` does not see
through the two spellings of the composition of modules on a scheme.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback of a quasi-coherent module along a morphism of the site, as an object of the
full subcategory of quasi-coherent modules on the scheme underlying the source. -/
abbrev quasicoherentPullbackObj {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj,
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom M.obj M.property⟩

/-- **The inverse image along a morphism of representable algebraic spaces of the `𝒪`-module
attached to a quasi-coherent module on the scheme is the `𝒪`-module attached to its pullback.**
For `g : V ⟶ U` of the site and `M` quasi-coherent on the scheme underlying `U`,
`g^*(M_{yoneda U}) ≅ (g^*M)_{yoneda V}`, where `(-)_{yoneda U}` is Stacks 03DX (2). -/
def modulePullbackRepresentedQuasicoherentIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
        (quasicoherentPullbackObj B S hS g M)).obj :=
  QuasiCoherentDescent.representedModuleIsoOfSchemeIso B S hS g M _
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
      (quasicoherentPullbackObj B S hS g M)).property
    (representedZariskiModuleQuasicoherentSchemeIso B S hS V
      (quasicoherentPullbackObj B S hS g M)).symm

/-- **The reading of `modulePullbackRepresentedQuasicoherentIso` on the scheme underlying the
source**: the comparison of Stacks 03LU with pullback of modules on schemes, followed by the
pullback of the base identification of `M` and the inverse of the base identification of
`g^*M`. -/
theorem representedZariski_map_modulePullbackRepresentedQuasicoherentIso
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom) =
      (QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso B S hS g M _
        (representedZariskiModuleQuasicoherentSchemeIso B S hS V
          (quasicoherentPullbackObj B S hS g M)).symm).hom :=
  QuasiCoherentDescent.representedZariski_map_representedModuleIsoOfSchemeIso B S hS g M _ _ _

/-! ### Naturality of the base identification, and composition -/

section Comp

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The base identification of Stacks 03DX (2) is natural.**  For a morphism `φ : M ⟶ N` of
quasi-coherent modules on the scheme underlying `U`, the module on the scheme of the morphism of
attached `𝒪`-modules is `φ`, read through
`AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso` at both ends.  It is the
naturality of the unit of the adjunction `𝓕 ↦ 𝓕^a` and of the unit of the equivalence
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, stated with the inverses of the
identifications so that no inverse of a morphism is formed. -/
theorem representedZariskiModuleQuasicoherentSchemeIso_naturality {U : BigFppfOver B S hS}
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    φ.hom ≫ (representedZariskiModuleQuasicoherentSchemeIso B S hS U N).inv =
      (representedZariskiModuleQuasicoherentSchemeIso B S hS U M).inv ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map φ).hom) := by
  have hu := (representedSmallEtaleModuleEquivalence B S hS U).unitIso.hom.naturality
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map φ.hom)
  have ha := (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
    U.left.property).unit.naturality φ.hom
  have h3 := ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map_comp _ _).symm.trans
    ((congrArg (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map hu).trans
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map_comp _ _))
  have h4 := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ha).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3)))
  exact h4

/-- `AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso_naturality` for an
isomorphism, as an equality of isomorphisms. -/
theorem representedZariskiModuleQuasicoherentSchemeIso_naturality_iso {U : BigFppfOver B S hS}
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ≅ N) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.mapIso
          ((ObjectProperty.ι _).mapIso
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.mapIso φ))) =
      representedZariskiModuleQuasicoherentSchemeIso B S hS U M ≪≫
        (ObjectProperty.ι _).mapIso φ ≪≫
          (representedZariskiModuleQuasicoherentSchemeIso B S hS U N).symm :=
  Iso.ext ((Iso.inv_comp_eq _).1
    (representedZariskiModuleQuasicoherentSchemeIso_naturality B S hS φ.hom).symm)

/-- `AlgebraicGeometry.Space.representedZariski_map_modulePullbackRepresentedQuasicoherentIso` as
an equality of isomorphisms, split into its three factors. -/
theorem representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.mapIso
          (modulePullbackRepresentedQuasicoherentIso B S hS g M)) =
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property).symm ≪≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).mapIso
            (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ≪≫
          (representedZariskiModuleQuasicoherentSchemeIso B S hS V
            (quasicoherentPullbackObj B S hS g M)).symm :=
  Iso.ext (representedZariski_map_modulePullbackRepresentedQuasicoherentIso B S hS g M)

/-- The contraction of two pullbacks of a quasi-coherent module along morphisms of the site, as an
isomorphism of quasi-coherent modules: `h^*(g^*M) ≅ (h ≫ g)^*M`. -/
def quasicoherentPullbackCompIso {W V U : BigFppfOver B S hS} (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackObj B S hS h (quasicoherentPullbackObj B S hS g M) ≅
      quasicoherentPullbackObj B S hS (h ≫ g) M :=
  ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackComp
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).app M.obj)

/-- **The identification `g^*(M_{yoneda U}) ≅ (g^*M)_{yoneda V}` composes.**  For `h : W ⟶ V` and
`g : V ⟶ U` of the site, the identification along `h ≫ g`, preceded by the contraction of the two
inverse images of Stacks 03LU, is the identification along `g` pulled back along `h`, followed by
the identification along `h` and by the module attached to the contraction `h^*(g^*M) ≅ (h ≫ g)^*M`
of the two pullbacks on the schemes.

Both sides are reflected from their readings on the scheme underlying `W`
(`AlgebraicGeometry.Space.QuasiCoherentDescent.bijective_representedZariski_map`), where the
equation is the composition law
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_iso` of the comparison, its
naturality, the naturality of the base identification and the naturality of the contraction of
pullbacks on schemes. -/
theorem modulePullbackRepresentedQuasicoherentIso_comp {W V U : BigFppfOver B S hS}
    (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (representedModulePullbackCompIso B S hS h g).app
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M =
    (modulePullback B S hS (representedSpaceMap B S hS h)).mapIso
        (modulePullbackRepresentedQuasicoherentIso B S hS g M) ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS h (quasicoherentPullbackObj B S hS g M) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.mapIso
            (quasicoherentPullbackCompIso B S hS h g M)) := by
  have hF := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  have hgF := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) _ hF
  have hA := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS h
    (relativelyRepresentable_yoneda_map B S hS h) _ hgF
  refine Iso.ext ((QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _ hA).1 ?_)
  refine congrArg Iso.hom (?_ :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS W).inverse.mapIso _) =
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS W).inverse.mapIso _))
  have hcomp := representedZariskiModulePullbackIso_comp_iso B S hS h g
    (relativelyRepresentable_yoneda_map B S hS h) (relativelyRepresentable_yoneda_map B S hS g)
    (relativelyRepresentable_yoneda_map B S hS (h ≫ g)) _ hF
  have hnat := representedZariskiModulePullbackIso_naturality_iso B S hS h
    (relativelyRepresentable_yoneda_map B S hS h) hgF
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
      (quasicoherentPullbackObj B S hS g M)).property
    (modulePullbackRepresentedQuasicoherentIso B S hS g M)
  have hpc : ∀ {Z} (x : _ ≅ Z),
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).app
          (representedZariskiModule B S hS U
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj) ≪≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) (h ≫ g).left)).mapIso
          (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ≪≫ x =
      (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).mapIso
          ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).mapIso
            (representedZariskiModuleQuasicoherentSchemeIso B S hS U M)) ≪≫
        (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).app
            M.obj ≪≫ x := fun x => by
    rw [← Iso.trans_assoc, ← Iso.trans_assoc]
    congr 1
    exact Iso.ext ((Scheme.Modules.pullbackComp
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left)).hom.naturality
        (representedZariskiModuleQuasicoherentSchemeIso B S hS U M).hom).symm
  have hK := congrArg (fun e => Iso.trans (Iso.symm (Iso.trans
      ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) h.left)).mapIso
        (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          _ hF))
      (representedZariskiModulePullbackIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h) _ hgF))) e) hcomp
  have hN := congrArg (fun e => Iso.trans (Iso.symm (representedZariskiModulePullbackIso B S hS h
      (relativelyRepresentable_yoneda_map B S hS h) _ hgF)) e) hnat
  have hι : (ObjectProperty.ι _).mapIso (quasicoherentPullbackCompIso B S hS h g M) =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).app
        M.obj :=
    rfl
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc] at hK hN
  simp only [Functor.mapIso_trans, hK, ← hN,
    representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso,
    representedZariskiModuleQuasicoherentSchemeIso_naturality_iso, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc, hpc]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg (· ≪≫ _) hι.symm)))

end Comp

end AlgebraicGeometry.Space

end
