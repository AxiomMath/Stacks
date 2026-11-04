module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CanonicalSchemeTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCoveringEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprBaseNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedSchemeModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase

/-!
# The component modules of a descent datum of a represented family, read on the space side

Let `B` be a big fppf site containing a scheme `S`, let `g : V ⟶ U` be a morphism of the big fppf
category over `S`, and let `M` be a quasi-coherent module on the scheme underlying `U`. An
isomorphism of the pullback of `M` along the underlying morphism of schemes with the module on the
scheme underlying `V` of an `𝒪`-module `F` on `yoneda.obj V` comes from an isomorphism of `F` with
the inverse image along `g` (Stacks 03LU) of the `𝒪`-module on `yoneda.obj U` that Stacks 03DX (2)
attaches to `M`. With this, every descent datum of quasi-coherent `𝒪`-modules relative to a
represented fpqc family is effective.

## Main definitions

* `CategoryTheory.isoOfBijectiveMap`: an isomorphism of two objects from an isomorphism of their
  images under a functor which is bijective on the hom-sets involved.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso`: the
  module on the scheme underlying `V` of the inverse image of the transported module is the
  module of the given one.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedModuleIsoOfSchemeIso`: the inverse
  image along `g` of the `𝒪`-module on `yoneda.obj U` attached to `M` is the given `𝒪`-module on
  `yoneda.obj V`, whenever their modules on the underlying schemes are isomorphic.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.IsSchemeCanonicalNatural`: the pairwise condition
  on the underlying schemes relating a family of isomorphisms of the pullbacks of one module with
  the readings of the transitions of the given datum.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedComponentIso`: the component
  isomorphism, at the component of the canonical descent datum.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.representedZariski_map_representedModuleIsoOfSchemeIso` and `…_inv`: the reading of
  `representedModuleIsoOfSchemeIso` on the underlying scheme is the identification it was
  reflected from.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_schemeIso_isSchemeCanonicalNatural`: a
  descent datum of a represented fpqc family has, on the underlying schemes, a module `M` and a
  compatible family of isomorphisms of its pullbacks with the component modules.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.zariskiSquare_representedZariskiPullbackIsoOfSchemeIso` and
  `…isZariskiNatural_representedModuleIsoOfSchemeIso`: the component isomorphisms commute with
  the two transitions read on the underlying schemes.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isCovering_represented`: every
  descent datum relative to a represented fpqc family is effective.

## Implementation notes

The `CategoryTheory.Cat`-bundled category of `AlgebraicGeometry.modulePullbackPseudofunctor` and
`AlgebraicGeometry.Scheme.Modules` are definitionally equal but different terms. Several
comparisons here are therefore stated at variable data, in declarations of their own, or composed
with `congrArg` and `Eq.trans` rather than `rw`; `CategoryTheory.isoOfBijectiveMap` is stated at
a variable functor for the same reason.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

/-- An isomorphism of two objects from an isomorphism of their images under a functor which is
bijective on the hom-sets involved. -/
def isoOfBijectiveMap {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A F : C}
    (hAF : Function.Bijective fun x : A ⟶ F => G.map x)
    (hFA : Function.Bijective fun x : F ⟶ A => G.map x)
    (hAA : Function.Injective fun x : A ⟶ A => G.map x)
    (hFF : Function.Injective fun x : F ⟶ F => G.map x)
    (e : G.obj A ≅ G.obj F) : A ≅ F where
  hom := (hAF.2 e.hom).choose
  inv := (hFA.2 e.inv).choose
  hom_inv_id := hAA (by
    simp only [G.map_comp, G.map_id, (hAF.2 e.hom).choose_spec, (hFA.2 e.inv).choose_spec,
      e.hom_inv_id])
  inv_hom_id := hFF (by
    simp only [G.map_comp, G.map_id, (hAF.2 e.hom).choose_spec, (hFA.2 e.inv).choose_spec,
      e.inv_hom_id])

/-- The image under the functor of the isomorphism reflected by
`CategoryTheory.isoOfBijectiveMap` is the given one. -/
@[simp]
theorem isoOfBijectiveMap_map_hom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A F : C}
    (hAF : Function.Bijective fun x : A ⟶ F => G.map x)
    (hFA : Function.Bijective fun x : F ⟶ A => G.map x)
    (hAA : Function.Injective fun x : A ⟶ A => G.map x)
    (hFF : Function.Injective fun x : F ⟶ F => G.map x)
    (e : G.obj A ≅ G.obj F) :
    G.map (isoOfBijectiveMap G hAF hFA hAA hFF e).hom = e.hom :=
  (hAF.2 e.hom).choose_spec

/-- The image under the functor of the inverse of the isomorphism reflected by
`CategoryTheory.isoOfBijectiveMap` is the inverse of the given one. -/
@[simp]
theorem isoOfBijectiveMap_map_inv {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A F : C}
    (hAF : Function.Bijective fun x : A ⟶ F => G.map x)
    (hFA : Function.Bijective fun x : F ⟶ A => G.map x)
    (hAA : Function.Injective fun x : A ⟶ A => G.map x)
    (hFF : Function.Injective fun x : F ⟶ F => G.map x)
    (e : G.obj A ≅ G.obj F) :
    G.map (isoOfBijectiveMap G hAF hFA hAA hFF e).inv = e.inv :=
  (hFA.2 e.inv).choose_spec

end CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Member

variable {V U : BigFppfOver B S hS} (g : V ⟶ U)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS V))

/-- The module on the scheme underlying `V` of the inverse image along `g` of the `𝒪`-module on
`yoneda.obj U` attached to `M` is the pullback of `M`, hence, through the given isomorphism `ε`,
the module of the given `𝒪`-module on `yoneda.obj V`. -/
def representedZariskiPullbackIsoOfSchemeIso
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    representedZariskiModule B S hS V
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj) ≅
      representedZariskiModule B S hS V F :=
  (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property).symm ≪≫
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
        (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ≪≫
      ε

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso`
written out as a composite of three isomorphisms. -/
theorem representedZariskiPullbackIsoOfSchemeIso_eq
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    representedZariskiPullbackIsoOfSchemeIso B S hS g M F ε =
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property).symm ≪≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
            (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ≪≫
          ε :=
  rfl

/-- Equalities of the two outer factors transfer a commutation of composites. -/
private theorem comp_eq_comp_of_eq_of_eq {C : Type*} [Category C] {W X Y Z : C}
    {u u' : W ⟶ X} {v v' : Y ⟶ Z} {s : W ⟶ Y} {t : X ⟶ Z} (hu : u = u') (hv : v = v')
    (h : u' ≫ t = s ≫ v') : u ≫ t = s ≫ v := by
  subst hu hv
  exact h

section Pulled

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The inverse image along a further morphism `a` of the inverse of
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso`, split
into its three factors. -/
theorem map_representedZariskiPullbackIsoOfSchemeIso_inv {Y : BigFppfOver B S hS} (a : Y ⟶ V)
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) a.left)).map
        (representedZariskiPullbackIsoOfSchemeIso B S hS g M F ε).inv =
      (((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
                (associatedBigEtaleSite B) a.left)).mapIso
            (representedZariskiModulePullbackIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
                M).property)).symm ≪≫
          (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) a.left)).mapIso
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
              (representedZariskiModuleQuasicoherentSchemeIso B S hS U M)) ≪≫
          (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) a.left)).mapIso ε).inv := by
  rw [← Functor.mapIso_inv, representedZariskiPullbackIsoOfSchemeIso_eq]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]

end Pulled

/-- The inverse image along `g` of the `𝒪`-module on `yoneda.obj U` attached to `M` is the
given `𝒪`-module on `yoneda.obj V`, whenever the pullback of `M` along the underlying morphism
of schemes is isomorphic to the module of that `𝒪`-module on the scheme underlying `V`. -/
def representedModuleIsoOfSchemeIso (hF : F.IsQuasicoherentOnSite)
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≅ F :=
  have hA := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  isoOfBijectiveMap
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (bijective_representedZariski_map B S hS _ F hA)
    (bijective_representedZariski_map B S hS F _ hF)
    (bijective_representedZariski_map B S hS _ _ hA).1
    (bijective_representedZariski_map B S hS F F hF).1
    (representedZariskiPullbackIsoOfSchemeIso B S hS g M F ε)

/-- The reading of
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedModuleIsoOfSchemeIso` on the underlying
scheme is the identification
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso` it was
reflected from. -/
theorem representedZariski_map_representedModuleIsoOfSchemeIso (hF : F.IsQuasicoherentOnSite)
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          (representedModuleIsoOfSchemeIso B S hS g M F hF ε).hom) =
      (representedZariskiPullbackIsoOfSchemeIso B S hS g M F ε).hom := by
  have hA := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  exact isoOfBijectiveMap_map_hom
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (bijective_representedZariski_map B S hS _ F hA)
    (bijective_representedZariski_map B S hS F _ hF)
    (bijective_representedZariski_map B S hS _ _ hA).1
    (bijective_representedZariski_map B S hS F F hF).1 _

/-- The reading of the inverse of
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedModuleIsoOfSchemeIso` on the underlying
scheme. -/
theorem representedZariski_map_representedModuleIsoOfSchemeIso_inv
    (hF : F.IsQuasicoherentOnSite)
    (ε : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M.obj ≅
      representedZariskiModule B S hS V F) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
          (representedModuleIsoOfSchemeIso B S hS g M F hF ε).inv) =
      (representedZariskiPullbackIsoOfSchemeIso B S hS g M F ε).inv := by
  have hA := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  exact isoOfBijectiveMap_map_inv
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (bijective_representedZariski_map B S hS _ F hA)
    (bijective_representedZariski_map B S hS F _ hF)
    (bijective_representedZariski_map B S hS _ _ hA).1
    (bijective_representedZariski_map B S hS F F hF).1 _

end Member

section Assembly

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)
  (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))

/-- The pairwise condition, on the underlying schemes, relating a family of isomorphisms of the
pullbacks of one quasi-coherent module with the readings of the transitions of `D`: at every
object `Y` of the big fppf category over `S` mapping to two members of the family with equal
composites to `U`, the pullback of `ε i` commutes with the reading
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` of the transition of `D` and
with the transition `AlgebraicGeometry.modulesCanonicalTransition` of the canonical descent datum
of `M` over schemes. -/
def IsSchemeCanonicalNatural
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (ε : ∀ i, (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (f i))).obj M.obj ≅
      representedZariskiModule B S hS (T i) (D.F i)) : Prop :=
  ∀ (Y : BigFppfOver B S hS) (q : Y ⟶ U) (i j : I) (a : Y ⟶ T i) (b : Y ⟶ T j)
      (ha : a ≫ f i = q) (hb : b ≫ f j = q)
      (ha' : (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map (f i) =
        (BigFppfOver.toScheme B S hS).map q)
      (hb' : (BigFppfOver.toScheme B S hS).map b ≫ (BigFppfOver.toScheme B S hS).map (f j) =
        (BigFppfOver.toScheme B S hS).map q),
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map (ε i).hom ≫
          (zariskiTransitionOn B S hS T f D a b ha hb).hom =
        modulesCanonicalTransition (fun i => (BigFppfOver.toScheme B S hS).map (f i)) M
            ((BigFppfOver.toScheme B S hS).map q) i j ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) ha' hb' ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map b)).map (ε j).hom

/-- For a descent datum `D` of a represented fpqc family there is a quasi-coherent module `M` on
the scheme underlying `U` and, for each member, an isomorphism `ε i` of the pullback of `M` along
the underlying morphism of schemes with the module of `D.F i` on the scheme underlying `T i`, and
the family `ε` is `AlgebraicGeometry.Space.QuasiCoherentDescent.IsSchemeCanonicalNatural`. -/
theorem exists_schemeIso_isSchemeCanonicalNatural
    (hf : Topology.IsCovering .fpqc B S hS (fun i => yoneda.obj (T i))
      (fun i => yoneda.map (f i))) :
    ∃ (M : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
      (ε : ∀ i, (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (f i))).obj M.obj ≅
        representedZariskiModule B S hS (T i) (D.F i)),
      IsSchemeCanonicalNatural B S hS T f D ε := by
  obtain ⟨D₀, hEff, ⟨e⟩⟩ := exists_isEffective_iso_reprSchemeDatum_of_isCovering B S hS T f D hf
  obtain ⟨M, ⟨eM⟩⟩ := hEff
  have Θ : Pseudofunctor.restrictDescentDataObj modulePullbackPseudofunctor
        (BigFppfOver.toScheme B S hS) f
        ((_root_.AlgebraicGeometry.canonicalDescentFunctor fun i =>
          (BigFppfOver.toScheme B S hS).map (f i)).obj M).obj ≅
      reprSchemeDatum B S hS T f D :=
    (Pseudofunctor.restrictDescentData modulePullbackPseudofunctor
        (BigFppfOver.toScheme B S hS) f).mapIso ((ObjectProperty.ι _).mapIso eM) ≪≫ e
  refine ⟨M, fun i => Pseudofunctor.DescentData.objIso Θ i, ?_⟩
  intro Y q i j a b ha hb ha' hb'
  have h := _root_.AlgebraicGeometry.restrictDescentDataHom_comm_modules
    (BigFppfOver.toScheme B S hS) f Θ.hom q a b ha hb
  rwa [reprSchemeDatum_hom B S hS T f D q a b ha hb,
    _root_.AlgebraicGeometry.restrictDescentDataObj_hom_canonical
      (BigFppfOver.toScheme B S hS) f M Y q i j a b ha hb ha' hb'] at h

section Naturality

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Space.smallEtaleRingedSite

variable {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  (ε : ∀ i, (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (f i))).obj M.obj ≅
    representedZariskiModule B S hS (T i) (D.F i))

/-- The identification
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedZariskiPullbackIsoOfSchemeIso` of the
module of the inverse image of the transported `𝒪`-module with the module of `D.F i` commutes
with the reading of the transition of `D` and the reading of the transition of the canonical
descent datum of Stacks 04W5. -/
theorem zariskiSquare_representedZariskiPullbackIsoOfSchemeIso
    (hε : IsSchemeCanonicalNatural B S hS T f D ε) (Y : BigFppfOver B S hS) (q : Y ⟶ U) (i j : I)
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) a.left)).map
          (representedZariskiPullbackIsoOfSchemeIso B S hS (f i) M (D.F i) (ε i)).inv ≫
        (zariskiTransitionOn B S hS T f
          (canonicalDescentDatum B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property)
          a b ha hb).hom =
      (zariskiTransitionOn B S hS T f D a b ha hb).hom ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) b.left)).map
          (representedZariskiPullbackIsoOfSchemeIso B S hS (f j) M (D.F j) (ε j)).inv := by
  have ha' : (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map (f i) =
      (BigFppfOver.toScheme B S hS).map q := by
    rw [← Functor.map_comp, ha]
  have hb' : (BigFppfOver.toScheme B S hS).map b ≫ (BigFppfOver.toScheme B S hS).map (f j) =
      (BigFppfOver.toScheme B S hS).map q := by
    rw [← Functor.map_comp, hb]
  have hcan := congrArg Iso.hom (zariskiTransitionOn_canonicalDescentDatum B S hS T f
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
    a b ha hb (ha'.trans hb'.symm))
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom] at hcan
  have hstep := hε Y q i j a b ha hb ha' hb'
  rw [_root_.AlgebraicGeometry.modulesCanonicalTransition_eq] at hstep
  have hnat := _root_.AlgebraicGeometry.pullbackComp_conj_eq
    ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map (f i))
    ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map (f j))
    (ha'.trans hb'.symm) (representedZariskiModuleQuasicoherentSchemeIso B S hS U M)
  have hsplit := Stacks.conj_of_two_squares
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) a.left)).mapIso
      (representedZariskiModulePullbackIso B S hS (f i)
        (relativelyRepresentable_yoneda_map B S hS (f i))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) b.left)).mapIso
      (representedZariskiModulePullbackIso B S hS (f j)
        (relativelyRepresentable_yoneda_map B S hS (f j))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) a.left)).mapIso
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (f i))).mapIso
        (representedZariskiModuleQuasicoherentSchemeIso B S hS U M)))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) b.left)).mapIso
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (f j))).mapIso
        (representedZariskiModuleQuasicoherentSchemeIso B S hS U M)))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) a.left)).mapIso (ε i))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) b.left)).mapIso (ε j))
    _ _ _ _ _ _ _ _ hcan hstep hnat
  exact comp_eq_comp_of_eq_of_eq
    (map_representedZariskiPullbackIsoOfSchemeIso_inv B S hS (f i) M (D.F i) a (ε i))
    (map_representedZariskiPullbackIsoOfSchemeIso_inv B S hS (f j) M (D.F j) b (ε j)) hsplit

/-- Given `M` and a family `ε` as in
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_schemeIso_isSchemeCanonicalNatural`, the
`𝒪`-module isomorphisms `AlgebraicGeometry.Space.QuasiCoherentDescent`
`.representedModuleIsoOfSchemeIso` they reflect are
`AlgebraicGeometry.Space.QuasiCoherentDescent.IsZariskiNatural` from `D` to the canonical descent
datum of Stacks 04W5 of the `𝒪`-module on `yoneda.obj U` that Stacks 03DX (2) attaches to `M`. -/
theorem isZariskiNatural_representedModuleIsoOfSchemeIso
    (hε : IsSchemeCanonicalNatural B S hS T f D ε) :
    IsZariskiNatural B S hS (T := T) (f := f) (D := D)
      (E := canonicalDescentDatum B S hS (representedFamily B S hS T)
        (representedFamilyMap B S hS T f)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property)
      (fun i => (representedModuleIsoOfSchemeIso B S hS (f i) M (D.F i)
        (D.quasicoherent i) (ε i)).inv) := by
  intro Y q i j a b ha hb
  have sq := zariskiSquare_representedZariskiPullbackIsoOfSchemeIso B S hS T f D ε hε
    Y q i j a b ha hb
  exact comp_eq_comp_of_eq_of_eq
    (congrArg _ (representedZariski_map_representedModuleIsoOfSchemeIso_inv B S hS (f i) M
      (D.F i) (D.quasicoherent i) (ε i)))
    (congrArg _ (representedZariski_map_representedModuleIsoOfSchemeIso_inv B S hS (f j) M
      (D.F j) (D.quasicoherent j) (ε j))) sq

/-- The inverse of `AlgebraicGeometry.Space.QuasiCoherentDescent.representedModuleIsoOfSchemeIso`,
as an isomorphism with the component of the canonical descent datum. -/
def representedComponentIso (i : I) :
    D.F i ≅ (canonicalDescentDatum B S hS (representedFamily B S hS T)
      (representedFamilyMap B S hS T f)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property).F i :=
  (representedModuleIsoOfSchemeIso B S hS (f i) M (D.F i) (D.quasicoherent i) (ε i)).symm

/-- The component isomorphisms `representedComponentIso` commute with the transitions of `D` and
of the canonical descent datum on the pairwise fibre products. -/
theorem naturality_representedComponentIso
    (hε : IsSchemeCanonicalNatural B S hS T f D ε) (i j : I) :
    (modulePullback B S hS (pairFst B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) i j)).map
        (representedComponentIso B S hS T f D ε i).hom ≫
      ((canonicalDescentDatum B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
            M).property).transition i j).hom =
    (D.transition i j).hom ≫
      (modulePullback B S hS (pairSnd B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) i j)).map
        (representedComponentIso B S hS T f D ε j).hom :=
  naturality_of_zariskiTransitionOn B S hS _
    (isZariskiNatural_representedModuleIsoOfSchemeIso B S hS T f D ε hε) i j

end Naturality

end Assembly

/-- For a family `f i : T i ⟶ U` of the big fppf category over `S` whose represented family of
algebraic spaces is an fpqc covering, every descent datum of quasi-coherent `𝒪`-modules relative
to it is isomorphic to the canonical descent datum of Stacks 04W5 of a quasi-coherent `𝒪`-module
on `yoneda.obj U`. -/
theorem isEffective_of_isCovering_represented
    {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS) (f : ∀ i, T i ⟶ U)
    (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))
    (hf : Topology.IsCovering .fpqc B S hS (fun i => yoneda.obj (T i))
      (fun i => yoneda.map (f i))) :
    IsEffective B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) D := by
  obtain ⟨M, ε, hε⟩ := exists_schemeIso_isSchemeCanonicalNatural B S hS T f D hf
  exact isEffective_of_forall_iso B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) D _ _ (representedComponentIso B S hS T f D ε)
    (naturality_representedComponentIso B S hS T f D ε hε)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
