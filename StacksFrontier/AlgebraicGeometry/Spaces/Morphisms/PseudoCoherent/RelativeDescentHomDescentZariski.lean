module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComposition

/-!
# The conclusion of Stacks 0DKV on an affine model, read on the Zariski sites

The affine case of the proof of Stacks 0DKV is "the case of schemes", Stacks 0DI7, read through
Stacks 071Q. After
`AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_of_modelHomDescent` the conclusion of
the tag for a situation with affine `X₀` is
`AlgebraicGeometry.Space.RelativeDescentSituation.ModelHomDescent`, a statement about the small
étale derived pullbacks along the represented morphisms `h_q : h_W ⟶ h_{Z'}` of a system of
objects of the big fppf site.  This file compares it with the same statement for the
Zariski derived pullbacks along the underlying morphisms of schemes,
`AlgebraicGeometry.Space.RelativeDescentSituation.ZariskiModelHomDescent`, which is the shape of
the conclusion of Stacks 0DI7.

The comparison runs through the associated-module functor `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})` of
Stacks 03DU (4) and needs `ε^*` to intertwine the two derived pullbacks *coherently*: an
identification `L(h_g)^* ∘ ε^* ≅ ε^* ∘ Lg^*` for every morphism `g` of the site, compatible with
the composition isomorphisms of Stacks 0D6D on the small étale sites and of Stacks 0D5S on the
Zariski sites.  That datum is
`AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison`.

## Main definitions

* `AlgebraicGeometry.Space.zariskiEtaleDerived`: `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})`.
* `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison`: the coherent identification of
  the two derived pullbacks under `ε^*`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.ZariskiModelHomDescent`: the Zariski form of
  `ModelHomDescent`.

## Main results

* `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison.factorHom_homMap`: under `ε^*`
  the maps on derived homomorphisms induced by a factorisation correspond.
* `AlgebraicGeometry.Space.RelativeDescentSituation.modelHomDescent_of_zariskiModelHomDescent`:
  `ModelHomDescent` for `(ε^*K, ε^*L)` from `ZariskiModelHomDescent` for `(K, L)`, when `ε^*` is
  bijective on the derived homomorphisms of the stages and of the limit.
* `AlgebraicGeometry.Space.RelativeDescentSituation.modelHomDescent_of_iso`: `ModelHomDescent` is
  invariant under isomorphisms of its arguments.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_of_zariskiModelHomDescent`: the
  conclusion of Stacks 0DKV for a situation with affine `X₀` from the Zariski form on its model.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_restrict`: restriction along a
  flat finitely presented morphism onto `X₀` keeps the limit a limit of schemes.

## Implementation notes

Everything is stated for an arbitrary pseudofunctoriality datum `P`, not at
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`: with `canonical` written out the
kernel has to compare the abelian structures on the module categories of represented spaces
that instance search finds here with those `canonical` was elaborated with, and times out.  The
instance environment is that of `RelativeDescentHomDescentModel.lean`, so that `ModelHomDescent`
is read with the same instances.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u v

namespace CategoryTheory.Functor

variable {A A' A'' E E' E'' : Type*} [Category* A] [Category* A'] [Category* A''] [Category* E]
  [Category* E'] [Category* E''] {εT : A ⥤ E} {εT' : A' ⥤ E'} {εT'' : A'' ⥤ E''}
  {Lg : A ⥤ A'} {Lf : A' ⥤ A''} {Lk : A ⥤ A''} {Mg : E ⥤ E'} {Mf : E' ⥤ E''} {Mk : E ⥤ E''}

/-- Conjugation by identifications `M ∘ ε ≅ ε ∘ L` that are compatible with two composition
isomorphisms `c : Mg ⋙ Mf ≅ Mk` and `s : Lg ⋙ Lf ≅ Lk` carries the map on homomorphisms induced
by `s` to the one induced by `c`. -/
theorem homCongr_map_conj_of_coherence (αg : εT ⋙ Mg ≅ Lg ⋙ εT')
    (αf : εT' ⋙ Mf ≅ Lf ⋙ εT'') (αk : εT ⋙ Mk ≅ Lk ⋙ εT'') (c : Mg ⋙ Mf ≅ Mk)
    (s : Lg ⋙ Lf ≅ Lk)
    (coh : ∀ M, c.hom.app (εT.obj M) ≫ αk.hom.app M =
      Mf.map (αg.hom.app M) ≫ αf.hom.app (Lg.obj M) ≫ εT''.map (s.hom.app M))
    {K L : A} (φ : Lg.obj K ⟶ Lg.obj L) :
    (c.app (εT.obj K)).homCongr (c.app (εT.obj L))
        (Mf.map (αg.hom.app K ≫ εT'.map φ ≫ αg.inv.app L)) =
      αk.hom.app K ≫ εT''.map ((s.app K).homCongr (s.app L) (Lf.map φ)) ≫ αk.inv.app L := by
  have nat := αf.hom.naturality φ
  simp only [Functor.comp_map] at nat
  simp only [Iso.homCongr_apply, Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [← cancel_epi (c.hom.app (εT.obj K)), ← cancel_mono (αk.hom.app L)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [coh L, reassoc_of% (coh K)]
  congr 1
  rw [← Mf.map_comp_assoc (αg.inv.app L), Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    reassoc_of% nat, ← εT''.map_comp_assoc (s.hom.app K), Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp]
  simp only [Functor.comp_obj, Category.comp_id]

/-- Conjugating by a natural isomorphism `c : G ⋙ F ≅ H` commutes with conjugating by the images
of isomorphisms `a : K ≅ K'` and `b : L ≅ L'`. -/
theorem homCongr_map_conj_of_iso {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} (c : G ⋙ F ≅ H) {K K' L L' : C₁}
    (a : K ≅ K') (b : L ≅ L') (φ : G.obj K ⟶ G.obj L) :
    (c.app K').homCongr (c.app L') (F.map ((G.mapIso a).homCongr (G.mapIso b) φ)) =
      (H.mapIso a).homCongr (H.mapIso b) ((c.app K).homCongr (c.app L) (F.map φ)) := by
  have na := c.hom.naturality a.inv
  have nb := c.hom.naturality b.hom
  simp only [Functor.comp_map] at na nb
  simp only [Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [← cancel_epi (c.hom.app K')]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% na, Iso.hom_inv_id_app_assoc, nb]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

/-- `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})` for an object `T` of the big fppf site, the functor induced on
derived categories by the exact associated-module functor; it is
`AlgebraicGeometry.Space.representedDerivedAssociatedModule`, with the category of
`𝒪_{h_T}`-modules spelled as the source of the derived pullback of the small étale ringed topos. -/
def zariskiEtaleDerived (T : BigFppfOver B S hS) :
    DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)) :=
  (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategory

/-- If `f ≫ g = k`, then the underlying morphisms of schemes satisfy the same relation. -/
theorem toScheme_map_comp_eq {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T')
    (g : T' ⟶ T) (k : T'' ⟶ T) (h : f ≫ g = k) :
    (BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map k := by
  rw [← Functor.map_comp, h]

/-- **`ε^*` intertwines the derived pullbacks of the Zariski and the small étale sites,
coherently**.  For every morphism `g : T' ⟶ T` of the big fppf site, an
identification `L(h_g)^* ∘ ε_T^* ≅ ε_{T'}^* ∘ Lg^*` of the derived pullback along the represented
morphism of algebraic spaces with the Zariski derived pullback along the underlying morphism of
schemes, compatible with the composition isomorphisms of Stacks 0D6D on both sides: those of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` on the small étale sites and those
of `Stacks.DerivedPullback.schemeFactorIso` (Stacks 0D5S) on the Zariski sites. -/
structure RepresentedDerivedPullbackComparison (P : DerivedPullbackComposition B S hS) where
  /-- The identification `L(h_g)^* ∘ ε_T^* ≅ ε_{T'}^* ∘ Lg^*`. -/
  iso : ∀ {T' T : BigFppfOver B S hS} (g : T' ⟶ T),
    zariskiEtaleDerived B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom ⋙
        zariskiEtaleDerived B S hS T'
  /-- The identifications are compatible with composition. -/
  iso_comp : ∀ {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T') (g : T' ⟶ T) (k : T'' ⟶ T)
    (h : f ≫ g = k) (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))),
    (P.iso (representedSpaceMap B S hS f)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS k)
        (representedSpaceMap_comp_eq B S hS f g k h)).hom.app
          ((zariskiEtaleDerived B S hS T).obj M) ≫ (iso k).hom.app M =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f)).map
          ((iso g).hom.app M) ≫
        (iso f).hom.app
          ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj M) ≫
        (zariskiEtaleDerived B S hS T'').map
          ((Stacks.DerivedPullback.schemeFactorIso ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map k)
            (toScheme_map_comp_eq B S hS f g k h)).hom.app M)

/-- `Stacks.DerivedPullback.schemeFactorHom f g k h K L φ` is `Lf^* φ` conjugated by the
composition isomorphism `Stacks.DerivedPullback.schemeFactorIso f g k h`. -/
theorem schemeFactorHom_eq_homCongr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶ (derivedPullback g.toLRSHom.toShHom).obj L) :
    Stacks.DerivedPullback.schemeFactorHom f g k h K L φ =
      ((Stacks.DerivedPullback.schemeFactorIso f g k h).app K).homCongr
        ((Stacks.DerivedPullback.schemeFactorIso f g k h).app L)
        ((derivedPullback f.toLRSHom.toShHom).map φ) :=
  rfl

/-- `P.factorHom f g k h K L χ` is `L(f)^* χ` conjugated by the composition isomorphism
`P.iso f g k h`. -/
theorem factorHom_eq_homCongr (P : DerivedPullbackComposition B S hS)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h K L χ = ((P.iso f g k h).app K).homCongr ((P.iso f g k h).app L)
      ((smallEtaleDerivedModulePullback B S hS f).map χ) :=
  rfl

namespace RepresentedDerivedPullbackComparison

variable {B S hS} {P : DerivedPullbackComposition B S hS}
  (Φ : RepresentedDerivedPullbackComparison B S hS P)

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(L(h_g)^*ε^*K, L(h_g)^*ε^*L)`: apply `ε^*` and transport
along the identification `L(h_g)^* ∘ ε^* ≅ ε^* ∘ Lg^*`. -/
def homMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (K L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj L) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((zariskiEtaleDerived B S hS T).obj K) ⟶
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((zariskiEtaleDerived B S hS T).obj L) :=
  (Φ.iso g).hom.app K ≫ (zariskiEtaleDerived B S hS T').map φ ≫
    (Φ.iso g).inv.app L

/-- **The maps on derived homomorphisms induced by a factorisation correspond under `ε^*`.** -/
theorem factorHom_homMap {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T') (g : T' ⟶ T)
    (k : T'' ⟶ T) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj L) :
    P.factorHom (representedSpaceMap B S hS f)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS k)
        (representedSpaceMap_comp_eq B S hS f g k h) _ _ (Φ.homMap g K L φ) =
      Φ.homMap k K L (Stacks.DerivedPullback.schemeFactorHom ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map k)
        (toScheme_map_comp_eq B S hS f g k h) K L φ) := by
  rw [factorHom_eq_homCongr, homMap, homMap, schemeFactorHom_eq_homCongr]
  exact CategoryTheory.Functor.homCongr_map_conj_of_coherence _ _ _
    (P.iso (representedSpaceMap B S hS f)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS k)
      (representedSpaceMap_comp_eq B S hS f g k h))
    (Stacks.DerivedPullback.schemeFactorIso ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map k)
      (toScheme_map_comp_eq B S hS f g k h))
    (Φ.iso_comp f g k h) φ

/-- `Φ.homMap` is bijective exactly when `ε^*` is bijective on the derived homomorphisms. -/
theorem bijective_homMap_iff {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (K L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))) :
    Function.Bijective (Φ.homMap g K L) ↔
      Function.Bijective (fun φ : (derivedPullback
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj K ⟶
          (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj L =>
        (zariskiEtaleDerived B S hS T').map φ) := by
  have e : Φ.homMap g K L = (((Φ.iso g).app K).homCongr ((Φ.iso g).app L)).symm ∘
      (fun φ => (zariskiEtaleDerived B S hS T').map φ) := by
    funext φ
    simp only [homMap, Function.comp_apply, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [e]
  exact Equiv.comp_bijective _ _

end RepresentedDerivedPullbackComparison

namespace DerivedPullbackComposition

variable {B S hS} (P : DerivedPullbackComposition B S hS)

/-- The map on derived homomorphisms induced by a factorisation is natural in both arguments: it
commutes with conjugation by the derived pullbacks of isomorphisms `a : K ≅ K'`, `b : L ≅ L'`. -/
theorem factorHom_conj {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    (a : K ≅ K') (b : L ≅ L')
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h K' L' (((smallEtaleDerivedModulePullback B S hS g).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS g).mapIso b) φ) =
      ((smallEtaleDerivedModulePullback B S hS k).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS k).mapIso b) (P.factorHom f g k h K L φ) := by
  rw [factorHom_eq_homCongr, factorHom_eq_homCongr]
  exact CategoryTheory.Functor.homCongr_map_conj_of_iso _ _ _ _

end DerivedPullbackComposition

namespace RelativeDescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] {D : RelativeDescentSituation B S hS hZ I} {Z' : BigAffineFppf B S hS}
  {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ⟶ D.Y.obj (op D.i₀)}
  (R : D.AffineBaseChangeRepresentation Z' z)
  (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
    ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)))

/-- **The conclusion of Stacks 0DKV for the represented system, read on the Zariski sites of the
underlying schemes**: every morphism `Lq^*K ⟶ Lq^*L` over the representing object of the limit
comes from a stage, and two morphisms at a stage with the same image agree at a later stage, for
the Zariski derived pullbacks along the underlying morphisms of schemes. -/
def ZariskiModelHomDescent : Prop :=
  (∀ ψ : (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj K ⟶
        (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj L,
      ∃ (j : D.LaterIndex)
        (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j)).toLRSHom.toShHom).obj K ⟶
          (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j)).toLRSHom.toShHom).obj L),
        Stacks.DerivedPullback.schemeFactorHom
          ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op j)))
          ((BigFppfOver.toScheme B S hS).map (R.q j)) ((BigFppfOver.toScheme B S hS).map R.qc)
          (toScheme_map_comp_eq B S hS _ _ _ (R.π_q j)) K L φ = ψ) ∧
    ∀ (j : D.LaterIndex)
      (φ φ' : (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j)).toLRSHom.toShHom).obj K ⟶
        (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j)).toLRSHom.toShHom).obj L),
      Stacks.DerivedPullback.schemeFactorHom
          ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op j)))
          ((BigFppfOver.toScheme B S hS).map (R.q j)) ((BigFppfOver.toScheme B S hS).map R.qc)
          (toScheme_map_comp_eq B S hS _ _ _ (R.π_q j)) K L φ =
        Stacks.DerivedPullback.schemeFactorHom
          ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op j)))
          ((BigFppfOver.toScheme B S hS).map (R.q j)) ((BigFppfOver.toScheme B S hS).map R.qc)
          (toScheme_map_comp_eq B S hS _ _ _ (R.π_q j)) K L φ' →
        ∃ (k : D.LaterIndex) (h : j ≤ k),
          Stacks.DerivedPullback.schemeFactorHom
              ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
              ((BigFppfOver.toScheme B S hS).map (R.q j))
              ((BigFppfOver.toScheme B S hS).map (R.q k))
              (toScheme_map_comp_eq B S hS _ _ _ (R.map_q j k h)) K L φ =
            Stacks.DerivedPullback.schemeFactorHom
              ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
              ((BigFppfOver.toScheme B S hS).map (R.q j))
              ((BigFppfOver.toScheme B S hS).map (R.q k))
              (toScheme_map_comp_eq B S hS _ _ _ (R.map_q j k h)) K L φ'

variable {P : DerivedPullbackComposition B S hS} (Φ : RepresentedDerivedPullbackComparison B S hS P)
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ D.X₀}
  (R₀ : D.AffineBaseChangeRepresentation Z' (e₀.hom ≫ D.p₀))

/-- **The conclusion of Stacks 0DKV for the represented system from its Zariski form**, when
`ε^*` is bijective on the derived homomorphisms at every stage and at the limit. -/
theorem modelHomDescent_of_zariskiModelHomDescent
    (hj : ∀ j : D.LaterIndex, Function.Bijective (Φ.homMap (R₀.q j) K L))
    (hc : Function.Bijective (Φ.homMap R₀.qc K L)) (H : ZariskiModelHomDescent R₀ K L) :
    ModelHomDescent P e₀ R₀ ((zariskiEtaleDerived B S hS _).obj K)
      ((zariskiEtaleDerived B S hS _).obj L) := by
  refine ⟨fun ψ => ?_, fun j φ φ' hφ => ?_⟩
  · obtain ⟨ψ', rfl⟩ := hc.2 ψ
    obtain ⟨j, φ, hφ⟩ := H.1 ψ'
    refine ⟨j, Φ.homMap (R₀.q j) K L φ, ?_⟩
    rw [← hφ]
    exact Φ.factorHom_homMap _ _ _ (R₀.π_q j) K L φ
  · obtain ⟨χ, rfl⟩ := (hj j).2 φ
    obtain ⟨χ', rfl⟩ := (hj j).2 φ'
    have e := Φ.factorHom_homMap _ _ _ (R₀.π_q j) K L
    obtain ⟨k, hjk, hk⟩ := H.2 j χ χ' (hc.1 ((e χ).symm.trans (hφ.trans (e χ'))))
    refine ⟨k, hjk, ?_⟩
    rw [Φ.factorHom_homMap _ _ _ (R₀.map_q j k hjk) K L χ,
      Φ.factorHom_homMap _ _ _ (R₀.map_q j k hjk) K L χ', hk]

omit Φ in
/-- `ModelHomDescent` is invariant under isomorphisms of both of its arguments. -/
theorem modelHomDescent_of_iso
    {K' K'' L' L'' : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (modelBase (Z' := Z'))))}
    (a : K' ≅ K'') (b : L' ≅ L'') (H : ModelHomDescent P e₀ R₀ K' L') :
    ModelHomDescent P e₀ R₀ K'' L'' := by
  refine ⟨fun ψ => ?_, fun j φ φ' hφ => ?_⟩
  · obtain ⟨j, φ, hφ⟩ := H.1 ((((smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS R₀.qc)).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS R₀.qc)).mapIso b)).symm ψ)
    refine ⟨j, ((smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS (R₀.q j))).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R₀.q j))).mapIso b) φ,
      ?_⟩
    rw [P.factorHom_conj, hφ, Equiv.apply_symm_apply]
  · have hs := (((smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS (R₀.q j))).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS (R₀.q j))).mapIso b)).surjective
    obtain ⟨χ, rfl⟩ := hs φ
    obtain ⟨χ', rfl⟩ := hs φ'
    have e := P.factorHom_conj (representedSpaceMap B S hS (R₀.c.π.app (op j)))
      (representedSpaceMap B S hS (R₀.q j)) (representedSpaceMap B S hS R₀.qc)
      (representedSpaceMap_π_q e₀ R₀ j) a b
    have h3 := (((smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS R₀.qc)).mapIso a).homCongr
        ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS R₀.qc)).mapIso b)).injective
      ((e χ).symm.trans (hφ.trans (e χ')))
    have H2 := H.2 j χ χ'
    have H3 := H2 h3
    obtain ⟨k, hjk, hk⟩ := H3
    refine ⟨k, hjk, ?_⟩
    have f := P.factorHom_conj
      (representedSpaceMap B S hS (R₀.W.map (homOfLE (show j ≤ k from hjk)).op))
      (representedSpaceMap B S hS (R₀.q j)) (representedSpaceMap B S hS (R₀.q k))
      (representedSpaceMap_W_map_q e₀ R₀ hjk) a b
    exact (f χ).trans ((congrArg _ hk).trans (f χ').symm)

/-- **Stacks 0DKV for a situation with affine `X₀`, from the Zariski form on its affine model.**
If the pullbacks of `K` and `L` to the model of `X₀` are `ε^*K''` and `ε^*L''`, `ε^*` is bijective
on the derived homomorphisms of the stages and of the limit of the model, and the Zariski form
`ZariskiModelHomDescent` holds for `(K'', L'')`, then the conclusion of the tag holds for
`(K, L)`. -/
theorem homDescent_of_zariskiModelHomDescent (K L : D.InitialDerived)
    {K'' L'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace))}
    (a : (zariskiEtaleDerived B S hS _).obj K'' ≅
      (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K)
    (b : (zariskiEtaleDerived B S hS _).obj L'' ≅
      (smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj L)
    (hj : ∀ j : D.LaterIndex, Function.Bijective (Φ.homMap (R₀.q j) K'' L''))
    (hc : Function.Bijective (Φ.homMap R₀.qc K'' L'')) (H : ZariskiModelHomDescent R₀ K'' L'') :
    D.HomDescent P K L :=
  homDescent_of_modelHomDescent P e₀ R₀ K L
    (modelHomDescent_of_iso R₀ a b
      (modelHomDescent_of_zariskiModelHomDescent (K := K'') (L := L'') (Φ := Φ) (R₀ := R₀) hj hc H))

omit Φ in
/-- **Restricting Situation 0DKU along a flat finitely presented morphism onto `X₀` keeps the
limit a limit of schemes on affine charts**: the restriction does not change the inverse system,
its limit or the chosen stage. -/
theorem isSchemeLimit_restrict (hD : D.IsSchemeLimit) {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀) (hgflat : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g) : (D.restrict hU₀ g hgflat hgfp).IsSchemeLimit :=
  ⟨hD.1, fun Z z R => hD.2 Z z
    { W := R.W, c := R.c, p := R.p, q := R.q, isPullback := R.isPullback, map_p := R.map_p,
      map_q := R.map_q, pc := R.pc, qc := R.qc, isPullback_pt := R.isPullback_pt, π_p := R.π_p,
      π_q := R.π_q }⟩

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
