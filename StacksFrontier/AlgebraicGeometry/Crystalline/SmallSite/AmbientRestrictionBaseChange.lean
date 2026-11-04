module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionConservative

/-!
# The ambient restrictions of a localised small crystalline site compare with those of its base

This is the small-site counterpart of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionBaseChange`.  Let `B`
be an object `(U', T', δ')` of the small crystalline site `Cris(X/S)` and let
`X = (g : (U, T, δ) ⟶ B)` be an object of the localised site `Cris(X/S)/B`.  Restriction of a
sheaf of modules on `Cris(X/S)/B` along the ambient restriction
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverFunctor` of `X`
is a Zariski sheaf `ρ_X(F)` on the ambient scheme `T` of `X`, and along the ambient restriction of
the base it is a Zariski sheaf `ρ_B(F)` on the ambient scheme `T'` of `B`.  The two are compared by
the `f`-map `ρ_B(F) ⟶ g_* ρ_X(F)` and its transpose `g^* ρ_B(F) ⟶ ρ_X(F)`, both natural in `F`,
and the transpose is invertible when `F` is the restriction to `Cris(X/S)/B` of a crystal in
`𝒪_{X/S}`-modules.

The site-generic components — that localising a site at its greatest object does not change the
sheaves of modules over a sheaf of rings, and the two criteria for a morphism into such a
localisation to be invertible — are imported from the big site's file and reused verbatim.  The
construction itself is repeated because a sheaf of modules on `Cris(X/S)` is in general not the
restriction of one on `CRIS(X/S)`; the ring level, on the other hand, *is* the big site's at the
underlying objects, so the `f`-map of the restricted structure sheaves is formed over the big
site's `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap` of the
underlying morphism.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientSelfFunctor` —
  the ambient restrictions of the base of a localised small crystalline site, named through the
  base rather than through its identity arrow.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.ambientOpensOverFunctor` — the preimage functor on the localised opens of the two ambient
  schemes.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverFMap` — the
  `f`-map `ρ_B(F) ⟶ g_* ρ_X(F)` of the ambient restrictions.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverComparison` —
  its transpose `g^* ρ_B(F) ⟶ ρ_X(F)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isIso_ambientOverComparison_app_over` — the comparison is invertible at the restriction of a
  crystal in `𝒪_{X/S}`-modules, packaged as `CrystallineThickening.ambientOverComparisonIso`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.ambientOverComparison_naturality` — the comparison is compatible with every morphism of
  sheaves of modules on `Cris(X/S)/B`, so that at crystals the ambient restriction at `X` of a
  morphism is the `g`-pullback of its ambient restriction at the base
  (`CrystallineThickening.pushforward_ambientOverStructureHom_map_over_eq`).

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} (B : CrystallineThickening S) (X : Over B)

/-- **The restrictions of a morphism of `Cris(X/S)` over the opens of the ambient scheme of its
target are compatible with further restriction**, being so in `CRIS(X/S)`. -/
@[reassoc]
theorem restrictOpenLE_restrictOpenMap {A A' : CrystallineThickening S} (g : A ⟶ A')
    {V V' : A'.obj.thickening.target.scheme.Opens} (h : V ≤ V') :
    restrictOpenLE A (g.hom.targetHom.hom.preimage_mono h) ≫ restrictOpenMap g V' =
      restrictOpenMap g V ≫ restrictOpenLE A' h :=
  ObjectProperty.hom_ext (Thickening.IsCrystalline (S := S))
    (Thickening.restrictOpenLE_restrictOpenMap g.hom h)

/-- **The preimage functor on the opens of the ambient schemes of an object of a localised small
crystalline site and of its base**, localised at the greatest opens of the two schemes. -/
noncomputable def ambientOpensOverFunctor :
    Over (⊤ : B.obj.thickening.target.scheme.Opens) ⥤
      Over (⊤ : X.left.obj.thickening.target.scheme.Opens) :=
  Over.post (X := (⊤ : B.obj.thickening.target.scheme.Opens))
      (Opens.map X.hom.hom.targetHom.hom.base) ⋙
    Over.map (homOfLE (le_top :
      (Opens.map X.hom.hom.targetHom.hom.base).obj
        (⊤ : B.obj.thickening.target.scheme.Opens) ≤ ⊤))

/-- The preimage functor on the opens of the two ambient schemes is continuous for the localised
Zariski topologies at the preimage of the greatest open, preimage of opens preserving finite
limits and covers. -/
instance isContinuous_overPost_ambientOpensMap :
    (Over.post (X := (⊤ : B.obj.thickening.target.scheme.Opens))
        (Opens.map X.hom.hom.targetHom.hom.base)).IsContinuous
      ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
      ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over
        ((Opens.map X.hom.hom.targetHom.hom.base).obj
          (⊤ : B.obj.thickening.target.scheme.Opens))) := by
  have : PreservesFiniteLimits (Opens.map X.hom.hom.targetHom.hom.base) :=
    preservesFiniteLimits_of_flat _
  have : (Opens.map X.hom.hom.targetHom.hom.base).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥B.obj.thickening.target.scheme)
      (Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (coverPreserving_opens_map X.hom.hom.targetHom.hom.base)
  infer_instance

/-- The preimage functor on the localised opens is continuous, being the preimage of opens
followed by `CategoryTheory.Over.map` of the inclusion of the preimage of the greatest open. -/
instance isContinuous_ambientOpensOverFunctor :
    (ambientOpensOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
      ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over ⊤) :=
  Functor.isContinuous_comp
    (Over.post (X := (⊤ : B.obj.thickening.target.scheme.Opens))
      (Opens.map X.hom.hom.targetHom.hom.base))
    (Over.map (homOfLE (le_top :
      (Opens.map X.hom.hom.targetHom.hom.base).obj
        (⊤ : B.obj.thickening.target.scheme.Opens) ≤ ⊤)))
    ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
    ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over
      ((Opens.map X.hom.hom.targetHom.hom.base).obj
        (⊤ : B.obj.thickening.target.scheme.Opens)))
    ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over ⊤)

/-- The structure morphism of the image of an open of the ambient scheme under an ambient
restriction: the restriction to that open, followed by the structure morphism of the object. -/
@[simp]
theorem ambientOverFunctor_obj_hom (Y : Over B)
    (W : Over (⊤ : Y.left.obj.thickening.target.scheme.Opens)) :
    ((ambientOverFunctor B Y).obj W).hom =
      restrictOpenLE Y.left (leOfHom W.hom) ≫ Y.left.restrictOpenHom ⊤ ≫ Y.hom := rfl

/-- An ambient restriction carries an inclusion of opens to the corresponding further
restriction. -/
@[simp]
theorem ambientOverFunctor_map_left (Y : Over B)
    {W W' : Over (⊤ : Y.left.obj.thickening.target.scheme.Opens)} (k : W ⟶ W') :
    ((ambientOverFunctor B Y).map k).left = restrictOpenLE Y.left (leOfHom k.left) := rfl

/-- The preimage functor on the localised opens is the preimage of opens. -/
@[simp]
theorem ambientOpensOverFunctor_obj_left (V : Over (⊤ : B.obj.thickening.target.scheme.Opens)) :
    ((ambientOpensOverFunctor B X).obj V).left = X.hom.hom.targetHom.hom ⁻¹ᵁ V.left := rfl

/-- **The ambient restrictions of the base object of a localised small crystalline site**, named
through the base rather than through its identity arrow. -/
noncomputable def ambientSelfFunctor :
    Over (⊤ : B.obj.thickening.target.scheme.Opens) ⥤ Over B :=
  ambientOverFunctor B (Over.mk (𝟙 B))

/-- The ambient restrictions of the base object are the ambient restrictions at its identity
arrow, on the nose. -/
theorem ambientSelfFunctor_eq (B : CrystallineThickening S) :
    ambientSelfFunctor B = ambientOverFunctor B (Over.mk (𝟙 B)) := rfl

/-- The ambient restrictions of the base object are continuous. -/
instance isContinuous_ambientSelfFunctor :
    (ambientSelfFunctor B).IsContinuous
      ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
      ((smallTopology S).over B) :=
  isContinuous_ambientOverFunctor B (Over.mk (𝟙 B))

/-- **The restrictions of the structure morphism of an object of a localised small crystalline
site over the opens of the ambient scheme of the base**, as a natural transformation of functors
of sites into that localised site: over an open `W` of the ambient scheme of the base it is the
restriction `(U ∩ g⁻¹W, g⁻¹W, δ|) ⟶ (U' ∩ W, W, δ'|)` of the structure morphism. -/
noncomputable def ambientOverRestrictionMap (B : CrystallineThickening S) (X : Over B) :
    ambientOpensOverFunctor B X ⋙ ambientOverFunctor B X ⟶ ambientSelfFunctor B where
  app V := Over.homMk (restrictOpenMap X.hom V.left) (by
    have h1 : restrictOpenMap X.hom V.left ≫
          (restrictOpenLE B (leOfHom V.hom) ≫ B.restrictOpenHom ⊤ ≫ 𝟙 B) =
        X.left.restrictOpenHom (X.hom.hom.targetHom.hom ⁻¹ᵁ V.left) ≫ X.hom := by
      rw [Category.comp_id, restrictOpenLE_restrictOpenHom, restrictOpenMap_restrictOpenHom]
    have h2 : restrictOpenLE X.left
          (le_top : X.hom.hom.targetHom.hom ⁻¹ᵁ V.left ≤ ⊤) ≫
            X.left.restrictOpenHom ⊤ ≫ X.hom =
        X.left.restrictOpenHom (X.hom.hom.targetHom.hom ⁻¹ᵁ V.left) ≫ X.hom := by
      rw [restrictOpenLE_restrictOpenHom_assoc]
    exact h1.trans h2.symm)
  naturality V V' i :=
    Over.OverMorphism.ext (restrictOpenLE_restrictOpenMap X.hom (leOfHom i.left))

/-- The preimage functor on the localised opens followed by the ambient restrictions of an object
is continuous. -/
instance isContinuous_ambientOpensOverFunctor_comp :
    (ambientOpensOverFunctor B X ⋙ ambientOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
      ((smallTopology S).over B) :=
  Functor.isContinuous_comp (ambientOpensOverFunctor B X) (ambientOverFunctor B X)
    ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
    ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over ⊤)
    ((smallTopology S).over B)

/-- **The comparison of structure sheaves along the ambient restrictions of the base object**,
which is again the identity, named through the base rather than through its identity arrow. -/
noncomputable def ambientOverSelfStructureHom :
    (Thickening.ringRestrictionSheaf B.obj).over ⊤ ⟶
      ((ambientSelfFunctor B).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
        ((smallTopology S).over B)).obj ((structureSheaf S).over B) :=
  𝟙 _

/-- The comparison of structure sheaves along the ambient restrictions of the base object is
invertible, being the identity. -/
instance isIso_ambientOverSelfStructureHom (B : CrystallineThickening S) :
    IsIso (ambientOverSelfStructureHom B) :=
  inferInstanceAs (IsIso (𝟙 ((Thickening.ringRestrictionSheaf B.obj).over ⊤)))

/-- The comparison of structure sheaves along the ambient restrictions of the base object is the
comparison at its identity arrow, on the nose. -/
theorem ambientOverSelfStructureHom_eq (B : CrystallineThickening S) :
    ambientOverSelfStructureHom B = ambientOverStructureHom B (Over.mk (𝟙 B)) := rfl

/-- **The `f`-map of the restricted structure sheaves along the preimage functor on the localised
opens.**  Over an open `W` of the ambient scheme of the base it is the restriction map of
`𝒪_{X/S}` along the restriction of the structure morphism over `W`. -/
noncomputable def ambientOpensOverRingHom :
    (Thickening.ringRestrictionSheaf B.obj).over ⊤ ⟶
      ((ambientOpensOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
          ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over ⊤)).obj
        ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) :=
  (Functor.sheafPushforwardContinuousNatTrans (ambientOverRestrictionMap B X) RingCat.{u}
    ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
    ((smallTopology S).over B)).app ((structureSheaf S).over B)

/-- **The `f`-map of the restricted structure sheaves is compatible with the two comparisons of
structure sheaves along the ambient restrictions.**  Both comparisons are identity morphisms. -/
theorem ambientOpensOverRingHom_comp :
    ambientOverSelfStructureHom B ≫
        (Functor.sheafPushforwardContinuousNatTrans (ambientOverRestrictionMap B X) RingCat.{u}
          ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
          ((smallTopology S).over B)).app ((structureSheaf S).over B) =
      ambientOpensOverRingHom B X ≫
        ((ambientOpensOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥B.obj.thickening.target.scheme).over ⊤)
          ((Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme).over ⊤)).map
            (ambientOverStructureHom B X) := rfl

/-- Pushforward of sheaves of modules along the `f`-map of the restricted structure sheaves on the
localised opens has a left adjoint, the sites and the sheaves of rings living in a single
universe. -/
instance isRightAdjoint_pushforward_ambientOpensOverRingHom
    (B : CrystallineThickening S) (X : Over B) :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).IsRightAdjoint := by
  have : (PresheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X).hom).IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward.{u}
      (show ((Thickening.ringRestrictionSheaf B.obj).over ⊤).obj ⟶
          (ambientOpensOverFunctor B X).op ⋙
            ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤).obj from
        (ambientOpensOverRingHom B X).hom)).IsRightAdjoint
  infer_instance

/-- **The `f`-map `ρ_B(F) ⟶ g_* ρ_X(F)` of the ambient restrictions of a localised small
crystalline site**, natural in the sheaf of `𝒪_{X/S}`-modules `F`. -/
noncomputable def ambientOverFMap (B : CrystallineThickening S) (X : Over B) :
    SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B) ⟶
      SheafOfModules.pushforward.{u} (ambientOverStructureHom B X) ⋙
        SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X) :=
  SheafOfModules.pushforwardNatTrans (ambientOverSelfStructureHom B)
      (ambientOverRestrictionMap B X) ≫
    (SheafOfModules.pushforwardCongr (ambientOpensOverRingHom_comp B X)).hom ≫
      (SheafOfModules.pushforwardComp (ambientOpensOverRingHom B X)
        (ambientOverStructureHom B X)).inv

/-- **The comparison `g^* ρ_B(F) ⟶ ρ_X(F)` of the ambient restrictions of a localised small
crystalline site**, natural in the sheaf of `𝒪_{X/S}`-modules `F`: the transpose of the `f`-map
along the adjunction between pullback and pushforward of sheaves of modules over the `f`-map of
the restricted structure sheaves. -/
noncomputable def ambientOverComparison (B : CrystallineThickening S) (X : Over B) :
    SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B) ⋙
        SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X) ⟶
      SheafOfModules.pushforward.{u} (ambientOverStructureHom B X) :=
  Functor.whiskerRight (ambientOverFMap B X)
      (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)) ≫
    Functor.whiskerLeft (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X))
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (ambientOpensOverRingHom B X)).counit

/-- On sections the `f`-map of the ambient restrictions is restriction of the module along the
restriction of the structure morphism over the open in question. -/
@[simp]
theorem ambientOverFMap_app_val_app
    (Z : SheafOfModules.{u} ((structureSheaf S).over B))
    (V : (Over (⊤ : B.obj.thickening.target.scheme.Opens))ᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj Z).val.obj V) :
    ((ambientOverFMap B X).app Z).val.app V x =
      Z.val.map ((ambientOverRestrictionMap B X).app V.unop).op x := rfl

/-- **The comparison of the ambient restrictions is the transpose of their `f`-map**, at every
module. -/
theorem ambientOverComparison_app (Z : SheafOfModules.{u} ((structureSheaf S).over B)) :
    (ambientOverComparison B X).app Z =
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ambientOpensOverRingHom B X)).homEquiv
        ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj Z)
        ((SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj Z)).symm
          ((ambientOverFMap B X).app Z) :=
    by rw [Adjunction.homEquiv_counit]; rfl

/-- **The `f`-map of the ambient restrictions is the transpose of their comparison**, at every
module. -/
theorem homEquiv_ambientOverComparison_app
    (Z : SheafOfModules.{u} ((structureSheaf S).over B)) :
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (ambientOpensOverRingHom B X)).homEquiv
      ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj Z)
      ((SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj Z))
        ((ambientOverComparison B X).app Z) = (ambientOverFMap B X).app Z := by
  rw [ambientOverComparison_app, Equiv.apply_symm_apply]

/-- The ambient restriction of a module restricted from the whole small crystalline site is the
restriction `F_T` of [Stacks, Tag 07IQ], localised at the greatest open. -/
theorem pushforward_ambientOverStructureHom_obj_over
    (M : SheafOfModules.{u} (structureSheaf S)) :
    (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj (M.over B) =
      (moduleRestrictionSheaf M X.left).over ⊤ := rfl

/-- The ambient restriction of the base object of a module restricted from the whole small
crystalline site is the restriction `F_{T'}` of [Stacks, Tag 07IQ], localised at the greatest
open. -/
theorem pushforward_ambientOverSelfStructureHom_obj_over
    (M : SheafOfModules.{u} (structureSheaf S)) :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj (M.over B) =
      (moduleRestrictionSheaf M B).over ⊤ := rfl

/-- **Pushforward of sheaves of modules along the preimage functor commutes with localisation at
the greatest opens**, on the nose. -/
theorem pushforward_ambientOpensOverRingHom_obj_over
    (N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)) :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).obj (N.over ⊤) =
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap X.hom.hom)).obj N).over ⊤ := rfl

/-- **Pushforward of sheaves of modules along the preimage functor commutes with localisation at
the greatest opens**, on morphisms as well as on objects. -/
theorem pushforward_ambientOpensOverRingHom_map_over
    {N N' : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)} (k : N ⟶ N') :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤) =
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap X.hom.hom)).map k).over ⊤ := rfl

/-- **The `f`-map of a crystal on the small site is universal**: for every sheaf of
`𝒪_T`-modules `N`, every morphism `F_{T'} ⟶ g_* N` is uniquely the `f`-map followed by the
pushforward of a morphism `F_T ⟶ N`.  This is the comparison map of [Stacks, Tag 07IQ] being
invertible, read through the adjunction between pullback and pushforward. -/
theorem bijective_comp_moduleFMapSheaf (M : SheafOfModules.{u} (structureSheaf S))
    {A₀ B₀ : CrystallineThickening S} (g : A₀ ⟶ B₀) (hg : IsIso (moduleComparisonSheaf M g))
    (N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A₀.obj)) :
    Function.Bijective (fun k : moduleRestrictionSheaf M A₀ ⟶ N ↦
      moduleFMapSheaf M g ≫
        (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map k) := by
  have hb := (isIso_iff_coyoneda_map_bijective (moduleComparisonSheaf M g)).1 hg N
  have he : (fun k : moduleRestrictionSheaf M A₀ ⟶ N ↦
        moduleFMapSheaf M g ≫
          (SheafOfModules.pushforward.{u}
            (Thickening.ringRestrictionSheafFMap g.hom)).map k) =
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
        (moduleRestrictionSheaf M B₀) N) ∘ (fun k ↦ moduleComparisonSheaf M g ≫ k) := by
    funext k
    simp only [Function.comp_apply]
    rw [Adjunction.homEquiv_naturality_right, ← moduleFMapSheaf_eq_moduleComparisonSheaf]
  rw [he]
  exact Function.Bijective.comp (Equiv.bijective _) hb

/-- **At a module restricted from the whole small crystalline site, the `f`-map of the ambient
restrictions is the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ]**, localised at the greatest
opens. -/
theorem ambientOverFMap_app_over (M : SheafOfModules.{u} (structureSheaf S)) :
    (ambientOverFMap B X).app (M.over B) = (moduleFMapSheaf M X.hom).over ⊤ := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- The ambient restriction of the base object carries the structure sheaf of the localised small
crystalline site to the structure sheaf of the Zariski site of the ambient scheme. -/
theorem pushforward_ambientOverSelfStructureHom_obj_unit :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj
        (SheafOfModules.unit ((structureSheaf S).over B)) =
      SheafOfModules.unit ((Thickening.ringRestrictionSheaf B.obj).over ⊤) := rfl

/-- **At the structure sheaf the `f`-map of the ambient restrictions is Mathlib's canonical map
from the unit to the pushforward of the unit**, both being the `f`-map of the restricted structure
sheaves read on the unit modules. -/
theorem ambientOverFMap_app_unit :
    (ambientOverFMap B X).app (SheafOfModules.unit ((structureSheaf S).over B)) =
      SheafOfModules.unitToPushforwardObjUnit (ambientOpensOverRingHom B X) := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- **The preimage functor on the localised opens is final.**  The structured arrow category at a
localised open of the ambient scheme of the object has the greatest open of the ambient scheme of
the base as a terminal object. -/
instance final_ambientOpensOverFunctor (B : CrystallineThickening S) (X : Over B) :
    (ambientOpensOverFunctor B X).Final where
  out V := isConnected_of_isTerminal _ (IsTerminal.ofUniqueHom
    (X := StructuredArrow.mk (Y := Over.mk (𝟙 (⊤ : B.obj.thickening.target.scheme.Opens)))
      (show V ⟶ (ambientOpensOverFunctor B X).obj
          (Over.mk (𝟙 (⊤ : B.obj.thickening.target.scheme.Opens))) from
        Over.homMk (homOfLE le_top) (Subsingleton.elim _ _)))
    (fun _ ↦ StructuredArrow.homMk (Over.homMk (homOfLE le_top) (Subsingleton.elim _ _))
      (Over.OverMorphism.ext (Subsingleton.elim _ _)))
    (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Subsingleton.elim _ _))))

/-- **The comparison of the ambient restrictions is an isomorphism at `F = 𝒪_{X/S}`.**  There it
is Mathlib's canonical map from the pullback of the unit to the unit, which is invertible because
the preimage functor on the localised opens is final. -/
theorem isIso_ambientOverComparison_app_unit :
    IsIso ((ambientOverComparison B X).app
      (SheafOfModules.unit ((structureSheaf S).over B))) := by
  rw [ambientOverComparison_app, ambientOverFMap_app_unit]
  exact inferInstanceAs
    (IsIso (SheafOfModules.pullbackObjUnitToUnit (ambientOpensOverRingHom B X)))

/-- **The `f`-map of the ambient restrictions followed by the pushforward of a restricted morphism
out of `F_T` is the localisation of the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ] followed
by the pushforward of that morphism.**  This is the one place where the two spellings of the
pushforward along
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOpensOverRingHom`
of a localisation are bridged; the bridge is made at the level of sections rather than left to
unification. -/
theorem ambientOverFMap_app_over_comp (M : SheafOfModules.{u} (structureSheaf S))
    (N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj))
    (k : moduleRestrictionSheaf M X.left ⟶ N) :
    (ambientOverFMap B X).app (M.over B) ≫
        (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤) =
      (moduleFMapSheaf M X.hom ≫
        (SheafOfModules.pushforward.{u}
          (Thickening.ringRestrictionSheafFMap X.hom.hom)).map k).over ⊤ := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.ambientOverFMap_app_over_comp` read as an equality of the two functions of the morphism `k`. -/
theorem comp_ambientOverFMap_app_over_eq (M : SheafOfModules.{u} (structureSheaf S))
    (N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)) :
    (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
        (ambientOverFMap B X).app (M.over B) ≫
          (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤)) =
      (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
        (moduleFMapSheaf M X.hom ≫
            (SheafOfModules.pushforward.{u}
              (Thickening.ringRestrictionSheafFMap X.hom.hom)).map k).over
          (⊤ : B.obj.thickening.target.scheme.Opens)) :=
  funext fun k ↦ ambientOverFMap_app_over_comp B X M N k

/-- **At the restriction of a crystal in `𝒪_{X/S}`-modules, the `f`-map of the ambient
restrictions is universal.**  The crystal condition of [Stacks, Tag 07IS] gives this on the
unlocalised Zariski site, and localisation at the greatest open is bijective on morphisms. -/
theorem bijective_comp_ambientOverFMap_app_over
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M)
    (N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)) :
    Function.Bijective (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
      (ambientOverFMap B X).app (M.over B) ≫
        (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤)) := by
  rw [comp_ambientOverFMap_app_over_eq B X M N]
  exact (Stacks.ModuleSliceTop.bijective_hom_over
      (Opens.grothendieckTopology ↥B.obj.thickening.target.scheme)
      (Thickening.ringRestrictionSheaf B.obj)
      (moduleRestrictionSheaf M B)
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap X.hom.hom)).obj N)).comp
    (bijective_comp_moduleFMapSheaf M X.hom (hM _ _ X.hom) N)

/-- **The comparison of the ambient restrictions is an isomorphism at a module restricted from a
crystal in `𝒪_{X/S}`-modules**, on the small crystalline site.  At `F.over B` the `f`-map of the
ambient restrictions is the localisation of the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ]
and the comparison is its transpose; the crystal condition of [Stacks, Tag 07IS] says exactly
that composing that `f`-map with the pushforward of a morphism out of `F_T` is bijective on those
morphisms. -/
theorem isIso_ambientOverComparison_app_over
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M) :
    IsIso ((ambientOverComparison B X).app (M.over B)) :=
  Stacks.ModuleSliceTop.isIso_of_bijective_comp_homEquiv
    (Opens.grothendieckTopology ↥X.left.obj.thickening.target.scheme)
    (Thickening.ringRestrictionSheaf X.left.obj)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ambientOpensOverRingHom B X))
    (Q := moduleRestrictionSheaf M X.left)
    ((ambientOverFMap B X).app (M.over B))
    (homEquiv_ambientOverComparison_app B X (M.over B))
    (bijective_comp_ambientOverFMap_app_over B X hM)

/-- **The ambient restriction at `X` of a module restricted from a crystal in `𝒪_{X/S}`-modules is
the `g`-pullback of its ambient restriction at the base**, the isomorphism being the comparison of
the ambient restrictions. -/
noncomputable def ambientOverComparisonIso
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M) :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B) ⋙
          SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).obj (M.over B) ≅
      (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj (M.over B) :=
  haveI := isIso_ambientOverComparison_app_over B X hM
  asIso ((ambientOverComparison B X).app (M.over B))

/-- The isomorphism of ambient restrictions at a crystal is the comparison of the ambient
restrictions. -/
@[simp]
theorem ambientOverComparisonIso_hom
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M) :
    (ambientOverComparisonIso B X hM).hom = (ambientOverComparison B X).app (M.over B) := rfl

/-- **The comparison of the ambient restrictions is compatible with every morphism of sheaves of
modules on the localised small crystalline site**: the ambient restriction at `X` of a morphism,
read through the comparison, is the `g`-pullback of its ambient restriction at the base.  Applied
to the two maps `a` and `b` of a presentation this says that their ambient restrictions at `X` are
the `g`-pullbacks of their ambient restrictions at the base. -/
theorem ambientOverComparison_naturality
    {Z Z' : SheafOfModules.{u} ((structureSheaf S).over B)} (φ : Z ⟶ Z') :
    (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).map
          ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).map φ) ≫
        (ambientOverComparison B X).app Z' =
      (ambientOverComparison B X).app Z ≫
        (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).map φ :=
  (ambientOverComparison B X).naturality φ

/-- **The isomorphisms of ambient restrictions at two crystals intertwine the ambient restriction
at `X` of a morphism with the `g`-pullback of its ambient restriction at the base.** -/
theorem ambientOverComparisonIso_hom_comp_pushforward_map
    {M M' : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M)
    (hM' : IsSheafCrystal M') (φ : M.over B ⟶ M'.over B) :
    (ambientOverComparisonIso B X hM).hom ≫
        (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).map φ =
      (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).map
          ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).map φ) ≫
        (ambientOverComparisonIso B X hM').hom :=
  (ambientOverComparison_naturality B X φ).symm

/-- **The ambient restriction at `X` of a morphism of restrictions of crystals is the
`g`-pullback of its ambient restriction at the base**, conjugated by the comparisons of the
ambient restrictions. -/
theorem pushforward_ambientOverStructureHom_map_over_eq
    {M M' : SheafOfModules.{u} (structureSheaf S)} (hM : IsSheafCrystal M)
    (hM' : IsSheafCrystal M') (φ : M.over B ⟶ M'.over B) :
    (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).map φ =
      (ambientOverComparisonIso B X hM).inv ≫
        (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).map
            ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).map φ) ≫
          (ambientOverComparisonIso B X hM').hom := by
  refine Eq.symm ?_
  rw [Iso.inv_comp_eq]
  exact (ambientOverComparisonIso_hom_comp_pushforward_map B X hM hM' φ).symm

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end
