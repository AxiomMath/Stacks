module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonSections

/-!
# The ambient restrictions of a localised crystalline site compare with those of its base

Let `(U', T', δ')` be an object `B` of the big crystalline site `CRIS(X/S)` and let
`X = (g : (U, T, δ) ⟶ B)` be an object of the localised site `CRIS(X/S)/B`.  Restriction of a
sheaf of modules on `CRIS(X/S)/B` along the ambient restriction
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctor` of `X` is the Zariski
sheaf `ρ_X(F)` on the ambient scheme `T` of `X`, and along the ambient restriction of the base —
named here through `B` itself rather than through its identity arrow — it is the Zariski sheaf
`ρ_B(F)` on the ambient scheme `T'` of `B`.  The two are compared by

* `Thickening.ambientOverFMap`, the `f`-map `ρ_B(F) ⟶ g_* ρ_X(F)`, and
* `Thickening.ambientOverComparison`, its transpose `g^* ρ_B(F) ⟶ ρ_X(F)`,

both natural in `F`.  The transposition is along the adjunction between pullback and pushforward
of sheaves of modules over `Thickening.ambientOpensOverRingHom`, the `f`-map of the restricted
structure sheaves taken on the localised Zariski sites — the slices of the opens of `T` and of
`T'` at their greatest elements, which carry the same sheaves of modules as the unlocalised sites
because the greatest element of a lattice is terminal (`Stacks.ModuleSliceTop.equivalence`).

The comparison is invertible at `F = 𝒪_{X/S}` (`Thickening.isIso_ambientOverComparison_app_unit`,
because the preimage functor on the localised opens is final) and, more to the point, at the
restriction to `CRIS(X/S)/B` of a *crystal* in `𝒪_{X/S}`-modules
(`Thickening.isIso_ambientOverComparison_app_over`): there `ρ_B` and `ρ_X` are the restrictions
`F_{T'}` and `F_T` of [Stacks, Tag 07IQ] and the comparison is the comparison map of that tag,
which the crystal condition of [Stacks, Tag 07IS] asks to be invertible.  Being a natural
transformation, the comparison is compatible with any morphism of sheaves of modules on
`CRIS(X/S)/B` (`Thickening.ambientOverComparison_naturality`); applied to the two maps of a
presentation this says that the ambient restrictions at `X` of those maps are the `g`-pullbacks of
their ambient restrictions at the base, which is what the step (2) ⇒ (1) of
[Stacks, Tag 07IT] needs in order to see a lifted presentation restrict to a presentation at every
object of the localised site.

## Main results

* `Stacks.ModuleSliceTop.equivalence` — localising a site at its greatest object does not change
  the sheaves of modules over a sheaf of rings.
* `Stacks.ModuleSliceTop.isIso_of_bijective_comp_over` — a morphism into a restriction to the
  slice at the greatest object is invertible as soon as composing with it is bijective on the
  restrictions of the morphisms out of the unlocalised object.
* `Stacks.ModuleSliceTop.isIso_of_bijective_comp_homEquiv` — the same criterion for a transpose
  along an adjunction, in terms of the transposed composition.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFMap` and
  `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverComparison` — the `f`-map and its
  transpose for the ambient restrictions of an object of a localised crystalline site.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_ambientOverComparison_app_over` — the
  comparison is invertible at the restriction of a crystal in `𝒪_{X/S}`-modules, packaged as
  `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverComparisonIso`.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverComparison_naturality` and
  `Thickening.pushforward_ambientOverStructureHom_map_over_eq` — the comparison is compatible with
  the morphisms of `CRIS(X/S)/B`, so that at crystals the ambient restriction at `X` of a morphism
  is the `g`-pullback of its ambient restriction at the base.

## Implementation notes

The ambient restrictions of the base are named through `B` itself,
`Thickening.ambientSelfFunctor B = Thickening.ambientOverFunctor B (Over.mk (𝟙 B))`, so that the
`f`-map and the comparison are natural transformations of functors indexed by a single object of
the localised site; `Thickening.ambientOverSelfStructureHom_eq` and
`Thickening.ambientSelfFunctor_eq` record that this is the ambient restriction at the identity
arrow on the nose.

Two spellings of the same sheaf of modules occur throughout: the pushforward along
`Thickening.ambientOpensOverRingHom` of a localisation, and the localisation of a pushforward along
`Thickening.ringRestrictionSheafFMap` (identified, definitionally, by
`Thickening.pushforward_ambientOpensOverRingHom_obj_over` and
`Thickening.pushforward_ambientOpensOverRingHom_map_over`).  The
identifications are definitional but *expensive* to see between two already-elaborated terms, so
the bridge between the two spellings is made once, propositionally and at the level of sections, in
`Thickening.ambientOverFMap_app_over_comp`, and everything downstream rewrites with it rather than
leaving it to unification; `Stacks.ModuleSliceTop.isIso_of_bijective_comp_homEquiv` is stated with
the adjunction abstract for the same reason.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u₁ v₁ u

/-- A function that is pointwise a bijection followed by a bijection is bijective. -/
private theorem bijective_of_forall_eq_comp {α β γ : Type*} {e : β → γ} {g : α → β} {f : α → γ}
    (he : Function.Bijective e) (hg : Function.Bijective g) (h : ∀ a, f a = e (g a)) :
    Function.Bijective f := by
  obtain rfl : f = e ∘ g := funext h
  exact he.comp hg

namespace Stacks.ModuleSliceTop

variable {C : Type u} [SemilatticeInf C] [OrderTop C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u})

/-- **The slice of a site at its greatest object is the site itself**, the greatest object of a
lattice being terminal. -/
noncomputable def siteEquivalence : Over (⊤ : C) ≌ C :=
  Over.equivalenceOfIsTerminal isTerminalTop

/-- The functor of `Stacks.ModuleSliceTop.siteEquivalence` is the forgetful functor of the
slice. -/
theorem siteEquivalence_functor :
    (siteEquivalence (C := C)).functor = Over.forget (⊤ : C) := rfl

/-- The functor of `Stacks.ModuleSliceTop.siteEquivalence` is continuous. -/
instance isContinuous_siteEquivalence_functor :
    (siteEquivalence (C := C)).functor.IsContinuous (J.over ⊤) J :=
  inferInstanceAs ((Over.forget (⊤ : C)).IsContinuous (J.over ⊤) J)

/-- The inverse of `Stacks.ModuleSliceTop.siteEquivalence` is continuous. -/
instance isContinuous_siteEquivalence_inverse :
    (siteEquivalence (C := C)).inverse.IsContinuous J (J.over ⊤) :=
  Functor.isContinuous_of_iso
    ((Over.forgetAdjStar (⊤ : C)).rightAdjointUniq (siteEquivalence (C := C)).toAdjunction)
    J (J.over ⊤)

/-- The counit of `Stacks.ModuleSliceTop.siteEquivalence` is the identity at every object. -/
theorem siteEquivalence_counit_app (U : C) : (siteEquivalence (C := C)).counit.app U = 𝟙 U :=
  Subsingleton.elim _ _

/-- The unit of `Stacks.ModuleSliceTop.siteEquivalence` is the identity at every object. -/
theorem siteEquivalence_unit_app (Y : Over (⊤ : C)) :
    (siteEquivalence (C := C)).unit.app Y = 𝟙 Y :=
  Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- **Localising a site at its greatest object does not change the sheaves of modules over a
sheaf of rings.**  The slice at a terminal object is equivalent to the site, and the two
restrictions of the sheaf of rings along the two directions of that equivalence are the sheaf of
rings itself. -/
noncomputable def equivalence :
    _root_.SheafOfModules.{u} R ≌ _root_.SheafOfModules.{u} (R.over ⊤) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (R := R) (S := R.over ⊤)
    (siteEquivalence (C := C)) (𝟙 _) (𝟙 _)
    (by ext U : 2; exact R.obj.map_id _)
    (by ext Y : 2; exact (R.over (⊤ : C)).obj.map_id _)

/-- The functor of `Stacks.ModuleSliceTop.equivalence` is restriction of sheaves of modules to the
slice at the greatest object. -/
theorem equivalence_functor :
    (equivalence J R).functor = _root_.SheafOfModules.overFunctor R ⊤ := rfl

/-- **Restriction of sheaves of modules to the slice of the site at its greatest object is an
equivalence.** -/
theorem isEquivalence_overFunctor_top :
    ((_root_.SheafOfModules.overFunctor R (⊤ : C)) :
      _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} (R.over ⊤)).IsEquivalence :=
  (equivalence J R).isEquivalence_functor

/-- Postcomposition with an isomorphism is bijective on morphisms out of a fixed object. -/
theorem bijective_comp_isoHom {C₁ : Type*} [Category C₁] {Y Z : C₁} (e : Y ≅ Z)
    (W : C₁) : Function.Bijective (fun f : W ⟶ Y ↦ f ≫ e.hom) :=
  ⟨fun _ _ hab ↦ by simpa using congrArg (fun t ↦ t ≫ e.inv) hab,
    fun g ↦ ⟨g ≫ e.inv, by simp⟩⟩

/-- **Restriction to the slice at the greatest object is bijective on morphisms.** -/
theorem bijective_hom_over (N N' : _root_.SheafOfModules.{u} R) :
    Function.Bijective (fun f : N ⟶ N' ↦ f.over (⊤ : C)) := by
  have := isEquivalence_overFunctor_top J R
  exact ⟨Functor.map_injective (_root_.SheafOfModules.overFunctor R (⊤ : C)),
    fun y ↦ ⟨(_root_.SheafOfModules.overFunctor R (⊤ : C)).preimage y, by simp⟩⟩

/-- **A morphism into a restriction to the slice at the greatest object is invertible as soon as
composing with it is bijective on the restrictions of the morphisms out of the unlocalised
object.**  Every object of the slice is isomorphic to a restriction, and every morphism out of a
restriction into a restriction is the restriction of a morphism, so the hypothesis gives
bijectivity of composition against every object of the slice. -/
theorem isIso_of_bijective_comp_over {W : _root_.SheafOfModules.{u} (R.over ⊤)}
    {Q : _root_.SheafOfModules.{u} R} {cmp : W ⟶ Q.over (⊤ : C)}
    (h : ∀ N : _root_.SheafOfModules.{u} R,
      Function.Bijective (fun k : Q ⟶ N ↦ cmp ≫ k.over (⊤ : C))) :
    IsIso cmp := by
  have := isEquivalence_overFunctor_top J R
  refine isIso_of_coyoneda_map_bijective _ fun D ↦ ?_
  obtain ⟨D', ι⟩ : Σ' D' : _root_.SheafOfModules.{u} R, (D'.over (⊤ : C)) ≅ D :=
    ⟨_, Functor.objObjPreimageIso _ D⟩
  have hg : Function.Bijective (fun k : Q ⟶ D' ↦ k.over (⊤ : C) ≫ ι.hom) :=
    Function.Bijective.comp
      (g := fun f : Q.over (⊤ : C) ⟶ D'.over (⊤ : C) ↦ f ≫ ι.hom)
      (f := fun k : Q ⟶ D' ↦ k.over (⊤ : C))
      (bijective_comp_isoHom ι _) (bijective_hom_over J R Q D')
  rw [← hg.of_comp_iff]
  exact bijective_of_forall_eq_comp (bijective_comp_isoHom ι _) (h D')
    fun k ↦ (Category.assoc _ _ _).symm

/-- **A transpose along an adjunction into a restriction to the slice at the greatest object is
invertible as soon as the transposed composition is bijective on the restrictions of the morphisms
out of the unlocalised object.**  Transposition is natural in the target, so composing the
transpose of `u` with the restriction of a morphism `k` transposes the composition of `u` with the
right adjoint of that restriction; the hypothesis therefore gives the hypothesis of
`Stacks.ModuleSliceTop.isIso_of_bijective_comp_over`, one bijection being the other followed by an
equivalence. -/
theorem isIso_of_bijective_comp_homEquiv {D₁ : Type u₁} [Category.{v₁} D₁]
    {L : D₁ ⥤ _root_.SheafOfModules.{u} (R.over ⊤)}
    {G : _root_.SheafOfModules.{u} (R.over ⊤) ⥤ D₁} (adj : L ⊣ G)
    {A : D₁} {Q : _root_.SheafOfModules.{u} R} {cmp : L.obj A ⟶ Q.over (⊤ : C)}
    (u : A ⟶ G.obj (Q.over (⊤ : C))) (hu : adj.homEquiv A (Q.over (⊤ : C)) cmp = u)
    (h : ∀ N : _root_.SheafOfModules.{u} R,
      Function.Bijective (fun k : Q ⟶ N ↦ u ≫ G.map (k.over (⊤ : C)))) :
    IsIso cmp := by
  refine isIso_of_bijective_comp_over J R (Q := Q) fun N ↦ ?_
  refine bijective_of_forall_eq_comp (Equiv.bijective (adj.homEquiv A (N.over ⊤)).symm) (h N)
    fun k ↦ ?_
  rw [← hu, Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]

end Stacks.ModuleSliceTop

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} (B : Thickening S) (X : Over B)

/-- **The preimage functor on the opens of the ambient schemes of an object of a localised
crystalline site and of its base**, localised at the greatest opens of the two schemes.  It is
`CategoryTheory.Over.post` of the preimage functor followed by `CategoryTheory.Over.map` of the
inclusion of the preimage of the greatest open. -/
noncomputable def ambientOpensOverFunctor :
    Over (⊤ : B.thickening.target.scheme.Opens) ⥤
      Over (⊤ : X.left.thickening.target.scheme.Opens) :=
  Over.post (X := (⊤ : B.thickening.target.scheme.Opens))
      (Opens.map X.hom.targetHom.hom.base) ⋙
    Over.map (homOfLE (le_top :
      (Opens.map X.hom.targetHom.hom.base).obj (⊤ : B.thickening.target.scheme.Opens) ≤ ⊤))

/-- The functor induced on slices by the preimage functor on the opens of the ambient schemes is
continuous. -/
instance isContinuous_overPost_ambientOpensMap :
    (Over.post (X := (⊤ : B.thickening.target.scheme.Opens))
        (Opens.map X.hom.targetHom.hom.base)).IsContinuous
      ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over
        ((Opens.map X.hom.targetHom.hom.base).obj
          (⊤ : B.thickening.target.scheme.Opens))) := by
  have : PreservesFiniteLimits (Opens.map X.hom.targetHom.hom.base) :=
    preservesFiniteLimits_of_flat _
  have : (Opens.map X.hom.targetHom.hom.base).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥B.thickening.target.scheme)
      (Opens.grothendieckTopology ↥X.left.thickening.target.scheme) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (coverPreserving_opens_map X.hom.targetHom.hom.base)
  infer_instance

/-- The preimage functor on the localised opens of the ambient schemes is continuous. -/
instance isContinuous_ambientOpensOverFunctor :
    (ambientOpensOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤) :=
  Functor.isContinuous_comp
    (Over.post (X := (⊤ : B.thickening.target.scheme.Opens))
      (Opens.map X.hom.targetHom.hom.base))
    (Over.map (homOfLE (le_top :
      (Opens.map X.hom.targetHom.hom.base).obj (⊤ : B.thickening.target.scheme.Opens) ≤ ⊤)))
    ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
    ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over
      ((Opens.map X.hom.targetHom.hom.base).obj (⊤ : B.thickening.target.scheme.Opens)))
    ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)

/-- The structure morphism of the image of an open of the ambient scheme under an ambient
restriction: the restriction to that open, followed by the structure morphism of the object. -/
@[simp]
theorem ambientOverFunctor_obj_hom (Y : Over B)
    (W : Over (⊤ : Y.left.thickening.target.scheme.Opens)) :
    ((ambientOverFunctor B Y).obj W).hom =
      Y.left.restrictOpenLE (leOfHom W.hom) ≫ Y.left.restrictOpenHom ⊤ ≫ Y.hom := rfl

/-- An ambient restriction carries an inclusion of opens to the corresponding further
restriction. -/
@[simp]
theorem ambientOverFunctor_map_left (Y : Over B)
    {W W' : Over (⊤ : Y.left.thickening.target.scheme.Opens)} (k : W ⟶ W') :
    ((ambientOverFunctor B Y).map k).left =
      Y.left.restrictOpenLE (leOfHom k.left) := rfl

/-- The preimage functor on the localised opens is the preimage of opens. -/
@[simp]
theorem ambientOpensOverFunctor_obj_left (V : Over (⊤ : B.thickening.target.scheme.Opens)) :
    ((ambientOpensOverFunctor B X).obj V).left =
      X.hom.targetHom.hom ⁻¹ᵁ V.left := rfl

/-- **The ambient restrictions of the base object of a localised crystalline site**, named
through the base rather than through its identity arrow. -/
noncomputable def ambientSelfFunctor :
    Over (⊤ : B.thickening.target.scheme.Opens) ⥤ Over B :=
  ambientOverFunctor B (Over.mk (𝟙 B))

/-- The ambient restrictions of the base object are the ambient restrictions at its identity
arrow. -/
theorem ambientSelfFunctor_eq (B : Thickening S) :
    ambientSelfFunctor B = ambientOverFunctor B (Over.mk (𝟙 B)) := rfl

/-- The ambient restrictions of the base object form a continuous functor. -/
instance isContinuous_ambientSelfFunctor :
    (ambientSelfFunctor B).IsContinuous
      ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
      ((topology S).over B) :=
  isContinuous_ambientOverFunctor B (Over.mk (𝟙 B))

/-- **The restrictions of the structure morphism of an object of a localised crystalline site
over the opens of the ambient scheme of the base**, as a natural transformation of functors of
sites into that localised site: over an open `W` of the ambient scheme of the base it is the
restriction `(U ∩ g⁻¹W, g⁻¹W, δ|) ⟶ (U' ∩ W, W, δ'|)` of the structure morphism. -/
noncomputable def ambientOverRestrictionMap (B : Thickening S) (X : Over B) :
    ambientOpensOverFunctor B X ⋙ ambientOverFunctor B X ⟶ ambientSelfFunctor B where
  app V := Over.homMk (restrictOpenMap X.hom V.left) (by
    have h1 : restrictOpenMap X.hom V.left ≫
          (B.restrictOpenLE (leOfHom V.hom) ≫ B.restrictOpenHom ⊤ ≫ 𝟙 B) =
        X.left.restrictOpenHom (X.hom.targetHom.hom ⁻¹ᵁ V.left) ≫ X.hom := by
      rw [Category.comp_id, restrictOpenLE_restrictOpenHom, restrictOpenMap_restrictOpenHom]
    have h2 : X.left.restrictOpenLE
          (le_top : X.hom.targetHom.hom ⁻¹ᵁ V.left ≤ ⊤) ≫
            X.left.restrictOpenHom ⊤ ≫ X.hom =
        X.left.restrictOpenHom (X.hom.targetHom.hom ⁻¹ᵁ V.left) ≫ X.hom := by
      rw [restrictOpenLE_restrictOpenHom_assoc]
    exact h1.trans h2.symm)
  naturality V V' i :=
    Over.OverMorphism.ext (restrictOpenLE_restrictOpenMap X.hom (leOfHom i.left))

/-- The preimage functor on the localised opens followed by the ambient restrictions of the object
is continuous. -/
instance isContinuous_ambientOpensOverFunctor_comp :
    (ambientOpensOverFunctor B X ⋙ ambientOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
      ((topology S).over B) :=
  Functor.isContinuous_comp (ambientOpensOverFunctor B X) (ambientOverFunctor B X)
    ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
    ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
    ((topology S).over B)

/-- **The comparison of structure sheaves along the ambient restrictions of the base object**,
which is again the identity, named through the base rather than through its identity arrow. -/
noncomputable def ambientOverSelfStructureHom :
    (B.ringRestrictionSheaf).over ⊤ ⟶
      ((ambientSelfFunctor B).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
        ((topology S).over B)).obj ((crystallineStructureSheaf S).over B) :=
  𝟙 _

/-- The comparison of structure sheaves along the ambient restrictions of the base object is an
isomorphism. -/
instance isIso_ambientOverSelfStructureHom (B : Thickening S) :
    IsIso (ambientOverSelfStructureHom B) :=
  inferInstanceAs (IsIso (𝟙 ((B.ringRestrictionSheaf).over ⊤)))

/-- The comparison of structure sheaves along the ambient restrictions of the base object is the
one at its identity arrow. -/
theorem ambientOverSelfStructureHom_eq (B : Thickening S) :
    ambientOverSelfStructureHom B = ambientOverStructureHom B (Over.mk (𝟙 B)) := rfl

/-- **The `f`-map of the restricted structure sheaves along the preimage functor on the localised
opens.**  Over an open `W` of the ambient scheme of the base it is the restriction map of
`𝒪_{X/S}` along the restriction of the structure morphism over `W`. -/
noncomputable def ambientOpensOverRingHom :
    (B.ringRestrictionSheaf).over ⊤ ⟶
      ((ambientOpensOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
          ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)).obj
        ((X.left.ringRestrictionSheaf).over ⊤) :=
  (Functor.sheafPushforwardContinuousNatTrans (ambientOverRestrictionMap B X) RingCat.{u}
    ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
    ((topology S).over B)).app ((crystallineStructureSheaf S).over B)

/-- **The `f`-map of the restricted structure sheaves is compatible with the two comparisons of
structure sheaves along the ambient restrictions.**  Both comparisons are identity morphisms, and
composition with an identity in `RingCat`, hence componentwise in sheaves of rings, is
definitionally the identity. -/
theorem ambientOpensOverRingHom_comp :
    ambientOverSelfStructureHom B ≫
        (Functor.sheafPushforwardContinuousNatTrans (ambientOverRestrictionMap B X) RingCat.{u}
          ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
          ((topology S).over B)).app ((crystallineStructureSheaf S).over B) =
      ambientOpensOverRingHom B X ≫
        ((ambientOpensOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥B.thickening.target.scheme).over ⊤)
          ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)).map
            (ambientOverStructureHom B X) := rfl

/-- Pushforward of sheaves of modules along the `f`-map of the restricted structure sheaves is a
right adjoint. -/
instance isRightAdjoint_pushforward_ambientOpensOverRingHom (B : Thickening S) (X : Over B) :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).IsRightAdjoint := by
  have : (PresheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X).hom).IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward.{u}
      (show ((B.ringRestrictionSheaf).over ⊤).obj ⟶
          (ambientOpensOverFunctor B X).op ⋙ ((X.left.ringRestrictionSheaf).over ⊤).obj from
        (ambientOpensOverRingHom B X).hom)).IsRightAdjoint
  infer_instance

/-- **The `f`-map `ρ_B(F) ⟶ g_* ρ_X(F)` of the ambient restrictions of a localised crystalline
site**, natural in the sheaf of `𝒪_{X/S}`-modules `F`: it is restriction of sheaves of modules
along the restrictions of the structure morphism over the opens of the ambient scheme of the
base. -/
noncomputable def ambientOverFMap (B : Thickening S) (X : Over B) :
    SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B) ⟶
      SheafOfModules.pushforward.{u} (ambientOverStructureHom B X) ⋙
        SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X) :=
  SheafOfModules.pushforwardNatTrans (ambientOverSelfStructureHom B)
      (ambientOverRestrictionMap B X) ≫
    (SheafOfModules.pushforwardCongr (ambientOpensOverRingHom_comp B X)).hom ≫
      (SheafOfModules.pushforwardComp (ambientOpensOverRingHom B X)
        (ambientOverStructureHom B X)).inv

/-- **The comparison `g^* ρ_B(F) ⟶ ρ_X(F)` of the ambient restrictions of a localised crystalline
site**, natural in the sheaf of `𝒪_{X/S}`-modules `F`: the transpose of the `f`-map along the
adjunction between pullback and pushforward of sheaves of modules over the `f`-map of the
restricted structure sheaves. -/
noncomputable def ambientOverComparison (B : Thickening S) (X : Over B) :
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
    (Z : SheafOfModules.{u} ((crystallineStructureSheaf S).over B))
    (V : (Over (⊤ : B.thickening.target.scheme.Opens))ᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj Z).val.obj V) :
    ((ambientOverFMap B X).app Z).val.app V x =
      Z.val.map ((ambientOverRestrictionMap B X).app V.unop).op x := rfl

/-- **The comparison of the ambient restrictions is the transpose of their `f`-map**, at every
module. -/
theorem ambientOverComparison_app
    (Z : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) :
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
    (Z : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)) :
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (ambientOpensOverRingHom B X)).homEquiv
      ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj Z)
      ((SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj Z))
        ((ambientOverComparison B X).app Z) = (ambientOverFMap B X).app Z := by
  rw [ambientOverComparison_app, Equiv.apply_symm_apply]

/-- The ambient restriction of a module restricted from the whole crystalline site is the
restriction `F_T` of [Stacks, Tag 07IQ], localised at the greatest open. -/
theorem pushforward_ambientOverStructureHom_obj_over
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj (M.over B) =
      (moduleRestrictionSheaf M X.left).over ⊤ := rfl

/-- The ambient restriction of the base object of a module restricted from the whole crystalline
site is the restriction `F_{T'}` of [Stacks, Tag 07IQ], localised at the greatest open. -/
theorem pushforward_ambientOverSelfStructureHom_obj_over
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj (M.over B) =
      (moduleRestrictionSheaf M B).over ⊤ := rfl

/-- **Pushforward of sheaves of modules along the preimage functor commutes with localisation at
the greatest opens**, on the nose. -/
theorem pushforward_ambientOpensOverRingHom_obj_over
    (N : SheafOfModules.{u} (X.left.ringRestrictionSheaf)) :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).obj (N.over ⊤) =
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap X.hom)).obj N).over ⊤ := rfl

/-- **Pushforward of sheaves of modules along the preimage functor commutes with localisation at
the greatest opens**, on morphisms as well as on objects. -/
theorem pushforward_ambientOpensOverRingHom_map_over
    {N N' : SheafOfModules.{u} (X.left.ringRestrictionSheaf)} (k : N ⟶ N') :
    (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤) =
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap X.hom)).map k).over ⊤ := rfl

/-- **The `f`-map of a crystal is universal**: for every sheaf of `𝒪_T`-modules `N`, every
morphism `F_{T'} ⟶ g_* N` is uniquely the `f`-map followed by the pushforward of a morphism
`F_T ⟶ N`.  This is the comparison map of [Stacks, Tag 07IQ] being invertible, read through the
adjunction between pullback and pushforward. -/
theorem bijective_comp_moduleFMapSheaf (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A₀ B₀ : Thickening S} (g : A₀ ⟶ B₀) (hg : IsIso (moduleComparisonSheaf M g))
    (N : SheafOfModules.{u} A₀.ringRestrictionSheaf) :
    Function.Bijective (fun k : moduleRestrictionSheaf M A₀ ⟶ N ↦
      moduleFMapSheaf M g ≫
        (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).map k) := by
  have hb := (isIso_iff_coyoneda_map_bijective (moduleComparisonSheaf M g)).1 hg N
  refine bijective_of_forall_eq_comp
    (Equiv.bijective ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B₀) N)) hb fun k ↦ ?_
  rw [Adjunction.homEquiv_naturality_right, ← moduleFMapSheaf_eq_moduleComparisonSheaf]

/-- **At a module restricted from the whole crystalline site, the `f`-map of the ambient
restrictions is the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ]**, localised at the greatest
opens.  Both are restriction of the module along the restrictions of the structure morphism over
the opens. -/
theorem ambientOverFMap_app_over (M : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (ambientOverFMap B X).app (M.over B) = (moduleFMapSheaf M X.hom).over ⊤ := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- The ambient restriction of the base object carries the structure sheaf of the localised
crystalline site to the structure sheaf of the Zariski site of the ambient scheme. -/
theorem pushforward_ambientOverSelfStructureHom_obj_unit :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).obj
        (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) =
      SheafOfModules.unit ((B.ringRestrictionSheaf).over ⊤) := rfl

/-- The ambient restriction of any object carries the structure sheaf of the localised crystalline
site to the structure sheaf of the Zariski site of its ambient scheme.  The unprimed name carries
the same statement at module universe `u + 1`, for the universe lifts. -/
theorem pushforward_ambientOverStructureHom_obj_unit' :
    (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj
        (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) =
      SheafOfModules.unit ((X.left.ringRestrictionSheaf).over ⊤) := rfl

/-- **At the structure sheaf the `f`-map of the ambient restrictions is Mathlib's canonical map
from the unit to the pushforward of the unit**, both being the `f`-map of the restricted structure
sheaves read on the unit modules. -/
theorem ambientOverFMap_app_unit :
    (ambientOverFMap B X).app (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) =
      SheafOfModules.unitToPushforwardObjUnit (ambientOpensOverRingHom B X) := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- **The preimage functor on the localised opens is final.**  The structured arrow category at a
localised open `V` of the ambient scheme of the object has the greatest open of the ambient scheme
of the base as a terminal object: `V` is contained in its preimage, and the slices of the opens of
a space over an open have at most one morphism between two objects. -/
instance final_ambientOpensOverFunctor (B : Thickening S) (X : Over B) :
    (ambientOpensOverFunctor B X).Final where
  out V := isConnected_of_isTerminal _ (IsTerminal.ofUniqueHom
    (X := StructuredArrow.mk (Y := Over.mk (𝟙 (⊤ : B.thickening.target.scheme.Opens)))
      (show V ⟶ (ambientOpensOverFunctor B X).obj
          (Over.mk (𝟙 (⊤ : B.thickening.target.scheme.Opens))) from
        Over.homMk (homOfLE le_top) (Subsingleton.elim _ _)))
    (fun _ ↦ StructuredArrow.homMk (Over.homMk (homOfLE le_top) (Subsingleton.elim _ _))
      (Over.OverMorphism.ext (Subsingleton.elim _ _)))
    (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Subsingleton.elim _ _))))

/-- **The comparison of the ambient restrictions is an isomorphism at `F = 𝒪_{X/S}`.**  There it
is Mathlib's canonical map from the pullback of the unit to the unit, which is invertible because
the preimage functor on the localised opens is final. -/
theorem isIso_ambientOverComparison_app_unit :
    IsIso ((ambientOverComparison B X).app
      (SheafOfModules.unit ((crystallineStructureSheaf S).over B))) := by
  rw [ambientOverComparison_app, ambientOverFMap_app_unit]
  exact inferInstanceAs
    (IsIso (SheafOfModules.pullbackObjUnitToUnit (ambientOpensOverRingHom B X)))

/-- **The `f`-map of the ambient restrictions followed by the pushforward of a restricted morphism
out of `F_T` is the localisation of the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ] followed
by the pushforward of that morphism.**  Both sides are restriction of the module along the
restrictions of the structure morphism over the opens, followed by the morphism; the localisation
of a composition is the composition of the localisations. -/
theorem ambientOverFMap_app_over_comp (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (N : SheafOfModules.{u} (X.left.ringRestrictionSheaf))
    (k : moduleRestrictionSheaf M X.left ⟶ N) :
    (ambientOverFMap B X).app (M.over B) ≫
        (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤) =
      (moduleFMapSheaf M X.hom ≫
        (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap X.hom)).map k).over ⊤ := by
  refine SheafOfModules.Hom.ext ?_
  ext V
  rfl

/-- `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFMap_app_over_comp` read as an
equality of the two functions of the morphism `k`. -/
theorem comp_ambientOverFMap_app_over_eq
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (N : SheafOfModules.{u} (X.left.ringRestrictionSheaf)) :
    (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
        (ambientOverFMap B X).app (M.over B) ≫
          (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤)) =
      (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
        (moduleFMapSheaf M X.hom ≫
            (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap X.hom)).map k).over
          (⊤ : B.thickening.target.scheme.Opens)) :=
  funext fun k ↦ ambientOverFMap_app_over_comp B X M N k

/-- **At the restriction of a crystal in `𝒪_{X/S}`-modules, the `f`-map of the ambient
restrictions is universal**: for every sheaf of `𝒪_T`-modules `N`, composing the `f`-map with the
pushforward of the restriction to the slice at the greatest open of a morphism `F_T ⟶ N` is
bijective on those morphisms.  The crystal condition of [Stacks, Tag 07IS] gives this on the
unlocalised Zariski site (`bijective_comp_moduleFMapSheaf`), and localisation at the greatest open
is bijective on morphisms (`Stacks.ModuleSliceTop.bijective_hom_over`). -/
theorem bijective_comp_ambientOverFMap_app_over
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M)
    (N : SheafOfModules.{u} (X.left.ringRestrictionSheaf)) :
    Function.Bijective (fun k : moduleRestrictionSheaf M X.left ⟶ N ↦
      (ambientOverFMap B X).app (M.over B) ≫
        (SheafOfModules.pushforward.{u} (ambientOpensOverRingHom B X)).map (k.over ⊤)) := by
  rw [comp_ambientOverFMap_app_over_eq B X M N]
  exact (Stacks.ModuleSliceTop.bijective_hom_over
      (Opens.grothendieckTopology ↥B.thickening.target.scheme) (B.ringRestrictionSheaf)
      (moduleRestrictionSheaf M B)
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap X.hom)).obj N)).comp
    (bijective_comp_moduleFMapSheaf M X.hom (hM _ _ X.hom) N)

/-- **The comparison of the ambient restrictions is an isomorphism at a module restricted from a
crystal in `𝒪_{X/S}`-modules.**

At `F.over B` the `f`-map of the ambient restrictions is the localisation of the `f`-map
`F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ]
(`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFMap_app_over`) and the comparison
is its transpose
(`Crystalline.GlobalCrystallineSituation.Thickening.homEquiv_ambientOverComparison_app`).  The
crystal condition of [Stacks, Tag 07IS] says exactly that composing that `f`-map with the
pushforward of a morphism out of `F_T` is bijective on those morphisms, and
`Stacks.ModuleSliceTop.isIso_of_bijective_comp_homEquiv` turns that bijection — for all morphisms
out of `F_T` on the *unlocalised* Zariski site — into invertibility of the transpose on the
localised one, localisation at the greatest open being an equivalence of categories of sheaves of
modules. -/
theorem isIso_ambientOverComparison_app_over
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M) :
    IsIso ((ambientOverComparison B X).app (M.over B)) :=
  Stacks.ModuleSliceTop.isIso_of_bijective_comp_homEquiv
    (Opens.grothendieckTopology ↥X.left.thickening.target.scheme) (X.left.ringRestrictionSheaf)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ambientOpensOverRingHom B X))
    (Q := moduleRestrictionSheaf M X.left)
    ((ambientOverFMap B X).app (M.over B))
    (homEquiv_ambientOverComparison_app B X (M.over B))
    (bijective_comp_ambientOverFMap_app_over B X hM)

/-- **The ambient restriction at `X` of a module restricted from a crystal in `𝒪_{X/S}`-modules is
the `g`-pullback of its ambient restriction at the base**, the isomorphism being the comparison of
the ambient restrictions. -/
noncomputable def ambientOverComparisonIso
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M) :
    (SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B) ⋙
          SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).obj (M.over B) ≅
      (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).obj (M.over B) :=
  haveI := isIso_ambientOverComparison_app_over B X hM
  asIso ((ambientOverComparison B X).app (M.over B))

/-- The isomorphism of ambient restrictions at a crystal is the comparison of the ambient
restrictions. -/
@[simp]
theorem ambientOverComparisonIso_hom
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M) :
    (ambientOverComparisonIso B X hM).hom = (ambientOverComparison B X).app (M.over B) := rfl

/-- **The comparison of the ambient restrictions is compatible with every morphism of sheaves of
modules on the localised crystalline site**: the ambient restriction at `X` of a morphism, read
through the comparison, is the `g`-pullback of its ambient restriction at the base.  Applied to
the two maps `a` and `b` of a presentation this says that their ambient restrictions at `X` are
the `g`-pullbacks of their ambient restrictions at the base, which is what the step (2) ⇒ (1) of
[Stacks, Tag 07IT] needs. -/
theorem ambientOverComparison_naturality
    {Z Z' : SheafOfModules.{u} ((crystallineStructureSheaf S).over B)} (φ : Z ⟶ Z') :
    (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).map
          ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).map φ) ≫
        (ambientOverComparison B X).app Z' =
      (ambientOverComparison B X).app Z ≫
        (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).map φ :=
  (ambientOverComparison B X).naturality φ

/-- **The isomorphisms of ambient restrictions at two crystals intertwine the ambient restriction
at `X` of a morphism with the `g`-pullback of its ambient restriction at the base.**  This is
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverComparison_naturality` at a morphism
of restrictions of crystals. -/
theorem ambientOverComparisonIso_hom_comp_pushforward_map
    {M M' : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M)
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
    {M M' : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsSheafCrystal M)
    (hM' : IsSheafCrystal M') (φ : M.over B ⟶ M'.over B) :
    (SheafOfModules.pushforward.{u} (ambientOverStructureHom B X)).map φ =
      (ambientOverComparisonIso B X hM).inv ≫
        (SheafOfModules.pullback.{u} (ambientOpensOverRingHom B X)).map
            ((SheafOfModules.pushforward.{u} (ambientOverSelfStructureHom B)).map φ) ≫
          (ambientOverComparisonIso B X hM').hom := by
  refine Eq.symm ?_
  rw [Iso.inv_comp_eq]
  exact (ambientOverComparisonIso_hom_comp_pushforward_map B X hM hM' φ).symm

end Thickening

end Crystalline.GlobalCrystallineSituation

end
