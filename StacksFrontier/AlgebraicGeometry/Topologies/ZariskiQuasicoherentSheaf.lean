module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# The Zariski half of Tag 03DT

For a scheme `S` and a module `F` on it, the presheaf of Tag 03DS sends a scheme `T` over `S` to
`Γ(T, T.hom⁺F)`. This presheaf is a sheaf for the Zariski topology on `CategoryTheory.Over S`.
Consequently Tag 03DT, that it is an fpqc sheaf when `F` is quasi-coherent, reduces to
faithfully flat descent of sections over an affine base.

## Main definitions

* `Stacks.Sites.pullbackCompIso` identifies the iterated pullback of `F` along `A ⟶ Y ⟶ S` with
  its pullback along the structure morphism of `A`.
* `Stacks.Sites.overSectionsIso` is, for an arrow `g : A ⟶ Y` of `CategoryTheory.Over S` whose
  underlying morphism is an open immersion, the comparison of the restriction of `Y.hom⁺F` to the
  open image of `g` with the pullback `A.hom⁺F`.
* `Stacks.Sites.overSectionsMap` is the induced map on global sections, with its target written
  as a group of sections of `Y.hom⁺F` over an open of `Y.left`.

## Main results

* `Stacks.Sites.restrictFunctorIsoPullback_congr`: the comparison
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` of restriction with pullback
  carries the congruence isomorphism of `restrictFunctor` to that of `pullback`.
* `Stacks.Sites.restrictFunctorIsoPullback_comp`: **restriction along an open immersion is
  pullback, compatibly with composition.** The comparison is compatible with
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `Stacks.Sites.pullbackSectionsMap_comp_overSectionsMap`: the map of the Tag 03DS presheaf along
  an arrow whose underlying morphism is an open immersion is, under the comparison, the
  restriction map of `Y.hom⁺F` to the open image.
* `Stacks.Sites.pullbackSectionsMap_comp_overSectionsMap_comp`: the same for a composite.
* `Stacks.Sites.isSheafFor_pullbackSections`: the sheaf condition of the Tag 03DS presheaf for a
  presieve of `CategoryTheory.Over S` whose arrows are jointly surjective open immersions.
* `Stacks.Sites.isSheaf_zariskiTopology_over_quasiCoherentPresheaf`: **the Zariski half of
  Tag 03DT**: the presheaf of Tag 03DS of a quasi-coherent module is a Zariski sheaf.
* `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_affine` and
  `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_affine_base`: Tag 03DT with the
  Zariski half discharged, so that only the affine faithfully flat statement remains.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules

universe u

namespace Stacks.Sites

section Opens

variable {Z : Scheme.{u}}

/-- A composite of two restriction maps of a module is the restriction map between the extreme
opens. -/
public theorem presheaf_map_comp_eq (M : Z.Modules) {A B C : Z.Opens}
    (f : B ⟶ A) (g : C ⟶ B) (h : C ⟶ A) :
    M.presheaf.map f.op ≫ M.presheaf.map g.op = M.presheaf.map h.op := by
  rw [← M.presheaf.map_comp, ← op_comp]; congr 2

/-- The element form of `Stacks.Sites.presheaf_map_comp_eq`. -/
public theorem presheaf_map_apply_comp (M : Z.Modules) {A B C : Z.Opens}
    (f : B ⟶ A) (g : C ⟶ B) (h : C ⟶ A) (s : ToType Γ(M, A)) :
    M.presheaf.map g.op (M.presheaf.map f.op s) = M.presheaf.map h.op s :=
  ConcreteCategory.congr_hom (presheaf_map_comp_eq M f g h) s

/-- Two composites of restriction maps of a module with the same source and target agree. -/
public theorem presheaf_map_comp_eq₂ (M : Z.Modules) {A B B' C : Z.Opens}
    (f : B ⟶ A) (g : C ⟶ B) (f' : B' ⟶ A) (g' : C ⟶ B') :
    M.presheaf.map f.op ≫ M.presheaf.map g.op = M.presheaf.map f'.op ≫ M.presheaf.map g'.op := by
  rw [presheaf_map_comp_eq M f g (g ≫ f), presheaf_map_comp_eq M f' g' (g ≫ f)]

/-- A restriction map of a module depends only on its endpoints. -/
public theorem presheaf_map_eq (M : Z.Modules) {A B : Z.Opens} (f g : B ⟶ A) :
    M.presheaf.map f.op = M.presheaf.map g.op := by
  rw [Subsingleton.elim f g]

/-- The open image of a composite of open immersions is contained in the open image of the second
factor. -/
public theorem image_top_comp_le {X' Y' Z' : Scheme.{u}} (p : X' ⟶ Y') (q : Y' ⟶ Z')
    [IsOpenImmersion q] [IsOpenImmersion (p ≫ q)] :
    (p ≫ q) ''ᵁ (⊤ : X'.Opens) ≤ q ''ᵁ (⊤ : Y'.Opens) := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨w, rfl⟩
  exact ⟨p.base w, by simp⟩

end Opens

section Restriction

variable {W W' Z : Scheme.{u}}

/-- **The comparison of restriction along an open immersion with pullback along it carries the
unit of `restrict ⊣ pushforward` to the unit of `pullback ⊣ pushforward`.** -/
public theorem unit_restrictFunctorIsoPullback (f : W ⟶ Z) [IsOpenImmersion f] (M : Z.Modules) :
    (restrictAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) =
      (pullbackPushforwardAdjunction f).unit.app M :=
  CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- `Stacks.Sites.unit_restrictFunctorIsoPullback` read in the other direction. -/
public theorem unit_restrictFunctorIsoPullback_inv (f : W ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) =
      (restrictAdjunction f).unit.app M := by
  rw [← unit_restrictFunctorIsoPullback f M, Category.assoc, ← Functor.map_comp]
  simp

/-- The unit of `restrict ⊣ pushforward` along a composite of open immersions, compared with the
composite of the two units along the factors. -/
public theorem unit_restrictFunctorComp (l : W' ⟶ W) (j : W ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion j] (M : Z.Modules) :
    (restrictAdjunction (l ≫ j)).unit.app M ≫
        (pushforward (l ≫ j)).map ((restrictFunctorComp l j).hom.app M) =
      (restrictAdjunction j).unit.app M ≫
        (pushforward j).map ((restrictAdjunction l).unit.app ((restrictFunctor j).obj M)) ≫
        (pushforwardComp l j).hom.app ((restrictFunctor l).obj ((restrictFunctor j).obj M)) := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.restrict_map]
  exact presheaf_map_comp_eq₂ M _ _ _ _

/-- **The unit of `(f ≫ g)⁺ ⊣ (f ≫ g)_*` is the unit of the composite adjunction**, compared
along the composition isomorphisms of pullback and pushforward. -/
public theorem unit_pullbackComp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app M ≫
        (pushforward f ⋙ pushforward g).map ((pullbackComp f g).hom.app M) ≫
        (pushforwardComp f g).hom.app ((pullback (f ≫ g)).obj M) =
      (pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  rw [(pushforwardComp f g).hom.naturality ((pullbackComp f g).hom.app M), ← Category.assoc, h,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Naturality of the unit of `restrict ⊣ pushforward` in the module. -/
private theorem unit_restrictAdjunction_map (l : W' ⟶ W) [IsOpenImmersion l] {M N : W.Modules}
    (φ : M ⟶ N) :
    (restrictAdjunction l).unit.app M ≫ (pushforward l).map ((restrictFunctor l).map φ) =
      φ ≫ (restrictAdjunction l).unit.app N := by
  simp

/-- **Restriction along an open immersion is pullback, compatibly with composition.** The
comparison `restrict (l ≫ j) ≅ (l ≫ j)⁺` agrees with the composite of the comparisons for `l` and
`j` with the two composition isomorphisms. -/
public theorem restrictFunctorIsoPullback_comp (l : W' ⟶ W) (j : W ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion j] (M : Z.Modules) :
    (restrictFunctorComp l j).hom.app M ≫
        ((restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M) ≫
          (restrictFunctorIsoPullback l).hom.app ((pullback j).obj M) ≫
          (pullbackComp l j).hom.app M) =
      (restrictFunctorIsoPullback (l ≫ j)).hom.app M := by
  have key : (restrictAdjunction l).unit.app ((restrictFunctor j).obj M) ≫
      (pushforward l).map ((restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M) ≫
        (restrictFunctorIsoPullback l).hom.app ((pullback j).obj M) ≫
        (pullbackComp l j).hom.app M) =
      (restrictFunctorIsoPullback j).hom.app M ≫
        ((pullbackPushforwardAdjunction l).unit.app ((pullback j).obj M) ≫
          (pushforward l).map ((pullbackComp l j).hom.app M)) := by
    rw [← unit_restrictFunctorIsoPullback l ((pullback j).obj M)]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (unit_restrictAdjunction_map l ((restrictFunctorIsoPullback j).hom.app M))]
  refine ((restrictAdjunction (l ≫ j)).homEquiv M _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    unit_restrictFunctorIsoPullback (l ≫ j) M,
    Functor.map_comp, ← Category.assoc, unit_restrictFunctorComp l j M, Category.assoc,
    Category.assoc,
    ← (pushforwardComp l j).hom.naturality
      ((restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M) ≫
        (restrictFunctorIsoPullback l).hom.app ((pullback j).obj M) ≫
        (pullbackComp l j).hom.app M),
    Functor.comp_map,
    ← Category.assoc ((pushforward j).map
      ((restrictAdjunction l).unit.app ((restrictFunctor j).obj M))),
    ← Functor.map_comp, key]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (unit_restrictFunctorIsoPullback j M),
    ← reassoc_of% (Adjunction.comp_unit_app (adj₁ := pullbackPushforwardAdjunction j)
      (adj₂ := pullbackPushforwardAdjunction l) M)]
  exact unit_pullbackComp l j M

/-- `Stacks.Sites.restrictFunctorIsoPullback_comp` with the comparison for the composite
inverted. -/
public theorem restrictFunctorIsoPullback_comp_inv (l : W' ⟶ W) (j : W ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion j] (M : Z.Modules) :
    (pullbackComp l j).hom.app M ≫ (restrictFunctorIsoPullback (l ≫ j)).inv.app M =
      (restrictFunctorIsoPullback l).inv.app ((pullback j).obj M) ≫
        (restrictFunctor l).map ((restrictFunctorIsoPullback j).inv.app M) ≫
        (restrictFunctorComp l j).inv.app M := by
  have h := restrictFunctorIsoPullback_comp l j M
  rw [← cancel_epi ((restrictFunctorComp l j).hom.app M ≫
    (restrictFunctor l).map ((restrictFunctorIsoPullback j).hom.app M) ≫
    (restrictFunctorIsoPullback l).hom.app ((pullback j).obj M))]
  simp only [Category.assoc]
  rw [reassoc_of% h, Iso.hom_inv_id_app]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Congruence of pullback along the reflexive equality is the identity:
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso`. -/
public theorem pullbackCongr_refl {X Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackCongr (rfl : f = f) = Iso.refl _ := by
  simp [Scheme.Modules.pullbackCongr]

/-- Congruence of restriction along the reflexive equality is the identity. -/
public theorem restrictFunctorCongr_refl {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    restrictFunctorCongr (rfl : f = f) = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ Scheme.Modules.hom_ext _ _ fun V ↦ ?_))
  simp
  rfl

/-- **Restriction along an open immersion is pullback, compatibly with congruence.**  The
comparison of restriction with pullback carries the congruence isomorphism of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` to that of
`AlgebraicGeometry.Scheme.Modules.pullback`. -/
public theorem restrictFunctorIsoPullback_congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (hf : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (restrictFunctorCongr hf).hom ≫ (restrictFunctorIsoPullback g).hom
      = (restrictFunctorIsoPullback f).hom ≫ (pullbackCongr hf).hom := by
  subst hf
  rw [restrictFunctorCongr_refl, pullbackCongr_refl]
  simp

/-- **The unit of `j⁺ ⊣ j_*` on global sections, for an open immersion `j`, is the restriction map
to the open image.** -/
public theorem topUnitMap_restrictFunctorIsoPullback_inv (j : W ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) :
    topUnitMap j ((restrictFunctorIsoPullback j).inv.app M) =
      M.presheaf.map (homOfLE (le_top (a := j ''ᵁ (⊤ : W.Opens)))).op :=
  congrArg (fun t ↦ Scheme.Modules.Hom.app t (⊤ : Z.Opens))
    (unit_restrictFunctorIsoPullback_inv j M)

/-- **The composition isomorphism of pullbacks on global sections, for open immersions, is a
restriction map.** -/
public theorem topUnitMap_pullbackComp (l : W' ⟶ W) (j : W ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion j] (M : Z.Modules)
    (hle : (l ≫ j) ''ᵁ (⊤ : W'.Opens) ≤ j ''ᵁ (⊤ : W.Opens)) :
    topUnitMap l ((pullbackComp l j).hom.app M) ≫
        ((restrictFunctorIsoPullback (l ≫ j)).inv.app M).app (⊤ : W'.Opens) =
      ((restrictFunctorIsoPullback j).inv.app M).app (⊤ : W.Opens) ≫
        M.presheaf.map (homOfLE hle).op := by
  rw [topUnitMap_comp, restrictFunctorIsoPullback_comp_inv, ← topUnitMap_comp,
    topUnitMap_restrictFunctorIsoPullback_inv]
  have hmod : (restrictAdjunction l).unit.app ((pullback j).obj M) ≫
      (pushforward l).map ((restrictFunctor l).map ((restrictFunctorIsoPullback j).inv.app M) ≫
        (restrictFunctorComp l j).inv.app M) =
      (restrictFunctorIsoPullback j).inv.app M ≫
        ((restrictAdjunction l).unit.app ((restrictFunctor j).obj M) ≫
          (pushforward l).map ((restrictFunctorComp l j).inv.app M)) := by
    rw [Functor.map_comp, ← Category.assoc, unit_restrictAdjunction_map, Category.assoc]
  have h3 : Scheme.Modules.Hom.app
      ((restrictAdjunction l).unit.app ((restrictFunctor j).obj M) ≫
        (pushforward l).map ((restrictFunctorComp l j).inv.app M)) (⊤ : W.Opens) =
      M.presheaf.map (homOfLE hle).op := by
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictAdjunction_unit_app_app,
      Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
      Scheme.Modules.restrict_map]
    exact presheaf_map_comp_eq M _ _ _
  refine (congrArg (fun t ↦ Scheme.Modules.Hom.app t (⊤ : W.Opens)) hmod).trans ?_
  rw [Scheme.Modules.Hom.comp_app, h3]
  rfl

end Restriction

section OverSections

variable {S : Scheme.{u}} (F : S.Modules)

/-- Iterated pullback of `F` along `A ⟶ Y ⟶ S`, compared with its pullback along the structure
morphism of `A`. -/
@[simps]
public noncomputable def pullbackCompIso {A' Y' : Scheme.{u}} (q : A' ⟶ Y') (y : Y' ⟶ S)
    (a : A' ⟶ S) (ha : q ≫ y = a) :
    (pullback q).obj ((pullback y).obj F) ≅ (pullback a).obj F where
  hom := (pullbackComp q y).hom.app F ≫ (pullbackCongr ha).hom.app F
  inv := (pullbackCongr ha).inv.app F ≫ (pullbackComp q y).inv.app F
  hom_inv_id := by simp
  inv_hom_id := by simp

@[simp]
public theorem pullbackCongr_rfl_hom_app {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (M : Y'.Modules) :
    (pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ := rfl

@[simp]
public theorem pullbackCongr_rfl_inv_app {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (M : Y'.Modules) :
    (pullbackCongr (rfl : f = f)).inv.app M = 𝟙 _ := rfl

/-- The associativity coherence of the pullback pseudofunctor, in the form that compares the
comparison isomorphism for `B' ⟶ A' ⟶ S` with the one for `B' ⟶ Y' ⟶ S`. -/
public theorem pullbackCompIso_cancel {B' A' Y' : Scheme.{u}} (p : B' ⟶ A') (q : A' ⟶ Y')
    (y : Y' ⟶ S) (a : A' ⟶ S) (b : B' ⟶ S) (ha : q ≫ y = a) (hb : p ≫ a = b)
    (hc : (p ≫ q) ≫ y = b) :
    (pullbackCompIso F p a b hb).hom ≫ (pullbackCompIso F (p ≫ q) y b hc).inv =
      (pullback p).map (pullbackCompIso F q y a ha).inv ≫
        (pullbackComp p q).hom.app ((pullback y).obj F) := by
  subst ha hb
  simp only [pullbackCompIso_hom, pullbackCompIso_inv, Category.assoc,
    pullbackCongr_rfl_hom_app, pullbackCongr_rfl_inv_app, Category.id_comp]
  rw [pullbackComp_assoc_app p q y F]
  rfl

variable (Y : Over S)

/-- **The comparison of the restriction of `Y.hom⁺F` to the open image of `g` with `A.hom⁺F`**,
for an arrow `g : A ⟶ Y` of `CategoryTheory.Over S` whose underlying morphism is an open
immersion. -/
public noncomputable def overSectionsIso {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    (restrictFunctor g.left).obj ((pullback Y.hom).obj F) ≅ (pullback A.hom).obj F :=
  (restrictFunctorIsoPullback g.left).app ((pullback Y.hom).obj F) ≪≫
    pullbackCompIso F g.left Y.hom A.hom (Over.w g)

/-- `Stacks.Sites.overSectionsIso` on global sections, with its target written as a group of
sections of `Y.hom⁺F` over an open of `Y.left`. -/
public noncomputable def overSectionsMap {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    Γ((pullback A.hom).obj F, (⊤ : A.left.Opens)) ⟶
      Γ((pullback Y.hom).obj F, g.left ''ᵁ (⊤ : A.left.Opens)) :=
  Scheme.Modules.Hom.app (overSectionsIso F Y g).inv (⊤ : A.left.Opens)

/-- `Stacks.Sites.overSectionsMap` is an isomorphism. -/
public instance isIso_overSectionsMap {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    IsIso (overSectionsMap F Y g) :=
  inferInstanceAs (IsIso (Scheme.Modules.Hom.app (overSectionsIso F Y g).inv _))

/-- The map of the Tag 03DS presheaf along `g : A ⟶ B` is the global-sections map of the
comparison `Stacks.Sites.pullbackCompIso` for `g.left`. -/
public theorem pullbackSectionsMap_eq_topUnitMap' {A B : Over S} (g : A ⟶ B) :
    pullbackSectionsMap F g =
      topUnitMap g.left (pullbackCompIso F g.left B.hom A.hom (Over.w g)).hom :=
  pullbackSectionsMap_eq_topUnitMap F g

/-- **The map of the Tag 03DS presheaf along an arrow whose underlying morphism is an open
immersion is the restriction map to the open image.** -/
public theorem pullbackSectionsMap_comp_overSectionsIso {A : Over S} (g : A ⟶ Y)
    [IsOpenImmersion g.left] :
    pullbackSectionsMap F g ≫
        Scheme.Modules.Hom.app (overSectionsIso F Y g).inv (⊤ : A.left.Opens) =
      ((pullback Y.hom).obj F).presheaf.map
        (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op := by
  rw [pullbackSectionsMap_eq_topUnitMap' F g, topUnitMap_comp,
    show (pullbackCompIso F g.left Y.hom A.hom (Over.w g)).hom ≫ (overSectionsIso F Y g).inv =
      (restrictFunctorIsoPullback g.left).inv.app ((pullback Y.hom).obj F) from by
        simp [overSectionsIso]]
  exact topUnitMap_restrictFunctorIsoPullback_inv g.left ((pullback Y.hom).obj F)

/-- `Stacks.Sites.pullbackSectionsMap_comp_overSectionsIso` with the target of the comparison
written as a group of sections of `Y.hom⁺F`. -/
public theorem pullbackSectionsMap_comp_overSectionsMap {A : Over S} (g : A ⟶ Y)
    [IsOpenImmersion g.left] :
    pullbackSectionsMap F g ≫ overSectionsMap F Y g =
      ((pullback Y.hom).obj F).presheaf.map
        (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op :=
  pullbackSectionsMap_comp_overSectionsIso F Y g

/-- **The map of the Tag 03DS presheaf along a factor of such an arrow is the restriction map
between the two open images.** -/
public theorem pullbackSectionsMap_comp_overSectionsIso_comp {A B : Over S} (g : A ⟶ Y)
    (k : B ⟶ A) [IsOpenImmersion g.left] [hki : IsOpenImmersion (k ≫ g).left]
    (hle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens)) :
    pullbackSectionsMap F k ≫
        Scheme.Modules.Hom.app (overSectionsIso F Y (k ≫ g)).inv (⊤ : B.left.Opens) =
      Scheme.Modules.Hom.app (overSectionsIso F Y g).inv (⊤ : A.left.Opens) ≫
        ((pullback Y.hom).obj F).presheaf.map (homOfLE hle).op := by
  have : IsOpenImmersion (k.left ≫ g.left) := hki
  have : IsOpenImmersion k.left := IsOpenImmersion.of_comp k.left g.left
  rw [pullbackSectionsMap_eq_topUnitMap' F k, topUnitMap_comp]
  have harg : (pullbackCompIso F k.left A.hom B.hom (Over.w k)).hom ≫
      (overSectionsIso F Y (k ≫ g)).inv =
      (pullback k.left).map (pullbackCompIso F g.left Y.hom A.hom (Over.w g)).inv ≫
        ((pullbackComp k.left g.left).hom.app ((pullback Y.hom).obj F) ≫
          (restrictFunctorIsoPullback (k.left ≫ g.left)).inv.app ((pullback Y.hom).obj F)) := by
    rw [show (overSectionsIso F Y (k ≫ g)).inv =
        (pullbackCompIso F (k.left ≫ g.left) Y.hom B.hom (Over.w (k ≫ g))).inv ≫
          (restrictFunctorIsoPullback (k.left ≫ g.left)).inv.app
            ((pullback Y.hom).obj F) from rfl,
      ← Category.assoc, pullbackCompIso_cancel, Category.assoc]
  rw [harg, ← comp_topUnitMap, ← topUnitMap_comp,
    topUnitMap_pullbackComp k.left g.left ((pullback Y.hom).obj F) hle,
    show (overSectionsIso F Y g).inv =
      (pullbackCompIso F g.left Y.hom A.hom (Over.w g)).inv ≫
        (restrictFunctorIsoPullback g.left).inv.app ((pullback Y.hom).obj F) from rfl,
    Scheme.Modules.Hom.comp_app]
  exact (Category.assoc _ _ _).symm

/-- `Stacks.Sites.pullbackSectionsMap_comp_overSectionsIso_comp` with the targets of the
comparisons written as groups of sections of `Y.hom⁺F`. -/
public theorem pullbackSectionsMap_comp_overSectionsMap_comp {A B : Over S} (g : A ⟶ Y)
    (k : B ⟶ A) [IsOpenImmersion g.left] [IsOpenImmersion (k ≫ g).left]
    (hle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens)) :
    pullbackSectionsMap F k ≫ overSectionsMap F Y (k ≫ g) =
      overSectionsMap F Y g ≫ ((pullback Y.hom).obj F).presheaf.map (homOfLE hle).op :=
  pullbackSectionsMap_comp_overSectionsIso_comp F Y g k hle

end OverSections

section SheafCondition

variable {S : Scheme.{u}} (F : S.Modules) (Y : Over S)

/-- Restricting a transferred section to a smaller open can be computed through any factorisation
of the arrow it comes from. -/
public theorem map_overSectionsMap {A B : Over S} (g : A ⟶ Y) (k : B ⟶ A) (m : B ⟶ Y)
    (hm : k ≫ g = m) [IsOpenImmersion g.left] [IsOpenImmersion m.left] (V : Y.left.Opens)
    (hVm : V ≤ m.left ''ᵁ (⊤ : B.left.Opens)) (hVg : V ≤ g.left ''ᵁ (⊤ : A.left.Opens))
    (t : ToType Γ((pullback A.hom).obj F, (⊤ : A.left.Opens))) :
    ((pullback Y.hom).obj F).presheaf.map (homOfLE hVg).op (overSectionsMap F Y g t) =
      ((pullback Y.hom).obj F).presheaf.map (homOfLE hVm).op
        (overSectionsMap F Y m (pullbackSectionsMap F k t)) := by
  subst hm
  have hk : IsOpenImmersion (k.left ≫ g.left) := ‹IsOpenImmersion (k ≫ g).left›
  have hmle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens) :=
    image_top_comp_le k.left g.left
  have h : overSectionsMap F Y (k ≫ g) (pullbackSectionsMap F k t) =
      ((pullback Y.hom).obj F).presheaf.map (homOfLE hmle).op (overSectionsMap F Y g t) :=
    ConcreteCategory.congr_hom
      (pullbackSectionsMap_comp_overSectionsMap_comp F Y g k hmle) t
  rw [h]
  exact (presheaf_map_apply_comp ((pullback Y.hom).obj F) (homOfLE hmle) (homOfLE hVm)
    (homOfLE hVg) _).symm

/-- **An open of `Y.left` inside the images of two arrows of `CategoryTheory.Over S` refines
both.** -/
public theorem exists_common_refinement {A B : Over S} (g₁ : A ⟶ Y) (g₂ : B ⟶ Y)
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left] (V : Y.left.Opens)
    (hV₁ : V ≤ g₁.left ''ᵁ (⊤ : A.left.Opens)) (hV₂ : V ≤ g₂.left ''ᵁ (⊤ : B.left.Opens)) :
    ∃ (C : Over S) (m : C ⟶ Y) (_ : IsOpenImmersion m.left),
      V ≤ m.left ''ᵁ (⊤ : C.left.Opens) ∧
        ∃ (k₁ : C ⟶ A) (k₂ : C ⟶ B), k₁ ≫ g₁ = m ∧ k₂ ≫ g₂ = m := by
  have hr : ∀ {C : Over S} (g : C ⟶ Y) [IsOpenImmersion g.left],
      V ≤ g.left ''ᵁ (⊤ : C.left.Opens) → Set.range V.ι.base ⊆ Set.range g.left.base := by
    intro C g _ hV z hz
    rw [Scheme.Opens.range_ι] at hz
    have hz' : z ∈ g.left ''ᵁ (⊤ : C.left.Opens) := hV hz
    rwa [Scheme.Hom.image_top_eq_opensRange] at hz'
  refine ⟨Over.mk (V.ι ≫ Y.hom), Over.homMk V.ι rfl,
    inferInstanceAs (IsOpenImmersion V.ι), le_of_eq (Scheme.Opens.ι_image_top V).symm,
    Over.homMk (IsOpenImmersion.lift g₁.left V.ι (hr g₁ hV₁))
      (by rw [← Over.w g₁, ← Category.assoc, IsOpenImmersion.lift_fac]; rfl),
    Over.homMk (IsOpenImmersion.lift g₂.left V.ι (hr g₂ hV₂))
      (by rw [← Over.w g₂, ← Category.assoc, IsOpenImmersion.lift_fac]; rfl),
    Over.OverMorphism.ext (by simp), Over.OverMorphism.ext (by simp)⟩

/-- **Two sections transferred along arrows of a presieve of open immersions agree on the
intersection of the two open images**, as soon as they agree after restriction along every pair of
morphisms with a common composite. -/
public theorem overSections_compatible {A B : Over S} (g₁ : A ⟶ Y) (g₂ : B ⟶ Y)
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (t₁ : ToType Γ((pullback A.hom).obj F, (⊤ : A.left.Opens)))
    (t₂ : ToType Γ((pullback B.hom).obj F, (⊤ : B.left.Opens)))
    (ht : ∀ (C : Over S) (k₁ : C ⟶ A) (k₂ : C ⟶ B), k₁ ≫ g₁ = k₂ ≫ g₂ →
      pullbackSectionsMap F k₁ t₁ = pullbackSectionsMap F k₂ t₂) :
    ((pullback Y.hom).obj F).presheaf.map
        (Opens.infLELeft (g₁.left ''ᵁ (⊤ : A.left.Opens)) (g₂.left ''ᵁ (⊤ : B.left.Opens))).op
        (overSectionsMap F Y g₁ t₁) =
      ((pullback Y.hom).obj F).presheaf.map
        (Opens.infLERight (g₁.left ''ᵁ (⊤ : A.left.Opens)) (g₂.left ''ᵁ (⊤ : B.left.Opens))).op
        (overSectionsMap F Y g₂ t₂) := by
  obtain ⟨C, m, hmi, hVm, k₁, k₂, hm₁, hm₂⟩ :=
    exists_common_refinement Y g₁ g₂
      ((g₁.left ''ᵁ (⊤ : A.left.Opens)) ⊓ (g₂.left ''ᵁ (⊤ : B.left.Opens)))
      inf_le_left inf_le_right
  have := hmi
  rw [presheaf_map_eq _ (Opens.infLELeft _ _) (homOfLE inf_le_left),
    presheaf_map_eq _ (Opens.infLERight _ _) (homOfLE inf_le_right),
    map_overSectionsMap F Y g₁ k₁ m hm₁ _ hVm inf_le_left t₁,
    map_overSectionsMap F Y g₂ k₂ m hm₂ _ hVm inf_le_right t₂,
    ht C k₁ k₂ (hm₁.trans hm₂.symm)]

/-- The maps of a `AlgebraicGeometry.PullbackSectionsPresheaf`, read through its identifications
with groups of global sections, as a commuting square. -/
public theorem objIso_hom_pullbackSectionsMap (P : PullbackSectionsPresheaf S F) {A C : Over S}
    (k : C ⟶ A) :
    (P.objIso (op A)).hom ≫ pullbackSectionsMap F k =
      P.functor.map k.op ≫ (P.objIso (op C)).hom := by
  rw [Stacks.Sites.PullbackSectionsPresheaf.functor_map _ P k.op]
  simp

/-- **The Zariski sheaf condition for the presheaf of Tag 03DS**, for a presieve of
`CategoryTheory.Over S` whose arrows are open immersions of the underlying schemes and are jointly
surjective. -/
public theorem isSheafFor_pullbackSections (P : PullbackSectionsPresheaf S F) (R : Presieve Y)
    (hoi : ∀ {A : Over S} (g : A ⟶ Y), R g → IsOpenImmersion g.left)
    (hcov : ∀ y : Y.left, ∃ (A : Over S) (g : A ⟶ Y) (_ : R g), y ∈ Set.range g.left.base) :
    Presieve.IsSheafFor (P.functor ⋙ CategoryTheory.forget AddCommGrpCat) R := by
  intro x hx
  have hoi' : ∀ i : Σ A : Over S, { g : A ⟶ Y // R g }, IsOpenImmersion i.2.1.left :=
    fun i ↦ hoi i.2.1 i.2.2
  have key : ∀ {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left]
      (t : ToType (P.functor.obj (op Y))),
      overSectionsMap F Y g ((P.objIso (op A)).hom (P.functor.map g.op t)) =
        ((pullback Y.hom).obj F).presheaf.map
          (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op
          ((P.objIso (op Y)).hom t) := by
    intro A g _ t
    have hmor : P.functor.map g.op ≫ (P.objIso (op A)).hom ≫ overSectionsMap F Y g =
        (P.objIso (op Y)).hom ≫ ((pullback Y.hom).obj F).presheaf.map
          (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op := by
      rw [← reassoc_of% (objIso_hom_pullbackSectionsMap F P g),
        pullbackSectionsMap_comp_overSectionsMap]
    exact ConcreteCategory.congr_hom hmor t
  have hcompat : ∀ i j : Σ A : Over S, { g : A ⟶ Y // R g },
      ((pullback Y.hom).obj F).presheaf.map
          (Opens.infLELeft (i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
            (j.2.1.left ''ᵁ (⊤ : j.1.left.Opens))).op
          (overSectionsMap F Y i.2.1 ((P.objIso (op i.1)).hom (x i.2.1 i.2.2))) =
        ((pullback Y.hom).obj F).presheaf.map
          (Opens.infLERight (i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
            (j.2.1.left ''ᵁ (⊤ : j.1.left.Opens))).op
          (overSectionsMap F Y j.2.1 ((P.objIso (op j.1)).hom (x j.2.1 j.2.2))) := by
    intro i j
    refine overSections_compatible F Y i.2.1 j.2.1 _ _ fun C k₁ k₂ hk ↦ ?_
    have h₁ := ConcreteCategory.congr_hom (objIso_hom_pullbackSectionsMap F P k₁)
      (x i.2.1 i.2.2)
    have h₂ := ConcreteCategory.congr_hom (objIso_hom_pullbackSectionsMap F P k₂)
      (x j.2.1 j.2.2)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁ h₂
    rw [h₁, h₂]
    exact congrArg (ConcreteCategory.hom (P.objIso (op C)).hom)
      (hx k₁ k₂ i.2.2 j.2.2 hk)
  obtain ⟨s, hs, hsuniq⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨((pullback Y.hom).obj F).presheaf, ((pullback Y.hom).obj F).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} Y.left)
    (fun i : Σ A : Over S, { g : A ⟶ Y // R g } ↦ i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
    (⊤ : Y.left.Opens) (fun _ ↦ homOfLE le_top)
    (by
      intro y _
      obtain ⟨A, g, hg, hy⟩ := hcov y
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨A, ⟨g, hg⟩⟩, ?_⟩
      rwa [Scheme.Hom.image_top_eq_opensRange])
    (fun i ↦ overSectionsMap F Y i.2.1 ((P.objIso (op i.1)).hom (x i.2.1 i.2.2)))
    hcompat
  have hglue : ∀ t : ToType (P.functor.obj (op Y)),
      (∀ {A : Over S} (g : A ⟶ Y) (hg : R g), P.functor.map g.op t = x g hg) →
      (P.objIso (op Y)).hom t = s := by
    intro t ht
    refine hsuniq _ fun i ↦ ?_
    have : IsOpenImmersion i.2.1.left := hoi' i
    rw [← key i.2.1 t, ht i.2.1 i.2.2]
  refine ⟨(P.objIso (op Y)).inv s, ?_, ?_⟩
  · intro A g hg
    have : IsOpenImmersion g.left := hoi g hg
    refine (ConcreteCategory.bijective_of_isIso (P.objIso (op A)).hom).1
      ((ConcreteCategory.bijective_of_isIso (overSectionsMap F Y g)).1 ?_)
    refine (key g ((P.objIso (op Y)).inv s)).trans ?_
    rw [show (P.objIso (op Y)).hom ((P.objIso (op Y)).inv s) = s from
      ConcreteCategory.congr_hom (P.objIso (op Y)).inv_hom_id s]
    exact hs ⟨A, ⟨g, hg⟩⟩
  · intro t ht
    rw [← hglue t fun g hg ↦ ht g hg]
    exact (ConcreteCategory.congr_hom (P.objIso (op Y)).hom_inv_id t).symm

end SheafCondition

section Main

/-- **The Zariski sheaf condition for the presheaf of Tag 03DS**, for the presieves that generate
the Zariski topology on `CategoryTheory.Over S`. -/
public theorem isSheafFor_zariski_presieve {S : Scheme.{u}} {F : S.Modules}
    (P : PullbackSectionsPresheaf S F) {Y : Over S} (R : Presieve Y)
    (hR : R.map (Over.forget S) ∈ Scheme.precoverage @IsOpenImmersion Y.left) :
    Presieve.IsSheafFor (P.functor ⋙ CategoryTheory.forget AddCommGrpCat) R := by
  obtain ⟨hsurj, hoi⟩ := hR
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hsurj
  refine isSheafFor_pullbackSections F Y P R (fun g hg ↦ hoi (Presieve.map.of hg)) fun y ↦ ?_
  obtain ⟨W, f, hf, hy⟩ := hsurj y
  rcases hf with @⟨A, g, hg⟩
  exact ⟨A, g, hg, hy⟩

/-- **The presheaf of Tag 03DS is a Zariski sheaf on the schemes over `S`.** -/
public theorem isSheaf_zariskiTopology_over_pullbackSectionsPresheaf {S : Scheme.{u}}
    {F : S.Modules} (P : PullbackSectionsPresheaf S F) :
    Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (P.functor ⋙ CategoryTheory.forget AddCommGrpCat) :=
  (isSheaf_over_toGrothendieck_iff (Scheme.precoverage @IsOpenImmersion) S _).2
    fun {_} R hR ↦ isSheafFor_zariski_presieve P R hR

/-- **The Zariski half of Tag 03DT.** The presheaf of Tag 03DS of a quasi-coherent module `F` on
`S` is a Zariski sheaf on the schemes over `S`. -/
public theorem isSheaf_zariskiTopology_over_quasiCoherentPresheaf (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_zariskiTopology_over_pullbackSectionsPresheaf (quasiCoherentPresheaf S F)

/-- **Tag 03DT with the Zariski half discharged.** The presheaf of Tag 03DS of a quasi-coherent
module is an fpqc sheaf on the schemes over `S` as soon as it satisfies the sheaf condition for a
single faithfully flat morphism of affine schemes over `S`. -/
public theorem isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_affine (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent]
    (haff : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ f : Spec R' ⟶ S, Presieve.IsSheafFor
        (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk f)).symm
          (Sieve.generate (Presieve.singleton (Spec.map φ)))).arrows) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine S F
    (isSheaf_zariskiTopology_over_quasiCoherentPresheaf S F) haff

/-- **Tag 03DT with the Zariski half discharged, and the affine half moved to an affine base.**
The presheaf of Tag 03DS of a quasi-coherent module is an fpqc sheaf on the schemes over `S` as
soon as faithfully flat descent of sections holds for quasi-coherent modules on affine schemes. -/
public theorem isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_affine_base (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent]
    (haff : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ (F' : (Spec R').Modules) [F'.IsQuasicoherent],
        Presieve.IsSheafFor
          (quasiCoherentPresheafFunctor (Spec R') F' ⋙ CategoryTheory.forget AddCommGrpCat)
          ((Sieve.overEquiv (Over.mk (𝟙 (Spec R')) : Over (Spec R'))).symm
            (Sieve.generate (Presieve.singleton (Spec.map φ)))).arrows) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine_base S F
    (isSheaf_zariskiTopology_over_quasiCoherentPresheaf S F) haff

end Main

end Stacks.Sites

end
