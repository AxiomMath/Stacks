module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.GlobalClauseFromTheStageClause
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.SectionsOnTheVertex
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Degree zero: the colimit comparison of Tag 0A37

This file proves the colimit comparison of Stacks 0A37 in degree zero, for an arbitrary system,
over a quasi-compact stage open and globally.  This is the base case of the degree induction that
proves the comparison in every degree (`SpectralAbelianSheafSystem.isIso_comparison`, in
`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonInEveryDegree.lean`).

The content is that the specification `Tag0A37.IsCohomologyMap` of the prescribed maps, which is
phrased through injective resolutions and right-derived evaluation, says in degree zero exactly
that the map is the map on sections: the `f`-map read on sections over the open upstairs, followed
by the restriction to the open downstairs.  Sections over an open are left exact
(`preservesFiniteLimits_sections`), so `CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifies
the degree-zero right-derived functor with the functor itself, and
`CategoryTheory.InjectiveResolution.toRightDerivedZero_eq` computes that identification on the
chosen resolution.  What is left is a cycles-level computation that uses nothing but the
commutation relation `I.ι.f 0 ≫ ψ.f 0 = φ ≫ f_*(J.ι.f 0)` carried by `IsCohomologyMap` and the
naturality of `restrictSections`.

With that, a presentation of the cohomology cocone in degree zero *is* the comparison cocone of
the stage system of sections, whose colimit property over a quasi-compact stage open is abelian
Stacks 0A33 on the vertex of a limiting cone —
`SpectralAbelianSheafSystem.isStageSectionsColimit`.  The global clause follows from the
quasi-compact-open one by `isIso_comparison_global_of_stage`.

## Main definitions

* `sectionsRestrictMap`: the map on sections induced by a map of abelian sheaves over a continuous
  map and a compatible pair of opens.
* `CohomologyCocone.zeroObjIso` and `CohomologyCocone.zeroVertexIso`: the degree-zero
  identifications of the cohomology groups of a presentation with groups of sections.
* `SpectralAbelianSheafSystem.degreeZeroDiagramIso`: in degree zero the cohomology diagram of a
  presentation over a stage open is the stage system of sections.

## Main results

* `IsCohomologyMap.eq_sectionsRestrictMap`: **in degree zero the prescribed map of Tag 0A37 is the
  map on sections.**
* `CohomologyCocone.zeroObjIso_naturality` and `CohomologyCocone.zeroIota_comp`: the arrows and the
  legs of a presentation, in degree zero, are the maps on sections.
* `SpectralAbelianSheafSystem.nonempty_isColimit_cohomologyCocone_zero` and
  `isIso_comparison_zero`: the quasi-compact-open comparison of Stacks 0A37 in degree zero, with
  no hypothesis on the stage sheaves.
* `SpectralAbelianSheafSystem.isIso_comparison_global_zero`: the global comparison of Stacks 0A37
  in degree zero.
* `SpectralAbelianSheafSystem.not_isZero_H_skyscraperPtSystem`,
  `...isIso_comparison_skyscraperPtSystem` and `...isIso_comparison_zero_skyscraperPtSystem`: a
  system whose degree-zero cohomology is `ℤ`, at which both comparisons are isomorphisms of
  non-zero groups.
* `SpectralAbelianSheafSystem.isIso_comparison_of_injective_of_degree` and
  `isIso_comparison_global_of_injective`: both comparisons in every degree for a system of
  injective sheaves, the degree-zero case here joined to the positive-degree case of
  `StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.SectionsOnTheVertex`.

## Implementation notes

The three rearrangements `conj_zero_rearrange`, `conj_nat` and `conj_leg` are stated with abstract
objects and morphisms on purpose.  The identifications with right-derived evaluation have
`(HomologicalComplex.homologyFunctor _ _ 0).obj K` as an endpoint where
`HomologicalComplex.homologyMap` has `K.homology 0`; the two are definitionally but not
syntactically equal, so `rw` cannot build a motive across the junction — `Iso.inv_hom_id_assoc`
there reports an application type mismatch on a goal that visibly contains its pattern.  An
abstract lemma applied by `exact` checks the two spellings at full transparency instead, and needs
no transparency option.  For the same reason `simp only [Category.assoc]` does **not** reassociate
across that junction, so the abstract lemmas are stated at the associativity the goal actually
has.

The naturality of `degreeZeroDiagramIso` and the leg identity of the final cocone are written in
term mode for the same reason: the goals mention `(F ⋙ G).map a` and
`(Cocone.precompose α.hom).obj t`, whose unfoldings to `((stageSystem i).map a).app (op U)` and to
`α.hom.app A ≫ t.ι.app A` are definitional but not visible to `rw`, which reports its pattern
absent from a target that contains it.

The two clauses are stated at `v = v' = u`, the universes to which Stacks 0A37's
colimit-comparison clauses have to be restated; see the universe verdict in the implementation
notes of
`StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ComparisonReduction`.
The narrowing is inherited from the
inputs — abelian Stacks 01FF, 0A32 and 0A33 are all stated for a `u`-small index — and is
not a decision taken here.

## References

* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v' u₂ v₂

namespace Stacks.Cohomology.SpectralLimit

/-- The rearrangement that turns the degree-zero identification of a prescribed cohomology map
into its cycles-level content.  It is stated with abstract objects and morphisms because the two
endpoints `(HomologicalComplex.homologyFunctor _ _ 0).obj K` and `K.homology 0` are definitionally
but not syntactically equal, so a rewriting tactic cannot build a motive across the junction while
`exact` checks the two spellings up to full definitional equality. -/
theorem conj_zero_rearrange {C : Type u₂} [Category.{v₂} C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    (tI : A₀ ⟶ A₁) (pI : A₁ ⟶ A₂) (ainv : A₂ ⟶ A₃) (ahom : A₃ ⟶ A₂) (hM : A₂ ⟶ A₄)
    (binv : A₄ ⟶ A₅) (s : A₀ ⟶ A₆) (tJ : A₆ ⟶ A₇) (pJ : A₇ ⟶ A₄) (cM : A₁ ⟶ A₇)
    (hA : ainv ≫ ahom = 𝟙 A₂) (hp : pI ≫ hM = cM ≫ pJ) (hc : tI ≫ cM = s ≫ tJ) :
    (tI ≫ pI ≫ ainv) ≫ ahom ≫ hM ≫ binv = s ≫ tJ ≫ pJ ≫ binv := by
  rw [Category.assoc tI, Category.assoc pI ainv, ← Category.assoc ainv, hA, Category.id_comp,
    ← Category.assoc pI, hp, Category.assoc, ← Category.assoc tI, hc, Category.assoc]

/-- Reading a conjugated map as a naturality square.  The hypothesis is the shape in which
`IsCohomologyMap` pins an arrow of a presentation of the cohomology cocone, and the conclusion is
the naturality square of the three-fold identification. -/
theorem conj_nat {C : Type u₂} [Category.{v₂} C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : C}
    (o₁ : X₁ ≅ Y₁) (d₁ : Y₁ ≅ Z₁) (r₁ : Z₁ ≅ W₁)
    (o₂ : X₂ ≅ Y₂) (d₂ : Y₂ ≅ Z₂) (r₂ : Z₂ ≅ W₂) (m : X₁ ⟶ X₂) (s : W₁ ⟶ W₂)
    (hm : o₁.inv ≫ m ≫ o₂.hom = d₁.hom ≫ r₁.hom ≫ s ≫ r₂.inv ≫ d₂.inv) :
    m ≫ o₂.hom ≫ d₂.hom ≫ r₂.hom = (o₁.hom ≫ d₁.hom ≫ r₁.hom) ≫ s := by
  have h := (Iso.inv_comp_eq o₁).1 hm
  rw [← Category.assoc m, h]
  simp

/-- The companion of `conj_nat` for a leg of the comparison cocone, where there is no
identification to strip on the target. -/
theorem conj_leg {C : Type u₂} [Category.{v₂} C] {X₁ Y₁ Z₁ W₁ Y₂ Z₂ W₂ : C}
    (o₁ : X₁ ≅ Y₁) (d₁ : Y₁ ≅ Z₁) (r₁ : Z₁ ≅ W₁)
    (d₂ : Y₂ ≅ Z₂) (r₂ : Z₂ ≅ W₂) (m : X₁ ⟶ Y₂) (s : W₁ ⟶ W₂)
    (hm : o₁.inv ≫ m = d₁.hom ≫ r₁.hom ≫ s ≫ r₂.inv ≫ d₂.inv) :
    m ≫ d₂.hom ≫ r₂.hom = (o₁.hom ≫ d₁.hom ≫ r₁.hom) ≫ s := by
  simpa using conj_nat o₁ d₁ r₁ (Iso.refl Y₂) d₂ r₂ m s (by simpa using hm)

/-- The map on sections over the two compatible opens induced by a map of abelian sheaves over a
continuous map: the `f`-map read on sections over `V`, followed by restriction to `U`. -/
def sectionsRestrictMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    (sections.{u, u} Y V).obj G ⟶ (sections.{u, u} X U).obj F :=
  (sections.{u, u} Y V).map φ ≫ (restrictSections.{u, u} f V U h).app F

/-- The degree-zero component of `sectionsComplexMap`. -/
theorem sectionsComplexMap_f_zero {X Y : TopCat.{u}} (f : X ⟶ Y)
    {I : CochainComplex (Y.Sheaf AddCommGrpCat.{u}) ℕ}
    {J : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ}
    (ψ : I ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex _).obj J)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    (sectionsComplexMap.{u, u} f ψ V U h).f 0 =
      (sections.{u, u} Y V).map (ψ.f 0) ≫
        (restrictSections.{u, u} f V U h).app (J.X 0) := rfl

/-- **The cycles-level content of the degree-zero identification.**  The canonical map from
sections over `V` into the degree-zero cycles of the section complex of an injective resolution,
followed by the cycles map of `sectionsComplexMap`, is the map on sections followed by the same
canonical map for the resolution downstairs.

Both sides are checked after composing with the inclusion of the cycles, where the first factor
becomes the functor applied to `ι` in degree zero; the commutation relation of the lift then
replaces `I.ι.f 0 ≫ ψ.f 0` by `φ` followed by the pushforward of `J.ι.f 0`, and the naturality of
`restrictSections` moves the latter past the restriction. -/
theorem toRightDerivedZero'_comp_cyclesMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V)
    (I : InjectiveResolution G) (J : InjectiveResolution F)
    (ψ : I.cocomplex ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J.cocomplex)
    (hcomm : I.ι.f 0 ≫ ψ.f 0 = φ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)) :
    I.toRightDerivedZero' (sections.{u, u} Y V) ≫
        HomologicalComplex.cyclesMap (sectionsComplexMap.{u, u} f ψ V U h) 0 =
      sectionsRestrictMap f φ V U h ≫ J.toRightDerivedZero' (sections.{u, u} X U) := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
  rw [Category.assoc, HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc, Category.assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles, sectionsComplexMap_f_zero,
    sectionsRestrictMap]
  -- `(sections Y V).map (I.ι.f 0) ≫ (sections Y V).map (ψ.f 0) ≫ τ.app (J.X 0)`
  -- `= (sections Y V).map φ ≫ τ.app F ≫ (sections X U).map (J.ι.f 0)`
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (restrictSections.{u, u} f V U h).app (J.cocomplex.X 0))
    (((sections.{u, u} Y V).map_comp (I.ι.f 0) (ψ.f 0)).symm.trans
      ((congrArg (fun z ↦ (sections.{u, u} Y V).map z) hcomm).trans
        ((sections.{u, u} Y V).map_comp φ
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)))))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun z ↦ (sections.{u, u} Y V).map φ ≫ z)
    ((restrictSections.{u, u} f V U h).naturality (J.ι.f 0))

/-- **In degree zero the map prescribed by Tag 0A37 is the map on sections**, read through the
canonical identification of the degree-zero right-derived functor of a left exact functor with
the functor itself.

Sections over an open are left exact, so `CategoryTheory.Functor.rightDerivedZeroIsoSelf` applies
to both sides, and the identification is computed on a chosen injective resolution by
`CategoryTheory.InjectiveResolution.toRightDerivedZero_eq`: what is left is the cycles-level
statement `toRightDerivedZero'_comp_cyclesMap`. -/
theorem IsCohomologyMap.eq_sectionsRestrictMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V)
    (eG : Sheaf.H'.{u, u, u} G 0 V ≅ ((sections.{u, u} Y V).rightDerived 0).obj G)
    (eF : Sheaf.H'.{u, u, u} F 0 U ≅ ((sections.{u, u} X U).rightDerived 0).obj F)
    {m : Sheaf.H'.{u, u, u} G 0 V ⟶ Sheaf.H'.{u, u, u} F 0 U}
    (hm : IsCohomologyMap f φ V U h 0 eG eF m) :
    m = eG.hom ≫ (sections.{u, u} Y V).rightDerivedZeroIsoSelf.hom.app G ≫
      sectionsRestrictMap f φ V U h ≫
        (sections.{u, u} X U).toRightDerivedZero.app F ≫ eF.inv := by
  obtain ⟨I, J, ψ, hcomm, hmeq⟩ := hm
  have hπ : (CochainComplex.isoHomologyπ₀
        (((sections.{u, u} Y V).mapHomologicalComplex _).obj I.cocomplex)).hom ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) 0 =
      HomologicalComplex.cyclesMap (sectionsComplexMap.{u, u} f ψ V U h) 0 ≫
        (CochainComplex.isoHomologyπ₀
          (((sections.{u, u} X U).mapHomologicalComplex _).obj J.cocomplex)).hom := by
    rw [← cancel_mono (CochainComplex.isoHomologyπ₀
      (((sections.{u, u} X U).mapHomologicalComplex _).obj J.cocomplex)).inv,
      Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      CochainComplex.isoHomologyπ₀_inv_naturality, Iso.hom_inv_id_assoc]
  have hstar : (sections.{u, u} Y V).toRightDerivedZero.app G ≫
        (I.isoRightDerivedObj (sections.{u, u} Y V) 0).hom ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) 0 ≫
        (J.isoRightDerivedObj (sections.{u, u} X U) 0).inv =
      sectionsRestrictMap f φ V U h ≫ (sections.{u, u} X U).toRightDerivedZero.app F := by
    rw [I.toRightDerivedZero_eq (sections.{u, u} Y V),
      J.toRightDerivedZero_eq (sections.{u, u} X U)]
    exact conj_zero_rearrange _ _ _ _ _ _ _ _ _ _ (Iso.inv_hom_id _) hπ
      (toRightDerivedZero'_comp_cyclesMap f φ V U h I J ψ hcomm)
  have key : (I.isoRightDerivedObj (sections.{u, u} Y V) 0).hom ≫
      HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) 0 ≫
        (J.isoRightDerivedObj (sections.{u, u} X U) 0).inv =
      (sections.{u, u} Y V).rightDerivedZeroIsoSelf.hom.app G ≫
        sectionsRestrictMap f φ V U h ≫
          (sections.{u, u} X U).toRightDerivedZero.app F := by
    rw [← hstar, ← Category.assoc, Functor.rightDerivedZeroIsoSelf_hom_inv_id_app,
      Category.id_comp]
  rw [hmeq]
  exact ((conj_assoc eG.hom _ _ _ eF.inv).trans
    (congrArg (fun z ↦ eG.hom ≫ z ≫ eF.inv) key)).trans
      (conj_assoc eG.hom _ _ _ eF.inv).symm

/-! ### The degree-zero identifications carried by a presentation -/

namespace CohomologyCocone

variable {K : Type v} [Category.{v'} K]
  {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E} {O : OpenCone E c}

/-- **In degree zero a presentation identifies its cohomology group at a stage with the group of
sections over the stage open.**  The presentation carries the identification with right-derived
sections as data, and sections over an open are left exact, so the degree-zero right-derived
functor is the functor itself. -/
def zeroObjIso (D : CohomologyCocone E c O 0) (k : K) :
    D.diagram.obj (op k) ≅ (sections.{u, u} (E.obj k) (O.obj k)).obj (E.obj k).sheaf :=
  D.objIso k ≪≫ D.objDerivedIso k ≪≫
    ((sections.{u, u} (E.obj k) (O.obj k)).rightDerivedZeroIsoSelf).app _

/-- The same identification on the cone point. -/
def zeroVertexIso (D : CohomologyCocone E c O 0) :
    Sheaf.H'.{u, u, u} c.pt.sheaf 0 O.pt ≅ (sections.{u, u} c.pt O.pt).obj c.pt.sheaf :=
  D.vertexDerivedIso ≪≫ ((sections.{u, u} c.pt O.pt).rightDerivedZeroIsoSelf).app _

/-- **In degree zero the arrows of a presentation are the maps on sections.** -/
theorem zeroObjIso_naturality (D : CohomologyCocone E c O 0) {j i : K} (a : j ⟶ i) :
    D.diagram.map a.op ≫ (D.zeroObjIso j).hom =
      (D.zeroObjIso i).hom ≫ sectionsRestrictMap (E.map a).hom.base (sheafMap (E.map a))
        (O.obj i) (O.obj j) (O.map_le a) :=
  conj_nat (D.objIso i) (D.objDerivedIso i) _ (D.objIso j) (D.objDerivedIso j) _ _ _
    (IsCohomologyMap.eq_sectionsRestrictMap _ _ _ _ _ _ _ (D.map_eq a))

/-- **In degree zero the legs of a presentation are the maps on sections.** -/
theorem zeroIota_comp (D : CohomologyCocone E c O 0) (k : K) :
    D.ι.app (op k) ≫ D.zeroVertexIso.hom =
      (D.zeroObjIso k).hom ≫ sectionsRestrictMap (c.π.app k).hom.base (sheafMap (c.π.app k))
        (O.obj k) O.pt (O.leg_le k) :=
  conj_leg (D.objIso k) (D.objDerivedIso k) _ D.vertexDerivedIso _ _ _
    (IsCohomologyMap.eq_sectionsRestrictMap _ _ _ _ _ _ _ (D.ι_eq k))

end CohomologyCocone

/-! ### The quasi-compact-open clause in degree zero, unconditionally -/

namespace SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **An arrow of the stage system, read over a fixed open, is a map on sections.**  This is
`abelianStageFunctor_map_eq` with the `f`-map and the restriction packaged as
`sectionsRestrictMap`. -/
theorem stageSystem_map_app_eq_sectionsRestrictMap (i : J) (U : Opens (S.E.obj i))
    {A B : (Over i)ᵒᵖ} (a : A ⟶ B) :
    ((S.stageSystem i).map a).app (op U) =
      sectionsRestrictMap (S.E.map a.unop.left).hom.base (sheafMap (S.E.map a.unop.left))
        ((Opens.map (S.E.map A.unop.hom).hom.base).obj U)
        ((Opens.map (S.E.map B.unop.hom).hom.base).obj U)
        (S.mapOpen_le a.unop U) :=
  S.abelianStageFunctor_map_eq U a

/-- **A leg of the comparison cocone of the stage system, read over a fixed open, is a map on
sections.** -/
theorem stageLeg_app_eq_sectionsRestrictMap (c : Cone S.E) {i : J} (A : Over i)
    (U : Opens (S.E.obj i)) :
    (S.stageLeg c A).app (op U) =
      sectionsRestrictMap (c.π.app A.left).hom.base (sheafMap (c.π.app A.left))
        ((Opens.map (S.E.map A.hom).hom.base).obj U)
        ((Opens.map (c.π.app i).hom.base).obj U) (S.legOpen_le c A U) := rfl

/-- **In degree zero the cohomology diagram of a presentation over a stage open is the stage
system of sections.**  Its components are the degree-zero identifications of the presentation and
its naturality is `CohomologyCocone.zeroObjIso_naturality`. -/
def degreeZeroDiagramIso (c : Cone S.E) (i : J) (U : Opens (S.E.obj i))
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) 0) :
    D.diagram ≅ S.stageSystem i ⋙
      (evaluation (Opens ↥(S.E.obj i : TopCat.{u}))ᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents (fun A ↦ D.zeroObjIso A.unop) fun {A _B} a ↦
    (D.zeroObjIso_naturality a.unop).trans
      (congrArg (fun z ↦ (D.zeroObjIso A.unop).hom ≫ z)
        (S.stageSystem_map_app_eq_sectionsRestrictMap i U a).symm)

/-- **The quasi-compact-open clause of Stacks 0A37 in degree zero, unconditionally**: every
presentation of the cohomology cocone over a quasi-compact open `U` of a stage is a colimit cocone
in degree `0`, with no hypothesis on the stage sheaves.

In degree zero the cohomology diagram is the stage system of sections and the cohomology on the
cone point is the sections on the cone point, by `degreeZeroDiagramIso` and
`CohomologyCocone.zeroVertexIso`; the legs match by `CohomologyCocone.zeroIota_comp`.  So the
statement is abelian Stacks 0A33 on the vertex of the limiting cone,
`isStageSectionsColimit`. -/
theorem nonempty_isColimit_cohomologyCocone_zero (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i)))
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) 0) :
    Nonempty (IsColimit D.cocone) := by
  obtain ⟨ht⟩ := S.isStageSectionsColimit c hc i U hU
  refine ⟨IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (S.degreeZeroDiagramIso c i U D) _).symm ht)
    (Cocone.ext D.zeroVertexIso.symm fun A ↦ ?_)⟩
  exact (congrArg (fun z ↦ z ≫ D.zeroVertexIso.inv) (D.zeroIota_comp A.unop).symm).trans
    (((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ D.ι.app (op A.unop) ≫ z) D.zeroVertexIso.hom_inv_id)).trans
        (Category.comp_id _))

/-- **The quasi-compact-open colimit comparison of Stacks 0A37 in degree zero**: for a limiting
cone of the system, a stage `i` and a quasi-compact open of that stage, the comparison is an
isomorphism in degree `0`.  Every degree is `SpectralAbelianSheafSystem.isIso_comparison`. -/
theorem isIso_comparison_zero (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i)))
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) 0) :
    IsIso D.comparison :=
  CohomologyCocone.isIso_comparison_of_isColimit D
    (S.nonempty_isColimit_cohomologyCocone_zero c hc i U hU D).some

/-- **The global colimit comparison of Stacks 0A37 in degree zero**: `H⁰(X, 𝓕) = colim H⁰(Xᵢ, 𝓕ᵢ)`.
Every degree is `SpectralAbelianSheafSystem.isIso_comparison_global`. -/
theorem isIso_comparison_global_zero (c : Cone S.E) (hc : IsLimit c)
    (D : CohomologyCocone S.E c (S.globalOpenCone c) 0) : IsIso D.comparison :=
  S.isIso_comparison_global_of_stage c 0
    (fun i U hU D' ↦ S.isIso_comparison_zero c hc i U hU D') D

/-! ### Every degree for a system of injective sheaves -/

/-- **The quasi-compact-open colimit comparison in every degree, for a system of injective
sheaves.**  Degree zero is `isIso_comparison_zero`; positive degree is
`isIso_comparison_of_injective'`, where both sides of the comparison are zero objects.  The
comparison for an arbitrary system is `SpectralAbelianSheafSystem.isIso_comparison`. -/
theorem isIso_comparison_of_injective_of_degree (c : Cone S.E) (hc : IsLimit c)
    (hinj : ∀ k, Injective (S.E.obj k).sheaf) (i : J) (U : Opens (S.E.obj i))
    (hU : IsCompact (U : Set (S.E.obj i))) (p : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p) :
    IsIso D.comparison := by
  cases p with
  | zero => exact S.isIso_comparison_zero c hc i U hU D
  | succ n => exact S.isIso_comparison_of_injective' c hc hinj i U hU n D

/-- **The global colimit comparison in every degree, for a system of injective sheaves.**  The
comparison for an arbitrary system is `SpectralAbelianSheafSystem.isIso_comparison_global`. -/
theorem isIso_comparison_global_of_injective (c : Cone S.E) (hc : IsLimit c)
    (hinj : ∀ k, Injective (S.E.obj k).sheaf) (p : ℕ)
    (D : CohomologyCocone S.E c (S.globalOpenCone c) p) : IsIso D.comparison :=
  S.isIso_comparison_global_of_stage c p
    (fun i U hU D' ↦ S.isIso_comparison_of_injective_of_degree c hc hinj i U hU p D') D

end SpectralAbelianSheafSystem

/-! ### A non-degenerate instance in degree zero

A system whose degree-zero cohomology is `ℤ`: the constant diagram over the one-object category at
the one-point space carrying the skyscraper sheaf of value `ℤ`, whose sections are `ℤ` over the
whole space and terminal over `⊥`.  At it both degree-zero comparisons are isomorphisms of non-zero
groups. -/

namespace SpectralAbelianSheafSystem

/-- Membership of the point of the one-point space in an open is decidable, classically.  The
skyscraper presheaf is defined by a case split on it.  Kept **local**: a global `Decidable`
instance produced by `Classical.propDecidable` is visible to every importer and nothing outside
this section needs it. -/
local instance decidableMemOpensUnit (U : Opens (TopCat.of Unit)) :
    Decidable ((() : TopCat.of Unit) ∈ U) :=
  Classical.propDecidable _

/-- The one-point space carrying the skyscraper sheaf of value `A`: sections `A` over the whole
space, a terminal object over `⊥`. -/
def skyscraperPtSpace (A : AddCommGrpCat.{0}) : SheafedSpace.{1, 0, 0} AddCommGrpCat.{0} where
  carrier := TopCat.of Unit
  presheaf := skyscraperPresheaf (X := TopCat.of Unit) () A
  IsSheaf := skyscraperPresheaf_isSheaf _ _

/-- The constant diagram at `skyscraperPtSpace A` over the one-object category, as a spectral
abelian sheaf system.  The one-point space is spectral and every transition map is the identity,
which is a spectral map. -/
def skyscraperPtSystem (A : AddCommGrpCat.{0}) : SpectralAbelianSheafSystem.{0, 0, 0} Unit where
  E := (Functor.const Unit).obj (skyscraperPtSpace A)
  spectralSpace _ := instSpectralSpaceUnit
  spectralMap _ := isSpectralMap_id

/-- The identity cone on the constant diagram at `skyscraperPtSpace A`. -/
def skyscraperPtCone (A : AddCommGrpCat.{0}) : Cone (skyscraperPtSystem A).E where
  pt := skyscraperPtSpace A
  π := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ rfl }

/-- The identity cone on a constant diagram over the one-object category is limiting. -/
def isLimit_skyscraperPtCone (A : AddCommGrpCat.{0}) : IsLimit (skyscraperPtCone A) where
  lift s := s.π.app ()
  fac s j := by cases j; exact Category.comp_id _
  uniq s m h := (Category.comp_id m).symm.trans (h ())

/-- A presentation of the global cohomology cocone of the skyscraper system in degree zero. -/
def skyscraperCohomologyCocone (A : AddCommGrpCat.{0}) :
    CohomologyCocone (skyscraperPtSystem A).E (skyscraperPtCone A)
      ((skyscraperPtSystem A).globalOpenCone (skyscraperPtCone A)) 0 :=
  ((skyscraperPtSystem A).nonempty_globalCohomologyCocone (skyscraperPtCone A)
    (isLimit_skyscraperPtCone A) 0).some

/-- The group of sections on the vertex of the global clause at the skyscraper system of value
`A` **is** `A`: the open is the whole space, which contains the point. -/
theorem sections_skyscraperPtSpace_top (A : AddCommGrpCat.{0}) :
    A = (sections.{0, 0} (skyscraperPtCone A).pt
      ((skyscraperPtSystem A).globalOpenCone (skyscraperPtCone A)).pt).obj
        (skyscraperPtCone A).pt.sheaf := by
  show _ = (skyscraperPresheaf (X := TopCat.of Unit) () A).obj (op ⊤)
  simp [skyscraperPresheaf]

/-- **The sections group on the vertex of the global clause is not a zero object** at the
skyscraper system of value `ℤ`. -/
theorem not_isZero_sections_skyscraperPtSpace :
    ¬ IsZero ((sections.{0, 0} (skyscraperPtCone (AddCommGrpCat.of ℤ)).pt
      ((skyscraperPtSystem (AddCommGrpCat.of ℤ)).globalOpenCone
        (skyscraperPtCone (AddCommGrpCat.of ℤ))).pt).obj
          (skyscraperPtCone (AddCommGrpCat.of ℤ)).pt.sheaf) := fun h ↦
  have : Subsingleton (AddCommGrpCat.of ℤ) :=
    AddCommGrpCat.subsingleton_of_isZero
      (h.of_iso (eqToIso (sections_skyscraperPtSpace_top (AddCommGrpCat.of ℤ))))
  absurd (Subsingleton.elim (0 : ℤ) 1) (by decide)

/-- **The degree-zero cohomology group that the global clause of Stacks 0A37 compares is not a
zero object** at the skyscraper system of value `ℤ`.  In degree zero a presentation identifies
that group with the sections on the vertex (`CohomologyCocone.zeroVertexIso`), which is `ℤ`. -/
theorem not_isZero_H_skyscraperPtSystem :
    ¬ IsZero (Sheaf.H'.{0, 0, 0} (skyscraperPtCone (AddCommGrpCat.of ℤ)).pt.sheaf 0
      ((skyscraperPtSystem (AddCommGrpCat.of ℤ)).globalOpenCone
        (skyscraperPtCone (AddCommGrpCat.of ℤ))).pt) := fun h ↦
  not_isZero_sections_skyscraperPtSpace
    (h.of_iso (skyscraperCohomologyCocone (AddCommGrpCat.of ℤ)).zeroVertexIso.symm)

/-- **The global degree-zero colimit comparison of Stacks 0A37 at the skyscraper system**: an
isomorphism between groups that `not_isZero_H_skyscraperPtSystem` shows are not zero. -/
theorem isIso_comparison_skyscraperPtSystem :
    IsIso (skyscraperCohomologyCocone (AddCommGrpCat.of ℤ)).comparison :=
  (skyscraperPtSystem (AddCommGrpCat.of ℤ)).isIso_comparison_global_zero
    (skyscraperPtCone (AddCommGrpCat.of ℤ)) (isLimit_skyscraperPtCone (AddCommGrpCat.of ℤ))
    (skyscraperCohomologyCocone (AddCommGrpCat.of ℤ))

/-- **The quasi-compact-open degree-zero colimit comparison of Stacks 0A37 at the skyscraper
system**, at the stage `i = ()` and the quasi-compact open `U = ⊤`.  The presentation is the global
one restricted along `Over.forget ()`, whose open cone is the stage open cone at `⊤` by
`globalOpenCone_whisker`; restriction does not move the vertex, so the group being compared is the
one `not_isZero_H_skyscraperPtSystem` shows is not zero. -/
theorem isIso_comparison_zero_skyscraperPtSystem :
    IsIso (((skyscraperCohomologyCocone (AddCommGrpCat.of ℤ)).whisker
      (Over.forget (() : Unit))).comparison) :=
  (skyscraperPtSystem (AddCommGrpCat.of ℤ)).isIso_comparison_zero
    (skyscraperPtCone (AddCommGrpCat.of ℤ)) (isLimit_skyscraperPtCone (AddCommGrpCat.of ℤ))
    () ⊤ ((skyscraperPtSystem (AddCommGrpCat.of ℤ)).isCompact_top ()) _

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end
