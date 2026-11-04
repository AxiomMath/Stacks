module

public import StacksFrontier.AlgebraicGeometry.Spaces.AssociatedModuleChartPushTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDefiningIdeal
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The ideal-sheaf comparison of a represented closed immersion, read against the inclusions

Let `B` be a big fppf site containing a scheme `S`, let `V` be an object of the big fppf category
over `S` and let `j : R ⟶ V` be a morphism whose underlying morphism of schemes is a closed
immersion.  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` identifies the
defining ideal sheaf of Stacks 03MB of the closed subspace which `j` cuts out with the associated
module of `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes.

Both sides are sheaves of **ideals**, so what a consumer needs is not only that comparison but
that it is compatible with the two inclusions into the two structure sheaves.  That compatibility
is what this file proves, as a morphism-level equation `… ≫ ι = …`.
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` has the same
content in transposed and sections form; the morphism-level form is what the comparison of the
two canonical maps of conormal modules composes with, and the "What part (2) of Stacks 04G2 still
needs" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean` names it as owed.

## Main results

* `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush_comp_restrictModule_map_ι`: **the
  Zariski half, with no hypothesis at all.**  The comparison of the submodule spelling of the
  chart restriction of a sheaf of ideals with its direct-image spelling, followed by the
  restriction of the inclusion `N ⟶ 𝒪`, is the inclusion of the Zariski restriction followed by
  the structure comparison `𝒪_V ⟶ (𝒪 on the small étale site)|_{Zar}`.  True on sections.
* `associatedModuleChartZariskiIdealSheafSelfChartIso_hom_comp_inverse_map_ι`, in the namespace
  `AlgebraicGeometry.Space` and written without the prefix so that it fits: the same one step up,
  on the small étale site of the representing scheme.  It is the Zariski statement transposed
  along the associated-module adjunction of Stacks 03DX.
* `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso_hom_comp_ι`: and
  one step further up, on the small étale site of the representable algebraic space.
* `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι`: **the
  compatibility of the ideal-sheaf comparison with the inclusion into the structure sheaf.**  The
  comparison followed by the inclusion of the defining ideal sheaf is the associated module of
  `Stacks.ClosedImmersion.idealSheafι` followed by
  `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`, the identification of the
  associated module of `𝒪_V` with the structure sheaf of the algebraic space.

## Route

Nothing here computes a value of a comparison built from a universal property, and the three
steps are the three layers the comparison is assembled from.

The Zariski statement is an equality of two morphisms of sheaves of modules on the small Zariski
site of the representing scheme, where both sides have sections: each sends a section of the
sheaf of ideals over a Zariski open `W` to its image under the comparison of scalars
`AlgebraicGeometry.Space.chartSectionsRingHom`, which for the identity chart is *defined* as the
structure comparison of the small étale site followed by the structure map of the inverse of the
comparison of the two small étale sites, and the latter is the identity.  So it holds by `rfl` on
sections.

The passage to the small étale site of the representing scheme is the only step with content, and
it is a statement about two morphisms **out of** an associated module, hence determined by their
transposes along the associated-module adjunction of Stacks 03DX.  The transpose of the left-hand
side is
`unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom`
of `AlgebraicGeometry.Space`; the transpose of the right-hand side is
`AlgebraicGeometry.SmallEtale.associatedModule` of the inclusion followed by the canonical map
`𝒪^a ⟶ 𝒪`, whose transpose is the structure comparison by Mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` of
`CategoryTheory.SheafOfModules`.  The comparison of the two transposes is exactly the Zariski
statement.

The passage to the small étale site of the algebraic space is the transport along the comparison
equivalence of the two small étale sites.  Its counit intervenes, and it **cancels**: the counit
at the structure sheaf is the identity
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_counitIso_app_unit`), so the
naturality of the counit at the inclusion `N ⟶ 𝒪` turns the counit correction into nothing.

## Implementation notes

Every structural step is an instantiation of a lemma of `CategoryTheory` stated at variables, and
each of those lemmas takes the morphisms it composes as **implicit** arguments determined by its
hypotheses.  That is forced, and it is the single measurement this file rests on: with the two
transposes passed as explicit arguments — that is, with the right-hand side of each hypothesis
restated at the geometric instance —
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso_hom_comp_inverse_map_ι`
exhausts the `isDefEq` budget; with them implicit, so that no argument at the instantiation is a
restatement, the whole file checks in about eight seconds.

For the same reason, each named comparison is carried to the composite it is defined as **as an
isomorphism** and never through its `hom` component, and the `hom` is projected only inside
`CategoryTheory.Functor.mapIso_trans_hom_comp_of_eq`, where the categories are variables.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` record what the
component-level spelling costs here.

`CategoryTheory.Equivalence.counitIso_hom_app_comp_of_eq` takes the value of the counit at the
target as an explicit morphism with an equation, rather than asserting it to be an identity: the
counit of an equivalence is not an identity in general, and the type
`(E.inverse ⋙ E.functor).obj M ≅ (𝟭 _).obj M` of its component admits the statement `= Iso.refl M`
only where the two objects happen to agree, which is the geometric fact at the structure sheaf
and not something a generic lemma may assume.

No declaration here carries a `stacks` tag.  The compatibility of an ideal-sheaf comparison with
the inclusions is a step of the proof of part (2) of Stacks 04G2, not an assertion of it.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2), whose counit
  isomorphism the chart comparison is built from.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the
  associated-module functor and its adjunction.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (2), whose
  reduction to the closed case consumes this.
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the schemes-side ideal
  sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Two composites agree when their transposes do.**  For an adjunction `F ⊣ G`, a composite
`a ≫ b` out of `F.obj X` is `F.map k ≫ g` as soon as the transpose of `a` is `t`, the transpose of
`g` is `s`, and `t ≫ G.map b = k ≫ s`.

The two transposes are **implicit**, determined by the hypotheses naming them; a consumer
therefore supplies three existing lemmas and restates nothing.  That is what makes this usable at
a geometric instance — see the implementation notes of this file. -/
theorem Adjunction.comp_eq_map_comp_of_transposes {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X X' : C} {Y Y' : D} {a : F.obj X ⟶ Y} (b : Y ⟶ Y') {k : X ⟶ X'} {g : F.obj X' ⟶ Y'}
    {t : X ⟶ G.obj Y} (ht : adj.unit.app X ≫ G.map a = t)
    {s : X' ⟶ G.obj Y'} (hs : adj.unit.app X' ≫ G.map g = s)
    (key : t ≫ G.map b = k ≫ s) :
    a ≫ b = F.map k ≫ g := by
  refine (adj.homEquiv X Y').injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    G.map_comp, ← Category.assoc, ht, hs]
  exact key

/-- **A composite out of an isomorphism which factors through the image of an isomorphism.**  If
`Ψ` is `F.mapIso θ` followed by `ρ`, and `ρ.hom ≫ h` is `F.map m`, then `Ψ.hom ≫ h` is `F.map` of
`θ.hom ≫ m`.

`Ψ` is given by name with a hypothesis identifying it with the composite, so that the projection
of `hom` out of that composite happens here, where the two categories are variables, and not at
the geometric instance; see the implementation notes. -/
theorem Functor.mapIso_trans_hom_comp_of_eq (F : C ⥤ D) {Z Z₀ W : C} {Y : D}
    (θ : Z ≅ Z₀) (ρ : F.obj Z₀ ≅ Y) (Ψ : F.obj Z ≅ Y) (hΨ : Ψ = F.mapIso θ ≪≫ ρ)
    (h : Y ⟶ F.obj W) {m : Z₀ ⟶ W} (hρ : ρ.hom ≫ h = F.map m)
    {c : Z ⟶ W} (hc : θ.hom ≫ m = c) :
    Ψ.hom ≫ h = F.map c := by
  subst hΨ; subst hc
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hρ, ← F.map_comp]

/-- **The counit of an equivalence moved past a morphism.**  For `h : M ⟶ M'` the counit at `M`
followed by `h` is the image under the equivalence of the image under its inverse of `h`,
followed by the counit at `M'`; this is the naturality of the counit, with the component at `M'`
named by a hypothesis.

The component is named rather than asserted to be an identity: the counit of an equivalence is
not an identity in general, so a generic statement cannot write `= 𝟙 M'` there. -/
theorem Equivalence.counitIso_hom_app_comp_of_eq (E : C ≌ D) {M M' : D} (h : M ⟶ M')
    (v : E.functor.obj (E.inverse.obj M') ⟶ M') (hv : E.counitIso.hom.app M' = v) :
    E.counitIso.hom.app M ≫ h = E.functor.map (E.inverse.map h) ≫ v := by
  have hnat := E.counitIso.hom.naturality h
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [← hv, ← hnat]

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- **The transpose of the canonical map `𝒪^a ⟶ 𝒪` of the small étale site is the structure
comparison.**  The unit of the associated-module adjunction of Stacks 03DX at the structure sheaf
of the scheme, followed by the restriction of
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` of the structure map of the small étale
ringed site, is `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of that structure map.

This is Mathlib's
`CategoryTheory.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` with
the hom-set bijection written out, stated at
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` so that a consumer matches it against
that adjunction structurally. -/
theorem unit_comp_restrictModule_map_pullbackObjUnitToUnit :
    (associatedModuleAdjunction B T hT).unit.app (SheafOfModules.unit T.ringCatSheaf) ≫
        (restrictModule B T hT).map
          (SheafOfModules.pullbackObjUnitToUnit (structureMap B T hT)) =
      SheafOfModules.unitToPushforwardObjUnit (structureMap B T hT) :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit (structureMap B T hT)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-- **The identification of the associated module of `𝒪_V` with the structure sheaf of the
representable algebraic space is the canonical map `𝒪^a ⟶ 𝒪` of the small étale site of the
representing scheme, transported.**  The second factor of
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` is
`CategoryTheory.Iso.refl`, so only the first survives. -/
theorem representedAssociatedModuleObjUnitIso_hom :
    (representedAssociatedModuleObjUnitIso B S hS V
        (isAlgebraicSpace_yoneda B S hS V)).hom =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        (SheafOfModules.pullbackObjUnitToUnit
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) :=
  Category.comp_id _

/-- **The counit of the comparison equivalence moved past a morphism into the structure sheaf.**
For `h : M ⟶ 𝒪` the counit of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` at `M` followed by `h` is the
image under the equivalence of the image under its inverse of `h`, with no counit correction
left: the counit at the structure sheaf is the identity, by
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_counitIso_app_unit`. -/
theorem representedSmallEtaleModuleEquivalence_counitIso_hom_app_comp
    {M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)}
    (h : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    (representedSmallEtaleModuleEquivalence B S hS V).counitIso.hom.app M ≫ h =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map h) :=
  (CategoryTheory.Equivalence.counitIso_hom_app_comp_of_eq
      (representedSmallEtaleModuleEquivalence B S hS V) h (CategoryStruct.id _)
      (congrArg Iso.hom
        (representedSmallEtaleModuleEquivalence_counitIso_app_unit B S hS (T := V)))).trans
    (Category.comp_id _)

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS
  ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)

/-! ### The Zariski half -/

/-- **The comparison of the two spellings of the chart restriction of a sheaf of ideals is
compatible with the inclusions into the two structure sheaves**, with no hypothesis on the sheaf
of ideals.

`AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush` at the identity chart, followed by
the transport of `AlgebraicGeometry.Space.chartPush_selfChart` and then by the Zariski
restriction of the inclusion `N ⟶ 𝒪`, is the inclusion of
`AlgebraicGeometry.Space.chartZariskiIdealSheaf` into `𝒪_V` followed by the structure comparison
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of the small étale ringed site.

Both sides have sections, and over a Zariski open `W` both send a section of the sheaf of ideals
to its image under the comparison of scalars
`AlgebraicGeometry.Space.chartSectionsRingHom`, which at the identity chart *is* the structure
comparison — the remaining factor of its definition, the structure map of the inverse of the
comparison of the two small étale sites, being the identity.  So the statement holds by `rfl` on
sections. -/
theorem chartZariskiIdealSheafIsoChartPush_comp_restrictModule_map_ι :
    ((chartZariskiIdealSheafIsoChartPush B S hS
              ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)).hom ≫
            eqToHom (chartPush_selfChart B S hS V N.toSheafOfModules)) ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              (chartScheme (selfChart B S hS V))
              (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (selfChart B S hS V)).left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map N.ι) =
        (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
            (selfChart B S hS V)).ι ≫
          SheafOfModules.unitToPushforwardObjUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property) := by
  ext W x
  rfl

variable (hN : N.toSheafOfModules.IsQuasicoherentOnSite)

/-! ### On the small étale site of the representing scheme -/

/-- **The comparison of a sheaf of ideals with the associated module of its Zariski restriction
is compatible with the inclusions**, on the small étale site of the representing scheme.

Both sides are morphisms out of an associated module, hence determined by their transposes along
the associated-module adjunction of Stacks 03DX, and the two transposes are the two sides of
`AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush_comp_restrictModule_map_ι`. -/
theorem associatedModuleChartZariskiIdealSheafSelfChartIso_hom_comp_inverse_map_ι :
    (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS V).inverse.map N.ι =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
            (selfChart B S hS V)).ι ≫
        SheafOfModules.pullbackObjUnitToUnit
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :=
  CategoryTheory.Adjunction.comp_eq_map_comp_of_transposes
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property)
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map N.ι)
    (unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom
      B S hS V N hN)
    (_root_.AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_pullbackObjUnitToUnit
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (chartZariskiIdealSheafIsoChartPush_comp_restrictModule_map_ι B S hS V N)

/-! ### On the small étale site of the representable algebraic space -/

/-- **The comparison of a sheaf of ideals with the associated module of its Zariski restriction
is the comparison on the representing scheme transported, followed by the counit of the
comparison equivalence**, by `rfl`: that is how
`AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso` is defined.

Stated as an equality of *isomorphisms*; the corresponding equality of `hom` components is what
the implementation notes of this file and of
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` record as
unaffordable. -/
theorem representedAssociatedModuleChartZariskiIdealSheafIso_eq :
    representedAssociatedModuleChartZariskiIdealSheafIso B S hS V N hN =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.mapIso
          (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN) ≪≫
        (representedSmallEtaleModuleEquivalence B S hS V).counitIso.app N.toSheafOfModules :=
  rfl

/-- **The comparison of a sheaf of ideals of a representable algebraic space with the associated
module of its Zariski restriction is compatible with the inclusions.**  The comparison followed
by the inclusion `N ⟶ 𝒪` is the transport of the associated module of the Zariski inclusion
followed by the canonical map `𝒪^a ⟶ 𝒪`.

The counit correction of the comparison cancels: it is the identity at the structure sheaf. -/
theorem representedAssociatedModuleChartZariskiIdealSheafIso_hom_comp_ι :
    (representedAssociatedModuleChartZariskiIdealSheafIso B S hS V N hN).hom ≫ N.ι =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
              (selfChart B S hS V)).ι ≫
          SheafOfModules.pullbackObjUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) :=
  CategoryTheory.Functor.mapIso_trans_hom_comp_of_eq
    (W := SheafOfModules.unit (representedSchemeStructureSheaf B S hS V))
    (representedSmallEtaleModuleEquivalence B S hS V).functor
    (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN)
    ((representedSmallEtaleModuleEquivalence B S hS V).counitIso.app N.toSheafOfModules)
    (representedAssociatedModuleChartZariskiIdealSheafIso B S hS V N hN)
    (representedAssociatedModuleChartZariskiIdealSheafIso_eq B S hS V N hN) N.ι
    (representedSmallEtaleModuleEquivalence_counitIso_hom_app_comp B S hS V N.ι)
    (associatedModuleChartZariskiIdealSheafSelfChartIso_hom_comp_inverse_map_ι B S hS V N hN)

/-! ### The ideal sheaf of a represented closed immersion -/

variable {R : BigFppfOver B S hS} (j : R ⟶ V)
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- The inclusion of `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes,
read back through the identification of that ideal sheaf with the Zariski restriction of the
defining ideal sheaf.  This is
`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι` with the
isomorphism moved to the other side. -/
theorem idealSheafι_eq_chartZariskiIdealSheafSelfChartIsoIdealSheaf_inv_comp_ι :
    Stacks.ClosedImmersion.idealSheafι
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom =
      (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).inv ≫
        (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (closedSubspaceRange B S hS j hj))
          (selfChart B S hS V)).ι :=
  (Iso.inv_hom_id_assoc (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj)
        (Stacks.ClosedImmersion.idealSheafι
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).symm.trans
    (congrArg (fun t => (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).inv ≫ t)
      (chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι B S hS V j hj))

/-- The preceding identification carried through the associated-module functor and reassociated
against the canonical map `𝒪^a ⟶ 𝒪`.  Its own declaration, so that the reassociation does not
share a heartbeat budget with the two steps around it. -/
theorem associatedModule_map_chartZariskiIdealSheafSelfChartIsoIdealSheaf_inv_comp :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).inv ≫
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                  (closedSubspaceRange B S hS j hj))
                (selfChart B S hS V)).ι ≫
            SheafOfModules.pullbackObjUnitToUnit
              (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          (Stacks.ClosedImmersion.idealSheafι
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
        SheafOfModules.pullbackObjUnitToUnit
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ SheafOfModules.pullbackObjUnitToUnit
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
      (CategoryTheory.Functor.map_comp_of_eq
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
        (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).inv
        (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (closedSubspaceRange B S hS j hj))
          (selfChart B S hS V)).ι
        (Stacks.ClosedImmersion.idealSheafι
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
        (idealSheafι_eq_chartZariskiIdealSheafSelfChartIsoIdealSheaf_inv_comp_ι
          B S hS V j hj)))

/-- **The ideal-sheaf comparison is the transport of the associated module of the Zariski
identification followed by the comparison of a sheaf of ideals with the associated module of its
Zariski restriction**, by `rfl`: that is how
`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` is defined.  Stated as an
equality of isomorphisms. -/
theorem representedAssociatedModuleIdealSheafIso_eq :
    representedAssociatedModuleIdealSheafIso B S hS V j hj =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.mapIso
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
            (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj)).symm ≪≫
        representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
          (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (closedSubspaceRange B S hS j hj))
          (isQuasicoherentOnSite_definingIdealSheaf B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (closedSubspaceRange B S hS j hj)) :=
  rfl

/-- `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι` with the
canonical map `𝒪^a ⟶ 𝒪` kept inside the transport, which is the shape the generic step produces.
Its own declaration, so that the two steps do not share a heartbeat budget. -/
theorem representedAssociatedModuleIdealSheafIso_hom_comp_ι_comp :
    (representedAssociatedModuleIdealSheafIso B S hS V j hj).hom ≫
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).ι =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              (Stacks.ClosedImmersion.idealSheafι
                ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
          SheafOfModules.pullbackObjUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) :=
  CategoryTheory.Functor.mapIso_trans_hom_comp_of_eq
    (W := SheafOfModules.unit (representedSchemeStructureSheaf B S hS V))
    (representedSmallEtaleModuleEquivalence B S hS V).functor
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
      (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj)).symm
    (representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))
      (isQuasicoherentOnSite_definingIdealSheaf B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (closedSubspaceRange B S hS j hj)))
    (representedAssociatedModuleIdealSheafIso B S hS V j hj)
    (representedAssociatedModuleIdealSheafIso_eq B S hS V j hj)
    (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
      (closedSubspaceRange B S hS j hj)).ι
    (representedAssociatedModuleChartZariskiIdealSheafIso_hom_comp_ι B S hS V
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))
      (isQuasicoherentOnSite_definingIdealSheaf B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (closedSubspaceRange B S hS j hj)))
    (associatedModule_map_chartZariskiIdealSheafSelfChartIsoIdealSheaf_inv_comp B S hS V j hj)

/-- **The ideal-sheaf comparison of a represented closed immersion is compatible with the
inclusion into the structure sheaf.**

`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` followed by the inclusion of
the defining ideal sheaf of Stacks 03MB of the closed subspace which `j` cuts out is the
transport of the associated module of `Stacks.ClosedImmersion.idealSheafι` — the inclusion of the
schemes-side ideal sheaf into `𝒪_V` — followed by
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`, the identification of the
associated module of `𝒪_V` with the structure sheaf of the algebraic space.

So the comparison is an identification of sheaves of *ideals* and not merely of modules.  This is
the morphism-level form of the compatibility that
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` carries in
transposed and sections form, and it is what the comparison of the two canonical maps of conormal
modules in part (2) of Stacks 04G2 composes with on the ambient space, where both inclusions are
monomorphisms. -/
theorem representedAssociatedModuleIdealSheafIso_hom_comp_ι :
    (representedAssociatedModuleIdealSheafIso B S hS V j hj).hom ≫
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).ι =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            (Stacks.ClosedImmersion.idealSheafι
              ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≫
        (representedAssociatedModuleObjUnitIso B S hS V
          (isAlgebraicSpace_yoneda B S hS V)).hom :=
  (representedAssociatedModuleIdealSheafIso_hom_comp_ι_comp B S hS V j hj).trans
    ((CategoryTheory.Functor.map_comp_of_eq
          (representedSmallEtaleModuleEquivalence B S hS V).functor
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
            (Stacks.ClosedImmersion.idealSheafι
              ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))
          (SheafOfModules.pullbackObjUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) _ rfl).symm.trans
      (congrArg (fun t => (representedSmallEtaleModuleEquivalence B S hS V).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              (Stacks.ClosedImmersion.idealSheafι
                ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≫ t)
        (representedAssociatedModuleObjUnitIso_hom B S hS V).symm))

end AlgebraicGeometry.Space

end
