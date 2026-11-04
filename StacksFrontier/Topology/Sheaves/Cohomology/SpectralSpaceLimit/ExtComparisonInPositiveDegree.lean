module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInDegreeZero

/-!
# The `Ext`-side comparison map of Tag 0A37 on injective resolutions, in positive degree

`Stacks.Cohomology.ExtComparison.extSpacePullbackMap_zero_eq` identifies the `Ext`-side
comparison arrow of Stacks 0A37 with the arrow
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` prescribes **in degree zero**, for the
canonical identifications of cohomology with right-derived sections.  What stood between that and
positive degree is one piece of homological algebra: a *resolution-level* formula for
`Stacks.Cohomology.ModuleComparison.extMapComp` -- the `Ext`-level map
`e ↦ Ext.mk₀ b ∘ (F e)` -- conjugated by
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` on both sides.  **This file supplies it.**

The lemma `Stacks.Cohomology.ModuleComparison.comparisonIso_hom_app_succ_eq` is the same formula
for the special case of Stacks 03FD, and it is read off through
`Stacks.Cohomology.ModuleComparison.compCorepresentation`: there the *source* `δ`-functor is the
right-derived functors of `F ⋙ G`, corepresented by `Y`.  That is exactly what Stacks 0A37 does
not have -- sections over `V` on the target space are not sections over `U` of the inverse image,
`U` being a strictly smaller open of a different space -- so the source has to be read through a
corepresentation of its own, which is what the statements below do.

## Main definitions

* `collapse₅`, the reassociation helper for the five-fold composite of the abstract part.
* `pushforwardAdjunctComplex`: the adjunct, under the inverse-image/direct-image adjunction, of a
  cochain map out of the inverse image of a complex -- the datum
  `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` asks for, built from the datum the `Ext`-side
  description produces.

## Main results

* `extCocycleComp_comp_i_of_corepresentation` and
  `extCocycleComp_comp_cyclesMap_of_corepresentation`: the cocycle transport
  `Stacks.Cohomology.ModuleComparison.extCocycleComp` is the chain map `φ` composed with the two
  corepresentations, read through the inclusions of the cocycles and then on cycles.  These
  generalize
  `Stacks.Cohomology.ModuleComparison.extCocycleComp_comp_i` and `_comp_cyclesMap` from
  `compUnit`/`compCorepresentation` to an arbitrary `b : XA ⟶ F.obj XB` together with
  corepresentations of the two corepresented functors, which is the shape Stacks 0A37 needs.
* `extMapComp_conj_succ`: **the resolution-level reading of the `Ext`-side comparison map in
  positive degree.**  Conjugated by `ModuleSheafCohomology.extFunctorObjIsoRightDerived`, the map
  `e ↦ Ext.mk₀ b ∘ (F e)` is computed on the chosen injective resolutions by the chain map
  `derivedSectionsMap` followed by any comparison `φ` of the image of the resolution upstairs with
  the resolution downstairs extending the identity.  Its degree-zero companion is
  `Stacks.Cohomology.ExtComparison.extMapComp_conj_zero`.
* `sectionsComplexMap_pushforwardAdjunctComplex`: **the two descriptions of the map of section
  complexes agree.**  The map `Stacks.Cohomology.SpectralLimit.sectionsComplexMap` attached to the
  adjunct of a cochain map `χ` is, degreewise, the pullback map on sections followed by `χ`.  This
  is `Stacks.Cohomology.ExtComparison.derivedSectionsMap_comp_eq_sectionsRestrictMap` applied in
  each degree.
* `extSpacePullbackMap_succ_eq`: **in positive degree the `Ext`-side comparison arrow is the arrow
  prescribed by Tag 0A37**, for the canonical identifications; the positive-degree companion of
  `Stacks.Cohomology.ExtComparison.extSpacePullbackMap_zero_eq`.
* `isCohomologyMap_extSpacePullbackMap`: **the identification Tag 0A37 asks for, in every
  degree.**  This is `Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap_zero`
  with `0` replaced by an arbitrary `p`, and it is what was open about the `Ext`-side description
  of the comparison arrows.

## Implementation notes

Everything here is at the abstract spelling -- two abelian categories, an exact functor between
them, two left exact functors to abelian groups with corepresentations -- and so none of the
`TopCat.Sheaf`-versus-`Sheaf` crossings that the implementation notes of
`Stacks.Cohomology.ExtComparison.extSpacePullbackMap_zero_eq`'s module describe arise.

The assembly is `Stacks.Cohomology.ModuleComparison.extReadingAssemble`, the bracket helper the
proof of Stacks 03FD uses, with `f1` discharged by `rfl` rather than by an `Ext`-level
formula: here the map being read *is* the conjugate, so there is nothing to identify it with
first.  The one new bracket is `collapse₅`: the source side of the comparison now has a fifth
factor, because the corepresentation of the source functor and the map of corepresented functors
are two transformations where `compCorepresentation` was one.

The second half of the file carries out that instantiation. Three inputs are assembled. The
comparison `φ` of the image of the resolution of `G` with the chosen resolution of `f⁻¹ G` is
`Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison`, the inverse image being exact.
The resolution of `f⁻¹ G` is moved onto the chosen resolution of `F` along the adjoint of the
`f`-map by `CategoryTheory.Functor.rightDerived_map_eq`, applied to
`CategoryTheory.InjectiveResolution.desc`. And the resulting cochain map is identified with
`Stacks.Cohomology.SpectralLimit.sectionsComplexMap` degreewise, which is
`Stacks.Cohomology.ExtComparison.derivedSectionsMap_comp_eq_sectionsRestrictMap` applied in each
degree, the `f`-map there being the adjunct of the degree-`k` component.

One point of shape.  `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` asks for a cochain map
`I ⟶ f_* J` into the *direct image* of a resolution downstairs, while the `Ext`-side description
produces a cochain map `f⁻¹ I ⟶ J` out of the *inverse image* of the resolution upstairs.  These
are the same datum, and `pushforwardAdjunctComplex` is the passage: its degree-`k` component is
the adjunct of the degree-`k` component, and the cochain condition is the naturality of the
adjunction unit.

Two spelling notes, each of which cost real heartbeats.  First, nothing below *states* a term of
the form `(extFunctorObj (freeOfOpen U) (n + 1)).map σ` or
`((abSections U).rightDerived (n + 1)).map σ`: at a literal `n + 1` the definition of
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` unfolds through its match, and the unifier
then descends into the derived category rather than comparing arguments.  Every such term is
introduced by `rw` from an *unascribed* `have`, exactly as the degree-zero proof in
`Stacks.Cohomology.ExtComparison.extSpacePullbackMap_zero_eq` does.  Second, the two spellings
`H'isoRightDerivedSections U p` and
`extFunctorObjIsoRightDerived (abSections U) (freeOfOpen U) (repU U) p` are `rfl`-equal but not
the same term, and crossing between them inside a composite is unaffordable at `n + 1`; so the
crossing is paid once, at the level of the isomorphism itself, by
`H'isoRightDerivedSections_eq_repU` and `H'isoRightDerivedSections_eq_repV`, and the conclusion of
`Stacks.Cohomology.ModuleComparison.extMapComp_conj_succ` is rewritten by them before anything is
composed.

The resolution-side object the prescribed arrow could alternatively have been matched against is
`Stacks.Cohomology.RightDerivedEdge.edge`, the edge morphism `Rⁿ Q (P X) ⟶ Rⁿ (Q ∘ P) X` for a
composite with `P` preserving injectives, whose characterisation
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` holds for *any* augmentation-preserving
comparison of *any* injective resolutions.  That route is not taken here: the direct
instantiation above needs no edge morphism.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open ModuleSheafCohomology
open Stacks.Cohomology.ModuleComparison

namespace Stacks.Cohomology.ExtComparison

universe v uA uB

section Collapse

variable {D : Type uA} [Category.{v} D]

/-- Collapsing a five-fold composite against a family of inclusions.  The four-fold version is
`Stacks.Cohomology.ModuleComparison.extReadingCollapse4`; the fifth factor appears
because the source side of the comparison reads through a corepresentation and a map of
corepresented functors where Stacks 03FD reads through one transformation. -/
theorem collapse₅ {O0 O1 O2 O3 O4 O5 V V' V'' W : D}
    (a : O0 ⟶ O1) (b : O1 ⟶ O2) (c : O2 ⟶ O3) (d : O3 ⟶ O4) (e : O4 ⟶ O5) (i : O5 ⟶ W)
    (i4 : O4 ⟶ V'') (i3 : O3 ⟶ V') (i2 : O2 ⟶ V) (i1 : O1 ⟶ V) (i0 : O0 ⟶ V)
    (mc : V ⟶ V') (md : V' ⟶ V'') (me : V'' ⟶ W)
    (h5 : e ≫ i = i4 ≫ me) (h4 : d ≫ i4 = i3 ≫ md) (h3 : c ≫ i3 = i2 ≫ mc)
    (h2 : b ≫ i2 = i1) (h1 : a ≫ i1 = i0) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ i = i0 ≫ mc ≫ md ≫ me :=
  calc (a ≫ b ≫ c ≫ d ≫ e) ≫ i = a ≫ b ≫ c ≫ d ≫ e ≫ i := by simp
    _ = a ≫ b ≫ c ≫ d ≫ i4 ≫ me := by rw [h5]
    _ = a ≫ b ≫ c ≫ (d ≫ i4) ≫ me := by simp
    _ = a ≫ b ≫ c ≫ (i3 ≫ md) ≫ me := by rw [h4]
    _ = a ≫ b ≫ (c ≫ i3) ≫ md ≫ me := by simp
    _ = a ≫ b ≫ (i2 ≫ mc) ≫ md ≫ me := by rw [h3]
    _ = (a ≫ (b ≫ i2)) ≫ mc ≫ md ≫ me := by simp
    _ = i0 ≫ mc ≫ md ≫ me := by rw [h2, h1]

end Collapse

variable {A : Type uA} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {B : Type uB} [Category.{v} B] [Abelian B] [HasExt.{v} B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (HA : A ⥤ Ab.{v}) [HA.Additive] [PreservesFiniteLimits HA]
  (XA : A) (αA : HA ≅ preadditiveCoyoneda.obj (op XA))
  (HB : B ⥤ Ab.{v}) [HB.Additive] [PreservesFiniteLimits HB]
  (XB : B) (αB : HB ≅ preadditiveCoyoneda.obj (op XB))
  (b : XA ⟶ F.obj XB)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [HA.Additive]
  [PreservesFiniteLimits HA] [HB.Additive] [PreservesFiniteLimits HB] in
/-- **The cocycle transport is the chain map composed with the two corepresentations**, read
through the inclusions of the cocycles.  This is
`Stacks.Cohomology.ModuleComparison.extCocycleComp_comp_i` with `compUnit` replaced by an
arbitrary `b` and `compCorepresentation` replaced by a corepresentation of the source functor
together with `derivedSectionsMap`.  Only two naturalities are used: that of `αB` at the cocycle
and that of `αA.inv` at `φ`. -/
theorem extCocycleComp_comp_i_of_corepresentation {Z : B} (I : InjectiveResolution Z)
    (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (n : ℕ) :
    AddCommGrpCat.ofHom (extCocycleComp F I J φ b n) ≫
        (extLeftHomologyData J XA n).i ≫ αA.inv.app (J.cocomplex.X (n + 1)) =
      (extLeftHomologyData I XB n).i ≫ αB.inv.app (I.cocomplex.X (n + 1)) ≫
        (derivedSectionsMap F HA XA αA HB XB αB b).app (I.cocomplex.X (n + 1)) ≫
          HA.map (φ.f (n + 1)) := by
  ext t
  have hid : αB.hom.app (I.cocomplex.X (n + 1))
      (αB.inv.app (I.cocomplex.X (n + 1)) (t.val : XB ⟶ I.cocomplex.X (n + 1))) =
      (t.val : XB ⟶ I.cocomplex.X (n + 1)) :=
    ConcreteCategory.congr_hom (αB.inv_hom_id_app (I.cocomplex.X (n + 1)))
      (t.val : XB ⟶ I.cocomplex.X (n + 1))
  have hα : ∀ u : XA ⟶ F.obj (I.cocomplex.X (n + 1)),
      αA.inv.app (J.cocomplex.X (n + 1)) (u ≫ φ.f (n + 1)) =
        HA.map (φ.f (n + 1)) (αA.inv.app (F.obj (I.cocomplex.X (n + 1))) u) := fun u =>
    NatTrans.naturality_apply αA.inv (φ.f (n + 1)) u
  show αA.inv.app (J.cocomplex.X (n + 1))
      (b ≫ F.map (t.val : XB ⟶ I.cocomplex.X (n + 1)) ≫ φ.f (n + 1)) =
    HA.map (φ.f (n + 1)) (αA.inv.app (F.obj (I.cocomplex.X (n + 1)))
      (b ≫ F.map (αB.hom.app (I.cocomplex.X (n + 1))
        (αB.inv.app (I.cocomplex.X (n + 1)) (t.val : XB ⟶ I.cocomplex.X (n + 1))))))
  rw [hid, ← hα]
  exact congrArg (fun u : XA ⟶ J.cocomplex.X (n + 1) =>
    αA.inv.app (J.cocomplex.X (n + 1)) u) (Category.assoc _ _ _).symm


omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits HA]
  [PreservesFiniteLimits HB] in
/-- **The cocycle transport on cycles**, i.e.
`extCocycleComp_comp_i_of_corepresentation` read on the cycles of the two complexes rather than
through the inclusions of the cocycles.  The inclusion of the cycles is a monomorphism, so this
is that lemma together with the compatibility of `HomologicalComplex.cyclesMap`,
`HomologicalComplex.cyclesIsoSc'` and
`CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso` with those inclusions. -/
theorem extCocycleComp_comp_cyclesMap_of_corepresentation {Z : B} (I : InjectiveResolution Z)
    (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (n : ℕ) (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    AddCommGrpCat.ofHom (extCocycleComp F I J φ b n) ≫
        ((extLeftHomologyData J XA n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op XA)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          J.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex αA.inv (ComplexShape.up ℕ)).app J.cocomplex) (n + 1)) =
      (extLeftHomologyData I XB n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op XB)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex αB.inv (ComplexShape.up ℕ)).app I.cocomplex) (n + 1) ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (derivedSectionsMap F HA XA αA HB XB αB b)
            (ComplexShape.up ℕ)).app I.cocomplex) (n + 1) ≫
        HomologicalComplex.cyclesMap
          ((HA.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) :=
  extReadingMono _ _ _ (((HA.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).iCycles
      (n + 1)) _ _
    (extReadingCollapse3 _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex αA.inv (ComplexShape.up ℕ)).app J.cocomplex) (n + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ n (n + 1) (n + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData J XA n)))
    (collapse₅ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i
        ((HA.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1))
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex (derivedSectionsMap F HA XA αA HB XB αB b)
          (ComplexShape.up ℕ)).app I.cocomplex) (n + 1))
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex αB.inv (ComplexShape.up ℕ)).app I.cocomplex) (n + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ n (n + 1) (n + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData I XB n)))
    (extCocycleComp_comp_i_of_corepresentation F HA XA αA HB XB αB b I J φ n)


section Succ

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]

/-- **The resolution-level reading of the `Ext`-side comparison map in positive degree.**
Conjugated by `ModuleSheafCohomology.extFunctorObjIsoRightDerived` on both sides, the `Ext`-level
map `e ↦ Ext.mk₀ b ∘ (F e)` of `Stacks.Cohomology.ModuleComparison.extMapComp` is computed, on
the chosen injective resolutions of `Z` and of `F.obj Z`, by the chain map `derivedSectionsMap`
followed by any comparison `φ` of the image of the resolution upstairs with the resolution
downstairs extending the identity.

The inputs are `Stacks.Cohomology.ModuleComparison.extMapComp_π` for the effect of the
`Ext`-level map on a class presented by a cocycle,
`Stacks.Cohomology.ModuleComparison.extFunctorObjIsoRightDerived_succ_π_comp` twice for the two
resolution-level readings, and `extCocycleComp_comp_cyclesMap_of_corepresentation` for the
compatibility of the cocycle transport with the chain map; they are assembled by
`Stacks.Cohomology.ModuleComparison.extReadingAssemble`. -/
theorem extMapComp_conj_succ (Z : B) (n : ℕ)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution Z).cocomplex ⟶
      (injectiveResolution (F.obj Z)).cocomplex)
    (hφ : F.map ((injectiveResolution Z).ι.f 0) ≫ φ.f 0 =
      (injectiveResolution (F.obj Z)).ι.f 0) :
    (extFunctorObjIsoRightDerived HB XB αB (n + 1)).inv.app Z ≫
        (extMapComp F b (n + 1)).app Z ≫
        (extFunctorObjIsoRightDerived HA XA αA (n + 1)).hom.app (F.obj Z) =
      ((injectiveResolution Z).isoRightDerivedObj HB (n + 1)).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (derivedSectionsMap F HA XA αA HB XB αB b)
              (ComplexShape.up ℕ)).app (injectiveResolution Z).cocomplex ≫
            (HA.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) ≫
        ((injectiveResolution (F.obj Z)).isoRightDerivedObj HA (n + 1)).inv := by
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  have f7 : ((HB.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution Z).cocomplex).homologyπ (n + 1) ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (derivedSectionsMap F HA XA αA HB XB αB b)
            (ComplexShape.up ℕ)).app (injectiveResolution Z).cocomplex ≫
          (HA.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) =
      (HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (derivedSectionsMap F HA XA αA HB XB αB b)
            (ComplexShape.up ℕ)).app (injectiveResolution Z).cocomplex) (n + 1) ≫
        HomologicalComplex.cyclesMap
          ((HA.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1)) ≫
        ((HA.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (F.obj Z)).cocomplex).homologyπ (n + 1) := by
    rw [← HomologicalComplex.cyclesMap_comp]
    exact HomologicalComplex.homologyπ_naturality _ (n + 1)
  exact extReadingAssemble
    (extLeftHomologyData (injectiveResolution Z) XB n).π
    ((extFunctorObjIsoRightDerived HB XB αB (n + 1)).hom.app Z)
    _
    ((extFunctorObjIsoRightDerived HB XB αB (n + 1)).inv.app Z)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    inferInstance
    rfl
    ((extFunctorObjIsoRightDerived HB XB αB (n + 1)).hom_inv_id_app Z)
    ((extFunctorObjIsoRightDerived HB XB αB (n + 1)).inv_hom_id_app Z)
    (extMapComp_π F (injectiveResolution Z) (injectiveResolution (F.obj Z)) φ hφ b n)
    (extFunctorObjIsoRightDerived_succ_π_comp HA XA αA (F.obj Z) n hi hk)
    (extFunctorObjIsoRightDerived_succ_π_comp HB XB αB Z n hi hk)
    (Iso.inv_hom_id _)
    f7
    (extCocycleComp_comp_cyclesMap_of_corepresentation F HA XA αA HB XB αB b (injectiveResolution Z)
      (injectiveResolution (F.obj Z)) φ n hi hk)

end Succ


/-! ### The instantiation at the inverse image along a continuous map of spaces

Everything above is at the abstract spelling.  The rest of the file instantiates it at the inverse
image of abelian sheaves along a continuous map and identifies the resulting arrow with the one
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` prescribes, in positive degree.  -/

section Space

universe u

open TopologicalSpace Stacks.Cohomology.AbelianColimit

/-! #### Two reassociation helpers

As with `Stacks.Cohomology.ExtComparison.assoc₂` and `assoc₃`, these are stated in an abstract
category so that no foreign constant is traversed, and they are applied by `exact` rather than by
`rw`: the goals they rearrange contain spelling crossings that a rewriting tactic cannot build a
motive across. -/

section Reassoc

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- Reassociating a four-fold composite against a further morphism.  The three-fold version is
`Stacks.Cohomology.ExtComparison.assoc₃`. -/
theorem assoc₄ {A₀ A₁ A₂ A₃ A₄ A₅ : C} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (d : A₃ ⟶ A₄) (k : A₄ ⟶ A₅) :
    (a ≫ b ≫ c ≫ d) ≫ k = a ≫ b ≫ c ≫ d ≫ k := by
  simp only [Category.assoc]

/-- **The rearrangement that turns the three resolution-level inputs into the conjugated reading
of the comparison arrow.**  Read at the instantiation below: `key` is
`extMapComp_conj_succ`, `hnat` is the naturality of the canonical identification at the adjoint of
the `f`-map followed by `CategoryTheory.Functor.rightDerived_map_eq`, `hvw` cancels the
identification at the resolution of `f⁻¹ G`, and `huz` composes the two cochain maps.

All objects and morphisms are variables on purpose.  Each of the hypotheses mentions the
identification of `Ext` with right-derived sections in a different spelling, and discharging the
rearrangement by `exact` against a statement written out in one of them makes the unifier unfold
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` at a literal `n + 1`. -/
theorem conj_succ_rearrange {A₀ A₁ A₃ A₄ A₅ C₀ B₀ B₁ B₂ : C}
    {eGi : A₁ ⟶ A₀} {a : A₀ ⟶ C₀} {eU : C₀ ⟶ A₃} {mσ : C₀ ⟶ A₅} {eFh : A₅ ⟶ A₄}
    {t : A₁ ⟶ B₀} {u : B₀ ⟶ B₁} {v : B₁ ⟶ A₃} {w : A₃ ⟶ B₁}
    {z : B₁ ⟶ B₂} {y : B₂ ⟶ A₄} {s : B₀ ⟶ B₂}
    (key : eGi ≫ a ≫ eU = t ≫ u ≫ v)
    (hnat : mσ ≫ eFh = eU ≫ w ≫ z ≫ y)
    (hvw : v ≫ w = 𝟙 B₁) (huz : u ≫ z = s) :
    eGi ≫ (a ≫ mσ) ≫ eFh = t ≫ s ≫ y := by
  have e1 : eGi ≫ (a ≫ mσ) ≫ eFh = eGi ≫ a ≫ mσ ≫ eFh := by simp only [Category.assoc]
  rw [e1, hnat]
  have e2 : eGi ≫ a ≫ eU ≫ w ≫ z ≫ y = (eGi ≫ a ≫ eU) ≫ w ≫ z ≫ y := by
    simp only [Category.assoc]
  rw [e2, key]
  simp only [Category.assoc]
  rw [← Category.assoc v w, hvw, Category.id_comp, ← huz]
  simp only [Category.assoc]

end Reassoc

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
  {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
  (φ : G ⟶ (Spaces.sheafPushforward f).obj F)
  (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V)

/-! #### The datum `IsCohomologyMap` asks for, built from the datum the `Ext` side produces -/

/-- **The adjunct of a cochain map out of an inverse image.**  A cochain map
`χ : f⁻¹ I ⟶ J` is carried by the inverse-image/direct-image adjunction to a cochain map
`I ⟶ f_* J`, degreewise by the adjunction and with the cochain condition the naturality of the
unit.  This is the passage between the datum
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` asks for -- a map into the direct image of a
resolution downstairs -- and the datum the `Ext`-side description produces, a map out of the
inverse image of a resolution upstairs. -/
def pushforwardAdjunctComplex
    (I : CochainComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) ℕ)
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (χ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ J) :
    I ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J where
  f k := (Spaces.sheafAdjunction f).unit.app (I.X k) ≫ (Spaces.sheafPushforward f).map (χ.f k)
  comm' i j _ := by
    have hu : I.d i j ≫ (Spaces.sheafAdjunction f).unit.app (I.X j) =
        (Spaces.sheafAdjunction f).unit.app (I.X i) ≫
          (Spaces.sheafPushforward f).map ((sheafPullback f).map (I.d i j)) :=
      (Spaces.sheafAdjunction f).unit.naturality (I.d i j)
    have hc : (sheafPullback f).map (I.d i j) ≫ χ.f j = χ.f i ≫ J.d i j := (χ.comm i j).symm
    change ((Spaces.sheafAdjunction f).unit.app (I.X i) ≫
          (Spaces.sheafPushforward f).map (χ.f i)) ≫ (Spaces.sheafPushforward f).map (J.d i j) =
        I.d i j ≫ (Spaces.sheafAdjunction f).unit.app (I.X j) ≫
          (Spaces.sheafPushforward f).map (χ.f j)
    symm
    calc I.d i j ≫ (Spaces.sheafAdjunction f).unit.app (I.X j) ≫
            (Spaces.sheafPushforward f).map (χ.f j)
        = (I.d i j ≫ (Spaces.sheafAdjunction f).unit.app (I.X j)) ≫
            (Spaces.sheafPushforward f).map (χ.f j) := (Category.assoc _ _ _).symm
      _ = ((Spaces.sheafAdjunction f).unit.app (I.X i) ≫
            (Spaces.sheafPushforward f).map ((sheafPullback f).map (I.d i j))) ≫
            (Spaces.sheafPushforward f).map (χ.f j) := by rw [hu]
      _ = (Spaces.sheafAdjunction f).unit.app (I.X i) ≫
            (Spaces.sheafPushforward f).map ((sheafPullback f).map (I.d i j) ≫ χ.f j) := by
            rw [Category.assoc, ← Functor.map_comp]
      _ = (Spaces.sheafAdjunction f).unit.app (I.X i) ≫
            (Spaces.sheafPushforward f).map (χ.f i ≫ J.d i j) := by rw [hc]
      _ = ((Spaces.sheafAdjunction f).unit.app (I.X i) ≫
            (Spaces.sheafPushforward f).map (χ.f i)) ≫
            (Spaces.sheafPushforward f).map (J.d i j) := by
            rw [Functor.map_comp, Category.assoc]

/-- The degree-`k` component of the adjunct of `χ` is the adjunction image of `χ.f k`. -/
private theorem pushforwardAdjunctComplex_f_eq_homEquiv
    (I : CochainComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) ℕ)
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (χ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ J) (k : ℕ) :
    (pushforwardAdjunctComplex f I J χ).f k =
      (Spaces.sheafAdjunction f).homEquiv (I.X k) (J.X k) (χ.f k) :=
  (Adjunction.homEquiv_unit (Spaces.sheafAdjunction f) _ _ _).symm

/-- **The two descriptions of the map of section complexes agree.**  The map of section complexes
`Stacks.Cohomology.SpectralLimit.sectionsComplexMap` attached to the adjunct of `χ` is the
pullback map on sections followed by `χ`.  Degreewise this is
`Stacks.Cohomology.ExtComparison.derivedSectionsMap_comp_eq_sectionsRestrictMap`, the `f`-map
there being the degree-`k` component of the adjunct; that the adjunct's components undo the
adjunction is `CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem sectionsComplexMap_pushforwardAdjunctComplex
    (I : CochainComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) ℕ)
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (χ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ J) :
    Stacks.Cohomology.SpectralLimit.sectionsComplexMap.{u, u} f
        (pushforwardAdjunctComplex f I J χ) V U h =
      (NatTrans.mapHomologicalComplex
          (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
            (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h))
          (ComplexShape.up ℕ)).app I ≫
        ((abSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map χ := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  have hs : ((Spaces.sheafAdjunction f).homEquiv (I.X k) (J.X k)).symm
      ((pushforwardAdjunctComplex f I J χ).f k) = χ.f k := by
    rw [pushforwardAdjunctComplex_f_eq_homEquiv, Equiv.symm_apply_apply]
  have key := derivedSectionsMap_comp_eq_sectionsRestrictMap f V U h (I.X k) (J.X k)
    ((pushforwardAdjunctComplex f I J χ).f k)
  rw [hs] at key
  exact key.symm

/-- **The adjunct of a cochain map extends the `f`-map** when the cochain map extends its
adjoint.  This is the commutation relation
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` carries, and the proof is the naturality of the
adjunction unit together with `CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem ι_comp_pushforwardAdjunctComplex_f_zero
    (I : CochainComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) ℕ)
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (χ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ J)
    (ιI : G ⟶ I.X 0) (ιJ : F ⟶ J.X 0)
    (hcomm : (sheafPullback f).map ιI ≫ χ.f 0 =
      ((Spaces.sheafAdjunction f).homEquiv G F).symm φ ≫ ιJ) :
    ιI ≫ (pushforwardAdjunctComplex f I J χ).f 0 =
      φ ≫ (Spaces.sheafPushforward f).map ιJ := by
  rw [pushforwardAdjunctComplex_f_eq_homEquiv, ← Adjunction.homEquiv_naturality_left, hcomm,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- **The two cochain maps of the instantiation compose to the map of section complexes.**  The
pullback map on sections followed by the comparison of resolutions upstairs, then by the lift of
the adjoint `f`-map, is the map of section complexes attached to the adjunct of the composite.
This is `sectionsComplexMap_pushforwardAdjunctComplex` together with
`HomologicalComplex.homologyMap_comp`. -/
theorem homologyMap_sectionsComplexMap_pushforwardAdjunctComplex
    (I : CochainComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) ℕ)
    (P : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) ℕ)
    (χ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ P)
    (g : P ⟶ J) (q : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
            (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
              (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h))
            (ComplexShape.up ℕ)).app I ≫
          ((abSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map χ) q ≫
        HomologicalComplex.homologyMap
          (((abSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map g) q =
      HomologicalComplex.homologyMap
        (Stacks.Cohomology.SpectralLimit.sectionsComplexMap.{u, u} f
          (pushforwardAdjunctComplex f I J (χ ≫ g)) V U h) q := by
  have hchain : ((NatTrans.mapHomologicalComplex
          (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
            (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h))
          (ComplexShape.up ℕ)).app I ≫
        ((abSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map χ) ≫
        ((abSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map g =
      Stacks.Cohomology.SpectralLimit.sectionsComplexMap.{u, u} f
        (pushforwardAdjunctComplex f I J (χ ≫ g)) V U h := by
    rw [sectionsComplexMap_pushforwardAdjunctComplex, Functor.map_comp, Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun ψ => HomologicalComplex.homologyMap ψ q) hchain

/-! #### The identification in positive degree -/

/-- The canonical identification of native cohomology over an open with right-derived sections is
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` at the corepresentation of sections, by
definition.  Stated so that the crossing between the two spellings can be paid once, by `rw`, at
the level of the isomorphism itself: inside a composite, at a literal `n + 1`, it is
unaffordable. -/
theorem H'isoRightDerivedSections_eq_repU {W : TopCat.{u}} (O : Opens ↥W) (p : ℕ) :
    H'isoRightDerivedSections O p =
      extFunctorObjIsoRightDerived (abSections O) (freeOfOpen O) (repU O) p :=
  rfl

/-- `H'isoRightDerivedSections_eq_repU` at the spelling `repV` of the corepresentation, which is
the one the target space carries. -/
theorem H'isoRightDerivedSections_eq_repV {W : TopCat.{u}} (O : Opens ↥W) (p : ℕ) :
    H'isoRightDerivedSections O p =
      extFunctorObjIsoRightDerived (abSections O) (freeOfOpen O) (repV O) p :=
  rfl

/-- **The conjugated reading of the `Ext`-side comparison arrow in positive degree.**  Conjugated
by the canonical identifications of cohomology with right-derived sections, the arrow
`extSpacePullbackMap` is computed on the chosen injective resolutions of `G` and of `F` by the map
of section complexes attached to the adjunct of `χ₀ ≫ g`, where `χ₀` compares the inverse image
of the resolution of `G` with the resolution of `f⁻¹ G` and `g` lifts the adjoint of the `f`-map.

The three inputs are `extMapComp_conj_succ`, the naturality of the canonical identification at the
adjoint of the `f`-map followed by `CategoryTheory.Functor.rightDerived_map_eq`, and
`homologyMap_sectionsComplexMap_pushforwardAdjunctComplex`; they are assembled by
`conj_succ_rearrange`. -/
theorem extSpacePullbackMap_succ_conj (n : ℕ)
    (χ₀ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution G).cocomplex ⟶
      (injectiveResolution ((sheafPullback f).obj G)).cocomplex)
    (hχ₀ : (sheafPullback f).map ((injectiveResolution G).ι.f 0) ≫ χ₀.f 0 =
      (injectiveResolution ((sheafPullback f).obj G)).ι.f 0)
    (g : (injectiveResolution ((sheafPullback f).obj G)).cocomplex ⟶
      (injectiveResolution F).cocomplex)
    (hg : (injectiveResolution ((sheafPullback f).obj G)).ι ≫ g =
      (CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})).map
          (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) ≫ (injectiveResolution F).ι) :
    (H'isoRightDerivedSections V (n + 1)).inv.app G ≫
        extSpacePullbackMap f φ V U h (n + 1) ≫
        (H'isoRightDerivedSections U (n + 1)).hom.app F =
      ((injectiveResolution G).isoRightDerivedObj (abSections V) (n + 1)).hom ≫
        HomologicalComplex.homologyMap
          (Stacks.Cohomology.SpectralLimit.sectionsComplexMap.{u, u} f
            (pushforwardAdjunctComplex f (injectiveResolution G).cocomplex
              (injectiveResolution F).cocomplex (χ₀ ≫ g)) V U h) (n + 1) ≫
        ((injectiveResolution F).isoRightDerivedObj (abSections U) (n + 1)).inv := by
  have hnat := (H'isoRightDerivedSections U (n + 1)).hom.naturality
    (((Spaces.sheafAdjunction f).homEquiv G F).symm φ)
  have hrd := Functor.rightDerived_map_eq (abSections U) (n + 1)
    (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) g hg
  rw [hrd] at hnat
  have key := extMapComp_conj_succ (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
    (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h) G n χ₀ hχ₀
  rw [← H'isoRightDerivedSections_eq_repV V (n + 1),
    ← H'isoRightDerivedSections_eq_repU U (n + 1)] at key
  have huz := homologyMap_sectionsComplexMap_pushforwardAdjunctComplex f V U h
    (injectiveResolution G).cocomplex
    (injectiveResolution ((sheafPullback f).obj G)).cocomplex
    (injectiveResolution F).cocomplex χ₀ g (n + 1)
  exact conj_succ_rearrange key hnat (Iso.inv_hom_id _) huz

/-- **In positive degree the `Ext`-side comparison arrow is the arrow prescribed by Tag 0A37.**
`extSpacePullbackMap_succ_conj` with the identification on the source cancelled; the
positive-degree companion of
`Stacks.Cohomology.ExtComparison.extSpacePullbackMap_zero_eq`. -/
theorem extSpacePullbackMap_succ_eq (n : ℕ)
    (χ₀ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution G).cocomplex ⟶
      (injectiveResolution ((sheafPullback f).obj G)).cocomplex)
    (hχ₀ : (sheafPullback f).map ((injectiveResolution G).ι.f 0) ≫ χ₀.f 0 =
      (injectiveResolution ((sheafPullback f).obj G)).ι.f 0)
    (g : (injectiveResolution ((sheafPullback f).obj G)).cocomplex ⟶
      (injectiveResolution F).cocomplex)
    (hg : (injectiveResolution ((sheafPullback f).obj G)).ι ≫ g =
      (CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})).map
          (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) ≫ (injectiveResolution F).ι) :
    extSpacePullbackMap f φ V U h (n + 1) ≫
        (H'isoRightDerivedSections U (n + 1)).hom.app F =
      (H'isoRightDerivedSections V (n + 1)).hom.app G ≫
        ((injectiveResolution G).isoRightDerivedObj (abSections V) (n + 1)).hom ≫
        HomologicalComplex.homologyMap
          (Stacks.Cohomology.SpectralLimit.sectionsComplexMap.{u, u} f
            (pushforwardAdjunctComplex f (injectiveResolution G).cocomplex
              (injectiveResolution F).cocomplex (χ₀ ≫ g)) V U h) (n + 1) ≫
        ((injectiveResolution F).isoRightDerivedObj (abSections U) (n + 1)).inv := by
  have hc := extSpacePullbackMap_succ_conj f φ V U h n χ₀ hχ₀ g hg
  rw [← hc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The positive-degree case of the identification Tag 0A37 asks for, for a given comparison of
resolutions.**  The injective resolutions are the chosen ones, the cochain map is the adjunct of
`χ₀ ≫ g`, its commutation with the `f`-map is
`ι_comp_pushforwardAdjunctComplex_f_zero`, and the identification of the arrow is
`extSpacePullbackMap_succ_eq`. -/
theorem isCohomologyMap_extSpacePullbackMap_succ_of_comparison (n : ℕ)
    (χ₀ : ((sheafPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution G).cocomplex ⟶
      (injectiveResolution ((sheafPullback f).obj G)).cocomplex)
    (hχ₀ : (sheafPullback f).map ((injectiveResolution G).ι.f 0) ≫ χ₀.f 0 =
      (injectiveResolution ((sheafPullback f).obj G)).ι.f 0)
    (g : (injectiveResolution ((sheafPullback f).obj G)).cocomplex ⟶
      (injectiveResolution F).cocomplex)
    (hg : (injectiveResolution ((sheafPullback f).obj G)).ι ≫ g =
      (CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})).map
          (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) ≫ (injectiveResolution F).ι)
    (hg0 : (injectiveResolution ((sheafPullback f).obj G)).ι.f 0 ≫ g.f 0 =
      ((Spaces.sheafAdjunction f).homEquiv G F).symm φ ≫ (injectiveResolution F).ι.f 0) :
    Stacks.Cohomology.SpectralLimit.IsCohomologyMap f φ V U h (n + 1)
      ((H'isoRightDerivedSections V (n + 1)).app G)
      ((H'isoRightDerivedSections U (n + 1)).app F)
      (extSpacePullbackMap f φ V U h (n + 1)) := by
  refine ⟨injectiveResolution G, injectiveResolution F,
    pushforwardAdjunctComplex f (injectiveResolution G).cocomplex
      (injectiveResolution F).cocomplex (χ₀ ≫ g), ?_, ?_⟩
  · refine ι_comp_pushforwardAdjunctComplex_f_zero f φ _ _ _ _ _ ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun w => w ≫ g.f 0) hχ₀)).trans hg0
  · have k3 := (assoc₂ _ _ ((H'isoRightDerivedSections U (n + 1)).inv.app F)).symm.trans
      ((whiskerRightEq (extSpacePullbackMap_succ_eq f φ V U h n χ₀ hχ₀ g hg) _).trans
        (assoc₄ _ _ _ _ _))
    rw [Iso.hom_inv_id_app, Category.comp_id] at k3
    exact k3

/-- **The positive-degree case of the identification Tag 0A37 asks for.**  The comparison `χ₀` of
the inverse image of the resolution of `G` with the resolution of `f⁻¹ G` is
`Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison`, and the lift `g` of the
adjoint of the `f`-map is `CategoryTheory.InjectiveResolution.desc`. -/
theorem isCohomologyMap_extSpacePullbackMap_succ (n : ℕ) :
    Stacks.Cohomology.SpectralLimit.IsCohomologyMap f φ V U h (n + 1)
      ((H'isoRightDerivedSections V (n + 1)).app G)
      ((H'isoRightDerivedSections U (n + 1)).app F)
      (extSpacePullbackMap f φ V U h (n + 1)) := by
  obtain ⟨χ₀, hχ₀⟩ := exists_mapResolutionComparison (sheafPullback f) (injectiveResolution G)
    (injectiveResolution ((sheafPullback f).obj G))
  exact isCohomologyMap_extSpacePullbackMap_succ_of_comparison f φ V U h n χ₀ hχ₀
    (InjectiveResolution.desc (((Spaces.sheafAdjunction f).homEquiv G F).symm φ)
      (injectiveResolution F) (injectiveResolution ((sheafPullback f).obj G)))
    (InjectiveResolution.desc_commutes _ _ _)
    (InjectiveResolution.desc_commutes_zero _ _ _)

/-- **The identification Tag 0A37 asks for, in every degree.**  The `Ext`-side comparison arrow
satisfies `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` in every degree, for the canonical
identifications of cohomology with right-derived sections.  This is
`Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap_zero` with `0` replaced by an
arbitrary `p`.

Together with `Stacks.Cohomology.AbelianColimit.H'spacePullback_map_comp_H'δ` this says: the
arrows that commute with the connecting morphism are, in every degree, exactly the arrows
prescribed by a lift of injective resolutions.

It is stated at `H'isoRightDerivedSections` and not at
`Stacks.Cohomology.AbelianColimit.H'isoRightDerivedDelta` because
`Stacks.Cohomology.AbelianColimit.rightDerivedSectionsDeltaFunctor` is *defined* by transport
along the former, so the former has a formula in every degree while the latter is pinned only in
degree zero. -/
theorem isCohomologyMap_extSpacePullbackMap (p : ℕ) :
    Stacks.Cohomology.SpectralLimit.IsCohomologyMap f φ V U h p
      ((H'isoRightDerivedSections V p).app G) ((H'isoRightDerivedSections U p).app F)
      (extSpacePullbackMap f φ V U h p) := by
  cases p with
  | zero => exact isCohomologyMap_extSpacePullbackMap_zero f φ V U h
  | succ n => exact isCohomologyMap_extSpacePullbackMap_succ f φ V U h n

end Space


end Stacks.Cohomology.ExtComparison

end
