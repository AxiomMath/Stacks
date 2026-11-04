module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafSequenceExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The map of ideal sheaves of a square of closed subspaces of representable algebraic spaces

Let `B` be a big fppf site containing a scheme `S`, let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`, and let `Z ⊆ yoneda.obj T'` and `Z' ⊆ yoneda.obj T` be closed subspaces
sitting in a square over `g`. There are two maps of ideal sheaves: the space-level
`AlgebraicGeometry.Space.idealSheafMap` of the square of closed subspaces, and the scheme-level
`Stacks.ClosedImmersion.idealSheafMap` of the square of the two representing closed immersions.
This file proves that the comparison functor `AlgebraicGeometry.Space.representedAssociatedModule`
carries the second to the first, under the identifications
`AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` of the ideal sheaves at the two ambient
corners, provided the underlying morphism of schemes of `g` is affine.

## Main results

* `AlgebraicGeometry.Space.conjugate_comp_of_inclusions`: a morphism characterised by its
  composite with an inclusion stays characterised after conjugation by two isomorphisms.
* `AlgebraicGeometry.Space.representedAssociatedModule_pullbackIso_inv_naturality`: naturality of
  the inverse of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`.
* `AlgebraicGeometry.Space.idealSheafMapConjugate_comp_definingIdealOfHom_ι`: the scheme-level map
  of ideal sheaves, conjugated into the sectionwise presentation, composed with the inclusion into
  the structure sheaf is the pullback of that inclusion followed by the structure-sheaf map.
* `AlgebraicGeometry.Space.representedAssociatedModule_modulePullbackUnitToUnit_square`: the
  comparison functor carries the canonical map `g^*𝒪_T ⟶ 𝒪_{T'}` to
  `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.representedAssociatedModule_idealComparison`: the comparison functor
  carries any morphism of the sectionwise ideal sheaves compatible with the structure-sheaf map to
  the space-level map of ideal sheaves.
* `AlgebraicGeometry.Space.representedAssociatedModule_idealSheafMap_square`: the comparison
  functor carries the conjugate of `Stacks.ClosedImmersion.idealSheafMap` to
  `AlgebraicGeometry.Space.idealSheafMap`.

## Implementation notes

The scheme-level map of ideal sheaves is a `CategoryTheory.Limits.kernel.lift` between the
categorical kernels `Stacks.ClosedImmersion.idealSheaf`, whereas
`AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` is stated at the sectionwise ideal
subsheaf `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`. The two are identified by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, compatibly with the inclusions
into the structure sheaf.

Modules on a scheme carry two category instances, that of `AlgebraicGeometry.Scheme.Modules` and
that of sheaves of modules over `RingedSpaceModuleAdjunction.structureSheafRing`; they are equal by
`rfl` (`Stacks.RingedSpaceModules.category_schemeModules_eq`), but mixing them in one statement is
expensive to elaborate. So `AlgebraicGeometry.Space.representedAssociatedModule_idealComparison` is
stated entirely at the `AlgebraicGeometry.Scheme.Modules` spelling with the scheme-level map of
ideal sheaves a variable, and
`AlgebraicGeometry.Space.representedAssociatedModule_idealSheafMap_square` instantiates it.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the map of ideal sheaves
  and of conormal modules of a square of closed subspaces of algebraic spaces.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the scheme-level map.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Space

/-! ### Conjugating a characterised morphism, at arbitrary categories -/

/-- **A morphism characterised by its composite with an inclusion stays characterised after
conjugation by two identifications.**  Let `ag : C ⥤ D`, let `e' : Ia ≅ Ka` carry `κ' : Ka ⟶ OA'`
to `ι' : Ia ⟶ OA'` and `e : Ib ≅ Kb` carry `κ : Kb ⟶ OA` to `ι : Ib ⟶ OA`, and let
`m₀ : ag.obj Ka ⟶ Kb` satisfy `m₀ ≫ κ = ag.map κ' ≫ s`.  Then the conjugate
`ag.map e'.hom ≫ m₀ ≫ e.inv` satisfies the same equation with `ι`, `ι'` in place of `κ`, `κ'`. -/
theorem conjugate_comp_of_inclusions {C D : Type*} [Category C] [Category D] (ag : C ⥤ D)
    {Ia Ka OA' : C} {Ib Kb OA : D}
    (e' : Ia ≅ Ka) (κ' : Ka ⟶ OA') {ι' : Ia ⟶ OA'} (h' : e'.hom ≫ κ' = ι')
    (e : Ib ≅ Kb) (κ : Kb ⟶ OA) {ι : Ib ⟶ OA} (h : e.hom ≫ κ = ι)
    (m₀ : ag.obj Ka ⟶ Kb) (s : ag.obj OA' ⟶ OA) (hm₀ : m₀ ≫ κ = ag.map κ' ≫ s) :
    (ag.map e'.hom ≫ m₀ ≫ e.inv) ≫ ι = ag.map ι' ≫ s := by
  rw [Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_assoc, hm₀, ← Category.assoc,
    ← ag.map_comp, h']

/-! ### Naturality and the structure-sheaf map -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (Z : ClosedSubspaces B S hS (yoneda.obj T')) (Z' : ClosedSubspaces B S hS (yoneda.obj T))

/-- **The naturality of the edge comparison, with the comparison of module categories written
as `AlgebraicGeometry.Space.representedAssociatedModule`.**  For a morphism `φ : 𝓕 ⟶ 𝓖` of
modules on `T`, the inverse of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`
commutes with the comparison functor applied to `g^*φ` and the space-level pullback of the
comparison functor applied to `φ`. -/
theorem representedAssociatedModule_pullbackIso_inv_naturality
    {𝓕 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules} (φ : 𝓕 ⟶ 𝓖) :
    (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).map
          ((Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left)).map φ) ≫
        (representedAssociatedModulePullbackIso B S hS g
            (relativelyRepresentable_yoneda_map B S hS g) 𝓖).inv =
      (representedAssociatedModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) 𝓕).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAssociatedModule B S hS T
            (isAlgebraicSpace_yoneda B S hS T)).map φ) :=
  representedAssociatedModulePullbackIso_inv_naturality B S hS g φ

/-- **The scheme-level map of ideal sheaves, conjugated into the sectionwise presentation, is
still the map induced by the structure-sheaf map.**  Conjugating
`Stacks.ClosedImmersion.idealSheafMap` by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso` at both ends, its composite with
the inclusion of the sectionwise ideal sheaf into the structure sheaf is the pullback of that
inclusion followed by `RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`. -/
theorem idealSheafMapConjugate_comp_definingIdealOfHom_ι
    (fs : (BigFppfOver.toScheme B S hS).obj (representingObj B S hS T' Z) ⟶
      (BigFppfOver.toScheme B S hS).obj (representingObj B S hS T Z'))
    (comm : (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T' Z).left).toLRSHom.toShHom ≫
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toLRSHom.toShHom =
        fs.toLRSHom.toShHom ≫
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z').left).toLRSHom.toShHom) :
    ((RingedSpaceModuleAdjunction.modulePullback
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  g.left).toLRSHom.toShHom).map
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T Z').left)).hom ≫
            Stacks.ClosedImmersion.idealSheafMap comm ≫
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T' Z).left)).inv) ≫
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T' Z).left)).ι =
      (RingedSpaceModuleAdjunction.modulePullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toLRSHom.toShHom).map
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z').left)).ι ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toLRSHom.toShHom :=
  conjugate_comp_of_inclusions _
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z').left))
    _
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso_hom_comp_idealSheafι
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z').left))
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T' Z).left))
    _
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso_hom_comp_idealSheafι
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T' Z).left))
    _ _ (Stacks.ClosedImmersion.idealSheafMap_comp_ι comm)

section Affine

variable [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]

/-- **The comparison functor carries the canonical map `g^*𝒪_T ⟶ 𝒪_{T'}` of Zariski modules on
the schemes to `AlgebraicGeometry.Space.structureModulePullbackMap` of the represented
morphism**, under the identifications
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` and
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`, when the underlying morphism of
schemes of `g` is affine. Here `g^*𝒪_T ⟶ 𝒪_{T'}` is
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` of the underlying morphism of ringed
spaces. -/
theorem representedAssociatedModule_modulePullbackUnitToUnit_square :
    (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).map
          (RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toLRSHom.toShHom) ≫
        (representedAssociatedModuleObjUnitIso B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).hom =
      (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
            (representedAssociatedModuleObjUnitIso B S hS T
              (isAlgebraicSpace_yoneda B S hS T)).hom ≫
          structureModulePullbackMap B S hS (representedSpaceMap B S hS g) :=
  representedAssociatedModule_structurePullback_square B S hS g _
    (Eq.trans
      (eq_whisker
        (congrArg
          (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          (homEquiv_modulePullbackUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toLRSHom.toShHom))
        _)
      (representedAssociatedModule_structureProjection_square B S hS g))

/-! ### The assembly -/

/-- **The comparison functor of a representable algebraic space carries a scheme-level map of
ideal sheaves to the space-level one.**  Let `m` be a morphism from the pullback along `g` of the
sectionwise defining ideal sheaf of `Z'` to that of `Z` whose composite with the inclusion into
the structure sheaf is the pullback of the inclusion followed by the structure-sheaf map. Then
`AlgebraicGeometry.Space.representedAssociatedModule` carries `m` to
`AlgebraicGeometry.Space.idealSheafMap` of the square of closed subspaces, the horizontal arrows
being the inverse of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` and the
vertical arrows `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented`. -/
theorem representedAssociatedModule_idealComparison
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ Z ≫
        representedSpaceMap B S hS g =
      f ≫ subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z')
    (m : (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left)).obj
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z').left)).toSheafOfModules ⟶
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (representingHom B S hS T' Z).left)).toSheafOfModules)
    (hm : m ≫
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T' Z).left)).ι =
        (Scheme.Modules.pullback
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                g.left)).map
            (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                (representingHom B S hS T Z').left)).ι ≫
          RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toLRSHom.toShHom) :
    (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).map m ≫
        (definingIdealSheafIsoRepresented B S hS T' Z).inv =
      (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
            (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                (representingHom B S hS T Z').left)).toSheafOfModules).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
            (definingIdealSheafIsoRepresented B S hS T Z').inv ≫
          idealSheafMap B S hS
            (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
            (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
            Z Z' (representedSpaceMap B S hS g) f hsq := by
  refine idealComparison_of_inclusions
    (EX := representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T'))
    (EX' := representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T))
    (ag := Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    (bg := modulePullback B S hS (representedSpaceMap B S hS g))
    (pG := fun M => (representedAssociatedModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) M).inv)
    (OA := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
    (OA' := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
    (ιI := (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T' Z).left)).ι)
    (ιI' := (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z').left)).ι)
    (m := m)
    (sA := RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left).toLRSHom.toShHom)
    (hm := hm)
    (ιJ := (definingIdealSheaf B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ Z).ι)
    (hιJ := mono_definingIdealSheaf_ι B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ Z)
    (ιJ' := (definingIdealSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z').ι)
    (n := idealSheafMap B S hS
      (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
      (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      Z Z' (representedSpaceMap B S hS g) f hsq)
    (sB := structureModulePullbackMap B S hS (representedSpaceMap B S hS g))
    (hn := idealSheafMap_comp_definingIdealSheaf_ι B S hS
      (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
      (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      Z Z' (representedSpaceMap B S hS g) f hsq)
    (eX := (definingIdealSheafIsoRepresented B S hS T' Z).inv)
    (eX' := (definingIdealSheafIsoRepresented B S hS T Z').inv)
    (cX := representedAssociatedModuleObjUnitIso B S hS T'
      (isAlgebraicSpace_yoneda B S hS T'))
    (cX' := representedAssociatedModuleObjUnitIso B S hS T
      (isAlgebraicSpace_yoneda B S hS T))
    (heX := ?heX) (heX' := ?heX') (hpG := ?hpG) (hstr := ?hstr)
  case heX => exact definingIdealSheafIsoRepresented_inv_comp_ι B S hS T' Z
  case heX' => exact definingIdealSheafIsoRepresented_inv_comp_ι B S hS T Z'
  case hpG =>
    exact representedAssociatedModule_pullbackIso_inv_naturality B S hS g
      (𝓖 := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
      (φ := (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (representingHom B S hS T Z').left)).ι)
  case hstr => exact representedAssociatedModule_modulePullbackUnitToUnit_square B S hS g

/-- **The comparison functor carries the scheme-level map of ideal sheaves to the space-level
one.**  The comparison functor
`AlgebraicGeometry.Space.representedAssociatedModule` carries
`Stacks.ClosedImmersion.idealSheafMap` of the square of the two representing closed immersions,
conjugated by `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso` into the
sectionwise presentation of the two ideal sheaves, to
`AlgebraicGeometry.Space.idealSheafMap` of the square of closed subspaces, the vertical arrows
being `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented`. -/
theorem representedAssociatedModule_idealSheafMap_square
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ Z ≫
        representedSpaceMap B S hS g =
      f ≫ subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z')
    (fs : (BigFppfOver.toScheme B S hS).obj (representingObj B S hS T' Z) ⟶
      (BigFppfOver.toScheme B S hS).obj (representingObj B S hS T Z'))
    (comm : (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T' Z).left).toLRSHom.toShHom ≫
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toLRSHom.toShHom =
        fs.toLRSHom.toShHom ≫
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z').left).toLRSHom.toShHom) :
    (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).map
          ((RingedSpaceModuleAdjunction.modulePullback
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  g.left).toLRSHom.toShHom).map
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T Z').left)).hom ≫
            Stacks.ClosedImmersion.idealSheafMap comm ≫
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T' Z).left)).inv) ≫
        (definingIdealSheafIsoRepresented B S hS T' Z).inv =
      (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
            (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                (representingHom B S hS T Z').left)).toSheafOfModules).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
            (definingIdealSheafIsoRepresented B S hS T Z').inv ≫
          idealSheafMap B S hS
            (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
            (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
            Z Z' (representedSpaceMap B S hS g) f hsq :=
  representedAssociatedModule_idealComparison B S hS g Z Z' f hsq _
    (idealSheafMapConjugate_comp_definingIdealOfHom_ι B S hS g Z Z' fs comm)

end Affine

end AlgebraicGeometry.Space

end
