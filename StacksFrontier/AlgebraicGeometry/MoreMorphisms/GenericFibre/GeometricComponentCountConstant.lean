module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyIrreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingHypotheses
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.CoveringFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.Topology.Constructible.IrreducibleMeet
public import StacksCore.Tactic.StacksAttribute

/-!
# Constancy of the number of geometric irreducible components on an open set

Stacks Tag 055A says that for a finite type morphism of schemes and a point `y` of the target,
the number of geometrically irreducible components of the fibres is constant on a nonempty open
subset of the closure of `y`.

The proof needs Stacks Tags 0554 and 0559, neither of which is available in the library, so the
results below take their conclusions as hypotheses, packaged as
`AlgebraicGeometry.IrreducibleComponentsLowerBoundAfterShrinking` and
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinking`.

## Main results

* `AlgebraicGeometry.exists_open_geometricIrreducibleComponentCount_eq` is Stacks Tag 055A
  granted those two hypotheses.

## Implementation notes

An open subset of the closure of a point is represented as an open set of the subtype carrying
the induced topology. Being of finite type is expressed by `LocallyOfFiniteType` together with
`QuasiCompact`, and the count itself is
`AlgebraicGeometry.geometricIrreducibleComponentCount` of Tag 0556.

The argument replaces the target by the reduced induced closed subscheme on the closure of `y`,
which is irreducible with generic point `y`, and then applies Tag 0551 to pass to a finite
etale cover whose generic fibre has geometrically irreducible components. There the count at
the generic point is a genuine natural number `n`; Tag 0554 bounds the count below by `n` near
the generic point, Tag 054Y makes the closures of the generic components cover every nearby
fibre, and the hypothesis above keeps each of those closures geometrically irreducible
fibrewise, which bounds the count above by `n`.

## References

* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

section Helpers

open CategoryTheory.Limits

private theorem finite_irreducibleComponents_geometricFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K] :
    (irreducibleComponents (geometricFiber f y K)).Finite := by
  let g := f.fiberToSpecResidueField y
  let h := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  let spec := Y.fromSpecResidueField y
  have : LocallyOfFiniteType g :=
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f spec) ‹LocallyOfFiniteType f›
  have hlt : LocallyOfFiniteType (pullback.snd g h) :=
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g h) inferInstance
  have hcompact : CompactSpace (geometricFiber f y K) := by
    show CompactSpace (Limits.pullback (C := Scheme) g h)
    infer_instance
  have hlocal : IsLocallyNoetherian (geometricFiber f y K) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.snd g h) hlt inferInstance
  have : IsNoetherian (geometricFiber f y K) :=
    { toIsLocallyNoetherian := hlocal, toCompactSpace := hcompact }
  exact AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

private theorem ncard_irreducibleComponents_le_geometricCount
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    (irreducibleComponents (f.fiber y)).ncard ≤
      geometricIrreducibleComponentCount f y := by
  let k := Y.residueField y
  let K := SeparableClosure k
  let F := f.fiber y
  let s := f.fiberToSpecResidueField y
  let t := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let G := geometricFiber f y K
  let π := pullback.fst s t
  have hOrd : (irreducibleComponents F).Finite := finite_irreducibleComponents_fiber f y
  rw [hOrd.cast_ncard_eq]
  calc
    (irreducibleComponents F).encard ≤
        ((fun C => π.base '' C) '' irreducibleComponents G).encard :=
      Set.encard_mono (surjOn_irreducibleComponents_baseChange k K F s)
    _ ≤ (irreducibleComponents G).encard := Set.encard_image_le _ _
    _ = geometricIrreducibleComponentCount f y :=
      encard_irreducibleComponents_geometricFiber f y K

private theorem exists_open_geometricCount_ge_n
    (H0554 : IrreducibleComponentsLowerBoundAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) (n : ℕ)
    (hcomp : (irreducibleComponents (f.fiber η)).ncard = n) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧
      ∀ y ∈ U, n ≤ geometricIrreducibleComponentCount f y := by
  obtain ⟨U, hU, hne, hLower⟩ :=
    H0554 f inferInstance inferInstance η hη n hcomp
  refine ⟨U, hU, hne, fun y hy => ?_⟩
  calc
    (n : ℕ∞) ≤ (irreducibleComponents (f.fiber y)).ncard := by
      exact_mod_cast hLower y hy
    _ ≤ geometricIrreducibleComponentCount f y :=
      ncard_irreducibleComponents_le_geometricCount f y

private theorem encard_irreducibleComponents_le_of_finiteClosedIrreducibleCover
    {X : Type u} [TopologicalSpace X] (hfinite : (irreducibleComponents X).Finite)
    (n : ℕ) (F : Fin n → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hirr : ∀ i, IsIrreducible (F i)) (hcover : (Set.univ : Set X) ⊆ ⋃ i, F i) :
    (irreducibleComponents X).encard ≤ n := by
  have hsubset : irreducibleComponents X ⊆ Set.range F := by
    intro C hC
    obtain ⟨i, hi⟩ := irreducible_subset_finite_iUnion_closed hC.1 F hclosed
      (fun x hx => hcover (Set.mem_univ x))
    exact ⟨i, (hC.2 (hirr i) hi).antisymm hi⟩
  have hle : (irreducibleComponents X).ncard ≤ n := by
    calc
      (irreducibleComponents X).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsubset (Set.finite_range F)
      _ = (F '' (Set.univ : Set (Fin n))).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le
      _ = n := by simp
  calc
    (irreducibleComponents X).encard = (irreducibleComponents X).ncard :=
      hfinite.cast_ncard_eq.symm
    _ ≤ n := by exact_mod_cast hle

private theorem geometricCount_le_of_fiberSubscheme_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K]
    (n : ℕ) (I : Fin n → X.IdealSheafData)
    (hGI : ∀ j, GeometricallyIrreducible
      (((I j).subschemeι ≫ f).fiberToSpecResidueField y))
    (hcover : ∀ x : f.fiber y, ∃ j,
      x ∈ Set.range (Scheme.Hom.fiberMapComp (I j).subschemeι f y).base) :
    geometricIrreducibleComponentCount f y ≤ n := by
  let q := f.fiberToSpecResidueField y
  let t := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField y) K))
  let G := pullback q t
  have hfinite : (irreducibleComponents G).Finite :=
    finite_irreducibleComponents_geometricFiber f y K
  let m (j : Fin n) := pullback.map
    (((I j).subschemeι ≫ f).fiberToSpecResidueField y) t q t
    (Scheme.Hom.fiberMapComp (I j).subschemeι f y) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]
        exact (Scheme.Hom.fiberMapComp_fiberToSpecResidueField (I j).subschemeι f y).symm)
    (by simp)
  have hrange (j : Fin n) : Set.range (m j).base =
      (pullback.fst q t).base ⁻¹'
        Set.range (Scheme.Hom.fiberMapComp (I j).subschemeι f y).base := by
    have h := Scheme.Pullback.range_map
      (((I j).subschemeι ≫ f).fiberToSpecResidueField y) t q t
      (Scheme.Hom.fiberMapComp (I j).subschemeι f y) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]
          exact (Scheme.Hom.fiberMapComp_fiberToSpecResidueField (I j).subschemeι f y).symm)
      (by simp)
    simpa [m] using h
  have hcoverG : (Set.univ : Set G) ⊆
      ⋃ j, Set.range (m j).base := by
    intro z hz
    obtain ⟨j, hj⟩ := hcover ((pullback.fst q t).base z)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [hrange j]
    simpa only [Set.mem_preimage] using hj
  have hclosed : ∀ j, IsClosed (Set.range (m j).base) := by
    intro j
    rw [hrange j]
    exact (Scheme.Hom.isClosedImmersion_fiberMapComp
        (I j).subschemeι f y).isClosedEmbedding.isClosed_range
      |>.preimage (pullback.fst q t).base.hom.continuous_toFun
  have hirr : ∀ j, IsIrreducible (Set.range (m j).base) := by
    intro j
    let qi := ((I j).subschemeι ≫ f).fiberToSpecResidueField y
    have hgeom : geometrically (IrreducibleSpace ·) qi := by
      simpa only [GeometricallyIrreducible.eq_geometrically] using hGI j
    have : IrreducibleSpace ↥(pullback qi t) :=
      AlgebraicGeometry.pullback_of_geometrically hgeom K t
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ ↥(pullback qi t)).image
        (m j).base.hom (m j).base.hom.continuous_toFun.continuousOn
  rw [← encard_irreducibleComponents_geometricFiber f y K]
  exact encard_irreducibleComponents_le_of_finiteClosedIrreducibleCover hfinite n _ hclosed hirr
    hcoverG

private theorem geometricallyIrreducible_fiber_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hGI : GeometricallyIrreducible (f ∣_ V)) (y : V) :
    GeometricallyIrreducible (f.fiberToSpecResidueField (V.ι y)) := by
  have hp := isPullback_morphismRestrict f V
  let e := hp.flip.isoPullback
  let he : Arrow.mk (f ∣_ V) ≅ Arrow.mk (pullback.snd f V.ι) :=
    Arrow.isoMk e (Iso.refl _) hp.flip.isoPullback_hom_snd
  have hGIbase : GeometricallyIrreducible (pullback.snd f V.ι) :=
    (MorphismProperty.arrow_mk_iso_iff
      (P := show MorphismProperty Scheme from @GeometricallyIrreducible) he).mp hGI
  rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber] at hGIbase
  have hw : y ∈ {z | GeometricallyIrreducible
      ((pullback.snd f V.ι).fiberToSpecResidueField z)} := hGIbase y
  rwa [geometricallyIrreducibleFiberLocus_baseChange] at hw

private theorem geometricCount_eq_of_overIso
    {X X' Y : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y}
    (e : Over.mk f ≅ Over.mk g) :
    geometricIrreducibleComponentCount f =
      geometricIrreducibleComponentCount g := by
  funext y
  let K := SeparableClosure (Y.residueField y)
  let e₁ := (Over.pullback (Y.fromSpecResidueField y)).mapIso e
  let e₂ := (Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))).mapIso e₁
  let e₃ : geometricFiber f y K ≅ geometricFiber g y K :=
    (Over.forget _).mapIso e₂
  let h := Scheme.homeoOfIso e₃
  show (irreducibleComponents (geometricFiber f y K)).encard =
    (irreducibleComponents (geometricFiber g y K)).encard
  exact Set.encard_congr (Equiv.symm
    (irreducibleComponentsEquivOfIsPreirreducibleFiber h h.continuous h.isOpenMap
      (fun z => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible)
      h.surjective).toEquiv)

private lemma geometricallyIrreducible_iff_of_universalHomeomorphism
    {X X' Y : Scheme.{u}} (i : X' ⟶ X) [UniversalHomeomorphism i]
    (f : X ⟶ Y) :
    GeometricallyIrreducible f ↔ GeometricallyIrreducible (i ≫ f) := by
  rw [GeometricallyIrreducible.eq_geometrically,
    AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms,
    AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms]
  constructor <;> intro h K _ y
  all_goals
    let P := pullback f y
    let P' := pullback (i ≫ f) y
    let Q := pullback i (pullback.fst f y)
    let e : P' ≃ₜ P :=
      (pullbackRightPullbackFstIso f y i).hom.homeomorph.symm.trans
      (UniversalHomeomorphism.universally_isHomeomorph
        (pullback.fst i (pullback.fst f y)) (pullback.fst f y)
        (pullback.snd i (pullback.fst f y))
        (IsPullback.of_hasPullback i (pullback.fst f y)).flip).homeomorph
    first
    | exact e.irreducibleSpace_iff.mpr (h K y)
    | exact e.irreducibleSpace_iff.mp (h K y)

private theorem closure_of_fiber_component_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : irreducibleComponents (f.fiber η)) :
    Set.range ((pullback.snd
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (f.fiberι η '' (C : Set (f.fiber η))), isClosed_closure⟩ : Closeds X)).subschemeι
      (f.fiberι η)).base) =
      (C : Set (f.fiber η)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (f.fiberι η '' (C : Set (f.fiber η))), isClosed_closure⟩ : Closeds X)
  have hrange : Set.range (pullback.snd I.subschemeι (f.fiberι η)).base =
      (f.fiberι η).base ⁻¹' Set.range I.subschemeι.base := by
    simpa using (Scheme.Pullback.range_snd I.subschemeι (f.fiberι η))
  rw [hrange, I.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show (f.fiberι η).base ⁻¹' closure ((f.fiberι η).base '' (C : Set _)) = _
  rw [← (f.fiberι η).isEmbedding.closure_eq_preimage_closure_image,
    (isClosed_of_mem_irreducibleComponents (C : Set (f.fiber η)) C.2).closure_eq]

/-- A morphism `j ≫ f` has geometrically irreducible fibre over `η` as soon as the base change
of `j` to the fibre of `f` over `η` does. -/
theorem geometricallyIrreducible_fiber_comp_of_pullback
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (η : Y) (j : Z ⟶ X)
    (h : GeometricallyIrreducible
      (pullback.snd j (f.fiberι η) ≫ f.fiberToSpecResidueField η)) :
    GeometricallyIrreducible ((j ≫ f).fiberToSpecResidueField η) := by
  let spec := Y.fromSpecResidueField η
  let ePull := pullbackRightPullbackFstIso f spec j
  have hPullArrow : Arrow.mk (pullback.snd j (f.fiberι η) ≫ f.fiberToSpecResidueField η) ≅
      Arrow.mk (pullback.snd (j ≫ f) spec) := by
    refine Arrow.isoMk ePull (Iso.refl _) ?_
    show ePull.hom ≫ pullback.snd (j ≫ f) spec =
      pullback.snd j (f.fiberι η) ≫ f.fiberToSpecResidueField η
    exact pullbackRightPullbackFstIso_hom_snd f spec j
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := show MorphismProperty Scheme from @GeometricallyIrreducible) hPullArrow).1 h

private theorem geometricallyIrreducible_fiber_of_component_closure
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : irreducibleComponents (f.fiber η))
    (hC : GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set (f.fiber η)), isClosed_of_mem_irreducibleComponents _ C.2⟩ :
            Closeds (f.fiber η))).subschemeι ≫ f.fiberToSpecResidueField η)) :
    GeometricallyIrreducible
      (((Scheme.IdealSheafData.vanishingIdeal
          (⟨closure (f.fiberι η '' (C : Set (f.fiber η))),
            isClosed_closure⟩ : Closeds X)).subschemeι ≫
          f).fiberToSpecResidueField η) := by
  let TC : Closeds (f.fiber η) :=
    ⟨(C : Set (f.fiber η)), isClosed_of_mem_irreducibleComponents _ C.2⟩
  let IC := Scheme.IdealSheafData.vanishingIdeal TC
  let T : Closeds X :=
    ⟨closure (f.fiberι η '' (C : Set (f.fiber η))), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let P := pullback I.subschemeι (f.fiberι η)
  let q := pullback.snd I.subschemeι (f.fiberι η)
  let N := P.nilradical
  let i := N.subschemeι
  let d := i ≫ q
  let A := d.ker
  let g := f.fiberToSpecResidueField η
  have : UniversalHomeomorphism i :=
    universalHomeomorphism_nilradical_subschemeι P
  have hiHomeo : IsHomeomorph i :=
    (inferInstance : UniversalHomeomorphism i)
      |>.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hisurj : Function.Surjective i.base := hiHomeo.surjective
  have hrangeD : Set.range d.base = (C : Set (f.fiber η)) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hisurj.range_eq, Set.image_univ]
    exact closure_of_fiber_component_range f η C
  have hsupp : A.support = TC := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, hrangeD, (isClosed_of_mem_irreducibleComponents _ C.2).closure_eq]
    rfl
  have : IsReduced A.subscheme :=
    ObjectProperty.prop_of_iso IsReduced (asIso d.toImage) (isReduced_nilradical_subscheme P)
  have hAeq : A = IC := by
    simpa [IC] using
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme A TC hsupp
  let e : N.subscheme ≅ IC.subscheme :=
    asIso d.toImage ≪≫ eqToIso (congrArg
      (fun J : (f.fiber η).IdealSheafData => J.subscheme) hAeq)
  have he : e.hom ≫ IC.subschemeι = d := by
    dsimp [e]
    rw [Category.assoc, eqToHom_subscheme_comp_subschemeι A IC hAeq]
    exact Scheme.Hom.toImage_imageι d
  have hArrow : Arrow.mk (i ≫ q ≫ g) ≅ Arrow.mk (IC.subschemeι ≫ g) := by
    refine Arrow.isoMk e (Iso.refl _) ?_
    calc
      e.hom ≫ (IC.subschemeι ≫ g) = (e.hom ≫ IC.subschemeι) ≫ g := by simp
      _ = d ≫ g := by rw [he]
      _ = i ≫ q ≫ g := rfl
  exact geometricallyIrreducible_fiber_comp_of_pullback f η I.subschemeι
    ((geometricallyIrreducible_iff_of_universalHomeomorphism i (q ≫ g)).2
      ((MorphismProperty.arrow_mk_iso_iff
        (P := show MorphismProperty Scheme from @GeometricallyIrreducible) hArrow).2 hC))

private theorem geometricCount_eq_of_mem_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (n : ℕ) (Z : Fin n → Set (f.fiber η)) (W : Fin n → Y.Opens)
    (hW : ∀ j, GeometricallyIrreducible
      (((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (f.fiberι η '' Z j), isClosed_closure⟩ : Closeds X)).subschemeι ≫ f) ∣_ W j))
    (y : Y) (hyW : ∀ j, y ∈ W j)
    (hcover : ∀ x : f.fiber y, ∃ j, f.fiberι y x ∈ closure (f.fiberι η '' Z j))
    (hlower : n ≤ geometricIrreducibleComponentCount f y) :
    geometricIrreducibleComponentCount f y = n := by
  let I : Fin n → X.IdealSheafData := fun j =>
    Scheme.IdealSheafData.vanishingIdeal
      (⟨closure (f.fiberι η '' Z j), isClosed_closure⟩ : Closeds X)
  have hGIat (j : Fin n) : GeometricallyIrreducible
      (((I j).subschemeι ≫ f).fiberToSpecResidueField y) := by
    simpa using geometricallyIrreducible_fiber_of_restrict
      ((I j).subschemeι ≫ f) (W j) (hW j) ⟨y, hyW j⟩
  have hcoverAt : ∀ x : f.fiber y, ∃ j,
      x ∈ Set.range (Scheme.Hom.fiberMapComp (I j).subschemeι f y).base := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    have hmem : f.fiberι y x ∈ Set.range (I j).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hj
    refine ⟨j, ?_⟩
    rw [Scheme.Hom.range_fiberMapComp]
    simpa using hmem
  exact le_antisymm (geometricCount_le_of_fiberSubscheme_cover f y
    (SeparableClosure (Y.residueField y)) n I hGIat hcoverAt) hlower

private theorem exists_open_geometricCount_eq_of_genericComponents
    (H0554 : IrreducibleComponentsLowerBoundAfterShrinking.{u})
    (H0559 : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hgeneric : ∀ C : irreducibleComponents (f.fiber η), GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal (X := f.fiber η)
          ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    ∃ W : Set Y, IsOpen W ∧ η ∈ W ∧
      ∃ n : ℕ, ∀ y ∈ W, geometricIrreducibleComponentCount f y = n := by
  classical
  let Cs := irreducibleComponents (f.fiber η)
  let : Fintype Cs := (finite_irreducibleComponents_fiber f η).fintype
  let n : ℕ := Fintype.card Cs
  let e : Fin n ≃ Cs := (Fintype.equivFin Cs).symm
  have hcomp : Cs.ncard = n := by
    rw [Set.ncard_eq_toFinset_card' Cs]
    simp [n]
  let I : Fin n → X.IdealSheafData := fun j =>
    Scheme.IdealSheafData.vanishingIdeal
      (⟨closure (f.fiberι η '' ((e j).1 : Set (f.fiber η))), isClosed_closure⟩ : Closeds X)
  have hgenericGI (j : Fin n) : GeometricallyIrreducible
      (((I j).subschemeι ≫ f).fiberToSpecResidueField η) :=
    geometricallyIrreducible_fiber_of_component_closure f η (e j) (hgeneric (e j))
  have hcoverGeneric : ∀ x : f.fiber η, ∃ j, x ∈ (e j).1 := by
    intro x
    have hx : (x : f.fiber η) ∈ ⋃₀ Cs := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
    exact ⟨e.symm ⟨C, hC⟩, by simpa using hxC⟩
  obtain ⟨Ucover, hUcoverOpen, hUcoverNe, hUcovered⟩ :=
    exists_open_fiber_covered_by_closures f η hη (fun j : Fin n => (e j).1) hcoverGeneric
  obtain ⟨Ulower, hUlowerOpen, hUlowerNe, hlower⟩ :=
    exists_open_geometricCount_ge_n H0554 f η hη n hcomp
  have hWjExists (j : Fin n) : ∃ W : Y.Opens, Nonempty W ∧
      GeometricallyIrreducible (((I j).subschemeι ≫ f) ∣_ W) := by
    let gj := (I j).subschemeι ≫ f
    have : GeometricallyIrreducible (gj.fiberToSpecResidueField η) := by
      simpa [gj, I] using hgenericGI j
    have : LocallyOfFiniteType gj := inferInstance
    have : QuasiCompact gj := inferInstance
    exact H0559 gj inferInstance inferInstance inferInstance η hη inferInstance
  choose Wj hWjne hWjGI using hWjExists
  have hmem (U : Set Y) (hU : IsOpen U) (hne : U.Nonempty) : η ∈ U :=
    (hη.mem_open_set_iff hU).2 (by rwa [Set.univ_inter])
  refine ⟨Ucover ∩ Ulower ∩ ⋂ j, (Wj j : Set Y),
    (hUcoverOpen.inter hUlowerOpen).inter (isOpen_iInter_of_finite fun j => (Wj j).isOpen),
    Set.mem_inter (Set.mem_inter (hmem _ hUcoverOpen hUcoverNe) (hmem _ hUlowerOpen hUlowerNe))
      (Set.mem_iInter.mpr fun j => hmem (Wj j) (Wj j).isOpen ⟨_, (hWjne j).some.2⟩), n, ?_⟩
  rintro y ⟨⟨hycover, hylower⟩, hyW⟩
  exact geometricCount_eq_of_mem_cover f η n (fun j => (e j).1) Wj hWjGI y
    (Set.mem_iInter.mp hyW) (hUcovered y hycover) (hlower y hylower)

private theorem exists_open_geometricCount_eq_of_irreducible
    (H0554 : IrreducibleComponentsLowerBoundAfterShrinking.{u})
    (H0559 : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (_hη : IsGenericPoint η Set.univ) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧
      ∃ n : ℕ∞, ∀ y ∈ U, geometricIrreducibleComponentCount f y = n := by
  obtain ⟨V, hVne, Y', g, hgSurj, hgFinite, hgEtale, hYirr, hYaff,
      hpull, hg'Surj, hg'Finite, hg'Etale, hgeneric⟩ :=
    exists_nonemptyOpen_finiteEtale_cover_geometricallyIrreducible_genericFiber f
  let k := g ≫ V.ι
  let f' := pullback.fst k f
  have : IrreducibleSpace Y' := hYirr
  have : LocallyOfFiniteType f' := inferInstance
  have : QuasiCompact f' := inferInstance
  obtain ⟨W, hWopen, hηW, n, hconst⟩ :=
    exists_open_geometricCount_eq_of_genericComponents H0554 H0559 f' (genericPoint Y')
      (genericPoint_spec Y') (hgeneric _ (genericPoint_spec Y'))
  have hkOpen : IsOpenMap k := by
    dsimp [k]
    have : Etale g := hgEtale
    exact IsOpenMap.comp (f := g) (g := V.ι) V.ι.isOpenMap
      (Scheme.Hom.isOpenMap g)
  refine ⟨k '' W, hkOpen _ hWopen, ⟨_, _, hηW, rfl⟩, n, ?_⟩
  rintro _ ⟨z', hz'W, rfl⟩
  let e : Over.mk f' ≅ Over.mk (pullback.snd f k) :=
    Over.isoMk (pullbackSymmetry k f) (pullbackSymmetry_hom_comp_snd k f)
  calc
    geometricIrreducibleComponentCount f (k z') =
        geometricIrreducibleComponentCount (pullback.snd f k) z' := by
          simpa only [Function.comp_apply] using
            (congrFun (geometricIrreducibleComponentCount_pullback f k) z').symm
    _ = geometricIrreducibleComponentCount f' z' :=
      (congrFun (geometricCount_eq_of_overIso e) z').symm
    _ = n := hconst z' hz'W

end Helpers

/-- **Stacks Project, Tag 055A**, granted Tags 0554 and 0559. The number of geometrically
irreducible components of the fibres of a finite type morphism is constant on a nonempty open
subset of the closure of any point of the target.

No tag is attached: the statement carries the hypotheses `H0554` and `H0559`, which the Stacks
statement does not have. Discharging both turns this into Tag 055A. -/
public theorem exists_open_geometricIrreducibleComponentCount_eq
    (H0554 : IrreducibleComponentsLowerBoundAfterShrinking.{u})
    (H0559 : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    ∃ V : TopologicalSpace.Opens (↑(closure ({y} : Set Y))), Nonempty V ∧
      ∃ n : ℕ∞, ∀ z : V, geometricIrreducibleComponentCount f z.1.1 = n := by
  classical
  let S := closure ({y} : Set Y)
  let T : Closeds Y := ⟨S, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let Z := I.subscheme
  let i := I.subschemeι
  have hrange : Set.range i.base = S := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let h : Z ≃ₜ S :=
    i.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace S :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y)).closure
  have : IrreducibleSpace Z := h.irreducibleSpace_iff.mpr inferInstance
  let fZ := CategoryTheory.Limits.pullback.snd f i
  have : LocallyOfFiniteType fZ := inferInstance
  have : QuasiCompact fZ := inferInstance
  obtain ⟨U, hU, hUne, n, hconst⟩ :=
    exists_open_geometricCount_eq_of_irreducible H0554 H0559 fZ (genericPoint Z)
      (genericPoint_spec Z)
  let UZ : Z.Opens := ⟨U, hU⟩
  let V : TopologicalSpace.Opens S := h.opensCongr UZ
  refine ⟨V, ?_, ⟨n, ?_⟩⟩
  · obtain ⟨z, hz⟩ := hUne
    refine ⟨⟨h z, ?_⟩⟩
    simpa [V, UZ] using hz
  · intro z
    let zZ : Z := h.symm z.1
    have hzZ : zZ ∈ UZ := by
      show h.symm z.1 ∈ UZ
      simpa [V, UZ] using z.2
    have hzEq : i.base zZ = z.1.1 := by
      have hval : (h zZ).1 = i.base zZ := by
        simp [h, Topology.IsEmbedding.toHomeomorph, Homeomorph.setCongr]
      exact hval.symm.trans (congrArg Subtype.val (h.apply_symm_apply z.1))
    have hpull : geometricIrreducibleComponentCount f (i.base zZ) =
        geometricIrreducibleComponentCount fZ zZ := by
      simpa [fZ, Function.comp_apply] using
        (congrFun (geometricIrreducibleComponentCount_pullback f i) zZ).symm
    rw [← hzEq]
    exact hpull.trans (hconst zZ hzZ)

end AlgebraicGeometry
