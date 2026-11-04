module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicSpaceCoproductFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# The disjoint union of a locally finite family of closed subspaces

Let `Y` be an algebraic space over a scheme `S` and let `{Z_i}_{i ∈ I}` be a family of closed
subspaces of `Y`, indexed by a type in the universe of the site whose cardinality is below the
cutoff of the site. The disjoint union `∐ Z_i`, formed among fppf sheaves of sets, is an
algebraic space over `S`. When the sets of points of the `Z_i` form a locally finite family in
`|Y|`, the morphism `∐ Z_i ⟶ Y` restricting to the inclusions of the `Z_i` is proper. The ranges
of the coproduct injections are pairwise disjoint on points and cover `|∐ Z_i|`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspacesCoproduct`: the sheaf `∐ Z_i`.
* `AlgebraicGeometry.Space.closedSubspacesCoproductι`: the injection of a summand.
* `AlgebraicGeometry.Space.closedSubspacesCoproductDesc`: the morphism `∐ Z_i ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_closedSubspacesCoproduct`: `∐ Z_i` is an algebraic
  space.
* `AlgebraicGeometry.Space.isProper_closedSubspacesCoproductDesc`: `∐ Z_i ⟶ Y` is proper.
* `AlgebraicGeometry.Space.disjoint_range_pointsMap_closedSubspacesCoproductι` and
  `AlgebraicGeometry.Space.iUnion_range_pointsMap_closedSubspacesCoproductι`: the pieces are
  pairwise disjoint and cover the points.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0ERS](https://stacks.math.columbia.edu/tag/0ERS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u} (Z : I → Subfunctor Y)
  (hZ : ∀ i, IsClosedSubspace B S hS (Z i))

/-- A closed subspace, as an fppf sheaf. -/
abbrev closedSubspaceSheaf (i : I) : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ⟨(Z i).toFunctor, (hZ i).1.isSheaf⟩

/-- The disjoint union `∐ Z_i` of a family of closed subspaces, as an fppf sheaf. -/
def closedSubspacesCoproduct : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ∐ closedSubspaceSheaf Z hZ

/-- The injection of a summand into `∐ Z_i`. -/
def closedSubspacesCoproductι (i : I) :
    closedSubspaceSheaf Z hZ i ⟶ closedSubspacesCoproduct Z hZ :=
  Sigma.ι (closedSubspaceSheaf Z hZ) i

/-- `∐ Z_i` is the coproduct of the `Z_i`. -/
def isColimitClosedSubspacesCoproduct :
    IsColimit (Cofan.mk (closedSubspacesCoproduct Z hZ) (closedSubspacesCoproductι Z hZ)) :=
  coproductIsCoproduct (closedSubspaceSheaf Z hZ)

/-- The morphism `∐ Z_i ⟶ Y` restricting to the inclusion of each `Z_i`. -/
def closedSubspacesCoproductDesc (hY : IsAlgebraicSpace B S hS Y) :
    (closedSubspacesCoproduct Z hZ).obj ⟶ Y :=
  (Cofan.IsColimit.desc (isColimitClosedSubspacesCoproduct Z hZ)
    (fun i ↦ (ObjectProperty.homMk (Z i).ι :
      closedSubspaceSheaf Z hZ i ⟶ (⟨Y, hY.isSheaf⟩ : Sheaf _ (Type u))))).hom

/-- The morphism `∐ Z_i ⟶ Y` restricts to the inclusion of each `Z_i`. -/
@[reassoc (attr := simp)]
theorem closedSubspacesCoproductι_desc (hY : IsAlgebraicSpace B S hS Y) (i : I) :
    (closedSubspacesCoproductι Z hZ i).hom ≫ closedSubspacesCoproductDesc Z hZ hY = (Z i).ι :=
  congrArg (fun k ↦ k.hom) (Cofan.IsColimit.fac (isColimitClosedSubspacesCoproduct Z hZ)
    (fun i ↦ (ObjectProperty.homMk (Z i).ι :
      closedSubspaceSheaf Z hZ i ⟶ (⟨Y, hY.isSheaf⟩ : Sheaf _ (Type u)))) i)

/-- The injection of a summand is a monomorphism of presheaves. -/
theorem mono_closedSubspacesCoproductι (i : I) : Mono (closedSubspacesCoproductι Z hZ i).hom :=
  Sheaf.mono_hom_cofan_inj _ (isColimitClosedSubspacesCoproduct Z hZ) i

/-! ### Algebraicity -/

include hZ in
/-- Given an atlas `U ⟶ Y`, each closed subspace `Z i` has an atlas `W ⟶ Z i` with the size of
`W` at most that of `U`. -/
theorem exists_atlas_closedSubspace_size_le {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ Y)
    (hasurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (haet : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a) (i : I) :
    ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ (Z i).toFunctor),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      ((BigFppfOver.toScheme B S hS).obj W).size ≤ ((BigFppfOver.toScheme B S hS).obj U).size := by
  have hrep := (hZ i).2.1
  have hpb := (hrep.isPullback a).flip
  refine ⟨hrep.pullback a, hrep.fst a,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hasurj,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb haet, ?_⟩
  · have hci : AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hrep.snd a)) :=
      (hZ i).2.property a (hrep.fst a) (hrep.snd a) (hrep.isPullback a)
    exact Scheme.size_le_of_mono_quasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd a))

include hZ in
/-- The disjoint union of a family of closed subspaces of an algebraic space, indexed by a type of
cardinality below the cutoff of the site, is an algebraic space. -/
theorem isAlgebraicSpace_closedSubspacesCoproduct (hY : IsAlgebraicSpace B S hS Y)
    (hI : #I < B.cutoff) : IsAlgebraicSpace B S hS (closedSubspacesCoproduct Z hZ).obj := by
  obtain ⟨U, a, hasurj, haet⟩ := hY.exists_atlas
  choose W b hbsurj hbet hbsize using exists_atlas_closedSubspace_size_le Z hZ a hasurj haet
  have hU : ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff := U.left.property
  exact isAlgebraicSpace_coproduct_of_size_le B S hS (fun i ↦ (Z i).toFunctor)
    (fun i ↦ (hZ i).1) (closedSubspacesCoproduct Z hZ) (closedSubspacesCoproductι Z hZ)
    (isColimitClosedSubspacesCoproduct Z hZ) W b hbsurj hbet (Equiv.refl I)
    (μ := max ((BigFppfOver.toScheme B S hS).obj U).size #I)
    (le_max_of_le_left (Scheme.aleph0_le_size _)) (max_lt hU hI) (le_max_right _ _)
    (fun i ↦ le_max_of_le_left (hbsize i))

/-! ### The morphism to `Y` -/

variable (hY : IsAlgebraicSpace B S hS Y) (hI : #I < B.cutoff)

include hI in
/-- `∐ Z_i ⟶ Y` is separated. -/
theorem isSeparated_closedSubspacesCoproductDesc :
    IsSeparated B S hS (closedSubspacesCoproductDesc Z hZ hY) :=
  isSeparated_of_isColimit_cofan_small B S hS _ (isColimitClosedSubspacesCoproduct Z hZ)
    (fun i ↦ (hZ i).1) (isAlgebraicSpace_closedSubspacesCoproduct Z hZ hY hI) hY _
    fun i ↦ by simpa using isSeparated_of_isClosedImmersion B S hS _ (hZ i).2

include hI in
/-- `∐ Z_i ⟶ Y` is locally of finite type. -/
theorem isLocallyOfFiniteType_closedSubspacesCoproductDesc :
    IsLocallyOfFiniteType B S hS (closedSubspacesCoproductDesc Z hZ hY) :=
  isLocallyOfFiniteType_of_isColimit_cofan B S hS _ (isColimitClosedSubspacesCoproduct Z hZ)
    (fun i ↦ (hZ i).1) (isAlgebraicSpace_closedSubspacesCoproduct Z hZ hY hI) hY _
    fun i ↦ by simpa using isLocallyOfFiniteType_of_isClosedImmersion B S hS _ (hZ i).2

variable {Z hZ} (hfin : LocallyFinite fun i ↦ subspacePointSet B S hS Y (Z i))

include hI hfin in
/-- If the `|Z_i|` form a locally finite family, then `∐ Z_i ⟶ Y` is quasi-compact. -/
theorem isQuasiCompact_closedSubspacesCoproductDesc :
    IsQuasiCompact B S hS (closedSubspacesCoproductDesc Z hZ hY) := by
  refine isQuasiCompact_of_isColimit_cofan_of_cofinitely_isEmpty B S hS _
    (isColimitClosedSubspacesCoproduct Z hZ) (fun i ↦ (hZ i).1)
    (isAlgebraicSpace_closedSubspacesCoproduct Z hZ hY hI) hY _ (fun i ↦ ?_) fun T hT g ↦ ?_
  · simpa using isQuasiCompact_of_isClosedImmersion' B S hS (hZ i).2
  · have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
    have _ : CompactSpace (points B S hS (yoneda.obj T)) := compactSpace_points_yoneda B S hS T
    have hK : IsCompact (Set.range (pointsMap B S hS (yoneda.obj T) g)) :=
      isCompact_range (continuous_pointsMap B S hS g)
    refine ⟨_, hfin.finite_nonempty_inter_compact hK, fun i hi ↦ ?_⟩
    refine isEmpty_points_pullback_of_preimage_range_eq_empty B S hS g _ ?_
    rw [closedSubspacesCoproductι_desc]
    exact Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ hi ⟨pointsMap B S hS _ g x, hx, x, rfl⟩

include hY hI in
/-- Every point of `∐ Z_i` lies in the range of one of the injections. -/
theorem exists_mem_range_pointsMap_closedSubspacesCoproductι
    (p : points B S hS (closedSubspacesCoproduct Z hZ).obj) :
    ∃ i, p ∈ Set.range (pointsMap B S hS _ (closedSubspacesCoproductι Z hZ i).hom) := by
  have hcov := isZariskiCover_range_cofan_inj _ (isColimitClosedSubspacesCoproduct Z hZ)
    (fun i ↦ (hZ i).1)
  have hunion := (isZariskiCover_iff_iUnion_points B S hS _
    (isAlgebraicSpace_closedSubspacesCoproduct Z hZ hY hI) I
    (fun i ↦ Subfunctor.range (closedSubspacesCoproductι Z hZ i).hom)
    hcov.1).1 hcov
  have hp : p ∈ ⋃ i, Set.range (pointsMap B S hS _
      (Subfunctor.range (closedSubspacesCoproductι Z hZ i).hom).ι) := by
    rw [hunion]; trivial
  obtain ⟨i, q, rfl⟩ := Set.mem_iUnion.1 hp
  have _ := mono_closedSubspacesCoproductι Z hZ i
  obtain ⟨z, rfl⟩ := pointsMap_surjective_of_isIso B S hS
    (Subfunctor.toRange (closedSubspacesCoproductι Z hZ i).hom) q
  exact ⟨i, z, by rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩

/-- The ranges of two distinct injections into `∐ Z_i` have no point in common. -/
theorem disjoint_range_pointsMap_closedSubspacesCoproductι {i j : I} (hij : i ≠ j) :
    Disjoint (Set.range (pointsMap B S hS _ (closedSubspacesCoproductι Z hZ i).hom))
      (Set.range (pointsMap B S hS _ (closedSubspacesCoproductι Z hZ j).hom)) := by
  rw [Set.disjoint_iff]
  rintro _ ⟨⟨a, rfl⟩, b, hb⟩
  obtain ⟨x, rfl⟩ := Quot.exists_rep a
  obtain ⟨z, rfl⟩ := Quot.exists_rep b
  rw [pointsMap_class, pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hb
  obtain ⟨r, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := hb
  have h1 := NatTrans.naturality_apply (closedSubspacesCoproductι Z hZ j).hom α.op z.value
  have h2 := NatTrans.naturality_apply (closedSubspacesCoproductι Z hZ i).hom β.op x.value
  have hT : IsEmpty ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
    Sheaf.isEmpty_toScheme_of_eq_of_ne _ (isColimitClosedSubspacesCoproduct Z hZ) (Ne.symm hij)
      _ _ (h1.trans (hα.trans (hβ.symm.trans h2.symm)))
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of r.carrier)))
  exact hT.elim hne.some

include hY hI hfin in
/-- If the `|Z_i|` form a locally finite family, then `∐ Z_i ⟶ Y` is universally closed. -/
theorem universallyClosed_closedSubspacesCoproductDesc :
    UniversallyClosed B S hS (closedSubspacesCoproductDesc Z hZ hY) := by
  intro T hT g
  set d := closedSubspacesCoproductDesc Z hZ hY
  let m : ∀ i, pullback g (Z i).ι ⟶ pullback g d := fun i ↦
    pullback.map g (Z i).ι g d (𝟙 T) (closedSubspacesCoproductι Z hZ i).hom (𝟙 Y)
      (by simp) (by simp [d])
  have hm : ∀ i, m i ≫ pullback.fst g d = pullback.fst g (Z i).ι := fun i ↦ by simp [m]
  have hsq : ∀ i, IsPullback (m i) (pullback.snd g (Z i).ι) (pullback.snd g d)
      (closedSubspacesCoproductι Z hZ i).hom := fun i ↦ by
    refine IsPullback.of_right ?_ (by simp [m]) (IsPullback.of_hasPullback g d)
    rw [hm i, closedSubspacesCoproductι_desc]
    exact IsPullback.of_hasPullback g (Z i).ι
  have hci : ∀ i, IsClosedImmersion B S hS (pullback.fst g (Z i).ι) := fun i ↦
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback g (Z i).ι).flip (hZ i).2
  intro C hC
  have himage : pointsMap B S hS _ (pullback.fst g d) '' C =
      ⋃ i, pointsMap B S hS _ (pullback.fst g (Z i).ι) ''
        (pointsMap B S hS _ (m i) ⁻¹' C) := by
    ext t
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨fun ⟨q, hqC, hq⟩ ↦ ?_, fun ⟨i, w, hwC, hw⟩ ↦ ⟨_, hwC, by rw [← hw, ← hm i,
      pointsMap_comp_apply]⟩⟩
    obtain ⟨i, z, hz⟩ := exists_mem_range_pointsMap_closedSubspacesCoproductι hY hI
      (pointsMap B S hS _ (pullback.snd g d) q)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (hsq i) q z hz.symm
    exact ⟨i, w, hw ▸ hqC, by rw [← hq, ← hm i, pointsMap_comp_apply, hw]⟩
  rw [himage]
  have hlf : LocallyFinite fun i ↦ pointsMap B S hS _ (pullback.fst g (Z i).ι) ''
      (pointsMap B S hS _ (m i) ⁻¹' C) := by
    refine (hfin.preimage_continuous (continuous_pointsMap B S hS g)).subset fun i ↦ ?_
    rintro _ ⟨w, -, rfl⟩
    refine ⟨pointsMap B S hS _ (pullback.snd g (Z i).ι) w, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition]
  exact hlf.isClosed_iUnion fun i ↦
    (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hT (hci i)).isClosedMap _
      (hC.preimage (continuous_pointsMap B S hS (m i)))

include hI hfin in
/-- The disjoint union of a locally finite family of closed subspaces is proper over the ambient
space. -/
theorem isProper_closedSubspacesCoproductDesc :
    IsProper B S hS (closedSubspacesCoproductDesc Z hZ hY) :=
  ⟨isSeparated_closedSubspacesCoproductDesc Z hZ hY hI,
    ⟨isLocallyOfFiniteType_closedSubspacesCoproductDesc Z hZ hY hI,
      isQuasiCompact_closedSubspacesCoproductDesc hY hI hfin⟩,
    universallyClosed_closedSubspacesCoproductDesc hY hI hfin⟩

end AlgebraicGeometry.Space

end
