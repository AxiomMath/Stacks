module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension

/-!
# Families of curves descend along fppf coverings of the base

Let `q : Q ⟶ S` be a morphism from an algebraic space to a scheme of the site, and `{Wᵢ ⟶ S}` an
fppf covering by schemes of the site such that every base change `Q ×_S Wᵢ ⟶ Wᵢ` is a family of
curves. Then `Q ⟶ S` is a family of curves: flatness (Stacks 041W), properness (Stacks 0422
through its constituents 0421, 041U and the fpqc locality of universal closedness) and finite
presentation (Stacks 041T with 041L and 041N) are local on the base for the fppf topology, and the
relative dimension at a point of `Q` is the relative dimension at a point of some `Q ×_S Wᵢ` over
it (Stacks 0D4N).

This is the first step of the descent of the glued stabilization in Stacks 0E8A.

## Main results

* `AlgebraicGeometry.Space.prop_of_isPullback_of_isFppfCovering`: a property of morphisms of
  algebraic spaces local on the target for the fppf topology holds for a morphism once it holds
  for its base changes along the members of an fppf covering.
* `AlgebraicGeometry.CurveFamily.ofIsFppfCovering`: the family of curves `Q ⟶ S`.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A property local on the target descends along an fppf covering.** If `P` is local on the
target for the fppf topology and every base change of `q : Q ⟶ Z` along the members of an fppf
covering `{fᵢ : Uᵢ ⟶ Z}` has `P`, then `q` has `P`. The base changes are given by cartesian
squares. -/
theorem prop_of_isPullback_of_isFppfCovering (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {Q Z : AlgebraicSpaces B S hS} (q : Q ⟶ Z) {ι : Type v} {U : ι → AlgebraicSpaces B S hS}
    (f : ∀ i, U i ⟶ Z) (hcov : IsFppfCovering B S hS (fun i => (U i).obj) (fun i => (f i).hom))
    {Y : ι → AlgebraicSpaces B S hS} {r : ∀ i, Y i ⟶ Q} {g : ∀ i, Y i ⟶ U i}
    (hsq : ∀ i, IsPullback (r i) (g i) q (f i)) (hg : ∀ i, P (g i)) : P q := by
  have hR : Presieve.ofArrows U f ∈ Topology.fppf.precoverage.{u, v} B S hS Z :=
    ⟨ι, U, f, rfl, Z.property, fun j => (U j).property, hcov⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hR ?_
  intro W k _ hk
  obtain ⟨i⟩ := hk
  refine (P.cancel_left_of_respectsIso (hsq i).isoPullback.hom _).mp ?_
  rw [(hsq i).isoPullback_hom_snd]
  exact hg i

end Space

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A property of morphisms of the structure morphism of a family of curves holds for its transport
to an equal base. -/
theorem prop_toBase_comp_eqToHom (P : MorphismProperty (AlgebraicSpaces B integerBase hZ))
    (Y : CurveFamily B hZ) {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q)
    (h : P Y.toBase) : P (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- The relative dimension bound of a family of curves holds for its transport to an equal
base. -/
theorem relativeDimensionLE_toBase_comp_eqToHom (Y : CurveFamily B hZ)
    {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q)
    (x : Space.points B integerBase hZ Y.total.obj) :
    ∃ e : ℕ, e ≤ 1 ∧ Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ
      (@HasFiberDimensionAt.{u} (e : ℕ∞)) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom x := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using Y.relativeDimensionLE x

variable {S₀ : BigFppfOver B integerBase hZ} {Q : AlgebraicSpaces B integerBase hZ}
  (q : Q ⟶ schemeSpace S₀) {ι : Type v} {W : ι → BigFppfOver B integerBase hZ}
  (φ : ∀ i, W i ⟶ S₀)
  (hcov : Space.IsFppfCovering B integerBase hZ (fun i => (schemeSpace (W i)).obj)
    (fun i => (schemeSpaceMap (φ i)).hom))
  {Y : ι → CurveFamily B hZ} (hY : ∀ i, (Y i).base = W i) (r : ∀ i, (Y i).total ⟶ Q)
  (hsq : ∀ i, IsPullback (r i) ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))) q
    (schemeSpaceMap (φ i)))

include hcov hsq in
/-- Every point of `Q` comes from a point of some `Yᵢ`. -/
theorem exists_pointsMap_eq_of_isFppfCovering (x : Space.points B integerBase hZ Q.obj) :
    ∃ i, ∃ y : Space.points B integerBase hZ (Y i).total.obj,
      Space.pointsMap B integerBase hZ _ (r i).hom y = x := by
  have hQ := Space.isFppfCovering_pullback_fst B integerBase hZ (fun i => schemeSpace (W i))
    (fun i => schemeSpaceMap (φ i)) hcov Q q
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hQ.jointly_surjective x)
  refine ⟨i, Space.pointsMap B integerBase hZ _ (hsq i).isoPullback.inv.hom y, ?_⟩
  have hr : (r i).hom =
      (hsq i).isoPullback.hom.hom ≫ (pullback.fst q (schemeSpaceMap (φ i))).hom :=
    congrArg (fun k => k.hom) (hsq i).isoPullback_hom_fst.symm
  have hid : (hsq i).isoPullback.inv.hom ≫ (hsq i).isoPullback.hom.hom = 𝟙 _ :=
    congrArg (fun k => k.hom) (hsq i).isoPullback.inv_hom_id
  rw [hr, ← Space.pointsMap_comp_apply, ← Category.assoc, hid, Category.id_comp]
  exact hy

include hcov hsq in
/-- The morphism `q` is of finite presentation, its base changes along an fppf covering being so
(Stacks 041T, 041L, 041N). -/
theorem isFinitePresentation_of_isFppfCovering :
    Space.IsFinitePresentation B integerBase hZ q.hom := by
    have hqs : (Space.quasiSeparatedProperty B integerBase hZ).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B integerBase hZ)
    let P : MorphismProperty (AlgebraicSpaces B integerBase hZ) :=
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (f : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B integerBase hZ f.hom) ⊓
      (Space.quasiCompactProperty B integerBase hZ ⊓ Space.quasiSeparatedProperty B integerBase hZ)
    have : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      MorphismProperty.IsLocalAtTarget.inf _ _
    exact Space.prop_of_isPullback_of_isFppfCovering P q _ hcov hsq
      (fun i => prop_toBase_comp_eqToHom P (Y i) (hY i) (Y i).finitePresentation)

/-- **Families of curves descend along fppf coverings of the base.** If `q : Q ⟶ S₀` becomes a
family of curves `Yᵢ ⟶ Wᵢ` after base change along every member of an fppf covering
`{φᵢ : Wᵢ ⟶ S₀}`, then `q` is a family of curves. -/
abbrev ofIsFppfCovering : CurveFamily B hZ where
  base := S₀
  total := Q
  toBase := q
  flat := by
    have : MorphismProperty.IsLocalAtTarget
        (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (f : F ⟶ G) =>
          Space.IsFlat B integerBase hZ f.hom)
        (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B integerBase hZ)
    exact Space.prop_of_isPullback_of_isFppfCovering
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (f : F ⟶ G) =>
        Space.IsFlat B integerBase hZ f.hom) q _ hcov hsq
      (fun i => prop_toBase_comp_eqToHom (fun ⦃F G⦄ (f : F ⟶ G) =>
        Space.IsFlat B integerBase hZ f.hom) (Y i) (hY i) (Y i).flat)
  proper := by
    have hsep : (Space.separatedProperty B integerBase hZ).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B integerBase hZ)
    have huc : (Space.universallyClosedProperty B integerBase hZ).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B integerBase hZ)
    have : (Space.properProperty B integerBase hZ).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, v} B integerBase hZ) :=
      Space.properProperty_isLocalAtTarget B integerBase hZ hsep inferInstance huc
    exact Space.prop_of_isPullback_of_isFppfCovering (Space.properProperty B integerBase hZ) q _
      hcov hsq (fun i => prop_toBase_comp_eqToHom (Space.properProperty B integerBase hZ) (Y i)
        (hY i) (Y i).proper)
  finitePresentation := isFinitePresentation_of_isFppfCovering q φ hcov hY r hsq
  relativeDimensionLE := by
    intro x
    obtain ⟨i, y, rfl⟩ := exists_pointsMap_eq_of_isFppfCovering q φ hcov hY r hsq x
    obtain ⟨e, he, hrel⟩ := relativeDimensionLE_toBase_comp_eqToHom (Y i) (hY i) y
    refine ⟨e, he, ?_⟩
    have hlft : Space.IsLocallyOfFiniteType B integerBase hZ q.hom :=
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        (isFinitePresentation_of_isFppfCovering q φ hcov hY r hsq).1
    exact (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ
      (AlgebraicSpaces.isPullback_hom B integerBase hZ (hsq i)) Q.property
      (isAlgebraicSpace_yoneda B integerBase hZ (W i))
      (isAlgebraicSpace_yoneda B integerBase hZ S₀) hlft y (e : ℕ∞)).mpr hrel

end CurveFamily

end AlgebraicGeometry

end
