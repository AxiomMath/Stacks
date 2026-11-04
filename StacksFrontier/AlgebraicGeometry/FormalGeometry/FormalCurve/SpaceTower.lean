module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Formal curves of algebraic spaces whose members are schemes

A cartesian tower `X₀ ⟶ X₁ ⟶ ⋯` of algebraic spaces over the adic thickenings `Sₙ` of `Spec A`,
every member of which is representable, is a cartesian tower of schemes
(`AlgebraicGeometry.Space.exists_schemeTower_of_isRepresentable`). When `X₀ ⟶ S₀` is proper and
`dim X₀ ≤ 1` the scheme form of [Stacks, Tag 0E7R]
(`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`) applies, and its
output, an H-projective scheme over `Spec A`, lies in the site and algebraizes the tower of spaces
(`AlgebraicGeometry.Space.exists_algebraization_of_isRepresentable`).

Properness of `X₀ ⟶ S₀` is transported through `AlgebraicGeometry.Space.presheaf_isProper_iff`
and the dimension through `AlgebraicGeometry.Space.dimension_yoneda_eq_topologicalKrullDim`; the
H-projective scheme is in the site because it is of finite type over `Spec A`
([Stacks, Tag 04T7]).

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The adic thickenings of a scheme of the site lie in the site**: `Spec (A / I ^ (n + 1))` is
of finite type over `Spec A` and quasi-compact ([Stacks, Tag 04T7]). -/
theorem contains_adicThickening (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of A))) (n : ℕ) : B.Contains (adicThickening A I n) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion (adicThickeningι A I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (Scheme.size_le_of_locallyOfFiniteType (adicThickeningι A I n)).trans_lt hS

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- The scheme underlying the `n`-th adic thickening object is the `n`-th adic thickening. -/
lemma toScheme_obj_adicThickeningObject (n : ℕ) :
    (BigFppfOver.toScheme B (Spec (.of A)) hS).obj (adicThickeningObject A I B hS hSn n) =
      adicThickening A I n := rfl

/-- The scheme morphism underlying the transition morphism of thickening objects. -/
lemma toScheme_map_adicThickeningSuccMap (n : ℕ) :
    (BigFppfOver.toScheme B (Spec (.of A)) hS).map (adicThickeningSuccMap A I B hS hSn n) =
      adicThickeningSucc A I n := rfl

/-- **A representable cartesian tower of algebraic spaces over the adic thickenings is a
cartesian tower of schemes.** -/
theorem exists_schemeTower_of_isRepresentable
    (X : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
    (p : ∀ n, X n ⟶ yoneda.obj (adicThickeningObject A I B hS hSn n))
    (i : ∀ n, X n ⟶ X (n + 1))
    (hcart : ∀ n, IsPullback (i n) (p n) (p (n + 1))
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n)))
    (hrep : ∀ n, (X n).IsRepresentable) :
    ∃ (U : ℕ → BigFppfOver B (Spec (.of A)) hS) (α : ∀ n, yoneda.obj (U n) ≅ X n)
      (φ : ∀ n, U n ⟶ adicThickeningObject A I B hS hSn n) (ι : ∀ n, U n ⟶ U (n + 1)),
      (∀ n, yoneda.map (φ n) = (α n).hom ≫ p n) ∧
      (∀ n, yoneda.map (ι n) ≫ (α (n + 1)).hom = (α n).hom ≫ i n) ∧
      ∀ n, IsPullback ((BigFppfOver.toScheme B _ hS).map (ι n))
        ((BigFppfOver.toScheme B _ hS).map (φ n))
        ((BigFppfOver.toScheme B _ hS).map (φ (n + 1))) (adicThickeningSucc A I n) := by
  let U : ∀ n, BigFppfOver B (Spec (.of A)) hS := fun n => (X n).reprX
  let α : ∀ n, yoneda.obj (U n) ≅ X n := fun n => (X n).reprW
  let φ : ∀ n, U n ⟶ adicThickeningObject A I B hS hSn n :=
    fun n => Yoneda.fullyFaithful.preimage ((α n).hom ≫ p n)
  let ι : ∀ n, U n ⟶ U (n + 1) :=
    fun n => Yoneda.fullyFaithful.preimage ((α n).hom ≫ i n ≫ (α (n + 1)).inv)
  have hφ : ∀ n, yoneda.map (φ n) = (α n).hom ≫ p n := fun n =>
    Yoneda.fullyFaithful.map_preimage _
  have hι : ∀ n, yoneda.map (ι n) ≫ (α (n + 1)).hom = (α n).hom ≫ i n := fun n => by
    rw [Yoneda.fullyFaithful.map_preimage]; simp
  refine ⟨U, α, φ, ι, hφ, hι, fun n => ?_⟩
  have hY : IsPullback (yoneda.map (ι n)) (yoneda.map (φ n)) (yoneda.map (φ (n + 1)))
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n)) := by
    refine IsPullback.of_iso (hcart n) (α n).symm (α (n + 1)).symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← hι, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, hφ, Iso.inv_hom_id_assoc]
    · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, hφ, Iso.inv_hom_id_assoc]
    · simp
  have hU : IsPullback (ι n) (φ n) (φ (n + 1)) (adicThickeningSuccMap A I B hS hSn n) :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using hY.w)) hY
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B (Spec (.of A)) hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B _ hS
  exact hU.map (BigFppfOver.toScheme B (Spec (.of A)) hS)

/-- The morphism from a site object over `Spec A` to the base object. -/
abbrev siteObjectToBase {Y : Scheme.{u}} (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)) :
    siteObject B (Spec (.of A)) hS hY fY ⟶ baseObject A B hS :=
  Over.homMk (ObjectProperty.homMk fY : B.obj hY ⟶ B.obj hS)

/-- **The algebraization of a representable formal curve.** A cartesian tower of algebraic
spaces over the adic thickenings, every member of which is a scheme, with bottom member proper
over `S₀` and of dimension at most one, is the system of adic fibres of an H-projective scheme
over `Spec A` lying in the site. -/
theorem exists_algebraization_of_isRepresentable [IsNoetherianRing A] [IsAdicComplete I A]
    (X : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
    (hX : ∀ n, IsAlgebraicSpace B (Spec (.of A)) hS (X n))
    (p : ∀ n, X n ⟶ yoneda.obj (adicThickeningObject A I B hS hSn n))
    (i : ∀ n, X n ⟶ X (n + 1))
    (hcart : ∀ n, IsPullback (i n) (p n) (p (n + 1))
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n)))
    (hproper : IsProper B (Spec (.of A)) hS (p 0))
    (hdim : dimension B (Spec (.of A)) hS (X 0) (hX 0) ≤ 1)
    (hrep : ∀ n, (X n).IsRepresentable) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)), IsProjectiveMorphism fY ∧
      ∃ k : ∀ n, X n ⟶ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY),
        (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (p n) (yoneda.map (siteObjectToBase A B hS hY fY))
          (yoneda.map (adicThickeningMap A I B hS hSn n)) := by
  set T := BigFppfOver.toScheme B (Spec (.of A)) hS with hT
  obtain ⟨U, α, φ, ι, hφ, hι, hsq⟩ :=
    exists_schemeTower_of_isRepresentable A I B hS hSn X p i hcart hrep
  -- properness of the bottom member
  have hiso (Q : MorphismProperty ((BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u))
      [Q.RespectsIso] : Q (p 0) ↔ Q (yoneda.map (φ 0)) := by
    rw [hφ 0]
    exact (MorphismProperty.cancel_left_of_respectsIso Q (α 0).hom _).symm
  have hrel : yoneda.relativelyRepresentable (p 0) :=
    (hiso _).mpr (Functor.relativelyRepresentable.map yoneda (φ 0))
  have hP : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsProper.{u} :
      MorphismProperty Scheme.{u}) T).presheaf (p 0) :=
    (presheaf_isProper_iff B _ hS (p 0) (hX 0) (isAlgebraicSpace_yoneda B _ hS _) hrel).mp
      hproper
  have hPφ := (hiso _).mp hP
  have hproper0 : _root_.AlgebraicGeometry.IsProper (T.map (φ 0)) :=
    (presheaf_yoneda_map_iff B _ hS (P := @_root_.AlgebraicGeometry.IsProper)
      inferInstance (φ 0)).mp hPφ
  -- dimension of the bottom member
  have hdim' : topologicalKrullDim (T.obj (U 0) : Type u) ≤ 1 := by
    rw [← dimension_yoneda_eq_topologicalKrullDim B _ hS (U 0),
      dimension_eq_of_iso B _ hS (isAlgebraicSpace_yoneda B _ hS (U 0)) (hX 0) (α 0)]
    exact hdim
  obtain ⟨Y, fY, hfY, k, hk, hkpb⟩ :=
    Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one A I
    (Xn := fun n => T.obj (U n))
    (fun n => T.map (φ n)) (fun n => T.map (ι n)) hsq hproper0 hdim'
  have : _root_.AlgebraicGeometry.IsProper fY := isProper_of_isProjectiveMorphism fY hfY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
  have hY : B.Contains Y := (Scheme.size_le_of_locallyOfFiniteType fY).trans_lt hS
  have hw : ∀ n, k n ≫ fY = B.inclusion.map (U n).hom := fun n => by
    rw [(hkpb n).w]
    exact congrArg B.inclusion.map (Over.w (φ n))
  let κ : ∀ n, U n ⟶ siteObject B (Spec (.of A)) hS hY fY := fun n =>
    Over.homMk (ObjectProperty.homMk (k n) : (U n).left ⟶ B.obj hY)
      (ObjectProperty.hom_ext _ (hw n))
  refine ⟨Y, hY, fY, hfY, fun n => (α n).inv ≫ yoneda.map (κ n), fun n => ?_, fun n => ?_⟩
  · have hκ : ι n ≫ κ (n + 1) = κ n := by
      ext
      exact hk n
    show i n ≫ (α (n + 1)).inv ≫ yoneda.map (κ (n + 1)) = (α n).inv ≫ yoneda.map (κ n)
    rw [← cancel_epi (α n).hom, ← Category.assoc, ← hι n, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← yoneda.map_comp, hκ]
  · have _ : PreservesLimitsOfShape WalkingCospan T :=
      preservesLimitsOfShape_walkingCospan_toScheme B _ hS
    have _ : ReflectsLimitsOfShape WalkingCospan T :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    have hU : IsPullback (κ n) (φ n) (siteObjectToBase A B hS hY fY)
        (adicThickeningMap A I B hS hSn n) :=
      IsPullback.of_map_of_faithful T (hkpb n)
    refine IsPullback.of_iso (hU.map yoneda) (α n) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · rw [Iso.refl_hom, Category.comp_id, hφ n]
    · simp
    · simp

end AlgebraicGeometry.Space

end
