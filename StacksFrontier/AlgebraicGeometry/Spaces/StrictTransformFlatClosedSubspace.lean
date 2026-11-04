module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAtPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComparisonOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedFunctionsKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections

/-!
# Flat closed subspaces containing the complement of an effective Cartier divisor

Let `S` be a scheme, let `D ⊆ A'` be an effective Cartier divisor on an algebraic space over
`S`, let `q : P ⟶ A'` be a morphism of algebraic spaces and write `q⁻¹D ⊆ P` for the inverse
image.  A closed subspace `C ⊆ P` is determined by `P ∖ q⁻¹D` as soon as it is flat over `A'`
and contains `P ∖ q⁻¹D`: if `C₁, C₂ ⊆ P` are closed subspaces, `C₁` is flat over `A'` and `C₂`
contains `P ∖ q⁻¹D`, then `C₁ ⊆ C₂`.

On an étale chart `W` of `P`, a function in the ideal of `C₂` vanishes over `P ∖ q⁻¹D`,
because that open subspace lies in `C₂`, so it is supported on `|q⁻¹D|`.  A function supported
on `|q⁻¹D|` maps into `𝒪_{C₁}` to a function supported on the inverse image of `D` in `C₁`,
which is zero because `C₁` is flat over `A'` and `D` is effective Cartier (the structure-sheaf
case of Stacks 05VW).  So the ideal of `C₂` lies in that of `C₁`, which is `C₁ ⊆ C₂` by
Stacks 03MB.

Applied to the projection `X ×_A A' ⟶ A'` of a blowup `b : A' ⟶ A` of `A` in `Z`, with `D` the
exceptional divisor `b⁻¹Z`, this says that the strict transform of `X` is the only closed
subspace of `X ×_A A'` which is flat over `A'` and contains the complement of the exceptional
preimage.  This is the identification `s⁻¹U' = t⁻¹U'` used in the proof of Stacks 0CQ4.

## Main results

* `AlgebraicGeometry.Space.exceptionalPreimageComplement_le_strictTransformSubfunctor`: the
  strict transform contains the complement of the exceptional preimage.
* `AlgebraicGeometry.Space.definingIdealAt_le_supportedSections_of_openComplement_le`: the
  ideal of a closed subspace containing `P ∖ D` consists of functions supported on `|D|`.
* `AlgebraicGeometry.Space.le_of_isFlat_of_openComplement_le`: a closed subspace flat over `A'`
  lies in every closed subspace containing `P ∖ q⁻¹D`.
* `AlgebraicGeometry.Space.eq_of_isFlat_of_openComplement_le`: two closed subspaces flat over
  `A'` and containing `P ∖ q⁻¹D` coincide.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_isFlat`: a closed subspace of
  `X ×_A A'` flat over the blowup and containing the complement of the exceptional preimage is
  the strict transform.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The strict transform contains the complement of the exceptional preimage -/

section Complement

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1)

/-- **The strict transform contains the complement of the exceptional preimage.**  For `b` the
blowup of `A` in `Z`, the open complement of `pr_{A'}^{-1}(b⁻¹Z)` in `X ×_A A'` is contained in
the strict transform of `X`, the exceptional divisor `b⁻¹Z` being effective Cartier. -/
theorem exceptionalPreimageComplement_le_strictTransformSubfunctor
    (hb : IsBlowupAlong B S hS Z b) :
    (exceptionalPreimageComplement B S hS f b Z).1 ≤
      strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom) := by
  have h := range_le_strictTransformSubfunctor_of_points_notMem B S hS f b
    (preimageClosedSubspace b Z) hb.isPullbackDefined
    (exceptionalPreimageComplementι B S hS f b Z)
    (subspacePointSet_openComplement B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageClosedSubspace B S hS f b Z)).le
  rwa [show (exceptionalPreimageComplementι B S hS f b Z).hom =
      (exceptionalPreimageComplement B S hS f b Z).1.ι from rfl, Subfunctor.range_ι] at h

end Complement

/-! ### Closed subspaces containing the complement of a closed subspace -/

/-- **The ideal of a closed subspace containing `P ∖ D` is supported on `|D|`.**  If a closed
subspace `C` of an algebraic space `P` contains the open complement of a closed subspace `D`,
then on every étale chart the defining ideal of `C` consists of functions supported on `|D|`. -/
theorem definingIdealAt_le_supportedSections_of_openComplement_le {P : AlgebraicSpaces B S hS}
    (D C : ClosedSubspaces B S hS P.1)
    (hC : (openComplementOfClosedSubspace B S hS P D).1 ≤ C.1) (W : SmallEtale B S hS P.1) :
    definingIdealAt B S hS P C (op W) ≤
      (supportedSectionsSubmodule B S hS P.1 P.2 (subspacePointSet B S hS P.1 D.1)
        (SheafOfModules.unit (structureRingSheaf B S hS P))).toSubmodule.obj (op W) := by
  have hT : IsClosed (subspacePointSet B S hS P.1 D.1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS P.2 D.1.ι D.2.2
  intro s hs
  refine (mem_supportedSectionsSubmodule_iff B S hS P.1 P.2 (subspacePointSet B S hS P.1 D.1)
    (SheafOfModules.unit (structureRingSheaf B S hS P)) W s).2 ?_
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS P _ hT
    (SheafOfModules.unit (structureRingSheaf B S hS P)) W s fun U₀ i hi => ?_
  set Y₀ : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj ((SmallEtale.toOver B S hS P.1).obj U₀),
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _⟩ with hY₀
  have hw : yoneda.map ((SmallEtale.toOver B S hS P.1).map i) ≫ W.1.hom = U₀.1.hom :=
    CostructuredArrow.w i.hom
  have hrange : Set.range (pointsMap B S hS Y₀.1 U₀.1.hom) ⊆
      Set.range (pointsMap B S hS (openComplementOfClosedSubspace B S hS P D).1.toFunctor
        (openComplementOfClosedSubspace B S hS P D).1.ι) := by
    rintro y ⟨z, rfl⟩
    rw [show Set.range (pointsMap B S hS
        (openComplementOfClosedSubspace B S hS P D).1.toFunctor
        (openComplementOfClosedSubspace B S hS P D).1.ι) =
        subspacePointSet B S hS P.1 (openComplementOfClosedSubspace B S hS P D).1 from rfl,
      subspacePointSet_openComplement]
    have hz := hi z
    rw [← hw, pointsMap_comp]
    exact hz
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS P.2 Y₀.2 _
    (openComplementOfClosedSubspace B S hS P D).2 U₀.1.hom).2 hrange
  have hD : Subfunctor.range U₀.1.hom ≤ C.1 := by
    rw [← hg]
    exact (Subfunctor.range_comp_le _ _).trans ((Subfunctor.range_ι _).le.trans hC)
  refine definingIdealAt_le_ker_of_comp_eq B S hS P Y₀ C (ObjectProperty.homMk U₀.1.hom)
    (ObjectProperty.homMk (Subfunctor.lift U₀.1.hom hD))
    (ObjectProperty.hom_ext _ (Subfunctor.lift_ι _ hD)) W
    ((SmallEtale.toOver B S hS P.1).map i) (𝟙 _) ?_ hs
  rw [Category.id_comp]
  exact hw

/-- **A closed subspace flat over `A'` lies in every closed subspace containing `P ∖ q⁻¹D`.**
Let `D ⊆ A'` be an effective Cartier divisor and `q : P ⟶ A'`.  If `C₂ ⊆ P` contains the open
complement of `q⁻¹D` and `C₁ ⊆ P` is flat over `A'`, then `C₁ ⊆ C₂`. -/
theorem le_of_isFlat_of_openComplement_le {A' P : AlgebraicSpaces B S hS} (q : P ⟶ A')
    (D : ClosedSubspaces B S hS A'.1) (hD : IsEffectiveCartierDivisor B S hS A' D)
    (C₁ C₂ : ClosedSubspaces B S hS P.1)
    (h₂ : (openComplementOfClosedSubspace B S hS P (preimageClosedSubspace q D)).1 ≤ C₂.1)
    (h₁ : IsFlat B S hS (C₁.1.ι ≫ q.hom)) :
    C₁.1 ≤ C₂.1 := by
  set Q : AlgebraicSpaces B S hS := ⟨C₁.1.toFunctor, C₁.2.1⟩ with hQ
  set ι : Q ⟶ P := ObjectProperty.homMk C₁.1.ι with hι
  set T := subspacePointSet B S hS P.1 (preimageClosedSubspace q D).1 with hTdef
  have hT : IsClosed T :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS P.2 _
      (preimageClosedSubspace q D).2.2
  have hset : Set.range (pointsMap B S hS (D.1.preimage (ι ≫ q).hom).toFunctor
        (D.1.preimage (ι ≫ q).hom).ι) = pointsMap B S hS Q.1 ι.hom ⁻¹' T := by
    rw [range_pointsMap_preimage_ι, hTdef,
      show subspacePointSet B S hS P.1 (preimageClosedSubspace q D).1 =
        Set.range (pointsMap B S hS (D.1.preimage q.hom).toFunctor
          (D.1.preimage q.hom).ι) from rfl,
      range_pointsMap_preimage_ι, ← Set.preimage_comp, ← pointsMap_comp]
    rfl
  have hno : HasNoSectionsSupportedIn B S hS Q (pointsMap B S hS Q.1 ι.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS Q)) := by
    have h := hasNoSectionsSupportedIn_preimage_of_isFlatAt B S hS (ι ≫ q) D
      (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS A' D hD)
      (fun y _ => (isFlat_iff_forall_isFlatAt B S hS _).1 h₁ y)
    intro W₀ s hs
    refine h W₀ s ?_
    rw [hset]
    exact hs
  refine le_of_forall_definingIdealAt_le B S hS P C₁ C₂ fun W _ => ?_
  exact (definingIdealAt_le_supportedSections_of_openComplement_le B S hS _ C₂ h₂ W).trans
    (supportedSectionsSubmodule_le_kernelIdealSheaf B S hS ι T hT hno (op W))

/-- **Two closed subspaces flat over `A'` and containing `P ∖ q⁻¹D` coincide**, for `D ⊆ A'` an
effective Cartier divisor and `q : P ⟶ A'`. -/
theorem eq_of_isFlat_of_openComplement_le {A' P : AlgebraicSpaces B S hS} (q : P ⟶ A')
    (D : ClosedSubspaces B S hS A'.1) (hD : IsEffectiveCartierDivisor B S hS A' D)
    (C₁ C₂ : ClosedSubspaces B S hS P.1)
    (h₁ : (openComplementOfClosedSubspace B S hS P (preimageClosedSubspace q D)).1 ≤ C₁.1)
    (h₂ : (openComplementOfClosedSubspace B S hS P (preimageClosedSubspace q D)).1 ≤ C₂.1)
    (hf₁ : IsFlat B S hS (C₁.1.ι ≫ q.hom)) (hf₂ : IsFlat B S hS (C₂.1.ι ≫ q.hom)) :
    C₁ = C₂ :=
  Subtype.ext (le_antisymm (le_of_isFlat_of_openComplement_le B S hS q D hD C₁ C₂ h₂ hf₁)
    (le_of_isFlat_of_openComplement_le B S hS q D hD C₂ C₁ h₁ hf₂))

/-! ### The strict transform as the flat closure of the complement of the exceptional preimage -/

section StrictTransform

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1)

/-- **A closed subspace of `X ×_A A'` flat over the blowup and containing the complement of the
exceptional preimage is the strict transform of `X`**, for `b` the blowup of `A` in `Z`. -/
theorem strictTransformSubfunctor_eq_of_isFlat (hb : IsBlowupAlong B S hS Z b)
    (C : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1)
    (hC : (exceptionalPreimageComplement B S hS f b Z).1 ≤ C.1)
    (hflat : IsFlat B S hS (C.1.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)) :
    strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom) = C.1 := by
  refine le_antisymm (sInf_le ⟨C.2, fun U _ => ?_⟩) ?_
  · exact definingIdealAt_le_supportedSections_of_openComplement_le B S hS
      (exceptionalPreimageClosedSubspace B S hS f b Z) C hC U
  · exact le_of_isFlat_of_openComplement_le B S hS (strictTransformPullbackToBlowUp B S hS f b)
      (preimageClosedSubspace b Z) hb.isPullbackDefined C (strictTransform B S hS f b _)
      (exceptionalPreimageComplement_le_strictTransformSubfunctor B S hS f b Z hb) hflat

end StrictTransform

end AlgebraicGeometry.Space

end
