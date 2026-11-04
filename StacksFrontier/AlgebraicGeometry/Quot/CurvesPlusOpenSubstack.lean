module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesIsolatedSingularities
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLocusSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusOpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtYoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# The open substack of curves with finite singular locus (Stacks 0DZW)

Stacks 0DZW: there is an open substack `Curves⁺ ⊂ Curves` such that

1. given a family of curves `X → S` the following are equivalent:
   (a) the classifying morphism `S → Curves` factors through `Curves⁺`,
   (b) the singular locus of `X → S` endowed with any/some closed subspace structure is finite
   over `S`;
2. given `X` a proper scheme over a field `k` of dimension `≤ 1` the following are equivalent:
   (a) the classifying morphism `Spec(k) → Curves` factors through `Curves⁺`,
   (b) `X → Spec(k)` is smooth except at finitely many points.

`Curves` is the library's stack of curves of Stacks 0D4Z,
`AlgebraicGeometry.curvesFiberedCategory`, and `Curves⁺` is the strictly full subcategory cut out
by `AlgebraicGeometry.IsFiniteNonSmoothLocus`. It is an open substack in the sense that its
inclusion is representable by algebraic spaces and an open immersion (Stacks 04YL, part (1), via
02ZW and 04XB): this is `AlgebraicGeometry.curvesPlus_isOpenSubstack`, proved from condition (o)
of Section 0E0E, which is the content of the source's proof — the singular locus `T ⊂ |X|` is
closed, the set of points of the base over which it is finite is open (Stacks 0A4Y, 0ABM, 0ACZ,
0A4X), and its formation commutes with arbitrary base change.

The classifying morphism of a family of curves `X → S` is a 1-morphism
`(Sch/S)_{fppf} → Curves` over the site whose value at `id_S` is `X`; by the 2-Yoneda lemma
(Stacks 004B) one exists, `AlgebraicGeometry.exists_classifyingMorphism`, and it is unique up to
2-isomorphism. Part (1) is `AlgebraicGeometry.curvesPlus_classifying_factors_iff`, proved for
every such classifying morphism; part (2) is
`AlgebraicGeometry.curvesPlus_classifying_factors_iff_of_field`, for the family of curves
`AlgebraicGeometry.curveFamilyOfProperOverField` attached to a proper scheme of dimension `≤ 1`
over a field, smoothness being smoothness of the morphism of schemes at a point. The three are
bundled in `AlgebraicGeometry.exists_curvesPlus`.

## Implementation notes

An `AlgebraicGeometry.Stack.OpenSubstack` presupposes an algebraic ambient stack, and the
algebraicity of `Curves` is Stacks 0D5A. What is proved here, without it, is the property of the
inclusion that makes `Curves⁺` an open substack. Granted 0D5A, `Curves⁺` is packaged as an
`AlgebraicGeometry.Stack.OpenSubstack` of the algebraic stack of curves, algebraic by Stacks 05UM,
with parts (1) and (2), in `AlgebraicGeometry.exists_openSubstack_curvesPlus`
(`StacksFrontier/AlgebraicGeometry/Quot/CurvesPlusAlgebraicOpenSubstack.lean`).

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Section 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The two formulations of the defining condition of `Curves⁺` in the library agree on the
nose. -/
theorem hasFiniteNonSmoothLocus_eq_isFiniteNonSmoothLocus :
    hasFiniteNonSmoothLocus B hZ = IsFiniteNonSmoothLocus B hZ :=
  rfl

/-! ### `Curves⁺` as a category fibred in groupoids, and its inclusion -/

/-- `Curves⁺`, the strictly full subcategory of the stack of curves cut out by finiteness of the
singular locus, as a category fibred in groupoids over the big fppf site. -/
abbrev curvesPlusFiberedCategory :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubFiberedCategory B hZ (IsFiniteNonSmoothLocus B hZ)
    (prop_of_hom_of_exists_isOpenSubspace B hZ _
      (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ))

/-- The inclusion `Curves⁺ ⟶ Curves`. -/
abbrev curvesPlusInclusion : curvesPlusFiberedCategory B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesSubInclusion B hZ (IsFiniteNonSmoothLocus B hZ)
    (prop_of_hom_of_exists_isOpenSubspace B hZ _
      (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ))

/-- **Stacks 0DZW, the open substack.** `Curves⁺` is an open substack of the stack of curves: it
is a strictly full subcategory, and its inclusion into `Curves` is representable by algebraic
spaces and an open immersion. -/
@[stacks 0DZW "Curves⁺ is an open substack of Curves: a strictly full subcategory whose inclusion \
is representable by algebraic spaces and an open immersion"]
theorem curvesPlus_isOpenSubstack :
    (show ObjectProperty (CurveFamily B hZ) from
        IsFiniteNonSmoothLocus B hZ).IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ (curvesPlusInclusion B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesPlusInclusion B hZ) :=
  ⟨⟨fun e h => CurveFamily.isFiniteNonSmoothLocus_of_hom B hZ e.inv h⟩,
    isRepresentableByAlgebraicSpaces_curvesSubInclusion B hZ _
      (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ),
    isOpenImmersion_curvesSubInclusion B hZ _
      (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ)⟩

/-! ### Classifying morphisms -/

/-- A classifying morphism of a family of curves `X → S`: a 1-morphism `(Sch/S)_{fppf} → Curves`
over the site whose value at `id_S` is (isomorphic to) `X`. -/
abbrev IsClassifyingMorphism (X : CurveFamily B hZ)
    (y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val) :
    Prop :=
  Nonempty (y.obj (Over.mk (𝟙 X.base.left)) ≅ X)

/-- Every family of curves has a classifying morphism: the 2-Yoneda lemma (Stacks 004B) applied
to the stack of curves, read on the big fppf site of the base through the iterated slice. -/
theorem exists_classifyingMorphism (X : CurveFamily B hZ) :
    ∃ y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val,
      IsClassifyingMorphism B hZ X y := by
  have hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids :=
    (curvesFiberedCategory B hZ).property
  let x : (curvesProjectionOver B hZ).Fiber X.base := Functor.Fiber.mk (a := X) rfl
  let L := Functor.TwoYoneda.liftFunctor (curvesProjectionOver B hZ) hp X.base x
  refine ⟨⟨Over.iteratedSliceBackward X.base ⋙ L, ?_⟩, ⟨?_⟩⟩
  · show Over.iteratedSliceBackward X.base ⋙ L ⋙ curvesProjectionOver B hZ = _
    rw [Functor.TwoYoneda.liftFunctor_w]
    rfl
  · let a := (Over.iteratedSliceBackward X.base).obj (Over.mk (𝟙 X.base.left))
    let c := Functor.TwoYoneda.chosenLift (curvesProjectionOver B hZ) hp X.base x a
    have : (curvesProjectionOver B hZ).IsStronglyCartesian a.hom c.φ := c.isStronglyCartesian
    have : IsIso a.hom := by
      have : IsIso ((Over.forget _).map a.hom) := by
        show IsIso (𝟙 _)
        infer_instance
      exact isIso_of_reflects_iso a.hom (Over.forget _)
    have hiso : IsIso c.φ :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso (p := curvesProjectionOver B hZ)
        (f := a.hom) c.φ
    exact @asIso _ _ _ _ c.φ hiso

/-- The classifying morphism of a family of curves factors through `Curves⁺` exactly when the
family lies in `Curves⁺`. -/
theorem curvesPlus_factors_iff (X : CurveFamily B hZ)
    (y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val)
    (hy : IsClassifyingMorphism B hZ X y) :
    (∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
          (curvesPlusFiberedCategory B hZ).val,
        Nonempty (g.comp (curvesPlusInclusion B hZ).hom ≅ y)) ↔
      IsFiniteNonSmoothLocus B hZ X := by
  obtain ⟨e⟩ := hy
  rw [exists_factorization_curvesSubInclusion_iff B hZ _
    (prop_of_hom_of_exists_isOpenSubspace B hZ _
      (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ))]
  exact ⟨fun h => CurveFamily.isFiniteNonSmoothLocus_of_hom B hZ e.inv h,
    fun h => CurveFamily.isFiniteNonSmoothLocus_of_hom B hZ e.hom h⟩

/-! ### Part (1) -/

/-- **Stacks 0DZW, part (1).** For a family of curves `X → S` and its classifying morphism
`S → Curves`, the classifying morphism factors through `Curves⁺` exactly when *some* closed
subspace structure on the singular locus of `X → S` is finite over `S`, and exactly when *every*
closed subspace structure on it is. -/
@[stacks 0DZW "part (1): for every family of curves X → S, the classifying morphism factors \
through Curves⁺ iff the singular locus with some, equivalently any, closed subspace structure is \
finite over S"]
theorem curvesPlus_classifying_factors_iff (X : CurveFamily B hZ)
    (y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val)
    (hy : IsClassifyingMorphism B hZ X y) :
    ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
          (curvesPlusFiberedCategory B hZ).val,
        Nonempty (g.comp (curvesPlusInclusion B hZ).hom ≅ y)) ↔
      ∃ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z ∧
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          CurveFamily.nonSmoothLocus B hZ X ∧
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) ∧
    ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
          (curvesPlusFiberedCategory B hZ).val,
        Nonempty (g.comp (curvesPlusInclusion B hZ).hom ≅ y)) ↔
      ∀ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z →
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          CurveFamily.nonSmoothLocus B hZ X →
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) :=
  ⟨(curvesPlus_factors_iff B hZ X y hy).trans
      (CurveFamily.isFiniteNonSmoothLocus_iff_exists_isClosedSubspace B hZ X),
    (curvesPlus_factors_iff B hZ X y hy).trans
      (CurveFamily.isFiniteNonSmoothLocus_iff_forall_isClosedSubspace B hZ X)⟩

/-! ### Part (2) -/

section Field

variable (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (e : (BigFppfOver.toScheme B integerBase hZ).obj W ≅ Spec (.of k))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))

include e hproper in
/-- A proper morphism to the spectrum of a field is locally of finite presentation: it is of
finite type, and the target is Noetherian. -/
theorem locallyOfFinitePresentation_of_isProper_of_field :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  have : LocallyOfFinitePresentation
      (((BigFppfOver.toScheme B integerBase hZ).map g ≫ e.hom) ≫ e.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

include e in
/-- Every morphism to the spectrum of a field is flat. -/
theorem flat_of_field : Flat ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  have : Flat (((BigFppfOver.toScheme B integerBase hZ).map g ≫ e.hom) ≫ e.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

/-- The family of curves attached to a proper scheme `X = T` of dimension at most one over a field
`k`, the base `W` of the site being identified with `Spec(k)` by `e`. Flatness and finite
presentation are automatic over a field, and the space-level quasi-compactness and
(quasi-)separatedness are those of the morphism of schemes (Stacks 03KY and 03KG). -/
def curveFamilyOfProperOverField
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    CurveFamily B hZ :=
  curveFamilyOfSchemeMorphism B hZ g (flat_of_field B hZ k g e) hproper
    (locallyOfFinitePresentation_of_isProper_of_field B hZ k g e hproper)
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance) hdim

/-- The family of curves attached to a proper scheme `X` of dimension at most one over a field
lies in `Curves⁺` exactly when `X → Spec(k)` is smooth except at finitely many points. -/
theorem isFiniteNonSmoothLocus_curveFamilyOfProperOverField_iff
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsFiniteNonSmoothLocus B hZ (curveFamilyOfProperOverField B hZ k g e hproper hdim) ↔
      {x : (BigFppfOver.toScheme B integerBase hZ).obj T |
        ¬ InfinitesimalLifting.SmoothAt
          ((BigFppfOver.toScheme B integerBase hZ).map g) x}.Finite := by
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    locallyOfFinitePresentation_of_isProper_of_field B hZ k g e hproper
  let X := curveFamilyOfProperOverField B hZ k g e hproper hdim
  show IsFiniteNonSmoothLocus B hZ X ↔ _
  have hsub : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
    ⟨fun _ _ => (Scheme.Hom.homeomorph e.hom).injective (Subsingleton.elim _ _)⟩
  rw [CurveFamily.isFiniteNonSmoothLocus_iff_forall_finite_nonSmoothLocus_fibre]
  have hns : CurveFamily.nonSmoothLocus B hZ X =
      Space.pointsToScheme B integerBase hZ T ⁻¹'
        {x : (BigFppfOver.toScheme B integerBase hZ).obj T |
          ¬ InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B integerBase hZ).map g) x} := by
    ext x
    refine not_congr ((Space.isSmoothAt_yoneda_map_iff B integerBase hZ g x).trans ?_)
    show _ ↔ Stacks.SmoothAtJacobian.Condition1 _ _
    exact (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus _ _).symm
  have hpts : Subsingleton (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
    (Space.pointsEquivScheme B integerBase hZ X.base).subsingleton
  have hfib : ∀ y₀ : Space.points B integerBase hZ (schemeSpace X.base).obj,
      {x : Space.points B integerBase hZ X.total.1 |
        x ∈ CurveFamily.nonSmoothLocus B hZ X ∧
          Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x = y₀} =
        CurveFamily.nonSmoothLocus B hZ X := fun y₀ => by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  simp only [hfib]
  let eT := Space.pointsEquivScheme B integerBase hZ T
  refine ⟨fun h => ?_, fun h y₀ => ?_⟩
  · rcases isEmpty_or_nonempty (Space.points B integerBase hZ (schemeSpace X.base).obj)
      with hE | ⟨⟨y₀⟩⟩
    · have : IsEmpty ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
        ⟨fun t => hE.false (Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom (eT.symm t))⟩
      exact Set.toFinite _
    · have hfin := h y₀
      rw [hns] at hfin
      exact hfin.of_preimage eT.surjective
  · rw [hns]
    exact h.preimage eT.injective.injOn


/-- **Stacks 0DZW, part (2).** Let `X` be a proper scheme of dimension at most one over a field
`k`. The classifying morphism `Spec(k) → Curves` of the attached family of curves factors through
`Curves⁺` exactly when `X → Spec(k)` is smooth except at finitely many points. -/
@[stacks 0DZW "part (2): for a proper scheme X of dimension at most one over a field k, the \
classifying morphism Spec(k) → Curves factors through Curves⁺ iff X → Spec(k) is smooth except at \
finitely many points"]
theorem curvesPlus_classifying_factors_iff_of_field
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (y : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val)
    (hy : IsClassifyingMorphism B hZ (curveFamilyOfProperOverField B hZ k g e hproper hdim) y) :
    (∃ g' : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ (curvesPlusFiberedCategory B hZ).val,
        Nonempty (g'.comp (curvesPlusInclusion B hZ).hom ≅ y)) ↔
      {x : (BigFppfOver.toScheme B integerBase hZ).obj T |
        ¬ InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B integerBase hZ).map g) x}.Finite :=
  by
  let X := curveFamilyOfProperOverField B hZ k g e hproper hdim
  exact (curvesPlus_factors_iff B hZ X y hy).trans
    (isFiniteNonSmoothLocus_curveFamilyOfProperOverField_iff B hZ k g e hproper hdim)

end Field

/-! ### The statement of record -/

/-- **Stacks 0DZW.** There is an open substack `Curves⁺` of the stack of curves — a strictly full
subcategory whose inclusion is representable by algebraic spaces and an open immersion — such that

1. for every family of curves `X → S` and its classifying morphism, the classifying morphism
   factors through `Curves⁺` iff the singular locus of `X → S` with some closed subspace
   structure is finite over `S`, iff it is finite over `S` with every closed subspace structure;
2. for every proper scheme `X` of dimension at most one over a field `k`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves⁺` iff `X → Spec(k)` is smooth except at finitely
   many points. -/
@[stacks 0DZW "the open substack Curves⁺ ⊂ Curves together with parts (1) and (2)"]
theorem exists_curvesPlus :
    ∃ (P : ObjectProperty (CurveFamily B hZ))
        (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F),
      P.IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ (curvesSubInclusion B hZ P hP).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesSubInclusion B hZ P hP) ∧
      (∀ (X : CurveFamily B hZ)
        (y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val),
        IsClassifyingMorphism B hZ X y →
          ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
                (curvesSubFiberedCategory B hZ P hP).val,
              Nonempty (g.comp (curvesSubInclusion B hZ P hP).hom ≅ y)) ↔
            ∃ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z ∧
              Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
                CurveFamily.nonSmoothLocus B hZ X ∧
              Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) ∧
          ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
                (curvesSubFiberedCategory B hZ P hP).val,
              Nonempty (g.comp (curvesSubInclusion B hZ P hP).hom ≅ y)) ↔
            ∀ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z →
              Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
                CurveFamily.nonSmoothLocus B hZ X →
              Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom))) ∧
      (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
        (e : (BigFppfOver.toScheme B integerBase hZ).obj W ≅ Spec (.of k))
        (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
        (y : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val),
        IsClassifyingMorphism B hZ (curveFamilyOfProperOverField B hZ k g e hproper hdim) y →
          ((∃ g' : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
                (curvesSubFiberedCategory B hZ P hP).val,
              Nonempty (g'.comp (curvesSubInclusion B hZ P hP).hom ≅ y)) ↔
            {x : (BigFppfOver.toScheme B integerBase hZ).obj T |
              ¬ InfinitesimalLifting.SmoothAt
                ((BigFppfOver.toScheme B integerBase hZ).map g) x}.Finite)) :=
  ⟨IsFiniteNonSmoothLocus B hZ, fun a h => CurveFamily.isFiniteNonSmoothLocus_of_hom B hZ a h,
    (curvesPlus_isOpenSubstack B hZ).1, (curvesPlus_isOpenSubstack B hZ).2.1,
    (curvesPlus_isOpenSubstack B hZ).2.2,
    curvesPlus_classifying_factors_iff B hZ,
    fun k _ _ _ g e hproper hdim y hy =>
      curvesPlus_classifying_factors_iff_of_field B hZ k g e hproper hdim y hy⟩

end AlgebraicGeometry

end
