module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# `Rf_*` commutes with direct sums of uniformly bounded families

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. The derived direct
image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` commutes with direct sums indexed by an arbitrary type of the
scheme universe, provided the family is *uniformly bounded*: there are integers `a ≤ b` with
every member of the family living in degrees `[a, b]`.

This is the dévissage half of [Stacks, Tag 08DZ]. The source reduces that tag, through the
spectral sequences of [Stacks, Tag 015J], to a direct sum of quasi-coherent sheaves and then to
[Stacks, Tag 07TB]; the reduction carried out here replaces the spectral sequences by the
truncation triangles of the canonical t-structure, which is possible because the direct-sum
comparison morphism satisfies two out of three along a distinguished triangle. What is left of
Tag 08DZ after this file is the passage from a uniformly bounded family to an arbitrary one,
which needs the uniform cohomological bound of [Stacks, Tag 08D5] part (2); that passage, and
the tag itself, are in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean`.

## Main results

* `Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_singleFunctor_obj`: the comparison
  morphism is invertible at a family of modules placed in a single degree. This is the base case,
  and it is where [Stacks, Tag 07TB] enters, through
  `Stacks.AlgebraicGeometry.HigherDirectImage.preservesColimitsOfShape_discrete_rightDerived`.
* `Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE`: **the comparison
  morphism is invertible at a uniformly bounded family.**
* `Stacks.Duality.DerivedPushforward.preservesColimit_discrete_of_isGE_isLE`: the same, read as
  preservation of the direct sum of the family.

## Implementation notes

**Why no quasi-coherence appears.** The base case identifies `H^m(Rf_*(ℱ[a]))` with
`R^{m-a} f_* ℱ` for an *arbitrary* `𝒪_X`-module `ℱ`, and the higher direct images of a
quasi-compact quasi-separated morphism commute with direct sums of arbitrary modules. So the
whole dévissage runs over `D(𝒪_X)` and not over `D_QCoh(𝒪_X)`; quasi-coherence is needed only
for the bound of Tag 08D5, i.e. only in the step this file does not take.

**The base case.** `Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived`
supplies the identification `H^m(Rf_*(ℱ[a])) ≅ R^{m-a} f_* ℱ` as an isomorphism of *functors*
of `ℱ`, which is what preservation of direct sums can be transported along; the objectwise
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, built from a chosen injective
resolution, would not suffice. In degrees `m < a` the identification is unavailable and
unnecessary: `ℱ[a]` lies in degrees `≥ a`, `Rf_*` moves cohomology to the right
(`Stacks.DerivedFunctor.isGE_totalRightDerived_obj`), and a direct sum of objects lying in
degrees `≥ a` again does (`Stacks.Duality.isGE_sigmaObj`), so both the source and the target of
the comparison morphism are zero and any morphism between them is invertible.

**The dévissage.** The induction is on the length `b - a` of the degree window, with the
truncation triangle `τ_{≤a}E ⟶ E ⟶ τ_{>a}E` of
`CategoryTheory.Triangulated.TStructure.triangleLEGT`: its first vertex lies in degrees `[a, a]`,
which is the base case, and its third lies in degrees `[a + 1, b]`, which is the inductive
hypothesis. Both of the "crossed" bounds this needs are Mathlib instances. The conclusion is
`CategoryTheory.Pretriangulated.isIso_sigmaComparison_of_distTriang`, which takes the three
families of vertices and the three families of morphisms separately — exactly the shape the
truncation triangle produces, since `truncLEι`, `truncGTπ` and `truncGTδLE` are natural
transformations.

**The model.** Nothing here fixes a model of the derived categories: the statements carry
`HasDerivedCategory` as a hypothesis at a free morphism universe. The index types are those of
the scheme universe, which is the universe in which `𝒪_X`-modules form a Grothendieck abelian
category and therefore the one in which the direct sums exist.

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 07TB](https://stacks.math.columbia.edu/tag/07TB)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace Stacks.Duality.DerivedPushforward

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-! ### Two auxiliary facts -/

/-- A morphism between two zero objects is an isomorphism. -/
theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
    {A B : C} (hA : IsZero A) (hB : IsZero B) (g : A ⟶ B) : IsIso g := by
  have h : g = (hA.iso hB).hom := hA.eq_of_src _ _
  rw [h]
  infer_instance

/-- **Placing a module in a fixed degree of the derived category preserves direct sums.** The
single functor is the single functor on cochain complexes, which preserves all colimits,
followed by the localization, which preserves direct sums indexed by the Grothendieck
universe. -/
theorem preservesColimitsOfShape_discrete_singleFunctor (a : ℤ) (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (DerivedCategory.singleFunctor X.Modules a) := by
  have h₁ : PreservesColimitsOfShape (Discrete α)
      (CochainComplex.singleFunctor X.Modules a) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete α)
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) a))
  have h₂ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := X.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts X.Modules α
  have h₃ : PreservesColimitsOfShape (Discrete α)
      (CochainComplex.singleFunctor X.Modules a ⋙ DerivedCategory.Q) :=
    comp_preservesColimitsOfShape _ _
  exact (preservesColimitsOfShape_iff_of_natIso
    (DerivedCategory.singleFunctorIsoCompQ X.Modules a)).2 h₃

/-! ### The identification of `H^m(Rf_*(ℱ[a]))` with `R^{m-a} f_* ℱ` -/

/-- **`H^m(Rf_*(ℱ[a])) ≅ R^{m-a} f_* ℱ`, naturally in the module `ℱ`.** This is
`Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived` for the derived direct
image, whose shift-commutation datum is the canonical one carried by
`Stacks.Duality.DerivedPushforward.commShift_derivedPushforward` and whose K-injective
resolutions come from the Grothendieck abelian category of `𝒪_X`-modules. -/
def singleCompDerivedPushforwardHomologyIso (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    DerivedCategory.singleFunctor X.Modules a ⋙ Stacks.Duality.derivedPushforward f ⋙
        DerivedCategory.homologyFunctor Y.Modules m ≅
      (Scheme.Modules.pushforward f).rightDerived n :=
  Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived
    (Scheme.Modules.pushforward f) (Stacks.Duality.derivedPushforward f)
    ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    Stacks.Cohomology.Localization.enoughKInjectives a m n hn

variable [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]

/-! ### The base case: a family placed in a single degree -/

/-- The direct-sum comparison morphism of `Rf_*` followed by a cohomology functor is invertible
at a family of modules placed in a single degree `a`.

Above degree `a` this is the direct-sum statement for `R^{m-a} f_*` transported along
`Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso`; below degree `a`
both sides are zero. -/
theorem isIso_sigmaComparison_comp_homology_singleFunctor
    (a m : ℤ) {α : Type u} (M : α → X.Modules) :
    IsIso (sigmaComparison
      (Stacks.Duality.derivedPushforward f ⋙ DerivedCategory.homologyFunctor Y.Modules m)
      (fun j ↦ (DerivedCategory.singleFunctor X.Modules a).obj (M j))) := by
  rcases le_or_gt a m with hle | hlt
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, m - a = (n : ℤ) := ⟨(m - a).toNat, by omega⟩
    have hRn : PreservesColimitsOfShape (Discrete α)
        ((Scheme.Modules.pushforward f).rightDerived n) :=
      Stacks.AlgebraicGeometry.HigherDirectImage.preservesColimitsOfShape_discrete_rightDerived
        f n α
    have hcomp : PreservesColimitsOfShape (Discrete α)
        (DerivedCategory.singleFunctor X.Modules a ⋙ Stacks.Duality.derivedPushforward f ⋙
          DerivedCategory.homologyFunctor Y.Modules m) :=
      (preservesColimitsOfShape_iff_of_natIso
        (singleCompDerivedPushforwardHomologyIso f a m n hn)).2 hRn
    have h₂ : IsIso (sigmaComparison (DerivedCategory.singleFunctor X.Modules a) M) :=
      isIso_sigmaComparison_of_preservesColimit _ M
        (preservesColimitsOfShape_discrete_singleFunctor a α).preservesColimit
    have h₁ : IsIso (sigmaComparison (DerivedCategory.singleFunctor X.Modules a ⋙
        (Stacks.Duality.derivedPushforward f ⋙
          DerivedCategory.homologyFunctor Y.Modules m)) M) :=
      isIso_sigmaComparison_of_preservesColimit _ M hcomp.preservesColimit
    rw [sigmaComparison_comp] at h₁
    have h₃ := h₂
    exact IsIso.of_isIso_comp_right _
      ((Stacks.Duality.derivedPushforward f ⋙
        DerivedCategory.homologyFunctor Y.Modules m).map
          (sigmaComparison (DerivedCategory.singleFunctor X.Modules a) M))
  · have hzero : ∀ (E : DerivedCategory X.Modules), E.IsGE a →
        IsZero ((Stacks.Duality.derivedPushforward f ⋙
          DerivedCategory.homologyFunctor Y.Modules m).obj E) := fun E _ ↦ by
      have hge : ((Stacks.Duality.derivedPushforward f).obj E).IsGE a :=
        Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) _ a
      exact DerivedCategory.isZero_of_isGE _ a m (by omega)
    refine isIso_of_isZero_of_isZero ?_ (hzero _ ?_) _
    · exact Stacks.Duality.isZero_sigmaObj _ fun j ↦ hzero _ inferInstance
    · exact Stacks.Duality.isGE_sigmaObj X.Modules _ a fun _ ↦ inferInstance

/-- **The direct-sum comparison morphism of `Rf_*` is invertible at a family of modules placed
in a single degree.** A morphism of the derived category is invertible as soon as it is on every
cohomology sheaf, and in each degree this is
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_comp_homology_singleFunctor`. -/
theorem isIso_sigmaComparison_singleFunctor_obj (a : ℤ) {α : Type u} (M : α → X.Modules) :
    IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
      (fun j ↦ (DerivedCategory.singleFunctor X.Modules a).obj (M j))) := by
  rw [DerivedCategory.isIso_iff]
  intro m
  refine isIso_map_sigmaComparison_of_isIso_comp _ _ _
    (isIso_sigmaComparison_comp_homology_singleFunctor f a m M) ?_
  exact isIso_sigmaComparison_of_preservesColimit _ _
    (Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor Y.Modules m).preservesColimit

/-- The direct-sum comparison morphism of `Rf_*` is invertible at a family concentrated in a
single degree `a`: every such object is isomorphic to a module placed in degree `a`, and
preservation of the direct sum of a family only depends on the family up to isomorphism. -/
theorem isIso_sigmaComparison_of_isGE_isLE_self (a : ℤ) {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hge : ∀ j, (E j).IsGE a) (hle : ∀ j, (E j).IsLE a) :
    IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f) E) := by
  have hex : ∀ j, ∃ N : X.Modules,
      Nonempty (E j ≅ (DerivedCategory.singleFunctor X.Modules a).obj N) := by
    intro j
    have := hge j
    have := hle j
    exact DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (E j) a
  choose N hN using hex
  have hpres : PreservesColimit
      (Discrete.functor fun j ↦ (DerivedCategory.singleFunctor X.Modules a).obj (N j))
      (Stacks.Duality.derivedPushforward f) :=
    preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ _
      (isIso_sigmaComparison_singleFunctor_obj f a N)
  have hdiag : (Discrete.functor fun j ↦ (DerivedCategory.singleFunctor X.Modules a).obj (N j))
      ≅ Discrete.functor E :=
    Discrete.natIso fun i ↦ ((hN i.as).some).symm
  exact isIso_sigmaComparison_of_preservesColimit _ E
    (preservesColimit_of_iso_diagram (Stacks.Duality.derivedPushforward f) hdiag)

/-! ### The dévissage -/

/-- **`Rf_*` commutes with the direct sum of a uniformly bounded family**, in the form the
induction is run in: the length of the degree window is bounded by `k`.

The induction step cuts each member of the family by the truncation triangle
`τ_{≤a}E ⟶ E ⟶ τ_{>a}E`, whose outer vertices are concentrated in degree `a` and lie in the
window `[a + 1, b]`; the comparison morphism satisfies two out of three along a distinguished
triangle. -/
theorem isIso_sigmaComparison_of_isGE_isLE_aux {α : Type u} :
    ∀ (k : ℕ) (a b : ℤ), b - a ≤ (k : ℤ) →
      ∀ E : α → DerivedCategory X.Modules, (∀ j, (E j).IsGE a) → (∀ j, (E j).IsLE b) →
      IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f) E) := by
  intro k
  induction k with
  | zero =>
      intro a b hba E hge hle
      refine isIso_sigmaComparison_of_isGE_isLE_self f a E hge fun j ↦ ?_
      have := hle j
      exact DerivedCategory.TStructure.t.isLE_of_le (E j) b a (by omega)
  | succ k ih =>
      intro a b hba E hge hle
      have h₁ : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
          fun j ↦ (DerivedCategory.TStructure.t.truncLE a).obj (E j)) := by
        refine isIso_sigmaComparison_of_isGE_isLE_self f a _ (fun j ↦ ?_) (fun _ ↦ ?_)
        · have := hge j
          infer_instance
        · infer_instance
      have h₃ : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
          fun j ↦ (DerivedCategory.TStructure.t.truncGT a).obj (E j)) := by
        refine ih (a + 1) b (by omega) _ (fun _ ↦ ?_) (fun j ↦ ?_)
        · infer_instance
        · have := hle j
          infer_instance
      exact isIso_sigmaComparison_of_distTriang (Stacks.Duality.derivedPushforward f)
        (fun j ↦ (DerivedCategory.TStructure.t.truncLEι a).app (E j))
        (fun j ↦ (DerivedCategory.TStructure.t.truncGTπ a).app (E j))
        (fun j ↦ (DerivedCategory.TStructure.t.truncGTδLE a).app (E j))
        (fun j ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished a (E j))
        h₁ h₃

/-- **`Rf_*` commutes with the direct sum of a uniformly bounded family.** Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of schemes and let `E` be a family of objects of
`D(𝒪_X)`, indexed by a type of the scheme universe, all lying in degrees `≥ a` and `≤ b`. Then
the canonical morphism `⨁ⱼ Rf_*(Eⱼ) ⟶ Rf_*(⨁ⱼ Eⱼ)` is an isomorphism. -/
theorem isIso_sigmaComparison_of_isGE_isLE {α : Type u} (a b : ℤ)
    (E : α → DerivedCategory X.Modules) (hge : ∀ j, (E j).IsGE a) (hle : ∀ j, (E j).IsLE b) :
    IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f) E) :=
  isIso_sigmaComparison_of_isGE_isLE_aux f (b - a).toNat a b (by omega) E hge hle

/-- **`Rf_*` preserves the direct sum of a uniformly bounded family**, the statement of
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE` read as preservation of a
colimit. -/
theorem preservesColimit_discrete_of_isGE_isLE {α : Type u} (a b : ℤ)
    (E : α → DerivedCategory X.Modules) (hge : ∀ j, (E j).IsGE a) (hle : ∀ j, (E j).IsLE b) :
    PreservesColimit (Discrete.functor E) (Stacks.Duality.derivedPushforward f) :=
  preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ E
    (isIso_sigmaComparison_of_isGE_isLE f a b E hge hle)

end Stacks.Duality.DerivedPushforward

end
