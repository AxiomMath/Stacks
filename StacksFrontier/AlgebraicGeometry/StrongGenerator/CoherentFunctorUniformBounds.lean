module

public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentFunctorBounds
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentUniformGeneratorUnconditional
public import StacksFrontier.CategoryTheory.Triangulated.ExactFunctorBoundedOperations
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniform bounds for a homological or cohomological functor on the coherent modules, from a
uniform generator

Let `k` be a field, let `X` be a scheme proper and smooth over `k`, let `𝒜` be an abelian
category and let `H : D_perf(𝒪_X) ⥤ 𝒜` be a homological functor whose cohomology
`H^i(K) = H(K[i])` is nonzero for only finitely many `i`, for every perfect `K`. Then there is an
`m ≥ 1` with `H^i(ℱ) = 0` for every coherent `𝒪_X`-module `ℱ` and every `i ∉ [-m, m]`; and the
same for a cohomological functor. This is [Stacks, Tag 0FZ8].

The proof in the source is "combine [Stacks, Tag 0FZ7] with [Stacks, Tag 0FX8]". This module
runs that combination against the *conclusion* of [Stacks, Tag 0FZ7] — a finite locally free
`𝒢` and integers `m₀, n ≥ 1` with every coherent `ℱ` in `smd(add(𝒢[-m₀, m₀])^{⋆ n})` — taken as
a statement about `X` and nothing else — and then feeds it the proved
`AlgebraicGeometry.exists_uniform_generator_isCoherent`. Nothing is assumed beyond the source's
hypotheses.

## Main results

* `AlgebraicGeometry.exists_uniform_bound_isZero_of_isHomological_of_isProper` and
  `AlgebraicGeometry.exists_uniform_bound_isZero_of_isCohomological_of_isProper`:
  **[Stacks, Tag 0FZ8]**, the homological and the cohomological case, for `X` proper and smooth
  over `k` and nothing else.
* `Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_singleFunctor_of_model` and
  `AlgebraicGeometry.uniformGenerator_of_standardModel`: the membership
  `ℱ[0] ∈ smd(add(𝒢[0][c, d])^{⋆ n})` does not depend on the chosen model of `D(𝒪_X)`, so the
  statement of [Stacks, Tag 0FZ7] at `CategoryTheory.HasDerivedCategory.standard` gives it at
  the locally small model on which `D_perf(𝒪_X)` is built here.
* `AlgebraicGeometry.exists_uniform_bound_isZero_of_isHomological_of_uniformGenerator` and
  `AlgebraicGeometry.exists_uniform_bound_isZero_of_isCohomological_of_uniformGenerator`: from a
  uniform generator of the coherent modules in the sense of [Stacks, Tag 0FZ7], the uniform
  window of a homological, resp. cohomological, functor on `D_perf(𝒪_X)`.

## Implementation notes

The window argument is the one of
`StacksFrontier/AlgebraicGeometry/StrongGenerator/CoherentFunctorBounds.lean`: the membership in
`D(𝒪_X)` is read in `D_perf(𝒪_X)` by
`Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_of_map_ι`, the
window of `H` on the single generator `𝒢` comes from the finiteness of its cohomology, and
[Stacks, Tag 0FX8] (resp. its contravariant form
`Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter`)
widens it to the tower by `[-m₀, m₀]`.

## References

* [Stacks Project, Tag 0FZ8](https://stacks.math.columbia.edu/tag/0FZ8)
* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FX8](https://stacks.math.columbia.edu/tag/0FX8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

universe u

namespace Stacks.TriangulatedGenerators

/-- **A bounded-shift membership between single objects does not depend on the model of the
derived category.** If `B[0]` lies in `smd(add(A[0][c, d])^{⋆ n})` in one chosen derived
category of `C`, then it does in any other. The comparison equivalence of the two models is
exact and carries `A[0]` and `B[0]` to `A[0]` and `B[0]`
(`StacksDraft.DerivedModel.modelSingleFunctorIso`), so this is [Stacks, Tag 0FX5] along it. -/
theorem retractClosure_extensionProductIter_singleFunctor_of_model {C : Type*} [Category C]
    [Abelian C] (h₁ : HasDerivedCategory C) (h₂ : HasDerivedCategory C) (A B : C) (c d : ℤ)
    (n : ℕ)
    (hB : letI := h₁; ((⨆ i ∈ Set.Icc c d, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor C 0).obj A)).isoClosure.shift
          i).binaryProductsClosure.extensionProductIter n).retractClosure
        ((DerivedCategory.singleFunctor C 0).obj B)) :
    letI := h₂; ((⨆ i ∈ Set.Icc c d, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor C 0).obj A)).isoClosure.shift
          i).binaryProductsClosure.extensionProductIter n).retractClosure
        ((DerivedCategory.singleFunctor C 0).obj B) := by
  let i1 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₁) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt C _ _ h₁ n
  let i2 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₂) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt C _ _ h₂ n
  let Φ := (StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor
  let : Φ.CommShift ℤ := StacksDraft.Perfect.derivedEquivalenceCommShift h₁ h₂
  have : Φ.IsTriangulated := StacksDraft.Perfect.derivedEquivalence_isTriangulated h₁ h₂
  let e := StacksDraft.DerivedModel.modelSingleFunctorIso h₁ h₂ 0
  have hmem := retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le Φ
    (P := ObjectProperty.singleton (@DerivedCategory.singleFunctor C _ _ h₁ 0 |>.obj A))
    (Q := (ObjectProperty.singleton (@DerivedCategory.singleFunctor C _ _ h₂ 0 |>.obj A)
      ).isoClosure)
    (fun X hX => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hX
      exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨e.app A⟩⟩) c d n _ hB
  simp only [isoClosure_eq_self] at hmem
  exact ObjectProperty.prop_of_iso _ (e.app B) hmem

end Stacks.TriangulatedGenerators

namespace AlgebraicGeometry

open Stacks.Cohomology.PerfectComplexes Stacks.TriangulatedGenerators

/-- **The uniform generator of [Stacks, Tag 0FZ7], transported from the standard model of `D(𝒪_X)`
to the locally small one.** The statement of [Stacks, Tag 0FZ7] read at
`CategoryTheory.HasDerivedCategory.standard` implies the same statement at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, by
`Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_singleFunctor_of_model`. -/
theorem uniformGenerator_of_standardModel {X : Scheme.{u}}
    (hgen : letI := HasDerivedCategory.standard X.Modules;
      ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :
    ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  obtain ⟨m, n, 𝒢, hm, hn, h𝒢, hall⟩ := hgen
  exact ⟨m, n, 𝒢, hm, hn, h𝒢, fun F hF =>
    retractClosure_extensionProductIter_singleFunctor_of_model
      (HasDerivedCategory.standard X.Modules) inferInstance 𝒢 F _ _ n (hall F hF)⟩

section Uniform

open Opposite CategoryTheory.Pretriangulated.Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

/-- **A uniform generator of the coherent modules, read inside `D_perf(𝒪_X)`.** If a finite
locally free `𝒢` and integers `m, n ≥ 1` make every coherent `𝒪_X`-module, in degree zero, a
direct summand of an `n`-fold extension of finite direct sums of shifts of `𝒢` by `[-m, m]` in
`D(𝒪_X)`, then the same membership holds in `D_perf(𝒪_X)`, for a perfect object `Z` (namely
`𝒢` in degree zero). -/
theorem exists_uniform_generator_coherentPerfect_of_uniformGenerator
    (hgen : ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :
    ∃ (m n : ℕ) (Z : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)),
      1 ≤ m ∧ 1 ≤ n ∧ ∀ (F : X.Modules) [F.IsCoherent],
        ((⨆ j ∈ Set.Icc (-(m : ℤ)) (m : ℤ),
          (ObjectProperty.singleton Z).isoClosure.shift
            j).binaryProductsClosure.extensionProductIter n).retractClosure
              (coherentPerfect f F) := by
  obtain ⟨m, n, 𝒢, hm, hn, h𝒢, hall⟩ := hgen
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := h𝒢
  have : 𝒢.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X 𝒢
  refine ⟨m, n, coherentPerfect f 𝒢, hm, hn, ?_⟩
  intro F hF
  refine retractClosure_extensionProductIter_biSup_shift_of_map_ι
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)
    (ObjectProperty.singleton (coherentPerfect f 𝒢)) (-(m : ℤ)) (m : ℤ) n ?_
  have hmap : (ObjectProperty.singleton (coherentPerfect f 𝒢)).map
      (ObjectProperty.ι (fun K : DerivedCategory X.Modules =>
        IsPerfect (X := X.toRingedSpace) K)) =
      (ObjectProperty.singleton ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure
      := by
    ext Y
    constructor <;> rintro ⟨W, hW, ⟨e⟩⟩ <;>
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hW <;>
      exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨e.symm⟩⟩
  simp only [hmap, isoClosure_eq_self]
  exact hall F hF

/-- A finite set of exceptional degrees lies in a window `[a, b]`, and a symmetric window `[-m, m]`
with `m ≥ 1` has the shifted window `[a - m₀, b + m₀]` inside it. -/
private theorem exists_window_of_finite {p : ℤ → Prop} (hfin : {i | ¬ p i}.Finite) (m₀ : ℕ) :
    ∃ (a b : ℤ) (m : ℕ), 1 ≤ m ∧ (∀ i ∉ Set.Icc a b, p i) ∧
      ∀ i ∉ Set.Icc (-(m : ℤ)) (m : ℤ), i ∉ Set.Icc (a + -(m₀ : ℤ)) (b + (m₀ : ℤ)) := by
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨b, hb⟩ := hfin.bddAbove
  refine ⟨a, b, 1 + (a - m₀).natAbs + (b + m₀).natAbs, by omega,
    fun i hi => not_not.1 fun hz => hi ⟨ha hz, hb hz⟩, fun i hi => ?_⟩
  simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
  omega

/-- **The uniform window of a homological functor, from a uniform generator.** Let `X` be smooth
over a field `k`, and suppose a finite locally free `𝒢` and `m₀, n ≥ 1` make every coherent
`𝒪_X`-module a member of `smd(add(𝒢[-m₀, m₀])^{⋆ n})`, as [Stacks, Tag 0FZ7] provides when `X` is
moreover proper. Let `H : D_perf(𝒪_X) ⥤ 𝒜` be homological with `H^i(K) = H(K[i])` nonzero for
only finitely many `i`, for every perfect `K`. Then there is `m ≥ 1` with `H^i(ℱ) = 0` for every
coherent `ℱ` and every `i ∉ [-m, m]`. -/
theorem exists_uniform_bound_isZero_of_isHomological_of_uniformGenerator
    (hgen : ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (Z⟦i⟧))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj ((coherentPerfect f F)⟦i⟧)) := by
  obtain ⟨m₀, n, Z, -, -, hall⟩ :=
    exists_uniform_generator_coherentPerfect_of_uniformGenerator f hgen
  obtain ⟨a, b, m, hm, hwin, hout⟩ := exists_window_of_finite (hfin Z) m₀
  refine ⟨m, hm, fun F hF i hi => ?_⟩
  refine H.isZero_obj_shift_of_retractClosure_extensionProductIter
    (ObjectProperty.singleton Z) (a := a) (b := b) ?_ (-(m₀ : ℤ)) (m₀ : ℤ) n (hall F)
    (hout i hi)
  intro Y hY
  obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
  exact hwin

/-- **The uniform window of a cohomological functor, from a uniform generator.** The
contravariant form of
`AlgebraicGeometry.exists_uniform_bound_isZero_of_isHomological_of_uniformGenerator`: a
cohomological functor on `D_perf(𝒪_X)` is a homological functor `D_perf(𝒪_X)ᵒᵖ ⥤ 𝒜`, and the
window argument is
`Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter`. -/
theorem exists_uniform_bound_isZero_of_isCohomological_of_uniformGenerator
    (hgen : ∃ (m n : ℕ) (𝒢 : X.Modules), 1 ≤ m ∧ 1 ≤ n ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) 𝒢 ∧
      ∀ F : X.Modules, F.IsCoherent →
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), (ObjectProperty.singleton
            ((DerivedCategory.singleFunctor X.Modules 0).obj 𝒢)).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter n).retractClosure
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : (ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K))ᵒᵖ ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (op (Z⟦i⟧)))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj (op ((coherentPerfect f F)⟦i⟧))) := by
  obtain ⟨m₀, n, Z, -, -, hall⟩ :=
    exists_uniform_generator_coherentPerfect_of_uniformGenerator f hgen
  obtain ⟨a, b, m, hm, hwin, hout⟩ := exists_window_of_finite (hfin Z) m₀
  refine ⟨m, hm, fun F hF i hi => ?_⟩
  refine isZero_obj_op_shift_of_retractClosure_extensionProductIter H
    (ObjectProperty.singleton Z) (a := a) (b := b) ?_ (-(m₀ : ℤ)) (m₀ : ℤ) n (hall F)
    (hout i hi)
  intro Y hY
  obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
  exact hwin

/-- **Uniform bounds for a homological functor on the coherent modules.** Let `k` be a field, let
`X` be a scheme proper and smooth over `k`, let `𝒜` be an abelian category and let
`H : D_perf(𝒪_X) ⥤ 𝒜` be a homological functor whose cohomology `H^i(K) = H(K[i])` is nonzero for
only finitely many `i`, for every perfect `K`. Then there is an `m ≥ 1` with `H^i(ℱ) = 0` for
every coherent `𝒪_X`-module `ℱ` and every `i ∉ [-m, m]`. -/
@[stacks 0FZ8 "the homological case; the cohomological case of the final sentence is \
`AlgebraicGeometry.exists_uniform_bound_isZero_of_isCohomological_of_isProper`"]
theorem exists_uniform_bound_isZero_of_isHomological_of_isProper [IsProper f]
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (Z⟦i⟧))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj ((coherentPerfect f F)⟦i⟧)) :=
  exists_uniform_bound_isZero_of_isHomological_of_uniformGenerator f
    (uniformGenerator_of_standardModel (exists_uniform_generator_isCoherent f)) H hfin

/-- **Uniform bounds for a cohomological functor on the coherent modules.** As
`AlgebraicGeometry.exists_uniform_bound_isZero_of_isHomological_of_isProper`, for a
cohomological functor, read as a homological functor `D_perf(𝒪_X)ᵒᵖ ⥤ 𝒜`. -/
@[stacks 0FZ8 "the cohomological case of the final sentence, a cohomological functor being a \
homological functor on the opposite category"]
theorem exists_uniform_bound_isZero_of_isCohomological_of_isProper [IsProper f]
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : (ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K))ᵒᵖ ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (op (Z⟦i⟧)))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj (op ((coherentPerfect f F)⟦i⟧))) :=
  exists_uniform_bound_isZero_of_isCohomological_of_uniformGenerator f
    (uniformGenerator_of_standardModel (exists_uniform_generator_isCoherent f)) H hfin

end Uniform

end AlgebraicGeometry

end
