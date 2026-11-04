module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Recognition
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorNorm
public import StacksFrontier.AlgebraicGeometry.NormInvertible.WellDefined
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The norm of an invertible module is additive on Picard groups

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` of degree `d` on functions
(`Stacks.Norm.MorphismNorm`, Tag 0BD1). This file proves that
`Stacks.Divisors.normInvertible f N` turns a tensor product into a tensor product, and hence that
the induced map on Picard groups of `Stacks.Divisors.exists_normPicardMap` is a homomorphism of
abelian groups.

This is one of the verifications that
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) omits, together with
well-definedness (`Stacks.Divisors.picardClass_normInvertible_congr`). The
source's own proof routes through the correspondence between invertible modules and
`H¹(X, 𝒪_X^*)` (Tag 09NU); **the route taken here does not**, and uses no cohomology at all.

## The obstruction, and what removes it

The norm is *defined* as the glue of a cocycle of normed transition units, so additivity asks for
a comparison between a **glue** and a **tensor product** — and nothing presents a tensor product
as a glue. The comparison is therefore made through
`Stacks.SheafOfModules.isoOfChartGenerators`: two modules carrying a
generator over each member of one open covering family, with the same pairwise transition units,
are isomorphic. Neither side has to be presented as a glue, which matters because
`normInvertible f N (L ⊗ M)` is a glue over `Stacks.Divisors.NormChart f (L ⊗ M)` while the
comparison runs over the **common** charts of `L` and `M`.

Those common charts are `Stacks.Divisors.TensorChart f L M = NormChart f L × NormChart f M`,
with the open of a pair being the intersection of the two chart opens. Over such an open both
`L` and `M` are trivial on the inverse image, so both sides acquire a generator:

* `Stacks.Divisors.normTensorGen`, the norm of the elementary tensor of the two chart generators;
* `Stacks.Divisors.tensorNormGen`, the elementary tensor of the norms of the two chart
  generators.

Their transition units agree, `Stacks.Divisors.generatorRatioUnit_tensorNormGen`, by three
multiplicativity statements and nothing else: the generator ratio is multiplicative
across a tensor product (`Stacks.SheafOfModules.generatorRatioUnit_tmulGenerator`), the normed
ratio is too (`Stacks.Divisors.normGeneratorRatio_tmulGenerator`), and the transition unit of two
normed generators is the norm of the transition unit upstairs
(`Stacks.Divisors.generatorRatioUnit_normGenerator`).

## Main definitions

* `Stacks.Divisors.TensorChart` and `Stacks.Divisors.tensorChartOpen`: the common charts of two
  modules.
* `Stacks.Divisors.tensorChartGenFst` and `Stacks.Divisors.tensorChartGenSnd`: the two chart
  generators over an open inside a common chart.
* `Stacks.Divisors.normTensorGen` and `Stacks.Divisors.tensorNormGen`: the chart generators of
  the two modules being compared.
* `Stacks.Divisors.normInvertibleTensorIso`: **the norm of a tensor product is the tensor product
  of the norms.**

## Main results

* `Stacks.Divisors.generatorRatioUnit_tensorNormGen`: the two chart generator families have the
  same transition units.
* `Stacks.Divisors.picardClass_normInvertible_tensorSheaf`: **the norm is additive on Picard
  classes.**
* `Stacks.Divisors.exists_normPicardAddMonoidHom`: **the norm descends to a homomorphism of
  abelian groups `Pic(X) → Pic(Y)`**, characterized by its value on the class of an invertible
  module. This strengthens `Stacks.Divisors.exists_normPicardMap`, which produced only a
  function.

## Implementation notes

No `@[stacks]` attribute is placed, following `WellDefined.lean`. Tag 0BCY asserts the existence
of a homomorphism `Norm_π : Pic(X) → Pic(Y)` *satisfying* `Norm_π(π^*𝒩) ≅ 𝒩^{⊗ d}`; the
homomorphism is constructed here and that property is not proved, so the tag is not carried in
full.

**Which Picard-group spelling.** The group structure on `Stacks.SheafOfModules.PicardGroup` is
found by instance search only through `AlgebraicGeometry.Scheme.ringCatIsSheaf`, so every
statement below that mentions addition is written at `AlgebraicGeometry.Scheme.picardGroup` and
`AlgebraicGeometry.Scheme.picardClass`, which are the spellings that carry that instance. The
sheaf-condition proofs in the three spellings are propositions and so definitionally equal, which
is why the characterizing law can still be stated at
`picardClass Y.presheaf (structureSheaf Y.sheaf).property` — the spelling `exists_normPicardMap`
uses — with no restatement.

Every tensor product here is `Stacks.SheafOfModules.Tensor.sheafTensor`, with the sheaf condition
of the structure sheaf written either as `X.toRingedSpace.IsSheaf` or through
`Presheaf.isSheaf_of_isSheaf_comp`. These are proofs of one proposition, so the iso proved for the
first spelling is accepted where `picardClass_tensorSheaf` wants the second, and no bridging lemma
appears.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- The norm of a generator, restricted, is the norm of the restricted generator. -/
theorem generatorRestrict_normGenerator (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    (L : X.Modules) (hL : HasTrivializingTargetCover f L) {W V : Y.Opens} (h : V ≤ W)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    generatorRestrict (X := Y.toRingedSpace) (normInvertible f N.toMorphismNormMap L) h
        (normGenerator f N.toMorphismNormMap L hL W s) =
      normGenerator f N.toMorphismNormMap L hL V
        (generatorRestrict (X := X.toRingedSpace) L
          ((Opens.map f.base).map (homOfLE h)).le s) :=
  (Subtype.ext (normGenerator_restrict f N.toMorphismNormMap L hL h s)).symm

/-- Restricting the norm of a generator gives the norm of any generator equal to its restriction. -/
private theorem generatorRestrict_normGenerator_of_eq (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    (L : X.Modules) (hL : HasTrivializingTargetCover f L) {W V : Y.Opens} (h : V ≤ W)
    {s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)}
    {t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)}
    (hst : generatorRestrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE h)).le s = t) :
    generatorRestrict (X := Y.toRingedSpace) (normInvertible f N.toMorphismNormMap L) h
        (normGenerator f N.toMorphismNormMap L hL W s) =
      normGenerator f N.toMorphismNormMap L hL V t :=
  (generatorRestrict_normGenerator f N L hL h s).trans (congrArg _ hst)

/-- The common charts of two modules: a chart of each, intersected. -/
abbrev TensorChart (f : X ⟶ Y) (L M : X.Modules) := NormChart f L × NormChart f M

/-- The open of a common chart. -/
def tensorChartOpen {f : X ⟶ Y} {L M : X.Modules} (c : TensorChart f L M) : Y.Opens :=
  c.1.val ⊓ c.2.val

/-- The common charts cover the target. -/
theorem tensorChart_cover {f : X ⟶ Y} {L M : X.Modules}
    (hL : HasTrivializingTargetCover f L) (hM : HasTrivializingTargetCover f M) :
    (⊤ : Y.Opens) ≤ ⨆ c : TensorChart f L M, tensorChartOpen c := by
  intro y _
  obtain ⟨U₁, hy₁, e₁⟩ := hL y
  obtain ⟨U₂, hy₂, e₂⟩ := hM y
  exact Opens.mem_iSup.mpr ⟨(⟨U₁, e₁⟩, ⟨U₂, e₂⟩), ⟨hy₁, hy₂⟩⟩

/-- The chart generator of `L` on a common chart, restricted to a smaller open. -/
noncomputable def tensorChartGenFst {f : X ⟶ Y} {L M : X.Modules} (c : TensorChart f L M)
    {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ A) :=
  normChartGeneratorOver f L c.1 A (h.trans inf_le_left)

/-- The chart generator of `M` on a common chart, restricted to a smaller open. -/
noncomputable def tensorChartGenSnd {f : X ⟶ Y} {L M : X.Modules} (c : TensorChart f L M)
    {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections X.toRingedSpace M (f ⁻¹ᵁ A) :=
  normChartGeneratorOver f M c.2 A (h.trans inf_le_right)

/-- Restricting the chart generator of `L` on a common chart gives the one on the smaller open. -/
theorem generatorRestrict_tensorChartGenFst {f : X ⟶ Y} {L M : X.Modules}
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE k)).le
        (tensorChartGenFst c h) =
      tensorChartGenFst c (k.trans h) :=
  normChartGeneratorOver_restrict f L c.1 (h.trans inf_le_left) k

/-- Restricting the chart generator of `M` on a common chart gives the one on the smaller open. -/
theorem generatorRestrict_tensorChartGenSnd {f : X ⟶ Y} {L M : X.Modules}
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := X.toRingedSpace) M ((Opens.map f.base).map (homOfLE k)).le
        (tensorChartGenSnd c h) =
      tensorChartGenSnd c (k.trans h) :=
  normChartGeneratorOver_restrict f M c.2 (h.trans inf_le_right) k

/-- The chart generator of the norm of the tensor product: the norm of the elementary tensor of
the two chart generators. -/
noncomputable def normTensorGen (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) {L M : X.Modules}
    (hLM : HasTrivializingTargetCover f ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))))
    (c : TensorChart f L M) {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections Y.toRingedSpace
      (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))) A :=
  normGenerator f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))) hLM A
    (tmulGenerator (tensorChartGenFst c h) (tensorChartGenSnd c h))

/-- The chart generator of the tensor product of the norms: the elementary tensor of the norms of
the two chart generators. -/
noncomputable def tensorNormGen (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) {L M : X.Modules}
    (hL : HasTrivializingTargetCover f L) (hM : HasTrivializingTargetCover f M)
    (c : TensorChart f L M) {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections Y.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj ((normInvertible f N.toMorphismNormMap L))).obj
        ((normInvertible f N.toMorphismNormMap M)))) A :=
  tmulGenerator (normGenerator f N.toMorphismNormMap L hL A (tensorChartGenFst c h))
    (normGenerator f N.toMorphismNormMap M hM A (tensorChartGenSnd c h))

/-- Restricting `normTensorGen` gives `normTensorGen` on the smaller open. -/
theorem generatorRestrict_normTensorGen (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (hLM : HasTrivializingTargetCover f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))))
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))) k
        (normTensorGen f N hLM c h) =
      normTensorGen f N hLM c (k.trans h) := by
  refine generatorRestrict_normGenerator_of_eq f N _ hLM k ?_
  exact (tmulGenerator_restrict (X := X.toRingedSpace) (tensorChartGenFst c h)
    (tensorChartGenSnd c h) ((Opens.map f.base).map (homOfLE k)).le).trans
    (congrArg₂ tmulGenerator (generatorRestrict_tensorChartGenFst c h k)
      (generatorRestrict_tensorChartGenSnd c h k))

/-- Restricting `tensorNormGen` gives `tensorNormGen` on the smaller open. -/
theorem generatorRestrict_tensorNormGen (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
          ((Y.toRingedSpace)).IsSheaf⟩).obj ((normInvertible f N.toMorphismNormMap L))).obj
          ((normInvertible f N.toMorphismNormMap M)))) k
        (tensorNormGen f N hL hM c h) =
      tensorNormGen f N hL hM c (k.trans h) := by
  refine (tmulGenerator_restrict (X := Y.toRingedSpace)
    (normGenerator f N.toMorphismNormMap L hL A (tensorChartGenFst c h))
    (normGenerator f N.toMorphismNormMap M hM A (tensorChartGenSnd c h)) k).trans ?_
  exact congrArg₂ tmulGenerator
    (generatorRestrict_normGenerator_of_eq f N L hL k (generatorRestrict_tensorChartGenFst c h k))
    (generatorRestrict_normGenerator_of_eq f N M hM k (generatorRestrict_tensorChartGenSnd c h k))

/-- **The transition units of the two chart generator families agree**, by multiplicativity of
the generator ratio across a tensor product and multiplicativity of the norm. -/
theorem generatorRatioUnit_tensorNormGen (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (hLM : HasTrivializingTargetCover f ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))))
    (c₁ c₂ : TensorChart f L M) (A : Y.Opens)
    (h₁ : A ≤ tensorChartOpen c₁) (h₂ : A ≤ tensorChartOpen c₂) :
    generatorRatioUnit (X := Y.toRingedSpace)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
          ((Y.toRingedSpace)).IsSheaf⟩).obj ((normInvertible f N.toMorphismNormMap L))).obj
          ((normInvertible f N.toMorphismNormMap M)))) A
        (tensorNormGen f N hL hM c₂ h₂) (tensorNormGen f N hL hM c₁ h₁) =
      generatorRatioUnit (X := Y.toRingedSpace)
        (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))) A
        (normTensorGen f N hLM c₂ h₂) (normTensorGen f N hLM c₁ h₁) := by
  refine Eq.symm ?_
  refine (generatorRatioUnit_normGenerator f N.toMorphismNormMap _ hLM A
    (tmulGenerator (tensorChartGenFst c₂ h₂) (tensorChartGenSnd c₂ h₂))
    (tmulGenerator (tensorChartGenFst c₁ h₁) (tensorChartGenSnd c₁ h₁))).trans ?_
  refine (normGeneratorRatio_tmulGenerator f N L M A (tensorChartGenFst c₂ h₂)
    (tensorChartGenFst c₁ h₁) (tensorChartGenSnd c₂ h₂) (tensorChartGenSnd c₁ h₁)).trans ?_
  refine Eq.trans ?_ (generatorRatioUnit_tmulGenerator (X := Y.toRingedSpace)
    (normGenerator f N.toMorphismNormMap L hL A (tensorChartGenFst c₂ h₂))
    (normGenerator f N.toMorphismNormMap L hL A (tensorChartGenFst c₁ h₁))
    (normGenerator f N.toMorphismNormMap M hM A (tensorChartGenSnd c₂ h₂))
    (normGenerator f N.toMorphismNormMap M hM A (tensorChartGenSnd c₁ h₁))).symm
  exact congrArg₂ (fun y z : (Γ(Y, A))ˣ => y * z)
    (generatorRatioUnit_normGenerator f N.toMorphismNormMap L hL A (tensorChartGenFst c₂ h₂)
      (tensorChartGenFst c₁ h₁)).symm
    (generatorRatioUnit_normGenerator f N.toMorphismNormMap M hM A (tensorChartGenSnd c₂ h₂)
      (tensorChartGenSnd c₁ h₁)).symm

/-- **The norm of a tensor product is the tensor product of the norms.** -/
noncomputable def normInvertibleTensorIso (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (hLM : HasTrivializingTargetCover f ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))) :
    normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj ((normInvertible f N.toMorphismNormMap L))).obj
        ((normInvertible f N.toMorphismNormMap M))) :=
  isoOfChartGenerators (X := Y.toRingedSpace)
    (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))))
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
      ((Y.toRingedSpace)).IsSheaf⟩).obj ((normInvertible f N.toMorphismNormMap L))).obj
      ((normInvertible f N.toMorphismNormMap M))))
    (fun c => normTensorGen f N hLM c le_rfl)
    (fun c => tensorNormGen f N hL hM c le_rfl)
    (fun i j A hi hj =>
      ((congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace) _ A)
          (generatorRestrict_tensorNormGen f N hL hM j le_rfl hj)
          (generatorRestrict_tensorNormGen f N hL hM i le_rfl hi)).trans
        (generatorRatioUnit_tensorNormGen f N hL hM hLM i j A hi hj)).trans
      (congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace) _ A)
          (generatorRestrict_normTensorGen f N hLM j le_rfl hj)
          (generatorRestrict_normTensorGen f N hLM i le_rfl hi)).symm)
    (tensorChart_cover hL hM)

/-- **The norm is additive on Picard classes.** -/
theorem picardClass_normInvertible_tensorSheaf (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (N : MorphismNorm f d) (L M : X.Modules)
    (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L)
    (hM : IsInvertible X.presheaf (structureSheaf X.sheaf).property M)
    (hNLM : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property
      (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))))
    (hNL : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property
      (normInvertible f N.toMorphismNormMap L))
    (hNM : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property
      (normInvertible f N.toMorphismNormMap M)) :
    Y.picardClass
        (normInvertible f N.toMorphismNormMap ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))) hNLM =
      Y.picardClass (normInvertible f N.toMorphismNormMap L) hNL +
        Y.picardClass (normInvertible f N.toMorphismNormMap M) hNM := by
  have hNLNM := isInvertible_tensorSheaf Y.presheaf Y.ringCatIsSheaf
    (normInvertible f N.toMorphismNormMap L) (normInvertible f N.toMorphismNormMap M)
  have hLM := isInvertible_tensorSheaf X.presheaf (structureSheaf X.sheaf).property L M
  refine Eq.trans ?_ (Y.picardClass_tensorSheaf (normInvertible f N.toMorphismNormMap L)
    (normInvertible f N.toMorphismNormMap M) hNL hNM hNLNM).symm
  refine (Y.picardClass_eq_iff _ _ hNLM hNLNM).mpr ⟨?_⟩
  exact normInvertibleTensorIso f N
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f M hM)
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f _ hLM)

/-- **The norm descends to a homomorphism of Picard groups.** -/
@[stacks 0BCY "the homomorphism of abelian groups"]
theorem exists_normPicardAddMonoidHom (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (N : MorphismNorm f d) :
    ∃ F : X.picardGroup →+ Y.picardGroup,
      ∀ (L : X.Modules) (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L),
        F (picardClass X.presheaf (structureSheaf X.sheaf).property L hL) =
          picardClass Y.presheaf (structureSheaf Y.sheaf).property
            (normInvertible f N.toMorphismNormMap L)
            (isInvertible_normInvertible f N.toMorphismNormMap L
              (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)) := by
  obtain ⟨F, hF⟩ := exists_normPicardMap f N
  refine ⟨AddMonoidHom.mk' F ?_, hF⟩
  intro x y
  obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq X.presheaf (structureSheaf X.sheaf).property x
  obtain ⟨M, hM, rfl⟩ := exists_picardClass_eq X.presheaf (structureSheaf X.sheaf).property y
  have hLM := isInvertible_tensorSheaf X.presheaf (structureSheaf X.sheaf).property L M
  refine Eq.trans (congrArg F (X.picardClass_tensorSheaf L M hL hM hLM)) ?_
  refine (hF _ hLM).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b : Y.picardGroup => a + b)
    (hF L hL).symm (hF M hM).symm)
  exact picardClass_normInvertible_tensorSheaf f N L M hL hM _ _ _

end Stacks.Divisors

end
