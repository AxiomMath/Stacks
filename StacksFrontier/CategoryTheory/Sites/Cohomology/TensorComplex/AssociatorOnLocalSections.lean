module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The associator of the total tensor complex on an iterated local pure tensor

Let `(C, O)` be a ringed site and let `A`, `B`, `D` be complexes of `O`-modules.  Complexes of
`O`-modules are symmetric monoidal with the total tensor complex
`Stacks.SheafOfModules.Tensor.tensorComplex` as their tensor product, on the nose, by Stacks 0FPQ
(`Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes`, whose
`tensor_eq_total` field is `rfl`).  So `α_ A B D` exists.  **This file computes it on the
generators**: on the homogeneous local pure tensor of `x`, `y`, `z` it reassociates,

`α_((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z)`,

with no sign and no hypothesis.

## Why this is the lemma that was missing

Every other ingredient of the derived-duality cluster of Example 0FPC already has its
local-section formula —
`AlgebraicGeometry.RingedSite.curryHomEquiv_val_app_tensorComplexSection`,
`AlgebraicGeometry.RingedSite.cochainEvaluation_val_app_tensorComplexSection`,
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_inv_tensorComplexSection` — and the
associator did not.  That is what made the chain-level transcription of the associativity
coherence of Stacks 08DI against Stacks 08J9 unavailable: the coherence is the only equation of
the cluster in which the associator occurs, and the local-section method of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAsTranspose` cannot be run on
it without this formula.  The implementation notes of that module attribute the obstruction
instead to the associator not existing — "the total tensor complex of this development carries no
associator, the good-trifunctor instances not being available".  That is false, as the existence
of `α_ A B D` here shows; the narrow fact that was missing is the formula below.

## Main results

* `AlgebraicGeometry.RingedSite.moduleAssociator_moduleTensorSection`: **the associator of
  `Mod(O)` reassociates a local pure tensor.**  This is Stacks 01CA's associator read on
  sections.
* `AlgebraicGeometry.RingedSite.ι₁₂_comp_associator_hom_f`: Mathlib's
  `HomologicalComplex.ι_mapBifunctorAssociatorX_hom` in this setting — the complex associator
  against the two iterated summand inclusions is the module associator.
* `AlgebraicGeometry.RingedSite.associator_tensorComplexSection`: **the associator of the total
  tensor complex reassociates an iterated homogeneous local pure tensor.**

## How it is proved

The module-level formula is assembled from two results about the *other* spelling of the
tensor product sheaf: `Stacks.SheafOfModules.associator_eq_tensorSheafAssociator`, which
identifies `α_` of the strict monoidal structure of Stacks 01CA with
`Stacks.SheafOfModules.tensorSheafAssociator`, and
`Stacks.SheafOfModules.tensorSections_associatorAt`, which computes that associator on local pure
tensors.  The two monoidal structures on `Mod(O)` are reconciled for free: their associators are
**the same term**, and the two spellings of the sheaf of rings and of the tensor product sheaf
are identified by `Stacks.SheafOfModules.TensorEncodings.ringSheaf_eq_structureSheaf`, which is
`rfl`.  So nothing about the sheafification-localized monoidal structure has to be unfolded here.

The passage to complexes is Mathlib's associator-against-inclusions lemma together with
`HomologicalComplex.mapBifunctor₁₂.ι_eq` and `HomologicalComplex.mapBifunctor₂₃.ι_eq`, which
decompose the iterated inclusions, and the two whiskering formulas below, which carry a local pure
tensor through a map of one factor.  `AlgebraicGeometry.RingedSite.tensorComplexSection` *is* the
summand inclusion applied to the module-level local pure tensor, by `rfl`.

## Nothing here is tagged

Stacks 0FPQ is carried by `Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes`
and Stacks 01CA by `Stacks.SheafOfModules.Strict.monoidalCategory`; the value of their
associativity constraint on a local section is a computation inside those structures, which
neither published statement makes.  So no declaration below carries a `@[stacks]` attribute.

## Implementation notes

*The last step is a `congrArg`, not a `rw`.*  Rewriting the left-hand side with
`tensorComplexSection_eq_ι₁₂` is rejected — "did not find an occurrence of the pattern" — with a
pattern the goal displays verbatim; the same equation applied by `congrArg` and `Eq.trans`, which
checks by definitional equality instead of syntactically, goes through.  The right-hand side is
rewritten normally.  That asymmetry is the measurement; the usual advice of trying the reverse
order first does not resolve it here, because only one of the two rewrites is at fault.

*The degree hypotheses are explicit binders, not `by omega`.*  With `(by omega)` in the statement
the proof term in a lemma's pattern is not the proof term in the goal, and `rw` misses even where
the two sections are the same; `a + b + d = j` and `a + (b + d) = j` are therefore both carried.

*The local pure tensor is defined at the `sheafificationAdjunction` unit spelling*, which is the
one `AlgebraicGeometry.RingedSite.tensorComplexSection` is built from, and
`moduleTensorSection_eq` records that it *is*
`Stacks.SheafOfModules.tensorSectionsAt`, which the section formulas of the Stacks 01CA
development are stated with, by `rfl`.  No second encoding is introduced.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The local pure tensor of two sections of sheaves of modules. -/
def moduleTensorSection (U : X.Cᵒᵖ)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : F.val.obj U) (t : G.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj F).obj G).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
    (F.val ⊗ G.val)).app U (s ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] t)

/-- (b) The local pure tensor of the total tensor complex is the inclusion of the summand applied
to the module-level local pure tensor. -/
theorem tensorComplexSection_eq_ι
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    tensorComplexSection X t r c h a b =
      (HomologicalComplex.ιMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) t r c (by simpa using h)).val.app (op W)
          (moduleTensorSection X (op W) (A.X t) (B.X r) a b) :=
  rfl

/-- Whiskering on the right acts on a local pure tensor through the left factor. -/
theorem moduleTensorSection_whiskerRight (U : X.Cᵒᵖ)
    {F F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : F ⟶ F')
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : F.val.obj U) (t : N.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map f).app N).val.app U
        (moduleTensorSection X U F N s t) =
      moduleTensorSection X U F' N (f.val.app U s) t :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) U F F' N N f (𝟙 N)
    s t

/-- Whiskering on the left acts on a local pure tensor through the right factor. -/
theorem moduleTensorSection_whiskerLeft (U : X.Cᵒᵖ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : G ⟶ G')
    (s : M.val.obj U) (t : G.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).map g).val.app U
        (moduleTensorSection X U M G s t) =
      moduleTensorSection X U M G' s (g.val.app U t) :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) U M M G G' (𝟙 M) g
    s t

section Mon

attribute [local instance]
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- **The associator of modules reassociates a local pure tensor.** -/
theorem moduleAssociator_moduleTensorSection (U : X.Cᵒᵖ)
    (F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : F.val.obj U) (t : G.val.obj U) (u : H.val.obj U) :
    ((α_ F G H).hom.val.app U)
        (moduleTensorSection X U
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj F).obj G) H
          (moduleTensorSection X U F G s t) u) =
      moduleTensorSection X U F
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj G).obj H) s
        (moduleTensorSection X U G H t u) :=
  Stacks.SheafOfModules.associator_hom_val_app_tmul X.O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) F G H U s t u

/-- (c) The associator against the summand inclusions, Mathlib's lemma in this setting. -/
theorem ι₁₂_comp_associator_hom_f
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a b d j : ℤ) (h : a + b + d = j) :
    HomologicalComplex.mapBifunctor₁₂.ι
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ) a b d j
        (by simp [ComplexShape.r, ComplexShape.π]; omega) ≫
        (α_ A B D).hom.f j =
      (α_ (A.X a) (B.X b) (D.X d)).hom ≫
        HomologicalComplex.mapBifunctor₂₃.ι
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) a b d j
          (by simp [ComplexShape.r, ComplexShape.π]; omega) := by
  apply HomologicalComplex.ι_mapBifunctorAssociatorX_hom

/-- (3) The iterated local pure tensor, left-bracketed, through the `₁₂` inclusion. -/
theorem tensorComplexSection_eq_ι₁₂
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (a b d j : ℤ) (h : a + b + d = j)
    (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W))
    (z : (D.X d).val.obj (op W)) :
    tensorComplexSection X (a + b) d j h
        (tensorComplexSection X a b (a + b) rfl x y) z =
      (HomologicalComplex.mapBifunctor₁₂.ι
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ) a b d j
        (by simp [ComplexShape.r, ComplexShape.π]; omega)).val.app (op W)
        (moduleTensorSection X (op W)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (A.X a)).obj (B.X b))
          (D.X d) (moduleTensorSection X (op W) (A.X a) (B.X b) x y) z) := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      a b d (a + b) j rfl (by simpa using h),
    comp_val_app_apply, moduleTensorSection_whiskerRight]
  rfl

/-- (4) The iterated local pure tensor, right-bracketed, through the `₂₃` inclusion. -/
theorem tensorComplexSection_eq_ι₂₃
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (a b d j : ℤ) (h' : a + (b + d) = j)
    (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W))
    (z : (D.X d).val.obj (op W)) :
    tensorComplexSection X a (b + d) j h' x
        (tensorComplexSection X b d (b + d) rfl y z) =
      (HomologicalComplex.mapBifunctor₂₃.ι
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) a b d j
        (by simp [ComplexShape.r, ComplexShape.π]; omega)).val.app (op W)
        (moduleTensorSection X (op W) (A.X a)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (B.X b)).obj (D.X d))
          x (moduleTensorSection X (op W) (B.X b) (D.X d) y z)) := by
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ A B D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) a b d (b + d) j rfl (by simpa using h'),
    comp_val_app_apply, moduleTensorSection_whiskerLeft]
  rfl

/-- **The associator of complexes reassociates an iterated local pure tensor.** -/
theorem associator_tensorComplexSection
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (a b d j : ℤ) (h : a + b + d = j) (h' : a + (b + d) = j)
    (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W))
    (z : (D.X d).val.obj (op W)) :
    ((α_ A B D).hom.f j).val.app (op W)
        (tensorComplexSection X (a + b) d j h
          (tensorComplexSection X a b (a + b) rfl x y) z) =
      tensorComplexSection X a (b + d) j h' x
        (tensorComplexSection X b d (b + d) rfl y z) := by
  rw [tensorComplexSection_eq_ι₂₃ X A B D W a b d j h' x y z]
  refine Eq.trans (congrArg
    (fun t => (ConcreteCategory.hom (((α_ A B D).hom.f j).val.app (op W))) t)
    (tensorComplexSection_eq_ι₁₂ X A B D W a b d j h x y z)) ?_
  rw [← comp_val_app_apply, ι₁₂_comp_associator_hom_f X A B D a b d j h, comp_val_app_apply,
    moduleAssociator_moduleTensorSection]

end Mon

end AlgebraicGeometry.RingedSite

end
