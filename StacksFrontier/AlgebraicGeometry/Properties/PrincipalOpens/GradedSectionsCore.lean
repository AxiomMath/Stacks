module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The graded section calculus on a nonvanishing open: shared steps

Let `X` be a scheme, let `L` be an invertible `𝒪_X`-module with global section `s` and let `H`
be an `𝒪_X`-module. The injectivity proofs of
[Stacks, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW) and
[Stacks, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ) share two groups of steps, which
are collected here because neither of their files is below the other.

The first group computes the graded action of Tag 01CV on homogeneous elements: the action is the
coherence isomorphism applied to a pure tensor of global sections, so it restricts to zero on an
open as soon as the restricted pure tensor does; a power of `s` restricted to an open where `s`
has a local equation `r` is divisible by the matching power of `r`; raising the exponent only
multiplies by a further power of `s`, so on a quasi-compact space one exponent serves a finite
cover.

The second group is the local geometry of an invertible module: a frame of `L` over an open turns
`s` into `r · l` and identifies `X_s` there with `X.basicOpen r`, the trivializing opens of
Tag 0B8M cover the scheme, and over an open trivializing `P` the restriction of `A ⊗ P` is the
restriction of `A`.

## Main results

* `Stacks.SheafOfModules.sectionModuleAction_restrict_eq_zero_of_smul` and
  `Stacks.SheafOfModules.sectionPower_restrict_dvd_smul`: the graded action vanishes where a
  local equation for `s` annihilates the acted-on section.
* `Stacks.SheafOfModules.exists_sectionModuleAction_eq_zero_of_locally`: the quasi-compact
  gluing step, from local annihilation to one global exponent.
* `Stacks.SheafOfModules.exists_scalar_section_of_generator` and
  `Stacks.SheafOfModules.exists_mem_over_iso_unit`: a local equation for `s` in a frame, and the
  triviality of an invertible module near a point.
* `Stacks.SheafOfModules.tensorOverUnitIso`: the restriction of a tensor product with a
  trivialized factor.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite Limits
open scoped _root_.TensorProduct

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

section GradedAction

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

/- The graded section calculus of Tags 01CU, 0B5L and 0B5M states its algebraic structures over
`TensorSheafification.structureSheaf`, which instance search does not match against the structure
sheaf of a scheme; `Stacks.SchemeModulesSpelling` crosses that gap. -/
attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule

open MonoidalCategory DirectSum

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- Restricting a morphism of sheaves of modules to an open annihilates the image of anything
whose own restriction there vanishes. -/
theorem map_restrict_eq_zero_of_restrict_eq_zero
    {A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (φ : A ⟶ B) (a : A.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace) (ha : A.val.map (terminal.from U).op a = 0) :
    B.val.map (terminal.from U).op
      (φ.val.app (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) a) = 0 :=
  (PresheafOfModules.naturality_apply φ.val (terminal.from U).op a).symm.trans
    (by rw [ha, map_zero])

/-- The section of a tensor product cut out by a pair of sections is natural in the open. -/
theorem tensorSectionsAt_restrict
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {V W : (Opens X.toRingedSpace)ᵒᵖ} (f : V ⟶ W) (m : A.val.obj V) (n : B.val.obj V) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (A)).obj (B))).val.map f
        (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m n) =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) W A B
        (A.val.map f m) (B.val.map f n) := by
  have h := (TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).naturality f
  have hh := congrArg (fun k => k.hom (m ⊗ₜ[(sectionSiteRing X).obj V] n)) h
  change ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
      (A.val ⊗ B.val)).app W).hom
    ((A.val.map f).hom m ⊗ₜ[(sectionSiteRing X).obj W] (B.val.map f).hom n) = _ at hh
  exact hh.symm

/-- A scalar may be moved from one factor of a sectionwise tensor to the other. -/
theorem tensorSectionsAt_smul_comm
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (V : (Opens X.toRingedSpace)ᵒᵖ) (r : (sectionSiteRing X).obj V) (m : A.val.obj V)
    (n : B.val.obj V) :
    tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B (r • m) n =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m (r • n) :=
  congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).app V).hom (TensorProduct.smul_tmul r m n)

/-- Scalars may be pulled out of both factors of a sectionwise tensor. -/
private theorem tensorSectionsAt_smul_smul
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (V : (Opens X.toRingedSpace)ᵒᵖ) (r r' : (sectionSiteRing X).obj V) (m : A.val.obj V)
    (n : B.val.obj V) :
    tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B (r • m) (r' • n) =
      (r * r') • tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m n :=
  (congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).app V).hom (TensorProduct.smul_tmul_smul r r' m n)).trans (map_smul _ _ _)

/-- A sectionwise tensor with a vanishing right factor vanishes. -/
theorem tensorSectionsAt_zero_right
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (V : (Opens X.toRingedSpace)ᵒᵖ) (m : A.val.obj V) :
    tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m 0 = 0 :=
  (congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).app V).hom (TensorProduct.tmul_zero _ m)).trans (map_zero _)

/-- A sectionwise tensor with a vanishing left factor vanishes. -/
theorem tensorSectionsAt_zero_left
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (V : (Opens X.toRingedSpace)ᵒᵖ) (n : B.val.obj V) :
    tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B 0 n = 0 :=
  (congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).app V).hom (TensorProduct.zero_tmul _ n)).trans (map_zero _)

/-- A sectionwise tensor is additive in its left factor. -/
theorem tensorSectionsAt_sub_left
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (V : (Opens X.toRingedSpace)ᵒᵖ) (m m' : A.val.obj V) (n : B.val.obj V) :
    tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B (m - m') n =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m n -
        tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) V A B m' n :=
  (congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    (A.val ⊗ B.val)).app V).hom (TensorProduct.sub_tmul m m' n)).trans (map_sub _ _ _)

/-- A global pure tensor restricts to zero on an open where the left factor is divisible by a
function annihilating the restriction of the right factor. -/
theorem tensorGlobalSection_restrict_eq_zero_of_smul
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (a : A.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : B.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U)) (q : A.val.obj (op U))
    (ha : A.val.map (terminal.from U).op a = r • q)
    (hb : r • B.val.map (terminal.from U).op b = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (A)).obj (B))).val.map
        (terminal.from U).op
        (tensorGlobalSection (sectionSiteRing X) (sectionSiteSheaf X) A B a b) = 0 := by
  refine Eq.trans (tensorSectionsAt_restrict X A B (terminal.from U).op a b) ?_
  refine Eq.trans (congrArg (fun z => tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op U) A B z (B.val.map (terminal.from U).op b)) ha) ?_
  refine (tensorSectionsAt_smul_comm X A B (op U) r q _).trans ?_
  exact (congrArg (fun z => tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op U) A B q z) hb).trans (tensorSectionsAt_zero_right X A B (op U) q)

/-- A global pure tensor restricts to zero on an open where the right factor restricts to
zero. -/
theorem tensorGlobalSection_restrict_eq_zero
    (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (a : A.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : B.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace)
    (hb : B.val.map (terminal.from U).op b = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (A)).obj (B))).val.map
        (terminal.from U).op
        (tensorGlobalSection (sectionSiteRing X) (sectionSiteSheaf X) A B a b) = 0 :=
  tensorGlobalSection_restrict_eq_zero_of_smul X A B a b U 1
    (A.val.map (terminal.from U).op a) (one_smul _ _).symm (by rw [hb, smul_zero])

variable (H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The graded action of a homogeneous section restricts to zero on an open where the acting
section is divisible by a function annihilating the restriction of the acted-on section. -/
theorem sectionModuleAction_restrict_eq_zero_of_smul (n : ℕ) (j : ℤ)
    (c : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op U))
    (hc : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
      (terminal.from U).op c = r • q)
    (ht : r • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.map
        (terminal.from U).op t = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((n : ℤ) + j))))).val.map (terminal.from U).op
      (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H n j c t) = 0 := by
  unfold sectionModuleAction
  refine map_restrict_eq_zero_of_restrict_eq_zero X _ _ U ?_
  exact tensorGlobalSection_restrict_eq_zero_of_smul X _ _ c t U r q hc ht

/-- The graded action of a homogeneous section restricts to zero on an open where the acted-on
section restricts to zero. -/
theorem sectionModuleAction_restrict_eq_zero (n : ℕ) (j : ℤ)
    (c : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace)
    (ht : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.map
        (terminal.from U).op t = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((n : ℤ) + j))))).val.map (terminal.from U).op
      (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H n j c t) = 0 := by
  exact sectionModuleAction_restrict_eq_zero_of_smul X L H n j c t U 1
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
      (terminal.from U).op c) (one_smul _ _).symm (by rw [ht, smul_zero])

/-- The coherence isomorphism multiplying two natural-number tensor powers, with the degree
written as a cast of a sum of naturals. This is the isomorphism through which
`Stacks.SheafOfModules.sectionRingMul` is defined. -/
abbrev sectionRingMulIso (n m : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ)))).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (m : ℤ)))) ≅
      TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L ((n + m : ℕ) : ℤ) :=
  TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ) (m : ℤ) ≪≫
    TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
      (Int.natCast_add n m).symm

/-- The product of two homogeneous sections is the coherence isomorphism applied to their
sectionwise tensor. -/
theorem sectionRingMul_eq (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m a b =
      ((sectionRingMulIso X L n m).hom).val.app (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
        (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) _ _ a b) :=
  rfl

/-- The power sections of `s` satisfy `s ^ (n + 1) = s ^ n · s`. -/
theorem sectionPower_succ (s : L.sections) (n : ℕ) :
    sectionPower X L s (n + 1) =
      sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n 1 (sectionPower X L s n)
        ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
          (s.eval (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))) := by
  have h := pow_succ (homogeneousSection X L s) n
  rw [homogeneousSection_pow_eq_of_sectionPower X L s (n + 1),
    homogeneousSection_pow_eq_of_sectionPower X L s n] at h
  conv_rhs at h => rw [homogeneousSection]
  rw [DirectSum.of_mul_of,
    (chosenRingStructure (sectionSiteRing X) (sectionSiteSheaf X) L).mul_eq] at h
  have hn := congrArg (fun z => z (n + 1)) h
  simpa only [DirectSum.of_eq_same] using hn

/-- **The power sections multiply.** The product of `sⁿ` and `sᵐ` in the section ring is
`s^{n+m}`. -/
theorem sectionPower_add (s : L.sections) (n m : ℕ) :
    sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m
      (sectionPower X L s n) (sectionPower X L s m) = sectionPower X L s (n + m) := by
  apply DirectSum.of_injective (β := fun k : ℕ =>
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) (n + m)
  rw [← sectionRing_of_mul_of, ← homogeneousSection_pow_eq_of_sectionPower,
    ← homogeneousSection_pow_eq_of_sectionPower, ← homogeneousSection_pow_eq_of_sectionPower,
    _root_.pow_add]

/-- The restriction of a product of homogeneous sections to an open is the coherence isomorphism
there applied to the sectionwise tensor of the restrictions. -/
theorem sectionRingMul_restrict (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((n + m : ℕ) : ℤ)).val.map (terminal.from U).op
        (sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m a b) =
      (sectionRingMulIso X L n m).hom.val.app (op U)
        (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U)
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
            (terminal.from U).op a)
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
            (terminal.from U).op b)) := by
  rw [sectionRingMul_eq]
  refine (PresheafOfModules.naturality_apply (sectionRingMulIso X L n m).hom.val
    (terminal.from U).op _).symm.trans ?_
  exact congrArg (((sectionRingMulIso X L n m).hom.val.app (op U)).hom)
    (tensorSectionsAt_restrict X
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
      (terminal.from U).op a b)

/-- **The power sections multiply on an open.** The coherence isomorphism sends the sectionwise
tensor of the restrictions of `sⁿ` and `sᵐ` to the restriction of `s^{n+m}`. -/
theorem sectionRingMulIso_sectionPower (s : L.sections) (U : Opens X.toRingedSpace) (n m : ℕ) :
    (sectionRingMulIso X L n m).hom.val.app (op U)
        (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U)
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
            (terminal.from U).op (sectionPower X L s n))
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
            (terminal.from U).op (sectionPower X L s m))) =
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ)).val.map (terminal.from U).op (sectionPower X L s (n + m)) := by
  rw [← sectionRingMul_restrict, sectionPower_add]

/-- **Local divisibility of the power sections.** On an open where `s` is `r` times a section of
`L`, the restriction of `s ^ n` is `r ^ n` times a section of `L^{⊗ n}`. -/
theorem sectionPower_restrict_dvd_smul (s : L.sections) (U : Opens X.toRingedSpace)
    (r : (sectionSiteRing X).obj (op U)) (l : L.val.obj (op U))
    (hs : s.eval (op U) = r • l) (n : ℕ) :
    ∃ q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op U),
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s n) = r ^ n • q := by
  induction n with
  | zero =>
    refine ⟨(TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((0 : ℕ) : ℤ)).val.map (terminal.from U).op (sectionPower X L s 0), ?_⟩
    rw [_root_.pow_zero, one_smul]
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    have hc1 : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          ((1 : ℕ) : ℤ)).val.map (terminal.from U).op
          ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
            (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
            (s.eval (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))) =
        r • (TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
          (op U) l := by
      refine Eq.trans (PresheafOfModules.naturality_apply
        (TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val
        (terminal.from U).op
        (s.eval (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))).symm ?_
      refine Eq.trans (congrArg
        (((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X)
          L).inv.val.app (op U)).hom)
        ((PresheafOfModules.sections_property s (terminal.from U).op).trans hs)) ?_
      exact ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X)
        L).inv.val.app (op U)).hom.map_smul r l
    refine ⟨((sectionRingMulIso X L n 1).hom).val.app (op U)
      (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) _ _ q
        ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
          (op U) l)), ?_⟩
    rw [sectionPower_succ X L s n, sectionRingMul_restrict, hq, hc1]
    refine Eq.trans (congrArg (((sectionRingMulIso X L n 1).hom.val.app (op U)).hom)
      (tensorSectionsAt_smul_smul X _ _ (op U) _ _ _ _)) ?_
    exact (map_smul _ _ _).trans (congrArg (· • _) (_root_.pow_succ r n).symm)

/-- Acting by `s ^ (e + k)` is acting by `s ^ k` after acting by `s ^ e`, read on the
homogeneous elements of the section module. -/
theorem sectionModuleAction_add (s : L.sections) (e k : ℕ) (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ (((e + k : ℕ) : ℤ) + j)
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H (e + k) j
          (sectionPower X L s (e + k)) t) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      DirectSum.of _ ((k : ℤ) + ((e : ℤ) + j))
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H k ((e : ℤ) + j)
          (sectionPower X L s k)
          (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
            (sectionPower X L s e) t)) := by
  have hpow : (DirectSum.of _ (e + k) (sectionPower X L s (e + k)) :
        sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) =
      (DirectSum.of _ k (sectionPower X L s k) :
          sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) *
        (DirectSum.of _ e (sectionPower X L s e) :
          sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) := by
    rw [← homogeneousSection_pow_eq_of_sectionPower, ← homogeneousSection_pow_eq_of_sectionPower,
      ← homogeneousSection_pow_eq_of_sectionPower, ← _root_.pow_add, add_comm k e]
  have h1 := (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L H).smul_eq
    (e + k) j (sectionPower X L s (e + k)) t
  have h2 := (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L H).smul_eq
    e j (sectionPower X L s e) t
  have h3 := (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L H).smul_eq
    k ((e : ℤ) + j) (sectionPower X L s k)
    (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
      (sectionPower X L s e) t)
  refine h1.symm.trans (Eq.trans ?_ h3)
  refine Eq.trans (congrArg (fun c => c • (DirectSum.of _ j t :
    sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H)) hpow) ?_
  refine Eq.trans (mul_smul _ _ _) ?_
  exact congrArg (fun z => (DirectSum.of _ k (sectionPower X L s k) :
    sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) • z) h2

/-- Two homogeneous elements of the section module placed in equal degrees by equal inclusions
have the same restrictions, so one restricts to zero exactly when the other does. -/
theorem restrict_eq_zero_of_of_eq {j j' : ℤ} (hjj : j = j')
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j')))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hab : (DirectSum.of _ j a : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      DirectSum.of _ j' b)
    (U : Opens X.toRingedSpace)
    (hb : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j')))).val.map
        (terminal.from U).op b = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.map
        (terminal.from U).op a = 0 := by
  subst hjj
  have hc := congrArg
    (fun z : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H => z j) hab
  simp only [DirectSum.of_eq_same] at hc
  exact (congrArg (fun z => ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L j)))).val.map
      (terminal.from U).op z) hc).trans hb

/-- Raising the exponent preserves local vanishing of the twisted section. -/
theorem sectionModuleAction_restrict_eq_zero_of_le (s : L.sections) (e N : ℕ)
    (hle : e ≤ N) (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (U : Opens X.toRingedSpace)
    (ht : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e : ℤ) + j))))).val.map (terminal.from U).op
      (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
        (sectionPower X L s e) t) = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((N : ℤ) + j))))).val.map (terminal.from U).op
      (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H N j
        (sectionPower X L s N) t) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  refine restrict_eq_zero_of_of_eq X L H (by push_cast; ring) _ _
    (sectionModuleAction_add X L H s e k j t) U ?_
  exact sectionModuleAction_restrict_eq_zero X L H k ((e : ℤ) + j) (sectionPower X L s k) _ U ht

/-- **The quasi-compact gluing step.** If near every point some power of `s` annihilates the
restriction of a twisted global section, then one power of `s` annihilates it globally. -/
theorem exists_sectionModuleAction_eq_zero_of_locally [CompactSpace X] (s : L.sections)
    (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hlocal : ∀ x : X, ∃ (e : ℕ) (U : Opens X.toRingedSpace), x ∈ U ∧
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L
          ((e : ℤ) + j))))).val.map (terminal.from U).op
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
          (sectionPower X L s e) t) = 0) :
    ∃ e : ℕ, sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
      (sectionPower X L s e) t = 0 := by
  classical
  choose ee UU hmem hzero using hlocal
  obtain ⟨σ, hσ⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun y : X => (UU y : Set X)) (fun y => (UU y).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hmem z⟩)
  refine ⟨σ.sup ee, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
          (((σ.sup ee : ℕ) : ℤ) + j))))).val.presheaf,
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L
          (((σ.sup ee : ℕ) : ℤ) + j))))).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : (σ : Set X) => UU i.1) (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))
    (fun i => terminal.from (UU i.1)) ?_ _ 0 ?_
  · intro z _
    obtain ⟨y, hyσ, hzy⟩ : ∃ y ∈ σ, z ∈ UU y := by
      have h := hσ (Set.mem_univ z)
      simpa using h
    exact Opens.mem_iSup.2 ⟨⟨y, hyσ⟩, hzy⟩
  · intro i
    refine Eq.trans ?_ (map_zero _).symm
    exact sectionModuleAction_restrict_eq_zero_of_le X L H s (ee i.1) (σ.sup ee)
      (Finset.le_sup i.2) j t (UU i.1) (hzero i.1)

end GradedAction

section LocalTriviality

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

/-- The sections of an `𝒪_X`-module over an open form a module over the sections of the
structure sheaf there. Mathlib states this for the abelian-presheaf spelling `Γ(M, U)`, which
instance search does not match against the `ModuleCat`-valued spelling used by the graded section
calculus. -/
@[instance_reducible]
def moduleOfSections {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens) :
    Module (Y.presheaf.obj (op V)) (M.val.obj (op V)) :=
  (M.val.obj (op V)).isModule

attribute [local instance] moduleOfSections

/-- **Restriction of a tensor product with a trivialized factor.** Over an open on which `P` is
isomorphic to the structure sheaf, the restriction of `A ⊗ P` is the restriction of `A`. -/
noncomputable def tensorOverUnitIso
    {Y : Scheme.{u}} (A P : Y.Modules) (U : Y.Opens)
    (e : P.over U ≅ _root_.SheafOfModules.unit
      ((structureSheafRing Y.toRingedSpace).over U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing Y),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing Y)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf Y))⟩).obj (A)).obj (P))).over U ≅
      A.over U :=
  _root_.AlgebraicGeometry.tensorRestrictionIso Y.toRingedSpace A P U ≪≫
    Invertible.tensorProductIso (Y.toRingedSpace.sheaf.over U).obj
      (Y.ringCatSheaf.over U).property (Iso.refl _) e ≪≫
    Invertible.tensorProductRightUnitor (Y.toRingedSpace.sheaf.over U).obj
      (Y.ringCatSheaf.over U).property (A.over U)

/-- **A local equation for a global section in a frame.** If `g` trivializes `M` over `U`, then
the restriction of `s` to `U` is a multiple `r • g` of the frame, and the basic open of `r` is
contained in the open where `s` does not vanish. -/
lemma exists_scalar_section_of_generator
    {Y : Scheme.{u}}
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M]
    (s : M.sections) {U : Opens Y.toRingedSpace}
    (g : GeneratorSections Y.toRingedSpace M U) :
    ∃ (r : (sectionSiteRing Y).obj (op U)) (l : M.val.obj (op U)),
      s.eval (op U) = r • l ∧ Y.basicOpen r ≤ nonvanishingOpen M s := by
  have hbij := g.property U le_rfl
  rw [generator_restrict_self M U g] at hbij
  obtain ⟨r, hr⟩ := hbij.surjective (s.eval (op U))
  refine ⟨r, g.val, hr.symm, fun z hz => ?_⟩
  have hzU : z ∈ U := Y.basicOpen_le r hz
  exact (mem_nonvanishingLocus_iff_isUnit_ringGerm M s g r hr.symm z hzU).mpr
    ((isUnit_ringGerm_iff_mem_basicOpen r z hzU).mpr hz)

/-- **An invertible module on a scheme is trivial near every point**, at the ringed-space
spelling of the structure sheaf: the trivializing opens of Tag 0B8M cover the scheme, so one of
them contains any given point. -/
lemma exists_mem_over_iso_unit
    {Y : Scheme.{u}}
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] (z : Y) :
    ∃ V : Opens Y.toRingedSpace, z ∈ V ∧ Nonempty (M.over V ≅
      _root_.SheafOfModules.unit
        ((structureSheafRing Y.toRingedSpace).over V)) := by
  obtain ⟨I, V, hV, e⟩ :=
    (Invertible.isLocallyTrivial_of_isInvertible M).exists_trivializing_cover
  have hz : z ∈ ⨆ i, V i := ((Opens.coversTop_iff _ V).mp hV) ▸ Opens.mem_top z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
  exact ⟨V i, hi, e i⟩

end LocalTriviality

end Stacks.SheafOfModules

end
