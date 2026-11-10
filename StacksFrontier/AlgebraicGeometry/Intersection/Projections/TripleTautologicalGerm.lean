module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TautologicalSectionLinear
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism

/-!
# The scalars of a tautological section are pulled back from `Spec k`

The tautological section `iota v` of `O(1)` on `P(M)` is `k`-homogeneous in `v`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection_eval_smul` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TautologicalSectionLinear` records the
scalar it picks up as `pullbackScalarFunction k M f r`, the pullback along `f : T ⟶ P(M)` of the
function `r / 1`.

A germ computation on a product of several projective spaces has to multiply such scalars coming
from *different* factors — one per slot of a tensor of tautological sections — and the scalars
produced are a priori different functions on `T`, one per projection. This file identifies them:
the function `r / 1` on `P(M)` is the pullback of `r` along the structure morphism
`P(M) ⟶ Spec k`, so the scalar attached to a slot depends only on the composite
`T ⟶ P(M) ⟶ Spec k`, which is the structure morphism of `T` for every slot. All of them are
therefore the single ring homomorphism
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGerm`, and that is what lets the ratios of the
three slots be multiplied and the sum over a basis be pulled out of a minor.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarTop`: the constant function `r` on a scheme
  over `Spec k`, spelled in the ring of scalars of the sheaves of modules on it, which is the
  spelling in which it can act on them.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGerm`: its germ at a point, as a ring
  homomorphism out of `k`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGlobalFunction_eq_scalarTop`: the function
  `r / 1` on `P(M)` is the constant `r` of the structure morphism, because the global function
  named by a degree-zero element is the pullback of that element along `Proj 𝒮 ⟶ Spec 𝒮₀`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.appTop_scalarTop`: constants are compatible with
  pullback, which is what makes every slot's scalar the same one.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isUnit_scalarGerm`: a nonzero constant has unit
  germ, which is what turns a nonzero determinant into a nonvanishing section.

## Implementation notes

That the global function named by a degree-zero element is the pullback of that element along
`Proj 𝒮 ⟶ Spec 𝒮₀` is proved *inside*
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGlobalFunction_eq_scalarTop`, as two `have`s,
rather than as named lemmas. No public form of either exists, but
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyGerm` carries private copies
-- at the time of writing its `degreeZeroRingToGlobalSections_val` (`:169`) and
`degreeZeroRingToGlobalSections_eq_toSpecZero` (`:179`) -- so naming them here would add a second
declaration of each. They cannot be reused instead, being private, and that file's whole private
germ layer duplicates the public `TautologicalSectionLinear`: importing it here makes the public
`degreeSection_add` shadow the private one and breaks its proofs. That file carries complete Tag
0B1T proofs, and its private layer is left as it is.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u w

/-! ### Constants on a scheme over `Spec k` -/

section Constants

variable (k : Type u) [Field k]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The constant function `r` on a scheme over `Spec k`**: the image of `r` under the map on
global functions induced by a structure morphism to `Spec k`. It is spelled in the ring of
scalars of the sheaves of modules on the scheme, which is the spelling in which it can act on
them. -/
public def scalarTop {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) (r : k) :
    T.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ τ.appTop).hom r

/-- **The germ at a point of the constant function `r`**, as a ring homomorphism from `k` to the
local ring there. Every slot of a tensor of tautological sections contributes its scalar through
this one homomorphism, which is what lets the slots' ratios be multiplied. -/
public def scalarGerm {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) (t : T) :
    k →+* ringStalk T.toRingedSpace t :=
  (ringGerm T.toRingedSpace t ⊤ (Opens.mem_top t)).comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ τ.appTop).hom

/-- A nonzero constant has unit germ: a nonzero element of a field has unit image under any ring
homomorphism. -/
public theorem isUnit_scalarGerm {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) (t : T) {r : k}
    (hr : r ≠ 0) : IsUnit (scalarGerm k τ t r) :=
  IsUnit.map (scalarGerm k τ t) (isUnit_iff_ne_zero.mpr hr)

/-- The germ of the constant function `r` is the value at `r` of the germ homomorphism. -/
public theorem ringGerm_scalarTop {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) (t : T) (r : k) :
    ringGerm T.toRingedSpace t ⊤ (Opens.mem_top t) (scalarTop k τ r) = scalarGerm k τ t r := rfl

/-- Constants are compatible with pullback: the pullback of the constant `r` along a morphism of
schemes over `Spec k` is the constant `r`. -/
public theorem appTop_scalarTop {T T' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ Spec (.of k))
    (r : k) : g.appTop.hom (scalarTop k h r) = scalarTop k (g ≫ h) r := rfl

/-- **The pullback of a constant along a morphism of schemes over `Spec k` is the constant**, in
the `sharp` spelling in which `pullbackScalarFunction` produces it. -/
public theorem sharp_top_scalarTop {T T' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ Spec (.of k))
    (r : k) :
    Stacks.RingedSpace.sharp g.toLRSHom.toShHom (op ⊤) (scalarTop k h r) =
      scalarTop k (g ≫ h) r := rfl

/-- Over the top open the function `r / 1` is its own global form, the restriction being along
the identity. -/
public theorem scalarFunction_top (M : Type u) [AddCommGroup M] [Module k M] (r : k) :
    scalarFunction k M r (op ⊤) = scalarGlobalFunction k M r := by simp [scalarFunction]

end Constants

/-! ### The scalar of a slot -/

section Slot

variable (k M : Type u) [Field k] [AddCommGroup M] [Module k M]

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The constants on `𝐏(M)` are the global functions named by the degree-zero part of the
symmetric algebra**: the function `r / 1` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGlobalFunction` is the constant `r` of the
structure morphism. -/
public theorem scalarGlobalFunction_eq_scalarTop (r : k) :
    scalarGlobalFunction k M r = scalarTop k (projectiveSpaceOfModuleToSpec k M) r := by
  change degreeZeroRingToGlobalSections (symmetricGrading k M) (scalarUnit k M r) = _
  have hval : ∀ (z : symmetricGrading k M 0)
      (x : ProjectiveSpectrum.top (symmetricGrading k M)),
      HomogeneousLocalization.val
          ((degreeZeroRingToGlobalSections (symmetricGrading k M) z).1 ⟨x, trivial⟩) =
        algebraMap (SymmetricAlgebra k M)
          (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
          (z : SymmetricAlgebra k M) := by
    intro z x
    rw [← Proj.stalkIso'_germ (symmetricGrading k M) ⊤ x trivial
        (degreeZeroRingToGlobalSections (symmetricGrading k M) z),
      degreeZeroRingToGlobalSections_stalk]
    change Localization.mk z.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = _
    exact Localization.mk_algebraMap (A := SymmetricAlgebra k M) z.1
  have htoSpec : ∀ z : symmetricGrading k M 0,
      degreeZeroRingToGlobalSections (symmetricGrading k M) z =
        (Proj.toSpecZero (symmetricGrading k M)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (symmetricGrading k M 0))).inv.hom z) := by
    intro z
    refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
    rw [hval z x.1]
    exact (Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val
      (symmetricGrading k M) z x.1).symm
  rw [htoSpec]
  have e : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (projectiveSpaceOfModuleToSpec k M).appTop) =
      (CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k M))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (symmetricGrading k M 0))).inv ≫
          (Proj.toSpecZero (symmetricGrading k M)).appTop := by
    rw [show (projectiveSpaceOfModuleToSpec k M).appTop =
        (Spec.map (CommRingCat.ofHom
            (algebraMap k (SymPow.symmetricPower 0 k M)))).appTop ≫
          (Proj.toSpecZero (symmetricGrading k M)).appTop from rfl,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have hval := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp e) r
  have hs : scalarUnit k M r = algebraMap k (symmetricGrading k M 0) r := by
    refine Subtype.ext ?_
    rw [SetLike.GradeZero.coe_algebraMap]
    change r • (1 : SymmetricAlgebra k M) = algebraMap k (SymmetricAlgebra k M) r
    rw [Algebra.smul_def, mul_one]
  rw [hs]
  exact hval.symm

/-- **The scalar a slot contributes, over the top open, is the constant of the composite
structure morphism.** This is what makes the scalars of different slots of a tensor equal: each
depends on its slot only through `T ⟶ 𝐏(Mᵢ) ⟶ Spec k`, which is `T`'s own structure morphism. -/
public theorem pullbackScalarFunction_top {T : Scheme.{u}}
    (f : T ⟶ projectiveSpaceOfModule k M) (r : k) :
    pullbackScalarFunction k M f r (op ⊤) =
      scalarTop k (f ≫ projectiveSpaceOfModuleToSpec k M) r := by
  rw [pullbackScalarFunction, scalarGlobalFunction_eq_scalarTop, sharp_top_scalarTop]
  simp

/-- Over the top open, scaling the vector by `r` scales a pulled-back tautological section by the
constant `r` of any structure morphism `τ` through which `f` factors. -/
private theorem pullbackTautSection_eval_top_smul {T : Scheme.{u}} (τ : T ⟶ Spec (.of k))
    (f : T ⟶ projectiveSpaceOfModule k M) (hf : f ≫ projectiveSpaceOfModuleToSpec k M = τ)
    (r : k) (v : M) :
    (pullbackTautSection k M f (r • v)).eval (op ⊤) =
      scalarTop k τ r • (pullbackTautSection k M f v).eval (op ⊤) := by
  rw [pullbackTautSection_eval_smul, pullbackScalarFunction_top, hf]

end Slot

/-! ### `𝒪(1,1,1)` on a scheme over three projective spaces -/

section Triple

variable (k M₁ M₂ M₃ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  [AddCommGroup M₃] [Module k M₃]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (p₃ : T ⟶ projectiveSpaceOfModule k M₃)

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The invertible module `𝒪(1,1,1) = p₁^* 𝒪(1) ⊗ p₂^* 𝒪(1) ⊗ p₃^* 𝒪(1)`** on a scheme
carrying three morphisms to the projective spaces of three possibly different modules. It is
assembled left-nested, so that the invertibility instances and the nonvanishing-locus computation
are a two-step induction. -/
public def tripleTaut : T.Modules :=
  ((Tensor.sheafTensor ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj
      (((Tensor.sheafTensor ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback p₁).obj (tautologicalModule k M₁))).obj
        ((Scheme.Modules.pullback p₂).obj (tautologicalModule k M₂)))).obj
    ((Scheme.Modules.pullback p₃).obj (tautologicalModule k M₃))

/-- **`𝒪(1,1,1)` is invertible**: a pullback of an invertible module is invertible, and so is a
tensor product of invertible modules. -/
public theorem isInvertible_tripleTaut :
    Stacks.SheafOfModules.IsInvertible T.presheaf
      (structureSheafRing T.toRingedSpace).property (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃) :=
  have h12 := @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ T.presheaf
    (structureSheafRing T.toRingedSpace).property _ _
    ((Scheme.Modules.pullback p₁).obj (tautologicalModule k M₁))
    ((Scheme.Modules.pullback p₂).obj (tautologicalModule k M₂))
    (Stacks.Modules.isInvertible_pullback _ _) (Stacks.Modules.isInvertible_pullback _ _)
  @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ T.presheaf
    (structureSheafRing T.toRingedSpace).property _ _ _
    ((Scheme.Modules.pullback p₃).obj (tautologicalModule k M₃)) h12
    (Stacks.Modules.isInvertible_pullback _ _)

/-- **The tensor `p₁^*(ι a) ⊗ p₂^*(ι b) ⊗ p₃^*(ι c)` of three tautological sections**, a global
section of `𝒪(1,1,1)`. -/
public def tripleTautSection (a : M₁) (b : M₂) (c : M₃) :
    (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃).sections :=
  tensorSections _ _
    (tensorSections _ _ (pullbackTautSection k M₁ p₁ a) (pullbackTautSection k M₂ p₂ b))
    (pullbackTautSection k M₃ p₃ c)

/-- **The nonvanishing locus of a tensor of three tautological sections** is the intersection of
the three preimages of the standard opens of its factors. -/
public theorem nonvanishingLocus_tripleTautSection (a : M₁) (b : M₂) (c : M₃) :
    Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃) (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c) =
      (p₁.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOfModule k M₁).toRingedSpace)
          (tautologicalModule k M₁) (tautologicalSection k M₁ a) ∩
        p₂.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOfModule k M₂).toRingedSpace)
          (tautologicalModule k M₂) (tautologicalSection k M₂ b)) ∩
      p₃.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k M₃).toRingedSpace)
        (tautologicalModule k M₃) (tautologicalSection k M₃ c) :=
  (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans
    (congrArg₂ (· ∩ ·)
      ((Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans
        (congrArg₂ (· ∩ ·) (nonvanishingLocus_pullbackTautSection k M₁ p₁ a)
          (nonvanishingLocus_pullbackTautSection k M₂ p₂ b)))
      (nonvanishingLocus_pullbackTautSection k M₃ p₃ c))

/-- **A tensor of three tautological sections is nonvanishing at a point exactly when each of the
three degree-one forms avoids the homogeneous prime of the corresponding projection** of that
point. -/
public theorem mem_nonvanishingLocus_tripleTautSection_iff (a : M₁) (b : M₂) (c : M₃) (t : T) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃) (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c) ↔
      SymmetricAlgebra.ι k M₁ a ∉ (p₁.base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k M₂ b ∉ (p₂.base t).asHomogeneousIdeal ∧
          SymmetricAlgebra.ι k M₃ c ∉ (p₃.base t).asHomogeneousIdeal := by
  have h := Set.ext_iff.mp (nonvanishingLocus_tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c) t
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    Set.mem_preimage, mem_nonvanishingLocus_tautologicalSection_iff,
    mem_nonvanishingLocus_tautologicalSection_iff,
    mem_nonvanishingLocus_tautologicalSection_iff] at h
  exact h.trans and_assoc

/-! ### Trilinearity -/

/-- A tensor of two sections is additive over `U` in its left factor. -/
private theorem tensorSections_eval_add_left_of {X : RingedSpace.{u, u}}
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} {s s₁ s₂ : F.sections}
    {t : G.sections} {U : (Opens X.carrier)ᵒᵖ} (h : s.eval U = s₁.eval U + s₂.eval U) :
    (tensorSections F G s t).eval U =
      (tensorSections F G s₁ t).eval U + (tensorSections F G s₂ t).eval U :=
  Eq.trans (congrArg (fun x => TensorStalkRingedSpace.toTensorSheafSection X F G U
    (x ⊗ₜ[X.presheaf.obj U] t.eval U)) h) (tensorSections_eval_add_left _ _ _ _ _ _)

/-- A tensor of two sections is additive over `U` in its right factor. -/
private theorem tensorSections_eval_add_right_of {X : RingedSpace.{u, u}}
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} {s : F.sections}
    {t t₁ t₂ : G.sections} {U : (Opens X.carrier)ᵒᵖ} (h : t.eval U = t₁.eval U + t₂.eval U) :
    (tensorSections F G s t).eval U =
      (tensorSections F G s t₁).eval U + (tensorSections F G s t₂).eval U :=
  Eq.trans (congrArg (fun x => TensorStalkRingedSpace.toTensorSheafSection X F G U
    (s.eval U ⊗ₜ[X.presheaf.obj U] x)) h) (tensorSections_eval_add_right _ _ _ _ _ _)

/-- A tensor of two sections is homogeneous over `U` in its left factor. -/
private theorem tensorSections_eval_smul_left_of {X : RingedSpace.{u, u}}
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} {s s₁ : F.sections}
    {t : G.sections} {U : (Opens X.carrier)ᵒᵖ} {r : X.presheaf.obj U}
    (h : s.eval U = r • s₁.eval U) :
    (tensorSections F G s t).eval U =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U) _ _
        r ((tensorSections F G s₁ t).eval U) :=
  Eq.trans (congrArg (fun x => TensorStalkRingedSpace.toTensorSheafSection X F G U
    (x ⊗ₜ[X.presheaf.obj U] t.eval U)) h) (tensorSections_eval_smul_left _ _ _ _ _ _)

/-- A tensor of two sections is homogeneous over `U` in its right factor. -/
private theorem tensorSections_eval_smul_right_of {X : RingedSpace.{u, u}}
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} {s : F.sections}
    {t t₁ : G.sections} {U : (Opens X.carrier)ᵒᵖ} {r : X.presheaf.obj U}
    (h : t.eval U = r • t₁.eval U) :
    (tensorSections F G s t).eval U =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U) _ _
        r ((tensorSections F G s t₁).eval U) :=
  Eq.trans (congrArg (fun x => TensorStalkRingedSpace.toTensorSheafSection X F G U
    (s.eval U ⊗ₜ[X.presheaf.obj U] x)) h) (tensorSections_eval_smul_right _ _ _ _ _ _)

/-- **The tensor is additive in its first vector.** -/
public theorem tripleTautSection_eval_add_one (a a' : M₁) (b : M₂) (c : M₃)
    (U : (Opens ↥T)ᵒᵖ) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ (a + a') b c).eval U =
      (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval U +
        (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a' b c).eval U :=
  tensorSections_eval_add_left_of
    (tensorSections_eval_add_left_of (pullbackTautSection_eval_add k M₁ p₁ a a' U))

/-- **The tensor is additive in its second vector.** -/
public theorem tripleTautSection_eval_add_two (a : M₁) (b b' : M₂) (c : M₃)
    (U : (Opens ↥T)ᵒᵖ) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a (b + b') c).eval U =
      (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval U +
        (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b' c).eval U :=
  tensorSections_eval_add_left_of
    (tensorSections_eval_add_right_of (pullbackTautSection_eval_add k M₂ p₂ b b' U))

/-- **The tensor is additive in its third vector.** -/
public theorem tripleTautSection_eval_add_three (a : M₁) (b : M₂) (c c' : M₃)
    (U : (Opens ↥T)ᵒᵖ) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b (c + c')).eval U =
      (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval U +
        (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c').eval U :=
  tensorSections_eval_add_right_of (pullbackTautSection_eval_add k M₃ p₃ c c' U)

/-- **The tensor is `k`-homogeneous in its first vector**, over the top open, the scalar being
the single constant function of `T`'s structure morphism. -/
public theorem tripleTautSection_eval_top_smul_one (τ : T ⟶ Spec (.of k))
    (h₁ : p₁ ≫ projectiveSpaceOfModuleToSpec k M₁ = τ) (r : k) (a : M₁) (b : M₂) (c : M₃) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ (r • a) b c).eval (op ⊤) =
      scalarTop k τ r • (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤) :=
  tensorSections_eval_smul_left_of
    (tensorSections_eval_smul_left_of (pullbackTautSection_eval_top_smul k M₁ τ p₁ h₁ r a))

/-- **The tensor is `k`-homogeneous in its second vector**, over the top open. -/
public theorem tripleTautSection_eval_top_smul_two (τ : T ⟶ Spec (.of k))
    (h₂ : p₂ ≫ projectiveSpaceOfModuleToSpec k M₂ = τ) (r : k) (a : M₁) (b : M₂) (c : M₃) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a (r • b) c).eval (op ⊤) =
      scalarTop k τ r • (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤) :=
  tensorSections_eval_smul_left_of
    (tensorSections_eval_smul_right_of (pullbackTautSection_eval_top_smul k M₂ τ p₂ h₂ r b))

/-- **The tensor is `k`-homogeneous in its third vector**, over the top open. -/
public theorem tripleTautSection_eval_top_smul_three (τ : T ⟶ Spec (.of k))
    (h₃ : p₃ ≫ projectiveSpaceOfModuleToSpec k M₃ = τ) (r : k) (a : M₁) (b : M₂) (c : M₃) :
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b (r • c)).eval (op ⊤) =
      scalarTop k τ r • (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤) :=
  tensorSections_eval_smul_right_of (pullbackTautSection_eval_top_smul k M₃ τ p₃ h₃ r c)

end Triple


/-! ### The germ of the tensor at a point -/

section Germ

variable (k M₁ M₂ M₃ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  [AddCommGroup M₃] [Module k M₃]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (p₃ : T ⟶ projectiveSpaceOfModule k M₃)

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- `𝒪(1,1,1)` retyped as a sheaf of modules over the structure sheaf of `T` read as a ringed
space, which is the spelling whose stalks carry their module structure by instance search. -/
public abbrev tripleSh : _root_.SheafOfModules.{u} (structureSheafRing T.toRingedSpace) :=
  tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃

/-- **The germ at a point of the tensor of three tautological sections.** -/
public abbrev tripleGerm (t : T) (a : M₁) (b : M₂) (c : M₃) :
    grpStalk T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t :=
  grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t)
    ((tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤))

/-- The submodule `𝔪ₜ · 𝒪(1,1,1)ₜ` of the stalk at `t`: a global section is nonvanishing at `t`
exactly when its germ escapes it. -/
public abbrev tripleMax (t : T) :
    Submodule (ringStalk T.toRingedSpace t)
      (grpStalk T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t) :=
  IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace t) • ⊤

/-- **The nonvanishing locus of a global section of `𝒪(1,1,1)` as a condition on its germ.** -/
public theorem mem_nonvanishingLocus_iff_notMem_tripleMax (t : T)
    (s : (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃).sections) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃) s ↔
      grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t)
          (s.eval (op ⊤)) ∉ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := Iff.rfl

/-- The germ of a tensor whose value over `⊤` is a sum is the sum of the germs. -/
private theorem tripleGerm_add_of_eval_add (t : T) {a b c a₁ b₁ c₁ a₂ b₂ c₂}
    (h : (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤) =
      (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a₁ b₁ c₁).eval (op ⊤) +
        (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a₂ b₂ c₂).eval (op ⊤)) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c =
      tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₁ b₁ c₁ + tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₂ b₂ c₂ :=
  (congrArg (grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t))
      h).trans (map_add _ _ _)

/-- The germ of a tensor whose value over `⊤` is a scalar multiple is the scalar multiple of the
germ. -/
private theorem tripleGerm_smul_of_eval_smul (τ : T ⟶ Spec (.of k)) (t : T) (r : k)
    {a b c a₁ b₁ c₁}
    (h : (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c).eval (op ⊤) =
      scalarTop k τ r • (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a₁ b₁ c₁).eval (op ⊤)) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c =
      scalarGerm k τ t r • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₁ b₁ c₁ :=
  (congrArg (grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t))
      h).trans
    (stalkModule_germ_smul T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤
      (Opens.mem_top t) _ _)

/-- The germ is additive in its first vector. -/
public theorem tripleGerm_add_one (t : T) (a a' : M₁) (b : M₂) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (a + a') b c =
      tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c + tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a' b c :=
  tripleGerm_add_of_eval_add k M₁ M₂ M₃ p₁ p₂ p₃ t
    (tripleTautSection_eval_add_one k M₁ M₂ M₃ p₁ p₂ p₃ a a' b c (op ⊤))

/-- The germ is additive in its second vector. -/
public theorem tripleGerm_add_two (t : T) (a : M₁) (b b' : M₂) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a (b + b') c =
      tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c + tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b' c :=
  tripleGerm_add_of_eval_add k M₁ M₂ M₃ p₁ p₂ p₃ t
    (tripleTautSection_eval_add_two k M₁ M₂ M₃ p₁ p₂ p₃ a b b' c (op ⊤))

/-- The germ is additive in its third vector. -/
public theorem tripleGerm_add_three (t : T) (a : M₁) (b : M₂) (c c' : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b (c + c') =
      tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c + tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c' :=
  tripleGerm_add_of_eval_add k M₁ M₂ M₃ p₁ p₂ p₃ t
    (tripleTautSection_eval_add_three k M₁ M₂ M₃ p₁ p₂ p₃ a b c c' (op ⊤))

/-- The germ is `k`-homogeneous in its first vector. -/
public theorem tripleGerm_smul_one (τ : T ⟶ Spec (.of k))
    (h₁ : p₁ ≫ projectiveSpaceOfModuleToSpec k M₁ = τ) (t : T) (r : k) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (r • a) b c =
      scalarGerm k τ t r • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c :=
  tripleGerm_smul_of_eval_smul k M₁ M₂ M₃ p₁ p₂ p₃ τ t r
    (tripleTautSection_eval_top_smul_one k M₁ M₂ M₃ p₁ p₂ p₃ τ h₁ r a b c)

/-- The germ is `k`-homogeneous in its second vector. -/
public theorem tripleGerm_smul_two (τ : T ⟶ Spec (.of k))
    (h₂ : p₂ ≫ projectiveSpaceOfModuleToSpec k M₂ = τ) (t : T) (r : k) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a (r • b) c =
      scalarGerm k τ t r • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c :=
  tripleGerm_smul_of_eval_smul k M₁ M₂ M₃ p₁ p₂ p₃ τ t r
    (tripleTautSection_eval_top_smul_two k M₁ M₂ M₃ p₁ p₂ p₃ τ h₂ r a b c)

/-- The germ is `k`-homogeneous in its third vector. -/
public theorem tripleGerm_smul_three (τ : T ⟶ Spec (.of k))
    (h₃ : p₃ ≫ projectiveSpaceOfModuleToSpec k M₃ = τ) (t : T) (r : k) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b (r • c) =
      scalarGerm k τ t r • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c :=
  tripleGerm_smul_of_eval_smul k M₁ M₂ M₃ p₁ p₂ p₃ τ t r
    (tripleTautSection_eval_top_smul_three k M₁ M₂ M₃ p₁ p₂ p₃ τ h₃ r a b c)

end Germ

/-! ### The vanishing criterion at a triple of closed points -/

section Closed

variable (k M₁ M₂ M₃ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  [AddCommGroup M₃] [Module k M₃]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (p₃ : T ⟶ projectiveSpaceOfModule k M₃)
  (t : T) (f₁ : Module.Dual k M₁) (hf₁ : f₁ ≠ 0)
  (e₁ : p₁.base t = linearFunctionalPoint k M₁ f₁ hf₁)
  (f₂ : Module.Dual k M₂) (hf₂ : f₂ ≠ 0)
  (e₂ : p₂.base t = linearFunctionalPoint k M₂ f₂ hf₂)
  (f₃ : Module.Dual k M₃) (hf₃ : f₃ ≠ 0)
  (e₃ : p₃.base t = linearFunctionalPoint k M₃ f₃ hf₃)

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The germ avoids `𝔪ₜ · 𝒪(1,1,1)ₜ` exactly when each of the three degree-one forms avoids the
homogeneous prime of the corresponding projection of `t`. -/
private theorem tripleGerm_notMem_iff (a : M₁) (b : M₂) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c ∉ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t ↔
      SymmetricAlgebra.ι k M₁ a ∉ (p₁.base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k M₂ b ∉ (p₂.base t).asHomogeneousIdeal ∧
          SymmetricAlgebra.ι k M₃ c ∉ (p₃.base t).asHomogeneousIdeal :=
  (mem_nonvanishingLocus_iff_notMem_tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t
    (tripleTautSection k M₁ M₂ M₃ p₁ p₂ p₃ a b c)).symm.trans
    (mem_nonvanishingLocus_tripleTautSection_iff k M₁ M₂ M₃ p₁ p₂ p₃ a b c t)

include e₁ in
/-- **A first vector killed by the first functional makes the germ vanish** at a point whose
first projection is the closed point cut out by that functional. -/
public theorem tripleGerm_mem_of_one (a : M₁) (ha : f₁ a = 0) (b : M₂) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c ∈ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  by_contra h
  rw [tripleGerm_notMem_iff, e₁] at h
  exact h.1 ((linearFunctionalPoint_ι_mem k M₁ f₁ hf₁ a).mpr ha)

include e₂ in
/-- **A second vector killed by the second functional makes the germ vanish.** -/
public theorem tripleGerm_mem_of_two (a : M₁) (b : M₂) (hb : f₂ b = 0) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c ∈ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  by_contra h
  rw [tripleGerm_notMem_iff, e₂] at h
  exact h.2.1 ((linearFunctionalPoint_ι_mem k M₂ f₂ hf₂ b).mpr hb)

include e₃ in
/-- **A third vector killed by the third functional makes the germ vanish.** -/
public theorem tripleGerm_mem_of_three (a : M₁) (b : M₂) (c : M₃) (hc : f₃ c = 0) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c ∈ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  by_contra h
  rw [tripleGerm_notMem_iff, e₃] at h
  exact h.2.2 ((linearFunctionalPoint_ι_mem k M₃ f₃ hf₃ c).mpr hc)

include e₁ e₂ e₃ in
/-- **The germ escapes `𝔪ₜ · 𝒪(1,1,1)ₜ` exactly when none of the three functionals kills its
vector.** -/
public theorem tripleGerm_notMem (a : M₁) (ha : f₁ a ≠ 0) (b : M₂) (hb : f₂ b ≠ 0) (c : M₃)
    (hc : f₃ c ≠ 0) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c ∉ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  rw [tripleGerm_notMem_iff, e₁, e₂, e₃]
  exact ⟨fun h => ha ((linearFunctionalPoint_ι_mem k M₁ f₁ hf₁ a).mp h),
    fun h => hb ((linearFunctionalPoint_ι_mem k M₂ f₂ hf₂ b).mp h),
    fun h => hc ((linearFunctionalPoint_ι_mem k M₃ f₃ hf₃ c).mp h)⟩

/-! ### The germ against a reference triple -/

variable (τ : T ⟶ Spec (.of k))
  (h₁ : p₁ ≫ projectiveSpaceOfModuleToSpec k M₁ = τ)
  (h₂ : p₂ ≫ projectiveSpaceOfModuleToSpec k M₂ = τ)
  (h₃ : p₃ ≫ projectiveSpaceOfModuleToSpec k M₃ = τ)

/-- If `g` is additive, `σ`-homogeneous, and lands in `N` on the kernel of `f`, then `g a` is
congruent modulo `N` to `σ (f a / f a₀) • g a₀`. -/
private theorem sub_smul_mem_of_map_eq_zero_mem {K V R G : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Semiring R] [AddCommGroup G] [Module R G] (σ : K →+* R) (N : Submodule R G)
    (f : Module.Dual K V) (g : V → G) (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (r : K) x, g (r • x) = σ r • g x) (hker : ∀ x, f x = 0 → g x ∈ N) {a₀ : V}
    (ha₀ : f a₀ ≠ 0) (a : V) : g a - σ (f a / f a₀) • g a₀ ∈ N := by
  have key : g a = g (a - (f a / f a₀) • a₀) + σ (f a / f a₀) • g a₀ := by
    rw [← hsmul, ← hadd, sub_add_cancel]
  rw [key, add_sub_cancel_right]
  refine hker _ ?_
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ ha₀, sub_self]

include e₁ h₁ in
/-- **Normalising the first slot.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, replacing the first vector by a
reference vector `a₀` costs the scalar `f₁ a / f₁ a₀`. -/
public theorem tripleGerm_sub_smul_one_mem (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
        scalarGerm k τ t (f₁ a / f₁ a₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b c ∈
      tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t :=
  sub_smul_mem_of_map_eq_zero_mem (scalarGerm k τ t) _ f₁
    (fun x => tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t x b c)
    (fun x y => tripleGerm_add_one k M₁ M₂ M₃ p₁ p₂ p₃ t x y b c)
    (fun r x => tripleGerm_smul_one k M₁ M₂ M₃ p₁ p₂ p₃ τ h₁ t r x b c)
    (fun x hx => tripleGerm_mem_of_one k M₁ M₂ M₃ p₁ p₂ p₃ t f₁ hf₁ e₁ x hx b c) ha₀ a

include e₂ h₂ in
/-- **Normalising the second slot.** -/
public theorem tripleGerm_sub_smul_two_mem (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
        scalarGerm k τ t (f₂ b / f₂ b₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b₀ c ∈
      tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t :=
  sub_smul_mem_of_map_eq_zero_mem (scalarGerm k τ t) _ f₂
    (fun x => tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a x c)
    (fun x y => tripleGerm_add_two k M₁ M₂ M₃ p₁ p₂ p₃ t a x y c)
    (fun r x => tripleGerm_smul_two k M₁ M₂ M₃ p₁ p₂ p₃ τ h₂ t r a x c)
    (fun x hx => tripleGerm_mem_of_two k M₁ M₂ M₃ p₁ p₂ p₃ t f₂ hf₂ e₂ a x hx c) hb₀ b

include e₃ h₃ in
/-- **Normalising the third slot.** -/
public theorem tripleGerm_sub_smul_three_mem (c₀ : M₃) (hc₀ : f₃ c₀ ≠ 0) (a : M₁) (b : M₂)
    (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
        scalarGerm k τ t (f₃ c / f₃ c₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c₀ ∈
      tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t :=
  sub_smul_mem_of_map_eq_zero_mem (scalarGerm k τ t) _ f₃
    (fun x => tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b x)
    (fun x y => tripleGerm_add_three k M₁ M₂ M₃ p₁ p₂ p₃ t a b x y)
    (fun r x => tripleGerm_smul_three k M₁ M₂ M₃ p₁ p₂ p₃ τ h₃ t r a b x)
    (fun x hx => tripleGerm_mem_of_three k M₁ M₂ M₃ p₁ p₂ p₃ t f₃ hf₃ e₃ a b x hx) hc₀ c

include e₁ e₂ e₃ h₁ h₂ h₃ in
/-- **The germ formula.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, the germ at `t` of the tensor of three
tautological sections is the germ of the reference tensor times the product of the three
ratios. -/
public theorem tripleGerm_sub_smul_mem (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0) (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0)
    (c₀ : M₃) (hc₀ : f₃ c₀ ≠ 0) (a : M₁) (b : M₂) (c : M₃) :
    tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
        scalarGerm k τ t (f₁ a / f₁ a₀ * (f₂ b / f₂ b₀) * (f₃ c / f₃ c₀)) •
          tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ ∈
      tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  have hone := tripleGerm_sub_smul_one_mem k M₁ M₂ M₃ p₁ p₂ p₃ t f₁ hf₁ e₁ τ h₁ a₀ ha₀ a b c
  have htwo := tripleGerm_sub_smul_two_mem k M₁ M₂ M₃ p₁ p₂ p₃ t f₂ hf₂ e₂ τ h₂ b₀ hb₀ a₀ b c
  have hthree :=
    tripleGerm_sub_smul_three_mem k M₁ M₂ M₃ p₁ p₂ p₃ t f₃ hf₃ e₃ τ h₃ c₀ hc₀ a₀ b₀ c
  have hsum : tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
      scalarGerm k τ t (f₁ a / f₁ a₀ * (f₂ b / f₂ b₀) * (f₃ c / f₃ c₀)) •
          tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ =
      (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a b c -
          scalarGerm k τ t (f₁ a / f₁ a₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b c) +
        scalarGerm k τ t (f₁ a / f₁ a₀) •
          (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b c -
            scalarGerm k τ t (f₂ b / f₂ b₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c) +
        (scalarGerm k τ t (f₁ a / f₁ a₀) * scalarGerm k τ t (f₂ b / f₂ b₀)) •
          (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c -
            scalarGerm k τ t (f₃ c / f₃ c₀) • tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀) := by
    rw [_root_.map_mul, _root_.map_mul]
    module
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.add_mem _ hone (Submodule.smul_mem _ _ htwo))
    (Submodule.smul_mem _ _ hthree)

include e₁ e₂ e₃ h₁ h₂ h₃ in
/-- **The germ formula for a signed sum of tensors.** A `2 × 2` minor of a pair of rows is such a
sum — one term per basis vector of whichever factor the bilinear entry is expanded in, with the
two signs coming from the antisymmetrisation — so this is the germ formula for a minor section,
stated without committing to which of the three slots the summation index moves in. -/
public theorem tripleGerm_sum_sub_smul_mem {ι : Type*} [Fintype ι] (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0)
    (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0) (c₀ : M₃) (hc₀ : f₃ c₀ ≠ 0)
    (A₁ A₂ : ι → M₁) (B₁ B₂ : ι → M₂) (C₁ C₂ : ι → M₃) :
    (∑ i, (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₁ i) (B₁ i) (C₁ i) -
        tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₂ i) (B₂ i) (C₂ i))) -
        scalarGerm k τ t
            (∑ i, (f₁ (A₁ i) / f₁ a₀ * (f₂ (B₁ i) / f₂ b₀) * (f₃ (C₁ i) / f₃ c₀) -
              f₁ (A₂ i) / f₁ a₀ * (f₂ (B₂ i) / f₂ b₀) * (f₃ (C₂ i) / f₃ c₀))) •
          tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ ∈
      tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t := by
  rw [map_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hone := tripleGerm_sub_smul_mem k M₁ M₂ M₃ p₁ p₂ p₃ t f₁ hf₁ e₁ f₂ hf₂ e₂ f₃ hf₃ e₃
    τ h₁ h₂ h₃ a₀ ha₀ b₀ hb₀ c₀ hc₀ (A₁ i) (B₁ i) (C₁ i)
  have htwo := tripleGerm_sub_smul_mem k M₁ M₂ M₃ p₁ p₂ p₃ t f₁ hf₁ e₁ f₂ hf₂ e₂ f₃ hf₃ e₃
    τ h₁ h₂ h₃ a₀ ha₀ b₀ hb₀ c₀ hc₀ (A₂ i) (B₂ i) (C₂ i)
  have hrw : (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₁ i) (B₁ i) (C₁ i) -
          tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₂ i) (B₂ i) (C₂ i)) -
        scalarGerm k τ t
            (f₁ (A₁ i) / f₁ a₀ * (f₂ (B₁ i) / f₂ b₀) * (f₃ (C₁ i) / f₃ c₀) -
              f₁ (A₂ i) / f₁ a₀ * (f₂ (B₂ i) / f₂ b₀) * (f₃ (C₂ i) / f₃ c₀)) •
          tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ =
      (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₁ i) (B₁ i) (C₁ i) -
          scalarGerm k τ t (f₁ (A₁ i) / f₁ a₀ * (f₂ (B₁ i) / f₂ b₀) * (f₃ (C₁ i) / f₃ c₀)) •
            tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀) -
        (tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t (A₂ i) (B₂ i) (C₂ i) -
          scalarGerm k τ t (f₁ (A₂ i) / f₁ a₀ * (f₂ (B₂ i) / f₂ b₀) * (f₃ (C₂ i) / f₃ c₀)) •
            tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀) := by
    rw [map_sub]
    module
  rw [hrw]
  exact Submodule.sub_mem _ hone htwo

include e₁ e₂ e₃ in
/-- **The vanishing criterion.** A global section of `𝒪(1,1,1)` whose germ at `t` is, modulo
`𝔪ₜ · 𝒪(1,1,1)ₜ`, the scalar `D / (f₁ a₀ · f₂ b₀ · f₃ c₀)` times the germ of the reference tensor
is nonvanishing at `t` exactly when `D ≠ 0`. A nonzero element of `k` has unit germ, and the
reference germ escapes `𝔪ₜ · 𝒪(1,1,1)ₜ` because none of the three functionals kills its vector. -/
public theorem mem_nonvanishingLocus_iff_of_germ_sub_smul_mem (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0)
    (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0) (c₀ : M₃) (hc₀ : f₃ c₀ ≠ 0)
    (S : (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃).sections) (D : k)
    (hS : grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t)
            (S.eval (op ⊤)) -
          scalarGerm k τ t (D / (f₁ a₀ * f₂ b₀ * f₃ c₀)) •
            tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ ∈
        tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (tripleTaut k M₁ M₂ M₃ p₁ p₂ p₃) S ↔ D ≠ 0 := by
  have he := tripleGerm_notMem k M₁ M₂ M₃ p₁ p₂ p₃ t f₁ hf₁ e₁ f₂ hf₂ e₂ f₃ hf₃ e₃
    a₀ ha₀ b₀ hb₀ c₀ hc₀
  rw [mem_nonvanishingLocus_iff_notMem_tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t S]
  refine ⟨fun h hD => h ?_, fun hD => ?_⟩
  · rw [hD, zero_div, map_zero, zero_smul, sub_zero] at hS
    exact hS
  · have hden : f₁ a₀ * f₂ b₀ * f₃ c₀ ≠ 0 := mul_ne_zero (mul_ne_zero ha₀ hb₀) hc₀
    have hunit := isUnit_scalarGerm k τ t (div_ne_zero hD hden)
    have h2 : scalarGerm k τ t (D / (f₁ a₀ * f₂ b₀ * f₃ c₀)) •
        tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ ∉ tripleMax k M₁ M₂ M₃ p₁ p₂ p₃ t :=
      (Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff _ _).mpr ⟨hunit, he⟩
    have hadd := Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_add _ _ h2 hS
    have heq : scalarGerm k τ t (D / (f₁ a₀ * f₂ b₀ * f₃ c₀)) •
            tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀ +
          (grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t)
              (S.eval (op ⊤)) -
            scalarGerm k τ t (D / (f₁ a₀ * f₂ b₀ * f₃ c₀)) •
              tripleGerm k M₁ M₂ M₃ p₁ p₂ p₃ t a₀ b₀ c₀) =
        grpGerm T.toRingedSpace (tripleSh k M₁ M₂ M₃ p₁ p₂ p₃).val t ⊤ (Opens.mem_top t)
          (S.eval (op ⊤)) := by
      abel
    rwa [heq] at hadd

end Closed

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
