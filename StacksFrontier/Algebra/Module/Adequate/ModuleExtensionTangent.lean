module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.Algebra.Module.Adequate.Tangent

/-!
# The tangent functor of an extension-of-scalars functor

For an `A`-module `M`, the module-valued functor `B ↦ B ⊗[A] M` has tangent module
`N ⊗[A] M` at a pair `(B, N)`: the square-zero extension `B[N]` splits as `B ⊕ N` over
`A`, so `B[N] ⊗[A] M` splits as `(B ⊗[A] M) ⊕ (N ⊗[A] M)` and the kernel of the
augmentation is the second summand.  Consequently the tangent functor of `B ↦ B ⊗[A] M`
is right exact in the module variable, because `- ⊗[A] M` is.

## Main results

* `AdequateFunctor.moduleExtensionTangentEquiv`: the identification
  `N ⊗[A] M ≃ₗ[B] T(B ↦ B ⊗[A] M)(B, N)`.
* `AdequateFunctor.hasRightExactTangentFunctor_moduleExtension`: the functor
  `B ↦ B ⊗[A] M` has property `(*)` of Tag 06ZF.
* `AdequateFunctor.moduleExtensionRightExactTangentFunctor`: the resulting
  `RightExactTangentFunctor`, the first inhabitant of that structure.

## References

* [Stacks Project, Tag 06Z8](https://stacks.math.columbia.edu/tag/06Z8)
* [Stacks Project, Tag 06ZF](https://stacks.math.columbia.edu/tag/06ZF)
-/

@[expose] public section

namespace AdequateFunctor

open CategoryTheory

universe u v w

section Splitting

variable (A : Type u) [CommRing A]

/-- The `A`-linear map on modules underlying a morphism of algebra-module pairs. -/
def pairLinear {X Y : AlgebraModulePair.{max u v} A} (f : X ⟶ Y) :
    X.module →ₗ[A] Y.module where
  toFun := f.linear
  map_add' := map_add _
  map_smul' a x := by
    change f.linear (algebraMap A X.algebra a • x) = algebraMap A Y.algebra a • f.linear x
    rw [f.linear.map_smulₛₗ]
    exact congrArg (· • f.linear x) (f.base.commutes a)

/-- The map on square-zero extensions induced by a morphism of algebra-module pairs,
spelled as an `A`-linear map between trivial square-zero extensions. -/
noncomputable def pairSquareZero {X Y : AlgebraModulePair.{max u v} A} (f : X ⟶ Y) :
    TrivSqZeroExt X.algebra X.module →ₗ[A] TrivSqZeroExt Y.algebra Y.module :=
  (squareZeroMap A f).toLinearMap

/-- The inclusion of the square-zero ideal, as an `A`-linear map. -/
noncomputable def pairInr (X : AlgebraModulePair.{max u v} A) :
    X.module →ₗ[A] TrivSqZeroExt X.algebra X.module :=
  (TrivSqZeroExt.inrHom X.algebra X.module).restrictScalars A

/-- The projection onto the square-zero ideal, as an `A`-linear map. -/
def pairSnd (X : AlgebraModulePair.{max u v} A) :
    TrivSqZeroExt X.algebra X.module →ₗ[A] X.module where
  toFun := TrivSqZeroExt.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The zero section of the square-zero extension, as an `A`-linear map. -/
def pairInl (X : AlgebraModulePair.{max u v} A) :
    X.algebra →ₗ[A] TrivSqZeroExt X.algebra X.module :=
  (TrivSqZeroExt.inlAlgHom A X.algebra X.module).toLinearMap

/-- The augmentation of the square-zero extension, as an `A`-linear map. -/
def pairFst (X : AlgebraModulePair.{max u v} A) :
    TrivSqZeroExt X.algebra X.module →ₗ[A] X.algebra :=
  (TrivSqZeroExt.fstHom A X.algebra X.module).toLinearMap

/-- Projecting onto the square-zero ideal after including it is the identity. -/
lemma pairSnd_comp_pairInr (X : AlgebraModulePair.{max u v} A) :
    (pairSnd A X).comp (pairInr A X) = LinearMap.id :=
  LinearMap.ext fun _ => rfl

/-- The map on square-zero extensions induced by `f` restricts on the square-zero ideal to
the module map of `f`. -/
lemma pairSquareZero_comp_pairInr {X Y : AlgebraModulePair.{max u v} A} (f : X ⟶ Y) :
    (pairSquareZero A f).comp (pairInr A X) = (pairInr A Y).comp (pairLinear A f) := by
  ext x
  · exact map_zero f.base
  · rfl

/-- Every element of `B[N]` is the sum of its ideal part and its zero-section part. -/
lemma pairInr_pairSnd_add_pairInl_pairFst
    (X : AlgebraModulePair.{max u v} A) (x : TrivSqZeroExt X.algebra X.module) :
    pairInr A X (pairSnd A X x) + pairInl A X (pairFst A X x) = x :=
  TrivSqZeroExt.ext (zero_add x.fst) (add_zero x.snd)

end Splitting

section Tangent

variable (A : Type u) [CommRing A] (M : ModuleCat.{w} A)

/-- The inclusion `N ⊗[A] M → B[N] ⊗[A] M` of the tangent part. -/
noncomputable def pairTensorInr (X : AlgebraModulePair.{max u v} A) :
    TensorProduct A X.module M →ₗ[A]
      TensorProduct A (TrivSqZeroExt X.algebra X.module) M :=
  LinearMap.rTensor (M : Type w) (pairInr A X)

/-- The projection `B[N] ⊗[A] M → N ⊗[A] M` onto the tangent part. -/
noncomputable def pairTensorSnd (X : AlgebraModulePair.{max u v} A) :
    TensorProduct A (TrivSqZeroExt X.algebra X.module) M →ₗ[A]
      TensorProduct A X.module M :=
  LinearMap.rTensor (M : Type w) (pairSnd A X)

/-- The augmentation `B[N] ⊗[A] M → B ⊗[A] M`. -/
noncomputable def pairTensorFst (X : AlgebraModulePair.{max u v} A) :
    TensorProduct A (TrivSqZeroExt X.algebra X.module) M →ₗ[A]
      TensorProduct A X.algebra M :=
  LinearMap.rTensor (M : Type w) (pairFst A X)

/-- The augmentation `B[N] ⊗[A] M → B ⊗[A] M` vanishes on the tangent part. -/
lemma pairTensorFst_pairTensorInr (X : AlgebraModulePair.{max u v} A)
    (t : TensorProduct A X.module M) :
    pairTensorFst A M X (pairTensorInr A M X t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul n m =>
    rw [pairTensorInr, pairTensorFst, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    exact TensorProduct.zero_tmul _ _
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]

/-- Projecting onto the tangent part after including it is the identity of `N ⊗[A] M`. -/
lemma pairTensorSnd_pairTensorInr (X : AlgebraModulePair.{max u v} A)
    (t : TensorProduct A X.module M) :
    pairTensorSnd A M X (pairTensorInr A M X t) = t := by
  rw [pairTensorSnd, pairTensorInr, ← LinearMap.rTensor_comp_apply,
    pairSnd_comp_pairInr, LinearMap.rTensor_id, LinearMap.id_apply]

/-- Every element of `B[N] ⊗[A] M` is the sum of its tangent part and the image of its
augmentation under the zero section. -/
lemma pairTensorInr_pairTensorSnd_add (X : AlgebraModulePair.{max u v} A)
    (x : TensorProduct A (TrivSqZeroExt X.algebra X.module) M) :
    pairTensorInr A M X (pairTensorSnd A M X x) +
      LinearMap.rTensor (M : Type w) (pairInl A X) (pairTensorFst A M X x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul y m =>
    rw [pairTensorSnd, pairTensorInr, pairTensorFst, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      ← TensorProduct.add_tmul, pairInr_pairSnd_add_pairInl_pairFst]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, map_add, add_add_add_comm, h₁, h₂]

/-- An element of `B[N] ⊗[A] M` in the kernel of the augmentation equals its tangent part. -/
lemma pairTensorInr_pairTensorSnd (X : AlgebraModulePair.{max u v} A)
    (x : TensorProduct A (TrivSqZeroExt X.algebra X.module) M)
    (hx : pairTensorFst A M X x = 0) :
    pairTensorInr A M X (pairTensorSnd A M X x) = x := by
  have h := pairTensorInr_pairTensorSnd_add A M X x
  rwa [hx, map_zero, add_zero] at h

/-- The inclusion of the tangent part commutes with the maps induced by a morphism of pairs. -/
lemma pairTensorInr_naturality {X Y : AlgebraModulePair.{max u v} A} (f : X ⟶ Y)
    (t : TensorProduct A X.module M) :
    LinearMap.rTensor (M : Type w) (pairSquareZero A f) (pairTensorInr A M X t) =
      pairTensorInr A M Y (LinearMap.rTensor (M : Type w) (pairLinear A f) t) := by
  rw [pairTensorInr, pairTensorInr, ← LinearMap.rTensor_comp_apply,
    ← LinearMap.rTensor_comp_apply, pairSquareZero_comp_pairInr]

/-- The inclusion of the tangent part intertwines the `B`-action on `N ⊗[A] M` with the action
of the zero section `inl b` on `B[N] ⊗[A] M`. -/
lemma pairTensorInr_smul (X : AlgebraModulePair.{max u v} A) (b : X.algebra)
    (t : TensorProduct A X.module M) :
    pairTensorInr A M X (b • t) =
      (TrivSqZeroExt.inl b : TrivSqZeroExt X.algebra X.module) • pairTensorInr A M X t := by
  induction t using TensorProduct.inductionOn with
  | tmul n m =>
    rw [TensorProduct.smul_tmul', pairTensorInr, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, TensorProduct.smul_tmul']
    exact congrArg (· ⊗ₜ[A] m) (TrivSqZeroExt.inl_mul_inr b n).symm
  | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]

/-- The tangent module of `B ↦ B ⊗[A] M` at `(B, N)` is `N ⊗[A] M`.  This identification is
the untagged remark of the Stacks project preceding Tag 06ZA. -/
noncomputable def moduleExtensionTangentEquiv (X : AlgebraModulePair.{max u v} A) :
    TensorProduct A X.module M ≃ₗ[X.algebra]
      tangentModule A (moduleExtension.{w, v} A M) X where
  toFun t := ⟨pairTensorInr A M X t, pairTensorFst_pairTensorInr A M X t⟩
  map_add' t₁ t₂ := Subtype.ext (map_add (pairTensorInr A M X) t₁ t₂)
  map_smul' b t := Subtype.ext (pairTensorInr_smul A M X b t)
  invFun x := pairTensorSnd A M X x.1
  left_inv t := pairTensorSnd_pairTensorInr A M X t
  right_inv x := Subtype.ext (pairTensorInr_pairTensorSnd A M X x.1 x.2)

/-- The identification `moduleExtensionTangentEquiv` is natural in the pair `(B, N)`. -/
lemma moduleExtensionTangentEquiv_naturality {X Y : AlgebraModulePair.{max u v} A}
    (f : X ⟶ Y) (t : TensorProduct A X.module M) :
    (tangentFunctor A (moduleExtension.{w, v} A M)).map f
        (moduleExtensionTangentEquiv A M X t) =
      moduleExtensionTangentEquiv A M Y
        (LinearMap.rTensor (M : Type w) (pairLinear A f) t) :=
  Subtype.ext
    (((tangentFunctor A (moduleExtension.{w, v} A M)).map_coe f
      (moduleExtensionTangentEquiv A M X t)).trans (pairTensorInr_naturality A M f t))

end Tangent

section RightExact

variable (A : Type u) [CommRing A] (M : ModuleCat.{w} A)

/-- The functor `B ↦ B ⊗[A] M` has property `(*)` of Tag 06ZF: at every `A`-algebra its
tangent functor sends a short exact sequence of modules to a right exact sequence.  This is
the base case for property `(*)`, the untagged remark preceding Tag 06ZA. -/
theorem hasRightExactTangentFunctor_moduleExtension :
    HasRightExactTangentFunctor A (moduleExtension.{w, v} A M) := by
  intro B _ _ S hS
  have hgsurj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hexact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  set fixed := fixedAlgebraModuleFunctor A B
  set F := moduleExtension.{w, v} A M
  have key : ∀ {M₁ M₂ : ModuleCat.{max u v} B} (f : M₁ ⟶ M₂)
      (t : TensorProduct A (fixed.obj M₁).module M),
      ConcreteCategory.hom ((tangentFunctorAt A F B).map f)
          (moduleExtensionTangentEquiv A M (fixed.obj M₁) t) =
        moduleExtensionTangentEquiv A M (fixed.obj M₂)
          (LinearMap.rTensor (M : Type w) (pairLinear A (fixed.map f)) t) :=
    fun f t => moduleExtensionTangentEquiv_naturality A M (fixed.map f) t
  have hrsurj : Function.Surjective
      (LinearMap.rTensor (M : Type w) (pairLinear A (fixed.map S.g))) :=
    LinearMap.rTensor_surjective _ hgsurj
  have hrexact : Function.Exact
      (LinearMap.rTensor (M : Type w) (pairLinear A (fixed.map S.f)))
      (LinearMap.rTensor (M : Type w) (pairLinear A (fixed.map S.g))) :=
    rTensor_exact _ hexact hgsurj
  have hsurj : Function.Surjective
      (ConcreteCategory.hom ((tangentFunctorAt A F B).map S.g)) := by
    intro z
    obtain ⟨t, ht⟩ := (moduleExtensionTangentEquiv A M (fixed.obj S.X₃)).surjective z
    obtain ⟨s, hs⟩ := hrsurj t
    exact ⟨moduleExtensionTangentEquiv A M (fixed.obj S.X₂) s, by rw [key S.g s, hs, ht]⟩
  refine ⟨?_, (AddCommGrpCat.epi_iff_surjective _).mpr hsurj⟩
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨t, ht⟩ := (moduleExtensionTangentEquiv A M (fixed.obj S.X₂)).surjective y
  have hzero : LinearMap.rTensor (M : Type w) (pairLinear A (fixed.map S.g)) t = 0 := by
    apply (moduleExtensionTangentEquiv A M (fixed.obj S.X₃)).injective
    rw [← key S.g t, ht, map_zero]
    exact hy
  obtain ⟨s, hs⟩ := (hrexact t).mp hzero
  refine ⟨moduleExtensionTangentEquiv A M (fixed.obj S.X₁) s, ?_⟩
  change ConcreteCategory.hom ((tangentFunctorAt A F B).map S.f) _ = y
  rw [key S.f s, hs, ht]

/-- The extension-of-scalars functor `B ↦ B ⊗[A] M`, packaged as a right exact tangent
functor situation.  Every result of Tags 06ZB and 06ZF stated for a
`RightExactTangentFunctor` applies to it. -/
noncomputable def moduleExtensionRightExactTangentFunctor :
    RightExactTangentFunctor.{u, max u v, max u v w} where
  A := A
  F := moduleExtension.{w, v} A M
  rightExact := hasRightExactTangentFunctor_moduleExtension.{u, v, w} A M

end RightExact

end AdequateFunctor
