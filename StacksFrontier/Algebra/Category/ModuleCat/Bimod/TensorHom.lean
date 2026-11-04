module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor-hom adjunction for ordinary bimodules

For algebras `A` and `B` over a commutative ring `R`, a right `A`-module `M`, an
`(A, B)`-bimodule `N` and a right `B`-module `P`, the `B`-linear maps `M ⊗_A N → P` are
canonically the `A`-balanced bilinear maps `M × N → P`. Equivalently, tensoring with `N` is left
adjoint to the corresponding internal hom. This is the ungraded, undifferentiated case of the
tensor-hom adjunction that the chapter needs for differential graded bimodules.

## Main definitions

* `Bimod.rightLinearMaps`: the `R`-module of `R`-linear maps respecting a right action.
* `Bimod.balancedRightLinearMaps`: the `R`-module of bilinear maps balanced over the middle
  algebra and linear over the algebra on the right.

## Main results

* `Bimod.tensorHomEquiv`: the tensor-hom isomorphism.
* `Bimod.tensorHomEquiv_apply`: its forward map, evaluated on a pure tensor.

## Implementation notes

Algebras and bimodules are expressed as monoid objects and bimodule objects in `ModuleCat R`,
which keeps the statement valid for noncommutative algebras. The two hom modules are written out
as concrete submodules of spaces of `R`-linear maps, which avoids choosing an internal-hom
object in the category of bimodules; the relative tensor product is Mathlib's
`Bimod.tensorBimod`, a coequalizer, so the forward map is restriction along its projection and
the inverse is the descent of a lift along it.

## References

* [Stacks Project, Tag 09LN](https://stacks.math.columbia.edu/tag/09LN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj
open scoped TensorProduct

namespace Bimod

universe u

variable {R : Type u} [CommRing R]

/-- In `ModuleCat R`, tensoring on the left with a fixed module preserves colimits. -/
local instance moduleCatTensorLeftPreserves : ∀ X : ModuleCat.{u} R,
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  fun X ↦ (ihom.adjunction X).leftAdjoint_preservesColimits

/-- In `ModuleCat R`, tensoring on the right with a fixed module preserves colimits. -/
local instance moduleCatTensorRightPreserves : ∀ X : ModuleCat.{u} R,
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  fun X ↦ CategoryTheory.Limits.preservesColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The `R`-submodule of `R`-linear maps which respect the specified right action. -/
public def rightLinearMaps {A B : Mon (ModuleCat.{u} R)} (X Y : Bimod A B) :
    Submodule R (X.X →ₗ[R] Y.X) where
  carrier := {f | ∀ (x : X.X) (b : B.X),
    f (X.actRight.hom (x ⊗ₜ[R] b)) = Y.actRight.hom (f x ⊗ₜ[R] b)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x b
    calc
      (f + g) (X.actRight.hom (x ⊗ₜ[R] b)) =
          f (X.actRight.hom (x ⊗ₜ[R] b)) + g (X.actRight.hom (x ⊗ₜ[R] b)) := rfl
      _ = Y.actRight.hom (f x ⊗ₜ[R] b) + Y.actRight.hom (g x ⊗ₜ[R] b) :=
        congrArg₂ (fun y z ↦ y + z) (hf x b) (hg x b)
      _ = Y.actRight.hom ((f + g) x ⊗ₜ[R] b) := by
        rw [LinearMap.add_apply, TensorProduct.add_tmul, map_add]
  smul_mem' := by
    intro r f hf x b
    calc
      (r • f) (X.actRight.hom (x ⊗ₜ[R] b)) =
          r • f (X.actRight.hom (x ⊗ₜ[R] b)) := rfl
      _ = r • Y.actRight.hom (f x ⊗ₜ[R] b) := congrArg (r • ·) (hf x b)
      _ = Y.actRight.hom (r • (f x ⊗ₜ[R] b)) := (map_smul _ _ _).symm
      _ = Y.actRight.hom ((r • f) x ⊗ₜ[R] b) :=
        congrArg Y.actRight.hom (TensorProduct.smul_tmul' r (f x) b)

/-- Balanced `R`-bilinear maps from a right `A`-module and an `(A,B)`-bimodule to a right
`B`-module. -/
public def balancedRightLinearMaps {A B : Mon (ModuleCat.{u} R)}
    (M : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) A) (N : Bimod A B)
    (P : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) B) :
    Submodule R (M.X →ₗ[R] (N.X →ₗ[R] P.X)) where
  carrier := {f |
    (∀ (m : M.X) (a : A.X) (n : N.X),
      f (M.actRight.hom (m ⊗ₜ[R] a)) n = f m (N.actLeft.hom (a ⊗ₜ[R] n))) ∧
    (∀ (m : M.X) (n : N.X) (b : B.X),
      f m (N.actRight.hom (n ⊗ₜ[R] b)) = P.actRight.hom (f m n ⊗ₜ[R] b))}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine ⟨fun m a n ↦ congrArg₂ (· + ·) (hf.1 m a n) (hg.1 m a n), fun m n b ↦ ?_⟩
    calc
      ((f + g) m) (N.actRight.hom (n ⊗ₜ[R] b)) =
          (f m) (N.actRight.hom (n ⊗ₜ[R] b)) +
            (g m) (N.actRight.hom (n ⊗ₜ[R] b)) := rfl
      _ = P.actRight.hom ((f m) n ⊗ₜ[R] b) +
            P.actRight.hom ((g m) n ⊗ₜ[R] b) :=
        congrArg₂ (· + ·) (hf.2 m n b) (hg.2 m n b)
      _ = P.actRight.hom (((f + g) m) n ⊗ₜ[R] b) := by
        rw [LinearMap.add_apply, LinearMap.add_apply, TensorProduct.add_tmul, map_add]
  smul_mem' := by
    intro r f hf
    refine ⟨fun m a n ↦ congrArg (r • ·) (hf.1 m a n), fun m n b ↦ ?_⟩
    calc
      ((r • f) m) (N.actRight.hom (n ⊗ₜ[R] b)) =
          r • (f m) (N.actRight.hom (n ⊗ₜ[R] b)) := rfl
      _ = r • P.actRight.hom ((f m) n ⊗ₜ[R] b) :=
        congrArg (r • ·) (hf.2 m n b)
      _ = P.actRight.hom (r • ((f m) n ⊗ₜ[R] b)) := (map_smul _ _ _).symm
      _ = P.actRight.hom (((r • f) m) n ⊗ₜ[R] b) :=
        congrArg P.actRight.hom (TensorProduct.smul_tmul' r ((f m) n) b)

/-- **Stacks 09LN, ordinary tensor--hom.**  For a right `A`-module `M`, an `(A,B)`-bimodule
`N`, and a right `B`-module `P`, `B`-linear maps from `M ⊗_A N` to `P` are canonically the
same as `A`-balanced maps from `M` into the `B`-linear maps from `N` to `P`. -/
@[stacks 09LN "ordinary_tensor_hom", sga "4 IV 12.14" "punctual topos"]
public noncomputable def tensorHomEquiv {A B : Mon (ModuleCat.{u} R)}
    (M : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) A) (N : Bimod A B)
    (P : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) B) :
    rightLinearMaps (M.tensorBimod N) P ≃ₗ[R] balancedRightLinearMaps M N P := by
  let π := (CategoryTheory.Limits.coequalizer.π
      (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft))).hom
  let e := TensorProduct.lift.equiv (RingHom.id R) M.X N.X P.X
  let forward : rightLinearMaps (M.tensorBimod N) P →ₗ[R]
      balancedRightLinearMaps M N P :=
    { toFun := fun f =>
        ⟨e.symm (f.1.comp π), by
          constructor
          · intro m a n
            dsimp [e]
            exact congrArg f.1 (congrArg (fun k => k.hom ((m ⊗ₜ[R] a) ⊗ₜ[R] n))
              (CategoryTheory.Limits.coequalizer.condition
                (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft))))
          · intro m n b
            dsimp [e]
            exact (congrArg f.1 (congrArg (fun k => k.hom ((m ⊗ₜ[R] n) ⊗ₜ[R] b))
              (Bimod.TensorBimod.π_tensor_id_actRight M N))).symm.trans
                (f.2 (π (m ⊗ₜ[R] n)) b)⟩
      map_add' := by intros; ext z x; rfl
      map_smul' := by intros; ext z x; rfl }
  let condition (g : balancedRightLinearMaps M N P) :
      (M.actRight ▷ N.X) ≫ ModuleCat.ofHom (TensorProduct.lift g.1) =
        ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft)) ≫
          ModuleCat.ofHom (TensorProduct.lift g.1) := by
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul ma n =>
      induction ma using TensorProduct.induction_on with
      | zero => simp
      | tmul m a => exact g.2.1 m a n
      | add x y hx hy => simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
    | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  let q (g : balancedRightLinearMaps M N P) :=
    CategoryTheory.Limits.coequalizer.desc
      (ModuleCat.ofHom (TensorProduct.lift g.1)) (condition g)
  let backward : balancedRightLinearMaps M N P →ₗ[R]
      rightLinearMaps (M.tensorBimod N) P :=
    { toFun := fun g =>
        ⟨(q g).hom, by
          intro x b
          obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
            (CategoryTheory.Limits.coequalizer.π
              (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft)))).mp inferInstance x
          have qπ : ∀ w : M.X ⊗[R] N.X, (q g).hom (π w) = TensorProduct.lift g.1 w :=
            fun w => congrArg (fun k => k.hom w)
              (CategoryTheory.Limits.coequalizer.π_desc
                (ModuleCat.ofHom (TensorProduct.lift g.1)) (condition g))
          have h := congrArg (fun k => k.hom (z ⊗ₜ[R] b))
            (Bimod.TensorBimod.π_tensor_id_actRight M N)
          change (M.tensorBimod N).actRight.hom (π z ⊗ₜ[R] b) =
            π (((α_ M.X N.X B.X).hom ≫ (M.X ◁ N.actRight)).hom (z ⊗ₜ[R] b)) at h
          change (q g).hom ((M.tensorBimod N).actRight.hom (π z ⊗ₜ[R] b)) =
            P.actRight.hom ((q g).hom (π z) ⊗ₜ[R] b)
          rw [h, qπ, qπ]
          clear h
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul m n =>
            change TensorProduct.lift g.1 (m ⊗ₜ[R] N.actRight.hom (n ⊗ₜ[R] b)) =
              P.actRight.hom (TensorProduct.lift g.1 (m ⊗ₜ[R] n) ⊗ₜ[R] b)
            exact g.2.2 m n b
          | add u v hu hv =>
            rw [TensorProduct.add_tmul, map_add, map_add, map_add, TensorProduct.add_tmul,
              map_add]
            exact congrArg₂ (· + ·) hu hv⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg ModuleCat.Hom.hom (CategoryTheory.Limits.coequalizer.hom_ext
          (k := q (x + y)) (l := q x + q y) (by
            rw [CategoryTheory.Limits.coequalizer.π_desc,
              Preadditive.comp_add, CategoryTheory.Limits.coequalizer.π_desc,
              CategoryTheory.Limits.coequalizer.π_desc]
            apply ModuleCat.hom_ext
            ext z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul m n => rfl
            | add x y hx hy => simp_all; abel))
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact congrArg ModuleCat.Hom.hom (CategoryTheory.Limits.coequalizer.hom_ext
          (k := q (r • x)) (l := r • q x) (by
            rw [CategoryTheory.Limits.coequalizer.π_desc,
              Linear.comp_smul, CategoryTheory.Limits.coequalizer.π_desc]
            apply ModuleCat.hom_ext
            ext z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul m n => rfl
            | add x y hx hy => simp_all)) }
  exact LinearEquiv.ofBijective forward (by
    have hleft : Function.LeftInverse backward forward := by
      intro f
      apply Subtype.ext
      exact congrArg ModuleCat.Hom.hom (CategoryTheory.Limits.coequalizer.hom_ext
        (k := q (forward f)) (l := ModuleCat.ofHom f.1) (by
          rw [CategoryTheory.Limits.coequalizer.π_desc]
          apply ModuleCat.hom_ext
          ext z
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul m n => rfl
          | add x y hx hy => simp_all))
    have hright : Function.RightInverse backward forward := by
      intro g
      apply Subtype.ext
      ext m n
      exact congrArg (fun k => k.hom (m ⊗ₜ[R] n))
        (CategoryTheory.Limits.coequalizer.π_desc
          (ModuleCat.ofHom (TensorProduct.lift g.1)) (condition g))
    exact ⟨hleft.injective, hright.surjective⟩)

/-- The forward tensor-hom correspondence is evaluation on pure tensors. -/
@[stacks 09LN "ordinary_tensor_hom"]
public theorem tensorHomEquiv_apply {A B : Mon (ModuleCat.{u} R)}
    (M : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) A) (N : Bimod A B)
    (P : Bimod (𝟙_ (Mon (ModuleCat.{u} R))) B)
    (f : rightLinearMaps (M.tensorBimod N) P) (m : M.X) (n : N.X) :
    (tensorHomEquiv M N P f).1 m n =
      f.1 (CategoryTheory.Limits.coequalizer.π
        (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft)) |>.hom
        (m ⊗ₜ[R] n)) :=
  rfl

end Bimod
