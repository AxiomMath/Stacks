module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Invariants of a group as a limit of coefficient functors

Let `Λ` be a commutative ring and `G` a group, and write `Λ[G]` for the group ring.  The functor
of invariants `M ↦ M^G`, from `Λ[G]`-modules to `Λ`-modules, is coextension of scalars along the
augmentation `ε : Λ[G] → Λ`, that is `M ↦ Hom_{Λ[G]}(Λ, M)`.  This file shows that it is the
limit, over the one-object category of `G`, of restriction of scalars along `Λ → Λ[G]` with `G`
acting: a `Λ[G]`-linear map `Λ → M` is the same as its value at `1`, a `G`-invariant element.

## Main definitions

* `Stacks.EtaleCohomology.groupRingAugmentation`: the augmentation `ε : Λ[G] →+* Λ`.
* `Stacks.EtaleCohomology.groupRingActionNatTrans`: the action of `g ∈ G` as an endomorphism of
  restriction of scalars along `Λ → Λ[G]`.
* `Stacks.EtaleCohomology.groupRingActionDiagram`: the diagram, indexed by the one-object
  category of `G`, of restriction of scalars with `G` acting.
* `Stacks.EtaleCohomology.groupRingInvariantsCone`: evaluation at `1`, a cone from coextension of
  scalars along `ε` over that diagram.

## Main results

* `Stacks.EtaleCohomology.isLimitGroupRingInvariantsCone`: that cone is a limit cone at every
  module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

variable (Λ : Type u) [CommRing Λ] (G : Type) [Group G]

/-- The augmentation `ε : Λ[G] →+* Λ`, sending every group element to `1`. -/
abbrev groupRingAugmentation : MonoidAlgebra Λ G →+* Λ :=
  (MonoidAlgebra.lift Λ Λ G 1).toRingHom

/-- The augmentation sends `c • g` to `c`. -/
@[simp]
lemma groupRingAugmentation_single (g : G) (c : Λ) :
    groupRingAugmentation Λ G (MonoidAlgebra.single g c) = c := by
  simp [MonoidAlgebra.lift_single]

/-- The inclusion of the scalars `Λ →+* Λ[G]`. -/
abbrev groupRingScalars : Λ →+* MonoidAlgebra Λ G :=
  MonoidAlgebra.singleOneRingHom

/-- The augmentation is a retraction of the inclusion of the scalars. -/
lemma groupRingAugmentation_scalars (c : Λ) :
    groupRingAugmentation Λ G (groupRingScalars Λ G c) = c :=
  groupRingAugmentation_single Λ G 1 c

/-- The scalars `Λ` are central in `Λ[G]`. -/
lemma groupRingScalars_commute (c : Λ) (a : MonoidAlgebra Λ G) :
    groupRingScalars Λ G c * a = a * groupRingScalars Λ G c := by
  change MonoidAlgebra.single 1 c * a = a * MonoidAlgebra.single 1 c
  ext x
  rw [MonoidAlgebra.coeff_single_one_mul, MonoidAlgebra.coeff_mul_single_one, mul_comm]

/-- **The action of `g ∈ G`** as an endomorphism of restriction of scalars along `Λ → Λ[G]`:
multiplication by the group element, which is `Λ`-linear because `Λ` is central. -/
def groupRingActionNatTrans (g : G) :
    ModuleCat.restrictScalars.{v} (groupRingScalars Λ G) ⟶
      ModuleCat.restrictScalars.{v} (groupRingScalars Λ G) where
  app M := ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)).obj M)
      (Y := (ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)).obj M)
    ({ toFun := fun m => MonoidAlgebra.single g (1 : Λ) • m
       map_add' := fun x y => smul_add _ x y
       map_smul' := fun c m => by
         change MonoidAlgebra.single g (1 : Λ) • (groupRingScalars Λ G c • (show M from m)) =
           groupRingScalars Λ G c • (MonoidAlgebra.single g (1 : Λ) • (show M from m))
         rw [smul_smul, smul_smul, groupRingScalars_commute] } :
      (ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)).obj M →ₗ[Λ]
        (ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)).obj M)
  naturality M N f := by
    ext m
    exact (f.hom.map_smul _ _).symm

/-- The action of `g` on `M` is multiplication by the group element `g ∈ Λ[G]`. -/
lemma groupRingActionNatTrans_app_apply (g : G) (M : ModuleCat.{v} (MonoidAlgebra Λ G))
    (m : (ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)).obj M) :
    ((groupRingActionNatTrans Λ G g).app M).hom m =
      MonoidAlgebra.single g (1 : Λ) • m :=
  rfl

/-- **The diagram of restriction of scalars with `G` acting**, indexed by the one-object
category of `G`. -/
def groupRingActionDiagram :
    SingleObj G ⥤ (ModuleCat.{v} (MonoidAlgebra Λ G) ⥤ ModuleCat.{v} Λ) where
  obj _ := ModuleCat.restrictScalars.{v} (groupRingScalars Λ G)
  map g := groupRingActionNatTrans Λ G g
  map_id _ := by
    ext M m
    exact one_smul (MonoidAlgebra Λ G) m
  map_comp f g := by
    ext M m
    change MonoidAlgebra.single (g * f) (1 : Λ) • m =
      MonoidAlgebra.single g (1 : Λ) • MonoidAlgebra.single f (1 : Λ) • m
    rw [smul_smul, MonoidAlgebra.single_mul_single, mul_one]

variable {Λ G} in
/-- On an element fixed by every group element, the group ring acts through the
augmentation. -/
lemma smul_eq_augmentation_smul_of_invariant {M : Type*} [AddCommGroup M]
    [Module (MonoidAlgebra Λ G) M] {m : M}
    (hm : ∀ g : G, MonoidAlgebra.single g (1 : Λ) • m = m) (a : MonoidAlgebra Λ G) :
    a • m = groupRingScalars Λ G (groupRingAugmentation Λ G a) • m := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, ha, hb, map_add, map_add, add_smul]
  | single g c =>
    have : MonoidAlgebra.single g c = groupRingScalars Λ G c * MonoidAlgebra.single g 1 := by
      change MonoidAlgebra.single g c = MonoidAlgebra.single 1 c * MonoidAlgebra.single g 1
      rw [MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [groupRingAugmentation_single, this, mul_smul, hm]

/-- **Evaluation at `1`**, from coextension of scalars along the augmentation to restriction of
scalars along `Λ → Λ[G]`: a `Λ[G]`-linear map `Λ → M` goes to its value at `1`. -/
def groupRingInvariantsEval :
    (ModuleCat.coextendScalars (groupRingAugmentation Λ G) :
      ModuleCat.{max v u} (MonoidAlgebra Λ G) ⥤ ModuleCat.{max v u} Λ) ⟶
      ModuleCat.restrictScalars (groupRingScalars Λ G) where
  app M := ModuleCat.ofHom
      (X := (ModuleCat.coextendScalars (groupRingAugmentation Λ G)).obj M)
      (Y := (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj M)
    { toFun := fun φ => φ (1 : Λ)
      map_add' := fun _ _ => rfl
      map_smul' := fun c φ => by
        have h := (ModuleCat.CoextendScalars.equiv _ M φ).map_smul (groupRingScalars Λ G c)
          (1 : Λ)
        refine (congrArg (ModuleCat.CoextendScalars.equiv _ M φ) ?_).trans h
        change (1 : Λ) * c = groupRingAugmentation Λ G (groupRingScalars Λ G c) * 1
        rw [groupRingAugmentation_scalars, one_mul, mul_one] }
  naturality _ _ _ := rfl

/-- **Evaluation at `1` is a cone** over the diagram of restriction of scalars with `G` acting:
the value at `1` of a `Λ[G]`-linear map `Λ → M` is fixed by `G`, because `G` acts trivially on
`Λ`. -/
def groupRingInvariantsCone :
    (Functor.const (SingleObj G)).obj
        (ModuleCat.coextendScalars (groupRingAugmentation Λ G) :
          ModuleCat.{max v u} (MonoidAlgebra Λ G) ⥤ ModuleCat.{max v u} Λ) ⟶
      groupRingActionDiagram.{max v u} Λ G where
  app _ := groupRingInvariantsEval.{v} Λ G
  naturality _ _ g := by
    ext M φ
    have h := (ModuleCat.CoextendScalars.equiv _ M φ).map_smul
      (MonoidAlgebra.single g (1 : Λ)) (1 : Λ)
    refine Eq.trans ?_ h
    refine congrArg (ModuleCat.CoextendScalars.equiv _ M φ) ?_
    change (1 : Λ) = groupRingAugmentation Λ G (MonoidAlgebra.single g 1) * 1
    rw [groupRingAugmentation_single, mul_one]

variable {Λ G} in
/-- The `Λ[G]`-linear map `Λ → M` with value `m` at `1`, for `m` fixed by `G`. -/
def groupRingInvariantsLinearMap (M : ModuleCat.{max v u} (MonoidAlgebra Λ G)) (m : M)
    (hm : ∀ g : G, MonoidAlgebra.single g (1 : Λ) • m = m) :
    (ModuleCat.restrictScalars (groupRingAugmentation Λ G)).obj (ModuleCat.of Λ Λ)
      →ₗ[MonoidAlgebra Λ G] M where
  toFun x := groupRingScalars Λ G (show Λ from x) • m
  map_add' x y := by
    change groupRingScalars Λ G ((show Λ from x) + (show Λ from y)) • m = _
    rw [map_add, add_smul]
  map_smul' a x := by
    change groupRingScalars Λ G (groupRingAugmentation Λ G a * (show Λ from x)) • m =
      a • groupRingScalars Λ G (show Λ from x) • m
    rw [smul_smul, ← groupRingScalars_commute, mul_smul,
      smul_eq_augmentation_smul_of_invariant hm a, smul_smul, ← map_mul, mul_comm]

variable {Λ G} in
/-- A `Λ[G]`-linear map `Λ → M` is determined by its value at `1`. -/
lemma coextendScalars_augmentation_apply (M : ModuleCat.{max v u} (MonoidAlgebra Λ G))
    (φ : (ModuleCat.coextendScalars (groupRingAugmentation Λ G)).obj M) (x : Λ) :
    φ x = groupRingScalars Λ G x • φ (1 : Λ) := by
  have h := (ModuleCat.CoextendScalars.equiv _ M φ).map_smul (groupRingScalars Λ G x) (1 : Λ)
  refine Eq.trans (congrArg (ModuleCat.CoextendScalars.equiv _ M φ) ?_) h
  change x = groupRingAugmentation Λ G (groupRingScalars Λ G x) * 1
  rw [groupRingAugmentation_scalars, mul_one]

/-- **Invariants are the limit of restriction of scalars with `G` acting**: evaluation at `1`
exhibits `Hom_{Λ[G]}(Λ, M)` as the limit, over the one-object category of `G`, of `M` viewed as
a `Λ`-module with `G` acting on it. -/
def isLimitGroupRingInvariantsCone (M : ModuleCat.{max v u} (MonoidAlgebra Λ G)) :
    IsLimit (((evaluation _ _).obj M).mapCone (Cone.mk _ (groupRingInvariantsCone.{v} Λ G))) where
  lift s := ModuleCat.ofHom (X := s.pt)
      (Y := (ModuleCat.coextendScalars (groupRingAugmentation Λ G)).obj M)
    { toFun := fun n => (ModuleCat.CoextendScalars.equiv _ M).symm
        (groupRingInvariantsLinearMap M ((s.π.app (SingleObj.star G)).hom n) fun g =>
          congrArg (fun f => ModuleCat.Hom.hom f n) (s.w g))
      map_add' := fun x y => by
        ext z
        change groupRingScalars Λ G (show Λ from z) •
            (show M from (s.π.app (SingleObj.star G)).hom (x + y)) =
          groupRingScalars Λ G (show Λ from z) • (show M from (s.π.app (SingleObj.star G)).hom x) +
            groupRingScalars Λ G (show Λ from z) •
              (show M from (s.π.app (SingleObj.star G)).hom y)
        rw [map_add]
        exact smul_add _ (show M from (s.π.app (SingleObj.star G)).hom x)
          (show M from (s.π.app (SingleObj.star G)).hom y)
      map_smul' := fun c x => by
        ext z
        change groupRingScalars Λ G (show Λ from z) •
            (show M from (s.π.app (SingleObj.star G)).hom (c • x)) =
          groupRingScalars Λ G ((show Λ from z) * c) •
            (show M from (s.π.app (SingleObj.star G)).hom x)
        rw [map_smul, map_mul, mul_smul]
        rfl }
  fac s j := by
    cases j
    ext n
    change groupRingScalars Λ G 1 • (show M from (s.π.app (SingleObj.star G)).hom n) = _
    rw [map_one, one_smul]
    rfl
  uniq s m hm := by
    refine ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
    apply ModuleCat.CoextendScalars.ext
    refine LinearMap.ext fun z => ?_
    have h := congrArg (fun f => ModuleCat.Hom.hom f n) (hm (SingleObj.star G))
    change (show (ModuleCat.coextendScalars (groupRingAugmentation Λ G)).obj M from m.hom n) z =
      groupRingScalars Λ G (show Λ from z) • (show M from (s.π.app (SingleObj.star G)).hom n)
    exact (coextendScalars_augmentation_apply M (m.hom n) z).trans
      (congrArg (fun y : M => groupRingScalars Λ G (show Λ from z) • y) h)

end Stacks.EtaleCohomology

end
