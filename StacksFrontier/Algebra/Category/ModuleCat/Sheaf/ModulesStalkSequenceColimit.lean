module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The stalk of an `ℕ`-indexed colimit of `𝒪_X`-modules, over the local ring at the point

`Stacks.ModuleSkyscraper.modulesStalkFunctor X x` takes an `𝒪_X`-module to its stalk at `x`
as a module over `𝒪_{X, x}`, the `CommRingCat`-valued stalk of the structure sheaf, and
`Stacks.ModuleSkyscraper.modulesStalkSkyAdjunction` exhibits it as a **left adjoint** of the
skyscraper functor.  A left adjoint preserves every colimit, so that adjunction already contains
[Stacks, Tag 01AH] over this stalk — the one whose scalars are the local ring `𝒪_{X, x}`, which
is the ring the reflexive powers of [Stacks, Tag 0EBN] and their multiplication-by-`s` maps are
linear over.

This file reads off what a consumer of an `ℕ`-indexed colimit needs: that the stalks of the
stages are jointly surjective onto the stalk of the colimit, and that an element of a stage
which dies in the colimit is killed by finitely many transition maps.  `ℕ` is filtered, so both
come from the concrete description of a filtered colimit of modules.

The sibling file `StacksFrontier/Topology/Sheaves/Modules/Colimits.lean` proves Tag 01AH for the
stalk functor valued over the *`RingCat`*-valued stalk, and
`AlgebraicGeometry.SheafOfModules.exists_stalkMap_eq` there is the same statement in that
spelling.  The distinction is the one recorded in `PullbackStalkColimit.lean`: only the
`CommRingCat` stalk is the ring `𝒪_{X, x}` that the rest of this material is stated over, which
is why both are here.

## Main results

* `Stacks.ModuleSkyscraper.modulesStalkFunctor_preservesColimits`: the stalk functor over
  `𝒪_{X, x}` preserves colimits.
* `Stacks.ModuleSkyscraper.isColimitModulesStalkMapCocone`: hence the stalk of a colimit of an
  `ℕ`-indexed diagram of `𝒪_X`-modules is a colimit of the stalks.
* `Stacks.ModuleSkyscraper.exists_stalkMapLinear_eq` and
  `exists_modulesStalkFunctor_map_eq`: joint surjectivity, element by element.
* `Stacks.ModuleSkyscraper.exists_map_eq_zero_of_stalkMapLinear_eq_zero` and
  `exists_map_eq_zero_of_modulesStalkFunctor_map_eq_zero`: an element of a stage killed in the
  colimit is killed by a transition map.
* `Stacks.ModuleSkyscraper.modulesStalkFunctor_map_add_zero` and
  `modulesStalkFunctor_map_add_succ`: the `k`-step map of the diagram at the stalk, recursively,
  which is what identifies it with a composite of `k` successor steps.

## Implementation notes

Each element-level statement comes in two spellings.  One is
`AlgebraicGeometry.stalkMapLinear`, the stalk of a morphism as a linear map over `𝒪_{X, x}`,
because that is the spelling
`Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerStalkMap` is defined in; the other is
the action of `modulesStalkFunctor` on morphisms.  The two are equal by `rfl`, which is
`modulesStalkFunctor_map_hom_apply`; the crossing is isolated there.

The spelling matters for more than taste: the module structures on a stalk reached through
`stalkMapLinear` have to be rebuilt from the presheaves at every occurrence, and a goal mixing
them with `X.Modules` is not type-correct at `implicit` transparency, so `rw` refuses it.
Working through `modulesStalkFunctor` keeps the rewriting inside `ModuleCat`, which is why the
recursion lemmas for the `k`-step map are stated there and for an arbitrary diagram.

The shape `ℕ` lives in `Type 0` while Tag 01AH is stated for shapes in `Type u`, so
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` is needed; nothing is narrowed, since
`max 0 u = u`.  The same happens for the forgetful functor to types, where the available
instance is for filtered shapes in `Type u`.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.ModuleSkyscraper

variable (X : Scheme.{u}) (x : X)

/-! ### The action of the stalk functor on morphisms -/

/-- **The stalk functor over `𝒪_{X, x}` acts on morphisms by `AlgebraicGeometry.stalkMapLinear`.**
Both are the stalk of the underlying morphism of presheaves of abelian groups, equipped with the
scalar action of the `CommRingCat`-valued stalk, so this is a definitional identity; it is
recorded once, here, and is what lets the statements below be read in either spelling. -/
theorem modulesStalkFunctor_map_hom_apply {M N : X.Modules} (φ : M ⟶ N)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    ((modulesStalkFunctor X x).map φ).hom m =
      AlgebraicGeometry.stalkMapLinear M.val N.val φ.val x m := rfl

/-- `AlgebraicGeometry.stalkMapLinear` of an identity is the identity. -/
theorem stalkMapLinear_id_apply (M : X.Modules)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    AlgebraicGeometry.stalkMapLinear M.val M.val (𝟙 M : M ⟶ M).val x m = m :=
  (modulesStalkFunctor_map_hom_apply X x (𝟙 M) m).symm.trans
    (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((modulesStalkFunctor X x).map_id M)) m)

/-- The stalk functor over `𝒪_{X, x}` takes an identity to the identity, pointwise. -/
theorem modulesStalkFunctor_map_id_apply (M : X.Modules)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    ((modulesStalkFunctor X x).map (𝟙 M)).hom m = m :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((modulesStalkFunctor X x).map_id M)) m

/-- The stalk functor over `𝒪_{X, x}` takes a composite to the composite, pointwise. -/
theorem modulesStalkFunctor_map_comp_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    ((modulesStalkFunctor X x).map (φ ≫ ψ)).hom m =
      ((modulesStalkFunctor X x).map ψ).hom (((modulesStalkFunctor X x).map φ).hom m) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((modulesStalkFunctor X x).map_comp φ ψ)) m

/-- `AlgebraicGeometry.stalkMapLinear` of a composite is the composite. -/
theorem stalkMapLinear_comp_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    AlgebraicGeometry.stalkMapLinear M.val P.val (φ ≫ ψ).val x m =
      AlgebraicGeometry.stalkMapLinear N.val P.val ψ.val x
        (AlgebraicGeometry.stalkMapLinear M.val N.val φ.val x m) := by
  rw [← modulesStalkFunctor_map_hom_apply X x (φ ≫ ψ) m, Functor.map_comp]
  rfl

/-! ### `ℕ`-indexed colimits -/

section Sequence

variable {D : CategoryTheory.Functor ℕ X.Modules}

/-- **The stalk functor over `𝒪_{X, x}` preserves colimits**, being a left adjoint of the
skyscraper functor by `modulesStalkSkyAdjunction`.  This is [Stacks, Tag 01AH] over the
`CommRingCat`-valued stalk. -/
theorem modulesStalkFunctor_preservesColimits : PreservesColimits (modulesStalkFunctor X x) :=
  (modulesStalkSkyAdjunction X x).leftAdjoint_preservesColimits

/-- **The stalk of an `ℕ`-indexed colimit of `𝒪_X`-modules is the colimit of the stalks.** -/
def isColimitModulesStalkMapCocone {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((modulesStalkFunctor X x).mapCocone c) := by
  letI : PreservesColimits (modulesStalkFunctor X x) :=
    modulesStalkFunctor_preservesColimits X x
  letI : PreservesColimitsOfSize.{0, 0} (modulesStalkFunctor X x) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact isColimitOfPreserves _ hc

/-- The forgetful functor to types preserves the colimit of an `ℕ`-indexed diagram of
`𝒪_{X, x}`-modules: `ℕ` is filtered, and the forgetful functor from modules preserves filtered
colimits of shapes in `Type u`, hence of the shape `ℕ`, which lives in `Type 0`. -/
instance preservesColimit_comp_modulesStalkFunctor_forget :
    PreservesColimit (D ⋙ modulesStalkFunctor X x)
      (forget (ModuleCat.{u} ↑(X.presheaf.stalk x))) := by
  let : PreservesFilteredColimitsOfSize.{0, 0}
      (forget (ModuleCat.{u} ↑(X.presheaf.stalk x))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  infer_instance

/-- **Joint surjectivity of the stalk maps into the stalk of an `ℕ`-indexed colimit.**  Every
element of the stalk of the colimit is the image of an element of the stalk of some stage. -/
theorem exists_stalkMapLinear_eq {c : Cocone D} (hc : IsColimit c)
    (a : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) c.pt.val.presheaf x)) :
    ∃ (n : ℕ) (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x)),
      AlgebraicGeometry.stalkMapLinear (D.obj n).val c.pt.val (c.ι.app n).val x m = a := by
  obtain ⟨n, m, hm⟩ := Concrete.isColimit_exists_rep (D ⋙ modulesStalkFunctor X x)
    (isColimitModulesStalkMapCocone X x hc) a
  exact ⟨n, m, (modulesStalkFunctor_map_hom_apply X x (c.ι.app n) m).symm.trans hm⟩

/-- **The zero-step map of an `ℕ`-indexed diagram acts as the identity on stalks.** -/
theorem modulesStalkFunctor_map_add_zero (D : CategoryTheory.Functor ℕ X.Modules) (n : ℕ)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x)) :
    ((modulesStalkFunctor X x).map (D.map (homOfLE (Nat.le_add_right n 0)))).hom m = m := by
  rw [show (homOfLE (Nat.le_add_right n 0) : (n : ℕ) ⟶ n + 0) = 𝟙 n from Subsingleton.elim _ _,
    D.map_id, modulesStalkFunctor_map_id_apply]

/-- **The `(k + 1)`-step map of an `ℕ`-indexed diagram is the `k`-step map followed by one
successor step**, on stalks. -/
theorem modulesStalkFunctor_map_add_succ (D : CategoryTheory.Functor ℕ X.Modules) (n k : ℕ)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x)) :
    ((modulesStalkFunctor X x).map (D.map (homOfLE (Nat.le_add_right n (k + 1))))).hom m =
      ((modulesStalkFunctor X x).map
          (D.map (homOfLE (Nat.le_add_right (n + k) 1)))).hom
        (((modulesStalkFunctor X x).map (D.map (homOfLE (Nat.le_add_right n k)))).hom m) := by
  rw [show (homOfLE (Nat.le_add_right n (k + 1)) : (n : ℕ) ⟶ n + (k + 1)) =
      homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_add_right (n + k) 1) from
    Subsingleton.elim _ _, D.map_comp, modulesStalkFunctor_map_comp_apply]

/-- `exists_stalkMapLinear_eq` in the `modulesStalkFunctor` spelling, which is the cheap one to
compute with: no module structure has to be reconstructed from the presheaves. -/
theorem exists_modulesStalkFunctor_map_eq {c : Cocone D} (hc : IsColimit c)
    (a : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) c.pt.val.presheaf x)) :
    ∃ (n : ℕ) (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x)),
      ((modulesStalkFunctor X x).map (c.ι.app n)).hom m = a := by
  obtain ⟨n, m, hm⟩ := Concrete.isColimit_exists_rep (D ⋙ modulesStalkFunctor X x)
    (isColimitModulesStalkMapCocone X x hc) a
  exact ⟨n, m, hm⟩

/-- `exists_map_eq_zero_of_stalkMapLinear_eq_zero` in the `modulesStalkFunctor` spelling. -/
theorem exists_map_eq_zero_of_modulesStalkFunctor_map_eq_zero {c : Cocone D} (hc : IsColimit c)
    (n : ℕ) (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x))
    (h : ((modulesStalkFunctor X x).map (c.ι.app n)).hom m = 0) :
    ∃ k : ℕ, ((modulesStalkFunctor X x).map
      (D.map (homOfLE (Nat.le_add_right n k)))).hom m = 0 := by
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq.{u}
    (D ⋙ modulesStalkFunctor X x) (isColimitModulesStalkMapCocone X x hc) m
    (0 : (D ⋙ modulesStalkFunctor X x).obj n) (h.trans (map_zero _).symm)
  obtain ⟨k, rfl⟩ := Nat.le.dest (leOfHom f)
  obtain rfl : f = homOfLE (Nat.le_add_right n k) := Subsingleton.elim _ _
  exact ⟨k, hfg.trans (map_zero _)⟩

/-- **An element of a stage killed in the stalk of the colimit is killed by a transition map.**
The colimit over `ℕ` is filtered, so two elements with the same image agree after a transition;
applied to `m` and `0` this says that `D.map (n ⟶ n + k)` kills `m` for some `k`. -/
theorem exists_map_eq_zero_of_stalkMapLinear_eq_zero {c : Cocone D} (hc : IsColimit c) (n : ℕ)
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj n).val.presheaf x))
    (h : AlgebraicGeometry.stalkMapLinear (D.obj n).val c.pt.val (c.ι.app n).val x m = 0) :
    ∃ k : ℕ, AlgebraicGeometry.stalkMapLinear (D.obj n).val (D.obj (n + k)).val
      (D.map (homOfLE (Nat.le_add_right n k))).val x m = 0 := by
  obtain ⟨k, hk⟩ := exists_map_eq_zero_of_modulesStalkFunctor_map_eq_zero X x hc n m
    ((modulesStalkFunctor_map_hom_apply X x (c.ι.app n) m).trans h)
  exact ⟨k, (modulesStalkFunctor_map_hom_apply X x
    (D.map (homOfLE (Nat.le_add_right n k))) m).symm.trans hk⟩

end Sequence

end Stacks.ModuleSkyscraper

end

end
