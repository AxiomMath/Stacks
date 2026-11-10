module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The telescope of an `ℕ`-indexed diagram

Let `X : ℕ ⥤ C` be a diagram in a preadditive category with countable coproducts, and write
`s : ∐ₖ X k ⟶ ∐ₖ X k` for the map sending the summand `X k` to the summand `X (k + 1)` by the
transition map. The *telescope* of `X` is the sequence

`∐ₖ X k --(1 - s)--> ∐ₖ X k --> colim X --> 0`.

This file proves that the second map is a cokernel of the first whenever its target is a colimit
of `X`, in any preadditive category, and that `1 - s` is a monomorphism for a diagram of modules
over a ring and for a diagram of sheaves of modules on a topological space. Together these make
the telescope a short exact sequence in the category of sheaves of modules on a space.

## Main definitions

* `CategoryTheory.Limits.telescopeShift`: the shift `s`.
* `CategoryTheory.Limits.telescopeDiff`: the difference `1 - s`.

## Main results

* `CategoryTheory.Limits.isColimitTelescope`: the canonical map from `∐ₖ X k` to the point of a
  colimit cocone is a cokernel of `1 - s`.
* `CategoryTheory.Limits.mono_telescopeDiff_moduleCat`: `1 - s` is injective for modules.
* `AlgebraicGeometry.SheafOfModules.mono_telescopeDiff`: `1 - s` is a monomorphism of sheaves of
  modules on a space.
* `AlgebraicGeometry.SheafOfModules.shortExact_telescope`: the telescope of a colimit cocone of
  sheaves of modules on a space is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace CategoryTheory.Limits

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproductsOfShape ℕ C]
  (X : ℕ ⥤ C)

/-- The shift of the telescope: the summand `X k` of `∐ₖ X k` is sent to the summand
`X (k + 1)` by the transition map. -/
def telescopeShift : ∐ X.obj ⟶ ∐ X.obj :=
  Sigma.desc fun k => X.map (homOfLE (Nat.le_succ k)) ≫ Sigma.ι X.obj (k + 1)

omit [Preadditive C] in
/-- The shift `s` restricted to the summand `X k` is the transition map `X k ⟶ X (k + 1)`
followed by the inclusion of the summand `X (k + 1)`. -/
@[reassoc (attr := simp)]
theorem ι_telescopeShift (k : ℕ) :
    Sigma.ι X.obj k ≫ telescopeShift X = X.map (homOfLE (Nat.le_succ k)) ≫ Sigma.ι X.obj (k + 1) :=
  Sigma.ι_comp_desc _ _

/-- The difference `1 - s` of the telescope. -/
def telescopeDiff : ∐ X.obj ⟶ ∐ X.obj := 𝟙 _ - telescopeShift X

/-- The difference `1 - s` restricted to the summand `X k` is the inclusion of `X k` minus the
transition map `X k ⟶ X (k + 1)` followed by the inclusion of `X (k + 1)`. -/
@[reassoc]
theorem ι_telescopeDiff (k : ℕ) :
    Sigma.ι X.obj k ≫ telescopeDiff X =
      Sigma.ι X.obj k - X.map (homOfLE (Nat.le_succ k)) ≫ Sigma.ι X.obj (k + 1) := by
  simp [telescopeDiff, Preadditive.comp_sub]

variable {X}

/-- The map out of `∐ₖ X k` induced by a cocone. -/
def telescopeπ (c : Cocone X) : ∐ X.obj ⟶ c.pt :=
  Sigma.desc fun k => (c.ι.app k : X.obj k ⟶ c.pt)

omit [Preadditive C] in
/-- The map `telescopeπ c` restricted to the summand `X k` is the cocone leg `c.ι.app k`. -/
@[reassoc (attr := simp)]
theorem ι_telescopeπ (c : Cocone X) (k : ℕ) : Sigma.ι X.obj k ≫ telescopeπ c = c.ι.app k :=
  Sigma.ι_comp_desc _ _

/-- The map out of `∐ₖ X k` induced by a cocone kills `1 - s`. -/
@[reassoc (attr := simp)]
theorem telescopeDiff_desc (c : Cocone X) :
    telescopeDiff X ≫ telescopeπ c = 0 := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [ι_telescopeDiff_assoc, Preadditive.sub_comp, Category.assoc, ι_telescopeπ,
    ι_telescopeπ, c.w, sub_self, comp_zero]

/-- A map out of `∐ₖ X k` killing `1 - s` gives a cocone on `X`. -/
def coconeOfTelescope {W : C} (g : ∐ X.obj ⟶ W) (hg : telescopeDiff X ≫ g = 0) : Cocone X where
  pt := W
  ι :=
    { app := fun k => Sigma.ι X.obj k ≫ g
      naturality := by
        have hstep : ∀ k : ℕ, X.map (homOfLE (Nat.le_succ k)) ≫ Sigma.ι X.obj (k + 1) ≫ g =
            Sigma.ι X.obj k ≫ g := by
          intro k
          have := congrArg (fun z => Sigma.ι X.obj k ≫ z) hg
          simp only [comp_zero] at this
          rw [← Category.assoc, ι_telescopeDiff, Preadditive.sub_comp, sub_eq_zero] at this
          rw [this, Category.assoc]
        intro i j f
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        induction d with
        | zero =>
          obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
          simp
        | succ d ih =>
          have hf : f = homOfLE (Nat.le_add_right i d) ≫ homOfLE (Nat.le_succ (i + d)) :=
            Subsingleton.elim _ _
          rw [hf, X.map_comp, Category.assoc,
            show X.map (homOfLE (Nat.le_succ (i + d))) ≫ Sigma.ι X.obj (i + (d + 1)) ≫ g =
              Sigma.ι X.obj (i + d) ≫ g from hstep (i + d)]
          exact ih _ }

/-- **The telescope of a colimit.** If `c` is a colimit cocone of `X`, the induced map
`∐ₖ X k ⟶ c.pt` is a cokernel of `1 - s`. -/
def isColimitTelescope {c : Cocone X} (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (telescopeπ c) (telescopeDiff_desc c)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} g hg => (hc.desc (coconeOfTelescope g hg) : c.pt ⟶ W))
    (fun {W} g hg => Sigma.hom_ext _ _ fun k => by
      have h1 := ι_telescopeπ_assoc c k (hc.desc (coconeOfTelescope g hg) : c.pt ⟶ W)
      have h2 := hc.fac (coconeOfTelescope g hg) k
      exact h1.trans h2)
    (fun {W} g hg m hm => hc.hom_ext fun k => by
      have h2 := hc.fac (coconeOfTelescope g hg) k
      refine Eq.trans ?_ h2.symm
      change c.ι.app k ≫ m = Sigma.ι X.obj k ≫ g
      rw [← hm, ι_telescopeπ_assoc])

end Preadditive


section Modules

variable {R : Type u} [Ring R] (X : ℕ ⥤ ModuleCat.{v} R)

open DirectSum

open DirectSum in
/-- The shift of the telescope on the direct sum. -/
def directSumTelescopeShift : (⨁ k, X.obj k) →ₗ[R] (⨁ k, X.obj k) :=
  DirectSum.toModule R ℕ _ fun k =>
    (DirectSum.lof R ℕ (fun k => X.obj k) (k + 1)).comp (X.map (homOfLE (Nat.le_succ k))).hom

/-- The shift of the telescope sends the summand `X k` into the summand `X (k + 1)` by the
transition map. -/
private theorem directSumTelescopeShift_lof (k : ℕ) (m : X.obj k) :
    directSumTelescopeShift X (DirectSum.lof R ℕ (fun k => X.obj k) k m) =
      DirectSum.lof R ℕ (fun k => X.obj k) (k + 1) ((X.map (homOfLE (Nat.le_succ k))).hom m) :=
  DirectSum.toModule_lof R _ _

/-- The component in degree `0` of the shift of any element of the direct sum vanishes. -/
theorem directSumTelescopeShift_apply_zero (z : ⨁ k, X.obj k) :
    directSumTelescopeShift X z 0 = 0 := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k m =>
    rw [← DirectSum.lof_eq_of R, directSumTelescopeShift_lof, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  | add a b ha hb => simp [ha, hb]

/-- The component in degree `j + 1` of the shift of `z` is the image of the component `z j`
under the transition map `X j ⟶ X (j + 1)`. -/
theorem directSumTelescopeShift_apply_succ (z : ⨁ k, X.obj k) (j : ℕ) :
    directSumTelescopeShift X z (j + 1) = (X.map (homOfLE (Nat.le_succ j))).hom (z j) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k m =>
    rw [← DirectSum.lof_eq_of R, directSumTelescopeShift_lof]
    by_cases hjk : j = k
    · subst hjk
      rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (by omega),
        DirectSum.of_eq_of_ne _ _ _ hjk, map_zero]
  | add a b ha hb => simp [ha, hb]

/-- `1 - s` is injective on the direct sum `⨁ k, X k`. -/
theorem injective_directSumTelescopeShift_sub :
    Function.Injective (LinearMap.id - directSumTelescopeShift X :
      (⨁ k, X.obj k) →ₗ[R] (⨁ k, X.obj k)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hfix : directSumTelescopeShift X z = z := by
    have := sub_eq_zero.mp hz
    exact this.symm
  have hcomp : ∀ j : ℕ, z j = 0 := by
    intro j
    induction j with
    | zero => rw [← hfix, directSumTelescopeShift_apply_zero]
    | succ j ih => rw [← hfix, directSumTelescopeShift_apply_succ, ih, map_zero]
  exact DFinsupp.ext hcomp

/-- For a diagram of modules, the shift `s` of the telescope corresponds to
`directSumTelescopeShift X` under the isomorphism `ModuleCat.coprodIsoDirectSum` between the
coproduct and the direct sum. -/
theorem telescopeShift_eq_moduleCat :
    telescopeShift X = (ModuleCat.coprodIsoDirectSum X.obj).hom ≫
      ModuleCat.ofHom (directSumTelescopeShift X) ≫ (ModuleCat.coprodIsoDirectSum X.obj).inv := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [ι_telescopeShift, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom,
    ← Category.assoc, ← ModuleCat.ofHom_comp]
  have : directSumTelescopeShift X ∘ₗ DirectSum.lof R ℕ (fun i => X.obj i) k =
      (DirectSum.lof R ℕ (fun k => X.obj k) (k + 1)).comp
        (X.map (homOfLE (Nat.le_succ k))).hom :=
    LinearMap.ext (directSumTelescopeShift_lof X k)
  rw [this, ModuleCat.ofHom_comp, Category.assoc, ModuleCat.lof_coprodIsoDirectSum_inv]
  rfl

/-- **`1 - s` is a monomorphism for a diagram of modules.** -/
theorem mono_telescopeDiff_moduleCat : Mono (telescopeDiff X) := by
  have h : telescopeDiff X = (ModuleCat.coprodIsoDirectSum X.obj).hom ≫
      ModuleCat.ofHom (LinearMap.id - directSumTelescopeShift X) ≫
        (ModuleCat.coprodIsoDirectSum X.obj).inv := by
    rw [telescopeDiff, telescopeShift_eq_moduleCat]
    rw [show ModuleCat.ofHom (LinearMap.id - directSumTelescopeShift X) =
      𝟙 _ - ModuleCat.ofHom (directSumTelescopeShift X) from rfl]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Iso.hom_inv_id]
  rw [h]
  have : Mono (ModuleCat.ofHom (LinearMap.id - directSumTelescopeShift X)) :=
    (ModuleCat.mono_iff_injective _).2 (injective_directSumTelescopeShift_sub X)
  infer_instance

end Modules

section Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproductsOfShape ℕ C]
  {D : Type*} [Category* D] [Preadditive D] [HasCoproductsOfShape ℕ D]
  (X : ℕ ⥤ C) (F : C ⥤ D) [F.Additive] [PreservesColimitsOfShape (Discrete ℕ) F]

/-- An additive functor preserving countable coproducts carries `1 - s` to `1 - s`. -/
theorem map_telescopeDiff :
    F.map (telescopeDiff X) = (PreservesCoproduct.iso F X.obj).hom ≫
      telescopeDiff (X ⋙ F) ≫ (PreservesCoproduct.iso F X.obj).inv := by
  rw [← cancel_epi (PreservesCoproduct.iso F X.obj).inv, Iso.inv_hom_id_assoc]
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc, ← F.map_comp, ι_telescopeDiff,
    show Sigma.ι (fun j ↦ F.obj (X.obj j)) k ≫ telescopeDiff (X ⋙ F) ≫ sigmaComparison F X.obj =
      (Sigma.ι (X ⋙ F).obj k ≫ telescopeDiff (X ⋙ F)) ≫ sigmaComparison F X.obj from
      (Category.assoc _ _ _).symm, ι_telescopeDiff, F.map_sub, Preadditive.sub_comp, F.map_comp,
    Category.assoc]
  exact congrArg₂ (· - ·) (ι_comp_sigmaComparison F X.obj k).symm
    (congrArg (fun z => F.map (X.map (homOfLE (Nat.le_succ k))) ≫ z)
      (ι_comp_sigmaComparison F X.obj (k + 1)).symm)

/-- `1 - s` is a monomorphism as soon as some additive, coproduct-preserving functor which
reflects monomorphisms carries it to one. -/
theorem mono_telescopeDiff_of_map (h : Mono (telescopeDiff (X ⋙ F))) [F.ReflectsMonomorphisms] :
    Mono (telescopeDiff X) := by
  refine F.mono_of_mono_map ?_
  rw [map_telescopeDiff]
  infer_instance

end Functor

end CategoryTheory.Limits

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  {O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (D : ℕ ⥤ _root_.SheafOfModules.{u} O)

/-- **`1 - s` is a monomorphism of sheaves of modules on a space.** -/
theorem mono_telescopeDiff : Mono (telescopeDiff D) := by
  rw [mono_iff_injective_stalkMap]
  intro x
  let : PreservesColimits (stalkFunctor O x) := stalkFunctor_preservesColimits O x
  let : PreservesColimitsOfShape (Discrete ℕ) (stalkFunctor O x) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have : (stalkFunctor O x).PreservesZeroMorphisms :=
    inferInstance
  have : (stalkFunctor O x).Additive := Functor.additive_of_preserves_binary_products _
  rw [← ModuleCat.mono_iff_injective]
  change Mono ((stalkFunctor O x).map (telescopeDiff D))
  rw [map_telescopeDiff]
  have := mono_telescopeDiff_moduleCat (D ⋙ stalkFunctor O x)
  infer_instance

/-- **The telescope of a colimit of sheaves of modules on a space is short exact.** For a
colimit cocone `c` of `D : ℕ ⥤ Mod(O)`,
`0 ⟶ ∐ₖ D k --(1 - s)--> ∐ₖ D k ⟶ c.pt ⟶ 0` is a short exact sequence. -/
theorem shortExact_telescope {c : Cocone D} (hc : IsColimit c) :
    (ShortComplex.mk (telescopeDiff D) (telescopeπ c) (telescopeDiff_desc c)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (isColimitTelescope hc)
  mono_f := mono_telescopeDiff D
  epi_g := Limits.epi_of_isColimit_cofork (isColimitTelescope hc)

end AlgebraicGeometry.SheafOfModules

end
