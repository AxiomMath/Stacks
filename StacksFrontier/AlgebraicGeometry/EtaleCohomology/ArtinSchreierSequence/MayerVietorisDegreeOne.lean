module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CoverExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# `H¹` of a scheme covered by two opens, and its restriction along a morphism

Let `X` be a scheme covered by two open subschemes `U` and `V`, and let
`S : 0 ⟶ j_{U ∩ V!} ℤ ⟶ j_{U!} ℤ ⊕ j_{V!} ℤ ⟶ ℤ ⟶ 0` be the Mayer–Vietoris sequence of the
constant sheaf (`Stacks.EtaleCohomology.shortExact_coverShortComplex`). For an abelian sheaf `F`
on `X_étale` its connecting map gives

`Hom(j_{U!} ℤ ⊕ j_{V!} ℤ, F) ⟶ Hom(j_{U ∩ V!} ℤ, F) ⟶ H¹(X, F) ⟶ Ext¹(j_{U!} ℤ ⊕ j_{V!} ℤ, F)`,

exact at the middle two terms. For a morphism `g : Y ⟶ X` the inverse image of `S` is again
short exact, and restriction of `H¹` along `g` is computed on the connecting maps.

## Main definitions

* `Stacks.ArtinSchreier.coverSequence`: the Mayer–Vietoris short complex of the constant sheaf.
* `Stacks.ArtinSchreier.coverDelta`: its connecting map `Hom(S.X₁, F) ⟶ H¹(X, F)`.
* `Stacks.ArtinSchreier.coverDeltaInverseImage`: the connecting map of the inverse image of `S`
  along `g : Y ⟶ X`, landing in `H¹(Y, -)`.

## Main results

* `Stacks.ArtinSchreier.exists_coverDelta_eq`,
  `Stacks.ArtinSchreier.exists_comp_eq_of_coverDelta_eq_zero`
  and their counterparts on `Y`: the two exactness statements.
* `Stacks.ArtinSchreier.sheafH_map_etaleCohomologyRestrictionMap_coverDelta`: restriction along
  `g` followed by a map `g^{-1} F ⟶ F'` on `Y` carries `δ s` to the connecting map on `Y` of the
  composite `g^{-1} s ⟶ F'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

variable {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)

/-- **The Mayer–Vietoris short complex of the constant sheaf `ℤ` for a cover of `X` by two opens**:
`j_{U ∩ V!} ℤ ⟶ j_{U!} ℤ ⊕ j_{V!} ℤ ⟶ ℤ`. -/
abbrev coverSequence : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk ((coverToBiprod.{u, 0} U V).app (etaleConstantInt X))
    ((coverFromBiprod.{u, 0} U V).app (etaleConstantInt X))
    (coverToBiprod_comp_coverFromBiprod.{u, 0} U V (etaleConstantInt X))

include hUV in
/-- The Mayer–Vietoris sequence of `ℤ` is short exact. -/
theorem coverSequence_shortExact : (coverSequence U V).ShortExact :=
  shortExact_coverShortComplex.{u, 0} U V hUV (etaleConstantInt X)

/-- A class pulled back along `S.g` that vanishes is the connecting class of some map. -/
private theorem exists_extClass_comp_mk₀_eq {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) {F : C} (y : Ext S.X₃ F 1)
    (hy : (Ext.mk₀ S.g).comp y (zero_add 1) = 0) :
    ∃ s : S.X₁ ⟶ F, hS.extClass.comp (Ext.mk₀ s) (add_zero 1) = y := by
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ hS F y hy (show 1 + 0 = 1 from rfl)
  obtain ⟨s, rfl⟩ := Ext.mk₀_bijective _ _ |>.2 x₁
  exact ⟨s, hx₁⟩

/-- If the connecting class of `s : S.X₁ ⟶ F` vanishes, then `s` factors through `S.f`. -/
private theorem exists_comp_eq_of_extClass_comp_mk₀_eq_zero {C : Type*} [Category* C] [Abelian C]
    [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) {F : C} (s : S.X₁ ⟶ F)
    (hs : hS.extClass.comp (Ext.mk₀ s) (add_zero 1) = 0) : ∃ t, S.f ≫ t = s := by
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS F (Ext.mk₀ s)
    (show 1 + 0 = 1 from rfl) hs
  obtain ⟨t, rfl⟩ := Ext.mk₀_bijective _ _ |>.2 x₂
  refine ⟨t, (Ext.mk₀_bijective _ _).1 ?_⟩
  rw [← Ext.mk₀_comp_mk₀]
  exact hx₂

section Delta

include hUV

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **The Mayer–Vietoris connecting map** `Hom(j_{U ∩ V!} ℤ, F) ⟶ H¹(X, F)`. -/
def coverDelta : ((coverSequence U V).X₁ ⟶ F) →+ Sheaf.H.{w} F 1 where
  toFun s := (coverSequence_shortExact U V hUV).extClass.comp (Ext.mk₀ s) (add_zero 1)
  map_zero' := by rw [Ext.mk₀_zero, Ext.comp_zero]
  map_add' a b := by rw [Ext.mk₀_add, Ext.comp_add]

/-- The Mayer–Vietoris connecting map is composition with the class of the sequence. -/
theorem coverDelta_apply (s : (coverSequence U V).X₁ ⟶ F) :
    coverDelta U V hUV F s = (coverSequence_shortExact U V hUV).extClass.comp (Ext.mk₀ s)
      (add_zero 1) :=
  rfl

/-- **Every class of `H¹(X, F)` is a Mayer–Vietoris coboundary** when
`Ext¹(j_{U!} ℤ ⊕ j_{V!} ℤ, F) = 0`. -/
theorem exists_coverDelta_eq (h : Subsingleton (Ext.{w} (coverSequence U V).X₂ F 1))
    (y : Sheaf.H.{w} F 1) : ∃ s, coverDelta U V hUV F s = y := by
  obtain ⟨s, hs⟩ := exists_extClass_comp_mk₀_eq (coverSequence_shortExact U V hUV) y (h.elim _ _)
  exact ⟨s, (coverDelta_apply U V hUV F s).trans hs⟩

/-- **A Mayer–Vietoris coboundary vanishes only on restrictions**: if `δ s = 0` then `s` factors
through `j_{U ∩ V!} ℤ ⟶ j_{U!} ℤ ⊕ j_{V!} ℤ`. -/
theorem exists_comp_eq_of_coverDelta_eq_zero (s : (coverSequence U V).X₁ ⟶ F)
    (hs : coverDelta U V hUV F s = 0) : ∃ t, (coverSequence U V).f ≫ t = s := by
  rw [coverDelta_apply] at hs
  exact exists_comp_eq_of_extClass_comp_mk₀_eq_zero (coverSequence_shortExact U V hUV) s hs

end Delta

/-! ### The inverse image along a morphism -/

section InverseImage

include hUV

variable {Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The inverse image of the Mayer–Vietoris sequence is short exact. -/
theorem coverSequence_map_shortExact :
    ((coverSequence U V).map (etaleAbelianInverseImage.{u, 0} g)).ShortExact :=
  (coverSequence_shortExact U V hUV).map_of_exact _

/-- **The connecting map of the inverse image of the Mayer–Vietoris sequence**, landing in
`H¹(Y, F')` through the identification `g^{-1} ℤ_X ≅ ℤ_Y`. -/
def coverDeltaInverseImage :
    ((etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₁ ⟶ F') →+ Sheaf.H.{w} F' 1 where
  toFun t := (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
      (AddCommGrpCat.of (ULift ℤ))).inv).comp
      ((coverSequence_map_shortExact U V hUV g).extClass.comp (Ext.mk₀ t) (add_zero 1))
      (zero_add 1)
  map_zero' := by rw [Ext.mk₀_zero, Ext.comp_zero, Ext.comp_zero]
  map_add' a b := by rw [Ext.mk₀_add, Ext.comp_add, Ext.comp_add]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The connecting map on `Y` is composition with the class of the inverse image of the
sequence, after the identification `ℤ_Y ≅ g^{-1} ℤ_X`. -/
theorem coverDeltaInverseImage_apply
    (t : (etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₁ ⟶ F') :
    coverDeltaInverseImage U V hUV g F' t =
      (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
        ((coverSequence_map_shortExact U V hUV g).extClass.comp (Ext.mk₀ t) (add_zero 1))
        (zero_add 1) :=
  rfl

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **Every class of `H¹(Y, F')` is a coboundary of the inverse image of the Mayer–Vietoris
sequence** when `Ext¹(g^{-1}(j_{U!} ℤ ⊕ j_{V!} ℤ), F') = 0`. -/
theorem exists_coverDeltaInverseImage_eq
    (h : Subsingleton (Ext.{w} ((etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₂)
      F' 1))
    (y : Sheaf.H.{w} F' 1) : ∃ t, coverDeltaInverseImage U V hUV g F' t = y := by
  let ι := (etaleAbelianInverseImageConstantIso.{u, 0} g).app (AddCommGrpCat.of (ULift ℤ))
  let y' : Ext.{w} ((etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₃) F' 1 :=
    (Ext.mk₀ ι.hom).comp y (zero_add 1)
  obtain ⟨t, hx₁⟩ := exists_extClass_comp_mk₀_eq (coverSequence_map_shortExact U V hUV g) y'
    (h.elim _ _)
  refine ⟨t, ?_⟩
  rw [coverDeltaInverseImage_apply, hx₁, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id, Ext.mk₀_id_comp]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **A coboundary of the inverse image of the Mayer–Vietoris sequence vanishes only on
restrictions.** -/
theorem exists_comp_eq_of_coverDeltaInverseImage_eq_zero
    (t : (etaleAbelianInverseImage.{u, 0} g).obj (coverSequence U V).X₁ ⟶ F')
    (ht : coverDeltaInverseImage U V hUV g F' t = 0) :
    ∃ r, (etaleAbelianInverseImage.{u, 0} g).map (coverSequence U V).f ≫ r = t := by
  let ι := (etaleAbelianInverseImageConstantIso.{u, 0} g).app (AddCommGrpCat.of (ULift ℤ))
  rw [coverDeltaInverseImage_apply] at ht
  have ht' : (coverSequence_map_shortExact U V hUV g).extClass.comp (Ext.mk₀ t) (add_zero 1) =
      0 := by
    have := congrArg (fun z => (Ext.mk₀ ι.hom).comp z (zero_add 1)) ht
    simp only [Ext.comp_zero] at this
    rwa [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by omega), Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id,
      Ext.mk₀_id_comp] at this
  exact exists_comp_eq_of_extClass_comp_mk₀_eq_zero (coverSequence_map_shortExact U V hUV g) t ht'

/-- **Restriction of `H¹` along `g` on Mayer–Vietoris coboundaries.** For `s : j_{U ∩ V!} ℤ ⟶ F`
and a morphism `θ : g^{-1} F ⟶ F'` on `Y`, restricting `δ s` along `g` and applying `θ` is the
coboundary on `Y` of `g^{-1} s ≫ θ`. -/
theorem sheafH_map_etaleCohomologyRestrictionMap_coverDelta
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (θ : (etaleAbelianInverseImage.{u, 0} g).obj F ⟶ F') (s : (coverSequence U V).X₁ ⟶ F) :
    Sheaf.H.map θ 1 (etaleCohomologyRestrictionMap.{u, 0, w} g F 1 (coverDelta U V hUV F s)) =
      coverDeltaInverseImage U V hUV g F'
        ((etaleAbelianInverseImage.{u, 0} g).map s ≫ θ) := by
  rw [coverDeltaInverseImage_apply, Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply,
    coverDelta_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]

end InverseImage

end Stacks.ArtinSchreier

end
