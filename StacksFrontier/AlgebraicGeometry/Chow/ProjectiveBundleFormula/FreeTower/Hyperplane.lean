module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The coordinate hyperplane of projective space over the integers

Let `ℙᵐ_ℤ = Proj ℤ[T₀, …, Tₘ]` with its twisting sheaf `𝒪(1)`. By [Stacks, Tag 01NE] a morphism
into `ℙ^{m+1}_ℤ` is an invertible module with `m + 2` generating global sections. The family
`(0, T₀, …, Tₘ)` of sections of `𝒪_{ℙᵐ}(1)` generates, so it classifies a morphism

  `hyperplane m : ℙᵐ_ℤ ⟶ ℙ^{m+1}_ℤ`

pulling `T₀` back to `0` and `T_{k+1}` back to `T_k`. This file shows that `hyperplane m` is the
zero scheme `V(T₀)` of the first coordinate: it factors through the closed immersion of the zero
scheme by an isomorphism, under which the restriction of `𝒪(1)` is `𝒪(1)`.

Both directions are universal properties. A morphism `f` into `ℙ^{m+1}_ℤ` with `f^*T₀ = 0`
factors through `V(T₀)` by [Stacks, Tag 02OR], and factors through `hyperplane m` by Tag 01NE,
since its tuple of sections is `(0, …)`.

## Main definitions

* `Stacks.Chow.FreeTower.hyperplane`: the morphism `ℙᵐ_ℤ ⟶ ℙ^{m+1}_ℤ` classified by
  `(𝒪(1), (0, T₀, …, Tₘ))`.
* `Stacks.Chow.FreeTower.hyperplaneIdeal`: the zero scheme of `T₀` on `ℙ^{m+1}_ℤ`.
* `Stacks.Chow.FreeTower.hyperplaneZeroSchemeIso`: the isomorphism of that zero scheme with
  `ℙᵐ_ℤ`.
* `Stacks.Chow.FreeTower.consZero`, `Stacks.Chow.FreeTower.tail`: prepending and dropping a zero
  section of a generating tuple.

## Main results

* `Stacks.Chow.FreeTower.hyperplaneZeroSchemeIso_inv_comp_subschemeι`: the isomorphism is
  compatible with the closed immersion of the zero scheme and `hyperplane m`.
* `Stacks.Chow.FreeTower.exists_pullback_subschemeι_iso`: the restriction of `𝒪(1)` to the
  zero scheme is the pullback of `𝒪(1)` along the isomorphism, matching `T_{k+1}` with `T_k`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.ProjectiveSpaceModuli Stacks.ProjectiveFromSections
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.Chow.FreeTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable (m : ℕ)

/-- The coordinate sections `Tᵢ` of `𝒪(1)` on `ℙᵐ_ℤ` generate it. -/
theorem generatesStalks_coordGlobalSection :
    GeneratesStalks (coordGlobalSection.{u} m) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  have hint : ⨆ i : Fin (m + 1),
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
      (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X m)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hint.ge
    (show x ∈ (⊤ : (projectiveSpaceAtUniverse.{u} m).Opens) from trivial))
  exact ⟨i, mem_nonvanishingLocus_coordGlobalSection i hi⟩

/-- **The tuple classifying the hyperplane**: `𝒪(1)` on `ℙᵐ_ℤ` with the sections
`(0, T₀, …, Tₘ)`. -/
def hyperplaneTuple : GeneratingTuple (projectiveSpaceAtUniverse.{u} m) (m + 1) where
  bundle := twistingSheafAtUniverse.{u} m
  isInvertible := inferInstance
  coord := Fin.cons 0 (coordGlobalSection.{u} m)
  generates := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _
      (generatesStalks_coordGlobalSection m) x
    refine ⟨i.succ, ?_⟩
    simp only [nvCover, Fin.cons_succ]
    exact hi

/-- **The coordinate hyperplane** `ℙᵐ_ℤ ⟶ ℙ^{m+1}_ℤ`, `[T₀ : … : Tₘ] ↦ [0 : T₀ : … : Tₘ]`: the
morphism classified by `hyperplaneTuple m` under [Stacks, Tag 01NE]. -/
def hyperplane : projectiveSpaceAtUniverse.{u} m ⟶ projectiveSpaceAtUniverse.{u} (m + 1) :=
  (pointsEquiv _ (m + 1)).symm ⟦hyperplaneTuple m⟧

/-- The tautological tuple of the morphism classifying a tuple is that tuple. -/
private theorem isomorphic_tautological_symm {X : Scheme.{u}} {n : ℕ} (t : GeneratingTuple X n) :
    Isomorphic (tautological ((pointsEquiv X n).symm ⟦t⟧)) t := by
  have h : pointsEquiv X n ((pointsEquiv X n).symm ⟦t⟧) = ⟦t⟧ := Equiv.apply_symm_apply _ _
  rw [pointsEquiv_apply] at h
  exact Quotient.exact h

/-- The tautological tuple of the hyperplane is the classifying tuple. -/
theorem isomorphic_tautological_hyperplane :
    Isomorphic (tautological (hyperplane m)) (hyperplaneTuple m) :=
  isomorphic_tautological_symm _


/-! ### Generating tuples -/

section Tuples

variable {X Y : Scheme.{u}} {n : ℕ}

/-- An isomorphism of `𝒪_X`-modules undoes its inverse on sections. -/
theorem app_inv_app_hom {M N : X.Modules} (β : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app β.inv U (Scheme.Modules.Hom.app β.hom U x) = x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply,
    show Scheme.Modules.Hom.app β.hom U ≫ Scheme.Modules.Hom.app β.inv U =
      Scheme.Modules.Hom.app (β.hom ≫ β.inv) U from rfl, β.hom_inv_id]
  simp

/-- A tuple with a zero section prepended. -/
def consZero (t : GeneratingTuple X n) : GeneratingTuple X (n + 1) where
  bundle := t.bundle
  isInvertible := t.isInvertible
  coord := Fin.cons 0 t.coord
  generates := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _ t.generates x
    refine ⟨i.succ, ?_⟩
    simp only [nvCover, Fin.cons_succ]
    exact hi

/-- A tuple with its first section dropped, when that section is zero. -/
def tail (t : GeneratingTuple X (n + 1)) (h : t.coord 0 = 0) : GeneratingTuple X n where
  bundle := t.bundle
  isInvertible := t.isInvertible
  coord := fun k => t.coord k.succ
  generates := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _ t.generates x
    cases i using Fin.cases with
    | zero =>
      exfalso
      simp only [nvCover, h] at hi
      have h' := (Stacks.NonvanishingOpen.mem_nonvanishingOpen _ _ _ _).1 hi
      rw [Stacks.Ample.nonvanishingLocus_zero] at h'
      exact h'
    | succ k => exact ⟨k, hi⟩

/-- Prepending a zero section respects the identification of Tag 01NE. -/
theorem consZero_isomorphic {t t' : GeneratingTuple X n} (h : Isomorphic t t') :
    Isomorphic (consZero t) (consZero t') := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, fun i => ?_⟩
  cases i using Fin.cases with
  | zero => exact map_zero _
  | succ k => exact hβ k

/-- Dropping a zero first section respects the identification of Tag 01NE. -/
theorem tail_isomorphic {t t' : GeneratingTuple X (n + 1)} (h : Isomorphic t t')
    (h₀ : t.coord 0 = 0) (h₀' : t'.coord 0 = 0) : Isomorphic (tail t h₀) (tail t' h₀') := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, fun k => hβ k.succ⟩

/-- A tuple whose first section is zero is the tuple with that section prepended to its tail. -/
theorem isomorphic_consZero_tail (t : GeneratingTuple X (n + 1)) (h : t.coord 0 = 0) :
    Isomorphic t (consZero (tail t h)) := by
  refine ⟨Iso.refl _, fun i => ?_⟩
  cases i using Fin.cases with
  | zero => exact h
  | succ k => rfl

/-- Pulling back commutes with prepending a zero section. -/
theorem pullbackTuple_consZero (f : Y ⟶ X) (t : GeneratingTuple X n) :
    Isomorphic (pullbackTuple f (consZero t)) (consZero (pullbackTuple f t)) := by
  refine ⟨Iso.refl _, fun i => ?_⟩
  cases i using Fin.cases with
  | zero =>
    show pullbackGlobalSections f t.bundle 0 = 0
    exact map_zero _
  | succ k => rfl

/-- Dropping the prepended zero section gives back the tuple. -/
theorem tail_consZero (t : GeneratingTuple X n) : Isomorphic (tail (consZero t) rfl) t :=
  ⟨Iso.refl _, fun _ => rfl⟩

/-- The tautological tuple of the morphism classifying a tuple is that tuple. -/
theorem isomorphic_tautological_pointsEquiv_symm (t : GeneratingTuple X n) :
    Isomorphic (tautological ((pointsEquiv X n).symm ⟦t⟧)) t :=
  isomorphic_tautological_symm t

/-- Two morphisms to projective space with isomorphic tautological tuples are equal. -/
theorem eq_of_isomorphic_tautological {g g' : X ⟶ projectiveSpaceAtUniverse.{u} n}
    (h : Isomorphic (tautological g) (tautological g')) : g = g' :=
  pointsOfHom_injective (Quotient.sound h)

/-- The tautological tuple of a composite is the pullback of the tautological tuple. -/
theorem isomorphic_tautological_comp (f : Y ⟶ X) (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    Isomorphic (tautological (f ≫ g)) (pullbackTuple f (tautological g)) :=
  Quotient.exact (pointsOfHom_comp f g)

/-- Equal morphisms have isomorphic tautological tuples. -/
theorem isomorphic_tautological_of_eq {g g' : X ⟶ projectiveSpaceAtUniverse.{u} n}
    (h : g = g') : Isomorphic (tautological g) (tautological g') := by
  subst h
  exact isomorphic_refl _

end Tuples

/-! ### The hyperplane is the zero scheme of `T₀` -/

/-- **The tuple of coordinates of `ℙᵐ_ℤ`**: `𝒪(1)` with `T₀, …, Tₘ`. -/
def baseTuple : GeneratingTuple (projectiveSpaceAtUniverse.{u} m) m where
  bundle := twistingSheafAtUniverse.{u} m
  isInvertible := inferInstance
  coord := coordGlobalSection.{u} m
  generates := generatesStalks_coordGlobalSection m

/-- The hyperplane tuple is the coordinate tuple with a zero section prepended. -/
theorem hyperplaneTuple_eq : hyperplaneTuple m = consZero (baseTuple m) := rfl

/-- The pullback of a global section along the identity is the section itself, through
`AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
theorem pullbackGlobalSections_id {X : Scheme.{u}} (F : X.Modules) (s : Γ(F, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app F) ⊤
      (pullbackGlobalSections (𝟙 X) F s) = s := by
  have h : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).hom.app F) (𝟙 X ⁻¹ᵁ ⊤)
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F)
        ⊤ s) = s :=
    congrArg (fun (t : F ⟶ (Scheme.Modules.pushforward (𝟙 X)).obj F) =>
      Scheme.Modules.Hom.app t ⊤ s) (AlgebraicGeometry.pullbackId_unit F)
  have hu : pullbackGlobalSections (𝟙 X) F s = Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F) ⊤ s := by
    have hid : ((Scheme.Modules.pullback (𝟙 X)).obj F).presheaf.map
        (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op = 𝟙 _ := by
      rw [show (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op =
        CategoryTheory.CategoryStruct.id (Opposite.op (⊤ : X.Opens)) from rfl]
      exact CategoryTheory.Functor.map_id _ _
    show ((Scheme.Modules.pullback (𝟙 X)).obj F).presheaf.map
        (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F) ⊤ s) = _
    exact (CategoryTheory.ConcreteCategory.congr_hom hid _).trans (CategoryTheory.id_apply _)
  rw [hu]
  exact h

/-- The tautological tuple of the identity of `ℙᵐ_ℤ` is the coordinate tuple. -/
theorem isomorphic_tautological_id :
    Isomorphic (tautological (𝟙 (projectiveSpaceAtUniverse.{u} m))) (baseTuple m) :=
  ⟨(Scheme.Modules.pullbackId _).app _, fun _ => pullbackGlobalSections_id _ _⟩

/-- `𝒪(1)` on `ℙᵐ_ℤ` is invertible, in the spelling the zero scheme is formed in. -/
instance isInvertible_twistingSheafAtUniverse :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveSpaceAtUniverse.{u} m).sheaf.obj
      (projectiveSpaceAtUniverse.{u} m).ringCatSheaf.property (twistingSheafAtUniverse.{u} m) :=
  Stacks.TwistInvertibleOverBase.isInvertibleModule_twistingSheafAtUniverse m

/-- **The hyperplane `V(T₀)`**: the zero scheme of the first coordinate of `ℙ^{m+1}_ℤ`. -/
abbrev hyperplaneIdeal : (projectiveSpaceAtUniverse.{u} (m + 1)).IdealSheafData :=
  Stacks.Divisors.zeroScheme _ (twistingSheafAtUniverse.{u} (m + 1))
    (coordGlobalSection.{u} (m + 1) 0)

/-- The hyperplane pulls `T₀` back to zero. -/
theorem pullbackCoordSection_hyperplane_zero :
    pullbackCoordSection (hyperplane m) 0 = 0 := by
  obtain ⟨β, hβ⟩ := isomorphic_tautological_hyperplane m
  have h : Scheme.Modules.Hom.app β.hom ⊤ (pullbackCoordSection (hyperplane m) 0) = 0 := hβ 0
  rw [← app_inv_app_hom β ⊤ (pullbackCoordSection (hyperplane m) 0), h]
  exact map_zero _

/-- The hyperplane factors through the zero scheme of `T₀`. -/
def toHyperplaneIdeal : projectiveSpaceAtUniverse.{u} m ⟶ (hyperplaneIdeal m).subscheme :=
  ((Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme _ _ _
    (hyperplane m)).1 (pullbackCoordSection_hyperplane_zero m)).choose

/-- `toHyperplaneIdeal m` followed by the closed immersion of `V(T₀)` is the hyperplane. -/
@[reassoc (attr := simp)]
theorem toHyperplaneIdeal_subschemeι :
    toHyperplaneIdeal m ≫ (hyperplaneIdeal m).subschemeι = hyperplane m :=
  ((Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme _ _ _
    (hyperplane m)).1 (pullbackCoordSection_hyperplane_zero m)).choose_spec

/-- `T₀` vanishes on its zero scheme. -/
theorem pullbackCoordSection_subschemeι_zero :
    pullbackCoordSection (hyperplaneIdeal m).subschemeι 0 = 0 :=
  (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme _ _ _
    (hyperplaneIdeal m).subschemeι).2 ⟨𝟙 _, Category.id_comp _⟩

/-- **The tuple of `V(T₀)`**: the restriction of `𝒪(1)` with the restrictions of
`T₁, …, T_{m+1}`. -/
def zeroSchemeTuple : GeneratingTuple (hyperplaneIdeal m).subscheme m :=
  tail (tautological (hyperplaneIdeal m).subschemeι) (pullbackCoordSection_subschemeι_zero m)

/-- **The morphism `V(T₀) ⟶ ℙᵐ_ℤ`** classified by `zeroSchemeTuple m`. -/
def fromHyperplaneIdeal : (hyperplaneIdeal m).subscheme ⟶ projectiveSpaceAtUniverse.{u} m :=
  (pointsEquiv _ m).symm ⟦zeroSchemeTuple m⟧

/-- `ℙᵐ_ℤ ⟶ V(T₀) ⟶ ℙᵐ_ℤ` is the identity, by Tag 01NE. -/
theorem toHyperplaneIdeal_fromHyperplaneIdeal :
    toHyperplaneIdeal m ≫ fromHyperplaneIdeal m = 𝟙 _ := by
  refine eq_of_isomorphic_tautological (isomorphic_trans (isomorphic_tautological_comp _ _)
    (isomorphic_trans (pullbackTuple_isomorphic _
      (isomorphic_tautological_pointsEquiv_symm (zeroSchemeTuple m))) ?_))
  refine isomorphic_trans ?_ (isomorphic_symm (isomorphic_tautological_id m))
  have h₁ : Isomorphic (pullbackTuple (toHyperplaneIdeal m)
      (tautological (hyperplaneIdeal m).subschemeι)) (tautological (hyperplane m)) :=
    isomorphic_trans (isomorphic_symm (isomorphic_tautological_comp _ _))
      (isomorphic_tautological_of_eq (toHyperplaneIdeal_subschemeι m))
  have h₂ := isomorphic_trans h₁ (isomorphic_tautological_hyperplane m)
  have h₀ : (pullbackTuple (toHyperplaneIdeal m)
      (tautological (hyperplaneIdeal m).subschemeι)).coord 0 = 0 := by
    show pullbackGlobalSections _ _ (pullbackCoordSection (hyperplaneIdeal m).subschemeι 0) = 0
    rw [pullbackCoordSection_subschemeι_zero]
    exact map_zero _
  exact isomorphic_trans (tail_isomorphic h₂ h₀ rfl) (tail_consZero (baseTuple m))

/-- `V(T₀) ⟶ ℙᵐ_ℤ ⟶ ℙ^{m+1}_ℤ` is the closed immersion of `V(T₀)`, by Tag 01NE. -/
theorem fromHyperplaneIdeal_hyperplane :
    fromHyperplaneIdeal m ≫ hyperplane m = (hyperplaneIdeal m).subschemeι := by
  refine eq_of_isomorphic_tautological (isomorphic_trans (isomorphic_tautological_comp _ _) ?_)
  refine isomorphic_trans (pullbackTuple_isomorphic _ (isomorphic_tautological_hyperplane m)) ?_
  refine isomorphic_trans (pullbackTuple_consZero (fromHyperplaneIdeal m) (baseTuple m)) ?_
  refine isomorphic_trans ?_ (isomorphic_symm (isomorphic_consZero_tail _
    (pullbackCoordSection_subschemeι_zero m)))
  refine consZero_isomorphic ?_
  refine isomorphic_trans (pullbackTuple_isomorphic _ (isomorphic_symm
    (isomorphic_tautological_id m))) ?_
  refine isomorphic_trans (isomorphic_symm (isomorphic_tautological_comp _ _)) ?_
  rw [Category.comp_id]
  exact isomorphic_tautological_pointsEquiv_symm _

/-- **`ℙᵐ_ℤ` is the zero scheme of `T₀` on `ℙ^{m+1}_ℤ`.** -/
def hyperplaneZeroSchemeIso : (hyperplaneIdeal m).subscheme ≅ projectiveSpaceAtUniverse.{u} m where
  hom := fromHyperplaneIdeal m
  inv := toHyperplaneIdeal m
  hom_inv_id := by
    rw [← cancel_mono (hyperplaneIdeal m).subschemeι, Category.assoc,
      toHyperplaneIdeal_subschemeι, fromHyperplaneIdeal_hyperplane, Category.id_comp]
  inv_hom_id := toHyperplaneIdeal_fromHyperplaneIdeal m

/-- The hyperplane is the closed immersion of `V(T₀)`, through the isomorphism. -/
theorem hyperplaneZeroSchemeIso_inv_comp_subschemeι :
    (hyperplaneZeroSchemeIso m).inv ≫ (hyperplaneIdeal m).subschemeι = hyperplane m :=
  toHyperplaneIdeal_subschemeι m

/-- **The restriction of `𝒪(1)` to `V(T₀)` is `𝒪(1)`** of `ℙᵐ_ℤ`, carried along the
isomorphism `hyperplaneZeroSchemeIso`. The isomorphism carries the restriction of `T_{k+1}` to
the pullback of `T_k`. -/
theorem exists_pullback_subschemeι_iso :
    ∃ β : (Scheme.Modules.pullback (hyperplaneIdeal m).subschemeι).obj
        (twistingSheafAtUniverse.{u} (m + 1)) ≅
      (Scheme.Modules.pullback (hyperplaneZeroSchemeIso m).hom).obj
        (twistingSheafAtUniverse.{u} m),
      ∀ k : Fin (m + 1), Scheme.Modules.Hom.app β.hom ⊤
        (pullbackCoordSection (hyperplaneIdeal m).subschemeι k.succ) =
          pullbackCoordSection (hyperplaneZeroSchemeIso m).hom k := by
  obtain ⟨β, hβ⟩ := isomorphic_symm (isomorphic_tautological_pointsEquiv_symm (zeroSchemeTuple m))
  exact ⟨β, hβ⟩

end Stacks.Chow.FreeTower

end
