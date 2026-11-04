module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardNormalizedIso
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent

/-!
# Invertible modules trivialised along the section are determined locally

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` with a section `σ`, and
assume `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T`, the hypothesis of
Stacks 0D28.  This file proves the separation half of the sheaf property in the proof of
Stacks 0D28: an invertible module `M` on `X_T` and a quasi-coherent module `N` which become
isomorphic on the base changes `X_{U_i}` of an fpqc covering family `{U_i ⟶ T}`, and whose
restrictions along the section `σ_T` are isomorphic, are isomorphic.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.nonempty_iso_of_isFpqcCovering`: **the separation
  step of Stacks 0D28.**

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The restriction of an isomorphism of inverse images, on homomorphisms. -/
theorem restrictPullbackHom_hom {V Z W : AlgebraicSpaces B S hS} {p : Z ⟶ W} {q : V ⟶ W}
    (a : V ⟶ Z) (ha : a ≫ p = q) {M N : Modules.{u, u} B S hS W.1 W.2}
    (γ : (modulePullback B S hS p).obj M ≅ (modulePullback B S hS p).obj N) :
    restrictPullbackHom a ha γ.hom = (restrictPullbackIso a ha ha γ).hom :=
  rfl

/-- The restriction of an isomorphism of inverse images, on inverse homomorphisms. -/
theorem restrictPullbackHom_inv {V Z W : AlgebraicSpaces B S hS} {p : Z ⟶ W} {q : V ⟶ W}
    (a : V ⟶ Z) (ha : a ≫ p = q) {M N : Modules.{u, u} B S hS W.1 W.2}
    (γ : (modulePullback B S hS p).obj M ≅ (modulePullback B S hS p).obj N) :
    restrictPullbackHom a ha γ.inv = (restrictPullbackIso a ha ha γ).inv :=
  congrArg Iso.hom (restrictPullbackIso_symm a ha ha γ)

/-- Restriction of homomorphisms of inverse images is compatible with composition. -/
theorem restrictPullbackHom_comp_hom {V Z W : AlgebraicSpaces B S hS} {p : Z ⟶ W} {q : V ⟶ W}
    (a : V ⟶ Z) (ha : a ≫ p = q) {M N P : Modules.{u, u} B S hS W.1 W.2}
    (α : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N)
    (β : (modulePullback B S hS p).obj N ⟶ (modulePullback B S hS p).obj P) :
    restrictPullbackHom a ha (α ≫ β) = restrictPullbackHom a ha α ≫ restrictPullbackHom a ha β := by
  rw [restrictPullbackHom, restrictPullbackHom, restrictPullbackHom, Functor.conjHom,
    Functor.conjHom, Functor.conjHom, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Restriction of homomorphisms of inverse images carries identities to identities. -/
theorem restrictPullbackHom_id {V Z W : AlgebraicSpaces B S hS} {p : Z ⟶ W} {q : V ⟶ W}
    (a : V ⟶ Z) (ha : a ≫ p = q) (M : Modules.{u, u} B S hS W.1 W.2) :
    restrictPullbackHom a ha (𝟙 ((modulePullback B S hS p).obj M)) = 𝟙 _ :=
  congrArg Iso.hom (restrictPullbackIso_refl a ha)

namespace PicardSituation

variable {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-- The Hom situation of the morphism `f : X ⟶ B` and the structure sheaf of `X`. -/
abbrev overlapSituation (s : PicardSituation B S hS) : HomSituation B S hS where
  X := s.X
  base := s.base
  f := s.f
  F := structureModule s.X
  G := structureModule s.X
  quasicoherent_F := isQuasicoherentOnSite_of_isInvertibleModule _ _
    (isInvertibleModule_structureModule s.X)
  quasicoherent_G := isQuasicoherentOnSite_of_isInvertibleModule _ _
    (isInvertibleModule_structureModule s.X)

/-- **Agreement on the fibre product of two base changes is agreement on the base change of the
overlap.**  Two isomorphisms `x`, `y` of the inverse images of `M` and `N` along `X_g` and
`X_{g'}` restrict to the same isomorphism on `X_U ×_{X_T} X_{U'}` as soon as they restrict to the
same isomorphism on the base change `X_{U ×_T U'}` of the overlap of the two test schemes, which
the fibre product maps to. -/
theorem restrictPullbackIso_fiberFst_eq {T U U' : s.SchemesOver} (g : U ⟶ T) (g' : U' ⟶ T)
    {M N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2}
    (x : (modulePullback B S hS (baseChangeMap s.f g)).obj M ≅
      (modulePullback B S hS (baseChangeMap s.f g)).obj N)
    (y : (modulePullback B S hS (baseChangeMap s.f g')).obj M ≅
      (modulePullback B S hS (baseChangeMap s.f g')).obj N)
    (e₁ : baseChangeMap s.f (s.overlapSituation.overlapTestFst g g') ≫ baseChangeMap s.f g =
      baseChangeMap s.f (s.overlapSituation.overlapTestFst g g' ≫ g))
    (e₂ : baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g') ≫ baseChangeMap s.f g' =
      baseChangeMap s.f (s.overlapSituation.overlapTestFst g g' ≫ g))
    (e₃ : fiberSnd (baseChangeMap s.f g) (baseChangeMap s.f g') ≫ baseChangeMap s.f g' =
      fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g') ≫ baseChangeMap s.f g)
    (h : restrictPullbackIso (baseChangeMap s.f (s.overlapSituation.overlapTestFst g g')) e₁ e₁ x =
      restrictPullbackIso (baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g')) e₂ e₂ y) :
    restrictPullbackIso (fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g')) rfl rfl x =
      restrictPullbackIso (fiberSnd (baseChangeMap s.f g) (baseChangeMap s.f g')) e₃ e₃ y := by
  have hf : fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g') =
      s.overlapSituation.overlapTestComparison g g' ≫
        baseChangeMap s.f (s.overlapSituation.overlapTestFst g g') :=
    (s.overlapSituation.overlapTestComparison_comp_baseChangeMap_fst g g').symm
  have hsn : fiberSnd (baseChangeMap s.f g) (baseChangeMap s.f g') =
      s.overlapSituation.overlapTestComparison g g' ≫
        baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g') :=
    (s.overlapSituation.overlapTestComparison_comp_baseChangeMap_snd g g').symm
  have hoc : s.overlapSituation.overlapTestComparison g g' ≫
      baseChangeMap s.f (s.overlapSituation.overlapTestFst g g' ≫ g) =
      fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g') ≫ baseChangeMap s.f g := by
    rw [hf, Category.assoc, e₁]
  have k₁ : (s.overlapSituation.overlapTestComparison g g' ≫
      baseChangeMap s.f (s.overlapSituation.overlapTestFst g g')) ≫ baseChangeMap s.f g =
      fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g') ≫ baseChangeMap s.f g := by
    rw [Category.assoc, e₁, hoc]
  have k₂ : (s.overlapSituation.overlapTestComparison g g' ≫
      baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g')) ≫ baseChangeMap s.f g' =
      fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g') ≫ baseChangeMap s.f g := by
    rw [Category.assoc, e₂, hoc]
  calc restrictPullbackIso (fiberFst (baseChangeMap s.f g) (baseChangeMap s.f g')) rfl rfl x
      = restrictPullbackIso (s.overlapSituation.overlapTestComparison g g' ≫
          baseChangeMap s.f (s.overlapSituation.overlapTestFst g g')) k₁ k₁ x :=
        restrictPullbackIso_congr hf _ _ _ _ x
    _ = restrictPullbackIso (s.overlapSituation.overlapTestComparison g g') hoc hoc
          (restrictPullbackIso (baseChangeMap s.f (s.overlapSituation.overlapTestFst g g'))
            e₁ e₁ x) :=
        (restrictPullbackIso_restrictPullbackIso _ e₁ e₁ _ hoc hoc x).symm
    _ = restrictPullbackIso (s.overlapSituation.overlapTestComparison g g') hoc hoc
          (restrictPullbackIso (baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g'))
            e₂ e₂ y) := by rw [h]
    _ = restrictPullbackIso (s.overlapSituation.overlapTestComparison g g' ≫
          baseChangeMap s.f (s.overlapSituation.overlapTestSnd g g')) k₂ k₂ y :=
        restrictPullbackIso_restrictPullbackIso _ e₂ e₂ _ hoc hoc y
    _ = restrictPullbackIso (fiberSnd (baseChangeMap s.f g) (baseChangeMap s.f g')) e₃ e₃ y :=
        restrictPullbackIso_congr hsn.symm _ _ _ _ y

/-- **The separation step of Stacks 0D28.**  Assume `𝒪_U ⟶ f_{U, *}𝒪_{X_U}` is an isomorphism
for every test scheme `U`.  Let `{g_i : U_i ⟶ T}` be a family of test schemes whose underlying
morphisms form an fpqc covering, `M` an invertible and `N` a quasi-coherent `𝒪_{X_T}`-module,
with `σ_T^*M ≅ σ_T^*N` and `X_{g_i}^*M ≅ X_{g_i}^*N` for every `i`.  Then `M ≅ N`. -/
theorem nonempty_iso_of_isFpqcCovering (hstr : s.StructureSheafMapIso) {T : s.SchemesOver}
    {I : Type v} {U : I → s.SchemesOver} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ (spaceMap (g i)).hom)
    {M N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2}
    (hM : IsInvertibleModule (s.baseChange T) M) (hN : N.IsQuasicoherentOnSite)
    (β : (modulePullback B S hS (baseChangeSection σ hσ T)).obj M ≅
      (modulePullback B S hS (baseChangeSection σ hσ T)).obj N)
    (hloc : ∀ i, Nonempty ((modulePullback B S hS (baseChangeMap s.f (g i))).obj M ≅
      (modulePullback B S hS (baseChangeMap s.f (g i))).obj N)) :
    Nonempty (M ≅ N) := by
  classical
  have hMi : ∀ i, IsInvertibleModule (s.baseChange (U i))
      ((modulePullback B S hS (baseChangeMap s.f (g i))).obj M) :=
    fun i ↦ modulePullbackInvertible _ M hM
  have hNi : ∀ i, IsInvertibleModule (s.baseChange (U i))
      ((modulePullback B S hS (baseChangeMap s.f (g i))).obj N) := fun i ↦ by
    have := hMi i
    exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (hloc i).some
  have hex : ∀ i, ∃ ψ, IsNormalized σ hσ N β
      (Iso.refl ((modulePullback B S hS (baseChangeSection σ hσ T)).obj N)) (g i) (g i)
      (spaceMap (g i) ≫ baseChangeSection σ hσ T) rfl rfl ψ :=
    fun i ↦ exists_isNormalized σ hσ (hstr (U i)) (hMi i) (hNi i) (hloc i).some
  choose ψ hψ using hex
  have hagree : ∀ i j, restrictPullbackIso (overlapFst (fun i ↦ baseChangeMap s.f (g i)) i j)
      (rfl : overlapFst (fun i ↦ baseChangeMap s.f (g i)) i j ≫ baseChangeMap s.f (g i) = _) rfl
      (ψ i) =
      restrictPullbackIso (overlapSnd (fun i ↦ baseChangeMap s.f (g i)) i j)
        (overlapSnd_comp_eq (𝟙 _) (fun i ↦ baseChangeMap s.f (g i))
          (fun i ↦ baseChangeMap s.f (g i)) (fun i ↦ Category.comp_id _) i j)
        (overlapSnd_comp_eq (𝟙 _) (fun i ↦ baseChangeMap s.f (g i))
          (fun i ↦ baseChangeMap s.f (g i)) (fun i ↦ Category.comp_id _) i j) (ψ j) := by
    intro i j
    have hcond : s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i =
        s.overlapSituation.overlapTestSnd (g i) (g j) ≫ g j :=
      s.overlapSituation.overlapTest_condition (g i) (g j)
    have hw : spaceMap (s.overlapSituation.overlapTestSnd (g i) (g j)) ≫ spaceMap (g j) ≫
        baseChangeSection σ hσ T =
        spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ spaceMap (g i) ≫
          baseChangeSection σ hσ T := by
      rw [← Category.assoc, ← Category.assoc, ← spaceMap_comp, ← spaceMap_comp, hcond]
    have h₁ := (hψ i).restrict σ hσ (s.overlapSituation.overlapTestFst (g i) (g j))
      (a₁' := s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i)
      (a₂' := s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i) rfl rfl
      (w' := spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ spaceMap (g i) ≫
        baseChangeSection σ hσ T) rfl
    have h₂ := (hψ j).restrict σ hσ (s.overlapSituation.overlapTestSnd (g i) (g j))
      (a₁' := s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i)
      (a₂' := s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i) hcond.symm hcond.symm hw
    exact restrictPullbackIso_fiberFst_eq (g i) (g j) (ψ i) (ψ j) _ _ _
      (IsNormalized.eq σ hσ (hstr _) (modulePullbackInvertible _ M hM) h₁ h₂)
  have hqcM : ((modulePullback B S hS (𝟙 (s.baseChange T))).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M
      (isQuasicoherentOnSite_of_isInvertibleModule _ M hM)
  have hqcN : ((modulePullback B S hS (𝟙 (s.baseChange T))).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ N hN
  have glue := fun {P Q : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2} hP hQ α hα ↦
    gluesModuleHomAlongFpqcCovering (𝟙 _) (fun i ↦ baseChangeMap s.f (g i))
      (fun i ↦ baseChangeMap s.f (g i)) (fun i ↦ Category.comp_id _)
      (isFpqcCovering_baseChangeMap s.f g hg) P Q hP hQ α hα
  have hid : ∀ {P : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2} hP
      (a : (modulePullback B S hS (𝟙 (s.baseChange T))).obj P ⟶
        (modulePullback B S hS (𝟙 (s.baseChange T))).obj P),
      (∀ i, restrictPullbackHom (baseChangeMap s.f (g i)) (Category.comp_id _) a = 𝟙 _) → a = 𝟙 _ :=
    fun hP a ha ↦ by
      obtain ⟨β₀, -, hu⟩ := glue hP hP (fun i ↦ 𝟙 _) fun i j ↦ by
        rw [restrictPullbackHom_id, restrictPullbackHom_id]
      exact (hu _ ha).trans (hu _ fun i ↦ restrictPullbackHom_id _ _ _).symm
  obtain ⟨φ, hφ, -⟩ := glue hqcM hqcN (fun i ↦ (ψ i).hom) fun i j ↦ by
    rw [restrictPullbackHom_hom, restrictPullbackHom_hom]
    exact congrArg Iso.hom (hagree i j)
  obtain ⟨φ', hφ', -⟩ := glue hqcN hqcM (fun i ↦ (ψ i).inv) fun i j ↦ by
    rw [restrictPullbackHom_inv, restrictPullbackHom_inv]
    exact congrArg Iso.inv (hagree i j)
  have e₁ : φ ≫ φ' = 𝟙 _ :=
    hid hqcM _ fun i ↦ by rw [restrictPullbackHom_comp_hom, hφ, hφ', Iso.hom_inv_id]
  have e₂ : φ' ≫ φ = 𝟙 _ :=
    hid hqcN _ fun i ↦ by rw [restrictPullbackHom_comp_hom, hφ, hφ', Iso.inv_hom_id]
  have hc := modulePushforwardCoherence B S hS
  exact ⟨((hc.modulePullbackIdIso _).app M).symm ≪≫ ⟨φ, φ', e₁, e₂⟩ ≪≫
    (hc.modulePullbackIdIso _).app N⟩

end PicardSituation

end AlgebraicGeometry.Space

end
