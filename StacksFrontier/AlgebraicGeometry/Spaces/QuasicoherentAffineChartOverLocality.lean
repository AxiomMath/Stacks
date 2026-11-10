module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects

/-!
# Quasi-coherent modules over an affine chart: from the chart to everything over it

Let `F` be an algebraic space and `c` an affine étale chart of `F`. For quasi-coherent
`𝒪_F`-modules, what happens on the sections over `c` propagates to every chart `T ⟶ c`:

* a morphism `φ : M ⟶ N` bijective on the sections over `c` is bijective on the sections over
  every `T ⟶ c`;
* a module with no sections over `c` has none over any `T ⟶ c`;
* a module with finitely presented sections over `c` has finitely presented sections over every
  affine `T ⟶ c`.

Over an affine `T ⟶ c` this is the base change comparison `𝒪(T) ⊗_{𝒪(c)} M(c) ≅ M(T)`
(`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite`); an arbitrary
`T` is covered by affine charts (`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), all
again over `c`, and the sheaf property finishes. These are the forms in which the local
conclusions of [Stacks, Tag 0CX9] on an affine chart are fed to the gluing step
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isExistenceNeighbourhood_chartsNeighbourhood`.

## Main results

* `Stacks.SheafOfModules.bijective_val_app_of_injective_of_locallySurjective`: the sheaf
  statement, on an arbitrary site.
* `AlgebraicGeometry.Space.bijective_val_app_of_bijective_affineChart`.
* `AlgebraicGeometry.Space.subsingleton_val_obj_of_subsingleton_affineChart`.
* `AlgebraicGeometry.Space.finitePresentation_val_obj_of_finitePresentation_affineChart`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u₁ v₁ v u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Bijectivity of a sections map from injectivity and local surjectivity.** Let
`φ : M ⟶ N` be a morphism of sheaves of modules, injective on the sections over every object
over `T`, and such that every section of `N` over `T` lifts, after restriction along each arrow
of a covering sieve of `T`. Then `φ` is bijective on the sections over `T`. -/
theorem bijective_val_app_of_injective_of_locallySurjective {M N : SheafOfModules.{v} R}
    (φ : M ⟶ N) {T : C} (Sv : Sieve T) (hSv : Sv ∈ J T)
    (hinj : ∀ ⦃V : C⦄ (_ : V ⟶ T), Function.Injective (φ.val.app (op V)))
    (hsurj : ∀ ⦃V : C⦄ (g : V ⟶ T), Sv g → ∀ t : N.val.obj (op T),
      ∃ s : M.val.obj (op V), φ.val.app (op V) s = N.val.map g.op t) :
    Function.Bijective (φ.val.app (op T)) := by
  refine ⟨hinj (𝟙 T), fun t => ?_⟩
  have hPtype : Presheaf.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{v}) :=
    ((sheafCompose J (forget AddCommGrpCat.{v})).obj ⟨M.val.presheaf, M.isSheaf⟩).2
  have hsh := hPtype.isSheafFor Sv hSv
  choose s hs using fun (V : C) (g : V ⟶ T) (hg : Sv g) => hsurj g hg t
  let x : Presieve.FamilyOfElements (M.val.presheaf ⋙ forget AddCommGrpCat.{v}) Sv.arrows :=
    fun V g hg => s V g hg
  have hfam : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    change M.val.map g₁.op (s Y₁ f₁ h₁) = M.val.map g₂.op (s Y₂ f₂ h₂)
    apply hinj (g₁ ≫ f₁)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hs, hs,
      ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply, ← op_comp,
      ← op_comp, fac]
  refine ⟨hsh.amalgamate x hfam, ?_⟩
  refine N.isSheaf.isSeparated T Sv hSv _ _ fun W g hg => ?_
  have key : M.val.map g.op (hsh.amalgamate x hfam) = s W g hg :=
    hsh.isAmalgamation hfam g hg
  change N.val.map g.op (φ.val.app (op T) _) = N.val.map g.op t
  refine (PresheafOfModules.naturality_apply φ.val g.op _).symm.trans ?_
  rw [key, hs]

/-- Restriction along a composite, applied to a section. -/
theorem val_map_comp_apply (M : SheafOfModules.{v} R) {W V T : C} (b : W ⟶ V) (g : V ⟶ T)
    (x : M.val.obj (op T)) :
    M.val.map (b ≫ g).op x = M.val.map b.op (M.val.map g.op x) := by
  rw [op_comp, PresheafOfModules.map_comp_apply]

/-- Two sections agreeing after restriction to the members of a covering family agree. -/
theorem eq_of_forall_ofArrows (M : SheafOfModules.{v} R) {T : C} {I : Type*} (Ti : I → C)
    (fi : ∀ k, Ti k ⟶ T) (hcov : Sieve.ofArrows Ti fi ∈ J T) (x y : M.val.obj (op T))
    (h : ∀ k, M.val.map (fi k).op x = M.val.map (fi k).op y) : x = y := by
  refine M.isSheaf.isSeparated T _ hcov x y fun W g hg => ?_
  obtain ⟨k, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  change M.val.map (b ≫ fi k).op x = M.val.map (b ≫ fi k).op y
  rw [val_map_comp_apply, val_map_comp_apply, h k]

/-- **Injectivity over everything over `c`, from enough objects.** If `J` has enough `P`
objects and `φ` is injective over every `P` object over `c`, it is injective over every object
over `c`. -/
theorem injective_val_app_of_hasEnoughObjects (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {c : C}
    (h : ∀ T : C, P T → (T ⟶ c) → Function.Injective (φ.val.app (op T)))
    (T : C) (f : T ⟶ c) : Function.Injective (φ.val.app (op T)) := by
  intro x y hxy
  obtain ⟨I, Ti, fi, hcov, haff⟩ := hP T
  refine eq_of_forall_ofArrows M Ti fi hcov x y fun k => h _ (haff k) (fi k ≫ f) ?_
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hxy]

/-- **Bijectivity over everything over `c`, from enough objects.** If `J` has enough `P`
objects and `φ` is bijective over every `P` object over `c`, it is bijective over every object
over `c`. -/
theorem bijective_val_app_of_hasEnoughObjects (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {c : C}
    (h : ∀ T : C, P T → (T ⟶ c) → Function.Bijective (φ.val.app (op T)))
    (T : C) (f : T ⟶ c) : Function.Bijective (φ.val.app (op T)) := by
  obtain ⟨I, Ti, fi, hcov, haff⟩ := hP T
  refine bijective_val_app_of_injective_of_locallySurjective φ _ hcov
    (fun V g => injective_val_app_of_hasEnoughObjects P hP φ (fun T hT g => (h T hT g).1) V
      (g ≫ f)) fun V g hg t => ?_
  obtain ⟨k, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  obtain ⟨s, hs⟩ := (h _ (haff k) (fi k ≫ f)).2 (N.val.map (fi k).op t)
  refine ⟨M.val.map b.op s, ?_⟩
  rw [PresheafOfModules.naturality_apply, hs, val_map_comp_apply]

/-- **Vanishing over everything over `c`, from enough objects.** -/
theorem subsingleton_val_obj_of_hasEnoughObjects (P : ObjectProperty C)
    (hP : J.HasEnoughObjects P) (M : SheafOfModules.{v} R) {c : C}
    (h : ∀ T : C, P T → (T ⟶ c) → Subsingleton (M.val.obj (op T)))
    (T : C) (f : T ⟶ c) : Subsingleton (M.val.obj (op T)) := by
  obtain ⟨I, Ti, fi, hcov, haff⟩ := hP T
  exact ⟨fun x y => eq_of_forall_ofArrows M Ti fi hcov x y fun k =>
    (h _ (haff k) (fi k ≫ f)).elim _ _⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Over an affine chart `T ⟶ c`, a morphism of quasi-coherent modules bijective over the affine
chart `c` is bijective. -/
theorem bijective_val_app_of_bijective_affineChart_of_isAffine
    {M N : Modules.{u, u} B S hS F hF} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) {c T : SmallEtale B S hS F}
    (hc : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj c))
    (hT : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T))
    (f : T ⟶ c) (hφ : Function.Bijective (φ.val.app (op c))) :
    Function.Bijective (φ.val.app (op T)) := by
  let := chartAlgebra (hF := hF) f
  let φc : (M.val.obj (op c) : Type u) ≃ₗ[chartRing B S hS F hF c] (N.val.obj (op c) : Type u) :=
    LinearEquiv.ofBijective (φ.val.app (op c)).hom hφ
  have hM' := bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF M hM hc hT f
  have hN' := bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF N hN hc hT f
  have hsq : ∀ z, φ.val.app (op T) (sectionsBaseChange M f z) =
      sectionsBaseChange N f (LinearEquiv.lTensor (chartRing B S hS F hF T) φc z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      rw [LinearEquiv.lTensor_tmul, chartBaseChange_tmul, chartBaseChange_tmul,
        chartRestrictLinear_apply, chartRestrictLinear_apply]
      exact ((φ.val.app (op T)).hom.map_smul b _).trans
        (congrArg (b • ·) (PresheafOfModules.naturality_apply φ.val f.op x))
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  refine (Function.Bijective.of_comp_iff _ hM').1 ?_
  rw [show φ.val.app (op T) ∘ sectionsBaseChange M f =
      sectionsBaseChange N f ∘ LinearEquiv.lTensor (chartRing B S hS F hF T) φc from funext hsq]
  exact hN'.comp (LinearEquiv.bijective _)

/-- **A morphism of quasi-coherent modules bijective over an affine chart `c` is bijective over
every chart `T ⟶ c`.** -/
theorem bijective_val_app_of_bijective_affineChart
    {M N : Modules.{u, u} B S hS F hF} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) {c : SmallEtale B S hS F}
    (hc : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj c))
    (hφ : Function.Bijective (φ.val.app (op c))) (T : SmallEtale B S hS F) (f : T ⟶ c) :
    Function.Bijective (φ.val.app (op T)) :=
  Stacks.SheafOfModules.bijective_val_app_of_hasEnoughObjects (IsAffineChart B S hS F)
    (hasEnoughObjects_isAffineChart B S hS F) φ
    (fun _ hV g => bijective_val_app_of_bijective_affineChart_of_isAffine hM hN φ hc hV g hφ) T f

/-- **A quasi-coherent module with no sections over an affine chart `c` has no sections over any
chart `T ⟶ c`.** -/
theorem subsingleton_val_obj_of_subsingleton_affineChart
    {M : Modules.{u, u} B S hS F hF} (hM : M.IsQuasicoherentOnSite) {c : SmallEtale B S hS F}
    (hc : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj c))
    (h0 : Subsingleton (M.val.obj (op c))) (T : SmallEtale B S hS F) (f : T ⟶ c) :
    Subsingleton (M.val.obj (op T)) := by
  refine Stacks.SheafOfModules.subsingleton_val_obj_of_hasEnoughObjects (IsAffineChart B S hS F)
    (hasEnoughObjects_isAffineChart B S hS F) M (fun V hV g => ?_) T f
  let := chartAlgebra (hF := hF) g
  have hs := (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF M hM hc hV g).2
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hs x
  obtain ⟨y', rfl⟩ := hs y
  rw [Subsingleton.elim x' y']

/-- **A quasi-coherent module with finitely presented sections over an affine chart `c` has
finitely presented sections over every affine chart `T ⟶ c`.** -/
theorem finitePresentation_val_obj_of_finitePresentation_affineChart
    {M : Modules.{u, u} B S hS F hF} (hM : M.IsQuasicoherentOnSite) {c T : SmallEtale B S hS F}
    (hc : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj c))
    (hT : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T))
    (f : T ⟶ c) (h : Module.FinitePresentation (chartRing B S hS F hF c) (M.val.obj (op c))) :
    Module.FinitePresentation (chartRing B S hS F hF T) (M.val.obj (op T)) := by
  let := chartAlgebra (hF := hF) f
  exact Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective _
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF M hM hc hT f))

end AlgebraicGeometry.Space

end
