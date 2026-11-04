module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFullness

/-!
# Morphisms of quasi-coherent modules on the slice at an affine chart

Let `F` be an algebraic space and `X` an étale chart of `F` whose underlying scheme is affine.
For quasi-coherent `𝒪_F`-modules `G` and `G'`, evaluation at the terminal object of the slice of
the small étale site at `X` identifies the morphisms `G|_X ⟶ G'|_X` of the restrictions with the
`𝒪_F(X)`-linear maps `G(X) ⟶ G'(X)`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.sliceHomEvaluation`: evaluation of a morphism of restrictions to
  the slice at `X` on the terminal object of the slice.

## Main results

* `AlgebraicGeometry.Space.C1573.bijective_sliceHomEvaluation`: the identification.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace SheafOfModules.C1573

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The isomorphism of sections at `T` induced by an isomorphism of sheaves of modules. -/
def isoValApp {P P' : SheafOfModules.{u} R} (e : P ≅ P') (T : Cᵒᵖ) :
    P.val.obj T ≅ P'.val.obj T where
  hom := e.hom.val.app T
  inv := e.inv.val.app T
  hom_inv_id := by
    rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, e.hom_inv_id]; rfl
  inv_hom_id := by
    rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, e.inv_hom_id]; rfl

/-- Evaluation of morphisms of sheaves of modules at an object is bijective for one pair of
modules as soon as it is for an isomorphic pair. -/
theorem bijective_val_app_of_iso {P P' Q Q' : SheafOfModules.{u} R} (e₁ : P ≅ P') (e₂ : Q ≅ Q')
    (T : Cᵒᵖ) (h : Function.Bijective fun α : P' ⟶ Q' => α.val.app T) :
    Function.Bijective fun α : P ⟶ Q => α.val.app T := by
  have key : (fun α : P ⟶ Q => α.val.app T) =
      ((isoValApp e₁ T).homCongr (isoValApp e₂ T)).symm ∘ (fun α : P' ⟶ Q' => α.val.app T) ∘
        e₁.homCongr e₂ := by
    funext α
    have hα : α = e₁.hom ≫ (e₁.inv ≫ α ≫ e₂.hom) ≫ e₂.inv := by simp
    conv_lhs => rw [hα]
    rfl
  rw [key]
  exact ((isoValApp e₁ T).homCongr (isoValApp e₂ T)).symm.bijective.comp
    (h.comp (e₁.homCongr e₂).bijective)

end SheafOfModules.C1573

namespace AlgebraicGeometry.Scheme.Modules.C1573

/-- On an affine scheme, a morphism of quasi-coherent modules is determined by, and can be built
from, the map of global sections of its pullback along an endomorphism equal to the identity. -/
theorem bijective_pullback_map_val_app_top_of_eq_id {Y : Scheme.{u}} [IsAffine Y] (h : Y ⟶ Y)
    (hh : h = 𝟙 Y) (M N : Y.Modules) [M.IsQuasicoherent] :
    Function.Bijective fun φ : M ⟶ N => ((Scheme.Modules.pullback h).map φ).val.app (op ⊤) := by
  subst hh
  have hb : Function.Bijective fun φ : M ⟶ N => φ.val.app (op ⊤) :=
    ModuleCat.homEquiv.symm.bijective.comp (Stacks.Algebraization.sectionsTop_bijective M N)
  let e := Scheme.Modules.pullbackId Y
  have : (Scheme.Modules.pullback (𝟙 Y)).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  exact (SheafOfModules.C1573.bijective_val_app_of_iso (e.app M) (e.app N) _ hb).comp
    ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective M N)

end AlgebraicGeometry.Scheme.Modules.C1573

namespace AlgebraicGeometry.Space.C1573

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Evaluation of a morphism of restrictions to the slice at `X` on the terminal object of the
slice: the map of sections over `X`. -/
def sliceHomEvaluation (X : (smallEtaleRingedSite B S hS F hF).C)
    {G G' : Modules.{u, u} B S hS F hF} (α : G.over X ⟶ G'.over X) :
    G.val.obj (op X) →ₗ[chartRing B S hS F hF X] G'.val.obj (op X) :=
  (α.val.app (op (CategoryTheory.Over.mk (𝟙 X)))).hom

/-- Evaluation on the terminal object of the slice at an affine chart is bijective on morphisms
of associated modules. -/
theorem bijective_val_app_sliceAssociatedModule (X : SmallEtale B S hS F)
    [IsAffine (chartScheme X)] {M N : (chartScheme X).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((SmallEtale.topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (SmallEtale.sliceToOver B S hS F X)))
    (hN : Presheaf.IsSheaf ((SmallEtale.topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) N (SmallEtale.sliceToOver B S hS F X))) :
    Function.Bijective fun α : SmallEtale.sliceAssociatedModule B S hS F hF X M hM ⟶
        SmallEtale.sliceAssociatedModule B S hS F hF X N hN =>
      α.val.app (op (CategoryTheory.Over.mk (𝟙 X))) := by
  have hff := SmallEtale.bijective_associatedModuleMap_slice B S hS F hF X (M := M) (N := N) hN
  have : IsAffine ((SmallEtale.sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).left :=
    show IsAffine (chartScheme X) from inferInstance
  have hpb := @Scheme.Modules.C1573.bijective_pullback_map_val_app_top_of_eq_id _ this
    ((SmallEtale.sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).hom
    (SmallEtale.sliceToOver_obj_mk_id_hom B S hS F X) M N ‹_›
  let mk : (Stacks.Sites.associatedModulePresheaf (chartScheme X) M
        (SmallEtale.sliceToOver B S hS F X) ⟶
      Stacks.Sites.associatedModulePresheaf (chartScheme X) N
        (SmallEtale.sliceToOver B S hS F X)) →
      (SmallEtale.sliceAssociatedModule B S hS F hF X M hM ⟶
        SmallEtale.sliceAssociatedModule B S hS F hF X N hN) := fun a => ⟨a⟩
  have hmk : Function.Bijective mk :=
    ⟨fun a b hab => congrArg SheafOfModules.Hom.val hab, fun α => ⟨α.val, rfl⟩⟩
  exact (Function.Bijective.of_comp_iff _ (hmk.comp hff)).mp hpb

/-- At an étale chart `X` whose underlying scheme is affine, evaluation on the terminal object of
the slice is a bijection from the morphisms `G|_X ⟶ G'|_X` of quasi-coherent modules to the
`𝒪_F(X)`-linear maps `G(X) ⟶ G'(X)`. -/
theorem bijective_sliceHomEvaluation (X : SmallEtale B S hS F)
    (hX : IsAffine (chartScheme X)) {G G' : Modules.{u, u} B S hS F hF}
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) :
    Function.Bijective (sliceHomEvaluation B S hS F hF X (G := G) (G' := G')) := by
  obtain ⟨M, hM, hMs, ⟨eM⟩⟩ :=
    exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite B S hS ⟨F, hF⟩ X G hG hX
  obtain ⟨N, hN, hNs, ⟨eN⟩⟩ :=
    exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite B S hS ⟨F, hF⟩ X G' hG' hX
  have := hM
  have := hN
  have : IsAffine (chartScheme X) := hX
  have h := SheafOfModules.C1573.bijective_val_app_of_iso eM eN _
    (bijective_val_app_sliceAssociatedModule B S hS F hF X hMs hNs)
  exact ModuleCat.homEquiv.bijective.comp h

end AlgebraicGeometry.Space.C1573

end
