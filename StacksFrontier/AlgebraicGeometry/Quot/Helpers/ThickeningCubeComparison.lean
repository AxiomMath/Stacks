module

public import StacksFrontier.Deformation.ToposThickening.Helpers.AdjunctionCubeMate

/-!
# The mate of a map of pulled-back ideals around a cube of algebraic spaces

For a commutative cube of algebraic spaces — on top `i₂ : V ⟶ W`, `j : W ⟶ X`, `i₂ ≫ j = i₁`,
on the bottom `t₂ : T ⟶ T₂`, `γ : T₂ ⟶ T₁`, `t₂ ≫ γ = t₁`, vertical `p`, `f₂`, `f₁` — the
comparisons of inverse images of modules of Stacks 03LU around its sides are the mates of the
comparisons of direct images, which are associative. So the mate calculus of
`Deformation.ToposThickening.homEquiv_sq_comp_map_comp_sq_inv` applies: a map of pulled-back
modules `λ : t₁^*N₁ ⟶ t₂^*N₂` adjoint to `κ : N₁ ⟶ γ_*N₂` followed by the unit of `t₂` induces,
on the top, the map adjoint to the corresponding map `f₁^*N₁ ⟶ j_*f₂^*N₂`
(`AlgebraicGeometry.Space.homEquiv_cubeSideIso_comp_map_comp_cubeSideIso_inv`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

-- The instance search of `AlgebraicGeometry.Space.homEquiv_thickeningIdealMap`'s file, so that the
-- instance terms of the small étale sites agree with it.
attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The comparisons `f_* ⋙ g_* ≅ k_*` of direct images are associative.** -/
theorem modulePushforwardCompIsoOfEq_assoc {W X Y Z : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (k : W ⟶ Z) (hfg : f ≫ g = fg)
    (hgh : g ≫ h = gh) (hk₁ : fg ≫ h = k) (hk₂ : f ≫ gh = k) :
    isoWhiskerLeft (smallEtaleRingedToposHom B S hS f).pushforwardModules
        (modulePushforwardCompIsoOfEq g h gh hgh) ≪≫ modulePushforwardCompIsoOfEq f gh k hk₂ =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIsoOfEq f g fg hfg)
          (smallEtaleRingedToposHom B S hS h).pushforwardModules ≪≫
        modulePushforwardCompIsoOfEq fg h k hk₁ := by
  subst hfg hgh hk₁
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  have e := pushforwardModulesCompAt_assoc B S hS f g h M
  simp only [pushforwardModulesCompAt_eq_modulePushforwardCompIso'] at e
  simp only [modulePushforwardCompIsoOfEq, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, eqToIso.hom,
    Functor.associator_inv_app, Category.id_comp, eqToHom_refl, Category.comp_id]
  exact e.symm

/-- The category of modules on the small étale ringed topos of an algebraic space, the source and
target of the adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`. -/
abbrev spaceModules (X : AlgebraicSpaces B S hS) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)

/-- The category structure of `AlgebraicGeometry.Space.spaceModules`, with the instance terms of
the adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`. -/
abbrev spaceModulesCategory (X : AlgebraicSpaces B S hS) : Category (spaceModules X) :=
  inferInstance

/-- The adjunction `f^* ⊣ f_*` of modules along a morphism of algebraic spaces. -/
abbrev spaceModuleAdj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ⊣
      (smallEtaleRingedToposHom B S hS f).pushforwardModules :=
  RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f)

variable {V W X T T₂ T₁ : AlgebraicSpaces B S hS} (i₂ : V ⟶ W) (j : W ⟶ X) (i₁ : V ⟶ X)
  (hi : i₂ ≫ j = i₁) (p : V ⟶ T) (f₂ : W ⟶ T₂) (f₁ : X ⟶ T₁) (t₂ : T ⟶ T₂) (γ : T₂ ⟶ T₁)
  (t₁ : T ⟶ T₁) (ht : t₂ ≫ γ = t₁) (k : W ⟶ T₁) (hk : j ≫ f₁ = k) (hk' : f₂ ≫ γ = k)
  (k₁ : V ⟶ T₁) (h₁ : i₁ ≫ f₁ = k₁) (h₁' : p ≫ t₁ = k₁) (k₂ : V ⟶ T₂) (h₂ : i₂ ≫ f₂ = k₂)
  (h₂' : p ≫ t₂ = k₂)

/-- **The comparison of inverse images around a side of the cube** (Stacks 03LU): for
`i ≫ f = k = p ≫ t`, the comparison `f^* ⋙ i^* ≅ k^* ≅ t^* ⋙ p^*`. -/
abbrev spaceCubeSideIso {Y T' : AlgebraicSpaces B S hS} (i : V ⟶ Y) (f : Y ⟶ T')
    (t : T ⟶ T') (kk : V ⟶ T') (hf : i ≫ f = kk) (ht' : p ≫ t = kk) :=
  Deformation.ToposThickening.cubeSideIso (spaceModuleAdj p) (spaceModuleAdj i) (spaceModuleAdj f)
    (spaceModuleAdj t) (spaceModuleAdj kk) (modulePushforwardCompIsoOfEq i f kk hf)
    (modulePushforwardCompIsoOfEq p t kk ht')

include hi hk h₁ in
/-- `i₂ ≫ k = k₁` for the diagonals of the cube. -/
theorem comp_eq_of_cube_top : i₂ ≫ k = k₁ := by
  rw [← hk, ← Category.assoc, hi, h₁]

include ht h₁' h₂' in
/-- `k₂ ≫ γ = k₁` for the diagonals of the cube. -/
theorem comp_eq_of_cube_bottom : k₂ ≫ γ = k₁ := by
  rw [← h₂', Category.assoc, ht, h₁']

/-- The three associativity constraints of the comparisons of direct images around the cube. -/
private theorem cube_modulePushforwardCompIsoOfEq_assoc :
    isoWhiskerLeft (smallEtaleRingedToposHom B S hS i₂).pushforwardModules
        (modulePushforwardCompIsoOfEq j f₁ k hk) ≪≫
        modulePushforwardCompIsoOfEq i₂ k k₁ (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁) =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIsoOfEq i₂ j i₁ hi)
          (smallEtaleRingedToposHom B S hS f₁).pushforwardModules ≪≫
        modulePushforwardCompIsoOfEq i₁ f₁ k₁ h₁ ∧
    isoWhiskerLeft (smallEtaleRingedToposHom B S hS i₂).pushforwardModules
        (modulePushforwardCompIsoOfEq f₂ γ k hk') ≪≫
        modulePushforwardCompIsoOfEq i₂ k k₁ (comp_eq_of_cube_top i₂ j i₁ hi f₁ k hk k₁ h₁) =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIsoOfEq i₂ f₂ k₂ h₂)
          (smallEtaleRingedToposHom B S hS γ).pushforwardModules ≪≫
        modulePushforwardCompIsoOfEq k₂ γ k₁ (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂') ∧
    isoWhiskerLeft (smallEtaleRingedToposHom B S hS p).pushforwardModules
        (modulePushforwardCompIsoOfEq t₂ γ t₁ ht) ≪≫ modulePushforwardCompIsoOfEq p t₁ k₁ h₁' =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIsoOfEq p t₂ k₂ h₂')
          (smallEtaleRingedToposHom B S hS γ).pushforwardModules ≪≫
        modulePushforwardCompIsoOfEq k₂ γ k₁ (comp_eq_of_cube_bottom p t₂ γ t₁ ht k₁ h₁' k₂ h₂') :=
  ⟨modulePushforwardCompIsoOfEq_assoc i₂ j f₁ i₁ k k₁ hi hk h₁ _,
    modulePushforwardCompIsoOfEq_assoc i₂ f₂ γ k₂ k k₁ h₂ hk' _ _,
    modulePushforwardCompIsoOfEq_assoc p t₂ γ k₂ t₁ k₁ h₂' ht _ h₁'⟩

/-- **The mate of a map of pulled-back modules around a cube of algebraic spaces.** For
`κ : N₁ ⟶ γ_*N₂` and `λ : t₁^*N₁ ⟶ t₂^*N₂` adjoint to `κ` followed by the unit of `t₂`, the map
`i₁^*f₁^*N₁ ≅ p^*t₁^*N₁ ⟶ p^*t₂^*N₂ ≅ i₂^*f₂^*N₂` is adjoint under `i₁^* ⊣ i₁_*` to the map
`f₁^*N₁ ⟶ j_*f₂^*N₂` adjoint to `κ` followed by the unit of `f₂`, followed by `j_*` of the unit
of `i₂` and `j_*i₂_* ≅ i₁_*`. -/
theorem homEquiv_cubeSideIso_comp_map_comp_cubeSideIso_inv
    {N₁ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₁).O)}
    {N₂ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₂).O)}
    (κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂)
    (lam : (smallEtaleRingedToposHom B S hS t₁).toModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toModulesHom.pullbackModules.obj N₂)
    (hlam : (spaceModuleAdj t₁).homEquiv _ _ lam =
      κ ≫ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.map
          ((spaceModuleAdj t₂).unit.app N₂) ≫
        (modulePushforwardCompIsoOfEq t₂ γ t₁ ht).hom.app _) :
    (spaceModuleAdj i₁).homEquiv _ _
        (Deformation.ToposThickening.cubeSideMap (ap := spaceModuleAdj p)
          (ai₁ := spaceModuleAdj i₁)
          (ai₂ := spaceModuleAdj i₂) (af₁ := spaceModuleAdj f₁) (af₂ := spaceModuleAdj f₂)
          (at₁ := spaceModuleAdj t₁) (at₂ := spaceModuleAdj t₂) (ak₁ := spaceModuleAdj k₁)
          (ak₂ := spaceModuleAdj k₂) (a₁ := modulePushforwardCompIsoOfEq i₁ f₁ k₁ h₁)
          (b₁ := modulePushforwardCompIsoOfEq p t₁ k₁ h₁')
          (a₂ := modulePushforwardCompIsoOfEq i₂ f₂ k₂ h₂)
          (b₂ := modulePushforwardCompIsoOfEq p t₂ k₂ h₂') lam) =
      Deformation.ToposThickening.cubeTopMap (ai₂ := spaceModuleAdj i₂)
        (af₁ := spaceModuleAdj f₁) (af₂ := spaceModuleAdj f₂)
        (ci := modulePushforwardCompIsoOfEq i₂ j i₁ hi)
        (d₁ := modulePushforwardCompIsoOfEq j f₁ k hk)
        (d₂ := modulePushforwardCompIsoOfEq f₂ γ k hk') κ := by
  have h := cube_modulePushforwardCompIsoOfEq_assoc i₂ j i₁ hi p f₂ f₁ t₂ γ t₁ ht k
    hk hk' k₁ h₁ h₁' k₂ h₂ h₂'
  exact Deformation.ToposThickening.homEquiv_sq_comp_map_comp_sq_inv (spaceModuleAdj i₁)
    (spaceModuleAdj i₂) (spaceModuleAdj j) (spaceModuleAdj p) (spaceModuleAdj f₁)
    (spaceModuleAdj f₂) (spaceModuleAdj t₁) (spaceModuleAdj t₂) (spaceModuleAdj γ)
    (spaceModuleAdj k₁) (spaceModuleAdj k₂) (spaceModuleAdj k) _ _ _ _ _ _ _ _ _ _
    h.1 h.2.1 h.2.2 κ lam hlam

/-- `AlgebraicGeometry.Space.homEquiv_cubeSideIso_comp_map_comp_cubeSideIso_inv` followed by a map
`y : i₂^*f₂^*N₂ ⟶ Q`: the transpose is `Deformation.ToposThickening.cubeTopTranspose` followed by
`j_*` of the transpose of `y` and `j_*i₂_* ≅ i₁_*`. -/
theorem homEquiv_cubeSideMap_comp_eq_cubeTopTranspose_comp
    {N₁ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₁).O)}
    {N₂ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₂).O)}
    (κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂)
    (lam : (smallEtaleRingedToposHom B S hS t₁).toModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toModulesHom.pullbackModules.obj N₂)
    (hlam : (spaceModuleAdj t₁).homEquiv _ _ lam =
      κ ≫ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.map
          ((spaceModuleAdj t₂).unit.app N₂) ≫
        (modulePushforwardCompIsoOfEq t₂ γ t₁ ht).hom.app _)
    {Q : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS V).O)}
    (y : (smallEtaleRingedToposHom B S hS i₂).toModulesHom.pullbackModules.obj
      ((smallEtaleRingedToposHom B S hS f₂).toModulesHom.pullbackModules.obj N₂) ⟶ Q) :
    (spaceModuleAdj i₁).homEquiv _ _
        (Deformation.ToposThickening.cubeSideMap (ap := spaceModuleAdj p)
          (ai₁ := spaceModuleAdj i₁)
          (ai₂ := spaceModuleAdj i₂) (af₁ := spaceModuleAdj f₁) (af₂ := spaceModuleAdj f₂)
          (at₁ := spaceModuleAdj t₁) (at₂ := spaceModuleAdj t₂) (ak₁ := spaceModuleAdj k₁)
          (ak₂ := spaceModuleAdj k₂) (a₁ := modulePushforwardCompIsoOfEq i₁ f₁ k₁ h₁)
          (b₁ := modulePushforwardCompIsoOfEq p t₁ k₁ h₁')
          (a₂ := modulePushforwardCompIsoOfEq i₂ f₂ k₂ h₂)
          (b₂ := modulePushforwardCompIsoOfEq p t₂ k₂ h₂') lam ≫ y) =
      Deformation.ToposThickening.cubeTopTranspose (spaceModuleAdj f₁) (spaceModuleAdj f₂)
          (modulePushforwardCompIsoOfEq j f₁ k hk) (modulePushforwardCompIsoOfEq f₂ γ k hk') κ ≫
        (smallEtaleRingedToposHom B S hS j).pushforwardModules.map
          ((spaceModuleAdj i₂).homEquiv _ _ y) ≫
        (modulePushforwardCompIsoOfEq i₂ j i₁ hi).hom.app Q := by
  have h := cube_modulePushforwardCompIsoOfEq_assoc i₂ j i₁ hi p f₂ f₁ t₂ γ t₁ ht k
    hk hk' k₁ h₁ h₁' k₂ h₂ h₂'
  exact Deformation.ToposThickening.homEquiv_cubeSideMap_comp (spaceModuleAdj i₁)
    (spaceModuleAdj i₂) (spaceModuleAdj j) (spaceModuleAdj p) (spaceModuleAdj f₁)
    (spaceModuleAdj f₂) (spaceModuleAdj t₁) (spaceModuleAdj t₂) (spaceModuleAdj γ)
    (spaceModuleAdj k₁) (spaceModuleAdj k₂) (spaceModuleAdj k) _ _ _ _ _ _ _ _ _ _
    h.1 h.2.1 h.2.2 κ lam hlam y

end AlgebraicGeometry.Space
