module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius

/-!
# The Frobenius twist commutes with a sectionwise change of coefficients

Let `Φ : Mod_R ⥤ Mod_Λ` be a functor preserving limits, applied sectionwise to sheaves on the
small étale sites. It commutes on the nose with every direct image, and the comparison
`g^{-1}(Φ L) ⟶ Φ(g^{-1} L)` for an inverse image is the mate
`Stacks.EtaleCohomology.coefficientMate`. This file shows that this comparison intertwines the
base change twists `g^{-1} ⟶ a_* g^{-1}` (`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist`)
for `R` and for `Λ`, provided the transformations `𝟭 ⟶ b_*` they are built from correspond under
`Φ`. For the Frobenius base change twist of `RΓ_c` this holds, the Frobenius descent isomorphism
being restriction of sections.

The comparison `Φ(L)|_{X̄_k̄} ⟶ Φ(L|_{X̄_k̄})` composed with extension by zero is then a morphism
of twisted complexes, which is how `π_X^*` on `RΓ_c(X_k̄, Hom_R(M, D))` is compared with `π_X^*` on
`RΓ_c(X_k̄, D)` in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_app_comp_coefficientMate`
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_app_comp_coefficientMate`
* `Stacks.EtaleCohomology.compactSupportCoefficientMate` and its compatibility with the Frobenius
  twists, `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_app_comp_compactSupportCoefficientMate`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Mate

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {L₁ : C₁ ⥤ C₂} {P₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ P₁) {L₂ : D₁ ⥤ D₂} {P₂ : D₂ ⥤ D₁} (adj₂ : L₂ ⊣ P₂)

/-- The adjoint of the mate of a square `β` is `Ψ₁` of the unit followed by `β`. -/
lemma homEquiv_strictMate_app {Ψ₁ : C₁ ⥤ D₁} {Ψ₂ : C₂ ⥤ D₂} (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂) (X : C₁) :
    adj₂.homEquiv _ _ ((strictMate adj₁ adj₂ β).app X) =
      Ψ₁.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) := by
  rw [strictMate_app, ← L₂.map_comp_assoc, Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [Adjunction.right_triangle_components, Category.comp_id]

end Mate

section Twist

variable {R Λ : Type} [Ring R] [Ring Λ] (Φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} Λ)
  [PreservesLimits Φ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y)
  (w : a ≫ g = g ≫ b)
  (ψR : 𝟭 (EtaleModules.{u, 0} R Y) ⟶ etaleModuleDirectImage.{u, 0} R b)
  (ψΛ : 𝟭 (EtaleModules.{u, 0} Λ Y) ⟶ etaleModuleDirectImage.{u, 0} Λ b)

/-- The comparison `g^{-1}(Φ L) ⟶ Φ(g^{-1} L)` for an inverse image. -/
abbrev inverseImageCoefficientMate :
    sheafCompose Y.smallEtaleTopology Φ ⋙ etaleModuleInverseImage.{u, 0} Λ g ⟶
      etaleModuleInverseImage.{u, 0} R g ⋙ sheafCompose Y'.smallEtaleTopology Φ :=
  coefficientMate (smallEtaleBaseChange g) (etaleModuleInverseImageAdj.{u, 0} R g)
    (etaleModuleInverseImage.{u, 0} Λ g) (etaleModuleInverseImageAdj.{u, 0} Λ g) Φ

include w in
/-- The composition isomorphisms of direct images commute with `Φ`. -/
lemma directImageComp_sheafCompose (G : EtaleModules.{u, 0} R Y') :
    (etaleModuleDirectImageComp.{u, 0} Λ g b (a ≫ g) w).hom.app
        ((sheafCompose Y'.smallEtaleTopology Φ).obj G) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ a g (a ≫ g) rfl).inv.app
        ((sheafCompose Y'.smallEtaleTopology Φ).obj G) =
      (sheafCompose Y.smallEtaleTopology Φ).map
        ((etaleModuleDirectImageComp.{u, 0} R g b (a ≫ g) w).hom.app G ≫
          (etaleModuleDirectImageComp.{u, 0} R a g (a ≫ g) rfl).inv.app G) :=
  by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  show (𝟙 _ ≫ Φ.map (G.obj.map _)) ≫ (𝟙 _ ≫ Φ.map (G.obj.map _)) =
    Φ.map ((𝟙 _ ≫ G.obj.map _) ≫ (𝟙 _ ≫ G.obj.map _))
  simp only [Category.id_comp, Functor.map_comp]

/-- **The base change twist commutes with the comparison of coefficients**, when the
transformations `ψ_R : 𝟭 ⟶ b_*` and `ψ_Λ : 𝟭 ⟶ b_*` correspond under `Φ`. -/
theorem etaleModuleBaseChangeTwist_app_comp_coefficientMate
    (hψ : ∀ L, ψΛ.app ((sheafCompose Y.smallEtaleTopology Φ).obj L) =
      (sheafCompose Y.smallEtaleTopology Φ).map (ψR.app L))
    (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψΛ).app
        ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
      (etaleModuleDirectImage.{u, 0} Λ a).map ((inverseImageCoefficientMate Φ g).app L) =
    (inverseImageCoefficientMate Φ g).app L ≫
      (sheafCompose Y'.smallEtaleTopology Φ).map
        ((etaleModuleBaseChangeTwist.{u, 0} R g a b w ψR).app L) := by
  set c := (inverseImageCoefficientMate Φ g).app L with hcdef
  have hc : (etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app
        ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).map c =
      (sheafCompose Y.smallEtaleTopology Φ).map
        ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L) := by
    have h := homEquiv_strictMate_app (etaleModuleInverseImageAdj.{u, 0} R g)
      (etaleModuleInverseImageAdj.{u, 0} Λ g) (Ψ₁ := sheafCompose Y.smallEtaleTopology Φ)
      (Ψ₂ := sheafCompose Y'.smallEtaleTopology Φ) (𝟙 _) L
    rw [Adjunction.homEquiv_unit] at h
    exact h.trans (Category.comp_id _)
  have hN := ((etaleModuleDirectImageComp.{u, 0} Λ g b (a ≫ g) w).hom ≫
    (etaleModuleDirectImageComp.{u, 0} Λ a g (a ≫ g) rfl).inv).naturality c
  dsimp only [Functor.comp_map, Functor.comp_obj] at hN
  have e0 : (etaleModuleBaseChangeTwistAdj.{u, 0} Λ g a b w ψΛ).app
        ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).map ((etaleModuleDirectImage.{u, 0} Λ a).map c) =
      ψΛ.app ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ b).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app
          ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).map c) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ g b (a ≫ g) w).hom.app
          ((sheafCompose Y'.smallEtaleTopology Φ).obj
            ((etaleModuleInverseImage.{u, 0} R g).obj L)) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ a g (a ≫ g) rfl).inv.app
          ((sheafCompose Y'.smallEtaleTopology Φ).obj
            ((etaleModuleInverseImage.{u, 0} R g).obj L)) := by
    simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
      Functor.comp_obj, Functor.id_obj] at hN ⊢
    rw [← hN, Functor.map_comp, Category.assoc]
  have e4 : (sheafCompose Y.smallEtaleTopology Φ).map
      ((etaleModuleBaseChangeTwistAdj.{u, 0} R g a b w ψR).app L) =
      (sheafCompose Y.smallEtaleTopology Φ).map (ψR.app L) ≫
        (sheafCompose Y.smallEtaleTopology Φ).map ((etaleModuleDirectImage.{u, 0} R b).map
          ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L)) ≫
        (sheafCompose Y.smallEtaleTopology Φ).map
          ((etaleModuleDirectImageComp.{u, 0} R g b (a ≫ g) w).hom.app
            ((etaleModuleInverseImage.{u, 0} R g).obj L) ≫
          (etaleModuleDirectImageComp.{u, 0} R a g (a ≫ g) rfl).inv.app
            ((etaleModuleInverseImage.{u, 0} R g).obj L)) := by
    simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.map_comp,
      Functor.comp_obj, Functor.id_obj, Functor.map_id, Category.assoc]
  have key : (etaleModuleBaseChangeTwistAdj.{u, 0} Λ g a b w ψΛ).app
        ((sheafCompose Y.smallEtaleTopology Φ).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).map ((etaleModuleDirectImage.{u, 0} Λ a).map c) =
      (sheafCompose Y.smallEtaleTopology Φ).map
        ((etaleModuleBaseChangeTwistAdj.{u, 0} R g a b w ψR).app L) :=
    by rw [e0, hc, hψ L, directImageComp_sheafCompose Φ g a b w]; exact e4.symm
  have hT := fun {S : Type} [Ring S] (ψ : 𝟭 (EtaleModules.{u, 0} S Y) ⟶
      etaleModuleDirectImage.{u, 0} S b) (X : EtaleModules.{u, 0} S Y) =>
    (congrArg ((etaleModuleInverseImageAdj.{u, 0} S g).homEquiv _ _)
      (etaleModuleBaseChangeTwist_app.{u, 0} S g a b w ψ X)).trans (Equiv.apply_symm_apply _ _)
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ g).homEquiv _ _).injective
  refine ((etaleModuleInverseImageAdj.{u, 0} Λ g).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (etaleModuleDirectImage.{u, 0} Λ g).map
    ((etaleModuleDirectImage.{u, 0} Λ a).map c)) (hT ψΛ _)).trans ?_
  refine key.trans ?_
  refine Eq.trans ?_ ((etaleModuleInverseImageAdj.{u, 0} Λ g).homEquiv_naturality_right _ _).symm
  rw [Adjunction.homEquiv_unit, ← hT ψR L, Adjunction.homEquiv_unit, Functor.map_comp]
  exact congrArg (· ≫ (etaleModuleDirectImage.{u, 0} Λ g).map
    ((sheafCompose Y'.smallEtaleTopology Φ).map
      ((etaleModuleBaseChangeTwist.{u, 0} R g a b w ψR).app L))) hc.symm

end Twist

section Frobenius

variable {R Λ : Type} [Ring R] [Ring Λ] (Φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} Λ)
  [PreservesLimits Φ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The Frobenius descent isomorphism `L ≅ (π_Y)_* L` commutes with `Φ`: it is restriction of
sections. -/
lemma geometricFrobeniusPushforwardIso_hom_app_sheafCompose (L : EtaleModules.{u, 0} R Y.left) :
    (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} Λ)).hom.app
        ((sheafCompose Y.left.smallEtaleTopology Φ).obj L) =
      (sheafCompose Y.left.smallEtaleTopology Φ).map
        ((geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} R)).hom.app L) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  induction U using Opposite.rec with | op U => ?_
  exact (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard _ _ U).trans
    (congrArg Φ.map (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard _ L U).symm)

/-- **The Frobenius base change twist commutes with the comparison of coefficients** for the
inverse image along `Y_k̄ ⟶ Y`. -/
theorem frobeniusBaseChangeTwist_app_comp_coefficientMate (L : EtaleModules.{u, 0} R Y.left) :
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
        ((sheafCompose Y.left.smallEtaleTopology Φ).obj L) ≫
      (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        ((inverseImageCoefficientMate Φ (fieldBaseChangeProj Y kbar)).app L) =
    (inverseImageCoefficientMate Φ (fieldBaseChangeProj Y kbar)).app L ≫
      (sheafCompose (fieldBaseChange Y kbar).smallEtaleTopology Φ).map
        ((frobeniusBaseChangeTwist.{u, 0} R Y kbar p q hcard).app L) :=
  etaleModuleBaseChangeTwist_app_comp_coefficientMate Φ _ _ _ _ _ _
    (geometricFrobeniusPushforwardIso_hom_app_sheafCompose Φ Y p q hcard) L

variable {X : Scheme.{u}} (j : X ⟶ Y.left) [Etale j]

/-- The comparison `Φ(L)|_{X̄_k̄} ⟶ Φ(L|_{X̄_k̄})` composed with extension by zero along
`j : X ⟶ X̄`: `(j_! Φ G)|_{X̄_k̄} ⟶ Φ((j_! G)|_{X̄_k̄})`. -/
def compactSupportCoefficientMate :
    (sheafCompose X.smallEtaleTopology Φ ⋙ etaleModuleExtensionByZero.{u, 0} Λ j) ⋙
        etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar) ⟶
      (etaleModuleExtensionByZero.{u, 0} R j ⋙
        etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y kbar)) ⋙
          sheafCompose (fieldBaseChange Y kbar).smallEtaleTopology Φ :=
  Functor.whiskerRight (coefficientMate (Scheme.Etale.smallEtaleCompose j)
      (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) Φ)
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} R j)
      (inverseImageCoefficientMate Φ (fieldBaseChangeProj Y kbar)) ≫
    (Functor.associator _ _ _).inv

/-- The component of `compactSupportCoefficientMate` at `G` is the inverse image of the component
of the extension-by-zero comparison, followed by the inverse image comparison at `j_! G`. -/
lemma compactSupportCoefficientMate_app (G : EtaleModules.{u, 0} R X) :
    (compactSupportCoefficientMate Φ Y kbar j).app G =
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
          ((coefficientMate (Scheme.Etale.smallEtaleCompose j)
            (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} Λ j)
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) Φ).app G) ≫
        (inverseImageCoefficientMate Φ (fieldBaseChangeProj Y kbar)).app
          ((etaleModuleExtensionByZero.{u, 0} R j).obj G) := by
  simp [compactSupportCoefficientMate]

/-- **The comparison for `RΓ_c` is a morphism of twisted objects**: it intertwines the Frobenius
base change twists of `(j_! Φ G)|_{X̄_k̄}` and of `(j_! G)|_{X̄_k̄}`. -/
theorem frobeniusBaseChangeTwist_app_comp_compactSupportCoefficientMate
    (G : EtaleModules.{u, 0} R X) :
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
        ((etaleModuleExtensionByZero.{u, 0} Λ j).obj
          ((sheafCompose X.smallEtaleTopology Φ).obj G)) ≫
      (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        ((compactSupportCoefficientMate Φ Y kbar j).app G) =
    (compactSupportCoefficientMate Φ Y kbar j).app G ≫
      (sheafCompose (fieldBaseChange Y kbar).smallEtaleTopology Φ).map
        ((frobeniusBaseChangeTwist.{u, 0} R Y kbar p q hcard).app
          ((etaleModuleExtensionByZero.{u, 0} R j).obj G)) := by
  rw [compactSupportCoefficientMate_app, Functor.map_comp]
  have h₁ := (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).naturality
    ((coefficientMate (Scheme.Etale.smallEtaleCompose j)
      (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) Φ).app G)
  have h₂ := frobeniusBaseChangeTwist_app_comp_coefficientMate Φ Y kbar p q hcard
    ((etaleModuleExtensionByZero.{u, 0} R j).obj G)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁
  rw [← Category.assoc, ← h₁, Category.assoc]
  exact congrArg ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
    ((coefficientMate (Scheme.Etale.smallEtaleCompose j)
      (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) Φ).app G) ≫ ·) h₂ |>.trans
    (Category.assoc _ _ _).symm

end Frobenius

end Stacks.EtaleCohomology
