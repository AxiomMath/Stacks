module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.BimoduleHomFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions

/-!
# The Frobenius twist and a change of coefficients

Let `Gf : Mod_R ⥤ Mod_S` be a functor between categories of modules over two rings, applied
sectionwise to sheaves on small étale sites. It commutes on the nose with direct images, and up to
the canonical comparison `g^{-1} ∘ Gf ⟶ Gf ∘ g^{-1}` (the mate of that strict commutation) with
inverse images. The base change twists `g^{-1} ⟶ a_* ∘ g^{-1}` of
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist`, out of which the canonical action of the
geometric Frobenius on `RΓ_c(X_k̄, -)` is built, commute with `Gf` along that comparison. This is
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_restrictScalars` with restriction of scalars
replaced by an arbitrary coefficient functor; the argument is the same.

The functor `Gf` need not be exact. The case used is `Gf = Hom_{A[G]}(M^*, -)` in Step 7 of the
proof of [Stacks, Tag 03UG], for which the instances required here are supplied by
`ModuleCat.BimoduleHom.preservesSheafification` and
`ModuleCat.BimoduleHom.preservesFilteredColimitsOfSize_of_univLE`.

## Main results

* `ModuleCat.BimoduleHom.preservesSheafification`: `Hom_R(N, -)` commutes with sheafification
  for finite `R` and `N`.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_coefficient`: the base change twist commutes
  with a change of coefficients.
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_coefficient`: the same for the Frobenius base
  change twist.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 7.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe w r u v

namespace ModuleCat.BimoduleHom

variable {R S : Type r} [Ring R] [Ring S] [Finite R] (N : Type w) [AddCommGroup N] [Module R N]
  [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N] [Finite N] [Small.{w} S]

/-- `Hom_R(N, -)` preserves filtered colimits indexed by categories of every size `≤ w`. -/
theorem preservesFilteredColimitsOfSize_of_univLE [UnivLE.{u, w}] :
    PreservesFilteredColimitsOfSize.{u, u} (functor R S N) :=
  CategoryTheory.Limits.preservesFilteredColimitsOfSize_of_univLE.{w, w, u, u} _

/-- **`Hom_R(N, -)` commutes with sheafification**, for finite `R` and `N`: it preserves the
filtered colimits over covers and the limits that the plus construction is built from. -/
theorem preservesSheafification {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{max u v, w}] : J.PreservesSheafification (functor R S N) := by
  have hlimR : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{w} R) := ModuleCat.hasLimitsOfSize
  have hlimS : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{w} S) := ModuleCat.hasLimitsOfSize
  have hA : ∀ W : C, PreservesColimitsOfShape (J.Cover W)ᵒᵖ (forget (ModuleCat.{w} R)) :=
    fun W => Stacks.ModuleSheaf.preservesColimitsOfShape_forget_moduleCat.{w} R J W
  have hB : ∀ W : C, PreservesColimitsOfShape (J.Cover W)ᵒᵖ (forget (ModuleCat.{w} S)) :=
    fun W => Stacks.ModuleSheaf.preservesColimitsOfShape_forget_moduleCat.{w} S J W
  have : PreservesFilteredColimitsOfSize.{max u v, max u v} (functor R S N) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, r, max u v} N
  have : PreservesLimitsOfSize.{max u v, max u v} (functor R S N) :=
    preservesLimitsOfSize_of_univLE.{w, w} _
  exact GrothendieckTopology.instPreservesSheafification J (functor R S N)

end ModuleCat.BimoduleHom

namespace Stacks.EtaleCohomology

variable {R S : Type} [Ring R] [Ring S] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Gf]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op]

/-- The change of coefficients `Gf`, applied sectionwise to sheaves on `X_étale`. -/
abbrev etaleModuleCoefficient (X : Scheme.{u}) :
    EtaleModules.{u, 0} R X ⥤ EtaleModules.{u, 0} S X :=
  sheafCompose X.smallEtaleTopology Gf

section Twist

variable {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)

/-- The comparison `g^{-1} ∘ Gf ⟶ Gf ∘ g^{-1}` of inverse images. -/
abbrev inverseImageCoefficientTwoSquare :=
  coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) Y.smallEtaleTopology
    Y'.smallEtaleTopology Gf

/-- The component at `L` of the comparison `g^{-1} ∘ Gf ⟶ Gf ∘ g^{-1}`. -/
abbrev inverseImageCoefficientApp (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleInverseImage.{u, 0} S g).obj ((etaleModuleCoefficient Gf Y).obj L) ⟶
      (etaleModuleCoefficient Gf Y').obj ((etaleModuleInverseImage.{u, 0} R g).obj L) :=
  (inverseImageCoefficientTwoSquare Gf g).app L

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
/-- `Gf` applied to the unit of `g^{-1} ⊣ g_*` is the unit at `Gf(L)` followed by direct
image of the inverse-image comparison. -/
theorem coefficient_map_inverseImageAdj_unit (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleCoefficient Gf Y).map ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L) =
      (etaleModuleInverseImageAdj.{u, 0} S g).unit.app ((etaleModuleCoefficient Gf Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S g).map
          (inverseImageCoefficientApp Gf g L) :=
  coefficientSheafPullbackTwoSquare_unit _ _ _ _ L

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
/-- The composition isomorphism of direct images commutes with `Gf`. -/
theorem coefficient_mapIso_directImageComp_app {X Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    (fh : X ⟶ Z) (hfh : fh = f ≫ h) (F : EtaleModules.{u, 0} R X) :
    (etaleModuleCoefficient Gf Z).mapIso ((etaleModuleDirectImageComp.{u, 0} R f h fh hfh).app F) =
      (etaleModuleDirectImageComp.{u, 0} S f h fh hfh).app
        ((etaleModuleCoefficient Gf X).obj F) := by
  ext : 1
  apply Sheaf.hom_ext
  ext : 1
  rfl

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
/-- **The inverse-image comparison is natural in the coefficient functor**: for a natural
endomorphism `θ` of `Gf`, `g^{-1}(θ_L) ≫ c_L = c_L ≫ θ_{g^{-1} L}`. -/
theorem inverseImageCoefficientApp_naturality (θ : Gf ⟶ Gf) (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleInverseImage.{u, 0} S g).map ((sheafCompose_map Y.smallEtaleTopology θ).app L) ≫
        inverseImageCoefficientApp Gf g L =
      inverseImageCoefficientApp Gf g L ≫
        (sheafCompose_map Y'.smallEtaleTopology θ).app
          ((etaleModuleInverseImage.{u, 0} R g).obj L) := by
  apply ((etaleModuleInverseImageAdj.{u, 0} S g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := (etaleModuleInverseImageAdj.{u, 0} S g).unit.naturality
    ((sheafCompose_map Y.smallEtaleTopology θ).app L)
  have hc := coefficient_map_inverseImageAdj_unit Gf g L
  have hθ := (sheafCompose_map Y.smallEtaleTopology θ).naturality
    ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu, Category.assoc, ← hc]
  exact hθ.symm.trans ((congrArg (· ≫ (sheafCompose_map Y.smallEtaleTopology θ).app
    ((etaleModuleInverseImage.{u, 0} R g ⋙ etaleModuleDirectImage.{u, 0} R g).obj L)) hc).trans
      (Category.assoc _ _ _))

variable (ψ' : 𝟭 (EtaleModules.{u, 0} R Y) ⟶ etaleModuleDirectImage.{u, 0} R b)
  (ψ : 𝟭 (EtaleModules.{u, 0} S Y) ⟶ etaleModuleDirectImage.{u, 0} S b)
  (hψ : ∀ L, (etaleModuleCoefficient Gf Y).map (ψ'.app L) =
    ψ.app ((etaleModuleCoefficient Gf Y).obj L))

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
include hψ in
/-- The adjoint form of the base change twist commutes with `Gf`. -/
theorem etaleModuleBaseChangeTwistAdj_coefficient (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleCoefficient Gf Y).map ((etaleModuleBaseChangeTwistAdj R g a b w ψ').app L) =
      (etaleModuleBaseChangeTwistAdj S g a b w ψ).app ((etaleModuleCoefficient Gf Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S g).map ((etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientApp Gf g L)) := by
  simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]
  have e1 : (etaleModuleCoefficient Gf Y).map
      ((etaleModuleDirectImage.{u, 0} R b).map
        ((etaleModuleInverseImageAdj.{u, 0} R g).unit.app L)) =
      (etaleModuleDirectImage.{u, 0} S b).map
        ((etaleModuleInverseImageAdj.{u, 0} S g).unit.app ((etaleModuleCoefficient Gf Y).obj L) ≫
          (etaleModuleDirectImage.{u, 0} S g).map
            (inverseImageCoefficientApp Gf g L)) :=
    congrArg (etaleModuleDirectImage.{u, 0} S b).map
      (coefficient_map_inverseImageAdj_unit Gf g L)
  have e2 := congrArg Iso.hom (coefficient_mapIso_directImageComp_app Gf g b (a ≫ g) w
    ((etaleModuleInverseImage.{u, 0} R g).obj L))
  have e3 := congrArg Iso.inv (coefficient_mapIso_directImageComp_app Gf a g (a ≫ g) rfl
    ((etaleModuleInverseImage.{u, 0} R g).obj L))
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at e2 e3
  have hψL : (etaleModuleCoefficient Gf Y).map (ψ'.app L) =
      ψ.app ((etaleModuleCoefficient Gf Y).obj L) := hψ L
  rw [e1, e2, e3, Functor.map_comp]
  have n1 : (etaleModuleDirectImage.{u, 0} S b).map ((etaleModuleDirectImage.{u, 0} S g).map
        (inverseImageCoefficientApp Gf g L)) ≫
      (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.app
        ((etaleModuleCoefficient Gf Y').obj ((etaleModuleInverseImage.{u, 0} R g).obj L)) =
      (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.app _ ≫
        (etaleModuleDirectImage.{u, 0} S (a ≫ g)).map
          (inverseImageCoefficientApp Gf g L) :=
    (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.naturality _
  have n2 : (etaleModuleDirectImage.{u, 0} S (a ≫ g)).map
        (inverseImageCoefficientApp Gf g L) ≫
      (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.app
        ((etaleModuleCoefficient Gf Y').obj ((etaleModuleInverseImage.{u, 0} R g).obj L)) =
      (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.app _ ≫
        (etaleModuleDirectImage.{u, 0} S g).map ((etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientApp Gf g L)) :=
    (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.naturality _
  have n12 : (etaleModuleDirectImage.{u, 0} S b).map ((etaleModuleDirectImage.{u, 0} S g).map
        (inverseImageCoefficientApp Gf g L)) ≫
      (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.app
        ((etaleModuleCoefficient Gf Y').obj ((etaleModuleInverseImage.{u, 0} R g).obj L)) ≫
      (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.app
        ((etaleModuleCoefficient Gf Y').obj ((etaleModuleInverseImage.{u, 0} R g).obj L)) =
      (etaleModuleDirectImageComp.{u, 0} S g b (a ≫ g) w).hom.app _ ≫
      (etaleModuleDirectImageComp.{u, 0} S a g (a ≫ g) rfl).inv.app _ ≫
        (etaleModuleDirectImage.{u, 0} S g).map ((etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientApp Gf g L)) := by
    rw [reassoc_of% n1, n2]
  refine (congrArg (· ≫ _) hψL).trans (congrArg (ψ.app _ ≫ ·) ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) n12)

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
include hψ in
/-- **The base change twist commutes with restriction of scalars.** -/
theorem etaleModuleBaseChangeTwist_coefficient (L : EtaleModules.{u, 0} R Y) :
    (etaleModuleBaseChangeTwist S g a b w ψ).app ((etaleModuleCoefficient Gf Y).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S a).map
          (inverseImageCoefficientApp Gf g L) =
      inverseImageCoefficientApp Gf g L ≫
        (etaleModuleCoefficient Gf Y').map ((etaleModuleBaseChangeTwist R g a b w ψ').app L) := by
  have hT : ∀ (Λ₀ : Type) [Ring Λ₀] (ψ₀ : 𝟭 (EtaleModules.{u, 0} Λ₀ Y) ⟶
      etaleModuleDirectImage.{u, 0} Λ₀ b) (M : EtaleModules.{u, 0} Λ₀ Y),
      (etaleModuleInverseImageAdj.{u, 0} Λ₀ g).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ₀ g).map
          ((etaleModuleBaseChangeTwist Λ₀ g a b w ψ₀).app M) =
        (etaleModuleBaseChangeTwistAdj Λ₀ g a b w ψ₀).app M := by
    intro Λ₀ _ ψ₀ M
    rw [etaleModuleBaseChangeTwist_app]
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  apply ((etaleModuleInverseImageAdj.{u, 0} S g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp,
    reassoc_of% (hT S ψ ((etaleModuleCoefficient Gf Y).obj L)),
    ← etaleModuleBaseChangeTwistAdj_coefficient Gf g a b w ψ' ψ hψ L, ← hT R ψ' L,
    Functor.map_comp]
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact (congrArg (· ≫ _) (coefficient_map_inverseImageAdj_unit Gf g L)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((etaleModuleDirectImage.{u, 0} S g).map_comp (inverseImageCoefficientApp Gf g L)
        ((etaleModuleCoefficient Gf Y').map
          ((etaleModuleBaseChangeTwist R g a b w ψ').app L))).symm))

end Twist

/-! ### The Frobenius twist -/

section Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
/-- The Frobenius descent isomorphism of [Tag 03SR] commutes with restriction of scalars: on
sections it is a restriction map of the sheaf. -/
theorem coefficient_map_geometricFrobeniusPushforwardIso (L : EtaleModules.{u, 0} R Y.left) :
    (etaleModuleCoefficient Gf Y.left).map
        ((geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} R)).hom.app L) =
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} S)).hom.app
        ((etaleModuleCoefficient Gf Y.left).obj L) := by
  apply Sheaf.hom_ext
  ext U : 2
  refine (congrArg Gf.map (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard
    (ModuleCat.{u + 1} R) L U.unop)).trans ?_
  exact (geometricFrobeniusPushforwardIso_hom_app_hom_app Y p q hcard (ModuleCat.{u + 1} S)
    ((etaleModuleCoefficient Gf Y.left).obj L) U.unop).symm

omit [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op] in
/-- **The Frobenius base change twist commutes with restriction of scalars.** -/
theorem frobeniusBaseChangeTwist_coefficient (L : EtaleModules.{u, 0} R Y.left) :
    (frobeniusBaseChangeTwist.{u, 0} S Y kbar p q hcard).app
        ((etaleModuleCoefficient Gf Y.left).obj L) ≫
        (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (inverseImageCoefficientApp Gf (fieldBaseChangeProj Y kbar) L) =
      inverseImageCoefficientApp Gf (fieldBaseChangeProj Y kbar) L ≫
        (etaleModuleCoefficient Gf (fieldBaseChange Y kbar)).map
          ((frobeniusBaseChangeTwist.{u, 0} R Y kbar p q hcard).app L) :=
  etaleModuleBaseChangeTwist_coefficient Gf _ _ _ _ _ _
    (coefficient_map_geometricFrobeniusPushforwardIso Gf Y p q hcard) L

end Frobenius

end Stacks.EtaleCohomology

end
