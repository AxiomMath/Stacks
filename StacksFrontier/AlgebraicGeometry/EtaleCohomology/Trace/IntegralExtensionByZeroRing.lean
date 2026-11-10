module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Integral base change and extension by zero, for an arbitrary coefficient ring

Let `Λ` be a ring, not necessarily commutative.  This file proves, for sheaves of `Λ`-modules on
small étale sites, the two comparisons that compute compactly supported cohomology along a
finite morphism:

* **integral base change** ([Stacks, Tag 0EYP]): for a cartesian square `i' ≫ g = g' ≫ i` with
  `i` integral the base change map `g^{-1} i_* ⟶ i'_* g'^{-1}` is an isomorphism;
* **extension by zero commutes with an integral direct image**: for a cartesian square
  ```
  V --j'--> V̄
  |f        |f̄
  v         v
  U --j---> Ū
  ```
  with `j` an open immersion and `f̄` integral, `j_!(f_* M) ⟶ f̄_*(j'_! M)` is an isomorphism.

Both are proved in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange`
and `...Trace.ExtensionByZeroIntegralDirectImage` for a commutative coefficient ring, which
those statements assume although their proofs never use it: the only inputs are the abelian
statement and the fact that forgetting the module structure is compatible with sheafification,
which holds for every ring (`Stacks.ModuleSheaf.hasSheafCompose_forget₂`).  The coefficient ring
of the Trace Formula chapter is a finite ring, not assumed commutative, which is why the
statements are made again here.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_app_of_isIntegralHom`.
* `Stacks.EtaleCohomology.extensionByZeroIntegralDirectImageMap` and
  `Stacks.EtaleCohomology.isIso_extensionByZeroIntegralDirectImageMap`.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Integral

variable (Λ : Type) [Ring Λ]

/-- Forgetting the `Λ`-module structure sends sheaves on the small étale site of `Z` to sheaves
of abelian groups, for any ring `Λ`. -/
local instance integralExtensionByZeroRing_hasSheafCompose_forget₂ (Z : Scheme.{u}) :
    Z.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Forgetting the `Λ`-module structure commutes with sheafification on the small étale site of
`Z`, for any ring `Λ`. -/
local instance integralExtensionByZeroRing_preservesSheafification_forget₂ (Z : Scheme.{u}) :
    Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)

/-- **Base change for an integral morphism, coefficients in an arbitrary ring
([Stacks, Tag 0EYP]).**  For a cartesian square `i' ≫ g = g' ≫ i` with `i` integral, the base
change map `g^{-1} i_* M ⟶ i'_* g'^{-1} M` of sheaves of `Λ`-modules is an isomorphism at every
`M`. -/
theorem isIso_etaleModuleBaseChange_app_of_isIntegralHom (sq : IsPullback i' g' g i)
    [IsIntegralHom i] (M : EtaleModules.{u, 0} Λ Z) :
    IsIso ((etaleModuleBaseChange Λ i i' g g' sq.w).app M) := by
  suffices IsIso (etaleModuleBaseChange Λ i i' g g' sq.w) from inferInstance
  let di : etaleModuleDirectImage.{u, 0} Λ i ⋙ etaleModuleUnderlyingAbelian (X := X) Λ ⟶
      etaleModuleUnderlyingAbelian (X := Z) Λ ⋙ smallEtalePushforwardAb i := 𝟙 _
  let di' : etaleModuleUnderlyingAbelian (X := Z') Λ ⋙ smallEtalePushforwardAb i' ⟶
      etaleModuleDirectImage.{u, 0} Λ i' ⋙ etaleModuleUnderlyingAbelian (X := X') Λ := 𝟙 _
  have : IsIso di := by
    change IsIso (𝟙 (etaleModuleDirectImage.{u, 0} Λ i ⋙ etaleModuleUnderlyingAbelian (X := X) Λ))
    infer_instance
  have : IsIso di' := by
    change IsIso (𝟙 (etaleModuleDirectImage.{u, 0} Λ i' ⋙ etaleModuleUnderlyingAbelian (X := X') Λ))
    infer_instance
  have hAb := isIso_smallEtaleBaseChangeAb_of_isIntegralHom g i i' g' sq
  rw [show smallEtaleBaseChangeAb g i i' g' sq.w = _ from
    Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _] at hAb
  have hhom : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (ab : A ⟶ C) (hab : ab = a ≫ b),
      (etaleAbelianDirectImageCompIso'.{u, 0} a b ab hab).hom =
        (etaleAbelianDirectImageCompIso'.{u, 0} a b (a ≫ b) rfl).hom ≫
          eqToHom (congrArg (fun m : A ⟶ C => etaleAbelianDirectImage.{u, 0} m) hab.symm) := by
    intro A B C a b ab hab
    subst hab
    simp
  have hcell : (smallEtalePushforwardAbCompIso g' i ≪≫
      eqToIso (congrArg smallEtalePushforwardAb sq.w.symm) ≪≫
        (smallEtalePushforwardAbCompIso i' g).symm).hom =
      (etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv := by
    rw [hhom, etaleAbelianDirectImageCompIso'_rfl, etaleAbelianDirectImageCompIso'_rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rfl
  rw [hcell] at hAb
  let T := TwoSquare.mk (smallEtalePushforwardAb g') (smallEtalePushforwardAb i')
    (smallEtalePushforwardAb i) (smallEtalePushforwardAb g)
    ((etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv)
  have hAb' : IsIso ((mateEquiv (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)).symm
      T) := hAb
  rw [etaleModuleBaseChange_eq_mateEquiv_symm]
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (etaleModuleInverseImageAdj.{u, 0} Λ g') (etaleModuleInverseImageAdj.{u, 0} Λ g)
    (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g') Z.smallEtaleTopology
      Z'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      X'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    di di' _ T ?_
  have key : ∀ {A B : Scheme.{u}} (h : B ⟶ A),
      mateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ h) (smallEtaleAdjunctionAb h)
        (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange h) A.smallEtaleTopology
          B.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) =
      coefficientPushforwardTwoSquare (smallEtaleBaseChange h) A.smallEtaleTopology
        B.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    fun h => Equiv.apply_symm_apply _ _
  rw [key g', key g]
  refine NatTrans.ext (funext fun M => ?_)
  refine Sheaf.hom_ext ?_
  refine NatTrans.ext (funext fun U => ?_)
  rfl

end Integral

section ExtensionByZero

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

/-- The isomorphism `f_* j'^{-1} ≅ j^{-1} f̄_*`: integral base change, with inverse image along
the étale maps `j`, `j'` read as restriction. -/
def restrictionIntegralDirectImageIso :
    etaleModuleRestriction.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ f ≅
      etaleModuleDirectImage.{u, 0} Λ fb ⋙ etaleModuleRestriction.{u, 0} Λ j :=
  haveI : ∀ M, IsIso ((etaleModuleBaseChange Λ fb f j j' sq.w).app M) :=
    isIso_etaleModuleBaseChange_app_of_isIntegralHom Λ fb f j j' sq
  haveI := NatIso.isIso_of_isIso_app (etaleModuleBaseChange Λ fb f j j' sq.w)
  Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').symm _ ≪≫
    (asIso (etaleModuleBaseChange Λ fb f j j' sq.w)).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j)

/-- **The canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)`**, adjoint under `j_! ⊣ j^{-1}` to the unit
of `j'_! ⊣ j'^{-1}` followed by `restrictionIntegralDirectImageIso`. -/
def extensionByZeroIntegralDirectImageMap (M : EtaleModules.{u, 0} Λ V) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f).obj M) ⟶
      (etaleModuleDirectImage.{u, 0} Λ fb).obj ((etaleModuleExtensionByZero.{u, 0} Λ j').obj M) :=
  ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).symm
    ((etaleModuleDirectImage.{u, 0} Λ f).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M) ≫
      (restrictionIntegralDirectImageIso Λ j j' f fb sq).hom.app _)

/-- **Extension by zero commutes with an integral direct image**, coefficients in an arbitrary
ring.  If `i : Z ⟶ Ub` is a closed immersion onto the complement of `U`, with base change
`i' : Z' ⟶ Vb` a closed immersion onto the complement of `V`, then
`j_!(f_* M) ⟶ f̄_*(j'_! M)` is an isomorphism. -/
theorem isIso_extensionByZeroIntegralDirectImageMap {Z Z' : Scheme.{u}} (i : Z ⟶ Ub)
    [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ) (i' : Z' ⟶ Vb)
    [IsClosedImmersion i'] (hij' : Set.range j'.base = (Set.range i'.base)ᶜ) (fZ : Z' ⟶ Z)
    (sqZ : IsPullback fZ i' i fb) (M : EtaleModules.{u, 0} Λ V) :
    IsIso (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M) := by
  have hU : IsIso ((etaleModuleInverseImage.{u, 0} Λ j).map
      (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)) := by
    have hR : IsIso ((etaleModuleRestriction.{u, 0} Λ j).map
        (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)) := by
      have h := Adjunction.homEquiv_unit (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) _ _
        (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)
      have h' : ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _)
          (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M) =
          (etaleModuleDirectImage.{u, 0} Λ f).map
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M) ≫
            (restrictionIntegralDirectImageIso Λ j j' f fb sq).hom.app _ :=
        Equiv.apply_symm_apply _ _
      have : IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
          ((etaleModuleDirectImage.{u, 0} Λ f).obj M) ≫ (etaleModuleRestriction.{u, 0} Λ j).map
            (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)) := by
        rw [← h, h']
        infer_instance
      exact IsIso.of_isIso_comp_left ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
        ((etaleModuleDirectImage.{u, 0} Λ f).obj M)) _
    have hn := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).hom.naturality
      (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)
    have : IsIso ((etaleModuleInverseImage.{u, 0} Λ j).map
        (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M) ≫
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).hom.app _) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).hom.app _)
  have hZ : IsIso ((etaleModuleInverseImage.{u, 0} Λ i).map
      (extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M)) := by
    have := isIso_etaleModuleBaseChange_app_of_isIntegralHom Λ fb fZ i i' sqZ
      ((etaleModuleExtensionByZero.{u, 0} Λ j').obj M)
    refine ⟨0, (isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _).eq_of_src _ _, ?_⟩
    refine IsZero.eq_of_src ?_ _ _
    exact ((etaleModuleDirectImage.{u, 0} Λ fZ).map_isZero
      (isZero_etaleModuleInverseImage_extensionByZero Λ i' j' hij' M)).of_iso
        (asIso ((etaleModuleBaseChange Λ fb fZ i i' sqZ.w).app _))
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

end ExtensionByZero

end Stacks.EtaleCohomology

end
