module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCochain
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.DirectImageCompCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Horizontal pasting of the base change maps of sheaves of `Λ`-modules

Consider two commutative squares of schemes side by side,
```
X₁' --a'--> X₂' --b'--> X₃'
|h₁         |h₂         |h₃
v           v           v
X₁  --a-->  X₂  --b-->  X₃
```
The base change map `g⁻¹ h_* ⟶ g'⁻¹ h'_*` of a square
(`Stacks.EtaleCohomology.etaleModuleBaseChangeGeneral` on sheaves,
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeGeneral` on `D(-_étale, Λ)`) is taken along the
horizontal arrows. This file proves that the base change map of the outer rectangle is the
composite of the base change maps of the two squares, read through the composition isomorphisms
`(a ≫ b)⁻¹ ≅ b⁻¹ ⋙ a⁻¹` of inverse images. The vertical pasting is
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange_vComp`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImageCompIsoUnconditional`:
  `(a ≫ b)⁻¹ ≅ b⁻¹ ⋙ a⁻¹` on `D(-_étale, Λ)`.

## Main results

* `Stacks.EtaleCohomology.conjugateEquiv_etaleModuleInverseImageCompIso_hom`: the conjugate of
  the composition isomorphism of inverse images is that of direct images.

## Implementation notes

On sheaves the base change map is the mate, along the inverse-image/direct-image adjunctions of
the horizontal arrows, of the comparison of the two composite direct images. Mates turn the
vertical composite of squares of left adjoints into the horizontal composite of their mates
(`CategoryTheory.mateEquiv_hcomp`), once the adjunction of `a ≫ b` is traded for the composite
of those of `a` and `b`; the composition isomorphism of inverse images,
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso`, is by construction the comparison of
left adjoints for which this trade is the composition of direct images. On derived categories
the statement descends along the derivation unit of the vertical direct image, as for the
vertical pasting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### The composition isomorphism of inverse images and its conjugate -/

section InverseImageComp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The direct-image comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` through which
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso` is defined is the composition
isomorphism `Stacks.EtaleCohomology.smallEtalePushforwardComp'` of direct images. -/
theorem sheafPushforwardContinuousComp'_smallEtaleBaseChangeComp_symm :
    Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm
        (ModuleCat.{max (u + 1) r} Λ) Z.smallEtaleTopology Y.smallEtaleTopology
        X.smallEtaleTopology =
      smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ) := by
  refine Iso.ext (NatTrans.ext (funext fun F =>
    Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
  simp [smallEtalePushforwardComp', smallEtaleBaseChangeComp']
  rfl

/-- **The conjugate of the composition isomorphism of inverse images is the composition
isomorphism of direct images**: under the adjunctions `(f ≫ g)⁻¹ ⊣ (f ≫ g)_*` and
`g⁻¹ ⋙ f⁻¹ ⊣ f_* ⋙ g_*`, the isomorphism `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` corresponds to
`f_* ⋙ g_* ≅ (f ≫ g)_*`. -/
theorem conjugateEquiv_etaleModuleInverseImageCompIso_hom :
    conjugateEquiv ((etaleModuleInverseImageAdj.{u, r} Λ g).comp
        (etaleModuleInverseImageAdj.{u, r} Λ f)) (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
        (etaleModuleInverseImageCompIso.{u, r} Λ f g).hom =
      (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ)).hom := by
  have h := leftAdjointUniq_eq_conjugateEquiv_symm_id
    (((etaleModuleInverseImageAdj.{u, r} Λ g).comp
        (etaleModuleInverseImageAdj.{u, r} Λ f)).ofNatIsoRight
      (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ)))
    (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
  have e : (etaleModuleInverseImageCompIso.{u, r} Λ f g).hom =
      ((etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g)).leftAdjointUniq
        (((etaleModuleInverseImageAdj.{u, r} Λ g).comp
          (etaleModuleInverseImageAdj.{u, r} Λ f)).ofNatIsoRight
          (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ)))).hom := by
    rw [← sheafPushforwardContinuousComp'_smallEtaleBaseChangeComp_symm]
    rfl
  have h2 := Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left
    ((etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
    (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ))
    (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
    ((etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g)).leftAdjointUniq
        (((etaleModuleInverseImageAdj.{u, r} Λ g).comp
          (etaleModuleInverseImageAdj.{u, r} Λ f)).ofNatIsoRight
          (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ)))).hom
  rw [h, Equiv.apply_symm_apply] at h2
  have h3 := h2.symm
  rw [Iso.inv_comp_eq, Category.comp_id] at h3
  rw [e, h]
  exact h3

/-- The conjugate of the inverse of the composition isomorphism of inverse images is the inverse
of the composition isomorphism of direct images. -/
theorem conjugateEquiv_etaleModuleInverseImageCompIso_inv_univ :
    conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
        ((etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
        (etaleModuleInverseImageCompIso.{u, r} Λ f g).inv =
      (smallEtalePushforwardComp' f g (f ≫ g) rfl (ModuleCat.{max (u + 1) r} Λ)).inv := by
  rw [← cancel_mono (smallEtalePushforwardComp' f g (f ≫ g) rfl
    (ModuleCat.{max (u + 1) r} Λ)).hom, Iso.inv_hom_id,
    ← conjugateEquiv_etaleModuleInverseImageCompIso_hom]
  exact conjugateEquiv_comm _ _ (Iso.hom_inv_id _)

end InverseImageComp

/-! ### Horizontal pasting of the comparisons of composite direct images -/

section SheafPaste

variable {X₁ X₂ X₃ X₁' X₂' X₃' : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
  (a' : X₁' ⟶ X₂') (b' : X₂' ⟶ X₃') (h₁ : X₁' ⟶ X₁) (h₂ : X₂' ⟶ X₂) (h₃ : X₃' ⟶ X₃)
  (wa : a' ≫ h₂ = h₁ ≫ a) (wb : b' ≫ h₃ = h₂ ≫ b) (w : (a' ≫ b') ≫ h₃ = h₁ ≫ (a ≫ b))

include wa wb in
/-- **Horizontal pasting of the comparisons of composite direct images.** For two commutative
squares side by side, the comparison `(a' ≫ b')_* ⋙ h₃,_* ⟶ h₁,_* ⋙ (a ≫ b)_*` of the outer
rectangle is the horizontal composite of those of the two squares, read through the
composition isomorphisms of direct images along `a' ≫ b'` and `a ≫ b`. -/
theorem smallEtaleDirectImageSquare_hComp (A : Type*) [Category* A] :
    smallEtaleDirectImageSquare h₃ (a ≫ b) (a' ≫ b') h₁ w A =
      ((TwoSquare.hComp (smallEtaleDirectImageSquare h₂ a a' h₁ wa A)
          (smallEtaleDirectImageSquare h₃ b b' h₂ wb A)).whiskerTop
        (smallEtalePushforwardComp' a' b' (a' ≫ b') rfl A).inv).whiskerBottom
        (smallEtalePushforwardComp' a b (a ≫ b) rfl A).hom := by
  have p₁ := smallEtalePushforwardComp'_assoc a' b' h₃ (a' ≫ b') rfl (b' ≫ h₃) rfl
    ((a' ≫ b') ≫ h₃) rfl (Category.assoc _ _ _) A
  have p₂ := smallEtalePushforwardComp'_assoc a' h₂ b (a' ≫ h₂) rfl (b' ≫ h₃) wb
    ((a' ≫ b') ≫ h₃) (by rw [Category.assoc, wb, Category.assoc]) (Category.assoc _ _ _) A
  have p₃ := smallEtalePushforwardComp'_assoc h₁ a b (a' ≫ h₂) wa (a ≫ b) rfl
    ((a' ≫ b') ≫ h₃) (by rw [Category.assoc, wb, ← Category.assoc]) w A
  refine NatTrans.ext (funext fun F => ?_)
  have q₁ := congrArg (fun e => e.hom.app F) p₁
  have q₂ := congrArg (fun e => e.hom.app F) p₂
  have q₃ := congrArg (fun e => e.hom.app F) p₃
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at q₁ q₂ q₃
  have e₁ : (smallEtalePushforwardComp' (a' ≫ b') h₃ ((a' ≫ b') ≫ h₃) rfl A).hom.app F =
      (smallEtalePushforward h₃ A).map
          ((smallEtalePushforwardComp' a' b' (a' ≫ b') rfl A).inv.app F) ≫
        (smallEtalePushforwardComp' b' h₃ (b' ≫ h₃) rfl A).hom.app
          ((smallEtalePushforward a' A).obj F) ≫
        (smallEtalePushforwardComp' a' (b' ≫ h₃) ((a' ≫ b') ≫ h₃) (Category.assoc _ _ _) A).hom.app
          F := by
    rw [← q₁, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have e₂ : (smallEtalePushforwardComp' a' (b' ≫ h₃) ((a' ≫ b') ≫ h₃) (Category.assoc _ _ _)
        A).hom.app F =
      (smallEtalePushforwardComp' h₂ b (b' ≫ h₃) wb A).inv.app
          ((smallEtalePushforward a' A).obj F) ≫
        (smallEtalePushforward b A).map
          ((smallEtalePushforwardComp' a' h₂ (a' ≫ h₂) rfl A).hom.app F) ≫
        (smallEtalePushforwardComp' (a' ≫ h₂) b ((a' ≫ b') ≫ h₃)
          (by rw [Category.assoc, wb, Category.assoc]) A).hom.app F := by
    rw [q₂, Iso.inv_hom_id_app_assoc]
  have e₃ : (smallEtalePushforwardComp' (a' ≫ h₂) b ((a' ≫ b') ≫ h₃)
        (by rw [Category.assoc, wb, Category.assoc]) A).hom.app F ≫
        (smallEtalePushforwardComp' h₁ (a ≫ b) ((a' ≫ b') ≫ h₃) w A).inv.app F =
      (smallEtalePushforward b A).map
          ((smallEtalePushforwardComp' h₁ a (a' ≫ h₂) wa A).inv.app F) ≫
        (smallEtalePushforwardComp' a b (a ≫ b) rfl A).hom.app
          ((smallEtalePushforward h₁ A).obj F) := by
    rw [← cancel_epi ((smallEtalePushforward b A).map
      ((smallEtalePushforwardComp' h₁ a (a' ≫ h₂) wa A).hom.app F)), reassoc_of% q₃,
      Iso.hom_inv_id_app]
    simp [← Functor.map_comp_assoc]
  simp only [smallEtaleDirectImageSquare, TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Functor.map_comp]
  rw [e₁, Category.assoc, Category.assoc, e₂, Category.assoc, Category.assoc, e₃]

variable (Λ : Type r) [Ring Λ]

include wa wb in
/-- **Horizontal pasting of the base change maps of sheaves of `Λ`-modules.** For two commutative
squares side by side, the base change map `h₃,_* ⋙ (a ≫ b)⁻¹ ⟶ (a' ≫ b')⁻¹ ⋙ h₁,_*` of the outer
rectangle is the vertical composite (as 2-squares) of those of the two squares, read through the
composition isomorphisms `(a ≫ b)⁻¹ ≅ b⁻¹ ⋙ a⁻¹` and `(a' ≫ b')⁻¹ ≅ b'⁻¹ ⋙ a'⁻¹` of inverse
images. -/
theorem etaleModuleBaseChange_hComp :
    TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ (a ≫ b) (a' ≫ b') h₁ w) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb))
          (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa))).whiskerLeft
        (etaleModuleInverseImageCompIso.{u, r} Λ a' b').inv).whiskerRight
        (etaleModuleInverseImageCompIso.{u, r} Λ a b).hom := by
  have m_a : mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ a')
      (etaleModuleInverseImageAdj.{u, r} Λ a)
      (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa)) =
      smallEtaleDirectImageSquare h₂ a a' h₁ wa (ModuleCat.{max (u + 1) r} Λ) :=
    Equiv.apply_symm_apply _ _
  have m_b : mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ b')
      (etaleModuleInverseImageAdj.{u, r} Λ b)
      (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb)) =
      smallEtaleDirectImageSquare h₃ b b' h₂ wb (ModuleCat.{max (u + 1) r} Λ) :=
    Equiv.apply_symm_apply _ _
  have key : mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ (a' ≫ b'))
      (etaleModuleInverseImageAdj.{u, r} Λ (a ≫ b))
      (((TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb))
          (TwoSquare.mk _ _ _ _ (etaleModuleBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa))).whiskerLeft
        (etaleModuleInverseImageCompIso.{u, r} Λ a' b').inv).whiskerRight
        (etaleModuleInverseImageCompIso.{u, r} Λ a b).hom) =
      smallEtaleDirectImageSquare h₃ (a ≫ b) (a' ≫ b') h₁ w (ModuleCat.{max (u + 1) r} Λ) := by
    rw [mateEquiv_conjugateEquiv_vcomp _ ((etaleModuleInverseImageAdj.{u, r} Λ b).comp
        (etaleModuleInverseImageAdj.{u, r} Λ a)),
      conjugateEquiv_mateEquiv_vcomp _ ((etaleModuleInverseImageAdj.{u, r} Λ b').comp
        (etaleModuleInverseImageAdj.{u, r} Λ a')),
      mateEquiv_hcomp, m_a, m_b, conjugateEquiv_etaleModuleInverseImageCompIso_hom,
      conjugateEquiv_etaleModuleInverseImageCompIso_inv_univ]
    exact (smallEtaleDirectImageSquare_hComp a b a' b' h₁ h₂ h₃ wa wb w _).symm
  change TwoSquare.mk _ _ _ _ ((mateEquiv _ _).symm _) = _
  rw [← key, Equiv.symm_apply_apply]

end SheafPaste


/-! ### The composition isomorphism of derived inverse images -/

section DerivedInverseImageComp

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The inverse image along a composite is the composite of the inverse images**, on
`D(-_étale, Λ)`: `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹`. All three are applied degreewise, and this is the
composition isomorphism `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso` of sheaves applied
degreewise. -/
def etaleModuleDerivedInverseImageCompIsoUnconditional :
    etaleModuleDerivedInverseImageGeneral.{u, r} Λ (f ≫ g) ≅
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ g ⋙
        etaleModuleDerivedInverseImageGeneral.{u, r} Λ f :=
  DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageCompIso.{u, r} Λ f g) ≪≫
    DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

end DerivedInverseImageComp

/-! ### Horizontal pasting of the derived base change maps -/

section DerivedPaste

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X₁ X₂ X₃ X₁' X₂' X₃' : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
  (a' : X₁' ⟶ X₂') (b' : X₂' ⟶ X₃') (h₁ : X₁' ⟶ X₁) (h₂ : X₂' ⟶ X₂) (h₃ : X₃' ⟶ X₃)
  (wa : a' ≫ h₂ = h₁ ≫ a) (wb : b' ≫ h₃ = h₂ ≫ b) (w : (a' ≫ b') ≫ h₃ = h₁ ≫ (a ≫ b))

include wa wb in
/-- **Horizontal pasting of the derived base change maps** on `D(-_étale, Λ)`. For two
commutative squares side by side, the base change map
`(a ≫ b)⁻¹ Rh₃,_* ⟶ Rh₁,_* (a' ≫ b')⁻¹` of the outer rectangle is
```
(a ≫ b)⁻¹ Rh₃,_* ≅ a⁻¹ b⁻¹ Rh₃,_* ⟶ a⁻¹ Rh₂,_* b'⁻¹ ⟶ Rh₁,_* a'⁻¹ b'⁻¹ ≅ Rh₁,_* (a' ≫ b')⁻¹,
```
the composite of the base change maps of the two squares, read through the composition
isomorphisms of derived inverse images. -/
theorem etaleModuleDerivedBaseChange_hComp :
    etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₃ (a ≫ b) (a' ≫ b') h₁ w =
      Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₃)
          (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb)
          (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImageGeneral.{u, r} Λ b')
          (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a' b').inv
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁) := by
  refine Functor.rightDerived_ext _
    (Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit
      (E' := etaleModuleInverseImage.{u, r} Λ (a ≫ b))
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₃))
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X₃') (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  have hu₀ : (Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit
      (E' := etaleModuleInverseImage.{u, r} Λ (a ≫ b))
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₃)).app K =
      (etaleModuleInverseImage.{u, r} Λ (a ≫ b)).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ h₃).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ (a ≫ b)).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₃).app K) := by
    have e₁ : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage.{u, r} Λ h₃ ⋙ etaleModuleInverseImage.{u, r} Λ (a ≫ b)))
        (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
    simp [Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit, e₁]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    hu₀, Category.assoc]
  congr 1
  have n₀ := (etaleModuleDerivedInverseImageCompIsoUnconditional.{u, r} Λ a b).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₃).app K)
  have nbc := (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa).naturality
    ((etaleModuleInverseImage.{u, r} Λ b').mapDerivedCategoryFactors.inv.app K)
  have nfa := (etaleModuleInverseImage.{u, r} Λ a).mapDerivedCategoryFactors.inv.naturality
    ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb)
      (ComplexShape.up ℤ)).app K)
  have nu := (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₁).naturality
    ((NatIso.mapHomologicalComplex (etaleModuleInverseImageCompIso.{u, r} Λ a' b')
      (ComplexShape.up ℤ)).inv.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at n₀ nbc nfa nu
  rw [etaleModuleDerivedBaseChange_fac', reassoc_of% n₀]
  simp only [etaleModuleDerivedInverseImageCompIsoUnconditional, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc,
    DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q]
  congr 1
  have hb : (etaleModuleInverseImage.{u, r} Λ a).mapDerivedCategory.map
        ((etaleModuleInverseImage.{u, r} Λ b).mapDerivedCategoryFactors.inv.app
          (((etaleModuleDirectImage.{u, r} Λ h₃).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ b).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₃).app K)) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
        ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb).app
          (DerivedCategory.Q.obj K)) =
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb)
            (ComplexShape.up ℤ)).app K)) ≫
        (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₂).app
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₂).map
            ((etaleModuleInverseImage.{u, r} Λ b').mapDerivedCategoryFactors.inv.app K)) := by
    simp only [← Functor.map_comp]
    congr 1
    exact etaleModuleDerivedBaseChange_fac_general.{u, r} Λ h₃ b b' h₂ wb K
  have nfa' : (etaleModuleInverseImage.{u, r} Λ a).mapDerivedCategoryFactors.inv.app
        (((etaleModuleInverseImage.{u, r} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ h₃).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb)
            (ComplexShape.up ℤ)).app K)) =
      DerivedCategory.Q.map (((etaleModuleInverseImage.{u, r} Λ a).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
            (etaleModuleBaseChangeGeneral.{u, r} Λ h₃ b b' h₂ wb) (ComplexShape.up ℤ)).app K)) ≫
        (etaleModuleInverseImage.{u, r} Λ a).mapDerivedCategoryFactors.inv.app
          (((etaleModuleDirectImage.{u, r} Λ h₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) :=
    nfa.symm
  have ha : (etaleModuleInverseImage.{u, r} Λ a).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ h₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ a).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₂).app
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa).app (DerivedCategory.Q.obj
          (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (etaleModuleBaseChangeGeneral.{u, r} Λ h₂ a a' h₁ wa) (ComplexShape.up ℤ)).app
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₁).app
          (((etaleModuleInverseImage.{u, r} Λ a').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map
          ((etaleModuleInverseImage.{u, r} Λ a').mapDerivedCategoryFactors.inv.app
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) :=
    etaleModuleDerivedBaseChange_fac_general.{u, r} Λ h₂ a a' h₁ wa _
  rw [reassoc_of% hb, reassoc_of% nbc, reassoc_of% nfa',
    reassoc_of% ha]
  have hfin : (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map
        ((etaleModuleInverseImage.{u, r} Λ a').mapDerivedCategoryFactors.inv.app
          (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ a').map
          ((etaleModuleInverseImage.{u, r} Λ b').mapDerivedCategoryFactors.inv.app K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map
        ((etaleModuleInverseImage.{u, r} Λ a').mapDerivedCategory.map
            ((etaleModuleInverseImage.{u, r} Λ b').mapDerivedCategoryFactors.hom.app K) ≫
          (etaleModuleInverseImage.{u, r} Λ a').mapDerivedCategoryFactors.hom.app
            (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (etaleModuleInverseImageCompIso.{u, r} Λ a' b') (ComplexShape.up ℤ)).inv.app K) ≫
          (etaleModuleInverseImage.{u, r} Λ (a' ≫ b')).mapDerivedCategoryFactors.inv.app K) =
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (etaleModuleInverseImageCompIso.{u, r} Λ a' b')
            (ComplexShape.up ℤ)).inv.app K)) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map
          ((etaleModuleInverseImage.{u, r} Λ (a' ≫ b')).mapDerivedCategoryFactors.inv.app K) := by
    simp only [← Functor.map_comp]
    congr 1
    simp [← Functor.map_comp_assoc]
  have nu' : (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₁).app
        (((etaleModuleInverseImage.{u, r} Λ a').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleInverseImage.{u, r} Λ b').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h₁).map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (etaleModuleInverseImageCompIso.{u, r} Λ a' b')
            (ComplexShape.up ℤ)).inv.app K)) =
      DerivedCategory.Q.map (((etaleModuleDirectImage.{u, r} Λ h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatIso.mapHomologicalComplex
            (etaleModuleInverseImageCompIso.{u, r} Λ a' b') (ComplexShape.up ℤ)).inv.app K)) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ h₁).app
          (((etaleModuleInverseImage.{u, r} Λ (a' ≫ b')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
    nu.symm
  rw [hfin, reassoc_of% nu']
  simp only [← Functor.map_comp_assoc]
  refine congrArg (fun t => DerivedCategory.Q.map t ≫ _) ?_
  have key := congr_app
    (etaleModuleBaseChange_hComp.{u, r} a b a' b' h₁ h₂ h₃ wa wb w Λ)
  ext n : 1
  simpa [TwoSquare.vComp] using key (K.X n)

end DerivedPaste

end Stacks.EtaleCohomology

end
