module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# The pasting law for derived comparisons of squares of additive functors

For a commutative square of additive functors whose horizontal functors are exact, the bounded
below derived comparison is the descent of the degreewise comparison along the derived-functor
unit.  This file reads that comparison at a bounded below complex, records the right derived
functors of exact functors and their composition isomorphism, and proves
`Stacks.Cohomology.BaseChange.derived_paste`: the comparison of a horizontally pasted rectangle
is the comparison of the first square carried by `RH`, followed by that of the second square.

See `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting` for an
overview.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Reassociation in an arbitrary category -/

section Reassoc

variable {𝒞 : Type*} [Category* 𝒞]

/-- Reassociating a threefold composite in front of a morphism. -/
public theorem assoc₃ {X₀ X₁ X₂ X₃ Y : 𝒞} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (t : X₃ ⟶ Y) : (a ≫ b ≫ c) ≫ t = a ≫ b ≫ c ≫ t := by
  simp

/-- Reassociating a fourfold composite in front of a morphism. -/
public theorem assoc₄ {X₀ X₁ X₂ X₃ X₄ Y : 𝒞} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (t : X₄ ⟶ Y) : (a ≫ b ≫ c ≫ d) ≫ t = a ≫ b ≫ c ≫ d ≫ t := by
  simp

/-- **The shape of the pasting chase, in an arbitrary category.**  Given a fourfold composite
rewritten by `h₁`, a naturality square `h₂`, the second square's step `h₃`, and the two
contractions `h₄` and `h₅`, the composite of the fourfold one with `c₁ ≫ c₂` is `q ≫ e₃ ≫ w`. -/
public theorem chaseAux {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ Y₃ Z₁ W₁ W₂ : 𝒞}
    {a₁ : X₀ ⟶ X₁} {a₂ : X₁ ⟶ X₂} {a₃ : X₂ ⟶ X₃} {a₄ : X₃ ⟶ X₄}
    {c₁ : X₄ ⟶ X₅} {c₂ : X₅ ⟶ X₆}
    {b₁ : X₀ ⟶ Y₁} {b₂ : Y₁ ⟶ Y₂} {b₃ : Y₂ ⟶ Y₃} {b₄ : Y₃ ⟶ X₄}
    {d₁ : Y₃ ⟶ Z₁} {d₂ : Z₁ ⟶ X₅}
    {e₂ : Y₁ ⟶ W₁} {e₃ : W₁ ⟶ W₂} {e₄ : W₂ ⟶ Z₁}
    {q : X₀ ⟶ W₁} {w : W₂ ⟶ X₆}
    (h₁ : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b₁ ≫ b₂ ≫ b₃ ≫ b₄)
    (h₂ : b₄ ≫ c₁ = d₁ ≫ d₂)
    (h₃ : b₂ ≫ b₃ ≫ d₁ = e₂ ≫ e₃ ≫ e₄)
    (h₄ : e₄ ≫ d₂ ≫ c₂ = w)
    (h₅ : b₁ ≫ e₂ = q) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ c₁ ≫ c₂ = q ≫ e₃ ≫ w := by
  rw [← h₅, ← h₄, ← assoc₄ a₁ a₂ a₃ a₄, h₁, assoc₄, Category.assoc b₁ e₂,
    ← Category.assoc b₄ c₁ c₂, h₂, Category.assoc, ← assoc₃ b₂ b₃ d₁, h₃, assoc₃]

end Reassoc

/-! ### The composition isomorphism of induced degreewise functors -/

section Degreewise

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]

/-- **The functor induced on bounded below homotopy categories by a composite is the composite
of the induced functors**, on objects. -/
public theorem mapHomotopyCategoryPlus_comp_obj (K : HomotopyCategory.Plus A) :
    (F ⋙ G).mapHomotopyCategoryPlus.obj K =
      G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K) := rfl

/-- The composition isomorphism of the functors induced on bounded below homotopy categories by
two composable additive functors is an identity morphism. -/
public theorem map_mapHomotopyCategoryPlusCompIso_hom_app {T : Type*} [Category* T]
    (Φ : HomotopyCategory.Plus D ⥤ T) (K : HomotopyCategory.Plus A) :
    Φ.map ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      𝟙 (Φ.obj (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K))) :=
  Φ.map_id _

/-- The inverse form of `map_mapHomotopyCategoryPlusCompIso_hom_app`. -/
public theorem map_mapHomotopyCategoryPlusCompIso_inv_app {T : Type*} [Category* T]
    (Φ : HomotopyCategory.Plus D ⥤ T) (K : HomotopyCategory.Plus A) :
    Φ.map ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) =
      𝟙 (Φ.obj (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K))) :=
  Φ.map_id _

/-- The functor induced on bounded below homotopy categories acts on a morphism through the
functor induced on homotopy categories. -/
public theorem mapHomotopyCategoryPlus_map_hom {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (F.mapHomotopyCategoryPlus.map f).hom =
      (F.mapHomotopyCategory (ComplexShape.up ℤ)).map f.hom := rfl

/-- **The composition isomorphism of the functors induced on bounded below homotopy categories
is an identity**, and is absorbed by any morphism it precedes after application of a functor. -/
public theorem map_mapHomotopyCategoryPlusCompIso_hom_comp {T : Type*} [Category* T]
    (Φ : HomotopyCategory.Plus D ⥤ T) (K : HomotopyCategory.Plus A) {X : T}
    (f : Φ.obj (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ⟶ X) :
    Φ.map ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) ≫ f = f := by
  rw [map_mapHomotopyCategoryPlusCompIso_hom_app]
  exact Category.id_comp f

/-- The inverse form of `map_mapHomotopyCategoryPlusCompIso_hom_comp`. -/
public theorem map_mapHomotopyCategoryPlusCompIso_inv_comp {T : Type*} [Category* T]
    (Φ : HomotopyCategory.Plus D ⥤ T) (K : HomotopyCategory.Plus A) {X : T}
    (f : Φ.obj (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ⟶ X) :
    Φ.map ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫ f = f := by
  rw [map_mapHomotopyCategoryPlusCompIso_inv_app]
  exact Category.id_comp f

end Degreewise

/-! ### The derived comparison at a bounded below complex -/

section Abstract

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- The unit exhibiting `RF ⋙ RG` as a right derived functor of degreewise `F` followed by
`RG`: the derived-functor unit of `RF`, whiskered with `RG`. -/
public def compUnit :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G.rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- `RF ⋙ RG` is a right derived functor of degreewise `F` followed by `RG`, with unit
`compUnit`: on a bounded below complex of injectives the unit of `RF` is already invertible. -/
public instance isRightDerivedFunctor_compUnit :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (compUnit F G) (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
    (compUnit F G) (fun K ↦ by dsimp [compUnit]; infer_instance)

/-- The component of `compUnit` at a bounded below complex. -/
public theorem compUnit_app (K : HomotopyCategory.Plus A) :
    (compUnit F G).app K =
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
  simp [compUnit]

variable (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

/-- The characterization of `Stacks.Cohomology.BaseChange.derived`, read at a bounded below
complex: the derived comparison precomposed with the unit of `RF` is `onHomotopy`. -/
@[reassoc]
public theorem derived_fac_app (K : HomotopyCategory.Plus A) :
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (derived F F' G G' τ e).app (DerivedCategory.Plus.Qh.obj K) =
      (onHomotopy F F' G G' τ e).app K := by
  have h := NatTrans.congr_app (derived_fac F F' G G' τ e) K
  simpa using h

/-- **The component of `Stacks.Cohomology.BaseChange.onHomotopy` at a bounded below complex**:
the comparison `e` undone, the degreewise transformation, and the derived-functor units of
`RF'` and of `RG'`. -/
public theorem onHomotopy_app (K : HomotopyCategory.Plus A) :
    (onHomotopy F F' G G' τ e).app K =
      e.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((mapPlus τ).app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K) := by
  have h : (onHomotopy F F' G G' τ e).app K =
      e.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((mapPlus τ).app K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K) := by
    simp [onHomotopy]
  rw [h]
  simp only [map_mapHomotopyCategoryPlusCompIso_hom_app,
    map_mapHomotopyCategoryPlusCompIso_inv_app]
  simp [mapHomotopyCategoryPlus_comp_obj]

end Abstract

/-! ### Right derived functors of exact functors -/

section ExactUnit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The derived-functor unit of an exact functor, as an isomorphism: the right derived functor
of an exact functor is computed degreewise. -/
public def exactUnitIso :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  letI : IsIso F.rightDerivedFunctorPlusUnith := exactUnit_isIso F
  asIso F.rightDerivedFunctorPlusUnith

/-- The isomorphism `exactUnitIso` is the derived-functor unit. -/
public theorem exactUnitIso_hom : (exactUnitIso F).hom = F.rightDerivedFunctorPlusUnith := rfl

/-- **The derived-functor unit of an exact functor cancels against `exactUnitIso`.** -/
public theorem unit_comp_exactUnitIso_inv_assoc {X : DerivedCategory.Plus B}
    (M : HomotopyCategory.Plus A)
    (f : DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj M) ⟶ X) :
    F.rightDerivedFunctorPlusUnith.app M ≫ (exactUnitIso F).inv.app M ≫ f = f := by
  rw [← exactUnitIso_hom, Iso.hom_inv_id_app_assoc]

end ExactUnit

/-! ### The iterated derived-functor unit -/

section IteratedUnit

variable {B D E : Type*} [Category* B] [Category* D] [Category* E]
  [Abelian B] [Abelian D] [Abelian E] [EnoughInjectives B] [EnoughInjectives D]
  (G : B ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]

/-- **The iterated derived-functor unit** `H(G(K)) ⟶ RH(RG(K))` of two composable additive
functors: the unit of `RH`, followed by `RH` applied to the unit of `RG`. -/
public def iteratedUnit (M : HomotopyCategory.Plus B) :
    DerivedCategory.Plus.Qh.obj
        (H.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj M)) ⟶
      (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).obj
        (DerivedCategory.Plus.Qh.obj M) :=
  H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj M) ≫
    H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app M)

/-- The iterated derived-functor unit, written out, in front of a morphism. -/
public theorem iteratedUnit_comp (M : HomotopyCategory.Plus B) {X : DerivedCategory.Plus E}
    (f : (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).obj
      (DerivedCategory.Plus.Qh.obj M) ⟶ X) :
    iteratedUnit G H M ≫ f =
      H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj M) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app M) ≫ f :=
  Category.assoc _ _ f

end IteratedUnit

section ExactComp

variable {B D E : Type*} [Category* B] [Category* D] [Category* E]
  [Abelian B] [Abelian D] [Abelian E] [EnoughInjectives B] [EnoughInjectives D]
  (G : B ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The composition isomorphism `R(H ∘ G) ≅ RG ⋙ RH` for exact `G` and `H`: every object is
right acyclic for the exact `H`, so the canonical comparison of Stacks 05T2 is invertible. -/
public def exactDerivedCompIso :
    (G ⋙ H).rightDerivedFunctorPlus ≅
      G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic G H
    (fun I _ ↦ Functor.rightAcyclic_of_exact H (G.obj I))

/-- **The derived-functor unit of `R(H ∘ G)` composed with the composition isomorphism** is the
iterated derived-functor unit. -/
public theorem unit_comp_exactDerivedCompIso_hom (M : HomotopyCategory.Plus B) :
    (exactUnitIso (G ⋙ H)).hom.app M ≫
        (exactDerivedCompIso G H).hom.app (DerivedCategory.Plus.Qh.obj M) =
      iteratedUnit G H M := by
  rw [iteratedUnit]
  have h := Functor.rightDerivedFunctorPlusComp_fac_app G H M
  simp only [map_mapHomotopyCategoryPlusCompIso_inv_app] at h
  simp only [mapHomotopyCategoryPlus_comp_obj, Category.id_comp] at h
  rw [exactUnitIso_hom]
  exact h

/-- **The composition isomorphism at an object in the image of the localization functor**,
written out through the derived-functor units of `R(H ∘ G)`, of `RH` and of `RG`. -/
public theorem exactDerivedCompIso_hom_app_qh (M : HomotopyCategory.Plus B) :
    (exactDerivedCompIso G H).hom.app (DerivedCategory.Plus.Qh.obj M) =
      (exactUnitIso (G ⋙ H)).inv.app M ≫ iteratedUnit G H M := by
  rw [← unit_comp_exactDerivedCompIso_hom G H M, Iso.inv_hom_id_app_assoc]

/-- **The derived-functor unit of `R(H ∘ G)` factors through the composition isomorphism**: the
units of `RH` and of `RG`, followed by the inverse of the composition isomorphism, are the unit
of the right derived functor of the composite. -/
public theorem unit_eq_comp_exactDerivedCompIso_inv (M : HomotopyCategory.Plus B) :
    iteratedUnit G H M ≫
        (exactDerivedCompIso G H).inv.app (DerivedCategory.Plus.Qh.obj M) =
      (G ⋙ H).rightDerivedFunctorPlusUnith.app M := by
  rw [← unit_comp_exactDerivedCompIso_hom G H M]
  erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- `unit_eq_comp_exactDerivedCompIso_inv` right associated. -/
public theorem unit_eq_comp_exactDerivedCompIso_inv'' (M : HomotopyCategory.Plus B) :
    H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj M) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app M) ≫
        (exactDerivedCompIso G H).inv.app (DerivedCategory.Plus.Qh.obj M) =
      (G ⋙ H).rightDerivedFunctorPlusUnith.app M :=
  (iteratedUnit_comp G H M _).symm.trans (unit_eq_comp_exactDerivedCompIso_inv G H M)

/-- `exactDerivedCompIso_hom_app_qh` in front of a morphism, right associated. -/
public theorem exactDerivedCompIso_hom_app_qh_assoc {X : DerivedCategory.Plus E}
    (M : HomotopyCategory.Plus B)
    (f : (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).obj
      (DerivedCategory.Plus.Qh.obj M) ⟶ X) :
    (exactDerivedCompIso G H).hom.app (DerivedCategory.Plus.Qh.obj M) ≫ f =
      (exactUnitIso (G ⋙ H)).inv.app M ≫
        H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj M) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app M) ≫ f := by
  rw [exactDerivedCompIso_hom_app_qh]
  erw [Category.assoc]
  exact congrArg _ (iteratedUnit_comp G H M f)

/-- `unit_eq_comp_exactDerivedCompIso_inv` with the iterated unit written out. -/
public theorem unit_eq_comp_exactDerivedCompIso_inv' (M : HomotopyCategory.Plus B) :
    (H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj M) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app M)) ≫
        (exactDerivedCompIso G H).inv.app (DerivedCategory.Plus.Qh.obj M) =
      (G ⋙ H).rightDerivedFunctorPlusUnith.app M :=
  unit_eq_comp_exactDerivedCompIso_inv G H M

end ExactComp

/-! ### Pasting two squares along the base -/

section PasteDegreewise

variable {A B C D C₂ D₂ : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* C₂] [Category* D₂]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian C₂] [Abelian D₂]
  (F : A ⥤ B) (F' : C ⥤ D) (F'' : C₂ ⥤ D₂)
  (G : B ⥤ D) (G' : A ⥤ C) (H : D ⥤ D₂) (H' : C ⥤ C₂)
  [F.Additive] [F'.Additive] [F''.Additive]
  [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  (τ₁ : F ⋙ G ⟶ G' ⋙ F') (τ₂ : F' ⋙ H ⟶ H' ⋙ F'')

/-- **The horizontal paste of two commutative squares of additive functors.** The comparison of
the outer rectangle is `H` applied to the comparison of the first square, followed by the
comparison of the second square applied after `G'`. -/
public def pasteTrans : F ⋙ G ⋙ H ⟶ (G' ⋙ H') ⋙ F'' :=
  Functor.whiskerRight τ₁ H ≫ Functor.whiskerLeft G' τ₂

/-- **The degreewise comparison of the pasted rectangle**, at a bounded below complex, is the
degreewise comparison of the first square carried by `H` followed by that of the second. -/
public theorem mapPlus_pasteTrans_app (K : HomotopyCategory.Plus A) :
    (mapPlus (pasteTrans F F' F'' G G' H H' τ₁ τ₂)).app K =
      H.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
        (mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K) := by
  ext
  dsimp only [pasteTrans, mapPlus, ObjectProperty.homMk, Functor.mapHomotopyCategoryPlus,
    ObjectProperty.lift, ObjectProperty.FullSubcategory.comp_hom]
  rfl

end PasteDegreewise

section PasteDerived

variable {A B C D C₂ D₂ : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* C₂] [Category* D₂]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian C₂] [Abelian D₂]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  [EnoughInjectives C₂]
  (F : A ⥤ B) (F' : C ⥤ D) (F'' : C₂ ⥤ D₂)
  (G : B ⥤ D) (G' : A ⥤ C) (H : D ⥤ D₂) (H' : C ⥤ C₂)
  [F.Additive] [F'.Additive] [F''.Additive]
  [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (τ₁ : F ⋙ G ⟶ G' ⋙ F') (τ₂ : F' ⋙ H ⟶ H' ⋙ F'')

omit [PreservesFiniteLimits H] [PreservesFiniteColimits H] in
/-- **The first square's step of the pasting chase.** The derived-functor unit of `RG` cancels
against the comparison through which the derived comparison of the first square is descended,
and what is left commutes past the degreewise comparison by naturality of the unit of `RH`. -/
@[reassoc]
public theorem firstStep (K : HomotopyCategory.Plus A) :
    H.rightDerivedFunctorPlusUnith.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) ≫
        H.rightDerivedFunctorPlus.map
          ((derived F F' G G' τ₁ (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map (H.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K)) ≫
        H.rightDerivedFunctorPlusUnith.app ((G' ⋙ F').mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K)) := by
  have hinner : G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (derived F F' G G' τ₁ (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K) := by
    rw [derived_fac_app, onHomotopy_app, ← exactUnitIso_hom G]
    simp
  have h2 := congrArg (fun m ↦ H.rightDerivedFunctorPlus.map m) hinner
  have h3 : H.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K) ≫
          F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
          F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K)) =
      H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K)) ≫
        H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K)) := by
    rw [Functor.map_comp]
    exact congrArg (fun t ↦ H.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K)) ≫ t)
      (H.rightDerivedFunctorPlus.map_comp _ _)
  rw [← Functor.map_comp, ← Functor.map_comp, h2.trans h3,
    reassoc_of% H.rightDerivedFunctorPlusUnith.naturality ((mapPlus τ₁).app K)]
  rfl

omit [EnoughInjectives A] in
/-- **The second square's step of the pasting chase**: the derived comparison of the second
square, read through its own factorization over the derived-functor unit of `RF'`. -/
@[reassoc]
public theorem secondStep (K : HomotopyCategory.Plus A) :
    H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        (derived F' F'' H H' τ₂ (exactUnitIso H)).app
          (DerivedCategory.Plus.Qh.obj (G'.mapHomotopyCategoryPlus.obj K)) =
      (exactUnitIso H).inv.app
          (F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map ((mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlusUnith.app
          (H'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlus.map
          (H'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) := by
  rw [derived_fac_app, onHomotopy_app]

end PasteDerived

section PasteAssembly

variable {A B C D C₂ D₂ : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* C₂] [Category* D₂]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian C₂] [Abelian D₂]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  [EnoughInjectives C₂]
  (F : A ⥤ B) (F' : C ⥤ D) (F'' : C₂ ⥤ D₂)
  (G : B ⥤ D) (G' : A ⥤ C) (H : D ⥤ D₂) (H' : C ⥤ C₂)
  [F.Additive] [F'.Additive] [F''.Additive]
  [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  (τ₁ : F ⋙ G ⟶ G' ⋙ F') (τ₂ : F' ⋙ H ⟶ H' ⋙ F'')

/-- **The pasting chase.**  The iterated derived-functor unit, the comparison of the first square
carried by `RH`, the comparison of the second square and the inverse composition isomorphism
compose to the degreewise pasted comparison followed by the derived-functor units of `RF''` and
of `R(H' ∘ G')`.  Both units of the exact horizontal functors cancel on the way: the one of `RG`
against the comparison descending the first square, the one of `RH` against the comparison
descending the second. -/
public theorem pasteTail (K : HomotopyCategory.Plus A) :
    H.rightDerivedFunctorPlusUnith.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) ≫
        H.rightDerivedFunctorPlus.map
          ((derived F F' G G' τ₁ (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K)) ≫
        (derived F' F'' H H' τ₂ (exactUnitIso H)).app
          (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        F''.rightDerivedFunctorPlus.map
          ((exactDerivedCompIso G' H').inv.app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          (H.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
            (mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlusUnith.app
          (H'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlus.map ((G' ⋙ H').rightDerivedFunctorPlusUnith.app K) := by
  have h₃ : H.rightDerivedFunctorPlusUnith.app ((G' ⋙ F').mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map
          (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        (derived F' F'' H H' τ₂ (exactUnitIso H)).app
          (DerivedCategory.Plus.Qh.obj (G'.mapHomotopyCategoryPlus.obj K)) =
      DerivedCategory.Plus.Qh.map ((mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlusUnith.app
          (H'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F''.rightDerivedFunctorPlus.map
          (H'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) :=
    by
    erw [secondStep F' F'' G' H H' τ₂ K]
    exact unit_comp_exactUnitIso_inv_assoc H _ _
  have h₄ : F''.rightDerivedFunctorPlus.map
        (H'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
      F''.rightDerivedFunctorPlus.map
          (H'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K)) ≫
        F''.rightDerivedFunctorPlus.map
          ((exactDerivedCompIso G' H').inv.app (DerivedCategory.Plus.Qh.obj K)) =
      F''.rightDerivedFunctorPlus.map ((G' ⋙ H').rightDerivedFunctorPlusUnith.app K) :=
    by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (unit_eq_comp_exactDerivedCompIso_inv'' G' H' K)
  exact chaseAux (firstStep F F' G G' H τ₁ K)
    ((derived F' F'' H H' τ₂ (exactUnitIso H)).naturality
      (G'.rightDerivedFunctorPlusUnith.app K))
    h₃ h₄ (DerivedCategory.Plus.Qh.map_comp _ _).symm

/-- **Base functoriality of the derived comparison, at a bounded below complex.**  Both sides
of the pasting law have the same composite with the derived-functor unit of `RF`, which
determines them. -/
public theorem derived_paste_app (K : HomotopyCategory.Plus A) :
    (compUnit F (G ⋙ H)).app K ≫
        (derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
          (exactUnitIso (G ⋙ H))).app (DerivedCategory.Plus.Qh.obj K) =
      (compUnit F (G ⋙ H)).app K ≫
        (exactDerivedCompIso G H).hom.app
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
          H.rightDerivedFunctorPlus.map
              ((derived F F' G G' τ₁ (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K)) ≫
            (derived F' F'' H H' τ₂ (exactUnitIso H)).app
                (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
              F''.rightDerivedFunctorPlus.map
                ((exactDerivedCompIso G' H').inv.app (DerivedCategory.Plus.Qh.obj K)) := by
  have hL : (compUnit F (G ⋙ H)).app K ≫
      (derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
        (exactUnitIso (G ⋙ H))).app (DerivedCategory.Plus.Qh.obj K) =
      (exactUnitIso (G ⋙ H)).inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
            (H.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
              (mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K)) ≫
          F''.rightDerivedFunctorPlusUnith.app ((G' ⋙ H').mapHomotopyCategoryPlus.obj K) ≫
            F''.rightDerivedFunctorPlus.map
              ((G' ⋙ H').rightDerivedFunctorPlusUnith.app K) := by
    rw [compUnit_app, derived_fac_app, onHomotopy_app, mapPlus_pasteTrans_app]
  have hR : (compUnit F (G ⋙ H)).app K ≫
      (exactDerivedCompIso G H).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        H.rightDerivedFunctorPlus.map
            ((derived F F' G G' τ₁ (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K)) ≫
          (derived F' F'' H H' τ₂ (exactUnitIso H)).app
              (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
            F''.rightDerivedFunctorPlus.map
              ((exactDerivedCompIso G' H').inv.app (DerivedCategory.Plus.Qh.obj K)) =
      (exactUnitIso (G ⋙ H)).inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
            (H.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
              (mapPlus τ₂).app (G'.mapHomotopyCategoryPlus.obj K)) ≫
          F''.rightDerivedFunctorPlusUnith.app ((G' ⋙ H').mapHomotopyCategoryPlus.obj K) ≫
            F''.rightDerivedFunctorPlus.map
              ((G' ⋙ H').rightDerivedFunctorPlusUnith.app K) := by
    rw [compUnit_app, ← Category.assoc]
    erw [(exactDerivedCompIso G H).hom.naturality (F.rightDerivedFunctorPlusUnith.app K),
      Category.assoc, exactDerivedCompIso_hom_app_qh_assoc]
    exact congrArg _ (pasteTail F F' F'' G G' H H' τ₁ τ₂ K)
  exact hL.trans hR.symm

/-- **Base functoriality of the derived comparison.**  For two commutative squares of additive
functors composable along the base, with all four horizontal functors exact, the comparison of
the pasted rectangle is the comparison of the first square carried by `RH`, followed by the
comparison of the second square, read through the composition isomorphisms identifying
`R(H ∘ G)` with `RG ⋙ RH` and `R(H' ∘ G')` with `RG' ⋙ RH'`. -/
public theorem derived_paste :
    derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
        (exactUnitIso (G ⋙ H)) =
      Functor.whiskerLeft F.rightDerivedFunctorPlus (exactDerivedCompIso G H).hom ≫
        Functor.whiskerRight (derived F F' G G' τ₁ (exactUnitIso G))
            H.rightDerivedFunctorPlus ≫
          Functor.whiskerLeft G'.rightDerivedFunctorPlus
              (derived F' F'' H H' τ₂ (exactUnitIso H)) ≫
            Functor.whiskerRight (exactDerivedCompIso G' H').inv
              F''.rightDerivedFunctorPlus :=
  Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ (G ⋙ H).rightDerivedFunctorPlus)
    (compUnit F (G ⋙ H)) (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext fun K ↦ derived_paste_app F F' F'' G G' H H' τ₁ τ₂ K))

/-- **Two out of three for the pasted comparison.**  If the derived comparisons of the two
squares are invertible at the relevant objects, so is the derived comparison of the pasted
rectangle: the remaining factors in `derived_paste` are components of isomorphisms. -/
public theorem isIso_derived_paste_app (X : DerivedCategory.Plus A)
    (h₁ : IsIso ((derived F F' G G' τ₁ (exactUnitIso G)).app X))
    (h₂ : IsIso ((derived F' F'' H H' τ₂ (exactUnitIso H)).app
      (G'.rightDerivedFunctorPlus.obj X))) :
    IsIso ((derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
      (exactUnitIso (G ⋙ H))).app X) := by
  have := h₁
  have := h₂
  rw [NatTrans.congr_app (derived_paste F F' F'' G G' H H' τ₁ τ₂) X]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **The degree-`n` cohomology of the pasted comparison.**  This is the form in which the
pasting law descends to the base change map on higher direct images, which is the degree-`n`
cohomology of the derived comparison. -/
public theorem homologyFunctor_map_derived_paste_app (n : ℤ) (X : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor D₂ n).map
        ((derived F F'' (G ⋙ H) (G' ⋙ H') (pasteTrans F F' F'' G G' H H' τ₁ τ₂)
          (exactUnitIso (G ⋙ H))).app X) =
      (DerivedCategory.Plus.homologyFunctor D₂ n).map
          ((exactDerivedCompIso G H).hom.app (F.rightDerivedFunctorPlus.obj X)) ≫
        (DerivedCategory.Plus.homologyFunctor D₂ n).map
            (H.rightDerivedFunctorPlus.map
              ((derived F F' G G' τ₁ (exactUnitIso G)).app X)) ≫
          (DerivedCategory.Plus.homologyFunctor D₂ n).map
              ((derived F' F'' H H' τ₂ (exactUnitIso H)).app
                (G'.rightDerivedFunctorPlus.obj X)) ≫
            (DerivedCategory.Plus.homologyFunctor D₂ n).map
              (F''.rightDerivedFunctorPlus.map
                ((exactDerivedCompIso G' H').inv.app X)) := by
  rw [NatTrans.congr_app (derived_paste F F' F'' G G' H H' τ₁ τ₂) X]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]

end PasteAssembly

end Stacks.Cohomology.BaseChange

end
