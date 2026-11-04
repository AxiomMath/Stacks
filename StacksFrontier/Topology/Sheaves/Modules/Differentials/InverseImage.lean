module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksFrontier.Topology.Sheaves.Modules.SquareZeroExtension

/-!
# Inverse images of sheaves of modules along a continuous map

Along a continuous map `f : Y ⟶ X`, a sheaf of modules over a sheaf of commutative rings on
`X` has an inverse image: the sheaf-module pullback along the unit `O ⟶ f_* f⁻¹O` of the
inverse-image/pushforward adjunction on sheaves of rings.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.opensMap`: the functor on opens underlying inverse image.
* `AlgebraicGeometry.SheafOfModules.inverseImageRingHom`: the unit `O ⟶ f_* f⁻¹O`, after
  forgetting commutativity.
* `AlgebraicGeometry.SheafOfModules.inverseImageModule`: the inverse image of a sheaf of
  modules.
* `AlgebraicGeometry.SheafOfModules.inverseImageModuleUnit`: the unit sending a local section
  to its inverse-image section.
* `AlgebraicGeometry.SheafOfModules.pushforwardInverseImageDerivation`: the comparison map
  sending a relative derivation for the inverse-image rings to a relative derivation for the
  original morphism with values in the pushforward.
* `AlgebraicGeometry.SheafOfModules.IsInverseImageDerivationComparison`: the property that
  this comparison map is bijective for every coefficient sheaf.
* `AlgebraicGeometry.SheafOfModules.pushforwardSqZeroHom`: a relative derivation with values in
  a pushforward, read as a morphism of sheaves of commutative rings into the pushforward of a
  square-zero extension.
* `AlgebraicGeometry.SheafOfModules.inverseImageDerivation`: the inverse image of a relative
  derivation.
* `AlgebraicGeometry.SheafOfModules.pullbackDifferentialsIso`: the canonical comparison
  isomorphism.

## Main results

* `AlgebraicGeometry.SheafOfModules.isInverseImageDerivationComparison`: the comparison map is
  bijective, which is the content of Tag 08RR.
* `AlgebraicGeometry.SheafOfModules.inverseImageDerivation_isUniversal`: the inverse image of
  the universal derivation is universal.
* `AlgebraicGeometry.SheafOfModules.pullbackDifferentialsIso_compatible`: the comparison
  isomorphism carries the inverse image of the universal derivation to the universal
  derivation.
* `AlgebraicGeometry.SheafOfModules.pullbackDifferentialsIso_unique`: that compatibility
  characterizes the comparison isomorphism.

## Implementation notes

Taking the inverse image of a module to be the sheaf-module pullback along the unit makes the
object here the actual inverse image, rather than an unspecified module carrying a derivation.
The sheaf-module pullback construction requires the space, the rings and the modules to lie in
one universe.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/


@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace
open CategoryTheory.Functor
open Stacks.Smooth

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] Stacks.Smooth.moduleMulOpposite

/-- The functor on opens underlying inverse image along a continuous map. -/
noncomputable abbrev opensMap {X Y : TopCat.{u}} (f : Y ⟶ X) :
    CategoryTheory.Functor (Opens X) (Opens Y) :=
  Opens.map f

/-- The unit map `O ⟶ f_* f^{-1}O`, after forgetting commutativity. -/
noncomputable def inverseImageRingHom {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : TopCat.Sheaf CommRingCat.{u} X) :
    underlyingRingSheaf O ⟶
      ((opensMap f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
    (underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O)) :=
  ObjectProperty.homMk (whiskerRight
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O).hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The inverse image of an `O`-module along a continuous map. -/
noncomputable def inverseImageModule {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : TopCat.Sheaf CommRingCat.{u} X)
    (M : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) :
    _root_.SheafOfModules.{u} (underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O)) := by
  letI : (PresheafOfModules.pushforward.{u} (inverseImageRingHom f O).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  exact (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f O)).obj M

/-- The unit sending a local section of a module to its inverse-image section. -/
noncomputable def inverseImageModuleUnit {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : TopCat.Sheaf CommRingCat.{u} X)
    (M : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) :
    M ⟶ (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj
      (inverseImageModule f O M) := by
  letI : (PresheafOfModules.pushforward.{u} (inverseImageRingHom f O).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  exact (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
    (inverseImageRingHom f O)).unit.app M


section Universality

variable {X Y : TopCat.{u}} (f : Y ⟶ X) {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- Pushforward of presheaves of modules along `inverseImageRingHom f O` is a right adjoint. -/
instance isRightAdjoint_presheafPushforward_inverseImageRingHom
    (O : TopCat.Sheaf CommRingCat.{u} X) :
    (PresheafOfModules.pushforward.{u} (inverseImageRingHom f O).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- Pushforward of sheaves of modules along `inverseImageRingHom f O` is a right adjoint. -/
instance isRightAdjoint_pushforward_inverseImageRingHom
    (O : TopCat.Sheaf CommRingCat.{u} X) :
    (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).IsRightAdjoint :=
  _root_.SheafOfModules.instIsRightAdjointPushforward _

/-- The inverse-image/pushforward adjunction on sheaves of modules along `f`. -/
noncomputable def inverseImageAdjunction (O : TopCat.Sheaf CommRingCat.{u} X) :
    _root_.SheafOfModules.pullback.{u} (inverseImageRingHom f O) ⊣
      _root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O) :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction _

/-- The inverse image of `M` is its sheaf-module pullback along `inverseImageRingHom f O`. -/
theorem inverseImageModule_eq (O : TopCat.Sheaf CommRingCat.{u} X)
    (M : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) :
    inverseImageModule f O M =
      (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f O)).obj M :=
  rfl

/-- The unit `inverseImageModuleUnit f O M` is the unit of `inverseImageAdjunction f O` at `M`. -/
theorem inverseImageModuleUnit_eq (O : TopCat.Sheaf CommRingCat.{u} X)
    (M : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) :
    inverseImageModuleUnit f O M = (inverseImageAdjunction f O).unit.app M :=
  rfl

/-- Equal morphisms of sheaves of commutative rings agree on sections. -/
private theorem sheaf_hom_app_apply_congr {Z : TopCat.{u}} {A B : TopCat.Sheaf CommRingCat.{u} Z}
    {m m' : A ⟶ B} (h : m = m') (U : (Opens Z)ᵒᵖ) (x : A.obj.obj U) :
    (m.hom.app U).hom x = (m'.hom.app U).hom x :=
  h ▸ rfl

/-- Morphisms of sheaves of commutative rings are equal if they agree on sections. -/
private theorem sheaf_hom_ext_apply {Z : TopCat.{u}} {A B : TopCat.Sheaf CommRingCat.{u} Z}
    {m m' : A ⟶ B} (h : ∀ (U : (Opens Z)ᵒᵖ) (x : A.obj.obj U),
      (m.hom.app U).hom x = (m'.hom.app U).hom x) : m = m' :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext (h U))))

/-- Naturality of the inverse-image unit on sheaves of rings, on sections. -/
theorem inverseImageRingHom_naturality_apply (phi : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ)
    (a : O₁.obj.obj U) :
    ((inverseImageRingHom f O₂).hom.app U).hom ((phi.hom.app U).hom a) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi).hom.app
          ((opensMap f).op.obj U)).hom
        (((inverseImageRingHom f O₁).hom.app U).hom a) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.naturality phi
  replace h := congrArg (fun m : O₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂) => (m.hom.app U).hom a) h
  simp only [Functor.id_map, Functor.comp_map] at h
  show (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O₂).hom.app
      U).hom ((phi.hom.app U).hom a) = _
  exact h

/-- A relative derivation for the inverse-image morphism of rings, read along the unit
`O ⟶ f_* f⁻¹O`, is a relative derivation for the original morphism with values in the
pushforward. -/
noncomputable def pushforwardInverseImageDerivation (phi : O₁ ⟶ O₂)
    (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂)))
    (δ : SheafDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) N) :
    SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N) where
  d {U} := (δ.d (X := (opensMap f).op.obj U)).comp
      ((inverseImageRingHom f O₂).hom.app U).hom.toAddMonoidHom
  d_mul a b :=
    (congrArg δ.d (map_mul ((inverseImageRingHom f O₂).hom.app _).hom a b)).trans
      (δ.d_mul _ _)
  d_map {U} {V} i x := by
    refine (congrArg δ.d ?_).trans (δ.d_map ((opensMap f).op.map i) _)
    exact congrArg (fun m : (underlyingRingSheaf O₂).obj.obj U ⟶
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂)).obj.obj
        ((opensMap f).op.obj V) => m.hom x)
      ((inverseImageRingHom f O₂).hom.naturality i)
  d_app a :=
    (congrArg δ.d (inverseImageRingHom_naturality_apply f phi _ a)).trans (δ.d_app _)

/-- The comparison derivation sends a section `b` to `δ` of its inverse-image section. -/
@[simp]
theorem pushforwardInverseImageDerivation_d (phi : O₁ ⟶ O₂)
    (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂)))
    (δ : SheafDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) N)
    (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U) :
    (pushforwardInverseImageDerivation f phi N δ).d b =
      δ.d (((inverseImageRingHom f O₂).hom.app U).hom b) :=
  rfl

/-- The comparison map is compatible with postcomposition by a morphism of sheaves of
modules, so it is a natural transformation of the two derivation functors. -/
theorem pushforwardInverseImageDerivation_postcomp (phi : O₁ ⟶ O₂)
    {N N' : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂))}
    (δ : SheafDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) N)
    (m : N ⟶ N') :
    pushforwardInverseImageDerivation f phi N' (δ.postcomp m.val) =
      (pushforwardInverseImageDerivation f phi N δ).postcomp
        ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).map m).val :=
  rfl

/-- Postcomposing a derivation twice is postcomposing by the composite. -/
theorem postcomp_postcomp {Z : TopCat.{u}} {R : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u}}
    {S : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u}} {psi : S ⟶ R}
    {M M' M'' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (d : M.Derivation' psi) (a : M ⟶ M') (b : M' ⟶ M'') :
    (d.postcomp a).postcomp b = d.postcomp (a ≫ b) :=
  rfl

/-- For every sheaf of modules over the inverse-image rings, reading a relative derivation
along the unit `O₂ ⟶ f_* f⁻¹O₂` is a bijection onto the relative derivations of `phi` with
values in the pushforward. -/
def IsInverseImageDerivationComparison (f : Y ⟶ X) (phi : O₁ ⟶ O₂) : Prop :=
  ∀ (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂))),
    Function.Bijective (pushforwardInverseImageDerivation f phi N)

section SquareZero

variable (N : _root_.SheafOfModules.{u}
  (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂)))

/-- The unit `O ⟶ f_* f⁻¹O` of the inverse-image/pushforward adjunction on sheaves of
*commutative* rings, on sections. The morphism of sheaves of rings `inverseImageRingHom` is this
map after forgetting commutativity, and the square-zero extension needs the commutative
spelling. -/
noncomputable def inverseImageRingUnitApp (O : TopCat.Sheaf CommRingCat.{u} X)
    (U : (Opens X)ᵒᵖ) :
    ↥(O.obj.obj U) →+* ↥(((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).obj.obj
      ((opensMap f).op.obj U)) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
    O).hom.app U).hom

/-- `inverseImageRingUnitApp f O U` agrees with the component of `inverseImageRingHom f O`. -/
theorem inverseImageRingUnitApp_apply (O : TopCat.Sheaf CommRingCat.{u} X) (U : (Opens X)ᵒᵖ)
    (b : O.obj.obj U) :
    inverseImageRingUnitApp f O U b = ((inverseImageRingHom f O).hom.app U).hom b :=
  rfl

/-- Transposing a morphism of sheaves of commutative rings out of the inverse image, on
sections: the transpose at `b` is the morphism evaluated at the inverse-image section of `b`. -/
theorem pullbackPushforwardAdjunction_homEquiv_app_apply
    (T : TopCat.Sheaf CommRingCat.{u} Y)
    (s : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂ ⟶ T) (U : (Opens X)ᵒᵖ)
    (b : O₂.obj.obj U) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv O₂ T)
        s).hom.app U).hom b
      = (s.hom.app ((opensMap f).op.obj U)).hom (inverseImageRingUnitApp f O₂ U b) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The derivation underlying a relative derivation of `phi` with values in the pushforward of
`N`, written as an additive map into the plain sections of `N`. -/
noncomputable def pushforwardDerivationApp (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) :
    ↥(O₂.obj.obj U) →+ ↥(N.val.obj ((opensMap f).op.obj U)) :=
  D.d

/-- The Leibniz rule for a relative derivation with values in a pushforward, written with the
scalars acting through the inverse-image unit. This is the form the square-zero extension of the
inverse-image rings asks for; the derivation's own `d_mul` has the scalars acting through the
restriction of scalars along that same unit. -/
theorem pushforwardDerivationApp_mul (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) (a b : ↥(O₂.obj.obj U)) :
    pushforwardDerivationApp f N phi D U (a * b)
      = inverseImageRingUnitApp f O₂ U a • pushforwardDerivationApp f N phi D U b
        + inverseImageRingUnitApp f O₂ U b • pushforwardDerivationApp f N phi D U a :=
  D.d_mul a b

/-- The component over an open of
`AlgebraicGeometry.SheafOfModules.pushforwardSqZeroHom`. -/
noncomputable def pushforwardSqZeroApp (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) :
    O₂.obj.obj U ⟶ (sqZeroPresheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂) N).obj
      ((opensMap f).op.obj U) :=
  CommRingCat.ofHom (sqZeroRingHom (inverseImageRingUnitApp f O₂ U)
    (pushforwardDerivationApp f N phi D U) (pushforwardDerivationApp_mul f N phi D U))

/-- The first coordinate of `pushforwardSqZeroApp` at `b` is the inverse-image section of `b`. -/
@[simp]
theorem pushforwardSqZeroApp_apply_fst (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U) :
    ((pushforwardSqZeroApp f N phi D U).hom b).fst = inverseImageRingUnitApp f O₂ U b :=
  sqZeroRingHom_fst _ _ (pushforwardDerivationApp_mul f N phi D U) b

/-- The second coordinate of `pushforwardSqZeroApp` at `b` is `D.d b`. -/
@[simp]
theorem pushforwardSqZeroApp_apply_snd (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U) :
    ((pushforwardSqZeroApp f N phi D U).hom b).snd = D.d b :=
  sqZeroRingHom_snd _ _ (pushforwardDerivationApp_mul f N phi D U) b

/-- **A relative derivation of `phi` with values in the pushforward of `N`, read as a morphism
of sheaves of commutative rings.** The map `b ↦ (b', D b)`, with `b'` the inverse-image section
of `b`, is a morphism of sheaves of commutative rings from `O₂` to the pushforward of the
square-zero extension of the inverse-image rings by `N`; multiplicativity is exactly the Leibniz
rule for `D`, whose scalars act through the inverse-image unit. -/
noncomputable def pushforwardSqZeroHom (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N)) :
    O₂ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      (sqZeroSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂) N) :=
  ObjectProperty.homMk
    { app := pushforwardSqZeroApp f N phi D
      naturality := fun U U' h ↦ CommRingCat.hom_ext (RingHom.ext fun b ↦ by
        change (pushforwardSqZeroApp f N phi D U').hom ((O₂.obj.map h).hom b)
            = ((sqZeroPresheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂) N).map
                ((opensMap f).op.map h)).hom ((pushforwardSqZeroApp f N phi D U).hom b)
        refine TrivSqZeroExt.ext ?_ ?_
        · refine (pushforwardSqZeroApp_apply_fst f N phi D U' _).trans (Eq.trans ?_
            ((sqZeroPresheaf_map_fst _ N ((opensMap f).op.map h) _).trans
              (congrArg
                (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂).obj.map
                  ((opensMap f).op.map h)).hom
                (pushforwardSqZeroApp_apply_fst f N phi D U b))).symm)
          exact congrArg (fun m : (underlyingRingSheaf O₂).obj.obj U ⟶
            (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂)).obj.obj
              ((opensMap f).op.obj U') => m.hom b)
            ((inverseImageRingHom f O₂).hom.naturality h)
        · refine (pushforwardSqZeroApp_apply_snd f N phi D U' _).trans (Eq.trans ?_
            ((sqZeroPresheaf_map_snd _ N ((opensMap f).op.map h) _).trans
              (congrArg (sectionRestrict N ((opensMap f).op.map h))
                (pushforwardSqZeroApp_apply_snd f N phi D U b))).symm)
          exact D.d_map h b) }

/-- The component of `pushforwardSqZeroHom` over an open `U` is `pushforwardSqZeroApp`. -/
@[simp]
theorem pushforwardSqZeroHom_app (phi : O₁ ⟶ O₂)
    (D : SheafDerivation phi
      ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj N))
    (U : (Opens X)ᵒᵖ) :
    (pushforwardSqZeroHom f N phi D).hom.app U = pushforwardSqZeroApp f N phi D U :=
  rfl

end SquareZero

section DerivationBijection

/-- Reading a relative derivation for the inverse-image morphism of rings along the unit
`O₂ ⟶ f_* f⁻¹O₂` is a bijection onto the relative derivations of `phi` with values in the
pushforward. -/
theorem isInverseImageDerivationComparison (phi : O₁ ⟶ O₂) :
    IsInverseImageDerivationComparison f phi := by
  intro N
  let O' := (TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂
  let phi' := (TopCat.Sheaf.pullback CommRingCat.{u} f).map phi
  let T := sqZeroSheaf O' N
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f
  have hcomp : ∀ (δ : SheafDerivation phi' N) (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U),
      ((A.homEquiv O₂ T (sqZeroSectionOfDerivation O' N phi' δ)).hom.app U).hom b
        = TrivSqZeroExt.inl (inverseImageRingUnitApp f O₂ U b)
          + TrivSqZeroExt.inr (δ.d (((inverseImageRingHom f O₂).hom.app U).hom b)) := by
    intro δ U b
    refine (pullbackPushforwardAdjunction_homEquiv_app_apply f T _ U b).trans ?_
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (sqZeroSectionApp_apply_fst O' N phi' δ _ _).trans (fst_inl_add_inr _ _).symm
    · exact (sqZeroSectionApp_apply_snd O' N phi' δ _ _).trans (snd_inl_add_inr _ _).symm
  constructor
  · intro δ₁ δ₂ hδ
    have hsec : sqZeroSectionOfDerivation O' N phi' δ₁
        = sqZeroSectionOfDerivation O' N phi' δ₂ := by
      refine (A.homEquiv O₂ T).injective (sheaf_hom_ext_apply fun U b ↦ ?_)
      refine (hcomp δ₁ U b).trans (Eq.trans ?_ (hcomp δ₂ U b).symm)
      refine congrArg (fun z : ↥(N.val.obj ((opensMap f).op.obj U)) ↦
        TrivSqZeroExt.inl (inverseImageRingUnitApp f O₂ U b) + TrivSqZeroExt.inr z) ?_
      exact PresheafOfModules.Derivation.congr_d hδ b
    refine derivation_ext O' N phi' fun V a ↦ ?_
    refine (sqZeroSectionApp_apply_snd O' N phi' δ₁ V a).symm.trans (Eq.trans ?_
      (sqZeroSectionApp_apply_snd O' N phi' δ₂ V a))
    exact congrArg TrivSqZeroExt.snd (sheaf_hom_app_apply_congr hsec V a)
  · intro D
    let t := pushforwardSqZeroHom f N phi D
    let s := (A.homEquiv O₂ T).symm t
    have hst : A.homEquiv O₂ T s = t := Equiv.apply_symm_apply _ _
    have hsapp : ∀ (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U),
        (s.hom.app ((opensMap f).op.obj U)).hom (inverseImageRingUnitApp f O₂ U b)
          = (pushforwardSqZeroApp f N phi D U).hom b := by
      intro U b
      refine (pullbackPushforwardAdjunction_homEquiv_app_apply f T s U b).symm.trans ?_
      exact sheaf_hom_app_apply_congr hst U b
    have hid : A.homEquiv O₂ O' (𝟙 O') = A.unit.app O₂ := by
      rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    have hsplit : s ≫ sqZeroProj O' N = 𝟙 O' := by
      refine (A.homEquiv O₂ O').injective ?_
      rw [Adjunction.homEquiv_naturality_right, hst, hid]
      refine sheaf_hom_ext_apply fun U b ↦ ?_
      show ((sqZeroProj O' N).hom.app ((opensMap f).op.obj U)).hom
            ((pushforwardSqZeroApp f N phi D U).hom b)
          = inverseImageRingUnitApp f O₂ U b
      exact pushforwardSqZeroApp_apply_fst f N phi D U b
    have htriv : (TopCat.Sheaf.pullback CommRingCat.{u} f).map phi ≫ s
        = (TopCat.Sheaf.pullback CommRingCat.{u} f).map phi ≫ sqZeroInl O' N := by
      refine (A.homEquiv O₁ T).injective ?_
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left, hst,
        Adjunction.homEquiv_unit]
      refine sheaf_hom_ext_apply fun U a ↦ ?_
      show (pushforwardSqZeroApp f N phi D U).hom ((phi.hom.app U).hom a)
          = ((sqZeroInl O' N).hom.app ((opensMap f).op.obj U)).hom
              (inverseImageRingUnitApp f O₂ U ((phi.hom.app U).hom a))
      refine TrivSqZeroExt.ext ?_ ?_
      · exact (pushforwardSqZeroApp_apply_fst f N phi D U _).trans
          (sqZeroInl_app_apply_fst O' N _ _).symm
      · refine (pushforwardSqZeroApp_apply_snd f N phi D U _).trans (Eq.trans ?_
          (sqZeroInl_app_apply_snd O' N _ _).symm)
        exact D.d_app a
    refine ⟨derivationOfSqZeroSection O' N phi' s hsplit htriv, ?_⟩
    refine derivation_ext O₂ _ phi fun U b ↦ ?_
    refine Eq.trans ?_ (pushforwardSqZeroApp_apply_snd f N phi D U b)
    exact congrArg TrivSqZeroExt.snd (hsapp U b)

end DerivationBijection

section Comparison

variable {phi : O₁ ⟶ O₂}

/-- The inverse image of a relative derivation, specified by its action on the images of local
sections under the inverse-image units. -/
@[stacks 08RR "inverse image of the derivation"]
noncomputable def inverseImageDerivation
    {M : _root_.SheafOfModules.{u} (underlyingRingSheaf O₂)}
    (d : SheafDerivation phi M) :
    {δ : SheafDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)
        (inverseImageModule f O₂ M) //
      ∀ (U : (Opens X)ᵒᵖ) (b : O₂.obj.obj U),
        δ.d (((inverseImageRingHom f O₂).hom.app U) b) =
          ((inverseImageModuleUnit f O₂ M).val.app U).hom (d.d b)} :=
  ⟨Classical.choose ((isInverseImageDerivationComparison f phi (inverseImageModule f O₂ M)).2
      (d.postcomp (inverseImageModuleUnit f O₂ M).val)),
    fun _U b => PresheafOfModules.Derivation.congr_d
      (Classical.choose_spec
        ((isInverseImageDerivationComparison f phi (inverseImageModule f O₂ M)).2
          (d.postcomp (inverseImageModuleUnit f O₂ M).val))) b⟩

/-- The comparison map sends the inverse image of `d` to `d` postcomposed with the unit
`inverseImageModuleUnit f O₂ M`. -/
theorem pushforwardInverseImageDerivation_inverseImageDerivation
    {M : _root_.SheafOfModules.{u} (underlyingRingSheaf O₂)}
    (d : SheafDerivation phi M) :
    pushforwardInverseImageDerivation f phi _ (inverseImageDerivation f d).val =
      d.postcomp (inverseImageModuleUnit f O₂ M).val :=
  Classical.choose_spec ((isInverseImageDerivationComparison f phi (inverseImageModule f O₂ M)).2
    (d.postcomp (inverseImageModuleUnit f O₂ M).val))

/-- The inverse image of the universal derivation remains universal. -/
@[stacks 08RR "universality"]
theorem inverseImageDerivation_isUniversal (phi : O₁ ⟶ O₂) :
    IsUniversal (inverseImageDerivation f (universalDerivation phi)).val := by
  intro F D
  have hpc : ∀ {m m' : moduleOfDifferentials phi ⟶
      (_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj F}, m = m' →
      (universalDerivation phi).postcomp m.val = (universalDerivation phi).postcomp m'.val :=
    fun h ↦ h ▸ rfl
  have key : ∀ h : inverseImageModule f O₂ (moduleOfDifferentials phi) ⟶ F,
      pushforwardInverseImageDerivation f phi F
          ((inverseImageDerivation f (universalDerivation phi)).val.postcomp h.val) =
        (universalDerivation phi).postcomp
          (((inverseImageAdjunction f O₂).homEquiv
            (moduleOfDifferentials phi) F h).val) := by
    intro h
    refine (pushforwardInverseImageDerivation_postcomp f phi _ h).trans ?_
    refine Eq.trans (congrArg (fun d : SheafDerivation phi
        ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj
          (inverseImageModule f O₂ (moduleOfDifferentials phi))) =>
        d.postcomp ((_root_.SheafOfModules.pushforward
          (inverseImageRingHom f O₂)).map h).val)
      (pushforwardInverseImageDerivation_inverseImageDerivation f
        (universalDerivation phi))) ?_
    refine (postcomp_postcomp _ _ _).trans ?_
    exact hpc (Adjunction.homEquiv_unit (inverseImageAdjunction f O₂) _ _ h).symm
  obtain ⟨k, hk, hk'⟩ := universalDerivation_isUniversal.{u, u, u} phi
    ((_root_.SheafOfModules.pushforward (inverseImageRingHom f O₂)).obj F)
    (pushforwardInverseImageDerivation f phi F D)
  refine ⟨((inverseImageAdjunction f O₂).homEquiv _ F).symm k,
    (isInverseImageDerivationComparison f phi F).1 ?_, ?_⟩
  · exact (key _).trans
      ((hpc (Equiv.apply_symm_apply ((inverseImageAdjunction f O₂).homEquiv _ F) k)).trans hk)
  · intro h hh
    refine ((inverseImageAdjunction f O₂).homEquiv _ F).eq_symm_apply.mpr (hk' _ ?_)
    exact (key h).symm.trans
      (congrArg (pushforwardInverseImageDerivation f phi F) hh)

/-- The canonical morphism from the inverse image of the differentials, determined by
carrying the inverse image of the universal derivation to the universal derivation. -/
noncomputable def pullbackDifferentialsHom (phi : O₁ ⟶ O₂) :
    inverseImageModule f O₂ (moduleOfDifferentials phi) ⟶
      moduleOfDifferentials ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) :=
  Classical.choose (inverseImageDerivation_isUniversal f phi _
    (universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)))

/-- `pullbackDifferentialsHom f phi` carries the inverse image of the universal derivation of
`phi` to the universal derivation of the inverse-image morphism. -/
theorem pullbackDifferentialsHom_spec (phi : O₁ ⟶ O₂) :
    (inverseImageDerivation f (universalDerivation phi)).val.postcomp
        (pullbackDifferentialsHom f phi).val =
      universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) :=
  (Classical.choose_spec (inverseImageDerivation_isUniversal f phi _
    (universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)))).1

/-- The canonical morphism to the inverse image of the differentials, determined by carrying
the universal derivation to the inverse image of the universal derivation. -/
noncomputable def pullbackDifferentialsInv (phi : O₁ ⟶ O₂) :
    moduleOfDifferentials ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) ⟶
      inverseImageModule f O₂ (moduleOfDifferentials phi) :=
  Classical.choose (universalDerivation_isUniversal
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) _
    (inverseImageDerivation f (universalDerivation phi)).val)

/-- `pullbackDifferentialsInv f phi` carries the universal derivation of the inverse-image
morphism to the inverse image of the universal derivation of `phi`. -/
theorem pullbackDifferentialsInv_spec (phi : O₁ ⟶ O₂) :
    (universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)).postcomp
        (pullbackDifferentialsInv f phi).val =
      (inverseImageDerivation f (universalDerivation phi)).val :=
  (Classical.choose_spec (universalDerivation_isUniversal
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) _
    (inverseImageDerivation f (universalDerivation phi)).val)).1

/-- The canonical identification between the inverse image of the module of relative
differentials and the module of relative differentials of the inverse-image morphism. -/
@[stacks 08RR "canonical identification",
  stacks 08RQ "the open-inclusion case: the identification of the restriction of the"]
noncomputable def pullbackDifferentialsIso (phi : O₁ ⟶ O₂) :
    inverseImageModule f O₂ (moduleOfDifferentials phi) ≅
      moduleOfDifferentials ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) where
  hom := pullbackDifferentialsHom f phi
  inv := pullbackDifferentialsInv f phi
  hom_inv_id :=
    (inverseImageDerivation_isUniversal f phi _
        (inverseImageDerivation f (universalDerivation phi)).val).unique
      (((postcomp_postcomp _ _ _).symm.trans
        (congrArg (fun d : SheafDerivation
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)
            (moduleOfDifferentials ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)) =>
          d.postcomp (pullbackDifferentialsInv f phi).val)
          (pullbackDifferentialsHom_spec f phi))).trans
        (pullbackDifferentialsInv_spec f phi)) rfl
  inv_hom_id :=
    (universalDerivation_isUniversal ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) _
        (universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi))).unique
      (((postcomp_postcomp _ _ _).symm.trans
        (congrArg (fun d : SheafDerivation
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)
            (inverseImageModule f O₂ (moduleOfDifferentials phi)) =>
          d.postcomp (pullbackDifferentialsHom f phi).val)
          (pullbackDifferentialsInv_spec f phi))).trans
        (pullbackDifferentialsHom_spec f phi)) rfl

/-- The canonical identification carries the inverse image of the universal derivation to the
universal derivation. -/
@[stacks 08RR "compatibility with universal derivations"]
theorem pullbackDifferentialsIso_compatible (phi : O₁ ⟶ O₂) :
    (inverseImageDerivation f (universalDerivation phi)).val.postcomp
        (pullbackDifferentialsIso f phi).hom.val =
      universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi) :=
  pullbackDifferentialsHom_spec f phi

/-- Compatibility with universal derivations uniquely characterizes the canonical
identification. -/
@[stacks 08RR "canonicity"]
theorem pullbackDifferentialsIso_unique (phi : O₁ ⟶ O₂)
    (e : inverseImageModule f O₂ (moduleOfDifferentials phi) ≅
      moduleOfDifferentials ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi))
    (he : (inverseImageDerivation f (universalDerivation phi)).val.postcomp e.hom.val =
      universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi)) :
    e = pullbackDifferentialsIso f phi :=
  Iso.ext ((inverseImageDerivation_isUniversal f phi _
    (universalDerivation ((TopCat.Sheaf.pullback CommRingCat.{u} f).map phi))).unique he
    (pullbackDifferentialsIso_compatible f phi))

end Comparison

end Universality


end AlgebraicGeometry.SheafOfModules
