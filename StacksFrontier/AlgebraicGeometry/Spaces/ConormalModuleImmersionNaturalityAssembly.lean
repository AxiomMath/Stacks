module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalChangeOfAmbientAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalCoborderSquareAmbientIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareTransportAgreement
public import StacksFrontier.AlgebraicGeometry.Conormal.SelfIsoSquareMap
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheafSquareComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackComposition
public import StacksFrontier.CategoryTheory.SquareTransportComposition

/-!
# Stacking a change of ambient underneath a conormal naturality square

For a square of morphisms of represented algebraic spaces whose horizontal edges are immersions,
the canonical map of [Stacks Project, Tag 04CP], preceded by the inverse image of a comparison
isomorphism, can be written as the transport of the inverse image, the associated module of a map
of Zariski modules on the source, and a comparison isomorphism. This file shows that this shape is
preserved by stacking a change of ambient (a square with an identity down its left-hand side)
underneath a square, for arbitrary comparison isomorphisms, and proves the congruence and unit
lemmas used to assemble it.

## Main results

* `AlgebraicGeometry.Space.conormalStack_ambient_comp`: the transported naturality square of the
  rectangle obtained by stacking a change of ambient underneath a square.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_hom_eq_of_eq`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq` and
  `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_eq_of_eq_left`: the transport of the inverse
  image, the comparison of [Stacks Project, Tag 03LU] and the map of [Stacks Project, Tag 04CP]
  at two equal arguments, up to `CategoryTheory.eqToHom` on objects.
* `AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement_transport`: the change-of-ambient
  agreement with the head of its right-hand side written as a transport.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id_right`: the composition
  law of the transport at a trailing identity.
* `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_congr_right` and
  `Stacks.ClosedImmersion.conormalSheafMap_congr_right`: the canonical maps depend on the
  right-hand vertical morphism only through its value.
* `AlgebraicGeometry.Space.modulePullbackCompIso_id_right`: the right unit law of
  [Stacks Project, Tag 03LU].

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry

universe u

namespace Stacks.ClosedImmersion

/-- The ringed-space canonical map of [Stacks Project, Tag 01R4] depends on the right-hand
vertical morphism of the square only through its value. -/
theorem conormalSheafMap_congr_right {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f : Z ⟶ W} {k₁ k₂ : Z' ⟶ W'} (hk : k₁ = k₂) (comm₁ : i ≫ k₁ = f ≫ j)
    (comm₂ : i ≫ k₂ = f ≫ j) :
    conormalSheafMap comm₁ = conormalSheafMap comm₂ := by
  subst hk
  rfl

end Stacks.ClosedImmersion

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical map `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` of
[Stacks Project, Tag 04CP] depends on the right-hand vertical morphism of the square only through
its value. -/
theorem kernelIdealZPowSquareMap_congr_right {Z X Z' X' : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') {g₁ g₂ : X ⟶ X'} (hg : g₁ = g₂)
    (hsq₁ : i ≫ g₁ = f ≫ i') (hsq₂ : i ≫ g₂ = f ≫ i') (n : ℤ) :
    kernelIdealZPowSquareMap B S hS i i' f g₁ hsq₁ n =
      kernelIdealZPowSquareMap B S hS i i' f g₂ hsq₂ n := by
  subst hg
  rfl

end AlgebraicGeometry.Space

namespace Stacks.CategoryTheory

/-- Whiskering `e : G ≅ 𝟭 C` on the right by `F` and composing with the left unitor gives, at an
object `Z`, the morphism `F.map (e.hom.app Z)`. -/
theorem isoWhiskerRight_trans_leftUnitor_hom_app {C : Type*} [Category* C] {D : Type*}
    [Category* D] (F : C ⥤ D) {G : C ⥤ C} (e : G ≅ 𝟭 C) (Z : C) :
    (Functor.isoWhiskerRight e F ≪≫ F.leftUnitor).hom.app Z = F.map (e.hom.app Z) := by
  simp

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]

/-- A pair of mutually cancelling morphisms stays cancelling under two nested functors. -/
theorem map_map_comp_eq_id_of (G : E ⥤ C) (A : D ⥤ E) {X Y : D} (x : X ⟶ Y) (y : Y ⟶ X)
    (hxy : x ≫ y = 𝟙 X) :
    G.map (A.map x) ≫ G.map (A.map y) = 𝟙 (G.obj (A.obj X)) := by
  rw [← G.map_comp, ← A.map_comp, hxy, A.map_id, G.map_id]

/-- If `x` factors as `y ≫ z` and `z` has a right inverse `z'`, then `x ≫ z' = y`. -/
theorem comp_eq_of_eq_comp_inv {A₁ A₂ A₃ : C} {x : A₁ ⟶ A₃} {y : A₁ ⟶ A₂} {z : A₂ ⟶ A₃}
    {z' : A₃ ⟶ A₂} (h : x = y ≫ z) (hz : z ≫ z' = 𝟙 A₂) : x ≫ z' = y := by
  rw [h, Category.assoc, hz, Category.comp_id]

/-- Replacing the head `c` of a three-fold composite `c ≫ m ≫ p` by `t ≫ q` and absorbing `q`
into the middle factor. -/
theorem eq_comp₃_of_head {A₁ A₂ A₃ A₄ A₅ : C} {lhs : A₁ ⟶ A₄} {c : A₁ ⟶ A₃} {m : A₃ ⟶ A₅}
    {p : A₅ ⟶ A₄} {t : A₁ ⟶ A₂} {q : A₂ ⟶ A₃} {m' : A₂ ⟶ A₅}
    (h : lhs = c ≫ m ≫ p) (hc : c = t ≫ q) (hm : q ≫ m = m') : lhs = t ≫ m' ≫ p := by
  rw [h, hc, ← hm]
  simp only [Category.assoc]

/-- A three-fold composite under two nested functors, split. -/
theorem map_map_eq_comp₃_of (G : E ⥤ C) (A : D ⥤ E) {X Y Z W : D} {w : X ⟶ W} (x : X ⟶ Y)
    (y : Y ⟶ Z) (z : Z ⟶ W) (h : w = x ≫ y ≫ z) :
    G.map (A.map w) = G.map (A.map x) ≫ G.map (A.map y) ≫ G.map (A.map z) := by
  rw [h, A.map_comp, A.map_comp, G.map_comp, G.map_comp]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The right unit law of [Stacks Project, Tag 03LU]**: the composition comparison of the
inverse image along `f ≫ 𝟙 Y` is the unit law `AlgebraicGeometry.Space.modulePullbackIdIso` at
`Y`, whiskered with the inverse image along `f`. -/
theorem modulePullbackCompIso_id_right {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    modulePullbackCompIso B S hS f (𝟙 Y) =
      Functor.isoWhiskerRight (modulePullbackIdIso B S hS Y) (modulePullback B S hS f) ≪≫
        (modulePullback B S hS f).leftUnitor :=
  ((modulePushforwardCoherence B S hS).modulePullbackCompIso_id_right f).trans
    (congrArg (fun e : modulePullback B S hS (𝟙 Y) ≅ 𝟭 (Modules.{u, u} B S hS Y.1 Y.2) ↦
        Functor.isoWhiskerRight e (modulePullback B S hS f) ≪≫
          (modulePullback B S hS f).leftUnitor)
      (modulePushforwardCoherence_modulePullbackIdIso B S hS Y))

/-- **The right unit law of [Stacks Project, Tag 03LU] at a module**: the composition comparison
along `f ≫ 𝟙 Y`, read at `M`, is the inverse image along `f` of the unit law at `M`. -/
theorem modulePullbackCompIso_id_right_hom_app {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS f (𝟙 Y)).hom.app M =
      (modulePullback B S hS f).map ((modulePullbackIdIso B S hS Y).hom.app M) :=
  (congr_app (congrArg Iso.hom (modulePullbackCompIso_id_right B S hS f)) M).trans
    (Stacks.CategoryTheory.isoWhiskerRight_trans_leftUnitor_hom_app
      (modulePullback B S hS f) (modulePullbackIdIso B S hS Y) M)

/-! ### The unit law of 03LU at a module, read as the transport along the identity -/

/-- **The unit law of [Stacks Project, Tag 03LU] at an associated module is the transport of the
inverse image along the identity of the site, followed by the Zariski unit law.** -/
theorem modulePullbackIdIso_hom_app_eq_representedAssociatedModulePullbackIso
    (T : BigFppfOver B S hS) (h : yoneda.relativelyRepresentable (yoneda.map (𝟙 T)))
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (modulePullbackIdIso B S hS
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS)).hom.app
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
    (𝓕))) =
      (representedAssociatedModulePullbackIso B S hS (𝟙 T) h 𝓕).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕)) :=
  (Stacks.CategoryTheory.comp_eq_of_eq_comp_inv
      ((representedAssociatedModulePullbackIso_id B S hS T h 𝓕).trans
        (congrArg
          (fun z => z ≫
            (representedSmallEtaleModuleEquivalence B S hS T).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).inv.app 𝓕)))
          (congr_app
            (congrArg Iso.hom
              (Stacks.CategoryTheory.eqToIso_of_refl_trans
                (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS T))
                (modulePullbackIdIso B S hS
                  (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))))
            ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
    (𝓕))))))
      (Stacks.CategoryTheory.map_map_comp_eq_id_of
        (representedSmallEtaleModuleEquivalence B S hS T).functor
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).inv.app 𝓕)
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app 𝓕)
        (Iso.inv_hom_id_app (Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T))
          𝓕))).symm

/-! ### The change of ambient with its head read as a transport -/

/-- **The agreement `AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement` across the change
of ambient, with the head of its right-hand side written as the transport of the inverse image
along `𝟙 R`**, and its middle factor the associated module of a single map of Zariski modules on
the source. -/
theorem conormalChangeOfAmbientAgreement_transport {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    (modulePullback B S hS
        (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))).map
        (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
          (representedSpaceMap B S hS j)
          (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
          (representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
          (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm 1 =
      (representedAssociatedModulePullbackIso B S hS (𝟙 R)
  (relativelyRepresentable_yoneda_map B S hS (𝟙 R))
  (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
    ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
      (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
      (Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j)).hom)) ≫
          (representedConormalKernelIdealZPowIso B S hS (immersionCoborderLift B S hS j)).hom :=
  Stacks.CategoryTheory.eq_comp₃_of_head
    (conormalChangeOfAmbientAgreement B S hS j)
    (modulePullbackIdIso_hom_app_eq_representedAssociatedModulePullbackIso B S hS R
      (relativelyRepresentable_yoneda_map B S hS (𝟙 R)) (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))
    (Stacks.CategoryTheory.map_map_comp_eq_of
      (representedSmallEtaleModuleEquivalence B S hS R).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R) R.left.property)
      ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
        (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))
      ((Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j)).hom) rfl)

/-! ### The transport's composition law at a trailing identity -/

section TrailingIdentity

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  representedSmallEtaleModuleEquivalence

/-- Absorbing an `eqToHom` of an object with itself on each side of a morphism. -/
private theorem eqToHom_comp_comp_eqToHom_of_refl {C : Type*} [Category* C] {X Y : C} (h : X = X)
    (g : X ⟶ Y) (h' : Y = Y) : eqToHom h ≫ g ≫ eqToHom h' = g :=
  (eqToHom_comp_of_refl h _).trans (comp_eqToHom_of_refl h' g)

/-! ### The transport across two spellings of its site morphism -/

/-- **The transport of the inverse image at two equal site morphisms `p = p'`**, with the two
transports of objects made explicit as `eqToHom e` and `eqToHom e'`. -/
theorem representedAssociatedModulePullbackIso_hom_eq_of_eq
    {T₁ T₂ : BigFppfOver B S hS} {p p' : T₁ ⟶ T₂} (hpp : p = p')
    (_hp : yoneda.relativelyRepresentable (yoneda.map p))
    (hp' : yoneda.relativelyRepresentable (yoneda.map p'))
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₂).Modules)
    (e : (modulePullback B S hS (representedSpaceMap B S hS p)).obj
    ((representedSmallEtaleModuleEquivalence B S hS T₂).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property).obj
    (𝓕))) =
      (modulePullback B S hS (representedSpaceMap B S hS p')).obj
    ((representedSmallEtaleModuleEquivalence B S hS T₂).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property).obj
    (𝓕))))
    (e' : (representedSmallEtaleModuleEquivalence B S hS T₁).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).obj
    ((Scheme.Modules.pullback (B.inclusion.map p'.left)).obj 𝓕)) =
      (representedSmallEtaleModuleEquivalence B S hS T₁).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).obj
    ((Scheme.Modules.pullback (B.inclusion.map p.left)).obj 𝓕))) :
    (representedAssociatedModulePullbackIso B S hS p
  (relativelyRepresentable_yoneda_map B S hS p)
  (𝓕)).hom =
      eqToHom e ≫ (representedAssociatedModulePullbackIso B S hS p'
  (relativelyRepresentable_yoneda_map B S hS p')
  (𝓕)).hom ≫ eqToHom e' := by
  subst hpp
  exact (eqToHom_comp_comp_eqToHom_of_refl e _ e').symm

/-- **The transport of the inverse image along `f ≫ 𝟙` is the transport along `f`.** -/
theorem representedAssociatedModulePullbackIso_hom_comp_id
    {T₁ T₂ : BigFppfOver B S hS} (f : T₁ ⟶ T₂)
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₂).Modules) :
    (representedAssociatedModulePullbackIso B S hS (f ≫ 𝟙 T₂)
  (relativelyRepresentable_yoneda_map B S hS (f ≫ 𝟙 T₂))
  (𝓕)).hom =
      (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  (𝓕)).hom := by
  exact (representedAssociatedModulePullbackIso_hom_eq_of_eq B S hS (Category.comp_id f)
    (relativelyRepresentable_yoneda_map B S hS (f ≫ 𝟙 T₂))
    (relativelyRepresentable_yoneda_map B S hS f) 𝓕 rfl rfl).trans
    (eqToHom_comp_comp_eqToHom_of_refl _ _ _)

/-- **The transport of the inverse image along `𝟙 ≫ f` is the transport along `f`.** -/
theorem representedAssociatedModulePullbackIso_hom_id_comp
    {T₁ T₂ : BigFppfOver B S hS} (f : T₁ ⟶ T₂)
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₂).Modules) :
    (representedAssociatedModulePullbackIso B S hS (𝟙 T₁ ≫ f)
  (relativelyRepresentable_yoneda_map B S hS (𝟙 T₁ ≫ f))
  (𝓕)).hom =
      (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  (𝓕)).hom := by
  exact (representedAssociatedModulePullbackIso_hom_eq_of_eq B S hS (Category.id_comp f)
    (relativelyRepresentable_yoneda_map B S hS (𝟙 T₁ ≫ f))
    (relativelyRepresentable_yoneda_map B S hS f) 𝓕 rfl rfl).trans
    (eqToHom_comp_comp_eqToHom_of_refl _ _ _)

/-! ### The comparison of 03LU and the square map across two spellings of an edge -/

/-- **The comparison of [Stacks Project, Tag 03LU] at two equal inner morphisms**, with the two
transports of objects made explicit. -/
theorem modulePullbackCompIso_hom_app_eq_of_eq {W X Y : AlgebraicSpaces B S hS}
    (f : W ⟶ X) {g g' : X ⟶ Y} (hgg : g = g') (M : Modules.{u, u} B S hS Y.1 Y.2)
    (e : (modulePullback B S hS g ⋙ modulePullback B S hS f).obj M =
      (modulePullback B S hS g' ⋙ modulePullback B S hS f).obj M)
    (e' : (modulePullback B S hS (f ≫ g')).obj M = (modulePullback B S hS (f ≫ g)).obj M) :
    (modulePullbackCompIso B S hS f g).hom.app M =
      eqToHom e ≫ (modulePullbackCompIso B S hS f g').hom.app M ≫ eqToHom e' := by
  subst hgg
  exact (eqToHom_comp_comp_eqToHom_of_refl e _ e').symm

/-- **The comparison of [Stacks Project, Tag 03LU] along `f` and the represented identity is the
comparison along `f` and the identity.** -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap_id_right {T₁ T₂ : BigFppfOver B S hS}
    (f : T₁ ⟶ T₂) (M : Modules.{u, u} B S hS
      (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩ : AlgebraicSpaces B S hS).1
      (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩ : AlgebraicSpaces B S hS).2) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS f)
          (representedSpaceMap B S hS (𝟙 T₂))).hom.app M =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS f)
        (𝟙 (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩ :
          AlgebraicSpaces B S hS))).hom.app M := by
  exact (modulePullbackCompIso_hom_app_eq_of_eq B S hS (representedSpaceMap B S hS f)
    (representedSpaceMap_id B S hS T₂) M rfl rfl).trans
    (eqToHom_comp_comp_eqToHom_of_refl _ _ _)

/-- **The canonical map of [Stacks Project, Tag 04CP] at two equal left-hand vertical
morphisms**, with the transport of its source made explicit. -/
theorem kernelIdealZPowSquareMap_eq_of_eq_left {Z X Z' X' : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (i' : Z' ⟶ X') {f f' : Z ⟶ Z'} (hff : f = f') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (hsq' : i ≫ g = f' ≫ i') (n : ℤ)
    (e : (modulePullback B S hS f).obj
          ((modulePullback B S hS i').obj (kernelIdealSheafZPow B S hS i' n).toSheafOfModules) =
        (modulePullback B S hS f').obj
          ((modulePullback B S hS i').obj
            (kernelIdealSheafZPow B S hS i' n).toSheafOfModules)) :
    kernelIdealZPowSquareMap B S hS i i' f g hsq n =
      eqToHom e ≫ kernelIdealZPowSquareMap B S hS i i' f' g hsq' n := by
  subst hff
  exact (congrArg (fun h : i ≫ g = f ≫ i' =>
      kernelIdealZPowSquareMap B S hS i i' f g h n) (proof_irrel hsq hsq')).trans
    (eqToHom_comp_of_refl e _).symm

/-- **The composition law for the transport of the inverse image at a trailing identity**, with
the comparison of [Stacks Project, Tag 03LU] taken along `𝟙` rather than
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 T₂)`, and the transport along `f ≫ 𝟙 T₂` replaced
by the transport along `f`. -/
theorem representedAssociatedModulePullbackIso_comp_id_right
    {T₁ T₂ : BigFppfOver B S hS} (f : T₁ ⟶ T₂)
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₂).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS f)).map
      (representedAssociatedModulePullbackIso B S hS (𝟙 T₂)
  (relativelyRepresentable_yoneda_map B S hS (𝟙 T₂))
  (𝓕)).hom ≫
        (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  ((Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 T₂)))).obj 𝓕)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).map
    ((Scheme.Modules.pullbackComp (B.inclusion.map f.left)
        (B.inclusion.map (Over.Hom.left (𝟙 T₂)))).hom.app 𝓕)) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS f)
          (𝟙 (⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩ :
            AlgebraicSpaces B S hS))).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T₂).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property).obj
    (𝓕))) ≫
        (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  (𝓕)).hom :=
  (representedAssociatedModulePullbackIso_comp_of_eq B S hS f (𝟙 T₂)
      (relativelyRepresentable_yoneda_map B S hS f)
      (relativelyRepresentable_yoneda_map B S hS (𝟙 T₂))
      (relativelyRepresentable_yoneda_map B S hS (f ≫ 𝟙 T₂)) 𝓕 _ rfl).trans
    ((CategoryTheory.eq_whisker
        (modulePullbackCompIso_hom_app_representedSpaceMap_id_right B S hS f
          ((representedSmallEtaleModuleEquivalence B S hS T₂).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property).obj (𝓕)))) _).trans
      (CategoryTheory.whisker_eq _
        (representedAssociatedModulePullbackIso_hom_comp_id B S hS f 𝓕)))

end TrailingIdentity

/-! ### Stacking a change of ambient underneath a square -/

section AmbientStack

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  squarePullbackCompIso representedSmallEtaleModuleEquivalence

variable {R₁ V₁ R₂ V₂ V₃ : BigFppfOver B S hS} (i₁ : R₁ ⟶ V₁) (i₂ : R₂ ⟶ V₂)
    (i₃ : R₂ ⟶ V₃) (f : R₁ ⟶ R₂) (g₁ : V₁ ⟶ V₂) (g₂ : V₂ ⟶ V₃)

/-- **The transported naturality square of the rectangle obtained by stacking a change of ambient
underneath a square.**

The upper square is `(i₁, i₂, f, g₁)` and the lower one `(i₂, i₃, 𝟙, g₂)` — a change of ambient,
with the identity down its left-hand side — each in the shape in which the inverse image along
the left edge of the comparison at the bottom row, followed by the canonical map of
[Stacks Project, Tag 04CP], is the transport of the inverse image, the associated module of a map
of Zariski modules on the source, and the comparison at the top row.  What comes out is that
shape for the outer rectangle, whose map of Zariski modules is the Zariski composition comparison
inverted, the inverse image along `f` of the lower square's, and the upper square's.

The three comparisons `e₁`, `e₂`, `e₃` are arbitrary isomorphisms of the relevant type. -/
theorem conormalStack_ambient_comp
    (e₁ : (representedSmallEtaleModuleEquivalence B S hS R₁).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₁) R₁.left.property).obj
    (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₁).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS i₁)).obj
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS i₁) 1).toSheafOfModules)
    (e₂ : (representedSmallEtaleModuleEquivalence B S hS R₂).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₂) R₂.left.property).obj
    (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₂).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS i₂)).obj
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS i₂) 1).toSheafOfModules)
    (e₃ : (representedSmallEtaleModuleEquivalence B S hS R₂).functor.obj
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₂) R₂.left.property).obj
    (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS i₃)).obj
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS i₃) 1).toSheafOfModules)
    (cm : (Scheme.Modules.pullback (B.inclusion.map f.left)).obj
          (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₂).toLRSHom.toShHom) ⟶
        Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₁).toLRSHom.toShHom)
    (ψ : (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 R₂)))).obj
          (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom) ⟶
        Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₂).toLRSHom.toShHom)
    (hsq₁ : representedSpaceMap B S hS i₁ ≫ representedSpaceMap B S hS g₁ =
      representedSpaceMap B S hS f ≫ representedSpaceMap B S hS i₂)
    (hsq₂ : representedSpaceMap B S hS i₂ ≫ representedSpaceMap B S hS g₂ =
      𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS) ≫
        representedSpaceMap B S hS i₃)
    (hsq : representedSpaceMap B S hS i₁ ≫ representedSpaceMap B S hS g₁ ≫
        representedSpaceMap B S hS g₂ =
      (representedSpaceMap B S hS f ≫
        𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS)) ≫
          representedSpaceMap B S hS i₃)
    (h₁ : (modulePullback B S hS (representedSpaceMap B S hS f)).map e₂.hom ≫
          kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS i₁)
            (representedSpaceMap B S hS i₂)
  (representedSpaceMap B S hS f) (representedSpaceMap B S hS g₁) hsq₁ 1 =
        (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₂).toLRSHom.toShHom)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R₁).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₁) R₁.left.property).map
    (cm)) ≫
            e₁.hom)
    (h₂ : (modulePullback B S hS
          (𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))).map
          e₃.hom ≫
          kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS i₂)
            (representedSpaceMap B S hS i₃)
  (𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))
    (representedSpaceMap B S hS g₂) hsq₂ 1 =
        (representedAssociatedModulePullbackIso B S hS (𝟙 R₂)
  (relativelyRepresentable_yoneda_map B S hS (𝟙 R₂))
  (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R₂).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₂) R₂.left.property).map
    (ψ)) ≫
            e₂.hom) :
    (modulePullback B S hS (representedSpaceMap B S hS f ≫
        𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))).map
        e₃.hom ≫
        kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS i₁)
          (representedSpaceMap B S hS i₃)
  (representedSpaceMap B S hS f ≫
    𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))
    (representedSpaceMap B S hS g₁ ≫ representedSpaceMap B S hS g₂) hsq 1 =
      (representedAssociatedModulePullbackIso B S hS f
  (relativelyRepresentable_yoneda_map B S hS f)
  (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R₁).functor.map
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₁) R₁.left.property).map
    ((Scheme.Modules.pullbackComp (B.inclusion.map f.left)
      (B.inclusion.map (Over.Hom.left (𝟙 R₂)))).inv.app
        (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom) ≫
      (Scheme.Modules.pullback (B.inclusion.map f.left)).map ψ ≫ cm)) ≫
          e₁.hom :=
  Stacks.CategoryTheory.square_transport_comp
    (F := modulePullback B S hS (representedSpaceMap B S hS f))
    (hc := Iso.inv_hom_id_app (modulePullbackCompIso B S hS (representedSpaceMap B S hS f)
      (𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))) _)
    (hgpc := Stacks.CategoryTheory.map_map_comp_eq_id_of
      (representedSmallEtaleModuleEquivalence B S hS R₁).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₁) R₁.left.property)
      ((Scheme.Modules.pullbackComp (B.inclusion.map f.left)
      (B.inclusion.map (Over.Hom.left (𝟙 R₂)))).hom.app (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom))
      ((Scheme.Modules.pullbackComp (B.inclusion.map f.left)
      (B.inclusion.map (Over.Hom.left (𝟙 R₂)))).inv.app (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom))
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp (B.inclusion.map f.left)
      (B.inclusion.map (Over.Hom.left (𝟙 R₂)))) (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom)))
    (hk := kernelIdealZPowSquareMap_comp B S hS (representedSpaceMap B S hS i₁)
      (representedSpaceMap B S hS i₂) (representedSpaceMap B S hS i₃)
      (representedSpaceMap B S hS f) (representedSpaceMap B S hS g₁)
      (𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ : AlgebraicSpaces B S hS))
      (representedSpaceMap B S hS g₂) hsq₁ hsq₂ hsq 1)
    (hnat := (modulePullbackCompIso B S hS (representedSpaceMap B S hS f)
      (𝟙 (⟨yoneda.obj R₂, isAlgebraicSpace_yoneda B S hS R₂⟩ :
        AlgebraicSpaces B S hS))).inv.naturality e₃.hom)
    (h₂ := h₂) (h₁ := h₁)
    (hTnat := representedAssociatedModulePullbackIso_naturality B S hS f
      (relativelyRepresentable_yoneda_map B S hS f) ψ)
    (hTcomp := representedAssociatedModulePullbackIso_comp_id_right B S hS f
      (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom))
    (ha := Stacks.CategoryTheory.map_map_eq_comp₃_of
      (representedSmallEtaleModuleEquivalence B S hS R₁).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj R₁) R₁.left.property)
      ((Scheme.Modules.pullbackComp (B.inclusion.map f.left)
      (B.inclusion.map (Over.Hom.left (𝟙 R₂)))).inv.app (Stacks.ClosedImmersion.conormalSheaf
    ((BigFppfOver.toScheme B S hS).map i₃).toLRSHom.toShHom))
      ((Scheme.Modules.pullback (B.inclusion.map f.left)).map ψ) cm rfl)

end AmbientStack

end AlgebraicGeometry.Space

end
