module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.FactorizationCriterion
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.Comp

/-!
# Existence of a factorization through a closed subspace

Let `X` be a locally ringed space, let `j : J ⟶ 𝒪_X` be a monomorphism of sheaves of modules
exhibiting `J` as a sheaf of ideals, and let `D` realize the associated closed subspace. A
morphism `f : Y ⟶ X` whose canonical map `f^* J ⟶ 𝒪_Y` vanishes factors through `D`.

## Main results

* `Stacks.ClosedImmersion.exists_factorization_of_pullbackIdealMap_eq_zero`: a morphism whose
  canonical map `f^* J ⟶ 𝒪_Y` vanishes factors through `D`.
* `Stacks.ClosedImmersion.factorsThrough_closedSubspace_iff`: a morphism factors through `D`
  if and only if its canonical map `f^* J ⟶ 𝒪_Y` vanishes.
* `Stacks.ClosedImmersion.stalkMap_surjective_of_isClosedImmersion`: the stalk maps of a closed
  immersion are surjective.

## References

* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- The stalk maps of a closed immersion of locally ringed spaces are surjective. -/
theorem stalkMap_surjective_of_isClosedImmersion {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i.toShHom] (z : Z) :
    Function.Surjective (ConcreteCategory.hom (i.toHom.stalkMap z)) := by
  have hs : Function.Surjective ((TopCat.Presheaf.stalkFunctor CommRingCat
      (i.toHom.base z)).map i.toHom.c) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks i.toHom.c).mp
      (isLocallySurjective_c i.toShHom) _
  have hp : IsIso (Z.presheaf.stalkPushforward CommRingCat i.toHom.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := CommRingCat) (f := i.toHom.base)
      (IsClosedImmersion.isClosedEmbedding (i := i.toShHom)).isInducing Z.presheaf z
  intro a
  obtain ⟨b, hb⟩ := hs (ConcreteCategory.hom
    (inv (Z.presheaf.stalkPushforward CommRingCat i.toHom.base z)) a)
  refine ⟨b, ?_⟩
  show ConcreteCategory.hom (Z.presheaf.stalkPushforward CommRingCat i.toHom.base z)
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat
      (i.toHom.base z)).map i.toHom.c) b) = a
  rw [hb]
  exact ConcreteCategory.congr_hom
    (IsIso.inv_hom_id (Z.presheaf.stalkPushforward CommRingCat i.toHom.base z)) a

section Existence

variable {X Y : LocallyRingedSpace.{u}}
  {J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  {j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)}

/-- `i_* 𝒪_D`, the pushforward of the structure sheaf of the closed subspace, as a presheaf of
commutative rings on `X`. -/
private abbrev pushforwardSubspacePresheaf [Mono j] (D : ClosedSubspaceData X J j) :
    TopCat.Presheaf CommRingCat X.toTopCat :=
  (TopCat.Presheaf.pushforward CommRingCat D.inclusion.base).obj D.space.presheaf

/-- `f_* 𝒪_Y` as a presheaf of commutative rings on `X`. -/
private abbrev pushforwardSourcePresheaf (f : Y ⟶ X) :
    TopCat.Presheaf CommRingCat X.toTopCat :=
  (TopCat.Presheaf.pushforward CommRingCat f.base).obj Y.presheaf

/-- The map on sections underlying `quotientStructureSheafMap`. -/
private noncomputable def quotientSectionMap [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) (U : (Opens X)ᵒᵖ) :
    (pushforwardSubspacePresheaf D).obj U → (pushforwardSourcePresheaf f).obj U :=
  fun z => ConcreteCategory.hom ((quotientStructureSheafMap D hf).val.app U) z

/-- The map on sections of `quotientStructureSheafMap` commutes with restriction. -/
private theorem quotientSectionMap_naturality [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (z : (pushforwardSubspacePresheaf D).obj U) :
    quotientSectionMap D hf V (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map i) z) =
      ConcreteCategory.hom ((pushforwardSourcePresheaf f).map i)
        (quotientSectionMap D hf U z) :=
  NatTrans.naturality_apply
    ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).map
      (quotientStructureSheafMap D hf).val) i z

/-- The map on sections of `quotientStructureSheafMap` carries the structure-sheaf map of the
inclusion to the structure-sheaf map of `f`. -/
private theorem quotientSectionMap_c_app [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) (U : Opens X)
    (z : X.presheaf.obj (op U)) :
    quotientSectionMap D hf (op U) (D.inclusion.c.app (op U) z) = f.c.app (op U) z :=
  congrArg (fun k => ConcreteCategory.hom (SheafOfModules.Hom.val k |>.app (op U)) z)
    (unitToPushforwardObjUnit_comp_quotientStructureSheafMap D hf)

/-- `f_* 𝒪_Y` as a sheaf of commutative rings on `X`. -/
private abbrev pushforwardSourceSheaf (f : Y ⟶ X) : TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.toSheafedSpace.sheaf

/-- The map on sections of `quotientStructureSheafMap` is unital. -/
private theorem quotientSectionMap_map_one [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) (U : Opens X) :
    quotientSectionMap D hf (op U) 1 = 1 := by
  simpa only [map_one] using quotientSectionMap_c_app D hf U 1

/-- The map on sections of `quotientStructureSheafMap` is multiplicative. -/
private theorem quotientSectionMap_map_mul [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) (U : Opens X)
    (a b : (pushforwardSubspacePresheaf D).obj (op U)) :
    quotientSectionMap D hf (op U) (a * b) =
      quotientSectionMap D hf (op U) a * quotientSectionMap D hf (op U) b := by
  refine TopCat.Presheaf.section_ext (pushforwardSourceSheaf f) U _ _ fun x hx => ?_
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff D.inclusion.c).mp
    (isLocallySurjective_c D.inclusion.toShHom)
  obtain ⟨V, hVU, ⟨a₀, ha₀⟩, hxV⟩ := hloc U a x hx
  obtain ⟨W, hWU, ⟨b₀, hb₀⟩, hxW⟩ := hloc U b x hx
  have hVT : V ⊓ W ≤ V := inf_le_left
  have hWT : V ⊓ W ≤ W := inf_le_right
  have hTU : V ⊓ W ≤ U := le_trans hVT hVU
  have key : ∀ {V' : Opens X} (hV' : V' ≤ U) (c : X.presheaf.obj (op V'))
      (d : (pushforwardSubspacePresheaf D).obj (op U)),
      ConcreteCategory.hom (D.inclusion.c.app (op V')) c =
          ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hV').op) d →
        quotientSectionMap D hf (op V')
            (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hV').op) d) =
          ConcreteCategory.hom (f.c.app (op V')) c := by
    intro V' hV' c d hc
    rw [← hc]
    exact quotientSectionMap_c_app D hf V' c
  have restr : ∀ {V' : Opens X} (hV' : V' ≤ U) (c₀ : X.presheaf.obj (op V'))
      (c : (pushforwardSubspacePresheaf D).obj (op U)) {T : Opens X} (hT : T ≤ V'),
      ConcreteCategory.hom (D.inclusion.c.app (op V')) c₀ =
          ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hV').op) c →
        ConcreteCategory.hom (D.inclusion.c.app (op T))
            (ConcreteCategory.hom (X.presheaf.map (homOfLE hT).op) c₀) =
          ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE (hT.trans hV')).op)
            c := by
    intro V' hV' c₀ c T hT h
    rw [NatTrans.naturality_apply D.inclusion.c (homOfLE hT).op c₀, h]
    exact TopCat.Presheaf.restrict_restrict hT hV' c
  have haT := restr hVU a₀ a hVT ha₀
  have hbT := restr hWU b₀ b hWT hb₀
  have hmulT : quotientSectionMap D hf (op (V ⊓ W))
        (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hTU).op) (a * b)) =
      quotientSectionMap D hf (op (V ⊓ W))
          (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hTU).op) a) *
        quotientSectionMap D hf (op (V ⊓ W))
          (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hTU).op) b) := by
    rw [key hTU (X.presheaf.map (homOfLE hVT).op a₀ * X.presheaf.map (homOfLE hWT).op b₀)
      (a * b) (by rw [map_mul, haT, hbT, map_mul]),
      key hTU _ a haT, key hTU _ b hbT,
      map_mul (ConcreteCategory.hom (f.c.app (op (V ⊓ W))))]
  refine TopCat.Presheaf.germ_ext (pushforwardSourcePresheaf f) (V ⊓ W) ⟨hxV, hxW⟩ (homOfLE hTU)
    (homOfLE hTU) ?_
  calc ConcreteCategory.hom ((pushforwardSourcePresheaf f).map (homOfLE hTU).op)
        (quotientSectionMap D hf (op U) (a * b))
      = quotientSectionMap D hf (op (V ⊓ W))
          (ConcreteCategory.hom ((pushforwardSubspacePresheaf D).map (homOfLE hTU).op) (a * b)) :=
        (quotientSectionMap_naturality D hf (homOfLE hTU).op (a * b)).symm
    _ = _ := by
        rw [hmulT, quotientSectionMap_naturality D hf (homOfLE hTU).op a,
          quotientSectionMap_naturality D hf (homOfLE hTU).op b,
          map_mul (ConcreteCategory.hom ((pushforwardSourcePresheaf f).map (homOfLE hTU).op))]

/-- `i_* 𝒪_D` as a sheaf of commutative rings on `X`. -/
private abbrev pushforwardSubspaceSheaf [Mono j] (D : ClosedSubspaceData X J j) :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat D.inclusion.base).obj D.space.toSheafedSpace.sheaf

/-- `quotientStructureSheafMap` as a morphism of sheaves of commutative rings
`i_* 𝒪_D ⟶ f_* 𝒪_Y`. -/
private noncomputable def quotientRingMap [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) :
    pushforwardSubspaceSheaf D ⟶ pushforwardSourceSheaf f :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := quotientSectionMap D hf U
          map_one' := by
            obtain ⟨U⟩ := U
            exact quotientSectionMap_map_one D hf U
          map_mul' := by
            obtain ⟨U⟩ := U
            exact quotientSectionMap_map_mul D hf U
          map_zero' := map_zero
            (ConcreteCategory.hom ((quotientStructureSheafMap D hf).val.app U))
          map_add' := map_add
            (ConcreteCategory.hom ((quotientStructureSheafMap D hf).val.app U)) }
      naturality := fun _ _ i =>
        ConcreteCategory.hom_ext _ _ (quotientSectionMap_naturality D hf i) }

/-- The structure-sheaf component of `f` factors as the one of the inclusion followed by
`quotientRingMap`, as morphisms of sheaves of rings on `X`. -/
private theorem comp_quotientRingMap [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) (U : Opens X)
    (z : X.presheaf.obj (op U)) :
    ConcreteCategory.hom ((quotientRingMap D hf).hom.app (op U))
        (ConcreteCategory.hom (D.inclusion.c.app (op U)) z) =
      ConcreteCategory.hom (f.c.app (op U)) z :=
  quotientSectionMap_c_app D hf U z

/-- Pushing `𝒪_Y` forward along `f` is pushing it forward along a continuous factorization of
`f` and then along the inclusion. -/
private theorem pushforwardSourceSheaf_eq [Mono j] (D : ClosedSubspaceData X J j) (f : Y ⟶ X)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) :
    pushforwardSourceSheaf f =
      (TopCat.Sheaf.pushforward CommRingCat D.inclusion.base).obj
        ((TopCat.Sheaf.pushforward CommRingCat b).obj Y.toSheafedSpace.sheaf) :=
  congrArg (fun k => (TopCat.Sheaf.pushforward CommRingCat k).obj Y.toSheafedSpace.sheaf) hb.symm

/-- `i_*` on sheaves of commutative rings is fully faithful for the inclusion of a closed
subspace. -/
private noncomputable def subspacePushforwardFullyFaithful [Mono j]
    (D : ClosedSubspaceData X J j) :
    (TopCat.Sheaf.pushforward CommRingCat D.inclusion.base).FullyFaithful :=
  ClosedImmersionSheaves.sheafPushforwardFullyFaithful (C := CommRingCat)
    (IsClosedImmersion.isClosedEmbedding (i := D.inclusion.toShHom)).isInducing

/-- The map `𝒪_D ⟶ b_* 𝒪_Y` obtained by descending `quotientRingMap` along the fully faithful
functor `i_*`. -/
private noncomputable def descendedRingMap [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) :
    D.space.toSheafedSpace.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat b).obj Y.toSheafedSpace.sheaf :=
  (subspacePushforwardFullyFaithful D).preimage
      (quotientRingMap D hf ≫ eqToHom (pushforwardSourceSheaf_eq D f hb))

/-- `i_*` of `descendedRingMap` is `quotientRingMap` followed by the transport along
`pushforwardSourceSheaf_eq`. -/
private theorem descendedRingMap_spec [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) :
    (TopCat.Sheaf.pushforward CommRingCat D.inclusion.base).map (descendedRingMap D hf hb) =
      quotientRingMap D hf ≫ eqToHom (pushforwardSourceSheaf_eq D f hb) :=
  (subspacePushforwardFullyFaithful D).map_preimage _

/-- The factorization of `f` as a morphism of presheafed spaces: the continuous factorization of
its underlying map together with the descended structure-sheaf map. -/
private noncomputable def factorPresheafedSpaceHom [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) :
    Y.toPresheafedSpace ⟶ D.space.toPresheafedSpace where
  base := b
  c := (TopCat.Sheaf.forget CommRingCat D.space.toTopCat).map (descendedRingMap D hf hb)

/-- Transporting an element along an equality of objects and back is the identity. -/
private theorem eqToHom_symm_eqToHom_apply {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory C FC]
    {A B : C} (h : A = B) (x : ToType A) :
    ConcreteCategory.hom (eqToHom h.symm) (ConcreteCategory.hom (eqToHom h) x) = x := by
  subst h
  simp

/-- The descended morphism of presheafed spaces is a factorization of `f`. -/
private theorem factorPresheafedSpaceHom_comp [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) :
    factorPresheafedSpaceHom D hf hb ≫ D.inclusion.toHom = f.toHom := by
  refine PresheafedSpace.Hom.ext _ _ hb ?_
  ext U z
  have hOpMap : (Opens.map (b ≫ D.inclusion.base)).op = (Opens.map f.base).op :=
    congrArg (fun k => (Opens.map k).op) hb
  have hOpen : (Opens.map (b ≫ D.inclusion.base)).obj U = (Opens.map f.base).obj U :=
    congrArg (fun k => (Opens.map k).obj U) hb
  have hsectionEq : Y.presheaf.obj (op ((Opens.map f.base).obj U)) =
      Y.presheaf.obj (op ((Opens.map (b ≫ D.inclusion.base)).obj U)) :=
    congrArg (fun S => S.presheaf.obj (op U)) (pushforwardSourceSheaf_eq D f hb)
  have hindex : (eqToHom hOpMap).app (op U) = (eqToHom hOpen.symm).op := Subsingleton.elim _ _
  have hBapp : (eqToHom (pushforwardSourceSheaf_eq D f hb)).hom.app (op U) =
      eqToHom hsectionEq := by
    show ((TopCat.Sheaf.forget CommRingCat X.toTopCat).map
      (eqToHom (pushforwardSourceSheaf_eq D f hb))).app (op U) = _
    rw [eqToHom_map, CategoryTheory.eqToHom_app]
    rfl
  have hrestriction : Y.presheaf.map ((eqToHom hOpen.symm).op) = eqToHom hsectionEq.symm := by
    rw [eqToHom_op, eqToHom_map]
  show ConcreteCategory.hom (Y.presheaf.map ((eqToHom hOpMap).app (op U)))
      (ConcreteCategory.hom ((descendedRingMap D hf hb).hom.app
          (op ((Opens.map D.inclusion.base).obj U)))
        (ConcreteCategory.hom (D.inclusion.c.app (op U)) z)) =
    ConcreteCategory.hom (f.c.app (op U)) z
  rw [show (descendedRingMap D hf hb).hom.app (op ((Opens.map D.inclusion.base).obj U)) =
      (quotientRingMap D hf ≫ eqToHom (pushforwardSourceSheaf_eq D f hb)).hom.app (op U) from by
    show ((TopCat.Presheaf.pushforward CommRingCat D.inclusion.base).map
      (descendedRingMap D hf hb).hom).app (op U) = _
    rw [TopCat.Presheaf.pushforward_map_app']
    exact congrArg (fun k => k.hom.app (op U)) (descendedRingMap_spec D hf hb)]
  show ConcreteCategory.hom (Y.presheaf.map ((eqToHom hOpMap).app (op U)))
      (ConcreteCategory.hom ((eqToHom (pushforwardSourceSheaf_eq D f hb)).hom.app (op U))
        (ConcreteCategory.hom ((quotientRingMap D hf).hom.app (op U))
          (ConcreteCategory.hom (D.inclusion.c.app (op U)) z))) =
    ConcreteCategory.hom (f.c.app (op U)) z
  rw [comp_quotientRingMap D hf U z, hindex, hBapp, hrestriction]
  exact eqToHom_symm_eqToHom_apply hsectionEq _

/-- The stalk maps of the descended morphism of presheafed spaces are local ring
homomorphisms. -/
private theorem factorPresheafedSpaceHom_isLocalHom [Mono j] (D : ClosedSubspaceData X J j)
    {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0)
    {b : Y.toTopCat ⟶ D.space.toTopCat} (hb : b ≫ D.inclusion.base = f.base) (y : Y) :
    IsLocalHom (CommRingCat.Hom.hom
      (PresheafedSpace.Hom.stalkMap (factorPresheafedSpaceHom D hf hb) y)) := by
  have hpoint : ConcreteCategory.hom D.inclusion.base
      (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y) =
      ConcreteCategory.hom f.base y :=
    congrArg (fun k : Y.toPresheafedSpace ⟶ X.toPresheafedSpace =>
      ConcreteCategory.hom k.base y) (factorPresheafedSpaceHom_comp D hf hb)
  let e : X.presheaf.stalk (ConcreteCategory.hom D.inclusion.base
        (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y)) ⟶
      X.presheaf.stalk (ConcreteCategory.hom f.base y) := eqToHom (by rw [hpoint])
  have hcomp : (D.inclusion.toHom.stalkMap
        (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y)) ≫
      PresheafedSpace.Hom.stalkMap (factorPresheafedSpaceHom D hf hb) y =
      e ≫ f.toHom.stalkMap y :=
    (PresheafedSpace.stalkMap.comp (factorPresheafedSpaceHom D hf hb)
        D.inclusion.toHom y).symm.trans
      (PresheafedSpace.stalkMap.congr_hom _ _ (factorPresheafedSpaceHom_comp D hf hb) y)
  have hcompLocal : IsLocalHom (CommRingCat.Hom.hom (e ≫ f.toHom.stalkMap y)) := by
    have h₁ : IsLocalHom (CommRingCat.Hom.hom e) := isLocalHom_of_isIso e
    have h₂ : IsLocalHom (CommRingCat.Hom.hom (f.toHom.stalkMap y)) := f.prop y
    infer_instance
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := stalkMap_surjective_of_isClosedImmersion D.inclusion
    (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y) a
  have hcUnit : IsUnit c := by
    refine hcompLocal.map_nonunit c ?_
    have hval := congrArg
      (fun k : X.presheaf.stalk (ConcreteCategory.hom D.inclusion.base
          (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y)) ⟶
        Y.presheaf.stalk y => ConcreteCategory.hom k c) hcomp
    rw [ConcreteCategory.comp_apply, hc] at hval
    rwa [← hval]
  rw [← hc]
  exact (D.inclusion.toHom.stalkMap
    (ConcreteCategory.hom (factorPresheafedSpaceHom D hf hb).base y)).hom.isUnit_map hcUnit

/-- A morphism of locally ringed spaces whose canonical map `f^* J ⟶ 𝒪_Y` vanishes factors
through the closed subspace cut out by `j`. -/
theorem exists_factorization_of_pullbackIdealMap_eq_zero [Mono j]
    (D : ClosedSubspaceData X J j) (f : Y ⟶ X) (hf : pullbackIdealMap f J j = 0) :
    ∃ g : Y ⟶ D.space, g ≫ D.inclusion = f := by
  obtain ⟨b, hb⟩ := exists_base_factorization_of_pullbackIdealMap_eq_zero D f hf
  exact ⟨LocallyRingedSpace.homMk
    (InducedCategory.homMk (factorPresheafedSpaceHom D hf hb))
    (factorPresheafedSpaceHom_isLocalHom D hf hb),
    LocallyRingedSpace.Hom.ext' (factorPresheafedSpaceHom_comp D hf hb)⟩

/-- A morphism of locally ringed spaces factors through the closed subspace cut out by `j`
exactly when the canonical map `f^* J ⟶ 𝒪_Y` vanishes. -/
@[stacks 01HP "factorization criterion"]
theorem factorsThrough_closedSubspace_iff [Mono j] (D : ClosedSubspaceData X J j) (f : Y ⟶ X) :
    (∃ g : Y ⟶ D.space, g ≫ D.inclusion = f) ↔ pullbackIdealMap f J j = 0 :=
  ⟨fun ⟨g, hg⟩ => pullbackIdealMap_eq_zero_of_factorsThrough D f g hg,
    exists_factorization_of_pullbackIdealMap_eq_zero D f⟩

end Existence

end Stacks.ClosedImmersion

end
