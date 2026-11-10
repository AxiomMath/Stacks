module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DivisorClass
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingMeromorphic

/-!
# Transport of meromorphic sections along a morphism of modules

Let `X` be an integral scheme and `f : L ⟶ N` a morphism of sheaves of `𝒪_X`-modules.
Extension of scalars to the sheaf of meromorphic functions carries `f` to a morphism of the
sheaves of meromorphic sections, hence a meromorphic section of `L` to one of `N`. When `f` is
an isomorphism this transport preserves regularity, and — on a locally Noetherian integral
scheme, for `L` and `N` invertible — it preserves the order of vanishing along every prime
divisor. Consequently the Weil divisor of a regular meromorphic section, and the Weil divisor
class of an invertible module, depend only on the isomorphism class of the module.

## Main definitions

* `AlgebraicGeometry.mapMeromorphicSection`: transport of a meromorphic section along a
  morphism of modules.
* `AlgebraicGeometry.stalkLinearMap`, `AlgebraicGeometry.stalkLinearEquiv`: the induced map on
  stalks, as a linear map over the local ring, and as a linear equivalence when the morphism is
  an isomorphism.
* `AlgebraicGeometry.constantGenericStalkModuleMap`: the induced morphism of constant
  generic-stalk module sheaves.

## Main results

* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_naturality`: the comparison
  isomorphism of Tag 01X5 part (2) is natural in the module.
* `AlgebraicGeometry.orderOfVanishingMeromorphic_mapMeromorphicSection`: the order of vanishing
  of Tag 02SF is unchanged by transport along an isomorphism.
* `AlgebraicGeometry.weilDivisorOfMeromorphicSection_mapMeromorphicSection` and
  `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_congr`: the Weil divisor of Tag 0BE6
  part (1) and the Weil divisor class of Tag 0BE6 part (2) are invariant.

## Implementation notes

The comparison isomorphism `AlgebraicGeometry.meromorphicSectionSheafIsoConstant` of Tag 01X5
part (2) is a *choice*, so it is not natural by construction. Its naturality is proved from the
characterization it is packaged with, which describes it only on sections of the form
`η_L(m)` for `η` the unit of extension of scalars: two morphisms out of a value of the left
adjoint agree as soon as their images under the unit do
(`CategoryTheory.Adjunction.hom_ext_of_unit`), and on those sections both sides are read off the
characterization. Over an open set missing the generic point the sections vanish, by
`TopologicalSpace.Opens.eq_bot_of_genericPoint_notMem` and
`CategoryTheory.SheafOfModules.subsingleton_obj_bot`.

The invariance of the order of vanishing is the coordinate description of Tag 02SF: the stalk
map of an isomorphism at the generic point of a prime divisor carries a generator of `L_ξ` to a
generator of `N_ξ` and commutes with specialization from the generic point of `X`, so the
coordinate of the transported section is the coordinate of the original one, and the two orders
are the order of the same element of the function field.

The adjunction unit and the chosen comparison isomorphism are spelled out at every use rather
than abbreviated by a local hypothesis: introducing them with `set` makes the definitional
comparisons against the characterization of the chosen isomorphism run away, where the same
proofs with the terms written out elaborate at once.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

/-- Two morphisms out of a value of a left adjoint agree as soon as their images under the
unit of the adjunction agree. -/
theorem CategoryTheory.Adjunction.hom_ext_of_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (u v : F.obj A ⟶ B)
    (h : adj.unit.app A ≫ G.map u = adj.unit.app A ≫ G.map v) : u = v := by
  refine (adj.homEquiv A B).injective ?_
  rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Transport of a meromorphic section along a morphism of modules: the image under the
morphism of sheaves of meromorphic sections (Tag 01X4 part (1)) obtained by extension of
scalars to the sheaf of meromorphic functions. -/
def mapMeromorphicSection [IsIntegral X] (L N : X.Modules) (e : L ⟶ N)
    (s : MeromorphicSection X.sheaf L) : MeromorphicSection X.sheaf N :=
  SheafOfModules.sectionsMap
    ((Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
      (toTotalQuotientSheaf X.sheaf)).map e) s

/-- Transport of a meromorphic section along an isomorphism preserves regularity in the sense
of Tag 02OX: multiplication by the transported section is multiplication by the original one
followed by an isomorphism. -/
theorem isRegularMeromorphicSection_mapMeromorphicSection [IsIntegral X] (L N : X.Modules)
    (e : L ≅ N) (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsRegularMeromorphicSection X.sheaf N (mapMeromorphicSection L N e.hom s) := by
  have hE : IsIso ((Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
      (toTotalQuotientSheaf X.sheaf)).map e.hom) :=
    ((Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
      (toTotalQuotientSheaf X.sheaf)).mapIso e).isIso_hom
  change Mono ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s) at hs
  change Mono ((meromorphicSectionSheaf X.sheaf N).unitHomEquiv.symm
    (SheafOfModules.sectionsMap ((Stacks.Sheaves.ChangeOfRings.changeOfRings
      (Opens.grothendieckTopology X) (toTotalQuotientSheaf X.sheaf)).map e.hom) s))
  have hcomp : Mono ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s ≫
      (Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
        (toTotalQuotientSheaf X.sheaf)).map e.hom) := inferInstance
  rwa [SheafOfModules.unitHomEquiv_symm_comp] at hcomp

/-- The map on stalks induced by a morphism of sheaves of modules, as a linear map over the
local ring. It is the stalk functor applied to the underlying morphism of presheaves of abelian
groups; linearity is the compatibility of the morphism with the action on sections. -/
def stalkLinearMap (L N : X.Modules) (f : L ⟶ N) (x : X) :
    L.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x := by
  refine { toFun := fun m => ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f)).hom m, map_add' := map_add _, map_smul' := ?_ }
  intro a m
  set g : L.presheaf.stalk x →+ N.presheaf.stalk x :=
    ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)).hom
  obtain ⟨U, hxU, r, hr⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, m0, hm⟩ := L.presheaf.exists_germ_eq m
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : ↑(X.ringCatSheaf.obj.obj (op W)) := X.presheaf.map iWU.op r
  let mW : ↑(L.val.obj (op W)) := L.presheaf.map iWV.op m0
  have hra : ConcreteCategory.hom (X.presheaf.germ W x hxW) rW = a :=
    (X.presheaf.germ_res_apply iWU x hxW r).trans hr
  have hrm : ConcreteCategory.hom (L.presheaf.germ W x hxW) mW = m :=
    (L.presheaf.germ_res_apply iWV x hxW m0).trans hm
  have hsmulL : ConcreteCategory.hom (L.presheaf.germ W x hxW) (rW • mW) =
      ConcreteCategory.hom (X.presheaf.germ W x hxW) rW •
        ConcreteCategory.hom (L.presheaf.germ W x hxW) mW :=
    PresheafOfModules.germ_smul (M := L.val) x W hxW rW mW
  have hsmulN : ConcreteCategory.hom (N.presheaf.germ W x hxW)
      (rW • ConcreteCategory.hom (f.val.app (op W)) mW) =
      ConcreteCategory.hom (X.presheaf.germ W x hxW) rW •
        ConcreteCategory.hom (N.presheaf.germ W x hxW)
          (ConcreteCategory.hom (f.val.app (op W)) mW) :=
    PresheafOfModules.germ_smul (M := N.val) x W hxW rW
      (ConcreteCategory.hom (f.val.app (op W)) mW)
  have hmap : ∀ z : L.presheaf.obj (op W),
      g (L.presheaf.germ W x hxW z) =
        N.presheaf.germ W x hxW (ConcreteCategory.hom (f.val.app (op W)) z) := by
    intro z
    change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f))
      (ConcreteCategory.hom (L.presheaf.germ W x hxW) z) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  change g (a • m) = a • g m
  calc
    g (a • m) = g (ConcreteCategory.hom (L.presheaf.germ W x hxW) (rW • mW)) := by
      rw [hsmulL, hra, hrm]
    _ = N.presheaf.germ W x hxW
        (ConcreteCategory.hom (f.val.app (op W)) (rW • mW)) := hmap _
    _ = N.presheaf.germ W x hxW
        (rW • ConcreteCategory.hom (f.val.app (op W)) mW) := by
      congr 1
      exact f.app_smul rW mW
    _ = a • g m := by rw [hsmulN, hra, ← hmap, hrm]

/-- The stalk map of an isomorphism of sheaves of modules is bijective. -/
theorem bijective_stalkLinearMap (L N : X.Modules) (f : L ⟶ N) [IsIso f] (x : X) :
    Function.Bijective (stalkLinearMap L N f x) := by
  change Function.Bijective (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)))
  have : IsIso (Scheme.Modules.Hom.mapPresheaf f) := by
    change IsIso ((Scheme.Modules.toPresheaf X).map f)
    exact Functor.map_isIso (Scheme.Modules.toPresheaf X) f
  exact ConcreteCategory.bijective_of_isIso _

/-- The stalk map of an isomorphism of sheaves of modules, as a linear equivalence over the
local ring. -/
def stalkLinearEquiv (L N : X.Modules) (f : L ⟶ N) [IsIso f] (x : X) :
    L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  LinearEquiv.ofBijective (stalkLinearMap L N f x) (bijective_stalkLinearMap L N f x)

/-- The stalk maps of a morphism of modules commute with specialization. -/
theorem stalkLinearMap_stalkSpecializes (L N : X.Modules) (f : L ⟶ N) {x y : X} (h : x ⤳ y)
    (m : L.presheaf.stalk y) :
    stalkLinearMap L N f x (L.presheaf.stalkSpecializes h m) =
      N.presheaf.stalkSpecializes h (stalkLinearMap L N f y m) := by
  change ConcreteCategory.hom ((L.presheaf.stalkSpecializes h) ≫
      (TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)) m =
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab y).map
      (Scheme.Modules.Hom.mapPresheaf f) ≫ N.presheaf.stalkSpecializes h) m
  rw [TopCat.Presheaf.stalkSpecializes_stalkFunctor_map]
  rfl

/-- The stalk map of a morphism of modules on a germ is the germ of the image. -/
theorem stalkLinearMap_germ (L N : X.Modules) (f : L ⟶ N) (U : X.Opens) (x : X) (hx : x ∈ U)
    (m : L.presheaf.obj (op U)) :
    stalkLinearMap L N f x (L.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (f.val.app (op U) m) := by
  change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f))
    (ConcreteCategory.hom (L.presheaf.germ U x hx) m) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The morphism of constant generic-stalk module sheaves (the target of the comparison
isomorphism of Tag 01X5 part (2)) induced by a morphism of sheaves of modules: the
sheafification of the constant presheaf morphism given by the stalk map at the generic
point. -/
def constantGenericStalkModuleMap [IsIntegral X] (L N : X.Modules) (f : L ⟶ N) :
    constantGenericStalkModuleSheaf X L ⟶ constantGenericStalkModuleSheaf X N := by
  let O : TopCat.Presheaf CommRingCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  letI : Module X.functionField (L.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L.val (genericPoint X)
  letI : Module X.functionField (N.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) N.val (genericPoint X)
  let cMap : Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
        (ModuleCat.of X.functionField (L.presheaf.stalk (genericPoint X))) ⟶
      Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
        (ModuleCat.of X.functionField (N.presheaf.stalk (genericPoint X))) :=
    { app := fun _ => ModuleCat.ofHom (stalkLinearMap L N f (genericPoint X))
      naturality := by intro U V i; ext m; rfl }
  exact (PresheafOfModules.sheafification (𝟙 (Stacks.Sheaves.Differentials.ringSheaf
    (C := Opens X) (J := Opens.grothendieckTopology X) S).obj)).map
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).map cMap)

/-- The constant sections of `AlgebraicGeometry.constantGenericStalkModuleMap`: the induced
morphism carries the constant section determined by `m` to the constant section determined by
the image of `m` under the stalk map at the generic point. -/
theorem constantGenericStalkModuleMap_section [IsIntegral X] (L N : X.Modules) (f : L ⟶ N)
    (U : X.Opens) (m : L.presheaf.stalk (genericPoint X)) :
    (constantGenericStalkModuleMap L N f).val.app (op U)
        (constantGenericStalkModuleSection X L U m) =
      constantGenericStalkModuleSection X N U (stalkLinearMap L N f (genericPoint X) m) := by
  let O : TopCat.Presheaf CommRingCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  let _ : Module X.functionField (L.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L.val (genericPoint X)
  let _ : Module X.functionField (N.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) N.val (genericPoint X)
  let cMap : Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
        (ModuleCat.of X.functionField (L.presheaf.stalk (genericPoint X))) ⟶
      Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
        (ModuleCat.of X.functionField (N.presheaf.stalk (genericPoint X))) :=
    { app := fun _ => ModuleCat.ofHom (stalkLinearMap L N f (genericPoint X))
      naturality := by intro U V i; ext m; rfl }
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) S).obj)).unit_naturality
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).map cMap)
  let _ : Algebra X.functionField (S.obj.obj (op U)) := (α.app (op U)).hom.toAlgebra
  exact congrArg (fun z => (z.app (op U)).hom (1 ⊗ₜ[X.functionField] m)) hn

/-- The totalQuotient-to-constant adjunction at which the comparison isomorphism of Tag 01X5
part (2) is read. -/
abbrev meromorphicExtendRestrictAdjunction (X : Scheme.{u}) :
    Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
        (toTotalQuotientSheaf X.sheaf) ⊣
      SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf)) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) (toTotalQuotientSheaf X.sheaf).hom X.ringCatSheaf.property
    (Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).property

/-- The comparison isomorphism of Tag 01X5 part (2) is natural in the module: transporting a
meromorphic section along a morphism of modules and then comparing with the constant
generic-stalk sheaf is the same as comparing first and then applying the induced map of
constant generic-stalk sheaves. -/
theorem meromorphicSectionSheafIsoConstant_naturality [IsIntegral X] (L N : X.Modules)
    (f : L ⟶ N) [L.IsQuasicoherent] [N.IsQuasicoherent] :
    (meromorphicSectionSheafIsoConstant X L).val.hom ≫
        (SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat.{u})).map
              (totalQuotientSheafIsoConstant X).val.hom)).map
            (constantGenericStalkModuleMap L N f) =
      (Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
        (toTotalQuotientSheaf X.sheaf)).map f ≫
          (meromorphicSectionSheafIsoConstant X N).val.hom := by
  refine (meromorphicExtendRestrictAdjunction X).hom_ext_of_unit _ _ ?_
  ext U m
  have hnat : ((Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
      (toTotalQuotientSheaf X.sheaf)).map f).val.app U
        (((meromorphicExtendRestrictAdjunction X).unit.app L).val.app U m) =
      ((meromorphicExtendRestrictAdjunction X).unit.app N).val.app U (f.val.app U m) :=
    congrArg (fun z => (z.val.app U) m) ((meromorphicExtendRestrictAdjunction X).unit_naturality f)
  by_cases hU : genericPoint X ∈ U.unop
  · change (constantGenericStalkModuleMap L N f).val.app U
        (((meromorphicSectionSheafIsoConstant X L).val.hom.val.app U)
          ((((meromorphicExtendRestrictAdjunction X).unit.app L).val.app U) m)) =
      ((meromorphicSectionSheafIsoConstant X N).val.hom.val.app U)
        (((Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
          (toTotalQuotientSheaf X.sheaf)).map f).val.app U
            ((((meromorphicExtendRestrictAdjunction X).unit.app L).val.app U) m))
    refine (congrArg (fun z => (constantGenericStalkModuleMap L N f).val.app U z)
        ((meromorphicSectionSheafIsoConstant X L).property U.unop m hU)).trans
      ((constantGenericStalkModuleMap_section L N f U.unop
          (L.presheaf.germ U.unop (genericPoint X) hU m)).trans
        ((congrArg (fun z => constantGenericStalkModuleSection X N U.unop z)
            (stalkLinearMap_germ L N f U.unop (genericPoint X) hU m)).trans
          ((((meromorphicSectionSheafIsoConstant X N).property U.unop
              (f.val.app U m) hU).symm).trans
            (congrArg (fun z =>
              (meromorphicSectionSheafIsoConstant X N).val.hom.val.app U z) hnat).symm)))
  · have hbot : U = op (⊥ : X.Opens) :=
      (Opposite.op_unop U).symm.trans
        (congrArg Opposite.op (Opens.eq_bot_of_genericPoint_notMem hU))
    subst hbot
    have hsub : Subsingleton ((constantGenericStalkModuleSheaf X N).val.obj (op (⊥ : X.Opens))) :=
      CategoryTheory.SheafOfModules.subsingleton_obj_bot _ _
    exact @Subsingleton.elim _ hsub _ _

/-- Naturality of the comparison isomorphism of Tag 01X5 part (2), read on a meromorphic
section over an open set. -/
theorem meromorphicSectionSheafIsoConstant_naturality_apply [IsIntegral X] (L N : X.Modules)
    (f : L ⟶ N) [L.IsQuasicoherent] [N.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (U : X.Opens) :
    (constantGenericStalkModuleMap L N f).val.app (op U)
        ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op U) (s.val (op U))) =
      (meromorphicSectionSheafIsoConstant X N).val.hom.val.app (op U)
        ((mapMeromorphicSection L N f s).val (op U)) :=
  congrArg (fun z => (z.val.app (op U)) (s.val (op U)))
    (meromorphicSectionSheafIsoConstant_naturality L N f)

/-- **Transport invariance of the order of vanishing.** An isomorphism of invertible modules
carries a regular meromorphic section to one with the same order of vanishing along every
prime divisor: the stalk map at the generic point of the divisor carries a generator to a
generator and leaves the coordinate of the section unchanged. -/
theorem orderOfVanishingMeromorphic_mapMeromorphicSection
    [IsLocallyNoetherian X] [IsIntegral X] (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (Z : PrimeDivisor X) :
    orderOfVanishingMeromorphic X L s hs Z =
      orderOfVanishingMeromorphic X N (mapMeromorphicSection L N e.hom s)
        (isRegularMeromorphicSection_mapMeromorphicSection L N e s hs) Z := by
  let _ : L.IsQuasicoherent := (orderOfVanishingMeromorphicData X L s hs Z).val.1
  let _ : N.IsQuasicoherent := (orderOfVanishingMeromorphicData X N
    (mapMeromorphicSection L N e.hom s)
    (isRegularMeromorphicSection_mapMeromorphicSection L N e s hs) Z).val.1
  have hL := (orderOfVanishingMeromorphicData X L s hs Z).property
  have hN := (orderOfVanishingMeromorphicData X N (mapMeromorphicSection L N e.hom s)
    (isRegularMeromorphicSection_mapMeromorphicSection L N e s hs) Z).property
  obtain ⟨m, hm, a, ha⟩ := hL.1
  have hgenN : Submodule.span (X.presheaf.stalk Z.genericPoint)
      {stalkLinearMap L N e.hom Z.genericPoint m} = ⊤ := by
    have hmap : Submodule.span (X.presheaf.stalk Z.genericPoint)
          {stalkLinearMap L N e.hom Z.genericPoint m} =
        Submodule.map (stalkLinearEquiv L N e.hom Z.genericPoint).toLinearMap
          (Submodule.span (X.presheaf.stalk Z.genericPoint) {m}) := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    rw [hmap, hm]
    simp
  have hspec : stalkLinearMap L N e.hom (genericPoint X)
        (a • L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) m) =
      a • N.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
        (stalkLinearMap L N e.hom Z.genericPoint m) :=
    (map_smul (stalkLinearMap L N e.hom (genericPoint X)) a _).trans
      (congrArg (fun z => a • z) (stalkLinearMap_stalkSpecializes L N e.hom
        ((genericPoint_spec X).specializes trivial) m))
  have hcoords := (congrArg (fun z =>
      (constantGenericStalkModuleMap L N e.hom).val.app (op (⊤ : X.Opens)) z) ha).trans
    ((constantGenericStalkModuleMap_section L N e.hom ⊤
        (a • L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) m)).trans
      (congrArg (fun z => constantGenericStalkModuleSection X N ⊤ z) hspec))
  have hcoordN := (meromorphicSectionSheafIsoConstant_naturality_apply L N e.hom
    s ⊤).symm.trans hcoords
  exact (hL.2 m hm a ha).trans
    (hN.2 (stalkLinearMap L N e.hom Z.genericPoint m) hgenN a hcoordN).symm

/-- **Transport invariance of the Weil divisor of a regular meromorphic section**, the divisor
`div_L(s)` of Tag 0BE6 part (1): an isomorphism `L ≅ N` of invertible modules carries `s` to a
regular meromorphic section of `N` with the same divisor. -/
theorem weilDivisorOfMeromorphicSection_mapMeromorphicSection
    [IsLocallyNoetherian X] [IsIntegral X] (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    weilDivisorOfMeromorphicSection X L s hs =
      weilDivisorOfMeromorphicSection X N (mapMeromorphicSection L N e.hom s)
        (isRegularMeromorphicSection_mapMeromorphicSection L N e s hs) := by
  ext Z
  simpa only [weilDivisorOfMeromorphicSection_apply] using
    orderOfVanishingMeromorphic_mapMeromorphicSection L N e s hs Z

/-- **The Weil divisor class of an invertible module depends only on its isomorphism class.**
Transporting a regular meromorphic section along an isomorphism `L ≅ N` leaves the order of
vanishing along every prime divisor unchanged, hence the Weil divisor, hence its class in
`Cl(X)`. This is the well-definedness the Weil divisor class of Tag 0BE6 part (2) needs in
order to descend to the Picard group of Tag 01CX, which is Tag 0BE7. -/
theorem weilDivisorClassOfInvertibleSheaf_congr [IsLocallyNoetherian X] [IsIntegral X]
    (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) :
    weilDivisorClassOfInvertibleSheaf X L = weilDivisorClassOfInvertibleSheaf X N := by
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  rw [weilDivisorClassOfInvertibleSheaf_eq X L s hs,
    weilDivisorClassOfInvertibleSheaf_eq X N (mapMeromorphicSection L N e.hom s)
      (isRegularMeromorphicSection_mapMeromorphicSection L N e s hs),
    weilDivisorOfMeromorphicSection_mapMeromorphicSection L N e s hs]

end AlgebraicGeometry

end
