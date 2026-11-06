module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalkwiseSlicePoints
public import StacksFrontier.Homology.Perfect.LargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived stalk of a perfect object of a ringed site is perfect

Let `(C, O)` be a ringed site and let `Φ` be a point of it. If `E` is a perfect object of `D(O)`
(Stacks 08G5), then its derived stalk `E_Φ` is a perfect object of the derived category of
modules over the stalk `O_Φ` (Stacks 0657): it is isomorphic to a bounded complex of finite
projective `O_Φ`-modules. This is the site form of the statement, for a ringed space, that the
stalks of a perfect complex are perfect.

## Main definitions

* `Stacks.moduleStalkUnitLinearEquiv`: the stalk of the structure sheaf, viewed as a module over
  itself, is free of rank one over the stalk ring, on the germ of `1`.

## Main results

* `Stacks.finite_and_projective_of_isDirectSummandOfFiniteFree`: an additive functor to modules
  over a ring which preserves finite colimits and carries the unit to the free module of rank one
  carries a direct summand of a finite free module to a finite projective module.
* `Stacks.isPerfect_Q_mapHomologicalComplex_of_isStrictlyPerfect`: such a functor carries a
  strictly perfect complex to a perfect object of the derived category of the ring.
* `AlgebraicGeometry.RingedSite.isPerfect_derivedModuleFiber_of_isPerfect`: the derived stalk of
  a perfect object is perfect.

## Implementation notes

A perfect object has, on the members of a family covering the final object of the site, a
strictly perfect model of a representing complex
(`AlgebraicGeometry.RingedSite.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex`). The
point `Φ` lifts to one of those members, `V`, through some `x`, because a point carries covering
sieves to jointly surjective families. The stalk at `Φ.over x` of a module on the slice over `V`
is read over the stalk ring at `Φ` along the comparison `overRingFiberIso` of Stacks 04H2; the
resulting functor is exact and carries the unit to the free module of rank one, so it carries the
strictly perfect model to a bounded complex of finite projective modules, quasi-isomorphic to the
stalk at `Φ.over x` of the restriction of the representing complex to `V`, which is its stalk at
`Φ` by `overModuleStalkNatIso'`.

The universes of the site, of its morphisms and of the sections of `O` are independent; the
modules have their sections in the universe of `O`, which is the universe of the points.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w d e

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- The section `1` of the structure sheaf over `U`, read as a section of the structure sheaf
viewed as a module over itself. -/
abbrev sitePointUnitOne (U : C) :
    (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.obj (op U) :=
  (1 : ((commRingSheafToRingSheaf O).obj.obj (op U) : Type w))

/-- The germ of the unit section `1` of the structure sheaf, viewed as a module over itself, at
a chosen neighbourhood of `Φ`. -/
def moduleStalkUnitGenerator : moduleStalk Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) :=
  moduleStalkGerm Φ O _ (IsCofiltered.nonempty (C := Φ.fiber.Elements)).some.1
    (IsCofiltered.nonempty (C := Φ.fiber.Elements)).some.2 (sitePointUnitOne O _)

/-- The germ of the unit section `1` at any neighbourhood `(U, ξ)` of `Φ` equals
`moduleStalkUnitGenerator Φ O`. -/
lemma moduleStalkGerm_unitOne (U : C) (ξ : Φ.fiber.obj U) :
    moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) U ξ
        (sitePointUnitOne O U) =
      moduleStalkUnitGenerator Φ O := by
  obtain ⟨W, z, a, b, ha, hb⟩ := exists_common_nbhd (Φ := Φ) ξ
    (IsCofiltered.nonempty (C := Φ.fiber.Elements)).some.2
  rw [moduleStalkUnitGenerator, ← ha, ← hb, ← moduleStalkGerm_restrict, ← moduleStalkGerm_restrict]
  congr 1
  exact (PresheafOfModules.unit_map_one (R := (commRingSheafToRingSheaf O).obj) a.op).trans
    (PresheafOfModules.unit_map_one (R := (commRingSheafToRingSheaf O).obj) b.op).symm

/-- **The stalk of the structure sheaf, viewed as a module over itself, is free of rank one**
over the stalk ring, on the germ of `1`. -/
def moduleStalkUnitLinearEquiv :
    ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) ≃ₗ[(Φ.presheafFiber
      (A := CommRingCat.{w})).obj O.obj]
      moduleStalk Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (moduleStalkUnitGenerator Φ O)) (by
    refine ⟨(injective_iff_map_eq_zero _).2 fun r hr => ?_, fun m => ?_⟩
    · obtain ⟨U, ξ, a, rfl⟩ := ringStalkGerm_jointly_surjective Φ O r
      rw [LinearMap.toSpanSingleton_apply, ← moduleStalkGerm_unitOne Φ O U ξ,
        ← moduleStalkGerm_smul] at hr
      have ha : moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) U ξ
          (show (SheafOfModules.unit (commRingSheafToRingSheaf O)).val.obj (op U) from a) =
            moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) U ξ 0 := by
        rw [map_zero, ← hr]
        congr 1
        exact (mul_one a).symm
      obtain ⟨Y, f, y, hy, hf⟩ := (Φ.toPresheafFiber_eq_iff' U ξ _ _).1 ha
      rw [← hy, ← ringStalkGerm_restrict]
      have : ((commRingSheafToRingSheaf O).obj.map f.op).hom a = 0 := hf.trans (map_zero _)
      rw [this, map_zero]
    · obtain ⟨U, ξ, t, rfl⟩ := moduleStalkGerm_jointly_surjective Φ O _ m
      let a : (commRingSheafToRingSheaf O).obj.obj (op U) := t
      refine ⟨ringStalkGerm Φ O U ξ a, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, ← moduleStalkGerm_unitOne Φ O U ξ,
        ← moduleStalkGerm_smul Φ O _ U ξ a (sitePointUnitOne O U)]
      congr 1
      exact mul_one a)

section StrictlyPerfect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R₀ : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
  {R : Type w} [CommRing R] (G : SheafOfModules.{w} R₀ ⥤ ModuleCat.{w} R) [G.Additive]
  [PreservesFiniteColimits G] (eG : G.obj (SheafOfModules.unit R₀) ≅ ModuleCat.of R R)

/-- The sheaves of `R₀`-modules form an abelian category; given a raised priority so that the
coproducts below are found through it rather than through an instance with a free module
universe. -/
@[sga "4 II 6.7"]
local instance (priority := high) sheafOfModulesAbelian : Abelian (SheafOfModules.{w} R₀) :=
  SheafOfModules.instAbelian R₀

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] [G.Additive] in
include eG in
/-- An additive functor preserving finite colimits and carrying the unit to the free module of
rank one carries a direct summand of a finite free module to a finite projective module. -/
theorem finite_and_projective_of_isDirectSummandOfFiniteFree {M : SheafOfModules.{w} R₀}
    (hM : IsDirectSummandOfFiniteFree R₀ M) :
    Module.Finite R (G.obj M) ∧ Module.Projective R (G.obj M) := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R₀ M).1 hM
  have : HasFiniteBiproducts (SheafOfModules.{w} R₀) := Abelian.hasFiniteBiproducts
  have : HasFiniteCoproducts (SheafOfModules.{w} R₀) :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  have : HasCoproductsOfShape (ULift.{w} (Fin n)) (SheafOfModules.{w} R₀) :=
    hasColimitsOfShape_discrete _ _
  let e : G.obj (SheafOfModules.free (R := R₀) (ULift.{w} (Fin n))) ≅
      ModuleCat.of R (DirectSum (ULift.{w} (Fin n)) (fun _ => R)) :=
    PreservesCoproduct.iso G _ ≪≫ Sigma.mapIso (fun _ => eG) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : ULift.{w} (Fin n) => ModuleCat.of R R)
  have : Module.Finite R (G.obj (SheafOfModules.free (R := R₀) (ULift.{w} (Fin n)))) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have : Module.Projective R (G.obj (SheafOfModules.free (R := R₀) (ULift.{w} (Fin n)))) :=
    Module.Projective.of_equiv e.toLinearEquiv.symm
  have hs : (G.map r).hom.comp (G.map i).hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, ← G.map_comp, hir, G.map_id]
    rfl
  exact ⟨Module.Finite.of_surjective (G.map r).hom fun m =>
    ⟨(G.map i).hom m, LinearMap.congr_fun hs m⟩, Module.Projective.of_split _ _ hs⟩

variable [HasDerivedCategory.{d} (ModuleCat.{w} R)]

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
include eG in
/-- **The image of a strictly perfect complex is perfect.** An additive functor to `R`-modules
preserving finite colimits and carrying the unit to the free module of rank one carries a strictly
perfect complex to a bounded complex of finite projective `R`-modules. -/
theorem isPerfect_Q_mapHomologicalComplex_of_isStrictlyPerfect
    (P : CochainComplex (SheafOfModules.{w} R₀) ℤ) (hP : IsStrictlyPerfect R₀ P) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  have hzero (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i) := by
    refine G.map_isZero ?_
    by_contra h
    have := ha h
    have := hb h
    omega
  refine ⟨_, a, b, ?_, ?_, fun i =>
    (finite_and_projective_of_isDirectSummandOfFiniteFree G eG (hP.termDirectSummand i)).1,
    fun i => (finite_and_projective_of_isDirectSummandOfFiniteFree G eG
      (hP.termDirectSummand i)).2, ⟨Iso.refl _⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hzero i (Or.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hzero i (Or.inr hi)

end StrictlyPerfect

end Stacks

namespace AlgebraicGeometry.RingedSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, w}} [LocallySmall.{w} Z.C]
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall

/-- Restriction of scalars along a ring isomorphism carries the ring, as a module over itself,
to the other ring. -/
def restrictScalarsInvSelfIso {R R' : CommRingCat.{w}} (ρ : R' ≅ R) :
    (ModuleCat.restrictScalars ρ.inv.hom).obj (ModuleCat.of R' R') ≅ ModuleCat.of R R :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars ρ.inv.hom).obj (ModuleCat.of R' R')).isModule) _
      { toFun := fun x => ρ.hom.hom x
        invFun := fun x => ρ.inv.hom x
        map_add' := fun x y => map_add ρ.hom.hom x y
        left_inv := fun x => congrArg (fun φ => φ.hom x) ρ.hom_inv_id
        right_inv := fun x => congrArg (fun φ => φ.hom x) ρ.inv_hom_id }
      (fun r x => by
        change ρ.hom.hom (ρ.inv.hom r * (show (R' : Type w) from x)) = r * ρ.hom.hom x
        rw [map_mul]
        congr 1
        exact congrArg (fun φ => φ.hom r) ρ.inv_hom_id)

variable (Φ : Z.J.Point.{w}) [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hR : HasDerivedCategory.{e}
    (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj))]

/-- **The derived stalk of a perfect object is perfect.** Let `(C, O)` be a ringed site and `Φ` a
point of it. If `E` is a perfect object of `D(O)`, then its derived stalk `E_Φ` is a perfect
object of the derived category of modules over the stalk `O_Φ`.

A strictly perfect model of a representative of `E` exists on the members of a family covering
the final object; `Φ` lifts to one of them, `V`, through some `x`; the stalk at `Φ.over x` of
the model is a bounded complex of finite projective modules, and it is quasi-isomorphic to the
stalk at `Φ.over x` of the restriction to `V`, which is the stalk at `Φ` by Stacks 04H2. -/
theorem isPerfect_derivedModuleFiber_of_isPerfect (E : RingedSite.DerivedModules.{u, v, w, d} Z)
    (hE : Z.IsPerfect E) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
    StacksDraft.Perfect.IsPerfect ((Stacks.derivedModuleFiber Φ Z.O).obj E) := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨ι, V, hV, hmod⟩ := Z.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex K hK
  obtain ⟨e₀⟩ := IsCofiltered.nonempty (C := Φ.fiber.Elements)
  obtain ⟨Y, f, ⟨i, ⟨g⟩⟩, y, -⟩ := Φ.jointly_surjective _ (hV e₀.obj) e₀.val
  let x : Φ.fiber.obj (V i) := Φ.fiber.map g y
  obtain ⟨P, hP, q, hq⟩ := hmod i
  let ρ := overRingFiberIso Φ x
  let G := overStalkFunctor Φ x ⋙ ModuleCat.restrictScalars ρ.inv.hom
  let eG : G.obj (SheafOfModules.unit _) ≅ ModuleCat.of _ _ :=
    (ModuleCat.restrictScalars ρ.inv.hom).mapIso
      (Stacks.moduleStalkUnitLinearEquiv (Φ.over x) (Z.over (V i)).O).toModuleIso.symm ≪≫
      restrictScalarsInvSelfIso ρ
  have hqG :
      IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let α : SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) (V i) ⋙ G ≅
      stalkFunctor Φ :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (overModuleStalkNatIso' Φ x) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((ModuleCat.restrictScalarsComp' ρ.inv.hom ρ.hom.hom _ rfl).symm ≪≫
        ModuleCat.restrictScalarsId' _ (by
          ext r
          exact congrArg (fun φ => φ.hom r) ρ.inv_hom_id)) ≪≫
      Functor.rightUnitor _
  let eK' : (Stacks.derivedModuleFiber Φ Z.O).obj E ≅
      DerivedCategory.Q.obj (((stalkFunctor Φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (Stacks.derivedModuleFiber Φ Z.O).mapIso eK.symm ≪≫
      (Stacks.sheafModuleFiberOfCommRing Φ Z.O).mapDerivedCategoryFactors.app K
  let eC : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Z.restrictComplex K (V i)) ≅
      ((stalkFunctor Φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K ≪≫
      (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).app K
  exact StacksDraft.Perfect.isPerfect_of_iso
    (eK' ≪≫ DerivedCategory.Q.mapIso eC.symm ≪≫
      (asIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q))).symm)
    (Stacks.isPerfect_Q_mapHomologicalComplex_of_isStrictlyPerfect G eG P hP)

/-- **The stalk of a module which is perfect in degree zero is a perfect module.** If a module
`M` placed in degree zero is a perfect object of `D(O)`, then its stalk at `Φ`, placed in degree
zero, is a perfect object of the derived category of the stalk ring: the derived stalk of a
module in degree zero is its stalk in degree zero. -/
theorem isPerfect_singleFunctor_moduleStalk_of_isPerfect (M : RingedSite.Modules.{u, v, w} Z)
    (hM : Z.IsPerfect ((DerivedCategory.singleFunctor _ 0).obj M)) :
    StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.moduleStalk Φ Z.O M)) := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((Stacks.sheafModuleFiberOfCommRing Φ Z.O).mapDerivedCategorySingleFunctor 0 |>.app M).symm
    (isPerfect_derivedModuleFiber_of_isPerfect Φ _ hM)

end AlgebraicGeometry.RingedSite

end
