module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksCore.Tactic.StacksAttribute

/-!
# The two presentations of the stalk of a sheaf of modules at a point of a site

Let `(C, J)` be a site, `p` a point of it, `O` a sheaf of commutative rings on `C` and `F` a
sheaf of `O`-modules.  Two constructions of the stalk `F_p`, as a module over the stalk ring
`O_p`, are in use:

* `Stacks.moduleStalk`, the value at `F` of the stalk functor
  `Stacks.sheafModuleFiberOfCommRing`, built from the colimit over the whole category of
  elements of the fibre functor of `p`;
* `Stacks.moduleStalkLarge`, a colimit over a *small final model* of that category, of the
  sections raised to a module universe `m` independent of the universe of the structure rings.

At `m` the universe of the structure rings the two are modules over one and the same ring, and
this file identifies them.  The identification is the one that matches germs: the germ of a
section over a neighbourhood of `p` on one side is the germ of the same section on the other.

## Main definitions

* `Stacks.liftedModuleStalkGerm`: the germ maps into `Stacks.moduleStalk`, read on the lifted
  sections of which the final-model stalk is a colimit.
* `Stacks.moduleStalkLargeToModuleStalk` and `Stacks.moduleStalkToModuleStalkLarge`: the two
  comparison maps, each determined by sending a germ to the germ of the same section.

## Main results

* `Stacks.moduleStalkLargeLinearEquiv` and `Stacks.moduleStalkLargeIso`: the comparison, as a
  linear equivalence over the stalk of `O` and as an isomorphism of `ModuleCat` objects.
* `Stacks.moduleStalkLargeLinearEquiv_germ`: it carries the germ of a section to the germ of the
  same section.
* `Stacks.exists_ringStalkGerm_and_moduleStalkLargeGerm`: an element of the stalk of the
  structure sheaf and an element of the final-model stalk are germs of sections over one common
  neighbourhood of the point.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  (F : SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-! ### The two comparison maps -/

/-- The germ maps into `Stacks.moduleStalk`, read on the lifted sections that the final-model
stalk is a colimit of. -/
def liftedModuleStalkGerm (U : C) (ξ : p.fiber.obj U) :
    (liftedSectionPresheaf.{w} O F).obj (op U) ⟶ AddCommGrpCat.of (moduleStalk p O F) :=
  AddCommGrpCat.ofHom ((moduleStalkGerm p O F U ξ).comp
    (AddEquiv.ulift (α := F.val.obj (op U))).toAddMonoidHom)

/-- The germ maps into `Stacks.moduleStalk` on lifted sections are compatible with restriction
along a morphism of neighbourhoods. -/
theorem liftedModuleStalkGerm_w ⦃V U : C⦄ (g : V ⟶ U) (η : p.fiber.obj V) :
    (liftedSectionPresheaf.{w} O F).map g.op ≫ liftedModuleStalkGerm p O F V η =
      liftedModuleStalkGerm p O F U (p.fiber.map g η) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s ↦ moduleStalkGerm_restrict p O F g η s.down)

/-- The germ maps into the final-model stalk are compatible with restriction along a morphism of
neighbourhoods. -/
theorem moduleStalkLargeGerm_hom_w ⦃V U : C⦄ (g : V ⟶ U) (η : p.fiber.obj V) :
    F.val.presheaf.map g.op ≫ AddCommGrpCat.ofHom (moduleStalkLargeGerm p O F V η) =
      AddCommGrpCat.ofHom (moduleStalkLargeGerm p O F U (p.fiber.map g η)) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s ↦ moduleStalkLargeGerm_w p O F g η s)

/-- The comparison out of the final-model stalk: the germ of a section over a neighbourhood of
`p` goes to the germ of the same section in `Stacks.moduleStalk`. -/
def moduleStalkLargeToModuleStalk : moduleStalkLarge.{w} p O F →+ moduleStalk p O F :=
  (p.presheafFiberDesc (liftedModuleStalkGerm p O F)
      (liftedModuleStalkGerm_w p O F)).hom.comp
    (moduleStalkLargeFinalIso.{w} p O F).hom.hom

/-- The comparison into the final-model stalk: the germ of a section over a neighbourhood of
`p` goes to the germ of the same section in `Stacks.moduleStalkLarge`. -/
def moduleStalkToModuleStalkLarge : moduleStalk p O F →+ moduleStalkLarge.{w} p O F :=
  (p.presheafFiberDesc (P := F.val.presheaf)
    (fun U ξ ↦ AddCommGrpCat.ofHom (moduleStalkLargeGerm p O F U ξ))
    (moduleStalkLargeGerm_hom_w p O F)).hom

/-- The comparison out of the final-model stalk sends a germ to the germ of the same
section. -/
theorem moduleStalkLargeToModuleStalk_germ (U : C) (ξ : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkLargeToModuleStalk p O F (moduleStalkLargeGerm p O F U ξ s) =
      moduleStalkGerm p O F U ξ s := by
  have h : (moduleStalkLargeFinalIso.{w} p O F).hom.hom
      ((moduleStalkLargeFinalIso.{w} p O F).inv.hom
        (p.toPresheafFiber U ξ (liftedSectionPresheaf.{w} O F) (ULift.up s))) =
      p.toPresheafFiber U ξ (liftedSectionPresheaf.{w} O F) (ULift.up s) :=
    ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{w} p O F).inv_hom_id _
  refine Eq.trans (congrArg
    (p.presheafFiberDesc (liftedModuleStalkGerm p O F)
      (liftedModuleStalkGerm_w p O F)).hom h) ?_
  exact ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberDesc (liftedModuleStalkGerm p O F)
      (liftedModuleStalkGerm_w p O F) U ξ) (ULift.up s)

/-- The comparison into the final-model stalk sends a germ to the germ of the same section. -/
theorem moduleStalkToModuleStalkLarge_germ (U : C) (ξ : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkToModuleStalkLarge p O F (moduleStalkGerm p O F U ξ s) =
      moduleStalkLargeGerm p O F U ξ s :=
  ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberDesc (P := F.val.presheaf)
      (fun U ξ ↦ AddCommGrpCat.ofHom (moduleStalkLargeGerm p O F U ξ))
      (moduleStalkLargeGerm_hom_w p O F) U ξ) s

/-! ### The comparison -/

/-- Every germ of the final-model stalk is fixed by the round trip through
`Stacks.moduleStalk`. -/
theorem moduleStalkLargeToModuleStalk_leftInverse :
    Function.LeftInverse (moduleStalkToModuleStalkLarge p O F)
      (moduleStalkLargeToModuleStalk p O F) := by
  intro z
  obtain ⟨U, ξ, s, rfl⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  rw [moduleStalkLargeToModuleStalk_germ, moduleStalkToModuleStalkLarge_germ]

/-- Every germ of `Stacks.moduleStalk` is fixed by the round trip through the final-model
stalk. -/
theorem moduleStalkLargeToModuleStalk_rightInverse :
    Function.RightInverse (moduleStalkToModuleStalkLarge p O F)
      (moduleStalkLargeToModuleStalk p O F) := by
  intro z
  obtain ⟨U, ξ, s, rfl⟩ := moduleStalkGerm_jointly_surjective p O F z
  rw [moduleStalkToModuleStalkLarge_germ, moduleStalkLargeToModuleStalk_germ]

/-- An element of the stalk of the structure sheaf and an element of the final-model stalk of a
sheaf of modules are germs of sections over one common neighbourhood of the point. -/
theorem exists_ringStalkGerm_and_moduleStalkLargeGerm
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{w} p O F) :
    ∃ (U : C) (ξ : p.fiber.obj U) (a : (commRingSheafToRingSheaf O).obj.obj (op U))
      (s : F.val.obj (op U)),
      ringStalkGerm p O U ξ a = r ∧ moduleStalkLargeGerm p O F U ξ s = z := by
  obtain ⟨U₁, ξ₁, a₀, ha₀⟩ := ringStalkGerm_jointly_surjective p O r
  obtain ⟨U₂, ξ₂, s₀, hs₀⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  obtain ⟨V, η, g₁, g₂, hg₁, hg₂⟩ := exists_common_neighborhood₂ p
    (fun _ : Unit ↦ U₁) (fun _ : Unit ↦ U₂) (fun _ ↦ ξ₁) (fun _ ↦ ξ₂)
  refine ⟨V, η, ((commRingSheafToRingSheaf O).obj.map (g₁ ()).op).hom a₀,
    (F.val.map (g₂ ()).op).hom s₀, ?_, ?_⟩
  · rwa [ringStalkGerm_restrict, hg₁ ()]
  · rwa [moduleStalkLargeGerm_w, hg₂ ()]

/-- **The two stalks agree**, as an isomorphism of additive groups carrying the germ of a
section to the germ of the same section. -/
def moduleStalkLargeAddEquiv : moduleStalkLarge.{w} p O F ≃+ moduleStalk p O F where
  __ := moduleStalkLargeToModuleStalk p O F
  invFun := moduleStalkToModuleStalkLarge p O F
  left_inv := moduleStalkLargeToModuleStalk_leftInverse p O F
  right_inv := moduleStalkLargeToModuleStalk_rightInverse p O F

/-- **The two stalks agree**, as a linear equivalence over the stalk of `O`. -/
def moduleStalkLargeLinearEquiv :
    moduleStalkLarge.{w} p O F ≃ₗ[(p.presheafFiber (A := CommRingCat.{w})).obj O.obj]
      moduleStalk p O F where
  __ := moduleStalkLargeAddEquiv p O F
  map_smul' r z := by
    obtain ⟨U, ξ, a, s, rfl, rfl⟩ := exists_ringStalkGerm_and_moduleStalkLargeGerm p O F r z
    change moduleStalkLargeToModuleStalk p O F
        (p.toPresheafFiber U ξ O.obj a • moduleStalkLargeGerm p O F U ξ s) =
      p.toPresheafFiber U ξ O.obj a •
        moduleStalkLargeToModuleStalk p O F (moduleStalkLargeGerm p O F U ξ s)
    rw [← moduleStalkLargeGerm_smul, moduleStalkLargeToModuleStalk_germ,
      moduleStalkLargeToModuleStalk_germ, moduleStalkGerm_smul]
    rfl

/-- The comparison carries the germ of a section to the germ of the same section. -/
theorem moduleStalkLargeLinearEquiv_germ (U : C) (ξ : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkLargeLinearEquiv p O F (moduleStalkLargeGerm p O F U ξ s) =
      moduleStalkGerm p O F U ξ s :=
  moduleStalkLargeToModuleStalk_germ p O F U ξ s

/-- **The two stalks agree**, as an isomorphism of modules over the stalk of `O`. -/
def moduleStalkLargeIso : moduleStalkLarge.{w} p O F ≅ moduleStalk p O F :=
  (moduleStalkLargeLinearEquiv p O F).toModuleIso

end Stacks

end

end
