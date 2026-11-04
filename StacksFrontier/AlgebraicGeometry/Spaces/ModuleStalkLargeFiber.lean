module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointModuleFiberStalk

/-!
# The stalk of a sheaf of modules at a point of a site, in one universe

`Stacks.moduleStalkLarge` is the stalk of a sheaf of modules at a point of a site with the
universe of the module sections independent of the universe of the structure rings, while
`Stacks.moduleStalk` is the same stalk with those universes equal.  This file identifies the
two where both are defined, and specialises the identification to the site of opens of a
topological space, where the stalk of a sheaf of modules is `TopCat.Presheaf.stalk` of its
underlying presheaf of abelian groups.

## Main definitions

* `Stacks.moduleStalkLargeFiberAddEquiv`: the comparison of `Stacks.moduleStalkLarge` with
  `Stacks.moduleStalk`, on underlying additive groups, and
  `Stacks.moduleStalkLargeFiberIso`: the same comparison as an isomorphism of modules over the
  fibre of the sheaf of commutative rings.
* `TopologicalSpace.Opens.moduleStalkLargeStalkIso`: the stalk of a sheaf of modules at a point
  of the site of opens is the ordinary stalk of its underlying presheaf of abelian groups.

## Main results

* `Stacks.moduleStalkLargeFiberAddEquiv_germ` and
  `Stacks.moduleStalkLargeFiberAddEquiv_smul`: the comparison carries the germ map of
  `Stacks.moduleStalkLargeGerm` to the germ map `Stacks.toPresheafModuleFiber`, and it is
  semilinear along `Stacks.commRingSheafFiberIso`.
* `TopologicalSpace.Opens.commRingFiberStalkHom_pointFiberStalkIso_inv`: the comparison of
  rings between the fibre of a sheaf of commutative rings at a point of the site of opens and
  the stalk of its ring sheaf is, on the `CommRingCat`-valued stalk, the identification of the
  two stalks.

## Implementation notes

`Stacks.moduleStalkLarge` is a colimit over a small final model of the category of
neighbourhoods of the point, of the sections raised by `ULift`, whereas
`Stacks.presheafModuleFiber` is the colimit over all neighbourhoods of the sections themselves.
The comparison is therefore the final-model comparison followed by
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso` for the universe lift,
followed by the removal of the lift; it is formed on underlying additive groups, since on both
sides the module structure is a structure on the colimit of the sections.  Semilinearity is the
only computation: both sides are determined on germs, where it is the semilinearity of the two
germ maps, and a scalar and a section are brought over one neighbourhood because the category of
elements of the fibre functor is cofiltered.

All of this is at a single universe, as it must be: `Stacks.moduleStalk` exists only there.

## References

* [Stacks Project, Section 7.32 (Tag 00Y3)](https://stacks.math.columbia.edu/tag/00Y3)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

variable {C : Type t} [Category.{v} C] {J : GrothendieckTopology C} (p : J.Point.{u})

/-- Two single neighbourhoods of a point of a site are refined by a common one: the one-element
case of `Stacks.exists_common_neighborhood₂`. -/
private theorem exists_common_neighborhood_pair {U V : C} (x : p.fiber.obj U)
    (y : p.fiber.obj V) :
    ∃ (W : C) (w : p.fiber.obj W) (f : W ⟶ U) (g : W ⟶ V),
      p.fiber.map f w = x ∧ p.fiber.map g w = y := by
  obtain ⟨W, w, f, g, hf, hg⟩ := exists_common_neighborhood₂ p (fun _ : Unit => U)
    (fun _ : Unit => V) (fun _ => x) (fun _ => y)
  exact ⟨W, w, f (), g (), hf (), hg ()⟩

variable [LocallySmall.{u} C] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u}) (F : SheafOfModules.{u} (commRingSheafToRingSheaf O))

/-- **The stalk of a sheaf of modules at a point of a site is the stalk of its underlying
presheaf of modules**, on underlying additive groups: the colimit of the lifted sections over a
small final model of the neighbourhoods of the point is the colimit of the sections over all of
them. -/
def moduleStalkLargeFiberAddEquiv :
    moduleStalkLarge.{u} p O F ≃+
      (presheafModuleFiber p (commRingSheafToRingSheaf O).obj).obj F.val :=
  ((moduleStalkLargeFinalIso.{u} p O F).addCommGroupIsoToAddEquiv.trans
    (((p.presheafFiberCompIso AddCommGrpCat.uliftFunctor.{u}).app
      F.val.presheaf).addCommGroupIsoToAddEquiv)).trans AddEquiv.ulift

/-- The comparison carries the germ of a section over a neighbourhood of the point to the germ
of the same section. -/
theorem moduleStalkLargeFiberAddEquiv_germ (U : C) (x : p.fiber.obj U) (s : F.val.obj (op U)) :
    moduleStalkLargeFiberAddEquiv p O F (moduleStalkLargeGerm p O F U x s) =
      toPresheafModuleFiber p F.val U x s := by
  rw [moduleStalkLargeGerm_apply]
  change AddEquiv.ulift
    ((p.presheafFiberCompIso AddCommGrpCat.uliftFunctor.{u}).hom.app F.val.presheaf
      ((moduleStalkLargeFinalIso.{u} p O F).hom
        ((moduleStalkLargeFinalIso.{u} p O F).inv
          (p.toPresheafFiber U x (liftedSectionPresheaf.{u} O F) (ULift.up s))))) = _
  refine Eq.trans (congrArg (fun z => AddEquiv.ulift
      ((p.presheafFiberCompIso AddCommGrpCat.uliftFunctor.{u}).hom.app F.val.presheaf z))
    (ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{u} p O F).inv_hom_id
      (p.toPresheafFiber U x (liftedSectionPresheaf.{u} O F) (ULift.up s)))) ?_
  exact congrArg AddEquiv.ulift (ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberCompIso_hom_app (F := AddCommGrpCat.uliftFunctor.{u})
      U x F.val.presheaf) (ULift.up s))

/-- The identification of the fibre of the ring sheaf of a sheaf of commutative rings with the
fibre of the sheaf itself carries the germ of a regular function to the germ of the same
function. -/
theorem commRingSheafFiberIso_inv_toPresheafFiber (U : C) (x : p.fiber.obj U)
    (a : (commRingSheafToRingSheaf O).obj.obj (op U)) :
    (commRingSheafFiberIso p O).inv (p.toPresheafFiber U x O.obj a) =
      p.toPresheafFiber U x (commRingSheafToRingSheaf O).obj a := by
  refine Eq.trans (congrArg (fun z => (commRingSheafFiberIso p O).inv z)
    (ConcreteCategory.congr_hom
      (p.toPresheafFiber_presheafFiberCompIso_hom_app
        (F := forget₂ CommRingCat.{u} RingCat.{u}) U x O.obj) a).symm) ?_
  exact ConcreteCategory.congr_hom (commRingSheafFiberIso p O).hom_inv_id
    (p.toPresheafFiber U x (commRingSheafToRingSheaf O).obj a)

/-- **The comparison is semilinear** along the identification of the fibre of the ring sheaf of
`O` with the fibre of `O`: a scalar and a section are germs over one common neighbourhood of the
point, and there both germ maps are semilinear. -/
theorem moduleStalkLargeFiberAddEquiv_smul
    (r : (p.presheafFiber (A := CommRingCat.{u})).obj O.obj) (z : moduleStalkLarge.{u} p O F) :
    moduleStalkLargeFiberAddEquiv p O F (r • z) =
      (commRingSheafFiberIso p O).inv r • moduleStalkLargeFiberAddEquiv p O F z := by
  obtain ⟨U, x, a, ha⟩ := p.toPresheafFiber_jointly_surjective (P := O.obj) r
  obtain ⟨V, y, b, hb⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  obtain ⟨W, t, f, g, hfx, hgy⟩ := exists_common_neighborhood_pair p x y
  obtain ⟨a', hr⟩ : ∃ a' : (commRingSheafToRingSheaf O).obj.obj (op W),
      p.toPresheafFiber W t O.obj a' = r :=
    ⟨O.obj.map f.op a, ((p.toPresheafFiber_w_apply f t O.obj a).trans
      (congrArg (fun c => p.toPresheafFiber U c O.obj a) hfx)).trans ha⟩
  obtain ⟨b', hm⟩ : ∃ b' : F.val.obj (op W), moduleStalkLargeGerm p O F W t b' = z :=
    ⟨F.val.map g.op b, ((moduleStalkLargeGerm_w p O F g t b).trans
      (congrArg (fun c => moduleStalkLargeGerm p O F V c b) hgy)).trans hb⟩
  rw [← hr, ← hm, ← moduleStalkLargeGerm_smul, moduleStalkLargeFiberAddEquiv_germ,
    moduleStalkLargeFiberAddEquiv_germ, commRingSheafFiberIso_inv_toPresheafFiber,
    toPresheafModuleFiber_smul]

/-- **The stalk of a sheaf of modules at a point of a site, in one universe, is the stalk
`Stacks.moduleStalk`**: the comparison of `Stacks.moduleStalkLargeFiberAddEquiv` as a morphism of
modules over the fibre of the sheaf of commutative rings. -/
def moduleStalkLargeFiberHom : moduleStalkLarge.{u} p O F ⟶ moduleStalk p O F :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u} ((p.presheafFiber (A := CommRingCat.{u})).obj O.obj))
    { toFun := fun z => moduleStalkLargeFiberAddEquiv p O F z
      map_add' := fun z z' => map_add (moduleStalkLargeFiberAddEquiv p O F) z z'
      map_smul' := fun r z => moduleStalkLargeFiberAddEquiv_smul p O F r z }

/-- The morphism `Stacks.moduleStalkLargeFiberHom` sends an element to its image under
`Stacks.moduleStalkLargeFiberAddEquiv`. -/
theorem moduleStalkLargeFiberHom_apply (z : moduleStalkLarge.{u} p O F) :
    moduleStalkLargeFiberHom p O F z = moduleStalkLargeFiberAddEquiv p O F z := rfl

/-- The morphism `Stacks.moduleStalkLargeFiberHom` is an isomorphism of modules. -/
instance isIso_moduleStalkLargeFiberHom : IsIso (moduleStalkLargeFiberHom p O F) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (moduleStalkLargeFiberAddEquiv p O F).bijective

/-- **The two stalks of a sheaf of modules at a point of a site agree**, as modules over the
fibre of the sheaf of commutative rings. -/
def moduleStalkLargeFiberIso : moduleStalkLarge.{u} p O F ≅ moduleStalk p O F :=
  asIso (moduleStalkLargeFiberHom p O F)

/-- The forward map of `Stacks.moduleStalkLargeFiberIso` sends an element to its image under
`Stacks.moduleStalkLargeFiberAddEquiv`. -/
theorem moduleStalkLargeFiberIso_hom_apply (z : moduleStalkLarge.{u} p O F) :
    (moduleStalkLargeFiberIso p O F).hom z = moduleStalkLargeFiberAddEquiv p O F z := rfl

end Stacks

namespace Opens

variable {Z : TopCat.{u}} (x : Z)
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})

/-- **The comparison of rings between the fibre of a sheaf of commutative rings at the point of
the site of opens attached to `x` and the stalk of its ring sheaf at `x` is the identification
of the two stalks**, once the fibre is identified with the `CommRingCat`-valued stalk. -/
theorem commRingFiberStalkHom_pointFiberStalkIso_inv
    [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (c : TopCat.Presheaf.stalk (C := CommRingCat.{u}) O.obj x) :
    commRingFiberStalkHom x O ((pointFiberStalkIso x O.obj).inv c) =
      (SemilinearStalk.commStalkIso O.obj x).inv c := by
  refine ((ConcreteCategory.congr_hom (SemilinearStalk.commStalkIso O.obj x).hom_inv_id
    (commRingFiberStalkHom x O ((pointFiberStalkIso x O.obj).inv c))).symm.trans ?_)
  refine congrArg (SemilinearStalk.commStalkIso O.obj x).inv ?_
  refine (ConcreteCategory.congr_hom (commRingFiberStalkHom_comp_commStalkIso x O)
    ((pointFiberStalkIso x O.obj).inv c)).trans ?_
  exact ConcreteCategory.congr_hom (pointFiberStalkIso x O.obj).inv_hom_id c

variable [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (F : _root_.SheafOfModules.{u}
    (Stacks.commRingSheafToRingSheaf (J := Opens.grothendieckTopology Z) O))

/-- **The stalk of a sheaf of modules at a point of the site of opens is the ordinary stalk of
its underlying presheaf of abelian groups**, as a module over the fibre of the structure sheaf
at that point with scalars restricted along
`TopologicalSpace.Opens.commRingFiberStalkHom`. -/
def moduleStalkLargeStalkIso :
    Stacks.moduleStalkLarge.{u} (pointGrothendieckTopology x) O F ≅
      (ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x O).hom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.commRingSheafToRingSheaf O) x).obj F) :=
  Stacks.moduleStalkLargeFiberIso (pointGrothendieckTopology x) O F ≪≫
    (moduleFiberStalkFunctorIsoOfCommRing x O).app F

end Opens

end
