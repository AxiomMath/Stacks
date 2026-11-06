module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkSemilinearComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOver

/-!
# The module stalk of a restriction to a slice, at a lifted point

Let `(C, J)` be a site, `Φ` a point of it, `U` an object of `C` and `x ∈ Φ.fiber U`, so that
`Φ.over x` is a point of the slice site `C/U` lying over `Φ` (Stacks 04H2). For a sheaf of
commutative rings `O` and a sheaf of `O`-modules `M`, the stalk of the restriction `M|_U` at
`Φ.over x`, a module over `(O|_U)_{Φ.over x}`, is the stalk `M_Φ` with its scalars restricted
along the identification `(O|_U)_{Φ.over x} ≅ O_Φ` of Stacks 04H2.

## Main definitions

* `Stacks.ringFiberOverEquiv`: the ring isomorphism `(O|_U)_{Φ.over x} ≃ O_Φ`.
* `Stacks.sliceModuleStalkIso`: the isomorphism `(M|_U)_{Φ.over x} ≅ M_Φ` of modules over
  `(O|_U)_{Φ.over x}`.

## Main results

* `Stacks.ringFiberOverEquiv_ringStalkGerm` and `Stacks.sliceModuleStalkIso_hom_germ`: both
  identifications send the germ at a neighbourhood `(W, y)` of `Φ.over x` to the germ at the
  neighbourhood `(W.left, y)` of `Φ`.
* `Stacks.sliceModuleStalkIso_naturality`: the module identification is natural in `M`.

## Implementation notes

On underlying abelian groups the identification is `Stacks.moduleStalkOverAddIso` of
`StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOver`; here the scalars are restricted on the
side of `M_Φ`, along `Stacks.ringFiberOverEquiv`, the inverse of `Stacks.ringStalkOverEquiv`.

## References

* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) {U : C} (x : Φ.fiber.obj U) (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The germ at a neighbourhood `(W, y)` of `Φ.over x` of a section of a restricted presheaf is
carried by the comparison of Stacks 04H2 to the germ at `(W.left, y)` of the same section. -/
theorem presheafFiberOverIso_hom_toPresheafFiber_apply {A : Type*} [Category A]
    [HasColimitsOfSize.{w, w} A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    (P : Cᵒᵖ ⥤ A) (W : Over U) (y : (Φ.over x).fiber.obj W)
    (s : ToType (P.obj (op W.left))) :
    ((Φ.presheafFiberOverIso x A).app P).hom
        ((Φ.over x).toPresheafFiber W y ((Over.forget U).op ⋙ P) s) =
      Φ.toPresheafFiber W.left y.val P s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom
      (Functor.Final.ι_colimitIso_hom (GrothendieckTopology.Point.overElements Φ x).op
        ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ((Φ.over x).fiber.elementsMk W y))) s)

/-- **The stalk of a restricted sheaf of rings at a lifted point** (Stacks 04H2): the ring
`(O|_U)_{Φ.over x}` is `O_Φ`. -/
def ringFiberOverEquiv :
    ((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj (O.over U).obj ≃+*
      (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj :=
  ((Φ.presheafFiberOverIso x CommRingCat.{w}).app O.obj).commRingCatIsoToRingEquiv

/-- The ring identification of Stacks 04H2 sends a germ at `(W, y)` to the germ at
`(W.left, y)`. -/
theorem ringFiberOverEquiv_ringStalkGerm (W : Over U) (y : (Φ.over x).fiber.obj W)
    (a : (commRingSheafToRingSheaf O).obj.obj (op W.left)) :
    ringFiberOverEquiv Φ x O (ringStalkGerm (Φ.over x) (O.over U) W y a) =
      ringStalkGerm Φ O W.left y.val a :=
  presheafFiberOverIso_hom_toPresheafFiber_apply Φ x O.obj W y a

variable (U) in
/-- Restriction of sheaves of `O`-modules to the slice over `U`, read as sheaves of modules over
the restricted sheaf of commutative rings `O|_U`. -/
abbrev overFunctorOfCommRing :
    SheafOfModules.{w} (commRingSheafToRingSheaf O) ⥤
      SheafOfModules.{w} (commRingSheafToRingSheaf (O.over U)) :=
  SheafOfModules.overFunctor (commRingSheafToRingSheaf O) U

variable (M : SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- **The module stalk of a restriction to a slice at a lifted point** (Stacks 04H2): the stalk
of `M|_U` at `Φ.over x` is `M_Φ`, as a module over `(O|_U)_{Φ.over x}` through
`Stacks.ringFiberOverEquiv`. -/
def sliceModuleStalkIso :
    moduleStalk (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).obj M) ≅
      (ModuleCat.restrictScalars (ringFiberOverEquiv Φ x O).toRingHom).obj (moduleStalk Φ O M) :=
  ModuleCat.isoMk (moduleStalkOverAddIso Φ x O M) (fun r => by
    ext n
    exact (moduleStalkOverAddEquiv_smul Φ x O M r n).symm)

/-- On underlying elements, the forward map of `Stacks.sliceModuleStalkIso` is
`Stacks.moduleStalkOverAddEquiv`. -/
theorem sliceModuleStalkIso_hom_apply
    (n : moduleStalk (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).obj M)) :
    (sliceModuleStalkIso Φ x O M).hom n = moduleStalkOverAddEquiv Φ x O M n :=
  rfl

/-- The identification `(M|_U)_{Φ.over x} ≅ M_Φ` sends the germ at `(W, y)` of a section `s` to
the germ of `s` at `(W.left, y)`. -/
theorem sliceModuleStalkIso_hom_germ (W : Over U) (y : (Φ.over x).fiber.obj W)
    (s : M.val.obj (op W.left)) :
    (sliceModuleStalkIso Φ x O M).hom
        (moduleStalkGerm (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).obj M) W y s) =
      moduleStalkGerm Φ O M W.left y.val s :=
  (sliceModuleStalkIso_hom_apply Φ x O M _).trans
    (moduleStalkOverAddEquiv_moduleStalkGerm Φ x O M W y s)

/-- The identification `(M|_U)_{Φ.over x} ≅ M_Φ` is natural in `M`. -/
theorem sliceModuleStalkIso_naturality {M M' : SheafOfModules.{w} (commRingSheafToRingSheaf O)}
    (g : M ⟶ M') :
    (sheafModuleFiberOfCommRing (Φ.over x) (O.over U)).map ((overFunctorOfCommRing U O).map g) ≫
        (sliceModuleStalkIso Φ x O M').hom =
      (sliceModuleStalkIso Φ x O M).hom ≫
        (ModuleCat.restrictScalars (ringFiberOverEquiv Φ x O).toRingHom).map
          ((sheafModuleFiberOfCommRing Φ O).map g) := by
  ext n
  obtain ⟨W, y, s, rfl⟩ := moduleStalkGerm_jointly_surjective (Φ.over x) (O.over U)
    ((overFunctorOfCommRing U O).obj M) n
  change (sliceModuleStalkIso Φ x O M').hom
      ((sheafModuleFiberOfCommRing (Φ.over x) (O.over U)).map ((overFunctorOfCommRing U O).map g)
        (moduleStalkGerm (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).obj M) W y s)) =
    (sheafModuleFiberOfCommRing Φ O).map g ((sliceModuleStalkIso Φ x O M).hom
      (moduleStalkGerm (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).obj M) W y s))
  refine (congrArg (sliceModuleStalkIso Φ x O M').hom
    (moduleStalkGerm_naturality (Φ.over x) (O.over U) ((overFunctorOfCommRing U O).map g)
      W y s)).trans ?_
  refine (sliceModuleStalkIso_hom_germ Φ x O M' W y _).trans ?_
  refine Eq.trans ?_ (congrArg ((sheafModuleFiberOfCommRing Φ O).map g)
    (sliceModuleStalkIso_hom_germ Φ x O M W y s)).symm
  exact (moduleStalkGerm_naturality Φ O g W.left y.val s).symm

/-- The identification `(M|_U)_{Φ.over x} ≅ M_Φ`, as an isomorphism of functors. -/
def sliceModuleStalkNatIso :
    overFunctorOfCommRing U O ⋙ sheafModuleFiberOfCommRing (Φ.over x) (O.over U) ≅
      sheafModuleFiberOfCommRing Φ O ⋙
        ModuleCat.restrictScalars (ringFiberOverEquiv Φ x O).toRingHom :=
  NatIso.ofComponents (sliceModuleStalkIso Φ x O) (fun g => sliceModuleStalkIso_naturality Φ x O g)

end Stacks

end
