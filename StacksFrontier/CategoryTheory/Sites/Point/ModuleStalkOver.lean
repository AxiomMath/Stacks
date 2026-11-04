module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkSemilinearComparison
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint

/-!
# The stalk of a sheaf of modules at a point of a localized site

Let `(C, J)` be a site, `Φ` a point of it, `V` an object of `C` and `q ∈ Φ.fiber.obj V`, so that
`Φ.over q` is the point of the localized site `C/V` of Stacks 04H2. For a sheaf of commutative
rings `O` on `C`, the stalk of `O` at `Φ` is the stalk of its restriction `O.over V` at
`Φ.over q`. For a sheaf `M` of `O`-modules, the stalk of `M` at `Φ` is likewise the stalk of its
restriction to `C/V` at `Φ.over q`, and this identification is semilinear over the
identification of the ring stalks and natural in `M`. This is Stacks 04H2 for sheaves of
modules: the triangle formed by `Φ.over q`, `Φ` and the localization morphism of ringed topoi
commutes on stalks of modules.

## Main definitions

* `Stacks.ringStalkOverEquiv` : the stalk of `O` at `Φ` is the stalk of `O.over V` at
  `Φ.over q`, as commutative rings.
* `Stacks.moduleStalkOverAddIso` and `Stacks.moduleStalkOverAddEquiv` : the stalk of `M` at `Φ`
  is the stalk of its restriction at `Φ.over q`, as abelian groups.
* `Stacks.moduleStalkOverIso` : the same identification, as modules over the stalk of `O`
  at `Φ`.
* `Stacks.sheafModuleFiberOverIso` : restricting a sheaf of `O`-modules to `C/V` and taking its
  stalk at `Φ.over q`, viewed as a module over the stalk of `O` at `Φ`, is the stalk at `Φ`, as
  an isomorphism of functors.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_comp_presheafFiberOverIso_hom_app` :
  the comparison of Stacks 04H2 takes the germ of a section at a neighbourhood of `Φ.over q` to
  its germ at `Φ`.
* `Stacks.ringStalkOverEquiv_toPresheafFiber` : the ring comparison matches germs.
* `Stacks.moduleStalkOverAddEquiv_smul` : the comparison of module stalks is semilinear over the
  ring comparison.
* `Stacks.sheafModuleFiberOverIso_hom_app_moduleStalkGerm` : the module comparison matches
  germs.

## Implementation notes

All comparisons are the colimit comparison `presheafFiberOverIso` of Stacks 04H2: on the
underlying abelian groups no other map occurs. Semilinearity is checked on germs over a common
neighbourhood of `Φ.over q`, which exists since the category of neighbourhoods of a point is
cofiltered.

The restriction functor `SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V` takes values
in sheaves of modules over `(commRingSheafToRingSheaf O).over V`, while the stalk functor at
`Φ.over q` is the one for sheaves of modules over `commRingSheafToRingSheaf (O.over V)`. The two
sheaves of rings are equal by definition, both having underlying presheaf
`(Over.forget V).op ⋙ O.val ⋙ forget₂ CommRingCat RingCat`, so the composite in
`Stacks.sheafModuleFiberOverIso` typechecks as written.

## References

* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u' v'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) {V : C} (q : Φ.fiber.obj V)
  (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{w, w} A]


/-- The comparison `presheafFiberOverIso` of Stacks 04H2 takes the germ of a section of a
restricted presheaf at a neighbourhood of `Φ.over q` to the germ of the same section at `Φ`. -/
@[reassoc]
lemma toPresheafFiber_comp_presheafFiberOverIso_hom_app (P : Cᵒᵖ ⥤ A) (W : Over V)
    (y : (Φ.over q).fiber.obj W) :
    (Φ.over q).toPresheafFiber W y ((Over.forget V).op ⋙ P) ≫
        (presheafFiberOverIso Φ q A).hom.app P =
      Φ.toPresheafFiber W.left y.val P :=
  Functor.Final.ι_colimitIso_hom (overElements Φ q).op
    ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨W, y⟩)

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) {V : C} (q : Φ.fiber.obj V)

section Ring

variable (O : Sheaf J CommRingCat.{w})

/-- The stalk at `Φ` of a sheaf of commutative rings `O` is the stalk at `Φ.over q` of its
restriction `O.over V` to the localized site: Stacks 04H2 for the sheaf of rings. -/
def ringStalkOverEquiv :
    (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj ≃+*
      ((Φ.over q).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj :=
  ((GrothendieckTopology.Point.presheafFiberOverIso Φ q CommRingCat.{w}).app
    O.obj).symm.commRingCatIsoToRingEquiv

/-- `Stacks.ringStalkOverEquiv` takes the germ at `Φ` of a section over `W.left` to its germ at
the neighbourhood `(W, y)` of `Φ.over q`. -/
lemma ringStalkOverEquiv_toPresheafFiber (W : Over V) (y : (Φ.over q).fiber.obj W)
    (s : O.obj.obj (op W.left)) :
    ringStalkOverEquiv Φ q O (Φ.toPresheafFiber W.left y.val O.obj s) =
      (Φ.over q).toPresheafFiber W y (O.over V).obj s := by
  have h := ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.toPresheafFiber_comp_presheafFiberOverIso_hom_app Φ q
      CommRingCat.{w} O.obj W y) s
  show ((GrothendieckTopology.Point.presheafFiberOverIso Φ q CommRingCat.{w}).app
    O.obj).inv _ = _
  rw [← h]
  exact ConcreteCategory.congr_hom
    ((GrothendieckTopology.Point.presheafFiberOverIso Φ q CommRingCat.{w}).app O.obj).hom_inv_id
    _

/-- The inverse of `Stacks.ringStalkOverEquiv` takes the germ at the neighbourhood `(W, y)` of
`Φ.over q` of a section over `W.left` to its germ at `Φ`. -/
lemma ringStalkOverEquiv_symm_toPresheafFiber (W : Over V) (y : (Φ.over q).fiber.obj W)
    (s : O.obj.obj (op W.left)) :
    (ringStalkOverEquiv Φ q O).symm ((Φ.over q).toPresheafFiber W y (O.over V).obj s) =
      Φ.toPresheafFiber W.left y.val O.obj s := by
  rw [RingEquiv.symm_apply_eq, ringStalkOverEquiv_toPresheafFiber]

end Ring

section Module

variable (O : Sheaf J CommRingCat.{w}) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over V).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying additive comparison of `Stacks.sheafModuleFiberOverIso`: the stalk at
`Φ.over q` of the restriction of `M` to the localized site is the stalk of `M` at `Φ`, as
abelian groups. It is `presheafFiberOverIso` for the underlying presheaf of abelian groups. -/
def moduleStalkOverAddIso (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    (forget₂ _ AddCommGrpCat.{w}).obj ((ModuleCat.restrictScalars
        (ringStalkOverEquiv Φ q O).toRingHom).obj
      (moduleStalk (Φ.over q) (O.over V)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M))) ≅
      (forget₂ _ AddCommGrpCat.{w}).obj (moduleStalk Φ O M) :=
  (Iso.refl _ : (forget₂ _ AddCommGrpCat.{w}).obj ((ModuleCat.restrictScalars
        (ringStalkOverEquiv Φ q O).toRingHom).obj
      (moduleStalk (Φ.over q) (O.over V)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M))) ≅
    (forget₂ _ AddCommGrpCat.{w}).obj
      (moduleStalk (Φ.over q) (O.over V)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M))) ≪≫
  (Iso.refl _ : (forget₂ _ AddCommGrpCat.{w}).obj
      (moduleStalk (Φ.over q) (O.over V)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M)) ≅
    ((Φ.over q).presheafFiber (A := AddCommGrpCat.{w})).obj
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M).val.presheaf) ≪≫
  (Iso.refl _ : ((Φ.over q).presheafFiber (A := AddCommGrpCat.{w})).obj
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M).val.presheaf ≅
    ((Φ.over q).presheafFiber (A := AddCommGrpCat.{w})).obj
      ((Over.forget V).op ⋙ M.val.presheaf)) ≪≫
  ((GrothendieckTopology.Point.presheafFiberOverIso Φ q AddCommGrpCat.{w}).app M.val.presheaf :
    ((Φ.over q).presheafFiber (A := AddCommGrpCat.{w})).obj
      ((Over.forget V).op ⋙ M.val.presheaf) ≅
    (Φ.presheafFiber (A := AddCommGrpCat.{w})).obj M.val.presheaf) ≪≫
  (Iso.refl _ : (Φ.presheafFiber (A := AddCommGrpCat.{w})).obj M.val.presheaf ≅
    (forget₂ _ AddCommGrpCat.{w}).obj (moduleStalk Φ O M))

/-- `Stacks.moduleStalkOverAddIso` as an additive equivalence between the two module stalks. -/
def moduleStalkOverAddEquiv (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    moduleStalk (Φ.over q) (O.over V)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) ≃+
      moduleStalk Φ O M :=
  (moduleStalkOverAddIso Φ q O M).addCommGroupIsoToAddEquiv

/-- `Stacks.moduleStalkOverAddEquiv` takes the germ at a neighbourhood `(W, y)` of `Φ.over q` of
a section of the restriction of `M` over `W` to the germ at `Φ` of the same section of `M` over
`W.left`. -/
lemma moduleStalkOverAddEquiv_moduleStalkGerm
    (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) (W : Over V)
    (y : (Φ.over q).fiber.obj W) (m : M.val.obj (op W.left)) :
    moduleStalkOverAddEquiv Φ q O M
        (moduleStalkGerm (Φ.over q) (O.over V)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) W y m) =
      moduleStalkGerm Φ O M W.left y.val m := by
  show ((GrothendieckTopology.Point.presheafFiberOverIso Φ q AddCommGrpCat.{w}).app
      M.val.presheaf).hom
      ((Φ.over q).toPresheafFiber W y ((Over.forget V).op ⋙ M.val.presheaf) m) =
    Φ.toPresheafFiber W.left y.val M.val.presheaf m
  exact ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.toPresheafFiber_comp_presheafFiberOverIso_hom_app Φ q
      AddCommGrpCat.{w} M.val.presheaf W y) m

/-- `Stacks.moduleStalkOverAddEquiv` is compatible with scalars on germs over a common
neighbourhood `(W, y)` of `Φ.over q`. -/
lemma moduleStalkOverAddEquiv_toPresheafFiber_smul
    (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) (W : Over V)
    (y : (Φ.over q).fiber.obj W) (s : (commRingSheafToRingSheaf O).obj.obj (op W.left))
    (m : M.val.obj (op W.left)) :
    moduleStalkOverAddEquiv Φ q O M
        ((Φ.over q).toPresheafFiber W y (O.over V).obj s •
          moduleStalkGerm (Φ.over q) (O.over V)
            ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) W y m) =
      Φ.toPresheafFiber W.left y.val O.obj s • moduleStalkGerm Φ O M W.left y.val m := by
  have h₁ := moduleStalkGerm_smul (Φ.over q) (O.over V)
    ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) W y s m
  have h₂ := moduleStalkGerm_smul Φ O M W.left y.val s m
  have h₃ := moduleStalkOverAddEquiv_moduleStalkGerm Φ q O M W y (s • m)
  exact (congrArg (moduleStalkOverAddEquiv Φ q O M) h₁.symm).trans (h₃.trans h₂)

/-- `Stacks.moduleStalkOverAddEquiv` is semilinear over the inverse of the ring comparison
`Stacks.ringStalkOverEquiv`. -/
lemma moduleStalkOverAddEquiv_smul (M : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (r : ((Φ.over q).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj)
    (n : moduleStalk (Φ.over q) (O.over V)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M)) :
    moduleStalkOverAddEquiv Φ q O M (r • n) =
      (ringStalkOverEquiv Φ q O).symm r • moduleStalkOverAddEquiv Φ q O M n := by
  obtain ⟨W₁, y₁, s, rfl⟩ := (Φ.over q).toPresheafFiber_jointly_surjective
    (P := (O.over V).obj) r
  obtain ⟨W₂, y₂, m, rfl⟩ := toPresheafModuleFiber_jointly_surjective (Φ.over q)
    ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M).val n
  obtain ⟨W, y, g₁, g₂, rfl, rfl⟩ : ∃ (W : Over V) (y : (Φ.over q).fiber.obj W)
      (g₁ : W ⟶ W₁) (g₂ : W ⟶ W₂),
      (Φ.over q).fiber.map g₁ y = y₁ ∧ (Φ.over q).fiber.map g₂ y = y₂ :=
    ⟨_, _, (IsCofiltered.minToLeft ((Φ.over q).fiber.elementsMk W₁ y₁)
        ((Φ.over q).fiber.elementsMk W₂ y₂)).1,
      (IsCofiltered.minToRight ((Φ.over q).fiber.elementsMk W₁ y₁)
        ((Φ.over q).fiber.elementsMk W₂ y₂)).1,
      (IsCofiltered.minToLeft ((Φ.over q).fiber.elementsMk W₁ y₁)
        ((Φ.over q).fiber.elementsMk W₂ y₂)).2,
      (IsCofiltered.minToRight ((Φ.over q).fiber.elementsMk W₁ y₁)
        ((Φ.over q).fiber.elementsMk W₂ y₂)).2⟩
  rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply, toPresheafModuleFiber_w]
  refine (moduleStalkOverAddEquiv_toPresheafFiber_smul Φ q O M W y _ _).trans ?_
  congr 1
  · exact (ringStalkOverEquiv_symm_toPresheafFiber Φ q O W y _).symm
  · exact (moduleStalkOverAddEquiv_moduleStalkGerm Φ q O M W y _).symm

/-- **Stacks 04H2 for a sheaf of modules.** The stalk at `Φ.over q` of the restriction of a sheaf
of `O`-modules `M` to the localized site, viewed as a module over the stalk of `O` at `Φ` through
`Stacks.ringStalkOverEquiv`, is the stalk of `M` at `Φ`. -/
def moduleStalkOverIso (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    (ModuleCat.restrictScalars (ringStalkOverEquiv Φ q O).toRingHom).obj
        (moduleStalk (Φ.over q) (O.over V)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M)) ≅
      moduleStalk Φ O M :=
  ModuleCat.isoMk (moduleStalkOverAddIso Φ q O M) (fun r => by
    ext n
    have h := moduleStalkOverAddEquiv_smul Φ q O M (ringStalkOverEquiv Φ q O r) n
    rw [RingEquiv.symm_apply_apply] at h
    exact h.symm)

/-- `Stacks.moduleStalkOverIso` takes the germ at a neighbourhood `(W, y)` of `Φ.over q` of a
section of the restriction of `M` over `W` to the germ at `Φ` of the same section of `M` over
`W.left`. -/
lemma moduleStalkOverIso_hom_moduleStalkGerm
    (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) (W : Over V)
    (y : (Φ.over q).fiber.obj W) (m : M.val.obj (op W.left)) :
    (moduleStalkOverIso Φ q O M).hom
        (moduleStalkGerm (Φ.over q) (O.over V)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) W y m) =
      moduleStalkGerm Φ O M W.left y.val m :=
  moduleStalkOverAddEquiv_moduleStalkGerm Φ q O M W y m

/-- **Stacks 04H2 for sheaves of modules.** Restricting a sheaf of `O`-modules to the localized
site `C/V`, taking its stalk at the point `Φ.over q` and viewing it as a module over the stalk of
`O` at `Φ` through `Stacks.ringStalkOverEquiv` is the stalk functor at `Φ`. -/
def sheafModuleFiberOverIso :
    SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V ⋙
        sheafModuleFiberOfCommRing (Φ.over q) (O.over V) ⋙
          ModuleCat.restrictScalars (ringStalkOverEquiv Φ q O).toRingHom ≅
      sheafModuleFiberOfCommRing Φ O :=
  NatIso.ofComponents (moduleStalkOverIso Φ q O) (fun {M N} f => by
    ext n
    obtain ⟨W, y, m, rfl⟩ := toPresheafModuleFiber_jointly_surjective (Φ.over q)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M).val n
    change (moduleStalkOverIso Φ q O N).hom
        ((sheafModuleFiberOfCommRing (Φ.over q) (O.over V)).map
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).map f)
          (moduleStalkGerm (Φ.over q) (O.over V) _ W y m)) =
      (sheafModuleFiberOfCommRing Φ O).map f ((moduleStalkOverIso Φ q O M).hom
        (moduleStalkGerm (Φ.over q) (O.over V) _ W y m))
    have h := moduleStalkGerm_naturality (Φ.over q) (O.over V)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).map f) W y m
    exact (congrArg (moduleStalkOverIso Φ q O N).hom h).trans
      ((moduleStalkOverIso_hom_moduleStalkGerm Φ q O N W y _).trans
        ((moduleStalkGerm_naturality Φ O f W.left y.val m).symm.trans
          (congrArg ((sheafModuleFiberOfCommRing Φ O).map f)
            (moduleStalkOverIso_hom_moduleStalkGerm Φ q O M W y m).symm))))

/-- `Stacks.sheafModuleFiberOverIso` takes the germ at a neighbourhood `(W, y)` of `Φ.over q` of
a section of the restriction of `M` over `W` to the germ at `Φ` of the same section of `M` over
`W.left`. -/
lemma sheafModuleFiberOverIso_hom_app_moduleStalkGerm
    (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) (W : Over V)
    (y : (Φ.over q).fiber.obj W) (m : M.val.obj (op W.left)) :
    (sheafModuleFiberOverIso Φ q O).hom.app M
        (moduleStalkGerm (Φ.over q) (O.over V)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).obj M) W y m) =
      moduleStalkGerm Φ O M W.left y.val m :=
  moduleStalkOverIso_hom_moduleStalkGerm Φ q O M W y m

end Module

end Stacks
