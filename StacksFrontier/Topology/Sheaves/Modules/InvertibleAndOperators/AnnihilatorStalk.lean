module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.Annihilator

/-!
# The stalk of the annihilator of a sheaf of modules

Let `F` be a sheaf of modules of finite type on a ringed space `X` and let `x` be a point. The
germs at `x` of the local sections of the annihilator `Ann(F)` are then exactly the elements of
the local ring `O_{X,x}` that annihilate the stalk `F_x`. The inclusion that holds for every `F`
is `Stacks.SheafOfModules.stalk_annihilatorSheaf_le_annihilator_stalk` (Tag 0H2I); the content
here is the reverse inclusion, which needs `F` of finite type.

## Main definitions

* `Stacks.SheafOfModules.internalSheafHom`: the internal hom of two `O_X`-modules on a
  topological space, packaged as a `SheafHom` (Stacks 01CO) built from the internal-hom presheaf
  of Stacks 03EM.

## Main results

* `Stacks.SheafOfModules.annihilatorSheaf_stalk`: the stalk of the annihilator sheaf of a sheaf
  of modules of finite type is the annihilator of its stalk.

## Implementation notes

The stalk of the annihilator subsheaf is described, as in Tag 0H2I, as the set of germs of its
local sections inside the stalk of the structure sheaf; this avoids choosing a model for the
stalk of a submodule sheaf.

The reverse inclusion runs as follows. An element of the annihilator of `F_x` is the germ of a
section `s` of `O_X` over some `U`. Its scalar action `Stacks.SheafOfModules.scalarAction` is a
section of the internal endomorphism sheaf over `U`, and the germ of that section is killed by
the canonical map from the stalk of the internal hom to the module of endomorphisms of `F_x`,
because the canonical map evaluates it as multiplication by the germ of `s`. For `F` of finite
type that canonical map is injective
(`Stacks.SheafOfModules.SheafHomStalk.injective_sheafHomStalkLinearMap`), so the germ of the
scalar action of `s` vanishes; hence `s` restricts to a section whose scalar action is zero on
some smaller neighbourhood, and such a section lies in the annihilator.

Finite type is used only through that injectivity. Everything else is a germ chase, carried out
in the `germAt`/`appAt` vocabulary of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk`. The chase is written with
`congrArg` and `Eq.trans` rather than `rw`, because the goals are built across the semireducible
definitions `appAt` and `structureSheafRing` and a rewrite is not type-correct at the matching
transparency. For the same reason the `germAt` vocabulary is applied with its sheaf of
commutative rings named, as `germAt (Rc := X.sheaf)`: the index of `F` is `structureSheafRing X`,
whose underlying presheaf is a projection rather than a `sheafCompose`, so the elaborator cannot
solve `structureSheaf ?Rc` against it.

The space, ring and module universes agree, as `structureSheafRing` and the
common-universe `SheafHom` interface require.

## References

* [Stacks Project, Tag 0H2J](https://stacks.math.columbia.edu/tag/0H2J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

open SheafHomStalk

attribute [local implicit_reducible] structureSheafRing PresheafOfModules.presheaf TopCat.Sheaf
  SheafOfModules.unit PresheafOfModules.unit

-- `structureSheafRing X` reduces to `X.presheaf ⋙ forget₂ _ _`, while the `SheafHom`/`germAt`
-- interface used below is stated at `structureSheaf X.sheaf`, that is at
-- `(sheafCompose _ (forget₂ _ _)).obj X.sheaf`; unfolding `sheafCompose` and `SheafedSpace.sheaf`
-- is what identifies the two.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- The internal hom of two sheaves of modules on a topological space, packaged as a `SheafHom`
(Stacks 01CO): its underlying sheaf is the internal-hom presheaf of Stacks 03EM. -/
@[ega "0 4.1.5" "special case"]
noncomputable def internalSheafHom {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (F G : SheafOfModules.{u} (structureSheaf Rc)) : SheafHom Rc F G where
  obj :=
    { val := internalHom Rc.obj F.val G.val
      isSheaf := internalHom_isSheaf Rc.obj F.val G.val G.isSheaf }
  sectionsEquiv U := by
    change ((restrFun Rc.obj U).obj F.val ⟶
      (restrFun Rc.obj U).obj G.val) ≃+ (F.over U ⟶ G.over U)
    let e : (F.over U ⟶ G.over U) ≃
        ((restrFun Rc.obj U).obj F.val ⟶ (restrFun Rc.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf Rc).over U)).homEquiv
        (X := F.over U) (Y := G.over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV m
    change ((homRestr Rc.obj F.val G.val (homOfLE hVU) s).app
      (op (Over.mk (homOfLE hWV)))) m = _
    rfl
  smul_natural := by
    intro U r s W hWU m
    change ((smulHom Rc.obj F.val G.val U r s).app
      (op (Over.mk (homOfLE hWU)))) m = _
    rfl

variable (X : RingedSpace.{u, u}) (F : SheafOfModules.{u} (structureSheafRing X))

/-- The canonical map on stalks, evaluated on the germ of a local homomorphism over `U` and the
germ of a local section over a smaller open `W`. This is
`Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap_germ` with the two opens allowed to
differ. -/
private lemma sheafHomStalkLinearMap_germ_le {G : SheafOfModules.{u} (structureSheafRing X)}
    (H : SheafHom X.sheaf F G) {x : X} {U W : Opens X} (hWU : W ≤ U) (hxU : x ∈ U)
    (hxW : x ∈ W) (s : H.obj.val.obj (op U)) (m : F.val.obj (op W)) :
    sheafHomStalkLinearMap H x (germAt H.obj U x hxU s) (germAt (Rc := X.sheaf) F W x hxW m)
      = germAt (Rc := X.sheaf) G W x hxW (appAt hWU (H.sectionsEquiv U s) m) := by
  change sheafHomStalkMap H x (germAt H.obj U x hxU s) (germAt (Rc := X.sheaf) F W x hxW m) = _
  rw [sheafHomStalkMap_germ H U hxU s, stalkLinearMap_apply,
    stalkMap_germ (H.sectionsEquiv U s) hxU hWU hxW m]

/-- The canonical map on stalks sends the germ of the scalar action of a section `s` of the
structure sheaf to multiplication by the germ of `s`. -/
private lemma sheafHomStalkLinearMap_germ_scalarAction (H : SheafHom X.sheaf F F) {x : X}
    {U W : Opens X} (hWU : W ≤ U) (hxU : x ∈ U) (hxW : x ∈ W)
    (s : X.sheaf.obj.obj (op U)) (m : F.val.obj (op W)) :
    sheafHomStalkLinearMap H x (germAt H.obj U x hxU ((scalarAction X F H).val.app (op U) s))
        (germAt (Rc := X.sheaf) F W x hxW m)
      = TopCat.Presheaf.germ X.sheaf.obj U x hxU s • germAt (Rc := X.sheaf) F W x hxW m :=
  (sheafHomStalkLinearMap_germ_le X F H hWU hxU hxW _ m).trans
    ((congrArg (germAt (Rc := X.sheaf) F W x hxW)
        (scalarAction_component X F H U W hWU s m)).trans
      ((germAt_smul (Rc := X.sheaf) F hxW _ m).trans
        (congrArg (· • germAt (Rc := X.sheaf) F W x hxW m)
          (TopCat.Presheaf.germ_res_apply X.sheaf.obj (homOfLE hWU) x hxW s))))

/-- The germ of a section over `W` is the germ of its restriction to `W ⊓ U`, for any open `U`
containing `x`. -/
private lemma germAt_eq_germAt_resLE_inf {W : Opens X} (U : Opens X) {x : X} (hxW : x ∈ W)
    (hxU : x ∈ U) (m : F.val.obj (op W)) :
    germAt (Rc := X.sheaf) F W x hxW m
      = germAt (Rc := X.sheaf) F (W ⊓ U) x (mem_inf hxW hxU)
          (resLE (Rc := X.sheaf) F inf_le_left m) :=
  (germAt_resLE (Rc := X.sheaf) F inf_le_left (mem_inf hxW hxU) m).symm

/-- For `F` of finite type, if the germ of `s` annihilates the stalk of `F`, then the germ of the
scalar action of `s` vanishes in the stalk of the internal endomorphism sheaf. -/
private lemma germAt_scalarAction_eq_zero [F.IsFiniteType] (H : SheafHom X.sheaf F F) {x : X}
    {U : Opens X} (hxU : x ∈ U) (s : X.sheaf.obj.obj (op U))
    (hs : TopCat.Presheaf.germ X.sheaf.obj U x hxU s ∈
      Module.annihilator (ringStalk X.sheaf x) (modStalk (Rc := X.sheaf) F x)) :
    germAt H.obj U x hxU ((scalarAction X F H).val.app (op U) s) = 0 := by
  refine injective_sheafHomStalkLinearMap H x ?_
  rw [map_zero]
  refine linearMap_ext fun W hxW m ↦ ?_
  rw [LinearMap.zero_apply, germAt_eq_germAt_resLE_inf X F U hxW hxU m,
    sheafHomStalkLinearMap_germ_scalarAction X F H (inf_le_right : W ⊓ U ≤ U) hxU
      (mem_inf hxW hxU) s (resLE (Rc := X.sheaf) F inf_le_left m)]
  exact Module.mem_annihilator.mp hs _

/-- A restricted section of the structure sheaf whose scalar action is zero lies in the
annihilator. -/
private lemma mem_annihilatorSheaf_of_scalarAction_eq_zero (H : SheafHom X.sheaf F F)
    {W U : Opens X} (iWU : W ⟶ U) (s : X.sheaf.obj.obj (op U))
    (hs : (scalarAction X F H).val.app (op W) ((structureSheafRing X).obj.map iWU.op s) = 0) :
    ((structureSheafRing X).obj.map iWU.op s) ∈ (annihilatorSheaf X F).toSubmodule.obj (op W) := by
  rw [mem_annihilatorSheaf_iff]
  intro V f m
  rw [show f = (homOfLE f.unop.le).op from Subsingleton.elim _ _,
    ← scalarAction_component X F H W V.unop f.unop.le _ m, hs, map_zero]
  exact zero_app_apply (N := F.over W) (P := F.over W) (op (Over.mk (homOfLE f.unop.le))) m

/-- **Stacks Project, Tag 0H2J.** For `F` of finite type, the germs at `x` of the local sections
of the annihilator sheaf of `F` are exactly the elements of the local ring `O_{X,x}` that
annihilate the stalk `F_x`. -/
@[stacks 0H2J]
theorem annihilatorSheaf_stalk [F.IsFiniteType] (x : X) :
    {r : TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x |
      ∃ (U : Opens X) (hx : x ∈ U) (s : (structureSheafRing X).obj.obj (op U)),
        s ∈ (annihilatorSheaf X F).toSubmodule.obj (op U) ∧
          TopCat.Presheaf.germ (C := CommRingCat.{u}) X.sheaf.obj U x hx s = r} =
      (Module.annihilator
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (show PresheafOfModules.{u}
              (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) from F.val).presheaf x) :
          Set (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro r ⟨U, hxU, s, hs, rfl⟩
    refine Module.mem_annihilator.mpr fun m ↦ ?_
    obtain ⟨V, hxV, t, rfl⟩ := exists_germ_eq (Rc := X.sheaf) F m
    have hxW : x ∈ V ⊓ U := mem_inf hxV hxU
    have h1 : TopCat.Presheaf.germ X.sheaf.obj U x hxU s
        = TopCat.Presheaf.germ X.sheaf.obj (V ⊓ U) x hxW
            (X.sheaf.obj.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op s) :=
      (TopCat.Presheaf.germ_res_apply X.sheaf.obj
        (homOfLE (inf_le_right : V ⊓ U ≤ U)) x hxW s).symm
    have h2 := germAt_eq_germAt_resLE_inf X F U hxV hxU t
    have h3 := (mem_annihilatorSheaf_iff X F (op U) s).mp hs (op (V ⊓ U))
      (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (resLE (Rc := X.sheaf) F inf_le_left t)
    exact (congrArg (· • germAt (Rc := X.sheaf) F V x hxV t) h1).trans
      ((congrArg (TopCat.Presheaf.germ X.sheaf.obj (V ⊓ U) x hxW
          (X.sheaf.obj.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op s) • ·) h2).trans
        ((germAt_smul (Rc := X.sheaf) F hxW _ (resLE (Rc := X.sheaf) F inf_le_left t)).symm.trans
          ((congrArg (germAt (Rc := X.sheaf) F (V ⊓ U) x hxW) h3).trans
            (germAt_zero (Rc := X.sheaf) F hxW))))
  · intro r hr
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
    obtain ⟨W, hxW, iWU, _iW0, hW⟩ :=
      TopCat.Presheaf.germ_eq (commVal (internalSheafHom X.sheaf F F).obj).presheaf x hxU hxU
        ((scalarAction X F (internalSheafHom X.sheaf F F)).val.app (op U) s) 0
        ((germAt_scalarAction_eq_zero X F (internalSheafHom X.sheaf F F) hxU s hr).trans
          (germAt_zero (internalSheafHom X.sheaf F F).obj hxU).symm)
    exact ⟨W, hxW, (structureSheafRing X).obj.map iWU.op s,
      mem_annihilatorSheaf_of_scalarAction_eq_zero X F (internalSheafHom X.sheaf F F) iWU s
        ((PresheafOfModules.naturality_apply
          (scalarAction X F (internalSheafHom X.sheaf F F)).val iWU.op s).trans
            (hW.trans (map_zero _))),
      TopCat.Presheaf.germ_res_apply X.sheaf.obj iWU x hxW s⟩

end Stacks.SheafOfModules
