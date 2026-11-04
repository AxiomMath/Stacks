module

public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointFiberStalk
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The fibre of a sheaf of modules at a point of the site of opens is its stalk

Let `X` be a topological space, `x : X` and `O` a sheaf of rings on `X`. The fibre at the point
`Opens.pointGrothendieckTopology x` of a presheaf of abelian groups is its stalk at `x`, and the
same holds for the sheaf of rings `O`; this is `Opens.pointFiberStalkIso`. This file upgrades the
first identification to one of *modules*: it is semilinear over the second, so the fibre of a
sheaf of `O`-modules is the stalk module with its scalars restricted along the comparison map of
rings.

## Main definitions

* `Opens.moduleFiberStalkHom`: the comparison map from the fibre of a sheaf of modules at the
  point attached to `x` to its stalk at `x`, as a map of modules over the fibre of `O`.
* `Opens.moduleFiberStalkIso` and `Opens.moduleFiberStalkFunctorIso`: that comparison map is an
  isomorphism, objectwise and as an isomorphism of functors.
* `Opens.commRingFiberStalkHom` and `Opens.moduleFiberStalkFunctorIsoOfCommRing`: the same
  isomorphism for sheaves of modules over the ring sheaf of a sheaf of commutative rings `O`,
  with the scalars read over the `CommRingCat`-valued fibre of `O`.

## Main results

* `Opens.pointFiberStalkHom_smul`: the comparison map between the fibre and the stalk of a
  presheaf of modules is semilinear over the comparison map between the fibre and the stalk of
  the presheaf of rings. This is the only computation in the file; both comparison maps are
  determined by their effect on germs, and on germs the statement is the compatibility of the
  two scalar actions with the germ maps.
* `Opens.commRingFiberStalkHom_comp_commStalkIso`: the comparison map of
  `Opens.commRingFiberStalkHom` becomes `Opens.pointFiberStalkHom` once the `RingCat`-valued
  stalk of a sheaf of commutative rings is identified with its `CommRingCat`-valued one.
* `Opens.ringStalkMap_comp_commStalkIso`: that identification of the two stalks is natural in
  the presheaf of commutative rings.

## Implementation notes

The single universe `u` carries the space, the rings and the module sections together. It is
forced rather than chosen: Mathlib's module structure on the stalk of a presheaf of modules is
stated for `X : TopCat.{u}`, `R : X.Presheaf RingCat.{u}` and `M : PresheafOfModules.{u} R`, so
`AlgebraicGeometry.SheafOfModules.stalkFunctor` exists at no other combination.

Both the fibre module and the stalk module have, as underlying abelian group, the fibre
respectively the stalk of the underlying presheaf of abelian groups —
`Stacks.sheafModuleFiberCompForget₂` and
`AlgebraicGeometry.SheafOfModules.stalkFunctorCompForget₂` are both `Iso.refl`. So the comparison
map of abelian groups needs no transport, and the whole content is scalar compatibility; that the
comparison map is an isomorphism and that it is natural are then reflected along
`forget₂ (ModuleCat _) AddCommGrpCat`, which is faithful and reflects isomorphisms.

## References

* [Stacks Project, Section 7.32 (Tag 00Y3)](https://stacks.math.columbia.edu/tag/00Y3)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Opens

variable {X : TopCat.{u}} (x : X)
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-! ### Semilinearity of the comparison map between the fibre and the stalk -/

/-- `Opens.toPresheafFiber_pointFiberStalkHom` read on elements, for a presheaf of rings. -/
theorem pointFiberStalkHom_toPresheafFiber (F : X.Presheaf RingCat.{u}) (U : Opens X)
    (hU : (pointGrothendieckTopology x).fiber.obj U) (a : F.obj (op U)) :
    pointFiberStalkHom x F ((pointGrothendieckTopology x).toPresheafFiber U hU F a) =
      TopCat.Presheaf.germ F U x hU.down.down a :=
  congrArg (fun φ => (ConcreteCategory.hom φ) a)
    (toPresheafFiber_pointFiberStalkHom x F U hU)

/-- `Opens.toPresheafFiber_pointFiberStalkHom` read on the germ map of a presheaf of modules:
the comparison map carries `Stacks.toPresheafModuleFiber` to the germ map at `x`. -/
theorem pointFiberStalkHom_toPresheafModuleFiber (M : PresheafOfModules.{u} O.obj) (U : Opens X)
    (hU : (pointGrothendieckTopology x).fiber.obj U) (s : M.obj (op U)) :
    pointFiberStalkHom x M.presheaf
        (Stacks.toPresheafModuleFiber (pointGrothendieckTopology x) M U hU s) =
      TopCat.Presheaf.germ M.presheaf U x hU.down.down s :=
  congrArg (fun φ => (ConcreteCategory.hom φ) s)
    (toPresheafFiber_pointFiberStalkHom x M.presheaf U hU)

/-- **The comparison map between the fibre and the stalk of a presheaf of modules is
semilinear.** It carries the action of the fibre of the presheaf of rings to the action of the
stalk of the presheaf of rings along the comparison map of rings.

Every element of the fibre is the image of a section over some open neighbourhood of `x`, and two
such sections may be restricted to a common neighbourhood, so it suffices to treat a scalar and a
section over one open neighbourhood; there the statement is the compatibility of both scalar
actions with the germ maps. -/
theorem pointFiberStalkHom_smul (M : PresheafOfModules.{u} O.obj)
    (r : ((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj)
    (m : (Stacks.presheafModuleFiber (pointGrothendieckTopology x) O.obj).obj M) :
    pointFiberStalkHom x M.presheaf (r • m) =
      pointFiberStalkHom x O.obj r • pointFiberStalkHom x M.presheaf m := by
  have key : ∀ (W : Opens X) (hW : (pointGrothendieckTopology x).fiber.obj W)
      (a : O.obj.obj (op W)) (s : M.obj (op W)),
      pointFiberStalkHom x M.presheaf
          ((pointGrothendieckTopology x).toPresheafFiber W hW O.obj a •
            Stacks.toPresheafModuleFiber (pointGrothendieckTopology x) M W hW s) =
        pointFiberStalkHom x O.obj
            ((pointGrothendieckTopology x).toPresheafFiber W hW O.obj a) •
          pointFiberStalkHom x M.presheaf
            (Stacks.toPresheafModuleFiber (pointGrothendieckTopology x) M W hW s) := by
    intro W hW a s
    rw [← Stacks.toPresheafModuleFiber_smul (pointGrothendieckTopology x) M W hW a s,
      pointFiberStalkHom_toPresheafModuleFiber, pointFiberStalkHom_toPresheafModuleFiber,
      pointFiberStalkHom_toPresheafFiber]
    exact PresheafOfModules.germ_ringCat_smul M x W hW.down.down a s
  obtain ⟨U, hU, a, ha⟩ :=
    (pointGrothendieckTopology x).toPresheafFiber_jointly_surjective (P := O.obj) r
  obtain ⟨V, hV, s, hs⟩ :=
    Stacks.toPresheafModuleFiber_jointly_surjective (pointGrothendieckTopology x) M m
  have hW : (pointGrothendieckTopology x).fiber.obj (U ⊓ V) :=
    ⟨⟨⟨hU.down.down, hV.down.down⟩⟩⟩
  have ha' : (pointGrothendieckTopology x).toPresheafFiber (U ⊓ V) hW O.obj
      (O.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) = r := by
    rw [(pointGrothendieckTopology x).toPresheafFiber_w_apply]
    exact ha
  have hs' : Stacks.toPresheafModuleFiber (pointGrothendieckTopology x) M (U ⊓ V) hW
      (M.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = m := by
    rw [← Stacks.toPresheafModuleFiber_w (pointGrothendieckTopology x) M
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) hW s]
    exact hs
  rw [← ha', ← hs']
  exact key _ hW _ _

/-! ### The comparison map of modules -/

/-- **The comparison map from the fibre of a sheaf of modules at the point attached to `x` to its
stalk at `x`**, as a map of modules over the fibre of the sheaf of rings. Its underlying map of
abelian groups is `Opens.pointFiberStalkHom`. -/
def moduleFiberStalkHom (M : _root_.SheafOfModules.{u} O) :
    (Stacks.sheafModuleFiber (pointGrothendieckTopology x) O).obj M ⟶
      (ModuleCat.restrictScalars.{u} (pointFiberStalkHom x O.obj).hom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj M) :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u}
      (((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj))
    { toFun := fun m => pointFiberStalkHom x M.val.presheaf m
      map_add' := fun m m' => map_add _ m m'
      map_smul' := fun r m => pointFiberStalkHom_smul x O M.val r m }

/-- On underlying abelian groups the comparison map of modules is
`Opens.pointFiberStalkHom`. -/
theorem forget₂_map_moduleFiberStalkHom (M : _root_.SheafOfModules.{u} O) :
    (forget₂ (ModuleCat.{u}
          (((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj))
        AddCommGrpCat.{u}).map (moduleFiberStalkHom x O M) =
      pointFiberStalkHom x M.val.presheaf := by
  ext m
  rfl

/-- The comparison map from the fibre of a sheaf of modules at the point attached to `x` to its
stalk at `x` is an isomorphism. -/
instance isIso_moduleFiberStalkHom (M : _root_.SheafOfModules.{u} O) :
    IsIso (moduleFiberStalkHom x O M) := by
  rw [← isIso_iff_of_reflects_iso _ (forget₂ (ModuleCat.{u}
      (((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj))
      AddCommGrpCat.{u}), forget₂_map_moduleFiberStalkHom]
  exact (pointFiberStalkIso x M.val.presheaf).isIso_hom

/-- **The fibre of a sheaf of modules at the point of the site of opens attached to `x` is its
stalk at `x`**, as a module over the fibre of the sheaf of rings with scalars restricted along
`Opens.pointFiberStalkHom`. -/
def moduleFiberStalkIso (M : _root_.SheafOfModules.{u} O) :
    (Stacks.sheafModuleFiber (pointGrothendieckTopology x) O).obj M ≅
      (ModuleCat.restrictScalars.{u} (pointFiberStalkHom x O.obj).hom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj M) :=
  asIso (moduleFiberStalkHom x O M)

/-- On underlying abelian groups the fibre of a morphism of sheaves of modules is the fibre of
the underlying morphism of presheaves of abelian groups. -/
theorem forget₂_map_sheafModuleFiber_map {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    (forget₂ (ModuleCat.{u}
          (((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj))
        AddCommGrpCat.{u}).map ((Stacks.sheafModuleFiber (pointGrothendieckTopology x) O).map f) =
      (pointGrothendieckTopology x).presheafFiber.map
        ((PresheafOfModules.toPresheaf O.obj).map f.val) := by
  ext m
  rfl

/-- **The fibre of a sheaf of modules at the point of the site of opens attached to `x` is its
stalk at `x`, naturally in the sheaf of modules.** -/
def moduleFiberStalkFunctorIso :
    Stacks.sheafModuleFiber (pointGrothendieckTopology x) O ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor O x ⋙
        ModuleCat.restrictScalars.{u} (pointFiberStalkHom x O.obj).hom :=
  NatIso.ofComponents (moduleFiberStalkIso x O) fun {M N} f => by
    apply (forget₂ (ModuleCat.{u}
      (((pointGrothendieckTopology x).presheafFiber (A := RingCat.{u})).obj O.obj))
      AddCommGrpCat.{u}).map_injective
    simp only [Functor.map_comp, moduleFiberStalkIso, asIso_hom,
      forget₂_map_moduleFiberStalkHom, forget₂_map_sheafModuleFiber_map]
    exact pointFiberStalkIso_natural x ((PresheafOfModules.toPresheaf O.obj).map f.val)

/-! ### Comparing the two stalks of a sheaf of commutative rings -/

/-- **The germ map into the `RingCat`-valued stalk of a presheaf of commutative rings is the
germ map into its `CommRingCat`-valued stalk**, read through the comparison isomorphism of the
two stalks. Both stalks are the same filtered colimit, computed before and after the forgetful
functor `CommRingCat ⥤ RingCat`, which preserves it. -/
theorem germ_commStalkIso_hom (F : X.Presheaf CommRingCat.{u}) (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (C := RingCat.{u}) (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx ≫
        (SemilinearStalk.commStalkIso F x).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (F.germ U x hx) :=
  ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

/-- **The identification of the `RingCat`-valued stalk of a presheaf of commutative rings with
its `CommRingCat`-valued stalk is natural in the presheaf.** Both sides are determined by their
effect on germs, where the statement is that a morphism of presheaves commutes with the germ
maps. -/
theorem ringStalkMap_comp_commStalkIso {F G : X.Presheaf CommRingCat.{u}} (φ : F ⟶ G) :
    SemilinearStalk.ringStalkMap
          (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u})) x ≫
        (SemilinearStalk.commStalkIso G x).hom =
      (SemilinearStalk.commStalkIso F x).hom ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  have h1 : TopCat.Presheaf.germ (C := RingCat.{u})
        (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hU ≫
      SemilinearStalk.ringStalkMap
        (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u})) x =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (φ.app (op U)) ≫
        TopCat.Presheaf.germ (C := RingCat.{u})
          (G ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hU :=
    TopCat.Presheaf.stalkFunctor_map_germ U x hU _
  have h2 : F.germ U x hU ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ =
      φ.app (op U) ≫ G.germ U x hU := TopCat.Presheaf.stalkFunctor_map_germ U x hU φ
  refine ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (SemilinearStalk.commStalkIso G x).hom) h1).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => (forget₂ CommRingCat.{u} RingCat.{u}).map (φ.app (op U)) ≫ t)
          (germ_commStalkIso_hom x G U hU))))).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
    (((congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map h2.symm).trans
      ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _)).trans
      (congrArg (fun t => t ≫ (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ))
        (germ_commStalkIso_hom x F U hU).symm))

/-- **The fibre-to-stalk comparison map of a presheaf of commutative rings is compatible with
the identification of the two stalks.** Both sides are determined by their effect on the
canonical maps out of the sections over an open neighbourhood of `x`, where both are the germ
map. -/
theorem pointFiberStalkHom_commStalkIso (F : X.Presheaf CommRingCat.{u}) :
    pointFiberStalkHom x (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≫
        (SemilinearStalk.commStalkIso F x).hom =
      (Stacks.commRingPresheafFiberIso (pointGrothendieckTopology x) F).hom ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (pointFiberStalkHom x F) := by
  refine (pointGrothendieckTopology x).presheafFiber_hom_ext fun U hU => ?_
  refine (toPresheafFiber_pointFiberStalkHom_assoc x _ U hU _).trans ?_
  refine (germ_commStalkIso_hom x F U hU.down.down).trans ?_
  refine (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    (toPresheafFiber_pointFiberStalkHom x F U hU).symm).trans ?_
  refine ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).trans ?_
  exact (GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app_assoc
    (pointGrothendieckTopology x) (forget₂ CommRingCat.{u} RingCat.{u}) U hU F _).symm

/-! ### Sheaves of modules over a sheaf of commutative rings -/

section CommRing

variable (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **The comparison map of rings from the `CommRingCat`-valued fibre of a sheaf of commutative
rings at the point attached to `x` to the stalk of its underlying sheaf of rings at `x`.** -/
def commRingFiberStalkHom :
    (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (((pointGrothendieckTopology x).presheafFiber (A := CommRingCat.{u})).obj O.obj) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{u}) (Stacks.commRingSheafToRingSheaf O).obj x :=
  (Stacks.commRingSheafFiberIso (pointGrothendieckTopology x) O).inv ≫
    pointFiberStalkHom x (Stacks.commRingSheafToRingSheaf O).obj

/-- **The fibre of a sheaf of modules over the ring sheaf of a sheaf of commutative rings `O` is
its stalk**, read over the `CommRingCat`-valued fibre of `O`. This is
`Opens.moduleFiberStalkFunctorIso` with the two restrictions of scalars — the one built into
`Stacks.sheafModuleFiberOfCommRing` and the one comparing the fibre with the stalk — composed
into the single ring map `Opens.commRingFiberStalkHom`. -/
def moduleFiberStalkFunctorIsoOfCommRing :
    Stacks.sheafModuleFiberOfCommRing (pointGrothendieckTopology x) O ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.commRingSheafToRingSheaf O) x ⋙
        ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x O).hom :=
  Functor.isoWhiskerRight (moduleFiberStalkFunctorIso x (Stacks.commRingSheafToRingSheaf O))
      (ModuleCat.restrictScalars.{u}
        (Stacks.commRingSheafFiberIso (pointGrothendieckTopology x) O).inv.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.commRingSheafToRingSheaf O) x)
      (ModuleCat.restrictScalarsComp'.{u}
        (Stacks.commRingSheafFiberIso (pointGrothendieckTopology x) O).inv.hom
        (pointFiberStalkHom x (Stacks.commRingSheafToRingSheaf O).obj).hom
        (commRingFiberStalkHom x O).hom rfl).symm

/-- **`Opens.commRingFiberStalkHom` is `Opens.pointFiberStalkHom`**, once the `RingCat`-valued
stalk of the sheaf of commutative rings is identified with its `CommRingCat`-valued one. The two
restrictions of scalars built into `Opens.commRingFiberStalkHom` cancel against the two
identifications of the `RingCat`-valued fibre and stalk with the `CommRingCat`-valued ones. -/
theorem commRingFiberStalkHom_comp_commStalkIso :
    commRingFiberStalkHom x O ≫ (SemilinearStalk.commStalkIso O.obj x).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (pointFiberStalkHom x O.obj) :=
  calc commRingFiberStalkHom x O ≫ (SemilinearStalk.commStalkIso O.obj x).hom
      = (Stacks.commRingPresheafFiberIso (pointGrothendieckTopology x) O.obj).inv ≫
          (pointFiberStalkHom x (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≫
            (SemilinearStalk.commStalkIso O.obj x).hom) := Category.assoc _ _ _
    _ = (Stacks.commRingPresheafFiberIso (pointGrothendieckTopology x) O.obj).inv ≫
          ((Stacks.commRingPresheafFiberIso (pointGrothendieckTopology x) O.obj).hom ≫
            (forget₂ CommRingCat.{u} RingCat.{u}).map (pointFiberStalkHom x O.obj)) :=
        congrArg _ (pointFiberStalkHom_commStalkIso x O.obj)
    _ = (forget₂ CommRingCat.{u} RingCat.{u}).map (pointFiberStalkHom x O.obj) :=
        (Stacks.commRingPresheafFiberIso (pointGrothendieckTopology x) O.obj).inv_hom_id_assoc _

end CommRing

end Opens

end
