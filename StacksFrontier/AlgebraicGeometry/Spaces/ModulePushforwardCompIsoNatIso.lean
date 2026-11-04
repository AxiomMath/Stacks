module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The composition comparison for direct images of modules, without transports

`AlgebraicGeometry.Space.modulePushforwardCompIso` is the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of
Stacks 03LU for direct images of `𝒪`-modules along morphisms of algebraic spaces.  Its
definition contains two transports along equalities of functors,
`AlgebraicGeometry.Space.modulePushforward_comp_eq` and
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`.  This file replaces both of
them by componentwise natural isomorphisms, after which the comparison can be decomposed one
factor at a time, and reads the decomposition on underlying sheaves of sets: the comparison is
the geometric comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2,
part (3).

## Main results

* `CategoryTheory.Functor.eqToIso_comp_of_eqToIso`: the transport of a composite of functors
  along equalities of its two factors is the two transports, whiskered.
* `AlgebraicGeometry.Space.modulePushforwardCompNatIso`: the identification
  `modulePushforward_comp_eq` as a componentwise natural isomorphism, and
  `AlgebraicGeometry.Space.eqToIso_modulePushforward_comp_eq`, its agreement with the transport.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_natIso`: the comparison of direct images
  with both of its transports replaced by componentwise natural isomorphisms, and
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq_natIso`, its component
  decomposed into the four factors.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply`: the
  comparison of direct images acts on a section by the geometric comparison of Stacks 03G2,
  part (3).

## Implementation notes

The underlying sheaf of sets of the iterated direct image has three spellings, two module-side
ones and the geometric one; all three are definitionally equal, but only the geometric one is a
common normal form, so every step of the assembly mentions it and applies the identities and
composition laws with explicit arguments.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (ofSheafHom hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_ofSheafHom)

universe u

namespace CategoryTheory.Functor

universe cv₀ cv₁ cv₂ cu₀ cu₁ cu₂

variable {A₀ : Type cu₀} {A₁ : Type cu₁} {A₂ : Type cu₂}
  [Category.{cv₀} A₀] [Category.{cv₁} A₁] [Category.{cv₂} A₂]

/-- **The transport of a composite of functors along equalities of its two factors is the two
transports, whiskered** — and if each factor's transport is already known to be a given
isomorphism, the composite's transport is those two isomorphisms, whiskered. -/
theorem eqToIso_comp_of_eqToIso {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {hp : p = p'} {hq : q = q'}
    {P : p ≅ p'} {Q : q ≅ q'} (hP : eqToIso hp = P) (hQ : eqToIso hq = Q)
    (h : p' ⋙ q' = p ⋙ q) :
    eqToIso h = isoWhiskerRight P.symm q' ≪≫ isoWhiskerLeft p Q.symm := by
  subst hP
  subst hQ
  subst hp
  subst hq
  obtain rfl : h = rfl := rfl
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The composition comparison for direct images is the geometric one -/

/-- A functor sends a composite to `r` when it sends the two factors to `p` and `q` with
`p ≫ q = r`. -/
private theorem map_comp_eq_of_map_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {W X Y : C} {a : W ⟶ X} {b : X ⟶ Y} {p : G.obj W ⟶ G.obj X} {q : G.obj X ⟶ G.obj Y}
    {r : G.obj W ⟶ G.obj Y} (ha : G.map a = p) (hb : G.map b = q) (hr : p ≫ q = r) :
    G.map (a ≫ b) = r :=
  (G.map_comp _ _).trans ((congrArg₂ (fun p q ↦ p ≫ q) ha hb).trans hr)

/-- The identification `AlgebraicGeometry.Space.modulePushforward_comp_eq` of the two iterated
direct images of modules, as a componentwise natural isomorphism: the comparison
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward` whiskered on each side. -/
noncomputable def modulePushforwardCompNatIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS g).pushforwardModules :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS f).symm
      (modulePushforward B S hS g) ≪≫
    Functor.isoWhiskerLeft (smallEtaleRingedToposHom B S hS f).pushforwardModules
      (pushforwardModulesIsoModulePushforward B S hS g).symm

/-- Both sides of `AlgebraicGeometry.Space.modulePushforward_comp_eq` have the iterated direct
image of sheaves of sets as their underlying sheaf, and the natural isomorphism above is the
identity there, read in the geometric spelling of that sheaf. -/
theorem moduleSheafFunctor_map_modulePushforwardCompNatIso_hom_app' (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforwardCompNatIso B S hS f g).hom.app F) =
      𝟙 ((smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) := by
  refine Eq.trans (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
    (NatTrans.comp_app
      (Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS f).symm
        (modulePushforward B S hS g)).hom
      (Functor.isoWhiskerLeft (smallEtaleRingedToposHom B S hS f).pushforwardModules
        (pushforwardModulesIsoModulePushforward B S hS g).symm).hom F)) ?_
  refine map_comp_eq_of_map_eq _ ?_ ?_ (Category.comp_id _)
  · refine Eq.trans (moduleSheafFunctor_map_modulePushforward_map_geometric B S hS g
      ((pushforwardModulesIsoModulePushforward B S hS f).inv.app F)) ?_
    refine Eq.trans (congrArg (smallToposMorphismTypeU B S hS g).pushforward.map
      (moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_inv_app B S hS f F)) ?_
    exact (smallToposMorphismTypeU B S hS g).pushforward.map_id _
  · exact moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_inv_app B S hS g
      ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj F)

/-- **The transport along `AlgebraicGeometry.Space.modulePushforward_comp_eq` is
`AlgebraicGeometry.Space.modulePushforwardCompNatIso`.** -/
theorem eqToIso_modulePushforward_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    eqToIso (modulePushforward_comp_eq B S hS f g) = modulePushforwardCompNatIso B S hS f g :=
  Functor.eqToIso_comp_of_eqToIso
    (eqToIso_pushforwardModules_eq_modulePushforward B S hS f)
    (eqToIso_pushforwardModules_eq_modulePushforward B S hS g)
    (modulePushforward_comp_eq B S hS f g)

/-- **The comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of Stacks 03LU, with no `eqToIso` factor.**  The
two transports along equalities of functors in the definition of
`AlgebraicGeometry.Space.modulePushforwardCompIso` are the two componentwise natural
isomorphisms `AlgebraicGeometry.Space.modulePushforwardCompNatIso` and
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`. -/
theorem modulePushforwardCompIso_eq_natIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso B S hS f g =
      modulePushforwardCompNatIso B S hS f g ≪≫
        (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g ≪≫
        pushforwardModulesIsoModulePushforward B S hS (f ≫ g) :=
  congrArg₂ (fun (a : modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
        (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
          (smallEtaleRingedToposHom B S hS g).pushforwardModules)
      (d : (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules ≅
        modulePushforward B S hS (f ≫ g)) ↦
      a ≪≫ (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g ≪≫ d)
    (eqToIso_modulePushforward_comp_eq B S hS f g)
    (eqToIso_pushforwardModules_eq_modulePushforward B S hS (f ≫ g))

/-- The component at `F` of the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of Stacks 03LU, decomposed into
its four factors: the components of `AlgebraicGeometry.Space.modulePushforwardCompNatIso`, of the
inverse of `RingedToposHom.pushforwardModulesCompIso`, of
`AlgebraicGeometry.Space.pushforwardModulesCompTransport` and of
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`. -/
theorem modulePushforwardCompIso_hom_app_eq_natIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardCompIso B S hS f g).hom.app F =
      (modulePushforwardCompNatIso B S hS f g).hom.app F ≫
        ((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g)).inv.app F ≫
          ((pushforwardModulesCompTransport B S hS f g).hom.app F ≫
            (pushforwardModulesIsoModulePushforward B S hS (f ≫ g)).hom.app F)) := by
  rw [modulePushforwardCompIso_eq_natIso B S hS f g]
  rfl

/-- The last two factors of `AlgebraicGeometry.Space.modulePushforwardCompIso`, on underlying
sheaves of sets: the geometric comparison, the fourth factor being the identity. -/
private theorem moduleSheafFunctor_map_modulePushforwardCompIso_tail₂ (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((pushforwardModulesCompTransport B S hS f g).hom.app F ≫
          (pushforwardModulesIsoModulePushforward B S hS (f ≫ g)).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  map_comp_eq_of_map_eq _
    (moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app B S hS f g F)
    (moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_hom_app B S hS (f ≫ g) F)
    (Category.comp_id _)

/-- The last three factors of `AlgebraicGeometry.Space.modulePushforwardCompIso`, on underlying
sheaves of sets. -/
private theorem moduleSheafFunctor_map_modulePushforwardCompIso_tail₁ (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g)).inv.app F ≫
          ((pushforwardModulesCompTransport B S hS f g).hom.app F ≫
            (pushforwardModulesIsoModulePushforward B S hS (f ≫ g)).hom.app F)) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  map_comp_eq_of_map_eq _ (moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app B S hS f g F)
    (moduleSheafFunctor_map_modulePushforwardCompIso_tail₂ B S hS f g F) (Category.id_comp _)

/-- **Stacks 03LU, the composition comparison for direct images read on a section.**  For a
section of the iterated direct image of `F` over an object `V` of the small étale site of `Z`,
the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` acts by the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3). -/
theorem moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s : ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
      ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F)).obj.obj V) :
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforwardCompIso B S hS f g).hom.app F)).hom.app V s =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)).hom.app V s :=
  have key : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforwardCompIso B S hS f g).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) := by
    refine Eq.trans (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
      (modulePushforwardCompIso_hom_app_eq_natIso B S hS f g F)) ?_
    refine map_comp_eq_of_map_eq _
      (moduleSheafFunctor_map_modulePushforwardCompNatIso_hom_app' B S hS f g F)
      (moduleSheafFunctor_map_modulePushforwardCompIso_tail₁ B S hS f g F) ?_
    exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS f g).hom.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
  congrArg (fun m ↦ m.hom.app V s) key

end AlgebraicGeometry.Space

end
