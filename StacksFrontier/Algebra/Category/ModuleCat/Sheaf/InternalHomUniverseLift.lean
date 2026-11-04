module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# The internal Hom does not see a universe lift of the sections

Raising the universe of the sections of a sheaf of modules,
`SheafOfModules.uliftForPresentation`, changes neither variable of the internal Hom presheaf of
Stacks 03EM:

`𝓗om_O(ULift F, ULift G) ≅ 𝓗om_O(F, G)`.

A section of the left-hand side over `U` is a morphism of the restrictions of the lifted modules
to the slice at `U`, and such a morphism is `ULift.up ∘ − ∘ ULift.down` of a morphism of the
restrictions of `F` and `G`; both directions are componentwise, so neither needs a limit, a
colimit nor sheafification.

The lift is taken to `max u v`, which is the universe in which the internal Hom already has its
own sections, so that the two sides land in the same module universe: the internal Hom of modules
with sections in `m` has sections in `max u v m`, and so does the internal Hom of their lifts.

That is what the statement is for.  The internal Hom of sheaves of modules with sections in `m`
is a sheaf of modules with sections in `max u v m`, never in `m`, so a statement *about* internal
Homs — quasi-coherence of one, say, which is clause (6) of Stacks 03M1 — can only be assembled at
the module universe `max u v m`, where it does not apply to modules whose sections lie in `m`.
The isomorphism below transports it to those, the lift being invisible on both sides.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomUliftDown` and
  `Stacks.SheafOfModules.InternalHom.internalHomUliftUp`: the two directions on sections.
* `Stacks.SheafOfModules.InternalHom.internalHomUliftIso`: **the internal Hom of two universe
  lifts is the internal Hom of the modules themselves.**

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomUliftIso_hom_app` and
  `Stacks.SheafOfModules.InternalHom.internalHomUliftIso_inv_app`: on sections the isomorphism
  is `ULift.down` of the value at `ULift.up`, and `ULift.up` of the value at `ULift.down`.  This
  pins it down rather than merely asserting that some isomorphism exists.

## Implementation notes

The module structures on the sections of the internal Hom are supplied by `letI` from the bundled
`ModuleCat` objects, as in
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomHom`: instance search does not see them
through `CategoryTheory.PresheafOfModules.pushforward`, which is what `restrFun` is.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w m

namespace Stacks.SheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : GrothendieckTopology C} {hO : Presheaf.IsSheaf J (Oforget O)}

/-- The universe lift of a sheaf of modules to the universe `max u v` in which the internal Hom
has its sections, which is the lift the internal Hom cannot see. -/
noncomputable abbrev uliftSections
    (F : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) :
    _root_.SheafOfModules.{max u v m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w}) :=
  _root_.SheafOfModules.uliftForPresentation.{u, v, w, m, max u v} F

variable {F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})}

/-- A morphism between the restrictions to the slice at `U` of the universe lifts of two sheaves
of modules, read as a morphism between the restrictions of the modules themselves: apply it to
`ULift.up` of a section and take `ULift.down` of the value. -/
noncomputable def internalHomUliftDown (U : C)
    (α : (restrFun O U).obj (uliftSections F).val ⟶
      (restrFun O U).obj (uliftSections G).val) :
    (restrFun O U).obj F.val ⟶ (restrFun O U).obj G.val where
  app X :=
    letI : AddCommGroup (((restrFun O U).obj F.val).obj X) :=
      (((restrFun O U).obj F.val).obj X).isAddCommGroup
    letI : Module ((ORestr O U).obj X) (((restrFun O U).obj F.val).obj X) :=
      (((restrFun O U).obj F.val).obj X).isModule
    letI : AddCommGroup (((restrFun O U).obj G.val).obj X) :=
      (((restrFun O U).obj G.val).obj X).isAddCommGroup
    letI : Module ((ORestr O U).obj X) (((restrFun O U).obj G.val).obj X) :=
      (((restrFun O U).obj G.val).obj X).isModule
    ConcreteCategory.ofHom (C := ModuleCat ((ORestr O U).obj X))
      { toFun := fun x => ((α.app X).hom (ULift.up x)).down
        map_add' := fun x y => congrArg ULift.down
          (map_add (α.app X).hom (ULift.up x) (ULift.up y))
        map_smul' := fun r x => congrArg ULift.down
          (map_smul (α.app X).hom r (ULift.up x)) }
  naturality {_ _} f := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    congrArg ULift.down (PresheafOfModules.naturality_apply α f (ULift.up x))

/-- A morphism between the restrictions to the slice at `U` of two sheaves of modules, read as a
morphism between the restrictions of their universe lifts: apply it to `ULift.down` of a section
and take `ULift.up` of the value. -/
noncomputable def internalHomUliftUp (U : C)
    (α : (restrFun O U).obj F.val ⟶ (restrFun O U).obj G.val) :
    (restrFun O U).obj (uliftSections F).val ⟶
      (restrFun O U).obj (uliftSections G).val where
  app X :=
    letI : AddCommGroup (((restrFun O U).obj (uliftSections F).val).obj X) :=
      (((restrFun O U).obj (uliftSections F).val).obj X).isAddCommGroup
    letI : Module ((ORestr O U).obj X) (((restrFun O U).obj (uliftSections F).val).obj X) :=
      (((restrFun O U).obj (uliftSections F).val).obj X).isModule
    letI : AddCommGroup (((restrFun O U).obj (uliftSections G).val).obj X) :=
      (((restrFun O U).obj (uliftSections G).val).obj X).isAddCommGroup
    letI : Module ((ORestr O U).obj X) (((restrFun O U).obj (uliftSections G).val).obj X) :=
      (((restrFun O U).obj (uliftSections G).val).obj X).isModule
    ConcreteCategory.ofHom (C := ModuleCat ((ORestr O U).obj X))
      { toFun := fun x => ULift.up ((α.app X).hom x.down)
        map_add' := fun x y => congrArg ULift.up (map_add (α.app X).hom x.down y.down)
        map_smul' := fun r x => congrArg ULift.up ((α.app X).hom.map_smul r x.down) }
  naturality {_ _} f := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    congrArg ULift.up (PresheafOfModules.naturality_apply α f x.down)

/-- The comparison `𝓗om_O(ULift F, ULift G) ⟶ 𝓗om_O(F, G)`, which on sections is
`Stacks.SheafOfModules.InternalHom.internalHomUliftDown`. -/
noncomputable def internalHomUliftHomMap
    (F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) :
    internalHom O (uliftSections F).val (uliftSections G).val ⟶ internalHom O F.val G.val where
  app U :=
    letI : AddCommGroup
        ((internalHom O (uliftSections F).val (uliftSections G).val).obj U) :=
      ((internalHom O (uliftSections F).val (uliftSections G).val).obj U).isAddCommGroup
    letI : Module ((Oforget O).obj U)
        ((internalHom O (uliftSections F).val (uliftSections G).val).obj U) :=
      ((internalHom O (uliftSections F).val (uliftSections G).val).obj U).isModule
    letI : AddCommGroup ((internalHom O F.val G.val).obj U) :=
      ((internalHom O F.val G.val).obj U).isAddCommGroup
    letI : Module ((Oforget O).obj U) ((internalHom O F.val G.val).obj U) :=
      ((internalHom O F.val G.val).obj U).isModule
    ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj U))
      { toFun := fun α => internalHomUliftDown U.unop α
        map_add' := fun α β => by
          apply PresheafOfModules.hom_ext
          intro X
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl
        map_smul' := fun r α => by
          apply PresheafOfModules.hom_ext
          intro X
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The comparison `𝓗om_O(F, G) ⟶ 𝓗om_O(ULift F, ULift G)`, which on sections is
`Stacks.SheafOfModules.InternalHom.internalHomUliftUp`. -/
noncomputable def internalHomUliftInvMap
    (F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) :
    internalHom O F.val G.val ⟶ internalHom O (uliftSections F).val (uliftSections G).val where
  app U :=
    letI : AddCommGroup
        ((internalHom O (uliftSections F).val (uliftSections G).val).obj U) :=
      ((internalHom O (uliftSections F).val (uliftSections G).val).obj U).isAddCommGroup
    letI : Module ((Oforget O).obj U)
        ((internalHom O (uliftSections F).val (uliftSections G).val).obj U) :=
      ((internalHom O (uliftSections F).val (uliftSections G).val).obj U).isModule
    letI : AddCommGroup ((internalHom O F.val G.val).obj U) :=
      ((internalHom O F.val G.val).obj U).isAddCommGroup
    letI : Module ((Oforget O).obj U) ((internalHom O F.val G.val).obj U) :=
      ((internalHom O F.val G.val).obj U).isModule
    ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj U))
      { toFun := fun α => internalHomUliftUp U.unop α
        map_add' := fun α β => by
          apply PresheafOfModules.hom_ext
          intro X
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl
        map_smul' := fun r α => by
          apply PresheafOfModules.hom_ext
          intro X
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- **The internal Hom of two universe lifts is the internal Hom of the modules themselves.**
For sheaves of modules `F`, `G` with sections in the universe `m` on a site with objects in
`Type u` and morphisms in `Type v`,

`𝓗om_O(ULift F, ULift G) ≅ 𝓗om_O(F, G)`,

the lift being `Stacks.SheafOfModules.InternalHom.uliftSections`, that is
`SheafOfModules.uliftForPresentation` to `max u v`.  Both sides have their sections in
`max u v m`, which is where the internal Hom of modules with sections in `m` already lives, so
no universe is raised by the statement.

In both directions the isomorphism is componentwise `ULift.down`/`ULift.up`, by
`Stacks.SheafOfModules.InternalHom.internalHomUliftDown` and
`Stacks.SheafOfModules.InternalHom.internalHomUliftUp`, and the two composites are the identity
on the nose. -/
noncomputable def internalHomUliftIso
    (F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) :
    internalHom O (uliftSections F).val (uliftSections G).val ≅ internalHom O F.val G.val where
  hom := internalHomUliftHomMap F G
  inv := internalHomUliftInvMap F G
  hom_inv_id := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- On sections the isomorphism of
`Stacks.SheafOfModules.InternalHom.internalHomUliftIso` is `ULift.down` of the value at
`ULift.up`.  This pins the isomorphism down. -/
theorem internalHomUliftIso_hom_app
    (F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) (U : Cᵒᵖ)
    (α : (internalHom O (uliftSections F).val (uliftSections G).val).obj U)
    (X : (Over U.unop)ᵒᵖ) (x : ((restrFun O U.unop).obj F.val).obj X) :
    ((((internalHomUliftIso F G).hom.app U).hom α).app X).hom x =
      (((α.app X).hom (ULift.up x))).down :=
  rfl

/-- On sections the inverse of the isomorphism of
`Stacks.SheafOfModules.InternalHom.internalHomUliftIso` is `ULift.up` of the value at
`ULift.down`. -/
theorem internalHomUliftIso_inv_app
    (F G : _root_.SheafOfModules.{m} (⟨Oforget O, hO⟩ : Sheaf J RingCat.{w})) (U : Cᵒᵖ)
    (α : (internalHom O F.val G.val).obj U)
    (X : (Over U.unop)ᵒᵖ) (x : ((restrFun O U.unop).obj (uliftSections F).val).obj X) :
    ((((internalHomUliftIso F G).inv.app U).hom α).app X).hom x =
      ULift.up ((α.app X).hom x.down) :=
  rfl

end Stacks.SheafOfModules.InternalHom

end
