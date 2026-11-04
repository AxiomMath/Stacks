module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank-one module on a slice site, and extension by zero at a large module universe

Let `(C, J)` be a site, `O` a sheaf of rings on it and `U` an object of `C`. Restriction of
sheaves of `O`-modules along `Over.forget U` has a left adjoint `j_{U!}`, extension by zero,
and the modules `j_{U!} O_U` generate the category of sheaves of modules. This file provides
both at a module universe large enough to accommodate a site whose objects, morphisms and ring
sections have three unrelated universes: the free module universe is `max u v w m`, where
`C : Type u`, `Category.{v} C` and `O` takes values in `RingCat.{w}`.

Two things are needed for that. The first is the rank-one module itself: `O` has sections in
`RingCat.{w}`, so the usual `SheafOfModules.unit O` is a module of universe `w` and cannot be
an object of `SheafOfModules.{max u v w m} O`. `presheafUnit` and `sheafUnit` are the same
module with its sections replaced by `ULift`s of themselves. The second is the adjoint itself:
Mathlib's `PresheafOfModules.pushforward` is known to be a right adjoint only when the site,
the ring and the modules all share one universe, so `SheafOfModules.pullback` is not available
as stated. What replaces it is
`Stacks.Sites.OverModules.presheafModuleAdjunctionsOver`, the direct-sum construction of the
presheaf-level adjoint of Stacks 03EJ, which has a free module universe already; transporting
it through `SheafOfModules.PullbackConstruction.adjunction` gives the sheaf-level adjoint.

## Main definitions

* `Stacks.Sites.OverModules.presheafUnit`: the rank-one presheaf of modules, with its sections
  lifted to a chosen larger universe.
* `Stacks.Sites.OverModules.sheafUnit`: the same for a sheaf of rings.
* `Stacks.Sites.OverModules.toSheafSheafUnitIso`: the identification of the abelian sheaf
  underlying `sheafUnit O` with the one underlying `O`, available when the lift target is
  absorbed by the ring universe.
* `Stacks.Sites.OverModules.sheafExtensionByZero`: extension by zero `j_{U!}` on sheaves of
  modules at the module universe `max u v w m`, with its adjunction
  `Stacks.Sites.OverModules.sheafExtensionAdjunction`.
* `Stacks.Sites.OverModules.extensionByZeroUnit`: the module `j_{U!} O_U` itself.
* `Stacks.Sites.OverModules.extensionByZeroHomEquiv`: the bijection between morphisms
  `j_{U!} O_U ⟶ F` and sections of `F` over `U`, and
  `Stacks.Sites.OverModules.extensionByZeroHomAddEquiv`, the same as an isomorphism of groups.

## Main results

* `Stacks.Sites.OverModules.sheafRestrictionIsRightAdjoint`: restriction of sheaves of modules
  along `Over.forget U` is a right adjoint at the module universe `max u v w m`, which is what
  makes `sheafExtensionByZero` definable.
* `Stacks.Sites.OverModules.toSheaf_sheafUnit_val`: the underlying abelian sheaf of `sheafUnit O`
  is the `ULift` of the one underlying `O`, by definition.
* `Stacks.Sites.OverModules.extensionByZeroHomEquiv_naturality` and
  `Stacks.Sites.OverModules.extensionByZeroHomEquiv_add`: that bijection is natural in `F` and
  additive.

## Implementation notes

`Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint` is the same statement with the
object, morphism, ring and module universes all equal to one `u`; it is obtained from Mathlib's
instance for a small site, and the exactness and abelian-comparison results proved alongside it
are available only there. Nothing in this file supersedes it: the two are independent
specialisations, and the universe-monomorphic one is what the material on Stacks 03DJ uses.

`sheafUnit` is a sheaf because `ULift`ing the sections is `AddCommGrpCat.uliftFunctor`, which
preserves the sheaf condition; the `change` identifies the underlying presheaf of abelian
groups of `presheafUnit O.obj` with that composite, which holds by definition.

`extensionByZeroHomEquiv` is the `ULift`ed form of
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`, Stacks 0G1V, which exists only with
all four universes equal. Its two properties are both proved by first rewriting it into the
composite of the adjunction transpose with evaluation at the terminal object of `C/U`
(`extensionByZeroHomEquiv_eq`): rewriting inside the nested `Equiv.trans` of the definition
itself does not fire.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.OverModules

universe v u w m z

variable {C : Type u} [Category.{v} C]

/-- The rank-one presheaf of modules over a presheaf of rings `O`, with its sections lifted
from the ring universe `w` to `max w z`. The module structure is the ring acting on itself. -/
noncomputable def presheafUnit (O : Cᵒᵖ ⥤ RingCat.{w}) : PresheafOfModules.{max w z} O where
  obj X := ModuleCat.of (O.obj X) (ULift.{z} (O.obj X))
  map {X Y} f := ModuleCat.ofHom
    (X := ModuleCat.of (O.obj X) (ULift.{z} (O.obj X)))
    (Y := (ModuleCat.restrictScalars (O.map f).hom).obj
      (ModuleCat.of (O.obj Y) (ULift.{z} (O.obj Y)))) {
    toFun := fun x => ⟨O.map f x.down⟩
    map_add' x y := congrArg ULift.up (map_add (O.map f).hom x.down y.down)
    map_smul' r x := congrArg ULift.up (map_mul (O.map f).hom r x.down) }
  map_id X := by
    ext x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (O.map_id X) x.down)
  map_comp f g := by
    ext x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (O.map_comp f g) x.down)

/-- The rank-one sheaf of modules over a sheaf of rings `O`, with its sections lifted from the
ring universe `w` to `max w z`. -/
noncomputable def sheafUnit {J : GrothendieckTopology C} (O : Sheaf J RingCat.{w}) :
    SheafOfModules.{max w z} O where
  val := presheafUnit O.obj
  isSheaf := by
    change Presheaf.IsSheaf J
      ((PresheafOfModules.unit O.obj).presheaf ⋙ AddCommGrpCat.uliftFunctor.{z})
    exact ((sheafCompose J AddCommGrpCat.uliftFunctor.{z}).obj
      ((SheafOfModules.toSheaf O).obj (SheafOfModules.unit O))).property

/-- The underlying abelian sheaf of the lifted rank-one module is the `ULift` of the underlying
abelian sheaf of `O`, on the nose: the sections of `sheafUnit O` over `X` are `ULift (O(X))` by
definition, and the forgetful functor on modules does not touch them. -/
theorem toSheaf_sheafUnit_val {J : GrothendieckTopology C} (O : Sheaf J RingCat.{w}) :
    ((SheafOfModules.toSheaf.{max w z} O).obj (sheafUnit.{v, u, w, z} O)).obj =
      ((sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj O).obj ⋙
        AddCommGrpCat.uliftFunctor.{z, w} :=
  rfl

/-- **The lifted rank-one module is the structure sheaf, once the lift collapses.** When the
module universe of `sheafUnit` is already the ring universe — that is, when the lift target `z`
is absorbed by the ring universe, written here as `max w z` — the underlying abelian sheaf of
`sheafUnit O` is the abelian sheaf underlying `O` itself.

This is the comparison the reduction of Stacks 08PC part (2) needs. Stacks 08P4
(`Stacks.Sites.ExtensionByZero.extensionByZeroCompToSheafIso`) rewrites the underlying abelian
sheaf of `j_{U!} O_U` as `j^{Ab}_{U!}` applied to the underlying abelian sheaf of
`sheafUnit (O.over U)`, whereas every later step of that reduction speaks of the structure sheaf
`O_U` itself; `sheafUnit` differs from it exactly by the `ULift` on its sections, which
`toSheaf_sheafUnit_val` above exhibits and which this isomorphism undoes.

Nothing beyond `AddEquiv.ulift` is used: the two underlying presheaves agree up to that lift
objectwise and the naturality square is `rfl`, so the comparison is read back through the full
faithfulness of `sheafToPresheaf`. The universe hypothesis is not a restriction in the
intended application, where the ring universe already contains the objects and morphisms of the
slice site. -/
noncomputable def toSheafSheafUnitIso {J : GrothendieckTopology C} (O : Sheaf J RingCat.{max w z})
    [J.HasSheafCompose (forget₂ RingCat.{max w z} AddCommGrpCat.{max w z})] :
    (SheafOfModules.toSheaf.{max w z} O).obj (sheafUnit.{v, u, max w z, z} O) ≅
      (sheafCompose J (forget₂ RingCat.{max w z} AddCommGrpCat.{max w z})).obj O :=
  (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max w z}).preimageIso
    (NatIso.ofComponents
      (fun X ↦ AddEquiv.toAddCommGrpIso (AddEquiv.ulift (α := (O.obj.obj X : Type (max w z)))))
      (fun _ ↦ rfl))

variable (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]

/-- Restriction of presheaves of modules along `Over.forget U` is a right adjoint at the module
universe `max u v w m`, with the morphism of presheaves of rings spelled as the identity of
`O_U`, which is the form `SheafOfModules.PullbackConstruction.adjunction` asks for. -/
private instance presheafRestrictionIsRightAdjoint (O : Sheaf J RingCat.{w}) (U : C) :
    (PresheafOfModules.pushforward.{max u v w m} (F := Over.forget U)
      (R := O.obj) (S := (O.over U).obj)
      (𝟙 (O.over U) : (O.over U) ⟶ (O.over U)).hom).IsRightAdjoint :=
  (presheafModuleAdjunctionsOver.{v, u, w, max w m} O.obj U).extensionRestriction.isRightAdjoint

/-- Restriction of sheaves of modules along `Over.forget U` is a right adjoint at the module
universe `max u v w m`; its left adjoint is extension by zero. -/
instance sheafRestrictionIsRightAdjoint (O : Sheaf J RingCat.{w}) (U : C) :
    (SheafOfModules.pushforward.{max u v w m} (F := Over.forget U)
      (𝟙 (O.over U) : (O.over U) ⟶ (O.over U))).IsRightAdjoint :=
  have := presheafRestrictionIsRightAdjoint.{v, u, w, m} J O U
  (SheafOfModules.PullbackConstruction.adjunction.{max u v w m}
    (F := Over.forget U) (𝟙 (O.over U))).isRightAdjoint

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- **Restriction of sheaves of modules along `Over.forget U` is a right adjoint at any module
universe `a` absorbing the morphisms of `C`**; its left adjoint is extension by zero.

The presheaf-level left adjoint is `Stacks.Sites.OverModules.extensionFunctorAdjunction`, the
direct-sum construction of Stacks 03EJ, whose coproducts are indexed by morphisms of `C` and so
need only `UnivLE.{v, a}`; `SheafOfModules.PullbackConstruction.adjunction` sheafifies it.

This is `sheafRestrictionIsRightAdjoint` above with the module universe a bare parameter rather
than `max u v w m`. A conclusion stated at a `max` does not determine its free summand when the
goal's module universe is itself a `max` (`max u v w ?m =?= max t u v w` has several
solutions), so instance search on such goals is stuck; with `a` bare it is read off the goal. -/
instance (priority := high) isRightAdjoint_sheafRestriction.{a} [UnivLE.{v, a}]
    [HasWeakSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
    (O : Sheaf J RingCat.{w}) (U : C) :
    (SheafOfModules.pushforward.{a} (F := Over.forget U)
      (𝟙 (O.over U) : (O.over U) ⟶ (O.over U))).IsRightAdjoint :=
  have : (PresheafOfModules.pushforward.{a} (F := Over.forget U)
      (R := O.obj) (S := (O.over U).obj)
      (𝟙 (O.over U) : (O.over U) ⟶ (O.over U)).hom).IsRightAdjoint :=
    (extensionFunctorAdjunction.{v, u, w, a} O.obj U).isRightAdjoint
  (SheafOfModules.PullbackConstruction.adjunction.{a}
    (F := Over.forget U) (𝟙 (O.over U))).isRightAdjoint

/-- Extension by zero `j_{U!}` from the slice site `C/U`, on sheaves of modules at the module
universe `max u v w m`. -/
noncomputable def sheafExtensionByZero (O : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u v w m} (O.over U) ⥤ SheafOfModules.{max u v w m} O :=
  have := sheafRestrictionIsRightAdjoint.{v, u, w, m} J O U
  SheafOfModules.pullback.{max u v w m} (F := Over.forget U) (𝟙 (O.over U))

/-- Extension by zero is left adjoint to restriction along `Over.forget U`. -/
@[sga "4 IV 11.3.1" "special case"]
noncomputable def sheafExtensionAdjunction (O : Sheaf J RingCat.{w}) (U : C) :
    sheafExtensionByZero.{v, u, w, m} J O U ⊣
      SheafOfModules.pushforward.{max u v w m} (F := Over.forget U) (𝟙 (O.over U)) :=
  have := sheafRestrictionIsRightAdjoint.{v, u, w, m} J O U
  SheafOfModules.pullbackPushforwardAdjunction.{max u v w m}
    (F := Over.forget U) (𝟙 (O.over U))

/-- `j_{U!} O_U`, the extension by zero of the lifted rank-one module on the slice site over
`U`. Naming it keeps the four universe arguments, which its consumers repeat many times, in one
place. -/
noncomputable abbrev extensionByZeroUnit (O : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u v w m} O :=
  (sheafExtensionByZero.{v, u, w, m} J O U).obj
    (sheafUnit.{v, max u v, w, max u v m} (O.over U))

/-- The sections of a presheaf of types over a category with a terminal object `T` are its
sections at `T`: a compatible family is determined by its value there, and every value
extends to one by restriction along the unique maps into `T`. -/
def sectionsEquivOfIsTerminal {D : Type*} [Category D] (P : Dᵒᵖ ⥤ Type*) (T : D)
    (hT : IsTerminal T) : P.sections ≃ P.obj (op T) where
  toFun s := s.1 (op T)
  invFun x := ⟨fun j => P.map (hT.from j.unop).op x, by
    intro j j' f
    change P.map f (P.map (hT.from j.unop).op x) = P.map (hT.from j'.unop).op x
    rw [← Functor.map_comp_apply, ← Quiver.Hom.op_unop f, ← op_comp,
      hT.hom_ext (f.unop ≫ hT.from j.unop) (hT.from j'.unop)]⟩
  left_inv s := Subtype.ext <| funext fun j => s.2 (hT.from j.unop).op
  right_inv _ := by simp

/-- Morphisms out of the lifted rank-one sheaf of modules are the sections of the target: a
morphism is determined by the image of the section `1`, and any section of `F` determines one
by multiplication. This is the `ULift`ed form of `SheafOfModules.unitHomEquiv`. -/
noncomputable def sheafUnitHomEquiv {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
    (F : SheafOfModules.{max w z} O) : (sheafUnit.{v, u, w, z} O ⟶ F) ≃ F.sections := by
  let E := sheafUnit.{v, u, w, z} O
  refine
    { toFun := fun f => ⟨fun X => f.val.app X (ULift.up.{z, w} (1 : O.obj.obj X)), ?_⟩
      invFun := fun s => ⟨(show PresheafOfModules.Hom E.val F.val from {
        app := fun X => ModuleCat.ofHom {
          toFun := fun x => x.down • s.eval X
          map_add' _ _ := by simp [add_smul]
          map_smul' _ _ := by simp [mul_smul] }
        naturality := by
          intro X Y g
          dsimp [E, sheafUnit, presheafUnit]
          ext x
          change O.obj.map g x.down • s.eval Y = F.val.map g (x.down • s.eval X)
          have hs : F.val.map g (s.eval X) = s.eval Y := s.property g
          rw [← hs, F.val.map_smul]
          rfl })⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro X Y g
    have hunit : (E.val.map g) (ULift.up 1) = ULift.up 1 := by
      dsimp [E, sheafUnit, presheafUnit]
      change ULift.up.{z, w} (O.obj.map g 1) = ULift.up.{z, w} 1
      simp
    change F.val.map g (f.val.app X (ULift.up.{z, w} 1)) = f.val.app Y (ULift.up.{z, w} 1)
    rw [← PresheafOfModules.naturality_apply f.val g (ULift.up.{z, w} 1), hunit]
  · intro f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    dsimp [E, sheafUnit, presheafUnit] at x ⊢
    change x.down • f.val.app X (ULift.up 1) = f.val.app X x
    have hx : (x.down : O.obj.obj X) • (ULift.up.{z, w} 1 : ULift.{z} (O.obj.obj X)) = x := by
      apply ULift.ext
      simp
    rw [← hx]
    have hxdown : (x.down • (ULift.up 1 : ULift.{z} (O.obj.obj X))).down = x.down :=
      congrArg ULift.down hx
    rw [hxdown]
    exact ((f.val.app X).hom.map_smul x.down (ULift.up.{z, w} 1)).symm
  · intro s
    apply Subtype.ext
    funext X
    change (ULift.up.{z, w} (1 : O.obj.obj X)).down • s.eval X = s.eval X
    simp

/-- **Stacks 0G1V at a large module universe.** Morphisms `j_{U!} O_U ⟶ F` out of the extension
by zero of the lifted rank-one module are canonically the sections of `F` over `U`: transpose
along the extension-by-zero adjunction, read the result as a section of the restriction of `F`,
and evaluate at the terminal object `𝟙 U` of `C/U`. -/
noncomputable def extensionByZeroHomEquiv (O : Sheaf J RingCat.{w}) (U : C)
    (F : SheafOfModules.{max u v w m} O) :
    (extensionByZeroUnit.{v, u, w, m} J O U ⟶ F) ≃
      (F.val.obj (op U) : Type (max u v w m)) :=
  let G := (SheafOfModules.pushforward.{max u v w m} (F := Over.forget U)
    (𝟙 (O.over U) : (O.over U) ⟶ (O.over U))).obj F
  (((sheafExtensionAdjunction.{v, u, w, m} J O U).homEquiv _ F).trans
    (sheafUnitHomEquiv.{v, max u v, w, max u v m} G)).trans
      (sectionsEquivOfIsTerminal (G.val.presheaf ⋙ forget AddCommGrpCat.{max u v w m})
        (Over.mk (𝟙 U)) Over.mkIdTerminal)

/-- `extensionByZeroHomEquiv` transposes along the adjunction and evaluates the resulting
section at the terminal object of `C/U`. Stating this once keeps the two lemmas below from
having to rewrite inside the nested `Equiv.trans`. -/
private lemma extensionByZeroHomEquiv_eq (O : Sheaf J RingCat.{w}) (U : C)
    (F : SheafOfModules.{max u v w m} O)
    (f : extensionByZeroUnit.{v, u, w, m} J O U ⟶ F) :
    extensionByZeroHomEquiv.{v, u, w, m} J O U F f =
      (sheafUnitHomEquiv.{v, max u v, w, max u v m}
        ((SheafOfModules.pushforward.{max u v w m} (F := Over.forget U)
          (𝟙 (O.over U) : (O.over U) ⟶ (O.over U))).obj F)
        ((sheafExtensionAdjunction.{v, u, w, m} J O U).homEquiv _ F f)).eval
          (op (Over.mk (𝟙 U))) := rfl

/-- `extensionByZeroHomEquiv` is natural in the sheaf of modules: composing with `g : F ⟶ H`
corresponds to applying `g` to sections over `U`. -/
theorem extensionByZeroHomEquiv_naturality (O : Sheaf J RingCat.{w}) (U : C)
    {F H : SheafOfModules.{max u v w m} O}
    (f : extensionByZeroUnit.{v, u, w, m} J O U ⟶ F) (g : F ⟶ H) :
    extensionByZeroHomEquiv.{v, u, w, m} J O U H (f ≫ g) =
      g.val.app (op U) (extensionByZeroHomEquiv.{v, u, w, m} J O U F f) := by
  simp only [extensionByZeroHomEquiv_eq, Adjunction.homEquiv_naturality_right]
  rfl

/-- `extensionByZeroHomEquiv` is additive. Writing the transpose as the unit followed by the
restriction of the morphism leaves the dependence on the morphism inside
`f ↦ f.val.app (op U)`, which is additive by definition; no additivity of the two functors is
needed. -/
theorem extensionByZeroHomEquiv_add (O : Sheaf J RingCat.{w}) (U : C)
    (F : SheafOfModules.{max u v w m} O)
    (f g : extensionByZeroUnit.{v, u, w, m} J O U ⟶ F) :
    extensionByZeroHomEquiv.{v, u, w, m} J O U F (f + g) =
      extensionByZeroHomEquiv.{v, u, w, m} J O U F f +
        extensionByZeroHomEquiv.{v, u, w, m} J O U F g := by
  simp only [extensionByZeroHomEquiv_eq, Adjunction.homEquiv_unit]
  rfl

/-- `extensionByZeroHomEquiv` as an isomorphism of additive groups. -/
noncomputable def extensionByZeroHomAddEquiv (O : Sheaf J RingCat.{w}) (U : C)
    (F : SheafOfModules.{max u v w m} O) :
    (extensionByZeroUnit.{v, u, w, m} J O U ⟶ F) ≃+
      (F.val.obj (op U) : Type (max u v w m)) :=
  AddEquiv.mk' (extensionByZeroHomEquiv.{v, u, w, m} J O U F)
    (extensionByZeroHomEquiv_add.{v, u, w, m} J O U F)

end Stacks.Sites.OverModules

end
