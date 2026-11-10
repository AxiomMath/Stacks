module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Every presheaf of modules is a quotient of a flat one

Let `O` be a presheaf of rings on a category `C` and let `F` be a presheaf of `O`-modules.
Every section of `F` over an object `U` is the image of the distinguished section of the
extension from the slice category over `U` of the rank-one `O|_U`-module, so the direct sum of
one such extension for every pair `(U, s)` with `s ∈ F(U)` surjects onto `F`. When `O` is a
presheaf of *commutative* rings each of those extensions is flat, by the direct-sum formula for
extension from a slice, and a direct sum of flat presheaves of modules is flat; so `F` is a
quotient of a flat presheaf of modules.

These are parts (1) and (2) of Stacks 03EW.

## Main definitions

* `Stacks.SheafOfModules.FlatResolution.uliftUnit`: the rank-one presheaf of modules, with its
  carriers lifted to a module universe independent of the ring universe.
* `Stacks.SheafOfModules.FlatResolution.uliftUnitMap`: the morphism out of `uliftUnit`
  determined by a global section of the target.

## Main results

* `Stacks.SheafOfModules.FlatResolution.extensionUliftUnit_isFlat`: the extension from a slice
  of the rank-one module is a flat presheaf of modules.
* `Stacks.SheafOfModules.FlatResolution.exists_epi_from_coproduct_extension`: part (1), the
  presentation by a direct sum of slice extensions.
* `Stacks.SheafOfModules.FlatResolution.exists_epi_from_flat_presheaf`: part (2), the flat
  cover.

## Implementation notes

The four universes — the objects of `C`, its morphisms, the sections of `O`, and the carriers
of the modules — are independent, and the module universe is the ambient one, so that the
direct sum indexed by all pairs `(U, s)` and the slice adjoints both exist. That is why the
rank-one module is `uliftUnit` rather than Mathlib's `PresheafOfModules.unit`: the latter puts
the module carriers in the ring universe, which here is not the ambient one. For the same
reason `uliftUnit` is not Mathlib's `PresheafOfModules.free` applied to the terminal presheaf
of types, whose module carriers again lie in the ring universe.

`extensionUliftUnit_isFlat` is the statement of Stacks 03EV part (1),
`Stacks.Sites.OverModules.presheafExtensionUnit_isFlat`, for `uliftUnit` in place of
Mathlib's `PresheafOfModules.unit`, and it has the same
two-line proof: the extension formula of Stacks 03EJ writes the sections over `V` as a direct
sum of one copy of `ULift (O(V))` for each arrow `V ⟶ U`, each summand is flat because `O(V)`
is flat over itself, a direct sum of flat modules is flat, and objectwise flatness suffices
(Stacks 03ES). It is *not* a generalization in the universes — that statement already has four
independent universes — but in the module: there the module universe is forced to be the ring
universe because `PresheafOfModules.unit` forces it.

Quotients are expressed as epimorphisms. The flatness of a direct sum is Stacks 03EU,
`Stacks.isFlat_coproduct`; it is stated for `Stacks.IsFlat`, which is a second copy of the
Stacks 03ER(1) predicate, so the two spellings are bridged by `isFlat_iff_stacksIsFlat`.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z

namespace Stacks.SheafOfModules.FlatResolution

open AlgebraicGeometry.SheafOfModules (ringPresheaf)
open Stacks.Sites.OverModules (overRingPresheaf presheafModuleAdjunctionsOver
  extensionObjLinearEquivDirectSum extensionFormula)

/-- The rank-one presheaf of modules on a presheaf of rings, with its carriers lifted to a
module universe independent of the universe of the ring's sections. -/
noncomputable def uliftUnit.{z', v', u', w'} {C : Type u'} [Category.{v'} C]
    (O : Cᵒᵖ ⥤ RingCat.{w'}) : _root_.PresheafOfModules.{max w' z'} O where
  obj X := ModuleCat.of (O.obj X) (ULift.{z'} (O.obj X))
  map {X Y} f := ModuleCat.ofHom
    (X := ModuleCat.of (O.obj X) (ULift.{z'} (O.obj X)))
    (Y := (ModuleCat.restrictScalars (O.map f).hom).obj
      (ModuleCat.of (O.obj Y) (ULift.{z'} (O.obj Y)))) {
    toFun := fun x => ⟨O.map f x.down⟩
    map_add' := fun x y => congrArg ULift.up (map_add (O.map f).hom x.down y.down)
    map_smul' := fun r x => congrArg ULift.up (map_mul (O.map f).hom r x.down) }
  map_id X := by ext x; exact congrArg ULift.up (ConcreteCategory.congr_hom (O.map_id X) x.down)
  map_comp f g := by
    ext x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (O.map_comp f g) x.down)

/-- The morphism out of the rank-one presheaf of modules determined by a global section of the
target: it sends the distinguished generator over `X` to `s X`. -/
noncomputable def uliftUnitMap.{z', v', u', w'} {C : Type u'} [Category.{v'} C]
    (O : Cᵒᵖ ⥤ RingCat.{w'}) (F : _root_.PresheafOfModules.{max w' z'} O)
    (s : ∀ X, F.obj X) (hs : ∀ {X Y} (f : X ⟶ Y), F.map f (s X) = s Y) :
    uliftUnit.{z'} O ⟶ F where
  app X := ModuleCat.ofHom (X := (uliftUnit.{z'} O).obj X) (Y := F.obj X) {
    toFun := fun x => x.down • s X
    map_add' := fun _ _ => add_smul _ _ _
    map_smul' := fun _ _ => mul_smul _ _ _ }
  naturality {X Y} f := by
    ext x
    change (O.map f x.down) • s Y = F.map f (x.down • s X)
    rw [_root_.PresheafOfModules.map_smul, hs f]
    rfl

/-- `uliftUnitMap` sends a section over `X` to the corresponding multiple of `s X`. -/
@[simp]
lemma uliftUnitMap_app_apply.{z', v', u', w'} {C : Type u'} [Category.{v'} C]
    (O : Cᵒᵖ ⥤ RingCat.{w'}) (F : _root_.PresheafOfModules.{max w' z'} O)
    (s : ∀ X, F.obj X) (hs : ∀ {X Y} (f : X ⟶ Y), F.map f (s X) = s Y) (X : Cᵒᵖ)
    (x : (uliftUnit.{z'} O).obj X) :
    (uliftUnitMap.{z'} O F s hs).app X x = x.down • s X := rfl

variable {C : Type u} [Category.{v} C]

/-- The family of sections of the restriction of `F` to the slice over `U` determined by a
section of `F` over `U`: over an object `V ⟶ U` of the slice it is the restriction of `s`
along that arrow. -/
private noncomputable def sliceRestriction (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) (U : C) (s : F.obj (op U))
    (X : (Over U)ᵒᵖ) :
    ((_root_.PresheafOfModules.pushforward₀.{max u v w z} (Over.forget U) O).obj F).obj X :=
  F.map (X.unop.hom.op) s

/-- `sliceRestriction` is compatible with the restriction maps of the slice. -/
private lemma sliceRestriction_map (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) (U : C) (s : F.obj (op U))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((_root_.PresheafOfModules.pushforward₀.{max u v w z} (Over.forget U) O).obj F).map f
        (sliceRestriction O F U s X) = sliceRestriction O F U s Y := by
  dsimp [sliceRestriction, _root_.PresheafOfModules.pushforward₀,
    _root_.PresheafOfModules.pushforward₀Obj,
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  change F.map (f.unop.left.op) (F.map (X.unop.hom.op) s) = F.map (Y.unop.hom.op) s
  rw [← _root_.PresheafOfModules.map_comp_apply]
  exact F.congr_map_apply (by simpa only [op_comp] using congrArg Quiver.Hom.op f.unop.w) s

/-- The morphism out of the rank-one module on the slice over `U` determined by a section of
`F` over `U`. -/
private noncomputable def sliceRestrictionMap (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) (U : C) (s : F.obj (op U)) :
    uliftUnit.{max u v w z} (overRingPresheaf O U) ⟶
      (_root_.PresheafOfModules.pushforward₀.{max u v w z} (Over.forget U) O).obj F :=
  uliftUnitMap.{max u v w z} (overRingPresheaf O U) _ (sliceRestriction O F U s)
    (fun f => sliceRestriction_map O F U s f)

/-- The morphism from the slice extension of the rank-one module determined by a section of
`F` over `U`, obtained from `sliceRestrictionMap` by the extension-restriction adjunction. -/
private noncomputable def extensionSectionMap (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) (U : C) (s : F.obj (op U)) :
    ((presheafModuleAdjunctionsOver.{v, u, w, max w z} O U).extension.obj
      (uliftUnit.{max u v w z} (overRingPresheaf O U))) ⟶ F :=
  (((presheafModuleAdjunctionsOver.{v, u, w, max w z} O U).extensionRestriction.homEquiv
      _ _).symm) (sliceRestrictionMap O F U s)

/-- The distinguished section over `U` of the extension from the slice over `U` of the
rank-one module: the image of `1` under the unit of the extension-restriction adjunction. -/
private noncomputable def distinguishedSection (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    ((presheafModuleAdjunctionsOver.{v, u, w, max w z} O U).extension.obj
      (uliftUnit.{max u v w z} (overRingPresheaf O U))).obj (op U) :=
  ((presheafModuleAdjunctionsOver.{v, u, w, max w z} O U).extensionRestriction.unit.app
    (uliftUnit.{max u v w z} (overRingPresheaf O U))).app (op (Over.mk (𝟙 U)))
    (ULift.up (1 : (overRingPresheaf O U).obj (op (Over.mk (𝟙 U)))))

/-- The adjunct map of `extensionSectionMap` sends the distinguished section over `U` to the
chosen section. -/
private lemma extensionSectionMap_id_app (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) (U : C) (s : F.obj (op U)) :
    (extensionSectionMap O F U s).app (op U) (distinguishedSection.{v, u, w, z} O U) = s := by
  have h := congrArg (fun k => k.app (op (Over.mk (𝟙 U)))
      (ULift.up (1 : (overRingPresheaf O U).obj (op (Over.mk (𝟙 U))))))
    ((presheafModuleAdjunctionsOver.{v, u, w, max w z} O U).extensionRestriction.homEquiv_unit
      (f := extensionSectionMap O F U s))
  refine h.symm.trans ?_
  simp only [extensionSectionMap, Equiv.apply_symm_apply]
  refine (one_smul ((overRingPresheaf O U).obj (op (Over.mk (𝟙 U))))
    (sliceRestriction O F U s (op (Over.mk (𝟙 U))))).trans ?_
  change F.map (𝟙 (op U)) s = s
  rw [F.map_id]
  rfl

/-- **Stacks 03EW, part (1).** Every presheaf of modules is a quotient of a direct sum of
extensions from slice categories of the rank-one module. The sum is indexed by all pairs
`(U, s)` with `s` a section of `F` over `U`, and the component at `(U, s)` is the morphism
adjoint to `s`. -/
@[stacks 03EW "part (1)"]
theorem exists_epi_from_coproduct_extension (O : Cᵒᵖ ⥤ RingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} O) :
    ∃ (ι : Type (max u v w z)) (U : ι → C),
      ∃ (p : (∐ fun i : ι =>
        ((presheafModuleAdjunctionsOver.{v, u, w, max w z} O (U i)).extension.obj
          (uliftUnit.{max u v w z} (overRingPresheaf O (U i))))) ⟶ F), Epi p := by
  classical
  let I := Σ X : C, F.obj (op X)
  let V : I → C := fun i => i.1
  let P : I → _root_.PresheafOfModules.{max u v w z} O := fun i =>
    (presheafModuleAdjunctionsOver.{v, u, w, max w z} O (V i)).extension.obj
      (uliftUnit.{max u v w z} (overRingPresheaf O (V i)))
  let fs : (i : I) → P i ⟶ F := fun i => extensionSectionMap O F (V i) i.2
  refine ⟨I, V, Sigma.desc fs, ?_⟩
  apply _root_.PresheafOfModules.epi_of_surjective
  intro X x
  exact ⟨(Sigma.ι P ⟨X.unop, x⟩).app X (distinguishedSection.{v, u, w, z} O X.unop),
    (congrArg (fun f => f.app X (distinguishedSection.{v, u, w, z} O X.unop))
      (Sigma.ι_comp_desc fs ⟨X.unop, x⟩)).trans (extensionSectionMap_id_app O F X.unop x)⟩

/-- **Stacks 03EV, part (1), for the lifted rank-one module.** The extension from the slice
category over `U` of `uliftUnit` is a flat presheaf of modules. -/
theorem extensionUliftUnit_isFlat (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat
      ((presheafModuleAdjunctionsOver.{v, u, w, max w z} (ringPresheaf O) U).extension.obj
        (uliftUnit.{max u v w z} (overRingPresheaf (ringPresheaf O) U))) := by
  classical
  apply AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat
  intro V
  let A := presheafModuleAdjunctionsOver.{v, u, w, max w z} (ringPresheaf O) U
  let G := uliftUnit.{max u v w z} (overRingPresheaf (ringPresheaf O) U)
  obtain ⟨e, _⟩ := extensionObjLinearEquivDirectSum.{v, u, w, max w z} (ringPresheaf O) U A G
  have hsum : Module.Flat ((ringPresheaf O).obj V)
      (extensionFormula.{v, u, w, max u w z} (ringPresheaf O) U V.unop G) := by
    refine Module.Flat.directSum_iff.2 fun _ => ?_
    change Module.Flat ((ringPresheaf O).obj V)
      (ULift.{max u v w z} ((ringPresheaf O).obj V))
    exact Module.Flat.of_linearEquiv ULift.moduleEquiv
  exact Module.Flat.of_linearEquiv (e V.unop)

/-- The two copies of the Stacks 03ER(1) flatness predicate for presheaves of modules agree. -/
private lemma isFlat_iff_stacksIsFlat {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{max u v w z} (ringPresheaf O)) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat F ↔ Stacks.IsFlat F :=
  Iff.rfl

/-- **Stacks 03EW, part (2).** Every presheaf of modules over a presheaf of commutative rings
is a quotient of a flat presheaf of modules: the direct sum produced by part (1) is a direct
sum of slice extensions of the rank-one module, each of which is flat. -/
@[stacks 03EW "part (2)"]
theorem exists_epi_from_flat_presheaf (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F : _root_.PresheafOfModules.{max u v w z} (ringPresheaf O)) :
    ∃ P : _root_.PresheafOfModules.{max u v w z} (ringPresheaf O),
      AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat P ∧
        ∃ (p : P ⟶ F), Epi p := by
  classical
  obtain ⟨ι, U, p, hp⟩ :=
    exists_epi_from_coproduct_extension.{v, u, w, z} (ringPresheaf O) F
  let Q : ι → _root_.PresheafOfModules.{max u v w z} (ringPresheaf O) := fun i =>
    (presheafModuleAdjunctionsOver.{v, u, w, max w z} (ringPresheaf O) (U i)).extension.obj
      (uliftUnit.{max u v w z} (overRingPresheaf (ringPresheaf O) (U i)))
  refine ⟨∐ Q, ?_, p, hp⟩
  rw [isFlat_iff_stacksIsFlat]
  exact Stacks.isFlat_coproduct Q fun i =>
    (isFlat_iff_stacksIsFlat _).1 (extensionUliftUnit_isFlat.{v, u, w, z} O (U i))

end Stacks.SheafOfModules.FlatResolution

end
