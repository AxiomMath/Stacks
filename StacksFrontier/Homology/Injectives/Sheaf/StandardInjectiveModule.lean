module

public import StacksFrontier.Homology.Injectives.Sheaf.DualEvaluationMono
import StacksCore.Tactic.StacksAttribute

/-!
# The standard injective module on a ringed site

Let `(C, O)` be a ringed site and `J` an injective abelian sheaf, so that every `O`-module `F`
has a dual `F^∨ = ℋom(F, J)`. For an `O`-module `G` one forms the free module
`Fr(G) = ⨁_{U, s ∈ G(U)} j_{U!}O_U`, a direct sum of extensions by zero indexed by all local
sections of `G`, and the *standard module* of `F` is the dual of the free module on the dual,
`J(F) = Fr(F^∨)^∨`. This file proves that `J(F)` is an injective `O`-module.

To extend a map `h : X ⟶ J(F)` along a monomorphism
`f : X ⟶ Y` one transposes it to `h^t : Fr(F^∨) ⟶ X^∨`, lifts `h^t` through `Y^∨ ⟶ X^∨` —
possible because `Fr(F^∨)` is a direct sum of objects `j_{U!}O_U`, whose maps to an `O`-module
are exactly its sections over `U`, and because the dual of a monomorphism is surjective on local
sections, `J` being injective — and transposes back.

## Main definitions

* `Stacks.Injectives.DualEvaluation.freeFlatModule`: the free module `Fr(G)`.
* `Stacks.Injectives.DualEvaluation.standardModule`: the standard module `J(F) = Fr(F^∨)^∨`.

## Main results

* `Stacks.Injectives.DualEvaluation.injective_standardModule`: the standard module of any
  `O`-module is injective.
* `Stacks.Injectives.DualEvaluation.dual_restrict_apply`: the restriction law of the internal-hom
  sheaf.
* `Stacks.Injectives.DualEvaluation.hom_ext_dual`: two morphisms into a dual agree as soon as all
  their pairings agree.

## Implementation notes

The dual, the evaluation map and the extensions by zero are the constructed ones: the dual is
`Stacks.Injectives.AbelianDual.dualFunctor`, whose sections over `U` are definitionally the local
homomorphisms, so no comparison map intervenes and the restriction law is a theorem rather than a
hypothesis. That the dual of a monomorphism is surjective on sections is the abelian statement
`internalHomFunctor_objwise_surjective`, the underlying abelian sheaf of the dual being the
abelian internal hom.

## References

* [Stacks Project, Tag 01DT](https://stacks.math.columbia.edu/tag/01DT)
* [Stacks Project, Tag 01DQ](https://stacks.math.columbia.edu/tag/01DQ)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Injectives.AbelianDual
open Stacks.SheafOfModules

namespace Stacks.Injectives.DualEvaluation

universe u

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  (O : Sheaf K CommRingCat.{u}) (Jab : Sheaf K AddCommGrpCat.{u}) [Injective Jab]

omit [Injective Jab] in
/-- The internal-hom pairing is functorial in the module: pairing a section of `Y^∨` pulled back
to `X^∨` against a section of `X` is pairing it against the image of that section in `Y`. -/
theorem localPairing_map {X Y : SheafOfModules.{u} (underlyingRingSheaf O)} (f : X ⟶ Y) (U : C)
    (φ : ((dualFunctor O Jab).obj (op Y)).val.obj (op U)) (x : X.val.obj (op U)) :
    (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map
        ((dualFunctor O Jab).map f.op)) φ).app (op (Over.mk (𝟙 U))) x =
      φ.app (op (Over.mk (𝟙 U)))
        (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map f) x) := rfl

omit [Injective Jab] in
/-- **The restriction law of the internal-hom sheaf `ℋom(F, J)`.** Restricting a section of
`F^∨` over `U` along `f : V ⟶ U` and evaluating the result at the terminal object of `C/V` is
evaluating the original section at the slice object `(V, f)`. -/
theorem dual_restrict_apply (F : SheafOfModules.{u} (underlyingRingSheaf O)) {U V : C} (f : V ⟶ U)
    (φ : ((dualFunctor O Jab).obj (op F)).val.obj (op U)) (x : F.val.obj (op V)) :
    (((dualFunctor O Jab).obj (op F)).val.map f.op φ).app (op (Over.mk (𝟙 V))) x =
      φ.app (op (Over.mk f)) x := by
  have h := presheafHom_map_app (F := F.val.presheaf) (G := Jab.obj) (𝟙 V) f f
    (Category.id_comp f) (φ : (presheafHom F.val.presheaf Jab.obj).obj (op U))
  exact congrArg (fun m => (ConcreteCategory.hom m) x) h

/-- Sections of a morphism of sheaves of modules commute with restriction. -/
theorem sectionMap_naturality {A B : SheafOfModules.{u} (underlyingRingSheaf O)} {U V : C}
    (α : V ⟶ U) (q : A ⟶ B) (x : A.val.obj (op U)) :
    (B.val.map α.op) (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map q) x) =
      ((SheafOfModules.evaluation (underlyingRingSheaf O) (op V)).map q) ((A.val.map α.op) x) :=
  (congrArg (fun m => m x) (congrArg ModuleCat.Hom.hom (q.val.naturality α.op))).symm

omit [Injective Jab] in
/-- Two morphisms into a dual agree as soon as all their pairings agree. -/
theorem hom_ext_dual {A B : SheafOfModules.{u} (underlyingRingSheaf O)}
    {g₁ g₂ : A ⟶ (dualFunctor O Jab).obj (op B)}
    (h : ∀ (W : C) (a : A.val.obj (op W)) (b : B.val.obj (op W)),
      (((SheafOfModules.evaluation (underlyingRingSheaf O) (op W)).map g₁) a).app
          (op (Over.mk (𝟙 W))) b =
        (((SheafOfModules.evaluation (underlyingRingSheaf O) (op W)).map g₂) a).app
          (op (Over.mk (𝟙 W))) b) :
    g₁ = g₂ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  obtain ⟨U⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply NatTrans.ext
  funext V
  obtain ⟨V⟩ := V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  change (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map g₁) x).app
      (op (Over.mk V.hom)) y =
    (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map g₂) x).app
      (op (Over.mk V.hom)) y
  rw [← dual_restrict_apply O Jab B V.hom
      (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map g₁) x) y,
    ← dual_restrict_apply O Jab B V.hom
      (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map g₂) x) y,
    sectionMap_naturality O V.hom g₁ x, sectionMap_naturality O V.hom g₂ x]
  exact h V.left (A.val.map V.hom.op x) y

omit [Injective Jab] in
/-- The transpose of a map into a dual: `(X ⟶ Y^∨) ↦ (Y ⟶ X^∨)`, obtained by dualizing and
composing with the evaluation map of `Y`. -/
def dualTranspose {X Y : SheafOfModules.{u} (underlyingRingSheaf O)}
    (f : X ⟶ (dualFunctor O Jab).obj (op Y)) : Y ⟶ (dualFunctor O Jab).obj (op X) :=
  ev O Jab Y ≫ (dualFunctor O Jab).map f.op

omit [Injective Jab] in
/-- The transpose pairs the two arguments the other way round. -/
theorem dualTranspose_pairing {X Y : SheafOfModules.{u} (underlyingRingSheaf O)}
    (l : X ⟶ (dualFunctor O Jab).obj (op Y)) (U : C)
    (y : Y.val.obj (op U)) (x : X.val.obj (op U)) :
    (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map (dualTranspose O Jab l))
        y).app (op (Over.mk (𝟙 U))) x =
      (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map l) x).app
        (op (Over.mk (𝟙 U))) y :=
  (localPairing_map O Jab l U
      (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map (ev O Jab Y)) y) x).trans
    (ev_apply O Jab Y U y _)

omit [Injective Jab] in
/-- Transposition is involutive. -/
theorem dualTranspose_involutive {X Y : SheafOfModules.{u} (underlyingRingSheaf O)}
    (f : X ⟶ (dualFunctor O Jab).obj (op Y)) :
    dualTranspose O Jab (dualTranspose O Jab f) = f :=
  hom_ext_dual O Jab fun W a b =>
    (dualTranspose_pairing O Jab (dualTranspose O Jab f) W a b).trans
      (dualTranspose_pairing O Jab f W b a)

omit [Injective Jab] in
/-- Transposition turns postcomposition with a dualized morphism into precomposition. -/
theorem dualTranspose_comp_dualMap {X Y G : SheafOfModules.{u} (underlyingRingSheaf O)}
    (f : X ⟶ Y) (k : G ⟶ (dualFunctor O Jab).obj (op Y)) :
    dualTranspose O Jab (k ≫ (dualFunctor O Jab).map f.op) = f ≫ dualTranspose O Jab k :=
  hom_ext_dual O Jab fun W a b =>
    ((dualTranspose_pairing O Jab (k ≫ (dualFunctor O Jab).map f.op) W a b).trans
        (localPairing_map O Jab f W
          (((SheafOfModules.evaluation (underlyingRingSheaf O) (op W)).map k) b) a)).trans
      (dualTranspose_pairing O Jab k W
        (((SheafOfModules.evaluation (underlyingRingSheaf O) (op W)).map f) a) b).symm

/-- The dual of a monomorphism is surjective on local sections over every object. -/
theorem dualMap_sections_surjective {X Y : SheafOfModules.{u} (underlyingRingSheaf O)}
    (f : X ⟶ Y) (hf : Mono f) (U : C) :
    Function.Surjective
      (fun φ : ((dualFunctor O Jab).obj (op Y)).val.obj (op U) =>
        ((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map
          ((dualFunctor O Jab).map f.op)) φ) := by
  have hm : Mono ((SheafOfModules.toSheaf (underlyingRingSheaf O)).map f) := by
    have := hf; infer_instance
  exact internalHomFunctor_objwise_surjective K Jab
    ((SheafOfModules.toSheaf (underlyingRingSheaf O)).map f) U

/-- The free module `Fr(G) = ⨁_{U, s ∈ G(U)} j_{U!}O_U` on the local sections of an
`O`-module `G`: one copy of the extension by zero `j_{U!}O_U` for every object `U` of the site
and every section of `G` over `U`. -/
def freeFlatModule (G : SheafOfModules.{u} (underlyingRingSheaf O)) :
    SheafOfModules.{u} (underlyingRingSheaf O) :=
  ∐ fun p : (Σ U : C, ToType (G.val.obj (op U))) => extensionByZeroUnitFamily O p.1

omit [Injective Jab] in
/-- The standard module `J(F) = Fr(F^∨)^∨` of an `O`-module `F`: the dual of the free module on
the dual of `F`. -/
def standardModule (F : SheafOfModules.{u} (underlyingRingSheaf O)) :
    SheafOfModules.{u} (underlyingRingSheaf O) :=
  (dualFunctor O Jab).obj (op (freeFlatModule O ((dualFunctor O Jab).obj (op F))))

/-- Maps out of `Fr(G)` lift along a morphism which is surjective on sections over every
object. -/
theorem exists_freeFlatModule_lift (G X Y : SheafOfModules.{u} (underlyingRingSheaf O))
    (q : X ⟶ Y)
    (hq : ∀ U : C, Function.Surjective
      (fun x : X.val.obj (op U) =>
        ((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map q) x))
    (f : freeFlatModule O G ⟶ Y) :
    ∃ g : freeFlatModule O G ⟶ X, g ≫ q = f := by
  classical
  let ι (p : Σ U : C, ToType (G.val.obj (op U))) :
      extensionByZeroUnitFamily O p.1 ⟶ freeFlatModule O G :=
    Sigma.ι (fun p : Σ U : C, ToType (G.val.obj (op U)) => extensionByZeroUnitFamily O p.1) p
  have key (p : Σ U : C, ToType (G.val.obj (op U))) :
      ∃ g : extensionByZeroUnitFamily O p.1 ⟶ X, g ≫ q = ι p ≫ f := by
    obtain ⟨x, hx⟩ := hq p.1 (extensionByZeroUnitHomEquiv.{u, u, u, u}
      (underlyingRingSheaf O) p.1 Y (ι p ≫ f))
    refine ⟨(extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) p.1 X).symm x, ?_⟩
    apply (extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) p.1 Y).injective
    rw [extensionByZeroUnitHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hx
  refine ⟨Sigma.desc fun p => (key p).choose, Sigma.hom_ext _ _ fun p => ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ q) (Sigma.ι_comp_desc _ _)).trans (key p).choose_spec)

/-- For every sheaf `F` of `O`-modules the standard module `J(F) = Fr(F^∨)^∨` is an injective
`O`-module. -/
@[stacks 01DT]
theorem injective_standardModule (F : SheafOfModules.{u} (underlyingRingSheaf O)) :
    Injective (standardModule O Jab F) := by
  refine ⟨fun {X Y} h f hf => ?_⟩
  obtain ⟨l, hl⟩ := exists_freeFlatModule_lift O ((dualFunctor O Jab).obj (op F))
    ((dualFunctor O Jab).obj (op Y)) ((dualFunctor O Jab).obj (op X))
    ((dualFunctor O Jab).map f.op)
    (fun U => dualMap_sections_surjective O Jab f hf U) (dualTranspose O Jab h)
  refine ⟨dualTranspose O Jab l, ?_⟩
  exact (dualTranspose_comp_dualMap O Jab f l).symm.trans
    ((congrArg (fun m : freeFlatModule O ((dualFunctor O Jab).obj (op F)) ⟶
          (dualFunctor O Jab).obj (op X) => dualTranspose O Jab m) hl).trans
      (dualTranspose_involutive O Jab
        (X := X) (Y := freeFlatModule O ((dualFunctor O Jab).obj (op F))) h))

end Stacks.Injectives.DualEvaluation

end
