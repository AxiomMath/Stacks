module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators

/-!
# Sections of an extension by zero are local combinations of its arrow generators

Let `(C, J)` be a small site, `O` a sheaf of rings on it and `U` an object of `C`. The
extension by zero `j_{U!} O_U` of the structure sheaf of the slice site carries, over each
object `W`, one distinguished section for each *arrow* `g : W ⟶ U`: the restriction along `g`
of the tautological generator `SheafOfModules.extensionByZeroGen` over `U`. This file proves
that those sections generate locally: a section of `j_{U!} O_U` over `W` becomes, on a covering
sieve of `W`, a finite `O`-linear combination of them.

This is the step at which a site differs from a space, and the difference is in the *index*.
Over a space, `j_{V!} O_V` restricted to an open `Z ≤ V` is free of rank one on the single
inclusion, and the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.exists_eq_smul_res_extGen` is an equality on the nose with
one coefficient and no shrinking. Over a site the set of arrows `W ⟶ U` is arbitrary, nothing
selects one of them, and the equality holds only after passing to a covering sieve.

## Main definitions

* `Stacks.Sites.ExtensionByZero.freeGen`: the basis element, over `W`, of the free presheaf of
  modules on the representable at `U`, attached to an arrow `g : W ⟶ U`.
* `Stacks.Sites.ExtensionByZero.genAt`: the generating section of `j_{U!} O_U` over `W`
  attached to an arrow `g : W ⟶ U`.
* `Stacks.Sites.ExtensionByZero.arrowGenComparison`: the morphism of presheaves of modules from
  the free presheaf on the representable at `U` to `j_{U!} O_U` that carries the basis element
  at an arrow to the generating section at that arrow.

## Main results

* `Stacks.Sites.ExtensionByZero.map_genAt`: restricting the generator at `g` along `k` gives
  the generator at `k ≫ g`, so the family of generators is stable under refinement.
* `Stacks.Sites.ExtensionByZero.arrowGenComparison_app_freeGen`: the comparison does carry the
  basis element at `g` to `genAt O U g`.
* `Stacks.Sites.ExtensionByZero.exists_sieve_eq_sum_smul_genAt`: **a section of `j_{U!} O_U`
  over `W` is, on a covering sieve of `W`, a finite `O`-linear combination of the generators
  attached to arrows into `U`.**

## Implementation notes

The proof reads `j_{U!} O_U` as the sheafification of the free presheaf of modules on the
representable at `U`, which is `SheafOfModules.extensionByZeroIsoSheafifiedFreeYoneda`; the
comparison `arrowGenComparison` is therefore locally surjective, and a section of the free
presheaf over `W` is a finite combination of the basis elements indexed by `W ⟶ U`, which is
`Finsupp.sum_single`.

Nothing here is an "away from a point" argument: there is no counterpart on a site of
`Stacks.Cohomology.LeftDualPerfect.exists_resS_eq_zero_of_not_mem`, and none is needed, because
the arrow is part of the index rather than a side condition on it.

`arrowGenComparison` is the transpose of `SheafOfModules.freeYonedaToExtensionByZero` under
`PresheafOfModules.sheafificationHomEquiv`, so that
`PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def` identifies it with "sheafify,
then compare" by `rfl`. That identification is what makes it locally surjective, and it is also
what pins its value at the basis element of the identity arrow: that value is read off
`SheafOfModules.sheafifiedFreeYonedaEquiv`, whose inverse `freeYonedaToExtensionByZero` is
defined to send the canonical generator to `SheafOfModules.extensionByZeroGen`.

`freeGen` exists for a bookkeeping reason rather than a mathematical one. The free module
`(ModuleCat.free (O(W))).obj ((yoneda.obj U).obj (op W))` and the value at `op W` of the free
presheaf of modules on the representable are the same module, but not by the same expression,
so `ModuleCat.freeMk` elaborated at an arrow does not rewrite inside statements about the
presheaf; `freeGen` fixes the spelling.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZero

section FreeModules

/-- **Every element of a free module is a finite combination of basis elements.** The free
module on `X` over `Rg` is the module of finitely supported functions on `X`, so an element is
the sum over its support of its values times the basis vectors. -/
theorem exists_finset_eq_sum_smul_single {Rg : Type u} [Ring Rg] {X : Type u} (z : X →₀ Rg) :
    ∃ (A : Finset X) (c : X → Rg), z = ∑ g ∈ A, c g • (Finsupp.single g (1 : Rg)) := by
  classical
  refine ⟨z.support, fun g => z g, ?_⟩
  conv_lhs => rw [← Finsupp.sum_single z]
  exact Finset.sum_congr rfl fun g _ => by rw [Finsupp.smul_single, smul_eq_mul, mul_one]

variable {C : Type u} [SmallCategory.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- The restriction maps of the free presheaf of modules on a presheaf of types send basis
elements to basis elements. -/
theorem freeObj_map_freeMk (F : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    (PresheafOfModules.freeObj (R := R) F).map f (ModuleCat.freeMk x) =
      ModuleCat.freeMk (F.map f x) := by
  rw [PresheafOfModules.freeObj_map]
  exact ModuleCat.freeDesc_apply _ x

/-- **The bijection `((free R).obj (yoneda.obj X) ⟶ M) ≃ M(X)` is evaluation at the basis
element of the identity.** This is `PresheafOfModules.freeYonedaEquiv_symm_app` read in the
forward direction. -/
theorem freeYonedaEquiv_apply {M : PresheafOfModules.{u} R} {X : C}
    (m : (PresheafOfModules.free R).obj (yoneda.obj X) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv m = m.app (op X) (ModuleCat.freeMk (𝟙 X)) := by
  conv_rhs => rw [← PresheafOfModules.freeYonedaEquiv.symm_apply_apply m]
  exact (PresheafOfModules.freeYonedaEquiv_symm_app M X
    (PresheafOfModules.freeYonedaEquiv m)).symm

end FreeModules

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

/-- **The basis element of the free presheaf of modules on the representable at `U`, over `W`,
attached to an arrow `g : W ⟶ U`.** -/
def freeGen (U : C) {W : C} (g : W ⟶ U) :
    ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).obj (op W) :=
  ModuleCat.freeMk (R := (O.obj.obj (op W) : Type u)) g

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The basis elements are stable under refinement**: the restriction along `k : W' ⟶ W` of
the basis element at `g : W ⟶ U` is the basis element at `k ≫ g`. -/
theorem map_freeGen (U : C) {W' W : C} (k : W' ⟶ W) (g : W ⟶ U) :
    ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).map k.op (freeGen O U g) =
      freeGen O U (k ≫ g) :=
  freeObj_map_freeMk O.obj (yoneda.obj U) k.op g

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Every section of the free presheaf on the representable at `U` over `W` is a finite
`O(W)`-combination of the basis elements at arrows `W ⟶ U`. -/
theorem exists_finset_eq_sum_smul_freeGen (U W : C)
    (z : ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).obj (op W)) :
    ∃ (A : Finset (W ⟶ U)) (c : (W ⟶ U) → O.obj.obj (op W)),
      z = ∑ g ∈ A, c g • freeGen O U g :=
  exists_finset_eq_sum_smul_single (Rg := (O.obj.obj (op W) : Type u)) (X := (W ⟶ U)) z

/-- **The generating section of `j_{U!} O_U` over `W` attached to an arrow `g : W ⟶ U`**: the
restriction along `g` of the tautological generator over `U`. On the site of opens of a space
there is at most one such arrow, and this is the restriction of
`Stacks.Cohomology.LeftDualPerfect.extGen`. -/
def genAt (U : C) {W : C} (g : W ⟶ U) :
    ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
      (SheafOfModules.unit (O.over U))).val.obj (op W) :=
  ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
    (SheafOfModules.unit (O.over U))).val.map g.op (SheafOfModules.extensionByZeroGen O U)

/-- The generator at the identity arrow is the tautological generator. -/
theorem genAt_id (U : C) : genAt O U (𝟙 U) = SheafOfModules.extensionByZeroGen O U := by
  rw [genAt, show (𝟙 U).op = 𝟙 (op U) from rfl, PresheafOfModules.map_id]
  rfl

/-- **The family of arrow generators is stable under refinement**: restricting the generator at
`g : W ⟶ U` along `k : W' ⟶ W` gives the generator at `k ≫ g`. -/
theorem map_genAt (U : C) {W' W : C} (k : W' ⟶ W) (g : W ⟶ U) :
    ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
        (SheafOfModules.unit (O.over U))).val.map k.op (genAt O U g) = genAt O U (k ≫ g) :=
  (PresheafOfModules.map_comp_apply _ g.op k.op (SheafOfModules.extensionByZeroGen O U)).symm

/-- **The comparison from the free presheaf of modules on the representable at `U` to
`j_{U!} O_U`**, as a morphism of presheaves of modules: the transpose, under the sheafification
bijection, of the isomorphism `SheafOfModules.freeYonedaToExtensionByZero`. -/
def arrowGenComparison (U : C) :
    (PresheafOfModules.free O.obj).obj (yoneda.obj U) ⟶
      (PresheafOfModules.restrictScalars (𝟙 O.obj)).obj
        ((SheafOfModules.forget O).obj ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
          (SheafOfModules.unit (O.over U)))) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 O.obj)
    (SheafOfModules.freeYonedaToExtensionByZero O U)

/-- **The comparison is "sheafify, then compare".** This is
`PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def` read on sections, and it holds by
`rfl`. -/
theorem arrowGenComparison_app (U : C) {W : C}
    (z : ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).obj (op W)) :
    (arrowGenComparison O U).app (op W) z =
      (SheafOfModules.freeYonedaToExtensionByZero O U).val.app (op W)
        ((CategoryTheory.toSheafify J
          ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).presheaf).app (op W) z) :=
  rfl

/-- The comparison carries the basis element at the identity to the tautological generator. -/
theorem arrowGenComparison_app_freeGen_id (U : C) :
    (arrowGenComparison O U).app (op U) (freeGen O U (𝟙 U)) =
      SheafOfModules.extensionByZeroGen O U :=
  (freeYonedaEquiv_apply (R := O.obj) (arrowGenComparison O U)).symm.trans
    ((SheafOfModules.sheafifiedFreeYonedaEquiv O _ U).apply_symm_apply
      (SheafOfModules.extensionByZeroGen O U))

/-- **The comparison carries the basis element at an arrow `g` to the generator at `g`.** -/
theorem arrowGenComparison_app_freeGen (U : C) {W : C} (g : W ⟶ U) :
    (arrowGenComparison O U).app (op W) (freeGen O U g) = genAt O U g := by
  have hbasis : ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).map g.op
      (freeGen O U (𝟙 U)) = freeGen O U g :=
    (map_freeGen O U g (𝟙 U)).trans (congrArg (freeGen O U) (Category.comp_id g))
  have hnat := PresheafOfModules.naturality_apply (arrowGenComparison O U) g.op
    (freeGen O U (𝟙 U))
  refine Eq.trans (congrArg (fun y => (arrowGenComparison O U).app (op W) y) hbasis.symm) ?_
  refine hnat.trans ?_
  rw [arrowGenComparison_app_freeGen_id]
  rfl

/-- **The comparison, read on sections over one object, sends a finite combination of basis
elements to the corresponding finite combination of arrow generators.** -/
theorem arrowGenComparison_app_sum (U : C) {W : C} (A : Finset (W ⟶ U))
    (c : (W ⟶ U) → O.obj.obj (op W)) :
    (arrowGenComparison O U).app (op W) (∑ g ∈ A, c g • freeGen O U g) =
      ∑ g ∈ A, c g • genAt O U g := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, arrowGenComparison_app_freeGen]
  rfl

/-- **A section of `j_{U!} O_U` over `W` is, on a covering sieve of `W`, a finite `O`-linear
combination of the generators attached to arrows into `U`.**

This is the sieve-indexed replacement for the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.exists_eq_smul_res_extGen`, which over a space holds with a
single coefficient and no shrinking, because an open has at most one inclusion into another. -/
theorem exists_sieve_eq_sum_smul_genAt (U : C) {W : C}
    (x : ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
      (SheafOfModules.unit (O.over U))).val.obj (op W)) :
    ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃W' : C⦄ (k : W' ⟶ W), T k →
      ∃ (A : Finset (W' ⟶ U)) (c : (W' ⟶ U) → O.obj.obj (op W')),
        ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
            (SheafOfModules.unit (O.over U))).val.map k.op x =
          ∑ g ∈ A, c g • genAt O U g := by
  classical
  have hiso : IsIso (SheafOfModules.freeYonedaToExtensionByZero O U) :=
    SheafOfModules.isIso_freeYonedaToExtensionByZero O U
  have hbij : Function.Bijective ((SheafOfModules.evaluation O (op W)).map
      (SheafOfModules.freeYonedaToExtensionByZero O U)) :=
    ConcreteCategory.bijective_of_isIso _
  obtain ⟨x', hx'⟩ := hbij.2 x
  refine ⟨_, Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J
    ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).presheaf) x', fun {W'} k hk => ?_⟩
  obtain ⟨z₀, hz⟩ := hk
  let z : ((PresheafOfModules.free O.obj).obj (yoneda.obj U)).obj (op W') := z₀
  obtain ⟨A, c, hzsum⟩ := exists_finset_eq_sum_smul_freeGen O U W' z
  refine ⟨A, c, ?_⟩
  refine Eq.trans (congrArg (fun y => ((SheafOfModules.extensionByZero.{u, u, u, u} O U).obj
    (SheafOfModules.unit (O.over U))).val.map k.op y) hx'.symm) ?_
  refine (PresheafOfModules.naturality_apply
    (SheafOfModules.freeYonedaToExtensionByZero O U).val k.op x').symm.trans ?_
  refine Eq.trans (congrArg (fun y =>
    (SheafOfModules.freeYonedaToExtensionByZero O U).val.app (op W') y) hz.symm) ?_
  refine (arrowGenComparison_app O U z).symm.trans ?_
  rw [hzsum]
  exact arrowGenComparison_app_sum O U A c

end Stacks.Sites.ExtensionByZero

end
