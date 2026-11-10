module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import StacksFrontier.Homology.Perfect.Characterizing

/-!
# Compactness of the free presheaf of modules on a representable

Let `C` be a small category in `Type u` and let `R` be a presheaf of rings on `C` with sections in
`Type u`. For an object `X` of `C` the free presheaf of modules `(free R).obj (yoneda.obj X)` —
the generator `j_{X!}R_X` of [Stacks, Tag 08RX] — corepresents the evaluation at `X`: morphisms
`(free R).obj (yoneda.obj X) ⟶ M` are the sections of `M` over `X`, by
`PresheafOfModules.freeYonedaEquiv`. Colimits of presheaves of modules are computed on sections,
so the evaluation at `X` commutes with direct sums; since the regular module is a compact object
of the category of modules over the ring of sections
(`StacksDraft.Perfect.isCompactObject_regularModule`), the free presheaf of modules on a
representable is a compact object of `PresheafOfModules R`.

This is the counterpart for presheaves of modules of
`CategoryTheory.Presheaf.isCompactObject_freeYoneda`, which says the same of the free diagram
`Presheaf.freeYoneda X P` in a category of diagrams; together with projectivity
(`PresheafOfModules.freeYonedaProjective`) and the separating property
(`PresheafOfModules.freeYoneda.isSeparating`) it is what a dévissage of a morphism of functors on
the unbounded derived category `D(PresheafOfModules R)` along compact generators needs.

## Main results

* `PresheafOfModules.isCompactObject_freeYoneda`: `(free R).obj (yoneda.obj X)` is a compact
  object of `PresheafOfModules R`, at the universe of the site.

## Implementation notes

The corepresentation bijection `PresheafOfModules.freeYonedaEquiv` is turned into an additive
equivalence onto the morphisms out of the regular module,
`PresheafOfModules.freeYonedaRegularHomAddEquiv`, rather than onto the sections themselves: the
compactness statement being transported is the compactness of the regular module, and that is a
statement about *morphism groups*, so both sides of the comparison have to be morphism groups.
Additivity of `freeYonedaEquiv` is not available in Mathlib and is obtained here by writing it as
the evaluation of a morphism at the tautological section
(`PresheafOfModules.freeYonedaEquiv_eq_app`), which is additive because the addition of morphisms
of presheaves of modules is computed on sections.

The index universe of the direct sums is the universe `u` of the site, which is also the universe
of the sections and the morphism universe of `PresheafOfModules R`; this is the universe at which
the cell presentation behind the dévissage tests compactness.

## References

* [Stacks Project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **Morphisms out of the regular module are its sections**, `(A ⟶ N) ≃+ N`, by evaluation at
`1`; the inverse sends `x` to the map `a ↦ a • x`. -/
def regularHomAddEquiv (A : Type u) [Ring A] (N : ModuleCat.{u} A) :
    (ModuleCat.of A A ⟶ N) ≃+ N where
  toFun f := f.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton A N x)
  left_inv f := ModuleCat.hom_ext (LinearMap.ext_ring (by simp))
  right_inv x := by simp
  map_add' f g := by simp

/-- The inverse of `regularHomAddEquiv A N` sends `x` to the map `a ↦ a • x`. -/
@[simp]
lemma regularHomAddEquiv_symm_apply (A : Type u) [Ring A] (N : ModuleCat.{u} A) (x : N) :
    (regularHomAddEquiv A N).symm x = ModuleCat.ofHom (LinearMap.toSpanSingleton A N x) :=
  rfl

/-- The map `a ↦ a • x` followed by `φ` is the map `a ↦ a • φ x`. -/
lemma regularHomAddEquiv_symm_comp (A : Type u) [Ring A] {N N' : ModuleCat.{u} A}
    (x : N) (φ : N ⟶ N') :
    (regularHomAddEquiv A N).symm x ≫ φ = (regularHomAddEquiv A N').symm (φ x) :=
  ModuleCat.hom_ext (LinearMap.ext_ring (by simp))

/-- **The corepresentation bijection of the free presheaf of modules on a representable is
evaluation at a tautological section**: `freeYonedaEquiv m` is the value of `m` over `X` at the
section corresponding to the identity. -/
lemma freeYonedaEquiv_eq_app {X : C} {M : PresheafOfModules.{u} R}
    (m : (free R).obj (yoneda.obj X) ⟶ M) :
    freeYonedaEquiv m =
      m.app (op X) (freeYonedaEquiv (𝟙 ((free R).obj (yoneda.obj X)))) := by
  conv_lhs => rw [← Category.id_comp m]
  rw [freeYonedaEquiv_comp]

/-- The corepresentation bijection is additive: it is the evaluation of a morphism at a fixed
section, and morphisms of presheaves of modules add on sections. -/
lemma freeYonedaEquiv_add {X : C} {M : PresheafOfModules.{u} R}
    (m m' : (free R).obj (yoneda.obj X) ⟶ M) :
    freeYonedaEquiv (m + m') = freeYonedaEquiv m + freeYonedaEquiv m' := by
  rw [freeYonedaEquiv_eq_app, freeYonedaEquiv_eq_app m, freeYonedaEquiv_eq_app m']
  simp

/-- **`PresheafOfModules.freeYonedaEquiv` as an additive equivalence onto the morphisms out of the
regular module of the ring of sections over `X`.** -/
def freeYonedaRegularHomAddEquiv (X : C) (M : PresheafOfModules.{u} R) :
    ((free R).obj (yoneda.obj X) ⟶ M) ≃+
      (ModuleCat.of (R.obj (op X)) (R.obj (op X)) ⟶ M.obj (op X)) :=
  (AddEquiv.mk' freeYonedaEquiv freeYonedaEquiv_add).trans
    (regularHomAddEquiv (R.obj (op X)) (M.obj (op X))).symm

/-- `freeYonedaRegularHomAddEquiv X M m` is the map `a ↦ a • freeYonedaEquiv m` out of the
regular module. -/
lemma freeYonedaRegularHomAddEquiv_apply (X : C) (M : PresheafOfModules.{u} R)
    (m : (free R).obj (yoneda.obj X) ⟶ M) :
    freeYonedaRegularHomAddEquiv X M m =
      (regularHomAddEquiv (R.obj (op X)) (M.obj (op X))).symm (freeYonedaEquiv m) :=
  rfl

/-- `freeYonedaRegularHomAddEquiv` is natural in the presheaf of modules: composing with `φ`
corresponds to composing with the component `φ.app (op X)`. -/
lemma freeYonedaRegularHomAddEquiv_comp (X : C) {M N : PresheafOfModules.{u} R}
    (m : (free R).obj (yoneda.obj X) ⟶ M) (φ : M ⟶ N) :
    freeYonedaRegularHomAddEquiv X N (m ≫ φ) =
      freeYonedaRegularHomAddEquiv X M m ≫ φ.app (op X) := by
  rw [freeYonedaRegularHomAddEquiv_apply, freeYonedaRegularHomAddEquiv_apply,
    regularHomAddEquiv_symm_comp, freeYonedaEquiv_comp]

/-- **The free presheaf of modules on a representable is a compact object.** Morphisms out of
`(free R).obj (yoneda.obj X)` are morphisms out of the regular module of `R(X)` into the sections
over `X`, and the sections over `X` of a direct sum of presheaves of modules form the direct sum
of the sections; so the compactness map of `(free R).obj (yoneda.obj X)` against a family is the
compactness map of the regular module against the family of sections over `X`, read through the
corepresentation bijections, and the regular module is compact. -/
theorem isCompactObject_freeYoneda (X : C) :
    IsCompactObject.{u} ((free R).obj (yoneda.obj X)) := by
  classical
  constructor
  intro I _ E _
  change Function.Bijective (cofanMap ((free R).obj (yoneda.obj X)) (Limits.Sigma.ι E))
  have hc : IsColimit (Cofan.mk ((∐ E).obj (op X))
      (fun i ↦ (Limits.Sigma.ι E i).app (op X))) :=
    isColimitMapCoconeCofanMkEquiv (evaluation R (op X)) E (Limits.Sigma.ι E)
      (isColimitOfPreserves _ (coproductIsCoproduct E))
  have hEq : ((freeYonedaRegularHomAddEquiv (R := R) X (∐ E)).toAddMonoidHom.comp
        (cofanMap ((free R).obj (yoneda.obj X)) (Limits.Sigma.ι E))) =
      (cofanMap (ModuleCat.of (R.obj (op X)) (R.obj (op X)))
          fun i ↦ (Limits.Sigma.ι E i).app (op X)).comp
        (DirectSum.map fun i ↦
          (freeYonedaRegularHomAddEquiv (R := R) X (E i)).toAddMonoidHom) := by
    refine DirectSum.addHom_ext fun i y ↦ ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, cofanMap_of, DirectSum.map_of,
      AddEquiv.coe_toAddMonoidHom]
    exact freeYonedaRegularHomAddEquiv_comp X y (Limits.Sigma.ι E i)
  refine ((freeYonedaRegularHomAddEquiv X (∐ E)).bijective.of_comp_iff' _).mp ?_
  rw [← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.coe_comp, hEq, AddMonoidHom.coe_comp]
  exact (bijective_cofanMap _ StacksDraft.Perfect.isCompactObject_regularModule _ hc).comp
    (bijective_directSumMap _ fun i ↦ (freeYonedaRegularHomAddEquiv X (E i)).bijective)

end PresheafOfModules

end
