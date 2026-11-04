module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# An ideal killing a module kills it after transport along a product-preserving functor

Let `𝒪` be a sheaf of rings, `𝒢` an `𝒪`-module and `ℐ ⊆ 𝒪` an ideal with `ℐ · 𝒢 = 0`
sectionwise.  For a finite-product-preserving functor `P` from sheaves of sets to types, the
transported scalar multiplication of `CategoryTheory.Sheaf.moduleSMulObj` vanishes on the image of
`P(ℐ)`: an element of `P(𝒪)` coming from `P(ℐ)` acts by zero on `P(𝒢)`.

The case in view is the direct image of modules of Stacks 03D1, whose scalar action is exactly this
transported action, with `P` the direct image of sheaves of sets followed by sections over a chart.

## Main definitions

* `CategoryTheory.Sheaf.idealSetInclusion`: the inclusion of the underlying sheaf of sets of an
  ideal into that of the sheaf of rings.

## Main results

* `CategoryTheory.Sheaf.moduleSMulObj_map_idealSetInclusion_of_smul_eq_zero`: the vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Functor

universe w t v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- The inclusion of the underlying sheaf of sets of an ideal `ℐ ⊆ 𝒪` into the underlying sheaf of
sets of `𝒪`. -/
abbrev idealSetInclusion (I : (SheafOfModules.unit R).Submodule) :
    moduleSheaf R I.toSheafOfModules ⟶ ringSheaf R :=
  (moduleSheafFunctor R).map I.ι

variable (G : SheafOfModules.{w} R) (I : (SheafOfModules.unit R).Submodule)

/-- If `ℐ · 𝒢 = 0` sectionwise, scalar multiplication restricted to `ℐ` factors through the zero
section. -/
theorem idealSetInclusion_prodMap_moduleSMulHom
    (hI : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), r ∈ I.obj X → ∀ q : G.val.obj X, r • q = 0) :
    prod.map (idealSetInclusion R I) (𝟙 _) ≫ moduleSMulHom R G =
      terminal.from _ ≫ moduleZeroHom R G := by
  refine hom_ext_sections (fun X s => ?_)
  rw [← prodObjMk_map_fst_map_snd (P := sectionsFunctor J X) s, Functor.map_comp_apply,
    Functor.map_comp_apply, map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    sectionsFunctor_map_moduleSMulHom, sectionsFunctor_map_moduleZeroHom]
  set a := (sectionsFunctor J X).map prod.fst s
  exact hI X _ a.2 _

variable (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- **An ideal killing a module kills it after transport**: if `ℐ · 𝒢 = 0` sectionwise, then an
element of `P(𝒪)` coming from `P(ℐ)` acts by zero on `P(𝒢)`. -/
theorem moduleSMulObj_map_idealSetInclusion_of_smul_eq_zero
    (hI : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), r ∈ I.obj X → ∀ q : G.val.obj X, r • q = 0)
    (k : P.obj (moduleSheaf R I.toSheafOfModules)) (x : P.obj (moduleSheaf R G)) :
    moduleSMulObj R G P (P.map (idealSetInclusion R I) k) x = moduleZeroObj R G P := by
  have h1 : prodObjMk (P := P) (P.map (idealSetInclusion R I) k) x =
      P.map (prod.map (idealSetInclusion R I) (𝟙 _)) (prodObjMk k x) := by
    rw [map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk, P.map_id, types_id_apply]
  rw [moduleSMulObj, h1, ← Functor.map_comp_apply,
    idealSetInclusion_prodMap_moduleSMulHom R G I hI, Functor.map_comp_apply, moduleZeroObj]
  congr 1
  exact Subsingleton.elim _ _

end CategoryTheory.Sheaf
