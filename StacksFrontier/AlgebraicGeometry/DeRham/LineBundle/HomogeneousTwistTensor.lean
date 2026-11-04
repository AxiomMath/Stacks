module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Multiplication by a homogeneous function, as a map out of a tensor product

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. Multiplying a relative form on
`L^⋆` by the homogeneous function of a local section of `L^{⊗ n}` is `𝒪_X`-bilinear, so it is a
map

`(L^⋆ → X)_* Ω^p_{L^⋆/S} ⊗_{𝒪_X} L^{⊗ n} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`

of `𝒪_X`-modules. This file builds that map, which is the map clause (1) of Tag 0FUH is about:
the comparison of the degree-`n` part of the pushed-forward forms with the degree-zero part
twisted by `L^{⊗ n}` is its restriction to those parts.

## Main definitions

* `Stacks.LineBundle.Situation.pushforwardAt` and `Situation.tensorPowerAt`: the pushforward of
  the relative forms and the tensor power of the line bundle, read at the indexing of sheaves of
  modules that the tensor product of Tag 05NA is defined over.
* `Stacks.LineBundle.Situation.twistApp`: **multiplication by a homogeneous function over one
  open**, as a map out of the tensor product of the two modules of sections.
* `Stacks.LineBundle.Situation.twistPresheafHom`: the same over all opens at once, as a morphism
  out of the tensor product *presheaf*.
* `Stacks.LineBundle.Situation.twistHom`: **the multiplication map
  `(L^⋆ → X)_* Ω^p_{L^⋆/S} ⊗_{𝒪_X} L^{⊗ n} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`**, out of the tensor
  product sheaf, by the sheafification adjunction.

## Main results

* `Stacks.LineBundle.Situation.laurentSmul_mul`: multiplication by a product of functions is the
  composite of the two multiplications.
* `Stacks.LineBundle.Situation.twistApp_tmul` and `Situation.twistHom_tmul`: **the map is
  multiplication by the homogeneous function on a local pure tensor**, before and after
  sheafification. This is what identifies it with the comparison of clause (1).

## Implementation notes

The two factors are retyped by `id (α := ·)` before the tensor product is formed. The tensor
product of sheaves of modules is indexed by a presheaf of *commutative* rings — Mathlib's
monoidal structure on `PresheafOfModules` requires the ring presheaf to factor through
`CommRingCat` — so `PresheafOfModules D.X.ringCatSheaf.obj` carries no `MonoidalCategoryStruct`
and `⊗` does not elaborate at that spelling at all, even though it is the spelling the
pushforward and the tensor powers are built at. The two indexings are equal by `rfl` and `id` is
what moves a term between them; a type ascription does not, since instance search reads the
inferred type of the term.

The bilinear datum is the one of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwist`: additivity and
`𝒪_X(U)`-linearity in the form, and the same in the section, the latter through
`Situation.laurentFunctionOfOpen_add` and `Situation.laurentFunctionOfOpen_smul`. Naturality is
`Situation.laurentSmul_map` together with `Situation.laurentFunctionOfOpen_map`, checked on pure
tensors.

The assembly is split into one declaration per layer — the map over one open, the morphism of
presheaves, the morphism of sheaves — rather than written as a single term: the elaboration of
the retyped `tensorLift` and of the adjunction are independent, and splitting them keeps each
within budget.

## What clause (1) still needs

Clause (1) of Tag 0FUH is the assertion that `Situation.twistHom` above carries the degree-zero
part of the pushed-forward forms, twisted by `L^{⊗ n}`, isomorphically onto the degree-`n` part.
Three pieces of that remain, and the third was not visible until the map existed:

* **The degree-raising inclusion.** That `Situation.laurentSmul` of a homogeneous function of
  degree `n` carries `Ω^p_{L^⋆/S, m}` into `Ω^p_{L^⋆/S, n + m}`, for every section and over every
  open — not only for homogeneous forms over an affine one, which is
  `Situation.smul_mem_gradedLaurentForms`. The route is the induction principle
  `Situation.gradedLaurentForms_le_iff` against the sub-`𝒪_X`-module sheaf of sections whose
  product with a fixed homogeneous function lands in the degree-`(n + m)` part, whose membership
  is local by the `isSheaf` field of `SheafOfModules.Submodule`, with
  `Situation.isHomogeneousLaurentForm_map` moving a generator to a smaller affine open. It is
  also what corestricts `twistHom` to the two graded pieces, so it is needed before the
  comparison map of clause (1) can even be written.
* **The local bijectivity**, over the cover
  `Situation.exists_affine_trivializing_cover_over_affine`:
  injectivity because the twisting function is a unit there
  (`Situation.laurentGenUnit`), surjectivity by
  `Situation.isHomogeneousLaurentForm_of_smul_genInt`, and then
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`.
* **The sections of a tensor product over a trivializing open, in every integer degree.** The
  source of the comparison is a *sheafified* tensor product, so bijectivity on sections over an
  open asks what those sections are; over a trivializing open they are the sections of the other
  factor, tensored with the generator. That is
  `Stacks.AlgebraicGeometry.TwistGenerator.bijective_tensorSectionsAt_gen`, which is indexed by
  `ℕ`. The negative degrees need the same statement for
  `Stacks.AlgebraicGeometry.TwistGenerator.genInt`, which follows from its degree `-1` case by the
  composition the `ℕ`-indexed proof already uses, the degree `-1` case holding because
  multiplication by the degree `-1` generator is inverse to multiplication by the degree-one
  generator.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA), the tensor product of
  sheaves of modules
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- The pushforward `(L^⋆ → X)_* Ω^p_{L^⋆/S}`, read at the indexing of sheaves of modules over
which the tensor product of Tag 05NA is defined. -/
def Situation.pushforwardAt (p : ℤ) :
    _root_.SheafOfModules.{u} (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property) :=
  id (α := _root_.SheafOfModules.{u}
    (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property)) (D.laurentFormsPushforward p)

/-- The tensor power `L^{⊗ n}`, read at the same indexing. -/
def Situation.tensorPowerAt (n : ℤ) :
    _root_.SheafOfModules.{u} (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property) :=
  id (α := _root_.SheafOfModules.{u}
    (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property)) (D.tensorPower n)

/-- **Multiplication by a product of functions is the composite of the two
multiplications.** -/
theorem Situation.laurentSmul_mul (p : ℤ) (U : D.X.Opens)
    (g f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U (g * f) ω = D.laurentSmul p U g (D.laurentSmul p U f ω) :=
  mul_smul g f
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)

/-- The tensor product presheaf `(L^⋆ → X)_* Ω^p_{L^⋆/S} ⊗_{p,𝒪_X} L^{⊗ n}`, formed at the
indexing Mathlib's monoidal structure on presheaves of modules is defined over. The two factors
are retyped by `id (α := ·)` first, as the implementation notes above describe: `⊗` does not
elaborate at the indexing the pushforward and the tensor powers are built at, and the
sheafification adjunction takes its argument at a third, definitionally equal, spelling.

This is an elaboration boundary, not an abbreviation: the body forms the product at the indexing
that carries the monoidal instance, and the type carries the result back to the one the
adjunction consumes. Inlining it puts `⊗` under an expected type at which instance search finds
nothing, which is what made the upstream alias it replaces impossible to inline. A short body is
not evidence of redundancy here. -/
def Situation.twistTensorPresheaf (p n : ℤ) :
    PresheafOfModules.{u} (structureRingPresheaf D.X.sheaf.obj) :=
  id (α := PresheafOfModules.{u} (structureRingPresheaf D.X.sheaf.obj))
        (D.pushforwardAt p).val ⊗
      id (α := PresheafOfModules.{u} (structureRingPresheaf D.X.sheaf.obj))
        (D.tensorPowerAt n).val

/-- **Multiplication by the homogeneous function of a local section of `L^{⊗ n}`, over one
open**, as a map out of the tensor product of the sections of the pushed-forward forms with the
sections of `L^{⊗ n}`. -/
def Situation.twistApp (p n : ℤ) (U : (Opens D.X)ᵒᵖ) :
    (D.twistTensorPresheaf p n).obj U ⟶
      (D.pushforwardAt p).val.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun ω x => D.laurentSmul p U.unop (D.laurentFunctionOfOpen n U.unop x) ω)
    (fun ω₁ ω₂ x => D.laurentSmul_add p U.unop _ ω₁ ω₂)
    (fun r ω x => D.laurentSmul_smul p U.unop _ r ω)
    (fun ω x y => by
      refine Eq.trans (congrArg (fun h => D.laurentSmul p U.unop h ω)
        (D.laurentFunctionOfOpen_add n U.unop x y)) ?_
      exact D.add_laurentSmul p U.unop _ _ ω)
    (fun r ω x => by
      refine Eq.trans (congrArg (fun h => D.laurentSmul p U.unop h ω)
        (D.laurentFunctionOfOpen_smul n U.unop r x)) ?_
      refine Eq.trans (D.laurentSmul_mul p U.unop _ _ ω) ?_
      exact (D.smul_eq_laurentSmul p U.unop r _).symm)

/-- The map over one open is multiplication by the homogeneous function, on a pure tensor. -/
@[simp]
theorem Situation.twistApp_tmul (p n : ℤ) (U : (Opens D.X)ᵒᵖ)
    (ω : (D.pushforwardAt p).val.obj U) (x : (D.tensorPowerAt n).val.obj U) :
    (D.twistApp p n U).hom (ω ⊗ₜ x) =
      D.laurentSmul p U.unop (D.laurentFunctionOfOpen n U.unop x) ω :=
  rfl

/-- **Multiplication by the homogeneous functions of the local sections of `L^{⊗ n}`, over all
opens at once**: a morphism out of the tensor product presheaf. Naturality is the naturality of
the homogeneous functions together with that of the multiplication. -/
def Situation.twistPresheafHom (p n : ℤ) :
    D.twistTensorPresheaf p n ⟶
      (D.pushforwardAt p).val where
  app U := D.twistApp p n U
  naturality {U V} g := ModuleCat.MonoidalCategory.tensor_ext fun ω x =>
    ((D.laurentSmul_map p (leOfHom g.unop) (D.laurentFunctionOfOpen n U.unop x) ω).trans
      (congrArg (fun h => D.laurentSmul p V.unop h
        ((D.laurentFormsPushforward p).val.map g ω))
        (D.laurentFunctionOfOpen_map n (leOfHom g.unop) x))).symm

/-- **The multiplication map
`(L^⋆ → X)_* Ω^p_{L^⋆/S} ⊗_{𝒪_X} L^{⊗ n} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`** of quasi-coherent
`𝒪_X`-modules: multiplication of a relative form on `L^⋆` by the homogeneous function of a local
section of `L^{⊗ n}`, read on the tensor product sheaf of Tag 05NA through the sheafification
adjunction. Clause (1) of Tag 0FUH is the assertion that it carries the degree-zero part of the
forms, twisted by `L^{⊗ n}`, isomorphically onto the degree-`n` part. -/
def Situation.twistHom (p n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor D.X.sheaf).obj (D.pushforwardAt p)).obj
        (D.tensorPowerAt n) ⟶
      D.pushforwardAt p :=
  ((sheafifyAdjunction D.X.sheaf.obj D.X.ringCatSheaf.property).homEquiv
    (D.twistTensorPresheaf p n)
    (D.pushforwardAt p)).symm (D.twistPresheafHom p n)

/-- **Composing the sheafification unit with the multiplication map gives back the
multiplication of the forms by the homogeneous functions.** This is the unit triangle of the
sheafification adjunction at the morphism the map was defined from, and it characterizes the map
without any choice of local generator. -/
theorem Situation.toSheafify_comp_twistHom (p n : ℤ) :
    toSheafify D.X.sheaf.obj D.X.ringCatSheaf.property
          (D.twistTensorPresheaf p n) ≫
        (_root_.SheafOfModules.forget
              (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property).obj)).map
          (D.twistHom p n) =
      D.twistPresheafHom p n :=
  ((sheafifyAdjunction D.X.sheaf.obj D.X.ringCatSheaf.property).homEquiv_unit
    (f := D.twistHom p n)).symm.trans
    (((sheafifyAdjunction D.X.sheaf.obj D.X.ringCatSheaf.property).homEquiv
      (D.twistTensorPresheaf p n)
      (D.pushforwardAt p)).apply_symm_apply (D.twistPresheafHom p n))

/-- **The multiplication map is multiplication by the homogeneous function on a local pure
tensor.** This is `Stacks.LineBundle.Situation.toSheafify_comp_twistHom` read on sections, and
it is the form in which the comparison of clause (1) of Tag 0FUH computes. -/
theorem Situation.twistHom_toSheafify_tmul (p n : ℤ) (U : (Opens D.X)ᵒᵖ)
    (ω : (D.pushforwardAt p).val.obj U) (x : (D.tensorPowerAt n).val.obj U) :
    ((toSheafify D.X.sheaf.obj D.X.ringCatSheaf.property
            (D.twistTensorPresheaf p n) ≫
          (_root_.SheafOfModules.forget
                (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property) ⋙
              PresheafOfModules.restrictScalars
                (𝟙 (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property).obj)).map
            (D.twistHom p n)).app U).hom (ω ⊗ₜ x) =
      D.laurentSmul p U.unop (D.laurentFunctionOfOpen n U.unop x) ω :=
  (congrArg
      (fun (φ : D.twistTensorPresheaf p n ⟶
          (D.pushforwardAt p).val) => (φ.app U).hom (ω ⊗ₜ x))
      (D.toSheafify_comp_twistHom p n)).trans (D.twistApp_tmul p n U ω x)

end Stacks.LineBundle

end
