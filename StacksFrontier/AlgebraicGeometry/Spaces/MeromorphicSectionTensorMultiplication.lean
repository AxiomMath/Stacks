module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRingTensorSpelling
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite

/-!
# The product of two meromorphic sections over a chart

Let `X` be an algebraic space over a scheme `S` and let `ℒ` and `𝒩` be `𝒪_X`-modules. Over an
étale scheme chart `V` the meromorphic sections of `ℒ` before sheafification are
`𝒦_X(V) ⊗_{𝒪_X(V)} ℒ(V)`, and this file constructs their **product**

`(a ⊗ l, b ⊗ n) ↦ (ab) ⊗ (l ⊗ n)`,

a meromorphic section of `ℒ ⊗_{𝒪_X} 𝒩` over `V` before sheafification. This is the chartwise
half of the algebraic-space analogue of Stacks 02SL, the product of two meromorphic sections;
the scheme-level construction `AlgebraicGeometry.tensorMeromorphicSection` instead multiplies
in the stalk at the generic point, through Stacks 01X5 part (2), which has no analogue on an
algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.tensorChartSection` is the image of `l ⊗ n` in the sections of
  `ℒ ⊗_{𝒪_X} 𝒩` over `V`, that is the sheafification unit of the tensor product presheaf.
* `AlgebraicGeometry.Space.meromorphicSectionTensorMul` is the product above.

## Main results

* `AlgebraicGeometry.Space.meromorphicSectionTensorMul_tmul`: the product carries
  `(a ⊗ l, b ⊗ n)` to `(ab) ⊗ (l ⊗ n)`.  This is what makes it the product of Stacks 02SL and
  not merely some bilinear map.
* `AlgebraicGeometry.Space.meromorphicSectionTensorMul_add_left`,
  `AlgebraicGeometry.Space.meromorphicSectionTensorMul_add_right`,
  `AlgebraicGeometry.Space.meromorphicSectionTensorMul_zero_left` and
  `AlgebraicGeometry.Space.meromorphicSectionTensorMul_zero_right`: the product is additive in
  each argument, being a linear map applied to `x ⊗ y`.
* `AlgebraicGeometry.Space.tensorChartSection_map` and
  `AlgebraicGeometry.Space.meromorphicSectionTensorMul_map`: **both products are compatible with
  restriction.**  This is what makes the chartwise product a matching family, and so the input
  of an amalgamation over an affine covering: over an affine chart the sheafification map of
  Stacks 0EN5 is bijective, so the product of two global meromorphic sections is honest there,
  and this is the compatibility that the sheaf condition then consumes.
* `AlgebraicGeometry.Space.bijective_smul_tensorChartSection`: **the product of two free
  generators is a free generator.**  If a section of `ℒ` and a section of `𝒩` each generate
  freely over every chart over `V`, then their product generates `ℒ ⊗_{𝒪_X} 𝒩` freely over every
  chart over `V`.  This is what reads a presentation of a meromorphic section of `ℒ ⊗ 𝒩` against
  a generator, and the hypothesis `hbij` of
  `AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit` for the product.

## Implementation notes

The product is the composite of two maps: the comparison of extension of scalars with the
tensor product,
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorAppIso` over Stacks 03CU, whose
inverse carries `(a ⊗ l) ⊗ (b ⊗ n)` to `(ab) ⊗ (l ⊗ n)` by
`TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul`, followed by the sheafification
unit of the tensor product presheaf tensored with `𝒦_X(V)`.

The tensor product of `𝒪_X`-modules is `AlgebraicGeometry.Space.picardTensorModule`, the
spelling in which addition of Picard classes is tensor product, so that this is a product of
meromorphic sections of the module the construction of Stacks 0EPW uses.

Every ring of regular functions is spelled `AlgebraicGeometry.Space.tensorChartRing` and the
module structures over it are the local instances `AlgebraicGeometry.Space.tensorChartModule`,
`AlgebraicGeometry.Space.tensorChartMeromorphicAlgebra` and
`AlgebraicGeometry.Space.tensorChartMeromorphicSectionModule`: the four definitionally equal
spellings of `𝒪_X(V)` in this development are not bridged by instance search, and a lemma
*statement* — unlike a definition with an ascribed result type — has no expected type from
which the instances can propagate.

Both the module universe and the universe of the structure rings are the universe `u` of the
schemes: this is the presheaf of meromorphic sections *before* the universe lift that
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` performs, and
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorAppIso` ties the two universes to
one another.

That is also why the tensor product of the *sheaves* `𝒦_X(ℒ)` and `𝒦_X(𝒩)` is not used:
`Stacks.SheafOfModules.TensorSheafification` fixes the module universe to the universe of the
structure rings, while `AlgebraicGeometry.Space.meromorphicSectionSheaf` has sections one
universe higher than its rings.

*Why freeness of the product is proved here and not read off the site.*
`Stacks.Cohomology.Torsors.Generators.tensorSection_bijective` is the same statement on a ringed
site, and it cannot be used: its proof descends an isomorphism of presheaves along the sheaf
condition for **type-valued** presheaves on the slice site, which forces the universe of the
module sections to dominate the universe of the objects of the site, i.e. `u ≥ u + 1` on the
small étale ringed site `AlgebraicGeometry.RingedSite.{u + 1, u, u}` of an algebraic space.  Its
pure-algebra ingredient `Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective` carries no
such constraint and is reused verbatim; what that ingredient gives is freeness of `l ⊗ n` in the
tensor product *presheaf* `ℒ(W) ⊗_{𝒪_X(W)} 𝒩(W)`, and the step from there to the tensor product
*sheaf* — whose sections over `V` are the sheafification of that presheaf — is the local
bijectivity of the sheafification unit together with the sheaf condition for `𝒪_X` and for
`ℒ ⊗_{𝒪_X} 𝒩`, which is what the four declarations below the product supply.  The slice site is
never mentioned: the covering sieves are taken over `V` itself.

The inverse of the comparison is taken on Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange` rather than on
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorAppIso`, which is that equivalence
read as an isomorphism of `ModuleCat`s: the categorical packaging carries a `letI` for the
algebra structure in its body, so unfolding it in a goal leaves a `let` that `simp` does not
push through, while the closed form below is two steps away from the underlying equivalence.

## References

* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.SheafOfModules.TensorSheafification
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] tensorChartModule
attribute [local instance] tensorChartMeromorphicAlgebra
attribute [local instance] tensorChartMeromorphicSectionModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (L N : Modules.{u, u} B S hS X hX) (V : SmallEtale B S hS X)

/-- **The product of two sections of `𝒪_X`-modules over a chart.**  The image of `l ⊗ n` under
the sheafification unit of the tensor product presheaf, a section of `ℒ ⊗_{𝒪_X} 𝒩` over `V`. -/
def tensorChartSection (l : L.val.obj (op V)) (n : N.val.obj (op V)) :
    (picardTensorModule B S hS hX L N).val.obj (op V) :=
  ((toSheafify (structureSheaf B S hS X hX).obj
    (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op V)).hom
      (l ⊗ₜ[tensorChartRing B S hS X hX V] n)

/-- **The product of two meromorphic sections over a chart**, before sheafification: the
meromorphic section `(ab) ⊗ (l ⊗ n)` of `ℒ ⊗_{𝒪_X} 𝒩` attached to `a ⊗ l` and `b ⊗ n`. -/
def meromorphicSectionTensorMul
    (x : (meromorphicSectionModule B S hS X hX L).obj (op V))
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    (meromorphicSectionModule B S hS X hX (picardTensorModule B S hS hX L N)).obj (op V) :=
  LinearMap.lTensor ((meromorphicChartSheaf B S hS X hX).obj.obj (op V))
      ((toSheafify (structureSheaf B S hS X hX).obj
        (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op V)).hom
    ((TensorProduct.AlgebraTensorModule.distribBaseChange
        (tensorChartRing B S hS X hX V)
        ((meromorphicChartSheaf B S hS X hX).obj.obj (op V))
        (L.val.obj (op V)) (N.val.obj (op V))).symm
      (x ⊗ₜ[(meromorphicChartSheaf B S hS X hX).obj.obj (op V)] y))

/-- **The product of two meromorphic sections in closed form.**  The meromorphic sections
`a ⊗ l` of `ℒ` and `b ⊗ n` of `𝒩` over a chart have product `(ab) ⊗ (l ⊗ n)`.  This is what
makes the construction above the product of Stacks 02SL and not merely some bilinear map.

The two steps are `TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul` and
`LinearMap.lTensor_tmul`, the two halves of the definition.  They are assembled with `congrArg`
and `Eq.trans`, which decide definitional equality, rather than with `rw`, whose keyed matching
does not see through the spellings of `𝒪_X(V)` behind `AlgebraicGeometry.Space.tensorChartRing`:
after the definition is unfolded the chart has to be read as an object of
`(smallEtaleRingedSite B S hS X hX).C`, which is definitionally true but not true at the
transparency `rw` works at. -/
theorem meromorphicSectionTensorMul_tmul
    (a b : (meromorphicChartSheaf B S hS X hX).obj.obj (op V))
    (l : L.val.obj (op V)) (n : N.val.obj (op V)) :
    meromorphicSectionTensorMul B S hS hX L N V
        (a ⊗ₜ[tensorChartRing B S hS X hX V] l) (b ⊗ₜ[tensorChartRing B S hS X hX V] n) =
      (a * b) ⊗ₜ[tensorChartRing B S hS X hX V] tensorChartSection B S hS hX L N V l n :=
  (congrArg
      (fun z => LinearMap.lTensor ((meromorphicChartSheaf B S hS X hX).obj.obj (op V))
        ((toSheafify (structureSheaf B S hS X hX).obj
          (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op V)).hom z)
      (TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul
        (tensorChartRing B S hS X hX V)
        ((meromorphicChartSheaf B S hS X hX).obj.obj (op V)) l n a b)).trans
    (LinearMap.lTensor_tmul _ _ _ _)

/-- **The product of two sections over a chart is compatible with restriction.**  The
sheafification unit of the tensor product presheaf is a morphism of presheaves of modules, and
the restriction maps of the tensor product presheaf carry `l ⊗ n` to the tensor of the
restrictions. -/
theorem tensorChartSection_map (W : SmallEtale B S hS X) (k : W ⟶ V)
    (l : L.val.obj (op V)) (n : N.val.obj (op V)) :
    ((picardTensorModule B S hS hX L N).val.map k.op).hom
        (tensorChartSection B S hS hX L N V l n) =
      tensorChartSection B S hS hX L N W ((L.val.map k.op).hom l) ((N.val.map k.op).hom n) :=
  (PresheafOfModules.naturality_apply (toSheafify (structureSheaf B S hS X hX).obj
    (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)) k.op
      (l ⊗ₜ[tensorChartRing B S hS X hX V] n)).symm

/-- The product of two meromorphic sections as an additive map out of the tensor product. -/
private def tensorMulAddHom :
    ((meromorphicSectionModule B S hS X hX L).obj (op V) ⊗[
        (meromorphicChartSheaf B S hS X hX).obj.obj (op V)]
      (meromorphicSectionModule B S hS X hX N).obj (op V)) →+
    (meromorphicSectionModule B S hS X hX (picardTensorModule B S hS hX L N)).obj (op V) :=
  (LinearMap.lTensor ((meromorphicChartSheaf B S hS X hX).obj.obj (op V))
      ((toSheafify (structureSheaf B S hS X hX).obj
        (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op V)).hom
    ).toAddMonoidHom.comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange
        (tensorChartRing B S hS X hX V)
        ((meromorphicChartSheaf B S hS X hX).obj.obj (op V))
        (L.val.obj (op V)) (N.val.obj (op V))).symm.toAddMonoidHom

/-- **The product of two meromorphic sections over a chart is additive in the first
argument.**  The product is a linear map applied to `x ⊗ y`, so it is additive in each
argument separately.

Assembled with `congrArg` and `Eq.trans` rather than with `rw`, for the reason recorded on
`AlgebraicGeometry.Space.meromorphicSectionTensorMul_tmul`. -/
theorem meromorphicSectionTensorMul_add_left
    (x x' : (meromorphicSectionModule B S hS X hX L).obj (op V))
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    meromorphicSectionTensorMul B S hS hX L N V (x + x') y =
      meromorphicSectionTensorMul B S hS hX L N V x y +
        meromorphicSectionTensorMul B S hS hX L N V x' y :=
  (congrArg (tensorMulAddHom B S hS hX L N V) (TensorProduct.add_tmul x x' y)).trans
    (map_add _ _ _)

/-- **The product of two meromorphic sections over a chart is additive in the second
argument.** -/
theorem meromorphicSectionTensorMul_add_right
    (x : (meromorphicSectionModule B S hS X hX L).obj (op V))
    (y y' : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    meromorphicSectionTensorMul B S hS hX L N V x (y + y') =
      meromorphicSectionTensorMul B S hS hX L N V x y +
        meromorphicSectionTensorMul B S hS hX L N V x y' :=
  (congrArg (tensorMulAddHom B S hS hX L N V) (TensorProduct.tmul_add x y y')).trans
    (map_add _ _ _)

/-- The product of two meromorphic sections over a chart vanishes when the first factor does. -/
theorem meromorphicSectionTensorMul_zero_left
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    meromorphicSectionTensorMul B S hS hX L N V 0 y = 0 :=
  (congrArg (tensorMulAddHom B S hS hX L N V) (TensorProduct.zero_tmul _ y)).trans
    (map_zero _)

/-- The product of two meromorphic sections over a chart vanishes when the second factor
does. -/
theorem meromorphicSectionTensorMul_zero_right
    (x : (meromorphicSectionModule B S hS X hX L).obj (op V)) :
    meromorphicSectionTensorMul B S hS hX L N V x 0 = 0 :=
  (congrArg (tensorMulAddHom B S hS hX L N V) (TensorProduct.tmul_zero _ x)).trans
    (map_zero _)

/-- **The product of a pure meromorphic section with any meromorphic section is compatible with
restriction.**  This is the case `x = a ⊗ l` of
`AlgebraicGeometry.Space.meromorphicSectionTensorMul_map`, proved by induction on the second
factor; it is split off so that the induction hypothesis is stated at the first factor `a ⊗ l`
rather than at an element whose type has been unfolded by the induction tactic.

Each branch is assembled with `congrArg` and `Eq.trans` rather than with a rewrite, for the
reason recorded on `AlgebraicGeometry.Space.meromorphicSectionTensorMul_tmul`:
`TensorProduct.induction_on` unfolds the module to the underlying tensor product, and neither
`rw` nor `simp` finds the zero, the sum or the tensor it then puts into the goal. -/
theorem meromorphicSectionTensorMul_map_tmul (W : SmallEtale B S hS X) (k : W ⟶ V)
    (a : (meromorphicChartSheaf B S hS X hX).obj.obj (op V)) (l : L.val.obj (op V))
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    ((meromorphicSectionModule B S hS X hX (picardTensorModule B S hS hX L N)).map k.op).hom
        (meromorphicSectionTensorMul B S hS hX L N V
          (a ⊗ₜ[tensorChartRing B S hS X hX V] l) y) =
      meromorphicSectionTensorMul B S hS hX L N W
        (((meromorphicSectionModule B S hS X hX L).map k.op).hom
          (a ⊗ₜ[tensorChartRing B S hS X hX V] l :
            (meromorphicSectionModule B S hS X hX L).obj (op V)))
        (((meromorphicSectionModule B S hS X hX N).map k.op).hom y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    erw [meromorphicSectionTensorMul_zero_right, map_zero, map_zero,
      meromorphicSectionTensorMul_zero_right]
    rfl
  | tmul b n =>
    exact ((congrArg
        (fun z => ((meromorphicSectionModule B S hS X hX
            (picardTensorModule B S hS hX L N)).map k.op).hom z)
        (meromorphicSectionTensorMul_tmul B S hS hX L N V a b l n)).trans
      ((meromorphicSectionModule_map_tmul B S hS X hX (picardTensorModule B S hS hX L N) V W k
          (a * b) (tensorChartSection B S hS hX L N V l n)).trans
        ((congrArg (fun z => ((((Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom
                (a * b)) ⊗ₜ[tensorChartRing B S hS X hX W] z :
              (meromorphicSectionModule B S hS X hX
                (picardTensorModule B S hS hX L N)).obj (op W)))
            (tensorChartSection_map B S hS hX L N V W k l n)).trans
          ((congrArg (fun z => ((z ⊗ₜ[tensorChartRing B S hS X hX W]
                  tensorChartSection B S hS hX L N W ((L.val.map k.op).hom l)
                    ((N.val.map k.op).hom n)) :
                (meromorphicSectionModule B S hS X hX
                  (picardTensorModule B S hS hX L N)).obj (op W)))
              (map_mul ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom
                a b)).trans
            ((meromorphicSectionTensorMul_tmul B S hS hX L N W
                (((Stacks.SheafOfModules.Tensor.ringSheaf
                    (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom a)
                (((Stacks.SheafOfModules.Tensor.ringSheaf
                    (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom b)
                ((L.val.map k.op).hom l) ((N.val.map k.op).hom n)).symm.trans
              ((congrArg (fun z => meromorphicSectionTensorMul B S hS hX L N W z
                    (((((Stacks.SheafOfModules.Tensor.ringSheaf
                        (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom b)
                        ⊗ₜ[tensorChartRing B S hS X hX W] ((N.val.map k.op).hom n)) :
                      (meromorphicSectionModule B S hS X hX N).obj (op W)))
                  (meromorphicSectionModule_map_tmul B S hS X hX L V W k a l).symm).trans
                (congrArg (fun z => meromorphicSectionTensorMul B S hS hX L N W
                    (((meromorphicSectionModule B S hS X hX L).map k.op).hom
                      (a ⊗ₜ[tensorChartRing B S hS X hX V] l :
                        (meromorphicSectionModule B S hS X hX L).obj (op V))) z)
                  (meromorphicSectionModule_map_tmul B S hS X hX N V W k b n).symm)))))))
  | add y y' hy hy' =>
    erw [meromorphicSectionTensorMul_add_right, map_add]
    rw [hy, hy']
    erw [map_add]
    exact (meromorphicSectionTensorMul_add_right B S hS hX L N W _ _ _).symm

/-- **The product of two meromorphic sections over a chart is compatible with
restriction.**  Restricting the product to a chart `W` over `V` is the product of the
restrictions.

This is what makes the chartwise product a *matching family*, and so the input of an
amalgamation over an affine covering: over an affine chart the sheafification map of Stacks 0EN5
is bijective, and this is the compatibility that the sheaf condition consumes.

The branches are assembled with `congrArg` and `Eq.trans` for the reason recorded on
`AlgebraicGeometry.Space.meromorphicSectionTensorMul_map_tmul`. -/
theorem meromorphicSectionTensorMul_map (W : SmallEtale B S hS X) (k : W ⟶ V)
    (x : (meromorphicSectionModule B S hS X hX L).obj (op V))
    (y : (meromorphicSectionModule B S hS X hX N).obj (op V)) :
    ((meromorphicSectionModule B S hS X hX (picardTensorModule B S hS hX L N)).map k.op).hom
        (meromorphicSectionTensorMul B S hS hX L N V x y) =
      meromorphicSectionTensorMul B S hS hX L N W
        (((meromorphicSectionModule B S hS X hX L).map k.op).hom x)
        (((meromorphicSectionModule B S hS X hX N).map k.op).hom y) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    erw [meromorphicSectionTensorMul_zero_left, map_zero, map_zero,
      meromorphicSectionTensorMul_zero_left]
    rfl
  | tmul a l => exact meromorphicSectionTensorMul_map_tmul B S hS hX L N V W k a l y
  | add x x' hx hx' =>
    erw [meromorphicSectionTensorMul_add_left, map_add]
    rw [hx, hx']
    erw [map_add]
    exact (meromorphicSectionTensorMul_add_left B S hS hX L N W _ _ _).symm

/-! ### The product of two free generators is a free generator -/

/-- **A scalar multiple on the left factor multiplies the product of two sections.**  The
sheafification unit of the tensor product presheaf is linear and `r • (l ⊗ n) = (r • l) ⊗ n`, so
the two statements are the same one. -/
theorem tensorChartSection_smul_left (W : SmallEtale B S hS X)
    (r : chartRing B S hS X hX W) (l : L.val.obj (op W)) (n : N.val.obj (op W)) :
    tensorChartSection B S hS hX L N W (r • l) n =
      r • tensorChartSection B S hS hX L N W l n :=
  ((toSheafify (structureSheaf B S hS X hX).obj
      (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op W)).hom.map_smul
    (r : tensorChartRing B S hS X hX W)
    (l ⊗ₜ[tensorChartRing B S hS X hX W] n : (L.val ⊗ N.val).obj (op W))

/-- **Restriction of a pure tensor in the tensor product presheaf.**  The restriction maps of
the tensor product presheaf of Stacks 05NA are the maps of a tensor product of restrictions, so
`l ⊗ n` restricts to the tensor of the restrictions.

The restricted sections are passed as the values `l'` and `n'` together with the equations
defining them, rather than written out: the codomain of a restriction map of a presheaf of
modules is a restriction of scalars, and a tensor written by hand over that type has no module
instance that instance search finds.  This is the idiom of
`AlgebraicGeometry.Space.meromorphicSectionModule_smul_tmul`. -/
theorem tensorChartPresheaf_map_tmul (W Z : SmallEtale B S hS X) (g : Z ⟶ W)
    (l : L.val.obj (op W)) (n : N.val.obj (op W))
    (l' : L.val.obj (op Z)) (n' : N.val.obj (op Z))
    (hl : (L.val.map g.op).hom l = l') (hn : (N.val.map g.op).hom n = n') :
    ((L.val ⊗ N.val).map g.op).hom
        (l ⊗ₜ[tensorChartRing B S hS X hX W] n : (L.val ⊗ N.val).obj (op W)) =
      (l' ⊗ₜ[tensorChartRing B S hS X hX Z] n' : (L.val ⊗ N.val).obj (op Z)) :=
  (congrArg (fun z : L.val.obj (op Z) ↦
      (z ⊗ₜ[tensorChartRing B S hS X hX Z] (N.val.map g.op).hom n :
        (L.val ⊗ N.val).obj (op Z))) hl).trans
    (congrArg (fun z : N.val.obj (op Z) ↦
      (l' ⊗ₜ[tensorChartRing B S hS X hX Z] z :
        (L.val ⊗ N.val).obj (op Z))) hn)

/-- **Restriction of a scalar multiple of a section of an `𝒪_X`-module.**  The restriction maps
of a presheaf of modules are semilinear, so the restriction of `x • l` is the restriction of `x`
times the restriction of `l`.

This is `CategoryTheory.PresheafOfModules.map_smul` with the two restricted values passed as
hypotheses, for the reason recorded on
`AlgebraicGeometry.Space.tensorChartPresheaf_map_tmul`: the scalar multiplication on the
codomain of a restriction map cannot be written by hand. -/
theorem map_smul_chartSection (W Z : SmallEtale B S hS X) (g : Z ⟶ W)
    (x : chartRing B S hS X hX W) (y : chartRing B S hS X hX Z)
    (hy : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X hX).O).obj.map g.op).hom x = y)
    (l : L.val.obj (op W)) (l' : L.val.obj (op Z))
    (hl : (L.val.map g.op).hom l = l') :
    (L.val.map g.op).hom (x • l) = (y • l' : L.val.obj (op Z)) := by
  subst hy
  subst hl
  exact L.val.map_smul g.op x l

/-- **The sheafification unit of the tensor product presheaf is locally injective.**  Two
sections of `ℒ ⊗_{p, 𝒪_X} 𝒩` over a chart with the same image in `ℒ ⊗_{𝒪_X} 𝒩` agree on a
covering of that chart: a sheafification map is a local equivalence, and on the small étale site
the local equivalences of concrete presheaves are the locally bijective morphisms. -/
theorem isLocallyInjective_toSheafify_tensorPresheaf :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X)
      ((PresheafOfModules.toPresheaf _).map
        (toSheafify (structureSheaf B S hS X hX).obj
          (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val))) := by
  show Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X)
    (CategoryTheory.toSheafify (SmallEtale.topology B S hS X) (L.val ⊗ N.val).presheaf)
  exact ((SmallEtale.topology B S hS X).W_toSheafify _).isLocallyInjective

/-- **The sheafification unit of the tensor product presheaf is locally surjective.**  Every
section of `ℒ ⊗_{𝒪_X} 𝒩` over a chart is, on a covering of that chart, the image of a section of
the tensor product presheaf.  The companion of
`AlgebraicGeometry.Space.isLocallyInjective_toSheafify_tensorPresheaf`, proved the same
way. -/
theorem isLocallySurjective_toSheafify_tensorPresheaf :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X)
      ((PresheafOfModules.toPresheaf _).map
        (toSheafify (structureSheaf B S hS X hX).obj
          (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val))) := by
  show Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X)
    (CategoryTheory.toSheafify (SmallEtale.topology B S hS X) (L.val ⊗ N.val).presheaf)
  exact ((SmallEtale.topology B S hS X).W_toSheafify _).isLocallySurjective

variable (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (f : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))

/-- **Multiplication by the product of two free generators is injective.**  Let `e` and `f` be
families of sections of `ℒ` and of `𝒩` over the charts over `V`, compatible with restriction and
each generating freely over every one of them.  Then over every chart over `V` multiplication by
the product of the two is injective on the regular functions.

The sheaf `ℒ ⊗_{𝒪_X} 𝒩` is a sheafification, so two multiples of the product that agree there
agree in the tensor product presheaf only over a covering sieve
(`AlgebraicGeometry.Space.isLocallyInjective_toSheafify_tensorPresheaf`).  Over a member of that
sieve the two restricted generators are still free, so
`Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective` — pure algebra over the regular
functions there — makes the two restricted scalars equal, and `𝒪_X` being separated they were
equal to begin with. -/
theorem injective_smul_tensorChartSection
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (hfbij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • f W k)
    (W : SmallEtale B S hS X) (k : W ⟶ V) :
    Function.Injective fun r : chartRing B S hS X hX W ↦
      r • tensorChartSection B S hS hX L N W (e W k) (f W k) := by
  have := isLocallyInjective_toSheafify_tensorPresheaf B S hS hX L N
  intro r r' hr
  have hr' : tensorChartSection B S hS hX L N W (r • e W k) (f W k) =
      tensorChartSection B S hS hX L N W (r' • e W k) (f W k) :=
    ((tensorChartSection_smul_left B S hS hX L N W r (e W k) (f W k)).trans hr).trans
      (tensorChartSection_smul_left B S hS hX L N W r' (e W k) (f W k)).symm
  have hT := Presheaf.equalizerSieve_mem (SmallEtale.topology B S hS X)
    ((PresheafOfModules.toPresheaf _).map (toSheafify (structureSheaf B S hS X hX).obj
      (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)))
    (((r • e W k) ⊗ₜ[tensorChartRing B S hS X hX W] f W k :
      (L.val ⊗ N.val).obj (op W)))
    (((r' • e W k) ⊗ₜ[tensorChartRing B S hS X hX W] f W k :
      (L.val ⊗ N.val).obj (op W))) hr'
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X hX).O).property.isSeparated W _ hT r r' ?_
  intro Z g hg
  have hres := fun s : chartRing B S hS X hX W ↦
    tensorChartPresheaf_map_tmul B S hS hX L N W Z g (s • e W k) (f W k)
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X hX).O).obj.map g.op).hom s • e Z (g ≫ k))
      (f Z (g ≫ k)) (map_smul_chartSection B S hS hX L W Z g s _ rfl (e W k) (e Z (g ≫ k))
        (hecompat W Z k g)) (hfcompat W Z k g)
  exact (Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective
      (R := chartRing B S hS X hX Z) (e Z (g ≫ k)) (f Z (g ≫ k))
      (hebij Z (g ≫ k)) (hfbij Z (g ≫ k))).1
    (((hres r).symm.trans hg).trans (hres r'))

/-- **The products of two compatible families of sections form a compatible family.**  The
product over a chart over `V`, restricted to a chart over it, is the product of the two
restrictions, which the compatibility of the two families identifies with the product attached
to the smaller chart. -/
theorem tensorChartSection_restrict_family
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (W : SmallEtale B S hS X) (k : W ⟶ V) (Z : SmallEtale B S hS X) (g : Z ⟶ W) :
    ((picardTensorModule B S hS hX L N).val.map g.op).hom
        (tensorChartSection B S hS hX L N W (e W k) (f W k)) =
      tensorChartSection B S hS hX L N Z (e Z (g ≫ k)) (f Z (g ≫ k)) :=
  (tensorChartSection_map B S hS hX L N W Z g (e W k) (f W k)).trans
    ((congrArg (fun w : L.val.obj (op Z) ↦
        tensorChartSection B S hS hX L N Z w ((N.val.map g.op).hom (f W k)))
      (hecompat W Z k g)).trans
      (congrArg (fun w : N.val.obj (op Z) ↦
        tensorChartSection B S hS hX L N Z (e Z (g ≫ k)) w) (hfcompat W Z k g)))

/-- **Restriction of a multiple of the product of two free generators.**  The restriction maps
of `ℒ ⊗_{𝒪_X} 𝒩` are semilinear and the products form a compatible family, so a multiple of the
product attached to a chart restricts to the corresponding multiple of the product attached to a
chart over it. -/
theorem smul_tensorChartSection_restrict
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (W : SmallEtale B S hS X) (k : W ⟶ V) (Z : SmallEtale B S hS X) (g : Z ⟶ W)
    (y : chartRing B S hS X hX W) (y' : chartRing B S hS X hX Z)
    (hy : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X hX).O).obj.map g.op).hom y = y') :
    ((picardTensorModule B S hS hX L N).val.map g.op).hom
        (y • tensorChartSection B S hS hX L N W (e W k) (f W k)) =
      (y' • tensorChartSection B S hS hX L N Z (e Z (g ≫ k)) (f Z (g ≫ k)) :
        (picardTensorModule B S hS hX L N).val.obj (op Z)) :=
  map_smul_chartSection B S hS hX (picardTensorModule B S hS hX L N) W Z g y y' hy
    (tensorChartSection B S hS hX L N W (e W k) (f W k))
    (tensorChartSection B S hS hX L N Z (e Z (g ≫ k)) (f Z (g ≫ k)))
    (tensorChartSection_restrict_family B S hS hX L N V e f hecompat hfcompat W k Z g)

/-- **A section of `ℒ ⊗_{𝒪_X} 𝒩` over a chart is a multiple of the product of two free
generators over a covering sieve of that chart.**  The tensor product sheaf is a sheafification,
so a section of it over a chart is the image of a section of the tensor product presheaf only
over the members of a covering sieve
(`AlgebraicGeometry.Space.isLocallySurjective_toSheafify_tensorPresheaf`); over each of them
`Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective` presents that section of the
presheaf as a multiple of the product of the two restricted generators. -/
theorem exists_sieve_smul_tensorChartSection_eq
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (hfbij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • f W k)
    (W : SmallEtale B S hS X) (k : W ⟶ V)
    (z : (picardTensorModule B S hS hX L N).val.obj (op W)) :
    ∃ T : Sieve W, T ∈ SmallEtale.topology B S hS X W ∧
      ∀ ⦃Z : SmallEtale B S hS X⦄ (g : Z ⟶ W), T g →
        ∃ y : chartRing B S hS X hX Z,
          (y • tensorChartSection B S hS hX L N Z (e Z (g ≫ k)) (f Z (g ≫ k)) :
              (picardTensorModule B S hS hX L N).val.obj (op Z)) =
            ((picardTensorModule B S hS hX L N).val.map g.op).hom z := by
  have := isLocallySurjective_toSheafify_tensorPresheaf B S hS hX L N
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map
      (toSheafify (structureSheaf B S hS X hX).obj
        (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val))) z,
    Presheaf.imageSieve_mem (SmallEtale.topology B S hS X)
      ((PresheafOfModules.toPresheaf _).map
        (toSheafify (structureSheaf B S hS X hX).obj
          (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val))) (U := op W) z, ?_⟩
  intro Z g hg
  obtain ⟨ζ, hζ⟩ := hg
  obtain ⟨y, hy⟩ := (Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective
    (R := chartRing B S hS X hX Z) (e Z (g ≫ k)) (f Z (g ≫ k))
    (hebij Z (g ≫ k)) (hfbij Z (g ≫ k))).2 ζ
  refine ⟨y, ?_⟩
  refine Eq.trans (tensorChartSection_smul_left B S hS hX L N Z y
    (e Z (g ≫ k)) (f Z (g ≫ k))).symm ?_
  exact (congrArg ((toSheafify (structureSheaf B S hS X hX).obj
    (structureRingPresheaf_isSheaf B S hS X hX) (L.val ⊗ N.val)).app (op Z)).hom hy).trans hζ

/-- **The product of two free generators is a free generator.**  Let `e` and `f` be families of
sections of `ℒ` and of `𝒩` over the charts over `V`, compatible with restriction and each
generating freely over every one of them.  Then over every chart over `V` their product
generates `ℒ ⊗_{𝒪_X} 𝒩` freely: `r ↦ r · (e ⊗ f)` is a bijection of the regular functions onto
the sections of `ℒ ⊗_{𝒪_X} 𝒩` there.

Injectivity is
`AlgebraicGeometry.Space.injective_smul_tensorChartSection`.  For surjectivity, a section is a
multiple of the product over the members of a covering sieve
(`AlgebraicGeometry.Space.exists_sieve_smul_tensorChartSection_eq`); the scalars so obtained
agree on common refinements, by injectivity over the refinement, so they amalgamate to a regular
function on the chart, and `ℒ ⊗_{𝒪_X} 𝒩` being separated the amalgamation multiplies the product
to the given section.

This is the hypothesis `hbij` of
`AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit` for the product, and — through
`Stacks.bijective_tmul_of_bijective_smul` — the freeness of the generator at the generic point
of a prime divisor that reading the coefficient of Stacks 0EPR of a product section needs. -/
theorem bijective_smul_tensorChartSection
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (hfbij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • f W k)
    (W : SmallEtale B S hS X) (k : W ⟶ V) :
    Function.Bijective fun r : chartRing B S hS X hX W ↦
      r • tensorChartSection B S hS hX L N W (e W k) (f W k) := by
  refine ⟨injective_smul_tensorChartSection B S hS hX L N V e f hecompat hebij hfcompat hfbij
    W k, ?_⟩
  intro z
  obtain ⟨T, hT, hTsol⟩ := exists_sieve_smul_tensorChartSection_eq B S hS hX L N V e f
    hebij hfbij W k z
  have hassoc : ∀ (Y : SmallEtale B S hS X) (κ κ' : Y ⟶ V) (y : chartRing B S hS X hX Y),
      κ = κ' →
      (y • tensorChartSection B S hS hX L N Y (e Y κ) (f Y κ) :
          (picardTensorModule B S hS hX L N).val.obj (op Y)) =
        (y • tensorChartSection B S hS hX L N Y (e Y κ') (f Y κ') :
          (picardTensorModule B S hS hX L N).val.obj (op Y)) :=
    fun Y κ κ' y h ↦ congrArg (fun t : Y ⟶ V ↦
      (y • tensorChartSection B S hS hX L N Y (e Y t) (f Y t) :
        (picardTensorModule B S hS hX L N).val.obj (op Y))) h
  have hone : ∀ (Z : SmallEtale B S hS X) (b : Z ⟶ W) (hb : T b)
      (Y : SmallEtale B S hS X) (a : Y ⟶ Z) (y : chartRing B S hS X hX Y),
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O).obj.map a.op).hom (hTsol b hb).choose = y →
      (y • tensorChartSection B S hS hX L N Y (e Y (a ≫ b ≫ k)) (f Y (a ≫ b ≫ k)) :
          (picardTensorModule B S hS hX L N).val.obj (op Y)) =
        ((picardTensorModule B S hS hX L N).val.map (a ≫ b).op).hom z := by
    intro Z b hb Y a y hy
    refine Eq.trans (smul_tensorChartSection_restrict B S hS hX L N V e f hecompat hfcompat
      Z (b ≫ k) Y a (hTsol b hb).choose y hy).symm ?_
    refine Eq.trans (congrArg ((picardTensorModule B S hS hX L N).val.map a.op).hom
      (hTsol b hb).choose_spec) ?_
    exact (PresheafOfModules.map_comp_apply _ b.op a.op z).symm
  have hsf := (isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS X)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O).obj ⋙ forget RingCat.{u})).mp
    (Presheaf.isSheaf_comp_of_isSheaf (SmallEtale.topology B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O).obj (forget RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O).property) T hT
  have hcompat : ∀ ⦃Z₁ Z₂ Y : SmallEtale B S hS X⦄ (a₁ : Y ⟶ Z₁) (a₂ : Y ⟶ Z₂)
      (b₁ : Z₁ ⟶ W) (b₂ : Z₂ ⟶ W) (hb₁ : T b₁) (hb₂ : T b₂), a₁ ≫ b₁ = a₂ ≫ b₂ →
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O).obj.map a₁.op).hom
            (hTsol b₁ hb₁).choose =
        ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O).obj.map a₂.op).hom
          (hTsol b₂ hb₂).choose := by
    intro Z₁ Z₂ Y a₁ a₂ b₁ b₂ hb₁ hb₂ hcomm
    refine injective_smul_tensorChartSection B S hS hX L N V e f hecompat hebij hfcompat hfbij
      Y (a₁ ≫ b₁ ≫ k) ?_
    refine Eq.trans (hone Z₁ b₁ hb₁ Y a₁ _ rfl) ?_
    refine Eq.trans (congrArg (fun t : Y ⟶ W ↦
      ((picardTensorModule B S hS hX L N).val.map t.op).hom z) hcomm) ?_
    refine Eq.trans (hone Z₂ b₂ hb₂ Y a₂ _ rfl).symm ?_
    exact hassoc Y (a₂ ≫ b₂ ≫ k) (a₁ ≫ b₁ ≫ k) _
      ((Category.assoc a₂ b₂ k).symm.trans
        ((congrArg (fun t : Y ⟶ W ↦ t ≫ k) hcomm.symm).trans (Category.assoc a₁ b₁ k)))
  refine ⟨hsf.amalgamate (fun Z b hb ↦ (hTsol b hb).choose) hcompat, ?_⟩
  have hsep := (isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS X)
      ((picardTensorModule B S hS hX L N).val.presheaf ⋙ forget AddCommGrpCat.{u})).mp
    (Presheaf.isSheaf_comp_of_isSheaf (SmallEtale.topology B S hS X)
      (picardTensorModule B S hS hX L N).val.presheaf (forget AddCommGrpCat.{u})
      (picardTensorModule B S hS hX L N).isSheaf) T hT
  refine hsep.isSeparatedFor.ext ?_
  intro Y g hg
  refine Eq.trans (smul_tensorChartSection_restrict B S hS hX L N V e f hecompat hfcompat
    W k Y g (hsf.amalgamate (fun Z b hb ↦ (hTsol b hb).choose) hcompat) _ rfl) ?_
  refine Eq.trans (congrArg (fun y : chartRing B S hS X hX Y ↦
      (y • tensorChartSection B S hS hX L N Y (e Y (g ≫ k)) (f Y (g ≫ k)) :
        (picardTensorModule B S hS hX L N).val.obj (op Y)))
    (hsf.valid_glue hcompat g hg)) ?_
  exact (hTsol g hg).choose_spec

end AlgebraicGeometry.Space

end
