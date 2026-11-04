module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner

/-!
# Integer tensor powers are carried along by any functor compatible with the tensor product

Let `L` be an invertible sheaf of modules on a ringed site `(C, J, 𝒪)`, let `(D, K, 𝒪')` be a
second ringed site, and let `R` be a functor from sheaves of `𝒪`-modules to sheaves of
`𝒪'`-modules. If `R` is compatible with the tensor product in the single sense that
`R(M ⊗ L) ≅ R M ⊗ R L` for every `M`, and carries the structure sheaf to the structure sheaf,
then `R (L^{⊗ n}) ≅ (R L)^{⊗ n}` for **every** `n : ℤ`.

This is the whole abstract content of "tensor powers commute with restriction to an open".
`Stacks.SheafOfModules.TensorPower.tensorPower` is the image of the structure sheaf under the
`n`th power of the autoequivalence `- ⊗ L`, an iterate of an abstract autoequivalence with no
sectionwise description, so nothing about it can be computed from a formula; the only way to
move a tensor power along a functor is to move the autoequivalence along it and iterate, which
is `Stacks.Equivalence.powIntertwineObj`. The negative exponents are not an afterthought: a
comparison for `- ⊗ L` says nothing about `L^{⊗ (-1)}` until one is produced for the
quasi-inverse.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.TensorComparison`: the one input — the objectwise
  comparison `R(M ⊗ L) ≅ R M ⊗ R L`.
* `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso`: **`R (L^{⊗ n}) ≅ (R L)^{⊗ n}` for every
  integer `n`**, from a `TensorComparison` and an identification of the structure sheaves.

## Main results

* `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero` and
  `mapTensorPowerIso_one`: the comparison at the exponents where both sides are already named.

## Where the `TensorComparison` input comes from

It is **not** an open obligation. `Stacks.SheafOfModules.TensorPower.whiskerTensorComparison`
(`Algebra/Category/ModuleCat/Sheaf/TensorSheafOverSlice.lean`) supplies it for restriction along
any functor of sites that is continuous and cocontinuous, which covers both
`SheafOfModules.overFunctor` (restriction to a slice) and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` (restriction to an open of a ringed
space); the resulting tensor-power statements are `whiskerTensorPowerIso` there and
`restrictTensorPowerIso` in
`Algebra/Category/ModuleCat/Sheaf/TensorPowerRestrictOpen.lean`.

The comparison is kept an *argument* here rather than folded into those files because it is the
only thing about `R` this file needs, and because nothing in the argument is specific to
restriction: any pullback, localization or change of site compatible with the tensor product
gets its tensor powers from `mapTensorPowerIso` with no further work. The two ingredients the
restriction case uses are Mathlib's monoidality of `pushforward₀OfCommRingCat`
(`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`, comparisons `Iso.refl`)
for the presheaf tensor product, and the local-bijectivity whiskering lemmas of
`Mathlib/CategoryTheory/Sites/PreservesLocallyBijective.lean` for the sheafification.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u v' u' w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (O' : Dᵒᵖ ⥤ CommRingCat.{w})
  (hO' : Presheaf.IsSheaf K (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O'))
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]

/-- **Compatibility of a functor with the tensor product by a fixed sheaf of modules**: an
isomorphism `R(M ⊗ L) ≅ R M ⊗ R L`, for every `M`, with no naturality required. This is the one
input of `mapTensorPowerIso`. -/
def TensorComparison
    (R : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
      ⥤
      _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :=
  ∀ M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := K)
        ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).obj
          (R.obj M)).obj (R.obj L)

variable
  (R : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).IsEquivalence]

/-- **A functor compatible with the tensor product carries the `n`th tensor power of `L` to the
`n`th tensor power of `R L`, for every integer `n`.** The comparison of the structure sheaves is
the value of the whole construction at `n = 0`, and is needed because a tensor power is the
image of the structure sheaf under an iterate. -/
noncomputable def mapTensorPowerIso (α : TensorComparison O hO O' hO' R L)
    (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
    (n : ℤ) : R.obj (tensorPower O hO L n) ≅ tensorPower O' hO' (R.obj L) n :=
  Stacks.Equivalence.powIntertwineObj ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).asEquivalence R (fun M => α M) n
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ≪≫
    (tensorPowerEquivalence O' hO' (R.obj L) n).functor.mapIso hunit

/-- At `n = 0` the comparison of tensor powers is the comparison of the structure sheaves. -/
theorem mapTensorPowerIso_zero (α : TensorComparison O hO O' hO' R L)
    (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
        :
    mapTensorPowerIso O hO O' hO' R L α hunit 0 = hunit := by
  apply Iso.ext
  show (Iso.refl _).hom ≫ (𝟭 _).map hunit.hom = hunit.hom
  simp

/-- At `n = 1` the comparison of tensor powers is the tensor comparison at the structure sheaf,
followed by tensoring the comparison of the structure sheaves by `R L`. -/
theorem mapTensorPowerIso_one (α : TensorComparison O hO O' hO' R L)
    (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
        :
    mapTensorPowerIso O hO O' hO' R L α hunit 1 =
      α (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)) ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).mapIso hunit :=
  rfl

end Stacks.SheafOfModules.TensorPower
