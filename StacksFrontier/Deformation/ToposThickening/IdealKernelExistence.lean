module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroIdealKernel
public import StacksFrontier.Deformation.ToposThickening.CurvatureKernelCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The ideal part of a flat lift is the kernel of its reduction

Tag 0DIU reads the curvature class of a flat lift in the ideal part `F₀ ⊗_{O₀} I` of the lifted
terms, through the identification `Deformation.ComplexLift.IdealKernel` of that ideal part with
the kernel of the reduction, normalized on local pure tensors by `x̄ ⊗ a ↦ a · x`. This file
constructs that identification: it is the step of the proof of Tag 0DIU reading "since `F^n` is
flat we have `I · F^n = F^n ⊗_O I = F^n₀ ⊗_{O₀} I`".

The mathematics is Tag 08M4, in the form
`Stacks.SheafOfModules.FlatSquareZero.exists_isKernel_idealTensor`: for a flat module `G` over
the thickening and a reduction `q : G ⟶ F|_O` presented by the universal property of extension
of scalars, multiplication `I ⊗_O F ⟶ G` is a kernel of `q`. All that is added here is the
translation: the square-zero ideal datum of `Deformation.ComplexLift.SquareZeroIdeal` as a
morphism of sheaves of modules, the universal property of `BaseChangeTo.unit` as the
presentation of the reduction, the symmetry `F₀ ⊗ I ≅ I ⊗ F₀`, and the compatibility of the
identifications with the differentials.

## Main definitions

* `Deformation.ComplexLift.tensorSymm`: the symmetry `F ⊗_{O₀} I ≅ I ⊗_{O₀} F` of the tensor
  product of sheaves of modules, on local pure tensors the transposition.
* `Deformation.ComplexLift.SquareZeroIdeal.inclHom`: the square-zero ideal datum as a morphism
  of sheaves of modules into the structure sheaf.

## Main results

* `Deformation.ComplexLift.exists_isKernel_mu`: Tag 08M4 read against the universal property of
  the reduction of a flat lift.
* `Deformation.ComplexLift.idealKernelEmb`: the canonical inclusion of the ideal part of a
  lifted term, and `Deformation.ComplexLift.idealKernelEmbIsLimit`, the kernel property of it.
* `Deformation.ComplexLift.idealKernel`: **Tag 0DIU**, the kernel identification of a bounded
  above flat lift, constructed from the lift.
* `Deformation.ComplexLift.nonempty_idealKernel`: **Tag 0DIU**, every bounded above flat lift
  carries a kernel identification.
* `Deformation.ComplexLift.exists_roof_of_derived_hom`: every morphism of the derived category
  is a roof of maps of complexes whose backward leg is a quasi-isomorphism.
* `Deformation.ComplexLift.obstructionMap_eq_of_lift'`: **Tag 0DIU**, the map `ω(K₀)` computed
  from any two flat lifts of `K₀` and any kernel identifications on them is the same.
* `Deformation.ComplexLift.omega`: **Tag 0DIU**, the canonical map
  `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`, a function of `K₀` alone.
* `Deformation.ComplexLift.omega_eq`: `ω(K₀)` is computed by any flat lift and any kernel
  identification on it.
* `Deformation.ComplexLift.omega_natural`: **Tag 0DIU**, naturality of `ω` along a map of
  complexes.
* `Deformation.ComplexLift.omega_natural_derived`: **Tag 0DIU**, naturality of `ω` along an
  arbitrary morphism of the derived category.

## Implementation notes

The kernel identification is constructed, not chosen: `idealKernel` assembles it from
`idealKernelEmb`, the multiplication map of Tag 08M4 read through the symmetry of the tensor
product, and `idealKernelEmbIsLimit`, its kernel property. `nonempty_idealKernel` is the
existence statement derived from it, kept because it is the form the independence argument
consumes; the identification is in any case unique
(`Deformation.ComplexLift.emb_coherence` applied to the identity morphism of lifts shows that
two identifications on one lift have the same `emb`).

`omega` is defined from `idealKernel` on a *chosen* flat lift. The choice of lift is
irreducible at this signature: a flat lift is produced by the tower construction of Tag 0DIT
(`Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex`), which is indexed by an integer
`N` beyond which the cohomology of `K₀` vanishes, and the only hypothesis of `omega` carrying
such an `N` is the proposition `hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n)`. There
is no canonical `N`: the integers that work form a non-empty up-set with no least element in
general. So no `def` can produce the lift from `omega`'s hypotheses, and nothing is lost by the
choice: `obstructionMap_eq_of_lift'` says it does not matter, and `omega_eq` computes `ω(K₀)`
from *any* lift and *any* kernel identification on it, which is full access to the
construction. The hypotheses of `omega` -- local surjectivity of `f`, bounded above cohomology
of `K₀` -- are exactly those of Tag 0DIU.

Naturality for an arbitrary morphism of `D(O₀)`, rather than one induced by a map of complexes,
is reduced to the latter by `exists_roof_of_derived_hom`: the quasi-isomorphisms of the homotopy
category have a left calculus of fractions, the quotient to the homotopy category is full, and
`DerivedCategory.quotientCompQhIso` transports the resulting roof from `DerivedCategory.Qh` to
`DerivedCategory.Q`. The intermediate complex of the roof again has bounded above cohomology,
because it receives a quasi-isomorphism from one that does.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Symm

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The symmetry of the tensor product of sheaves of modules.** It is the sheafification of
the braiding of the objectwise tensor product, so on local pure tensors it is the
transposition. -/
def tensorSymm (O₀ : Sheaf J CommRingCat.{w}) (G I : SheafMod O₀) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).obj G ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj G)).obj I := by
  letI : SymmetricCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) :=
    PresheafOfModules.symmetricCategory (R := O₀.obj)
  exact (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).mapIso (β_ G.val I.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The symmetry `tensorSymm` sends the local pure tensor `x ⊗ a` to `a ⊗ x`. -/
lemma tensorSymm_hom_tmul (O₀ : Sheaf J CommRingCat.{w}) (G I : SheafMod O₀)
    (U : Cᵒᵖ) (x : G.val.obj U) (a : I.val.obj U) :
    (tensorSymm O₀ G I).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj G.val I.val)).app U (x ⊗ₜ[O₀.obj.obj U] a)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj I.val G.val)).app U (a ⊗ₜ[O₀.obj.obj U] x) := by
  let : SymmetricCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) :=
    PresheafOfModules.symmetricCategory (R := O₀.obj)
  exact AlgebraicGeometry.SheafOfModules.sheafification_map_unit J
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) (β_ G.val I.val).hom U
    (x ⊗ₜ[O₀.obj.obj U] a)

end Symm

section Existence

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive]

/-- The inclusion of a square-zero ideal sheaf into the structure sheaf, as a morphism of
sheaves of `O`-modules. -/
def SquareZeroIdeal.inclHom (S : SquareZeroIdeal f I) :
    (restrict f).obj I ⟶ _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars ((ringSheafMap f).hom.app U).hom).obj (I.val.obj U))
        { toFun := fun a => show O.obj.obj U from S.incl U a
          map_add' := fun a b => (S.incl U).map_add a b
          map_smul' := fun r a => S.incl_smul U r a }
      naturality := fun {U V} g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact S.incl_map g a }

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat]
  [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive] in
/-- On sections, `SquareZeroIdeal.inclHom` is the inclusion `SquareZeroIdeal.incl`. -/
@[simp]
lemma SquareZeroIdeal.inclHom_app (S : SquareZeroIdeal f I) (U : Cᵒᵖ) (a : I.val.obj U) :
    (show O.obj.obj U from S.inclHom.val.app U a) = S.incl U a := rfl

variable {K₀ : CochainComplex (SheafMod O₀) ℤ}

omit [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive] in
/-- For a flat term of a lift, the ideal part is the kernel of the reduction: Tag 08M4 read
against the universal property of `Stacks.SheafOfModules.ComplexLifting.BaseChangeTo.unit`. -/
theorem exists_isKernel_mu (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    ∃ mu : (restrict f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj
        (L.baseChange.complex.X n))).obj I) ⟶ L.F.X n,
      (∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : (L.F.X n).val.obj U),
        mu.val.app U
            (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj I.val (L.baseChange.complex.X n).val)).app U
              (a ⊗ₜ[O₀.obj.obj U] (L.baseChange.unit n).val.app U x)) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) • x) ∧
      ∃ hz : mu ≫ L.baseChange.unit n = 0,
        Nonempty (IsLimit (KernelFork.ofι mu hz)) :=
  Stacks.SheafOfModules.FlatSquareZero.exists_isKernel_idealTensor f hf I
    (L.F.X n) (L.baseChange.complex.X n) S.inclHom
    (fun U a => S.f_incl U a)
    (fun U b hb => S.existsUnique_incl U b hb)
    (fun U a b => S.incl_mul_incl U a b)
    (L.baseChange.unit n) (L.baseChange.isExtension n) (L.flat n)

/-- **The ideal part of a lifted term**, as the multiplication map `I ⊗_{O₀} F₀ⁿ ⟶ Fⁿ` into
it: `Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelι` for the flat term `Fⁿ` and the
reduction `Fⁿ ⟶ F₀ⁿ|_O` of the lift. On local pure tensors it is `a ⊗ x̄ ↦ a · x`
(`idealKernelMul_tmul`). -/
def idealKernelMul (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    (restrict f).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj
          (L.baseChange.complex.X n))).obj I) ⟶ L.F.X n :=
  Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelι f hf I (L.F.X n)
    (L.baseChange.complex.X n) S.inclHom (fun U a => S.f_incl U a)
    (fun U b hb => S.existsUnique_incl U b hb) (L.baseChange.unit n)
    (L.baseChange.isExtension n)

omit [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive] in
/-- On a local pure tensor `a ⊗ x̄`, where `x̄` is the reduction of `x`, the map `idealKernelMul`
takes the value `a · x`. -/
lemma idealKernelMul_tmul (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) (U : Cᵒᵖ) (a : I.val.obj U) (x : (L.F.X n).val.obj U) :
    (idealKernelMul hf S L n).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj I.val (L.baseChange.complex.X n).val)).app U
          (a ⊗ₜ[O₀.obj.obj U] (L.baseChange.unit n).val.app U x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) • x :=
  Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelι_tmul f hf I (L.F.X n)
    (L.baseChange.complex.X n) S.inclHom (fun U a => S.f_incl U a)
    (fun U b hb => S.existsUnique_incl U b hb) (L.baseChange.unit n)
    (L.baseChange.isExtension n) U a x

omit [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive] in
/-- The composite of `idealKernelMul` with the reduction of the lifted term is zero. -/
lemma idealKernelMul_comp_unit (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    idealKernelMul hf S L n ≫ L.baseChange.unit n = 0 :=
  Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelι_comp_reduction f hf I (L.F.X n)
    (L.baseChange.complex.X n) S.inclHom (fun U a => S.f_incl U a)
    (fun U b hb => S.existsUnique_incl U b hb) (L.baseChange.unit n)
    (L.baseChange.isExtension n)

/-- The ideal part of a lifted term is exactly the kernel of its reduction: Tag 08M4, in the
form `Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelIsLimit`, for the flat term `Fⁿ`. -/
def idealKernelMulIsLimit (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    IsLimit (KernelFork.ofι (idealKernelMul hf S L n) (idealKernelMul_comp_unit hf S L n)) :=
  Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelIsLimit f hf I (L.F.X n)
    (L.baseChange.complex.X n) S.inclHom (fun U a => S.f_incl U a)
    (fun U b hb => S.existsUnique_incl U b hb) (L.baseChange.unit n)
    (L.baseChange.isExtension n) (fun U a b => S.incl_mul_incl U a b) (L.flat n)

/-- **The canonical inclusion of the ideal part of a lifted term**, in the normalization of
`Deformation.ComplexLift.IdealKernel`: the multiplication map `idealKernelMul`, precomposed
with the symmetry `F₀ⁿ ⊗_{O₀} I ≅ I ⊗_{O₀} F₀ⁿ` so that its source is the degree `n` term of
`L.idealTensor`. On local pure tensors it is `x̄ ⊗ a ↦ a · x` (`idealKernelEmb_tmul`). -/
def idealKernelEmb (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    (restrict f).obj ((L.idealTensor (I := I)).X n) ⟶ L.F.X n :=
  (restrict f).map (tensorSymm O₀ (L.baseChange.complex.X n) I).hom ≫ idealKernelMul hf S L n

/-- On a local pure tensor `x̄ ⊗ a`, where `x̄` is the reduction of `x`, the map `idealKernelEmb`
takes the value `a · x`. -/
lemma idealKernelEmb_tmul (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) (U : Cᵒᵖ) (x : (L.F.X n).val.obj U) (a : I.val.obj U) :
    (idealKernelEmb hf S L n).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) • x :=
  Eq.trans (congrArg (fun t => (idealKernelMul hf S L n).val.app U t)
    (tensorSymm_hom_tmul O₀ (L.baseChange.complex.X n) I U
      ((L.baseChange.unit n).val.app U x) a)) (idealKernelMul_tmul hf S L n U a x)

/-- The composite of `idealKernelEmb` with the reduction of the lifted term is zero. -/
lemma idealKernelEmb_comp_unit (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    idealKernelEmb hf S L n ≫ L.baseChange.unit n = 0 := by
  change ((restrict f).map (tensorSymm O₀ (L.baseChange.complex.X n) I).hom ≫
    idealKernelMul hf S L n) ≫ L.baseChange.unit n = 0
  rw [Category.assoc, idealKernelMul_comp_unit, comp_zero]

/-- The ideal part of a lifted term is the kernel of its reduction, in the normalization of
`Deformation.ComplexLift.IdealKernel`: `idealKernelMulIsLimit` transported along the symmetry
of the tensor product. -/
def idealKernelEmbIsLimit (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    IsLimit (KernelFork.ofι (idealKernelEmb hf S L n) (idealKernelEmb_comp_unit hf S L n)) := by
  haveI : IsIso ((restrict f).map (tensorSymm O₀ (L.baseChange.complex.X n) I).hom) :=
    inferInstanceAs (IsIso ((restrict f).mapIso (tensorSymm O₀ _ I)).hom)
  exact (idealKernelMulIsLimit hf S L n).ofIsoLimit
    (Fork.ext ((restrict f).mapIso (tensorSymm O₀ (L.baseChange.complex.X n) I)).symm
      (by
        change ((restrict f).mapIso (tensorSymm O₀ (L.baseChange.complex.X n) I)).inv ≫
          ((restrict f).map (tensorSymm O₀ (L.baseChange.complex.X n) I).hom ≫
            idealKernelMul hf S L n) = idealKernelMul hf S L n
        rw [← Category.assoc, Functor.mapIso_inv, ← Functor.map_comp, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]))

/-- The inclusions `idealKernelEmb` commute with the differentials of `L.idealTensor` and of the
lifted complex. -/
lemma idealKernelEmb_d (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) (n : ℤ) :
    idealKernelEmb hf S L n ≫ L.F.d n =
      (restrict f).map ((L.idealTensor (I := I)).d n (n + 1)) ≫
        idealKernelEmb hf S L (n + 1) := by
  refine restrictTensor_hom_ext_of_unit f (L.baseChange.unit n)
    (Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.isLocallySurjective f hf
      (L.baseChange.isExtension n)) _ _ fun U x a => ?_
  have hdx : (L.baseChange.unit (n + 1)).val.app U ((L.F.d n).val.app U x) =
      (L.baseChange.complex.d n (n + 1)).val.app U
        ((L.baseChange.unit n).val.app U x) :=
    congrArg (fun k : L.F.X n ⟶ (restrict f).obj (L.baseChange.complex.X (n + 1)) =>
      k.val.app U x) (L.baseChange.differential n)
  have hstep : ((restrict f).map ((L.idealTensor (I := I)).d n (n + 1))).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X (n + 1)).val I.val)).app U
        ((L.baseChange.unit (n + 1)).val.app U ((L.F.d n).val.app U x) ⊗ₜ[O₀.obj.obj U] a) := by
    rw [hdx]
    exact Deformation.ToposThickening.tensorSheaf_map_unit_tmul O₀
      (L.baseChange.complex.d n (n + 1)) U ((L.baseChange.unit n).val.app U x) a
  calc ((idealKernelEmb hf S L n ≫ L.F.d n).val.app U)
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a))
      = (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) •
          (L.F.d n).val.app U x :=
        Eq.trans (congrArg (fun t => (L.F.d n).val.app U t)
          (idealKernelEmb_tmul hf S L n U x a))
          (((L.F.d n).val.app U).hom.map_smul _ _)
    _ = ((idealKernelEmb hf S L (n + 1)).val.app U)
          (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X (n + 1)).val I.val)).app U
            ((L.baseChange.unit (n + 1)).val.app U ((L.F.d n).val.app U x) ⊗ₜ[O₀.obj.obj U]
              a)) := (idealKernelEmb_tmul hf S L (n + 1) U ((L.F.d n).val.app U x) a).symm
    _ = (((restrict f).map ((L.idealTensor (I := I)).d n (n + 1)) ≫
            idealKernelEmb hf S L (n + 1)).val.app U)
          (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
            ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) :=
        congrArg (fun t => ((idealKernelEmb hf S L (n + 1)).val.app U) t) hstep.symm

/-- **Stacks 0DIU.** The identification of the ideal part of a bounded above flat lift with the
kernel of its reduction, normalized by the pure-tensor formula `x̄ ⊗ a ↦ a · x`: it is
constructed, not chosen, from `idealKernelEmb` and `idealKernelEmbIsLimit`.

This is the step "since `F^n` is flat, `I · F^n = F^n ⊗_O I = F^n₀ ⊗_{O₀} I`" of the proof of
Tag 0DIU; the mathematics is Tag 08M4. -/
def idealKernel (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) : IdealKernel S L where
  emb n := idealKernelEmb hf S L n
  emb_comp_unit n := idealKernelEmb_comp_unit hf S L n
  isKernel n := idealKernelEmbIsLimit hf S L n
  emb_d n := idealKernelEmb_d hf S L n
  emb_tmul n U x a := idealKernelEmb_tmul hf S L n U x a

/-- **Stacks 0DIU.** Every bounded above flat lift carries an identification of its ideal part
with the kernel of its reduction, normalized by the pure-tensor formula `x̄ ⊗ a ↦ a · x`.

The identification is `Deformation.ComplexLift.idealKernel`; this is its existence statement,
which is what the independence argument consumes. -/
@[stacks 0DIU "variant: the ideal part of a flat lift is the kernel of its reduction, a step of the
proof; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem nonempty_idealKernel (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (L : FlatLift f K₀) : Nonempty (IdealKernel S L) :=
  ⟨idealKernel hf S L⟩

end Existence

section Roof

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- **Every morphism of the derived category is a roof of maps of complexes.** For
`ψ : K₀ ⟶ L₀` in `D(A)` there are a complex `M`, a map `g : K₀ ⟶ M` and a quasi-isomorphism
`t : L₀ ⟶ M` with `ψ ≫ t = g` in the derived category.

This is the left calculus of fractions of the quasi-isomorphisms in the homotopy category,
`CategoryTheory.Localization.exists_leftFraction`, transported from
`DerivedCategory.Qh` to `DerivedCategory.Q` along `DerivedCategory.quotientCompQhIso`; the legs
are genuine maps of complexes because the quotient to the homotopy category is full. -/
theorem exists_roof_of_derived_hom {K₀ L₀ : CochainComplex A ℤ}
    (ψ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj L₀) :
    ∃ (M : CochainComplex A ℤ) (g : K₀ ⟶ M) (t : L₀ ⟶ M),
      IsIso (DerivedCategory.Q.map t) ∧
        ψ ≫ DerivedCategory.Q.map t = DerivedCategory.Q.map g := by
  let Qu := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have hinv : W.IsInvertedBy DerivedCategory.Qh := Localization.inverts DerivedCategory.Qh W
  have : Qu.EssSurj := ⟨fun X => ⟨X.as, ⟨Iso.refl _⟩⟩⟩
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction DerivedCategory.Qh W
    (e.hom.app K₀ ≫ ψ ≫ e.inv.app L₀)
  have hfac := φ.map_comp_map_s DerivedCategory.Qh hinv
  rw [← hφ] at hfac
  have hs1 : IsIso (DerivedCategory.Qh.map φ.s) := hinv _ φ.hs
  let ι := Qu.objObjPreimageIso φ.Y'
  obtain ⟨g, hg⟩ := Qu.map_surjective (φ.f ≫ ι.inv)
  obtain ⟨t, ht⟩ := Qu.map_surjective (φ.s ≫ ι.inv)
  have hQt := e.hom.naturality t
  have hQg := e.hom.naturality g
  have hfac' : (e.hom.app K₀ ≫ ψ ≫ e.inv.app L₀) ≫ (Qu ⋙ DerivedCategory.Qh).map t =
      (Qu ⋙ DerivedCategory.Qh).map g := by
    change _ ≫ DerivedCategory.Qh.map (Qu.map t) = DerivedCategory.Qh.map (Qu.map g)
    rw [hg, ht, Functor.map_comp, Functor.map_comp, ← Category.assoc, hfac]
  have h1 : IsIso ((Qu ⋙ DerivedCategory.Qh).map t) := by
    change IsIso (DerivedCategory.Qh.map (Qu.map t))
    rw [ht, Functor.map_comp]
    infer_instance
  refine ⟨_, g, t, ?_, ?_⟩
  · have h3 : IsIso (e.hom.app L₀ ≫ DerivedCategory.Q.map t) := by
      rw [← hQt]
      infer_instance
    exact IsIso.of_isIso_comp_left (e.hom.app L₀) (DerivedCategory.Q.map t)
  · rw [← cancel_epi (e.hom.app K₀), ← hQg, ← hfac', Category.assoc, Category.assoc, hQt]
    simp

end Roof

section Canonical

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)]

/-- **Stacks 0DIU, `ω(K₀)` depends on the complex alone.** Any two bounded above flat lifts of
`K₀`, with any kernel identifications on them, compute the same map. -/
@[stacks 0DIU "variant: independence of the flat lift at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_lift' (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I)
    {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    {L L' : FlatLift f K₀} (T : IdealKernel S L) (T' : IdealKernel S L') :
    obstructionMap D T = obstructionMap D T' := by
  obtain ⟨M, ⟨h⟩, ⟨h'⟩⟩ := exists_flatLiftHom_pair L L' hf hK
  obtain ⟨TM⟩ := nonempty_idealKernel hf S M
  rw [obstructionMap_eq_of_hom' D hf h T TM, obstructionMap_eq_of_hom' D hf h' T' TM]

/-- **Stacks 0DIU.** The canonical map `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` attached to a
square-zero extension `f : O ⟶ O₀` of sheaves of rings with ideal sheaf `I`, as a function of
the bounded above complex `K₀` alone: it is the curvature of the lifted differential of any
bounded above flat lift of `K₀`, read through the canonical identification of the ideal part of
that lift with the kernel of its reduction.

The kernel identification is not chosen: it is `Deformation.ComplexLift.idealKernel`, built
from the lift. The lift itself is chosen -- `Deformation.ComplexLift.exists_flatLift` -- and
that is irreducible here, because the bound the lifting construction is indexed by is available
only inside the propositional hypothesis `hK`. That the choice does not matter is
`Deformation.ComplexLift.obstructionMap_eq_of_lift'`, and `Deformation.ComplexLift.omega_eq`
computes `ω(K₀)` from any lift and any kernel identification, so nothing about `ω(K₀)` is
hidden by it. -/
@[stacks 0DIU "variant: the map ω(K₀) of a bounded above complex at a supplied derived ideal tensor
datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
def omega (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (D : DerivedIdealTensor I) (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n)) :
    DerivedCategory.Q.obj K₀ ⟶ (D.functor.obj (DerivedCategory.Q.obj K₀))⟦(2 : ℤ)⟧ :=
  obstructionMap D (idealKernel hf S (Classical.choice (exists_flatLift hf K₀ hK)))

/-- **Stacks 0DIU.** The canonical map is computed by *any* bounded above flat lift and any
kernel identification on it. -/
@[stacks 0DIU "variant: ω is computed by any flat lift at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem omega_eq (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (D : DerivedIdealTensor I) {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    {L : FlatLift f K₀} (T : IdealKernel S L) :
    omega hf S D K₀ hK = obstructionMap D T :=
  obstructionMap_eq_of_lift' hf S D hK _ T

/-- **Stacks 0DIU, naturality of `ω`.** For a map `φ : K₀ ⟶ L₀` of bounded above complexes of
`O₀`-modules the square formed by `ω(K₀)`, `ω(L₀)` and the maps induced by `φ` commutes. No
compatibility of lifts is assumed: the lift of `φ` is
`Deformation.ComplexLift.exists_flatLiftHom` and the lift-independence is
`Deformation.ComplexLift.omega_eq`. -/
@[stacks 0DIU "variant: naturality of ω along a map of complexes at a supplied derived ideal tensor
datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus_natural"]
theorem omega_natural (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (D : DerivedIdealTensor I) {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ} (φ : K₀ ⟶ L₀)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hL : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L₀.homology n)) :
    DerivedCategory.Q.map φ ≫ omega hf S D L₀ hL =
      omega hf S D K₀ hK ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          (D.functor.map (DerivedCategory.Q.map φ)) := by
  obtain ⟨L⟩ := exists_flatLift hf K₀ hK
  obtain ⟨M, ⟨h⟩⟩ := exists_flatLiftHom hf L φ hL
  obtain ⟨TL⟩ := nonempty_idealKernel hf S L
  obtain ⟨TM⟩ := nonempty_idealKernel hf S M
  rw [omega_eq hf S D hK TL, omega_eq hf S D hL TM]
  exact obstructionMap_natural D h TL TM (emb_natural hf h TL TM)

/-- **Stacks 0DIU, naturality of `ω` for an arbitrary morphism of the derived category.** For
any `ψ : K₀ ⟶ L₀` in `D(O₀)` between bounded above complexes -- not merely one coming from a map
of complexes -- the square formed by `ω(K₀)`, `ω(L₀)` and the maps induced by `ψ` commutes.

Every such `ψ` is a roof `K₀ ⟶ M ⟵ L₀` of maps of complexes with the second leg a
quasi-isomorphism (`Deformation.ComplexLift.exists_roof_of_derived_hom`), so this follows from
naturality along maps of complexes applied to the two legs. -/
@[stacks 0DIU "variant: naturality of ω along a derived map at a supplied derived ideal tensor
datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus_natural"]
theorem omega_natural_derived (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (D : DerivedIdealTensor I) {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hL : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L₀.homology n))
    (ψ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj L₀) :
    ψ ≫ omega hf S D L₀ hL =
      omega hf S D K₀ hK ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          (D.functor.map ψ) := by
  obtain ⟨M, g, t, ht, hgt⟩ := exists_roof_of_derived_hom ψ
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso (SheafMod O₀) t).mp ht
  obtain ⟨N, hN⟩ := hL
  have hM : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (M.homology n) :=
    ⟨N, fun n hn =>
      IsZero.of_iso (hN n hn) (asIso (HomologicalComplex.homologyMap t n)).symm⟩
  have hnt := omega_natural hf S D t ⟨N, hN⟩ hM
  have hng := omega_natural hf S D g hK hM
  have : IsIso ((CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      (D.functor.map (DerivedCategory.Q.map t))) := inferInstance
  rw [← cancel_mono ((CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀))
    (2 : ℤ)).map (D.functor.map (DerivedCategory.Q.map t)))]
  simp only [Category.assoc]
  rw [← hnt, ← Category.assoc, hgt, hng]
  simp only [← Functor.map_comp, hgt]

end Canonical

end Deformation.ComplexLift

end
