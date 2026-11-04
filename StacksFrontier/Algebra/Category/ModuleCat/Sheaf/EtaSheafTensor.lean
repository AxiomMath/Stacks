module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Data.Int.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Décalage commutes with tensoring by an invertible module

In Situation 0GT4 — `X` a ringed space, `I` an invertible sheaf of `O_X`-modules and
`ι : I ⟶ O_X` a monomorphism exhibiting `I` as an invertible ideal sheaf — let `F` be a cochain
complex of `I`-torsion-free `O_X`-modules and let `L` be an invertible `O_X`-module. Then the
décalage of `F ⊗ L` is the décalage of `F`, tensored with `L`.

## Main definitions

* `idealPowerTensorIso`: the interchange `I^{⊗ n} ⊗ (M ⊗ L) ≅ (I^{⊗ n} ⊗ M) ⊗ L`, moving an
  integer ideal power past an invertible tensor factor.
* `IdealPowerTensorComparison`, `idealPowerTensorComparison`: the properties that characterize
  that interchange in every integer degree, and `idealPowerTensorIso` as an instance of them.
* `etaTensorInvertible`: the comparison `η_I (F ⊗ L) ≅ (η_I F) ⊗ L` of cochain complexes.

## Main results

* `etaTensorInvertible` (Tag 0F9W) identifies the décalage of `F ⊗ L` with the décalage of `F`
  tensored by `L`.
* `etaTensorInvertible_fst` and `etaTensorInvertible_snd` compute that comparison degreewise on
  each of the two projections of the fibre product defining the décalage term.
* `idealTorsionFree_tensorInvertible`: tensoring an `I`-torsion-free module by an invertible
  module leaves it `I`-torsion-free, which is what lets `η_I` be formed on the tensor side.
* `idealPowerTensorIso_zero`, `idealPowerTensorIso_natural` and `idealPowerTensorIso_incl`:
  the interchange is the identity in degree `0`, is natural in the module, and is compatible
  with the inclusion of consecutive ideal powers.
* `IdealPowerTensorComparison.map_eq`: the interchange is unique in **every** integer degree,
  negative ones included, so the comparison of Tag 0F9W involves no choice.

## Implementation notes

The source writes an *equality* `η_I(F ⊗ L) = (η_I F) ⊗ L`. No such equality is available
here: `(η_I F)^n` is by construction a categorical fibre product (`etaTerm`), and the two sides
are fibre products of different — though isomorphic — diagrams, so they agree only up to the
canonical comparison that a limit cone determines. The statement is therefore formalized as a
specified isomorphism of cochain complexes, together with the two degreewise identities
`etaTensorInvertible_fst` and `etaTensorInvertible_snd` describing its composite with each
projection of the defining fibre product. Tensoring by `L` is an equivalence, so it carries the
fibre product defining `(η_I F)^n` to a fibre product; a map into a fibre product is determined
by its two projections, so those two identities determine the comparison uniquely in terms of
`idealPowerTensorIso`, which `IdealPowerTensorComparison.map_eq` in turn pins down in every
integer degree. The identification is therefore canonical and not merely existent.

The comparison is assembled from two inputs. Degreewise, `idealPowerTensorIso` interchanges an
integer ideal power with the invertible tensor factor; it is built at the zeroth power from the
braiding and transported to every integer power by the successor comparison `powSuccIso` of
Tag 01CU, which is why `idealPowerTensorIso_zero`, `idealPowerTensorIso_natural` and
`idealPowerTensorIso_incl` are the characterizing facts rather than a closed formula. Those three
determine it only in nonnegative degrees: the induction from degree `0` runs along
`idealPowerTensorIso_incl`, whose right-hand factor `idealPowerIncl` is a monomorphism on an
`I`-torsion-free module (`idealPowerIncl_mono`), and in negative degrees the recursion runs the
other way, where a monomorphism is not enough. Since the source's `I^i F` is defined for every
`i : ℤ` and the negative twists are the point of the construction, uniqueness in negative
degrees is recorded separately: `IdealPowerTensorComparison` carries the degree-`0`
normalization together with the recursion step itself, and `IdealPowerTensorComparison.map_eq`
shows any two such families agree in every integer degree — downwards because tensoring by `I`
is an equivalence, hence faithful, so the recursion step can be solved backwards.

Globally, tensoring by an invertible module is an equivalence, hence preserves the fibre
products defining the décalage terms, and `PreservesPullback.iso` turns that into the required
comparison of pullbacks.

Both sides of the main statement have to be *formable*, and the right-hand side is
`η_I F` tensored by `L` whereas the left-hand side needs the terms of `F ⊗ L` to be
`I`-torsion-free. That is `idealTorsionFree_tensorInvertible`, which is proved by transporting
the multiplication map `I ⊗ - ⟶ -` across the equivalence `- ⊗ L`; most of
`IdealTorsionFree.lean` is private, so the facts about the annihilator subsheaf that this needs
are re-proved here as private lemmas.

Invertibility is taken in the `Stacks.SheafOfModules.IsInvertible` spelling of Tag 01CS and the
tensor-power calculus in the `Stacks.SheafOfModules.Invertible` spelling of Tag 01CU, exactly as
in `EtaSheaf.lean`; the bridging instance `algebraicGeometryIsInvertible` of that file converts
between the two invertibility predicates.

## References

* [Stacks Project, Tag 0F9W](https://stacks.math.columbia.edu/tag/0F9W)
* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

/- Three spellings of the structure sheaf of rings of `X` meet in this file: `TopCat.Sheaf
RingCat` (the spelling of `Oₓ`), `Sheaf (Opens.grothendieckTopology X) RingCat` (the spelling the
tensor-sheafification calculus of Tag 05NA is stated over) and the ring presheaf
`structureRingPresheaf`, which is what indexes `PresheafOfModules`. They are the same object, but
the definitions between them are not reducible, so unification below instance transparency does
not see through them. Making them locally unfoldable, as here, is necessary but not sufficient:
every declaration below that computes with the sheafification adjunction at presheaf level, or
that composes the tensor-power calculus across two of the spellings, needs unification at full
transparency, and each such declaration carries that option on its own rather than the file
imposing it globally. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence
  tensorPowerEquivalence powSuccIso powSuccIso_natural
  tensorProductRightUnitor)

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf sheafify sheafifyAdjunction toSheafify isIso_sheafify_map_whiskerRight isIso_sheafify_map_toSheafify)

universe u v w

namespace Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

section Swap

open MonoidalCategory BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Braiding `I` past `L` before multiplying by `i : I ⟶ 𝟙_ C` is the same as multiplying by
`i` first and then tensoring by `L`. -/
public lemma swap_multiply (M I L : C) (i : I ⟶ 𝟙_ C) :
    (α_ M I L).hom ≫ M ◁ (β_ I L).hom ≫ (α_ M L I).inv ≫
      (M ⊗ L) ◁ i ≫ (ρ_ (M ⊗ L)).hom =
    (M ◁ i ≫ (ρ_ M).hom) ▷ L := by
  rw [← associator_inv_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, ← braiding_naturality_left]
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← associator_naturality_middle_assoc]
  simp [Category.assoc]

omit [BraidedCategory C] in
/-- Braiding `f` past the ideal before multiplying by `i : I ⟶ 𝟙_ C` is the same as multiplying
first and then applying `f`. -/
public lemma multiply_naturality (I : C) (i : I ⟶ 𝟙_ C) {M N : C} (f : M ⟶ N) :
    (f ▷ I) ≫ (N ◁ i) ≫ (ρ_ N).hom = ((M ◁ i) ≫ (ρ_ M).hom) ≫ f := by
  rw [← Category.assoc, ← tensorHom_def, tensorHom_def', Category.assoc,
    rightUnitor_naturality, Category.assoc]

end Swap

section TensorCommute

open MonoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

local notation "Osh" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (ObjectProperty.FullSubcategory.mk O
    (Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO)))

/- The two maps below are the sheafification unit and the ideal map, each given a *declared*
type at the spelling the tensor calculus needs: `toSheafify O hO P` lands in the right adjoint
of the sheafification adjunction applied to `P^#`, while the monoidal calculus wants
`(P^#).val`, and `i.val` lands in `(SheafOfModules.unit Osh).val` while it wants the monoidal
unit. Each pair agrees definitionally but not at `implicit` transparency, and a type ascription
does not help: the mismatched spelling sits in an *implicit* argument of `◁`/`▷`, which is
inferred from the argument's own type. Only a declared type reaches it. -/

/-- The sheafification unit, with its target spelled as the underlying presheaf of modules of
the sheafification. -/
private noncomputable def unitVal (P : PresheafOfModules.{w} (Osh).obj) :
    P ⟶ (((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).obj P).val :=
  ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) P

/-- The sheafification counit, with its source spelled as the sheafification of the underlying
presheaf of modules. -/
private noncomputable def counitVal (P : SheafOfModules.{w} Osh) :
    ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).obj P.val ⟶ P :=
  ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).counit.app P

/-- A map to the unit sheaf of modules, with its target spelled as the monoidal unit of
presheaves of modules. -/
private def idealUnit {I : SheafOfModules.{w} Osh} (i : I ⟶ SheafOfModules.unit Osh) :
    I.val ⟶ 𝟙_ (PresheafOfModules.{w} (Osh).obj) :=
  i.val

/-- The sheafification unit is natural. -/
private lemma toSheafify_natural {P Q : PresheafOfModules.{w} (Osh).obj} (f : P ⟶ Q) :
    f ≫ ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) Q = ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) P ≫ (((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map f).val := by
  have h := ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).unit.naturality f
  convert h using 1
  rfl

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.toSheafify in
/-- Sheafifying a twofold presheaf tensor product agrees with two successive sheaf tensor
products. -/
private noncomputable def tensorRightPairIso (I L : SheafOfModules.{w} Osh) :
    SheafOfModules.forget Osh ⋙ tensorRight I.val ⋙ tensorRight L.val ⋙
      (PresheafOfModules.sheafification.{w, v, w, u}
        (R₀ := (Osh).obj) (R := Osh) (𝟙 (Osh).obj)) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj I ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L := by
  let S := PresheafOfModules.sheafification.{w, v, w, u}
    (R₀ := (Osh).obj) (R := Osh) (𝟙 (Osh).obj)
  refine NatIso.ofComponents (fun moduleSheaf => ?_) ?_
  · exact @asIso _ _ _ _
      (S.map (unitVal O hO (moduleSheaf.val ⊗ I.val) ▷ L.val))
      (isIso_sheafify_map_whiskerRight O hO
        (unitVal O hO (moduleSheaf.val ⊗ I.val)) L.val
      (isIso_sheafify_map_toSheafify O hO
        (moduleSheaf.val ⊗ I.val)))
  · intro source target map
    let liftedTensor : PresheafOfModules.{w} (Osh).obj ⥤ SheafOfModules.{w} Osh :=
      tensorRight L.val ⋙ S
    exact (liftedTensor.map_comp (map.val ▷ I.val)
      (unitVal O hO (target.val ⊗ I.val))).symm.trans
        ((congrArg liftedTensor.map (toSheafify_natural O hO (map.val ▷ I.val))).trans
          (liftedTensor.map_comp (unitVal O hO (source.val ⊗ I.val))
            (S.map (map.val ▷ I.val)).val))

/-- Tensoring by `I` and tensoring by `L` commute, by the braiding of the tensor product. -/
@[no_expose]
public noncomputable def tensorRightCommuteIso (I L : SheafOfModules.{w} Osh) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj I ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj I := by
  exact (tensorRightPairIso O hO I L).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget Osh)
        ((tensorRightTensor I.val L.val).symm ≪≫
          (curriedTensor _).flip.mapIso (β_ I.val L.val) ≪≫
          tensorRightTensor L.val I.val))
      ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))) ≪≫ tensorRightPairIso O hO L I

/-- The interchange of the two outer tensor factors of `(M ⊗ I) ⊗ L`, with source and target
spelled through the functors that `tensorRightPairIso` is stated over. The braiding is taken as
an argument so that this needs no braided structure on presheaves of modules beyond the one the
caller already has in scope. -/
private noncomputable def swapMap (I L M : SheafOfModules.{w} Osh)
    (b : I.val ⊗ L.val ⟶ L.val ⊗ I.val) :
    (SheafOfModules.forget Osh ⋙ tensorRight I.val ⋙ tensorRight L.val).obj M ⟶
      (SheafOfModules.forget Osh ⋙ tensorRight L.val ⋙ tensorRight I.val).obj M :=
  (α_ M.val I.val L.val).hom ≫ M.val ◁ b ≫ (α_ M.val L.val I.val).inv

/-- Multiplication `M ⊗ I ⟶ M` by the ideal, induced by `i : I ⟶ O`. -/
private noncomputable def rightMultiply (I : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) (M : SheafOfModules.{w} Osh) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj I).obj M ⟶ M := by
  change ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).obj (M.val ⊗ I.val) ⟶ M
  exact ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map ((M.val ◁ i.val) ≫ (ρ_ M.val).hom) ≫
    ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).counit.app M

/-- Multiplication by the ideal is the sheafification of the presheaf multiplication, followed
by the sheafification counit. -/
private lemma rightMultiply_eq (I : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) (M : SheafOfModules.{w} Osh) :
    rightMultiply O hO I i M =
      ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map ((M.val ◁ i.val) ≫ (ρ_ M.val).hom) ≫
        ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).counit.app M :=
  rfl

/-- On sections of the presheaf tensor product, multiplication by the ideal is the presheaf
multiplication. -/
private lemma toSheafify_rightMultiply (I : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) (M : SheafOfModules.{w} Osh) :
    ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
        (rightMultiply O hO I i M).val =
      (M.val ◁ i.val) ≫ (ρ_ M.val).hom := by
  have h := (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).homEquiv
    (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) M).apply_symm_apply
    ((M.val ◁ i.val) ≫ (ρ_ M.val).hom)
  exact h

/-- Multiplication by the ideal is natural in the module. -/
private lemma rightMultiply_natural (I : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) {M N : SheafOfModules.{w} Osh} (f : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj I).map f ≫ rightMultiply O hO I i N =
      rightMultiply O hO I i M ≫ f := by
  -- The presheaf-level content: braiding `f` past the ideal and then multiplying is
  -- multiplying first and then applying `f`. Stated separately, inside the monoidal category
  -- of presheaves of modules, where every object has a single spelling.
  have hmon := multiply_naturality I.val i.val f.val
  -- The rest is the adjunction. Each step is a ground equation fed to `congrArg`, because the
  -- composite `toSheafify … ≫ (…).val` is type-correct only at default transparency: the
  -- unit lands in the right adjoint applied to the sheafification, and `.val` reads the
  -- underlying presheaf of modules, which are the same object spelled differently.
  apply (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).homEquiv
    (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) N).injective
  show ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
      ((((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (f.val ▷ I.val)).val ≫ (rightMultiply O hO I i N).val) =
    ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
      ((rightMultiply O hO I i M).val ≫ f.val)
  calc ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
        ((((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (f.val ▷ I.val)).val ≫ (rightMultiply O hO I i N).val)
      = (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
          (((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (f.val ▷ I.val)).val) ≫ (rightMultiply O hO I i N).val :=
        (Category.assoc _ _ _).symm
    _ = ((f.val ▷ I.val) ≫
          ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (N.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj)) ≫
          (rightMultiply O hO I i N).val :=
        congrArg (fun k => k ≫ (rightMultiply O hO I i N).val)
          (toSheafify_natural O hO (f.val ▷ I.val)).symm
    _ = (f.val ▷ I.val) ≫
          (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (N.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
            (rightMultiply O hO I i N).val) := Category.assoc _ _ _
    _ = (f.val ▷ I.val) ≫ ((N.val ◁ i.val) ≫ (ρ_ N.val).hom) :=
        congrArg (fun k => (f.val ▷ I.val) ≫ k) (toSheafify_rightMultiply O hO I i N)
    _ = ((M.val ◁ i.val) ≫ (ρ_ M.val).hom) ≫ f.val := hmon
    _ = (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
          (rightMultiply O hO I i M).val) ≫ f.val :=
        congrArg (fun k => k ≫ f.val) (toSheafify_rightMultiply O hO I i M).symm
    _ = ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ≫
          ((rightMultiply O hO I i M).val ≫ f.val) := Category.assoc _ _ _

/-- The components of the comparison of a twofold tensor product. -/
private lemma tensorRightPairIso_hom_app (I L M : SheafOfModules.{w} Osh) :
    (tensorRightPairIso O hO I L).hom.app M =
      ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map
        (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) (M.val ⊗ I.val : PresheafOfModules.{w} (Osh).obj) ▷ L.val) := rfl

/-- The left triangle identity of the sheafification adjunction. -/
private lemma sheafify_toSheafify_counit (P : PresheafOfModules.{w} (Osh).obj) :
    ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj)).unit.app) P) ≫
      ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).counit.app (((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).obj P) = 𝟙 _ :=
  ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).left_triangle_components P

/-- The left triangle identity of the sheafification adjunction, in the `unitVal`/`counitVal`
spelling. -/
private lemma sheafify_unitVal_counitVal (P : PresheafOfModules.{w} (Osh).obj) :
    ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (unitVal O hO P) ≫ counitVal O hO (((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).obj P) = 𝟙 _ :=
  ((PresheafOfModules.sheafificationAdjunction.{w} (R := Osh) (𝟙 (Osh).obj))).left_triangle_components P

/-- Multiplying by the ideal after the comparison of a twofold tensor product is the
sheafification of the presheaf multiplication on `M ⊗ L`. -/
private lemma tensorRightPairIso_multiply (I L M : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) :
    (tensorRightPairIso O hO L I).hom.app M ≫
      rightMultiply O hO I i (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).obj M) =
    ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (((M.val ⊗ L.val) ◁ i.val) ≫ (ρ_ (M.val ⊗ L.val)).hom) := by
  let sheafification : PresheafOfModules.{w} (Osh).obj ⥤ SheafOfModules.{w} Osh :=
    PresheafOfModules.sheafification.{w, v, w, u}
      (R₀ := (Osh).obj) (R := Osh) (𝟙 (Osh).obj)
  let presheaf : PresheafOfModules.{w} (Osh).obj := M.val ⊗ L.val
  let unit : presheaf ⟶ (sheafification.obj presheaf).val := unitVal O hO presheaf
  let counit : sheafification.obj (sheafification.obj presheaf).val ⟶
      sheafification.obj presheaf := counitVal O hO (sheafification.obj presheaf)
  let multiplication : presheaf ⊗ I.val ⟶ presheaf :=
    (presheaf ◁ idealUnit O hO i) ≫ (ρ_ presheaf).hom
  let sheafifiedMultiplication : (sheafification.obj presheaf).val ⊗ I.val ⟶
      (sheafification.obj presheaf).val :=
    ((sheafification.obj presheaf).val ◁ idealUnit O hO i) ≫
      (ρ_ (sheafification.obj presheaf).val).hom
  have naturality : (unit ▷ I.val) ≫ sheafifiedMultiplication = multiplication ≫ unit :=
    multiply_naturality I.val (idealUnit O hO i) unit
  refine (congrArg (fun comparison => comparison ≫
    rightMultiply O hO I i
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).obj M))
    (tensorRightPairIso_hom_app O hO L I M)).trans ?_
  refine (congrArg (sheafification.map (unit ▷ I.val) ≫ ·)
    (rightMultiply_eq O hO I i
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).obj M))).trans ?_
  exact (Category.assoc (sheafification.map (unit ▷ I.val))
    (sheafification.map sheafifiedMultiplication) counit).symm.trans
      ((congrArg (fun morphism => morphism ≫ counit)
        (sheafification.map_comp (unit ▷ I.val) sheafifiedMultiplication).symm).trans
          ((congrArg (fun morphism => sheafification.map morphism ≫ counit) naturality).trans
            ((congrArg (fun morphism => morphism ≫ counit)
              (sheafification.map_comp multiplication unit)).trans
                ((Category.assoc (sheafification.map multiplication)
                  (sheafification.map unit) counit).trans
                    ((congrArg (sheafification.map multiplication ≫ ·)
                      (sheafify_unitVal_counitVal O hO presheaf)).trans
                        (Category.comp_id _))))))

/-- Interchanging the two tensor factors carries multiplication by the ideal on `M ⊗ L` to
multiplication by the ideal on `M`, tensored by `L`. -/
private lemma tensorRightCommuteIso_multiply (I L M : SheafOfModules.{w} Osh)
    (i : I ⟶ SheafOfModules.unit Osh) :
    (tensorRightCommuteIso O hO I L).hom.app M ≫
      rightMultiply O hO I i (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).obj M) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).map (rightMultiply O hO I i M) := by
  -- `swapMap` is the same composite, but with a *declared* type at the spelling of the
  -- functors `tensorRightPairIso` is stated over; without that the goal produced by `rw [hc]`
  -- is type-correct only at default transparency and nothing below can fire.
  have hc : (tensorRightCommuteIso O hO I L).hom.app M =
      (tensorRightPairIso O hO I L).inv.app M ≫
        ((PresheafOfModules.sheafification.{w} (R := Osh) (𝟙 (Osh).obj))).map (swapMap O hO I L M (β_ I.val L.val).hom) ≫
        (tensorRightPairIso O hO L I).hom.app M := by rfl
  apply (cancel_epi ((tensorRightPairIso O hO I L).hom.app M)).mp
  rw [hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [tensorRightPairIso_multiply, tensorRightPairIso_hom_app]
  let sheafification := PresheafOfModules.sheafification.{w, v, w, u}
    (R₀ := (Osh).obj) (R := Osh) (𝟙 (Osh).obj)
  have presheafEquation : swapMap O hO I L M (β_ I.val L.val).hom ≫
      ((M.val ⊗ L.val) ◁ idealUnit O hO i ≫ (ρ_ (M.val ⊗ L.val)).hom) =
      (unitVal O hO (M.val ⊗ I.val) ▷ L.val) ≫
        ((rightMultiply O hO I i M).val ▷ L.val) :=
    (swap_multiply M.val I.val L.val (idealUnit O hO i)).trans
      ((congrArg (fun morphism => morphism ▷ L.val)
        (toSheafify_rightMultiply O hO I i M).symm).trans
          (comp_whiskerRight _ _ _))
  refine (sheafification.map_comp (swapMap O hO I L M (β_ I.val L.val).hom)
    ((M.val ⊗ L.val) ◁ idealUnit O hO i ≫ (ρ_ (M.val ⊗ L.val)).hom)).symm.trans ?_
  refine (congrArg sheafification.map presheafEquation).trans ?_
  refine (sheafification.map_comp (unitVal O hO (M.val ⊗ I.val) ▷ L.val)
    ((rightMultiply O hO I i M).val ▷ L.val)).trans ?_
  apply congrArg (sheafification.map (unitVal O hO (M.val ⊗ I.val) ▷ L.val) ≫ ·)
  refine Eq.trans ?_ (Stacks.SheafOfModules.Tensor.sheafTensor_map_app
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩
    (rightMultiply O hO I i M) L).symm
  apply congrArg sheafification.map
  apply PresheafOfModules.hom_ext
  intro siteObject
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro leftSection rightSection
  rfl

end TensorCommute

open Opposite MonoidalCategory
open scoped TensorProduct
open scoped ZeroObject

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The image of a monomorphism of sheaves of modules, as a subsheaf of the target. -/
public noncomputable def monoRange {N M : SheafOfModules.{w} R} (f : N ⟶ M) [Mono f] :
    M.Submodule := by
  let P : M.val.Submodule :=
    { obj := fun U => (f.val.app U).hom.range
      map := by
        intro U V g s hs
        obtain ⟨t, rfl⟩ := hs
        exact ⟨(N.val.map g).hom t, (congrArg (fun k => k.hom t) (f.val.naturality g))⟩ }
  let p := Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map f.val)
    (forget AddCommGrpCat.{w})
  haveI : Mono p := by
    have : Mono f.val := (SheafOfModules.forget R).map_mono f
    have : Mono ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
      (PresheafOfModules.toPresheaf R.obj).map_mono f.val
    exact Functor.map_mono ((Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})) _
  have hN : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{w}) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ N.isSheaf
  have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{w}) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.isSheaf
  refine ⟨P, ?_⟩
  have hr := Presieve.isSheaf_iso J (asIso (Subfunctor.toRange p)) hN
  have hp : P.toSubfunctor = Subfunctor.range p := by
    ext U s
    rfl
  intro U s hs
  change s ∈ P.toSubfunctor.obj U
  rw [hp] at hs ⊢
  exact ((Subfunctor.range p).isSheaf_iff hM).mp hr U s hs

/-- The sections of the zero subsheaf over any object are zero. -/
lemma bot_submodule_obj (M : SheafOfModules.{w} R) (U : Cᵒᵖ) :
    (⊥ : M.Submodule).toSubmodule.obj U = ⊥ := by
  let : HasZeroObject (SheafOfModules.{w} R) := hasZeroObject_of_hasTerminal_object
  let Z := monoRange (0 : (0 : SheafOfModules.{w} R) ⟶ M)
  have hzero : (0 : (0 : SheafOfModules.{w} R) ⟶ M).val.app U = 0 := by
    rw [show (0 : (0 : SheafOfModules.{w} R) ⟶ M).val = 0 from
      (SheafOfModules.forget R).map_zero _ _]
    rfl
  apply le_antisymm
  · intro s hs
    have hz := (SheafOfModules.Submodule.le_iff.mp (bot_le : (⊥ : M.Submodule) ≤ Z) U) hs
    change s ∈ ((0 : (0 : SheafOfModules.{w} R) ⟶ M).val.app U).hom.range at hz
    obtain ⟨t, ht⟩ := hz
    refine (Submodule.mem_bot _).mpr ?_
    rw [← ht, hzero]
    simp
  · exact bot_le

end

/-- Multiplication by the ideal vanishes on `N` exactly when every local section of the ideal
annihilates every local section of `N`. -/
private lemma rightMultiply_eq_zero_iff (I N : SheafOfModules.{u} Oₓ) (i : I ⟶ 𝒪) :
    rightMultiply X.presheaf (Oₓ).property I i N = 0 ↔
      ∀ (U : (Opens X)ᵒᵖ) (s : N.val.obj U) (a : I.val.obj U),
        (N.val.obj U).isModule.toSMul.smul (idealSection X i U a) s = 0 := by
  let sheafification := PresheafOfModules.sheafification.{u} (R := Oₓ) (𝟙 (Oₓ).obj)
  let adjunction := PresheafOfModules.sheafificationAdjunction.{u} (R := Oₓ) (𝟙 (Oₓ).obj)
  let multiplication : N.val ⊗ I.val ⟶ N.val := (N.val ◁ i.val) ≫ (ρ_ N.val).hom
  have evaluation : rightMultiply X.presheaf (Oₓ).property I i N =
      (adjunction.homEquiv (N.val ⊗ I.val) N).symm multiplication := rfl
  have zeroEvaluation : (adjunction.homEquiv (N.val ⊗ I.val) N).symm 0 = 0 :=
    (congrArg (fun morphism => morphism ≫ adjunction.counit.app N)
      (Functor.map_zero sheafification (N.val ⊗ I.val) N.val)).trans zero_comp
  have ht : rightMultiply X.presheaf (Oₓ).property I i N = 0 ↔
      (N.val ◁ i.val) ≫ (ρ_ N.val).hom = 0 := by
    constructor
    · intro h
      exact (adjunction.homEquiv (N.val ⊗ I.val) N).symm.injective
        ((evaluation.symm.trans h).trans zeroEvaluation.symm)
    · intro h
      exact evaluation.trans
        ((congrArg (adjunction.homEquiv (N.val ⊗ I.val) N).symm h).trans zeroEvaluation)
  rw [ht]
  constructor
  · intro h U s a
    -- `TensorProduct.map_tmul` and `TensorProduct.rid_tmul` are both `rfl`, so evaluating the
    -- presheaf multiplication at the section `s ⊗ₜ a` *is* multiplication by `idealSection`,
    -- definitionally; no rewriting is needed, and none is possible, since the scalar ring of
    -- `s` and the base ring of the tensor product are different spellings.
    exact congrArg (fun k => (k.app U).hom (s ⊗ₜ[(Oₓ).obj.obj U] a)) h
  · intro h
    ext U : 1
    apply ModuleCat.hom_ext
    change (TensorProduct.rid ((Oₓ).obj.obj U) (N.val.obj U)).toLinearMap.comp
      (TensorProduct.map LinearMap.id (i.val.app U).hom) = 0
    apply TensorProduct.ext'
    intro s a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply]
    convert! h U s a using 1

/-- A monomorphism into an `I`-torsion-free module whose source is annihilated by the ideal is
zero. -/
private lemma mono_eq_zero_of_torsionFree (I : SheafOfModules.{u} Oₓ) (i : I ⟶ 𝒪)
    {N M : SheafOfModules.{u} Oₓ} (f : N ⟶ M) [Mono f]
    (hM : IsIdealTorsionFree X i M)
    (hN : rightMultiply X.presheaf (Oₓ).property I i N = 0) :
    f = 0 := by
  have hk := (rightMultiply_eq_zero_iff X I N i).mp hN
  have hle : monoRange f ≤ idealPowerAnnihilatorSubsheaf X i M 1 := by
    apply le_sSup
    intro U s hs V hVU a
    obtain ⟨t, rfl⟩ := hs
    -- Naturality of `f` on sections, and `map_smul` for `f`, are both passed fully applied:
    -- the scalar lives in `O X` while the module is indexed by the ring presheaf of `Oₓ`, so
    -- neither pattern matches below default transparency.
    have hcomp : (f.val.app (op V)).hom ((N.val.map (homOfLE hVU).op).hom t)
        = (M.val.map (homOfLE hVU).op).hom ((f.val.app U).hom t) :=
      congrArg (fun k => ModuleCat.Hom.hom k t) (f.val.naturality (homOfLE hVU).op)
    have hz := (congrArg (f.val.app (op V)).hom
      (hk (op V) ((N.val.map (homOfLE hVU).op).hom t) (a 0))).trans (map_zero _)
    have hsm := (f.val.app (op V)).hom.map_smulₛₗ (idealSection X i (op V) (a 0))
      ((N.val.map (homOfLE hVU).op).hom t)
    have hz2 : (M.val.obj (op V)).isModule.toSMul.smul (idealSection X i (op V) (a 0))
        ((M.val.map (homOfLE hVU).op).hom ((f.val.app U).hom t)) = 0 :=
      hcomp ▸ hsm.symm.trans hz
    have product : (∏ index : Fin 1,
        (idealSection X i (op V) (a index) : (Oₓ).obj.obj (op V))) =
        idealSection X i (op V) (a 0) := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    exact (congrArg (fun scalar => (M.val.obj (op V)).isModule.toSMul.smul scalar
      ((M.val.map (homOfLE hVU).op).hom ((f.val.app U).hom t))) product).trans hz2
  have hbot := (show idealPowerAnnihilatorSubsheaf X i M 1 = _ from hM) ▸ hle
  ext U s
  have hs := SheafOfModules.Submodule.le_iff.mp hbot U (show
    (f.val.app U).hom s ∈ (monoRange f).toSubmodule.obj U from ⟨s, rfl⟩)
  exact (Submodule.mem_bot _).mp
    ((congrArg (fun submodule => (f.val.app U).hom s ∈ submodule)
      (bot_submodule_obj (M := M) U)).mp hs)

/-- Tensoring by an invertible module is an equivalence. -/
private instance tensorRight_isEquivalence (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).IsEquivalence :=
  tensorRightFunctor_isEquivalence X.presheaf (Oₓ).property L

private instance tensorRight_full (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).Full :=
  Functor.IsEquivalence.full

private instance tensorRight_faithful (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).Faithful :=
  Functor.IsEquivalence.faithful

/-- An `I`-torsion-free module stays `I`-torsion-free after tensoring by an invertible module. -/
private lemma torsionFree_tensor (I : SheafOfModules.{u} Oₓ) (i : I ⟶ 𝒪)
    (L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (hM : IsIdealTorsionFree X i M) :
    IsIdealTorsionFree X i (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) := by
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L
  have : G.EssSurj := Functor.IsEquivalence.essSurj (F := G)
  have : G.Additive := Functor.flip_obj_additive
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) L
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let idealTensor := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    X.sheaf).flip.obj I
  let commute : idealTensor ⋙ G ≅ G ⋙ idealTensor :=
    tensorRightCommuteIso X.presheaf (Oₓ).property I L
  let lattice : CompleteLattice (G.obj M).Submodule :=
    SheafOfModules.Submodule.instCompleteLattice
  change idealPowerAnnihilatorSubsheaf X i (G.obj M) 1 = lattice.bot
  apply @le_antisymm _ lattice.toPartialOrder _ _
  · apply @sSup_le _ lattice.toCompleteSemilatticeSup _ _
    intro N hN
    have hk : rightMultiply X.presheaf (Oₓ).property I i N.toSheafOfModules = 0 := by
      apply (rightMultiply_eq_zero_iff X I N.toSheafOfModules i).mpr
      intro U s a
      have hz := hN U s.val s.property (unop U) le_rfl (fun _ => a)
      have hid : (homOfLE (le_rfl : unop U ≤ unop U)).op = 𝟙 U := Subsingleton.elim _ _
      rw [hid] at hz
      apply Subtype.ext
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, PresheafOfModules.map_id,
        ModuleCat.restrictScalarsId'_inv_app] at hz
      exact hz
    let Q := G.objPreimage N.toSheafOfModules
    let e : G.obj Q ≅ N.toSheafOfModules := G.objObjPreimageIso N.toSheafOfModules
    let f : Q ⟶ M := G.preimage (e.hom ≫ N.ι)
    have hf : G.map f = e.hom ≫ N.ι := G.map_preimage _
    have : Mono f := G.mono_of_mono_map (by rw [hf]; infer_instance)
    have hq : rightMultiply X.presheaf (Oₓ).property I i Q = 0 := by
      let multiplication : idealTensor.obj Q ⟶ Q := rightMultiply X.presheaf (Oₓ).property I i Q
      have mappedZero : G.map (0 : idealTensor.obj Q ⟶ Q) = 0 :=
        G.map_zero (idealTensor.obj Q) Q
      apply G.map_injective
      change G.map multiplication = G.map (0 : idealTensor.obj Q ⟶ Q)
      have hge : rightMultiply X.presheaf (Oₓ).property I i (G.obj Q) = 0 := by
        apply (cancel_mono e.hom).mp
        exact (rightMultiply_natural X.presheaf (Oₓ).property I i e.hom).symm.trans
          ((congrArg (idealTensor.map e.hom ≫ ·) hk).trans
            ((comp_zero).trans (zero_comp).symm))
      have coherence : commute.hom.app Q ≫ rightMultiply X.presheaf (Oₓ).property I i (G.obj Q) =
          G.map multiplication :=
        tensorRightCommuteIso_multiply X.presheaf (Oₓ).property I L Q i
      exact coherence.symm.trans
        ((congrArg (commute.hom.app Q ≫ ·)
          hge).trans ((comp_zero).trans mappedZero.symm))
    have hz := mono_eq_zero_of_torsionFree X I i f hM hq
    have hι : N.ι = 0 := by
      apply (cancel_epi e.hom).mp
      exact (hf.symm.trans (congrArg G.map hz)).trans
        ((G.map_zero Q M).trans (comp_zero).symm)
    intro U s hs
    have hzero := congrArg (fun k => (k.val.app U).hom ⟨s, hs⟩) hι
    change s = 0 at hzero
    rw [hzero]
    exact Submodule.zero_mem _
  · exact lattice.bot_le _

section CoherentPowers

variable {C : Type u} [Category.{v} C]
variable (E G : C ⥤ C) (P : ℤ → C ⥤ C)
  (s : ∀ n, P n ⋙ E ≅ P (n + 1)) (c : E ⋙ G ≅ G ⋙ E)

/-- Extend an interchange with an integer power to the next power. -/
private noncomputable def commuteSucc (n : ℤ) (q : G ⋙ P n ≅ P n ⋙ G) :
    G ⋙ P (n + 1) ≅ P (n + 1) ⋙ G :=
  Functor.isoWhiskerLeft G (s n).symm ≪≫
    Functor.isoWhiskerRight q E ≪≫
      Functor.isoWhiskerLeft (P n) c.symm ≪≫ Functor.isoWhiskerRight (s n) G

/-- Recover an interchange with an integer power from the interchange with the next power. -/
private noncomputable def commutePred [E.Full] [E.Faithful]
    (n : ℤ) (q : G ⋙ P (n + 1) ≅ P (n + 1) ⋙ G) :
    G ⋙ P n ≅ P n ⋙ G :=
  ((Functor.FullyFaithful.ofFullyFaithful E).whiskeringRight C).preimageIso
    (Functor.isoWhiskerLeft G (s n) ≪≫ q ≪≫
      Functor.isoWhiskerRight (s n).symm G ≪≫ Functor.isoWhiskerLeft (P n) c)

/-- Passing down a power and back up again returns the original interchange. -/
private theorem commuteSucc_commutePred [E.Full] [E.Faithful]
    (n : ℤ) (q : G ⋙ P (n + 1) ≅ P (n + 1) ⋙ G) :
    commuteSucc E G P s c n (commutePred E G P s c n q) = q := by
  ext M
  simp [commuteSucc, commutePred, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Category.assoc, ← G.map_comp]

/-- Extend a specified interchange at degree zero coherently to all integer powers. -/
private noncomputable def commuteInt [E.Full] [E.Faithful]
    (z : G ⋙ P 0 ≅ P 0 ⋙ G) (n : ℤ) : G ⋙ P n ≅ P n ⋙ G :=
  Int.inductionOn' n 0 z (fun k _ q => commuteSucc E G P s c k q)
    (fun k _ q => commutePred E G P s c (k - 1) (by simpa using q))

/-- The coherent extension is the given isomorphism in degree `0`. Stated here, where the
functors are abstract, rather than at `idealPowerTensorIso`, where evaluating the integer
recursion would have to be done through the three spellings of the structure sheaf. -/
private theorem commuteInt_zero [E.Full] [E.Faithful] (z : G ⋙ P 0 ≅ P 0 ⋙ G) :
    commuteInt E G P s c z 0 = z :=
  Int.inductionOn'_self

/-- The coherent extension satisfies its defining recursion in every integer degree. -/
private theorem commuteInt_succ [E.Full] [E.Faithful]
    (z : G ⋙ P 0 ≅ P 0 ⋙ G) (n : ℤ) :
    commuteInt E G P s c z (n + 1) = commuteSucc E G P s c n (commuteInt E G P s c z n) := by
  by_cases hn : 0 ≤ n
  · exact Int.inductionOn'_add_one hn
  · have hn' : n + 1 ≤ 0 := by omega
    have h := Int.inductionOn'_sub_one (motive := fun n => G ⋙ P n ≅ P n ⋙ G)
      (zero := z) (succ := fun k _ q => commuteSucc E G P s c k q)
      (pred := fun k _ q => commutePred E G P s c (k - 1) (by simpa using q)) hn'
    have hnn : n + 1 - 1 = n := by omega
    have hh : commuteInt E G P s c z n =
        commutePred E G P s c n (commuteInt E G P s c z (n + 1)) := by
      convert! h using 1 <;> simp only [commuteInt, hnn, eq_mpr_eq_cast]
      all_goals congr! 1 <;> first | omega | simp
    rw [hh, commuteSucc_commutePred]

/-- The coherent extension is compatible with a natural transformation `a : E ⟶ 𝟭 C` that
commutes with `G`: this is the inductive step in integer degree. -/
private theorem commuteInt_incl [E.Full] [E.Faithful]
    (z : G ⋙ P 0 ≅ P 0 ⋙ G) (a : E ⟶ 𝟭 C)
    (h : ∀ M, c.inv.app M ≫ G.map (a.app M) = a.app (G.obj M))
    (n : ℤ) (M : C) :
    (s n).inv.app (G.obj M) ≫ a.app ((P n).obj (G.obj M)) ≫
        (commuteInt E G P s c z n).hom.app M =
      (commuteInt E G P s c z (n + 1)).hom.app M ≫
        G.map ((s n).inv.app M ≫ a.app ((P n).obj M)) := by
  rw [commuteInt_succ]
  simp only [commuteSucc, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [← G.map_comp, Iso.hom_inv_id_app_assoc]
  rw [h]
  exact congrArg ((s n).inv.app (G.obj M) ≫ ·)
    (a.naturality ((commuteInt E G P s c z n).hom.app M)).symm

end CoherentPowers

/-- Tensoring an `I`-torsion-free module by an invertible module preserves
`I`-torsion-freeness. -/
public theorem idealTorsionFree_tensorInvertible
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (hM : IsIdealTorsionFree X ι M) :
    IsIdealTorsionFree X ι (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) :=
  torsionFree_tensor X I ι L M hM

/-- The successor comparison `I^{⊗ n} ⊗ - ⊗ I ≅ I^{⊗ (n+1)} ⊗ -` as a natural isomorphism. -/
public noncomputable def idealPowerSuccNatIso (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I] (n : ℤ) :
    (tensorPowerEquivalence X.presheaf (Oₓ).property I n).functor ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I ≅
      (tensorPowerEquivalence X.presheaf (Oₓ).property I (n + 1)).functor :=
  NatIso.ofComponents
    (powSuccIso (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence X.presheaf (Oₓ).property I)) n)
    (fun f => powSuccIso_natural
      (@Functor.asEquivalence _ _ _ _
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
        (tensorRightFunctor_isEquivalence X.presheaf (Oₓ).property I)) n f)

/-- Interchange of tensoring by `L` with an arbitrary integer ideal power. -/
private noncomputable def idealPowerCommuteNatIso (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I] (n : ℤ) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L ⋙
        (tensorPowerEquivalence X.presheaf (Oₓ).property I n).functor ≅
      (tensorPowerEquivalence X.presheaf (Oₓ).property I n).functor ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L := by
  exact commuteInt ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L)
    (fun degree => (tensorPowerEquivalence X.presheaf (Oₓ).property I degree).functor)
    (idealPowerSuccNatIso X I) (tensorRightCommuteIso X.presheaf (Oₓ).property I L) (Iso.refl _) n

/-- The ideal-power inclusion is the successor comparison followed by multiplication by the
ideal. -/
private lemma idealPowerIncl_eq_multiply (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerIncl X I ι n M =
      (idealPowerSuccNatIso X I n).inv.app M ≫
        rightMultiply X.presheaf (Oₓ).property I ι (idealPowerTerm X I n M) := by
  -- What is left is the identity `𝟙 A ⊗ₘ ι = A ◁ ι` under `sheafify`, reassociated past the
  -- counit. The composite `(A ◁ ι.val) ≫ (ρ_ A).hom` is type-correct only at default
  -- transparency — `ι.val` lands in the unit *sheaf* and `ρ_` expects the monoidal unit — so
  -- the two steps are assembled as terms, where that is exactly the transparency used.
  have hA := ((PresheafOfModules.sheafification.{u} (R := Oₓ) (𝟙 (Oₓ).obj))).map_comp
    ((idealPowerTerm X I n M).val ◁ ι.val) (ρ_ (idealPowerTerm X I n M).val).hom
  have hcounit := (congrArg (fun k => k ≫
      ((PresheafOfModules.sheafificationAdjunction.{u} (R := Oₓ) (𝟙 (Oₓ).obj))).counit.app
        (idealPowerTerm X I n M)) hA).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => ((PresheafOfModules.sheafification.{u} (R := Oₓ) (𝟙 (Oₓ).obj))).map k ≫
          (((PresheafOfModules.sheafification.{u} (R := Oₓ) (𝟙 (Oₓ).obj))).map
              (ρ_ (idealPowerTerm X I n M).val).hom ≫
            ((PresheafOfModules.sheafificationAdjunction.{u} (R := Oₓ) (𝟙 (Oₓ).obj))).counit.app
              (idealPowerTerm X I n M)))
        (id_tensorHom (idealPowerTerm X I n M).val ι.val).symm))
  refine congrArg ((idealPowerSuccNatIso X I n).inv.app M ≫ ·) ?_
  refine (congrArg (fun morphism => morphism ≫
    (tensorProductRightUnitor X.presheaf (Oₓ).property (idealPowerTerm X I n M)).hom)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf
      (𝟙 (idealPowerTerm X I n M)) ι)).trans ?_
  refine Eq.trans ?_ hcounit.symm
  apply congrArg (fun morphism => morphism ≫
    (tensorProductRightUnitor X.presheaf (Oₓ).property (idealPowerTerm X I n M)).hom)
  apply congrArg (PresheafOfModules.sheafification.{u} (R := Oₓ) (𝟙 (Oₓ).obj)).map
  apply PresheafOfModules.hom_ext
  intro siteObject
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro leftSection rightSection
  rfl

/-- The interchange of an integer invertible ideal power with tensoring by an invertible
module, with the ideal power kept in the first tensor factor. -/
@[no_expose]
public noncomputable def idealPowerTensorIso (I L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] (n : ℤ) :
    idealPowerTerm X I n (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj (idealPowerTerm X I n M) :=
  (idealPowerCommuteNatIso X I L n).app M

/-- At the zeroth ideal power the interchange is the identity. -/
public theorem idealPowerTensorIso_zero (I L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] :
    (idealPowerTensorIso X I L M 0).hom = 𝟙 _ := by
  -- The integer recursion starts at degree `0` with `Iso.refl`; `commuteInt_zero` evaluates it
  -- there, so nothing has to be unfolded through the structure-sheaf spellings.
  have h : idealPowerCommuteNatIso X I L 0 = Iso.refl _ := commuteInt_zero _ _ _ _ _ _
  change ((idealPowerCommuteNatIso X I L 0).app M).hom = 𝟙 _
  rw [h]
  rfl

/-- The interchange is natural in the module. -/
public theorem idealPowerTensorIso_natural (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (n : ℤ) {M N : SheafOfModules.{u} Oₓ} (a : M ⟶ N) :
    (idealPowerTensorIso X I L M n).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map (idealPowerMap X I n a) =
      idealPowerMap X I n
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map a) ≫
        (idealPowerTensorIso X I L N n).hom :=
  ((idealPowerCommuteNatIso X I L n).hom.naturality a).symm

/-- The interchange respects the inclusion of consecutive ideal powers. -/
public theorem idealPowerTensorIso_incl (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] (n : ℤ) :
    idealPowerIncl X I ι n (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) ≫
      (idealPowerTensorIso X I L M n).hom =
    (idealPowerTensorIso X I L M (n + 1)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map (idealPowerIncl X I ι n M) := by
  let E := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L
  let a : E ⟶ 𝟭 _ :=
    { app := rightMultiply X.presheaf (Oₓ).property I ι
      naturality := fun {M N} f => rightMultiply_natural X.presheaf (Oₓ).property I ι f }
  rw [idealPowerIncl_eq_multiply, idealPowerIncl_eq_multiply]
  exact commuteInt_incl E G _ (idealPowerSuccNatIso X I)
    (tensorRightCommuteIso X.presheaf (Oₓ).property I L) (Iso.refl _) a (fun N => by
      let interchange : E ⋙ G ≅ G ⋙ E := tensorRightCommuteIso X.presheaf (Oₓ).property I L
      have multiplication : interchange.hom.app N ≫ a.app (G.obj N) = G.map (a.app N) :=
        tensorRightCommuteIso_multiply X.presheaf (Oₓ).property I L N ι
      exact (congrArg (interchange.inv.app N ≫ ·) multiplication.symm).trans
        (Iso.inv_hom_id_app_assoc interchange N (a.app (G.obj N)))) n M

/-- The interchange is the component of the natural interchange built by integer recursion. -/
private lemma idealPowerTensorIso_hom (I L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] (n : ℤ) :
    (idealPowerTensorIso X I L M n).hom = (idealPowerCommuteNatIso X I L n).hom.app M := rfl

/-- The natural interchange in degree `n + 1` is the one transported from degree `n`. -/
private lemma idealPowerCommuteNatIso_succ (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I] (n : ℤ) :
    idealPowerCommuteNatIso X I L (n + 1) =
      commuteSucc ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L) _ (idealPowerSuccNatIso X I)
        (tensorRightCommuteIso X.presheaf (Oₓ).property I L) n
        (idealPowerCommuteNatIso X I L n) := by
  exact commuteInt_succ
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L)
    (fun degree => (tensorPowerEquivalence X.presheaf (Oₓ).property I degree).functor)
    (idealPowerSuccNatIso X I) (tensorRightCommuteIso X.presheaf (Oₓ).property I L)
    (Iso.refl _) n

/-- A degreewise interchange of the integer ideal powers of `I` with tensoring by `L`: a map in
every integer degree which is the identity in degree `0` and in each degree is transported from
the previous one along the successor comparison of ideal powers and the interchange of the two
tensor factors. -/
public structure IdealPowerTensorComparison (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] where
  /-- The interchange in degree `n`, at the module `M`. -/
  map : ∀ (n : ℤ) (M : SheafOfModules.{u} Oₓ),
    idealPowerTerm X I n (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj (idealPowerTerm X I n M)
  /-- In degree `0` the interchange is the identity. -/
  zero : ∀ M : SheafOfModules.{u} Oₓ, map 0 M = 𝟙 _
  /-- Degree `n + 1` is transported from degree `n`. -/
  succ : ∀ (n : ℤ) (M : SheafOfModules.{u} Oₓ),
    map (n + 1) M =
      (idealPowerSuccNatIso X I n).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I).map
          (X := idealPowerTerm X I n
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj M))
          (Y := ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj
            (idealPowerTerm X I n M)) (map n M) ≫
          (tensorRightCommuteIso X.presheaf (Oₓ).property I L).inv.app
            (idealPowerTerm X I n M) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map
            (X := ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I).obj
              (idealPowerTerm X I n M))
            (Y := idealPowerTerm X I (n + 1) M)
            ((idealPowerSuccNatIso X I n).hom.app M)

/-- `idealPowerTensorIso` is such a comparison. -/
public noncomputable def idealPowerTensorComparison (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] :
    IdealPowerTensorComparison X I L where
  map n M := (idealPowerTensorIso X I L M n).hom
  zero M := idealPowerTensorIso_zero X I L M
  succ n M := by
    simp only [idealPowerTensorIso_hom]
    rw [idealPowerCommuteNatIso_succ]
    rfl

@[simp] public theorem idealPowerTensorComparison_map (I L M : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L] (n : ℤ) :
    (idealPowerTensorComparison X I L).map n M = (idealPowerTensorIso X I L M n).hom := rfl

/-- Any two such comparisons agree in **every** integer degree, negative ones included: the
degree-`0` normalization starts the recursion, and the recursion runs downwards as well as
upwards because tensoring by `I` is an equivalence, hence faithful. -/
@[stacks 0F9W "uniqueness of the degreewise interchange"]
public theorem IdealPowerTensorComparison.map_eq (I L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (c d : IdealPowerTensorComparison X I L) (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    c.map n M = d.map n M := by
  let idealTensor := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I
  let moduleTensor := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L
  have key : ∀ k : ℤ, c.map (k + 1) M = d.map (k + 1) M → c.map k M = d.map k M := by
    intro k h
    let degreeTerm : SheafOfModules.{u} Oₓ := idealPowerTerm X I k M
    let nextTerm : SheafOfModules.{u} Oₓ := idealPowerTerm X I (k + 1) M
    let firstStep : idealTensor.obj (idealPowerTerm X I k (moduleTensor.obj M)) ≅
        idealPowerTerm X I (k + 1) (moduleTensor.obj M) :=
      (idealPowerSuccNatIso X I k).app (moduleTensor.obj M)
    let successor : idealTensor.obj degreeTerm ≅ nextTerm := (idealPowerSuccNatIso X I k).app M
    let interchange : idealTensor.obj (moduleTensor.obj degreeTerm) ≅
        moduleTensor.obj (idealTensor.obj degreeTerm) :=
      ((tensorRightCommuteIso X.presheaf (Oₓ).property I L).app degreeTerm).symm
    let lastStep := interchange ≪≫ moduleTensor.mapIso successor
    have comparison : firstStep.inv ≫ idealTensor.map
        (X := idealPowerTerm X I k (moduleTensor.obj M)) (Y := moduleTensor.obj degreeTerm)
        (c.map k M) ≫ lastStep.hom =
        firstStep.inv ≫ idealTensor.map
          (X := idealPowerTerm X I k (moduleTensor.obj M)) (Y := moduleTensor.obj degreeTerm)
          (d.map k M) ≫ lastStep.hom :=
      (c.succ k M).symm.trans (h.trans (d.succ k M))
    apply idealTensor.map_injective
    exact (cancel_mono lastStep.hom).mp ((cancel_epi firstStep.inv).mp comparison)
  induction n using (Int.inductionOn' · 0) with
  | zero => rw [c.zero, d.zero]
  | succ k hk ih => rw [c.succ, d.succ, ih]
  | pred k hk ih =>
    refine key (k - 1) ?_
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1]
    exact ih

/-- Degreewise, the two fibre products defining the décalage terms of `F ⊗ L` and of `F` are
identified: tensoring by `L` is an equivalence, hence preserves the fibre product, and the
diagrams are identified by the interchange of ideal powers. -/
private noncomputable def etaTermTensorIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F) n ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).obj (etaTerm X I ι F n) := by
  let G : SheafOfModules.{u} Oₓ ⥤ SheafOfModules.{u} Oₓ :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L
  have : G.IsEquivalence := tensorRightFunctor_isEquivalence X.presheaf (Oₓ).property L
  change pullback (idealPowerMap X I n (G.map (F.d n (n + 1))))
    (idealPowerIncl X I ι n (G.obj (F.X (n + 1)))) ≅ G.obj (etaTerm X I ι F n)
  let leftComparison : idealPowerTerm X I n (G.obj (F.X n)) ≅
      G.obj (idealPowerTerm X I n (F.X n)) := idealPowerTensorIso X I L (F.X n) n
  let rightComparison : idealPowerTerm X I (n + 1) (G.obj (F.X (n + 1))) ≅
      G.obj (idealPowerTerm X I (n + 1) (F.X (n + 1))) :=
    idealPowerTensorIso X I L (F.X (n + 1)) (n + 1)
  let baseComparison : idealPowerTerm X I n (G.obj (F.X (n + 1))) ≅
      G.obj (idealPowerTerm X I n (F.X (n + 1))) := idealPowerTensorIso X I L (F.X (n + 1)) n
  let sourceLeft : idealPowerTerm X I n (G.obj (F.X n)) ⟶
      idealPowerTerm X I n (G.obj (F.X (n + 1))) :=
    idealPowerMap X I n (G.map (F.d n (n + 1)))
  let sourceRight : idealPowerTerm X I (n + 1) (G.obj (F.X (n + 1))) ⟶
      idealPowerTerm X I n (G.obj (F.X (n + 1))) :=
    idealPowerIncl X I ι n (G.obj (F.X (n + 1)))
  let targetLeft : G.obj (idealPowerTerm X I n (F.X n)) ⟶
      G.obj (idealPowerTerm X I n (F.X (n + 1))) :=
    G.map (idealPowerMap X I n (F.d n (n + 1)))
  let targetRight : G.obj (idealPowerTerm X I (n + 1) (F.X (n + 1))) ⟶
      G.obj (idealPowerTerm X I n (F.X (n + 1))) :=
    G.map (idealPowerIncl X I ι n (F.X (n + 1)))
  have leftSquare : sourceLeft ≫ baseComparison.hom = leftComparison.hom ≫ targetLeft :=
    (idealPowerTensorIso_natural X I L n (F.d n (n + 1))).symm
  have rightSquare : sourceRight ≫ baseComparison.hom = rightComparison.hom ≫ targetRight :=
    idealPowerTensorIso_incl X I ι L (F.X (n + 1)) n
  let pullbackComparison : pullback sourceLeft sourceRight ≅ pullback targetLeft targetRight :=
    @asIso _ _ (pullback sourceLeft sourceRight) (pullback targetLeft targetRight)
      (pullback.map sourceLeft sourceRight targetLeft targetRight
        leftComparison.hom rightComparison.hom baseComparison.hom leftSquare rightSquare)
      (pullback.map_isIso sourceLeft sourceRight targetLeft targetRight
        leftComparison.hom rightComparison.hom baseComparison.hom leftSquare rightSquare)
  let preservedPullback : G.obj (etaTerm X I ι F n) ≅ pullback targetLeft targetRight :=
    PreservesPullback.iso G
      (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1)))
  exact pullbackComparison ≪≫ preservedPullback.symm

/-- The first projection of the degreewise comparison. -/
private theorem etaTermTensorIso_fst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    (etaTermTensorIso X I ι L F n).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map
        (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
          (idealPowerIncl X I ι n (F.X (n + 1)))) =
      pullback.fst _ _ ≫ (idealPowerTensorIso X I L (F.X n) n).hom := by
  simp only [etaTermTensorIso, id_eq, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
    PreservesPullback.iso_inv_fst, pullback.map, pullback.lift_fst]
  rfl

/-- The second projection of the degreewise comparison. -/
private theorem etaTermTensorIso_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    (etaTermTensorIso X I ι L F n).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map
        (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
          (idealPowerIncl X I ι n (F.X (n + 1)))) =
      pullback.snd _ _ ≫ (idealPowerTensorIso X I L (F.X (n + 1)) (n + 1)).hom := by
  simp only [etaTermTensorIso, id_eq, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
    PreservesPullback.iso_inv_snd, pullback.map, pullback.lift_snd]
  rfl

/-- The differential of the décalage is killed by the second projection one degree up. -/
private theorem etaDifferentialData_d_comp_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (D : EtaDifferentialData X I ι F) (n : ℤ) :
    D.d n ≫ pullback.snd (idealPowerMap X I (n + 1) (F.d (n + 1) ((n + 1) + 1)))
      (idealPowerIncl X I ι (n + 1) (F.X ((n + 1) + 1))) = 0 := by
  rw [← D.d_fst (n + 1), ← Category.assoc, D.d_comp_d, zero_comp]

/-- **Stacks Project, Tag 0F9W.** Décalage by an invertible ideal commutes with tensoring by an
invertible module: the décalage of `F ⊗ L` is canonically isomorphic to the décalage of `F`
tensored by `L`. -/
@[stacks 0F9W, no_expose]
public noncomputable def etaTensorInvertible (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) :
    etaObj X I ι
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)
          (fun n => idealTorsionFree_tensorInvertible X I ι L (F.X n) (hF n)) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (etaObj X I ι F hF) := by
  let G : SheafOfModules.{u} Oₓ ⥤ SheafOfModules.{u} Oₓ :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L
  have : G.IsEquivalence := tensorRightFunctor_isEquivalence X.presheaf (Oₓ).property L
  let F' : CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let D := etaDifferentialData X I ι F hF
  let D' := etaDifferentialData X I ι F'
    (fun n => idealTorsionFree_tensorInvertible X I ι L (F.X n) (hF n))
  refine HomologicalComplex.Hom.isoOfComponents (etaTermTensorIso X I ι L F) ?_
  intro n m hnm
  have hm : n + 1 = m := hnm
  subst m
  change (etaTermTensorIso X I ι L F n).hom ≫ G.map (CochainComplex.of.d _ D.d n (n + 1)) =
    CochainComplex.of.d _ D'.d n (n + 1) ≫ (etaTermTensorIso X I ι L F (n + 1)).hom
  rw [CochainComplex.of_d, CochainComplex.of_d]
  apply (cancel_mono (PreservesPullback.iso G
    (idealPowerMap X I (n + 1) (F.d (n + 1) ((n + 1) + 1)))
    (idealPowerIncl X I ι (n + 1) (F.X ((n + 1) + 1)))).hom).mp
  apply pullback.hom_ext (C := SheafOfModules.{u} Oₓ)
    (f := G.map (idealPowerMap X I (n + 1) (F.d (n + 1) (n + 1 + 1))))
    (g := G.map (idealPowerIncl X I ι (n + 1) (F.X (n + 1 + 1))))
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst]
    rw [← G.map_comp, D.d_fst]
    rw [etaTermTensorIso_fst, ← Category.assoc, D'.d_fst]
    exact etaTermTensorIso_snd X I ι L F n
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd]
    rw [← G.map_comp, etaDifferentialData_d_comp_snd X I ι F D n, Functor.map_zero, comp_zero]
    rw [etaTermTensorIso_snd, ← Category.assoc,
      etaDifferentialData_d_comp_snd X I ι F' D' n, zero_comp]

/-- On the first projection of the defining fibre product, the comparison of Tag 0F9W is the
interchange of the `n`-th ideal power with the invertible tensor factor. -/
@[stacks 0F9W "first degreewise projection"]
public theorem etaTensorInvertible_fst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaTensorInvertible X I ι L F hF).hom.f n ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map
          (X := etaTerm X I ι F n) (Y := idealPowerTerm X I n (F.X n))
          (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
            (idealPowerIncl X I ι n (F.X (n + 1)))) =
      pullback.fst _ _ ≫ (idealPowerTensorIso X I L (F.X n) n).hom :=
  etaTermTensorIso_fst X I ι L F n

/-- On the second projection of the defining fibre product, the comparison of Tag 0F9W is the
interchange of the `(n+1)`-st ideal power with the invertible tensor factor. -/
@[stacks 0F9W "second degreewise projection"]
public theorem etaTensorInvertible_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property I]
    (L : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (Oₓ).property L]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaTensorInvertible X I ι L F hF).hom.f n ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj L).map
          (X := etaTerm X I ι F n) (Y := idealPowerTerm X I (n + 1) (F.X (n + 1)))
          (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
            (idealPowerIncl X I ι n (F.X (n + 1)))) =
      pullback.snd _ _ ≫ (idealPowerTensorIso X I L (F.X (n + 1)) (n + 1)).hom :=
  etaTermTensorIso_snd X I ι L F n

end Stacks.IdealTorsion.Eta
