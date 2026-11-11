module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBockstein
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealInclSucc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc

/-!
# Tensoring on the left with a module commutes with integer ideal powers

Let `X` be a ringed space, `I` an invertible sheaf of `O_X`-modules and `ι : I ⟶ O_X`. For an
integer `n` write `I^n ⊗ M` for `Stacks.IdealTorsion.Eta.idealPowerTerm X I n M`, the image of
`M` under the `n`-th integer power of the autoequivalence `- ⊗ I`. For an arbitrary
`O_X`-module `N` this file constructs the isomorphism

`N ⊗ (I^n ⊗ O_X) ≅ I^n ⊗ N`

in every integer degree `n`, proves that it is natural in `N` and compatible with the inclusions
`I^{n+1} ⊗ - ⟶ I^n ⊗ -` induced by `ι`, and deduces the corresponding statements for the
quotients `I^n/I^{n+1}` and `I^n/I^{n+2}`, using that `N ⊗ -` preserves cokernels.

No hypothesis is placed on `N`: it need not be invertible, flat or `I`-torsion-free.

## Main definitions

* `Stacks.IdealTorsion.ReductionDerived.idealPowerTensorLeftIso`: the isomorphism
  `N ⊗ (I^n ⊗ O_X) ≅ I^n ⊗ N`.
* `Stacks.IdealTorsion.ReductionDerived.tensorCokernelIso`: `N ⊗ coker g ≅ coker (N ⊗ g)`.
* `Stacks.IdealTorsion.ReductionDerived.powerQuotientTensorIso`: `N ⊗ I^n/I^{n+1}` is the
  cokernel of `I^{n+1} ⊗ N ⟶ I^n ⊗ N`.
* `Stacks.IdealTorsion.ReductionDerived.powerQuotientTwoTensorIso`: the same for `I^n/I^{n+2}`.
* `Stacks.IdealTorsion.ReductionDerived.powerQuotientShortComplexTensorIso`: the successive
  quotient sequence `I^{n+1}/I^{n+2} → I^n/I^{n+2} → I^n/I^{n+1}` tensored by `N`, identified
  with the successive quotient sequence of `I^{n+2} ⊗ N ⟶ I^{n+1} ⊗ N ⟶ I^n ⊗ N`.

## Main results

* `idealPowerTensorLeftIso_natural`: the isomorphism is natural in `N`.
* `idealPowerTensorLeftIso_incl`: it carries the ideal-power inclusion of `O_X` tensored by `N`
  to the ideal-power inclusion of `N`.
* `powerQuotientTensorIso_natural`, `powerQuotientTwoTensorIso_natural`: the quotient
  isomorphisms are natural in `N`.

## Implementation notes

The isomorphism is the transport `Stacks.Equivalence.powIntertwineObj` of the associativity
constraint `N ⊗ (M ⊗ I) ≅ (N ⊗ M) ⊗ I` along the integer iterates of `- ⊗ I`, followed by the
right unit constraint `N ⊗ O_X ≅ N` inside `I^n ⊗ -`. The transport is natural in the module it
is applied to (`Stacks.Equivalence.powIntertwineObj_naturality`); naturality in `N` is a
naturality in the intertwining functor `N ⊗ -` instead, which is proved here
(`powIntertwineObj_natural_functor`) by the same induction.

The coherence computations are carried out in the symmetric monoidal structure
`Stacks.SheafOfModules.sheafTensorMonoidal`, whose tensor product, whiskerings and constraints
are, definitionally, the sheaf tensor product of Tag 01CA and its fixed constraints.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

open Stacks.SheafOfModules.Invertible (tensorRightFunctor_isEquivalence tensorProductAssociator
  tensorProductRightUnitor)

open Stacks.Equivalence (inverseIntertwineObj powNatIntertwineObj powIntertwineObj)

open Stacks.IdealTorsion.Eta (idealPowerTerm idealPowerIncl idealPowerMap)

universe v₁ v₂ u₁ u₂ u

namespace Stacks.IdealTorsion.ReductionDerived

/-! ### Naturality of the transported comparison in the intertwining functor -/

section Abstract

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **The comparison for the quasi-inverses is natural in the intertwining functor.** If a
natural transformation `φ : R ⟶ R'` is compatible with the comparisons `α` and `α'`, it is
compatible with the comparisons `Stacks.Equivalence.inverseIntertwineObj` built from them. -/
theorem inverseIntertwineObj_natural_functor (e : A ≌ A) (e' : B ≌ B) {R R' : A ⥤ B}
    (φ : R ⟶ R')
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (α' : ∀ M : A, R'.obj (e.functor.obj M) ≅ e'.functor.obj (R'.obj M))
    (hφ : ∀ M : A, φ.app (e.functor.obj M) ≫ (α' M).hom = (α M).hom ≫ e'.functor.map (φ.app M))
    (N : A) :
    φ.app (e.inverse.obj N) ≫ (inverseIntertwineObj e e' R' α' N).hom =
      (inverseIntertwineObj e e' R α N).hom ≫ e'.inverse.map (φ.app N) := by
  have key : ∀ (S : A ⥤ B) (β : ∀ M : A, S.obj (e.functor.obj M) ≅ e'.functor.obj (S.obj M)),
      (inverseIntertwineObj e e' S β N).hom =
        e'.unit.app (S.obj (e.inverse.obj N)) ≫
          e'.inverse.map ((β (e.inverse.obj N)).inv ≫ S.map (e.counit.app N)) := fun _ _ => rfl
  have hunit : φ.app (e.inverse.obj N) ≫ e'.unit.app (R'.obj (e.inverse.obj N)) =
      e'.unit.app (R.obj (e.inverse.obj N)) ≫
        e'.inverse.map (e'.functor.map (φ.app (e.inverse.obj N))) :=
    e'.unit.naturality _
  have hα : e'.functor.map (φ.app (e.inverse.obj N)) ≫ (α' (e.inverse.obj N)).inv =
      (α (e.inverse.obj N)).inv ≫ φ.app (e.functor.obj (e.inverse.obj N)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hφ, Iso.inv_hom_id_assoc]
  have hc : φ.app (e.functor.obj (e.inverse.obj N)) ≫ R'.map (e.counit.app N) =
      R.map (e.counit.app N) ≫ φ.app N :=
    (φ.naturality _).symm
  rw [key, key, ← Category.assoc, hunit, Category.assoc, ← Functor.map_comp, Category.assoc,
    ← Functor.map_comp]
  congr 2
  rw [← Category.assoc, hα, Category.assoc, hc, Category.assoc]

/-- **The comparison for natural-number iterates is natural in the intertwining functor**, by
the induction `Stacks.Equivalence.powNatIntertwineObj` recurses along. -/
theorem powNatIntertwineObj_natural_functor (e : A ≌ A) (e' : B ≌ B) {R R' : A ⥤ B}
    (φ : R ⟶ R')
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (α' : ∀ M : A, R'.obj (e.functor.obj M) ≅ e'.functor.obj (R'.obj M))
    (hφ : ∀ M : A, φ.app (e.functor.obj M) ≫ (α' M).hom = (α M).hom ≫ e'.functor.map (φ.app M)) :
    ∀ (n : ℕ) (M : A),
      φ.app ((e.powNat n).functor.obj M) ≫ (powNatIntertwineObj e e' R' α' n M).hom =
        (powNatIntertwineObj e e' R α n M).hom ≫ (e'.powNat n).functor.map (φ.app M)
  | 0, M => by
      change φ.app M ≫ 𝟙 (R'.obj M) = 𝟙 (R.obj M) ≫ φ.app M
      rw [Category.comp_id, Category.id_comp]
  | 1, M => hφ M
  | n + 2, M => by
      have ih := powNatIntertwineObj_natural_functor e e' φ α α' hφ (n + 1) (e.functor.obj M)
      change φ.app ((e.powNat (n + 1)).functor.obj (e.functor.obj M)) ≫
          ((powNatIntertwineObj e e' R' α' (n + 1) (e.functor.obj M)).hom ≫
            (e'.powNat (n + 1)).functor.map (α' M).hom) =
        ((powNatIntertwineObj e e' R α (n + 1) (e.functor.obj M)).hom ≫
            (e'.powNat (n + 1)).functor.map (α M).hom) ≫
          (e'.powNat (n + 1)).functor.map (e'.functor.map (φ.app M))
      rw [← Category.assoc, ih, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, hφ M]

/-- **The comparison for integer iterates is natural in the intertwining functor.** A negative
exponent is the natural-number case for the quasi-inverses, where the compatibility of `φ` is
`inverseIntertwineObj_natural_functor`. -/
theorem powIntertwineObj_natural_functor (e : A ≌ A) (e' : B ≌ B) {R R' : A ⥤ B}
    (φ : R ⟶ R')
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (α' : ∀ M : A, R'.obj (e.functor.obj M) ≅ e'.functor.obj (R'.obj M))
    (hφ : ∀ M : A, φ.app (e.functor.obj M) ≫ (α' M).hom = (α M).hom ≫ e'.functor.map (φ.app M)) :
    ∀ (n : ℤ) (M : A),
      φ.app ((e ^ n).functor.obj M) ≫ (powIntertwineObj e e' R' α' n M).hom =
        (powIntertwineObj e e' R α n M).hom ≫ (e' ^ n).functor.map (φ.app M)
  | Int.ofNat n, M => powNatIntertwineObj_natural_functor e e' φ α α' hφ n M
  | Int.negSucc n, M =>
      powNatIntertwineObj_natural_functor e.symm e'.symm φ
        (fun P => inverseIntertwineObj e e' R α P) (fun P => inverseIntertwineObj e e' R' α' P)
        (fun P => inverseIntertwineObj_natural_functor e e' φ α α' hφ P) (n + 1) M

end Abstract

/-! ### The left tensor factor and the integer ideal powers -/

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- The monoidal structure whose tensor product and constraints are, definitionally, the sheaf
tensor product of Tag 01CA and its fixed constraints. -/
noncomputable local instance sheafTensorMonoidalOfRingedSpace :
    MonoidalCategory (SheafOfModules.{u} Oₓ) :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj (Oₓ).property

/-- The autoequivalence `- ⊗ I` of the category of `O_X`-modules, whose integer iterates are
the ideal powers `Stacks.IdealTorsion.Eta.idealPowerTerm`. -/
noncomputable abbrev tensorIdealEquivalence (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I] :
    SheafOfModules.{u} Oₓ ≌ SheafOfModules.{u} Oₓ :=
  @Functor.asEquivalence _ _ _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
    (tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I)

/-- The inverse associativity constraint `N ⊗ (M ⊗ I) ≅ (N ⊗ M) ⊗ I`: the comparison by which
`N ⊗ -` intertwines the autoequivalence `- ⊗ I` with itself. -/
noncomputable def tensorLeftAssocIso (I N M : SheafOfModules.{u} Oₓ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj M) :=
  (tensorProductAssociator X.sheaf.obj (Oₓ).property N M I).symm

/-- **Tensoring on the left by a module commutes with integer ideal powers**:
`N ⊗ (I^n ⊗ O_X) ≅ I^n ⊗ N` for every integer `n` and every module `N`. It is the associativity
constraint transported to the `n`-th iterate of `- ⊗ I`, followed by the right unit constraint
`N ⊗ O_X ≅ N` inside `I^n ⊗ -`. -/
noncomputable def idealPowerTensorLeftIso (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj
        (idealPowerTerm X I n 𝒪) ≅ idealPowerTerm X I n N :=
  powIntertwineObj (tensorIdealEquivalence X I) (tensorIdealEquivalence X I)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N)
      (tensorLeftAssocIso X I N) n 𝒪 ≪≫
    ((tensorIdealEquivalence X I) ^ n).functor.mapIso
      (tensorProductRightUnitor X.sheaf.obj (Oₓ).property N)

/-- The forward map of `idealPowerTensorLeftIso`, unfolded into the transported comparison and
the right unit constraint. -/
theorem idealPowerTensorLeftIso_hom (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (idealPowerTensorLeftIso X I N n).hom =
      (powIntertwineObj (tensorIdealEquivalence X I) (tensorIdealEquivalence X I)
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N)
          (tensorLeftAssocIso X I N) n 𝒪).hom ≫
        idealPowerMap X I n (tensorProductRightUnitor X.sheaf.obj (Oₓ).property N).hom :=
  rfl

/-- **`idealPowerTensorLeftIso` is natural in the module `N`.** -/
theorem idealPowerTensorLeftIso_natural (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {N N' : SheafOfModules.{u} Oₓ} (f : N ⟶ N') (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app
        (idealPowerTerm X I n 𝒪) ≫ (idealPowerTensorLeftIso X I N' n).hom =
      (idealPowerTensorLeftIso X I N n).hom ≫ idealPowerMap X I n f := by
  have hφ : ∀ M : SheafOfModules.{u} Oₓ,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app
          ((tensorIdealEquivalence X I).functor.obj M) ≫ (tensorLeftAssocIso X I N' M).hom =
        (tensorLeftAssocIso X I N M).hom ≫ (tensorIdealEquivalence X I).functor.map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app M) :=
    fun M => associator_inv_naturality_left f M I
  have h := powIntertwineObj_natural_functor (tensorIdealEquivalence X I)
    (tensorIdealEquivalence X I)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f)
    (tensorLeftAssocIso X I N) (tensorLeftAssocIso X I N') hφ n 𝒪
  have hρ : f ▷ 𝟙_ (SheafOfModules.{u} Oₓ) ≫ (ρ_ N').hom = (ρ_ N).hom ≫ f :=
    rightUnitor_naturality f
  have hmap : ((tensorIdealEquivalence X I) ^ n).functor.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app 𝒪) ≫
      idealPowerMap X I n (tensorProductRightUnitor X.sheaf.obj (Oₓ).property N').hom =
      idealPowerMap X I n (tensorProductRightUnitor X.sheaf.obj (Oₓ).property N).hom ≫
        idealPowerMap X I n f :=
    ((((tensorIdealEquivalence X I) ^ n).functor.map_comp _ _).symm.trans
      (congrArg ((tensorIdealEquivalence X I) ^ n).functor.map hρ)).trans
        (((tensorIdealEquivalence X I) ^ n).functor.map_comp _ _)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hmap).trans (Category.assoc _ _ _).symm)))

/-- **`idealPowerTensorLeftIso` is compatible with the ideal-power inclusions**: it carries the
inclusion `I^{n+1} ⊗ O_X ⟶ I^n ⊗ O_X`, tensored on the left by `N`, to the inclusion
`I^{n+1} ⊗ N ⟶ I^n ⊗ N`. -/
@[reassoc]
theorem idealPowerTensorLeftIso_incl (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (idealPowerIncl X I ι n 𝒪) ≫ (idealPowerTensorLeftIso X I N n).hom =
      (idealPowerTensorLeftIso X I N (n + 1)).hom ≫ idealPowerIncl X I ι n N := by
  let R := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N
  let a : (tensorIdealEquivalence X I).functor ⟶ 𝟭 (SheafOfModules.{u} Oₓ) :=
    { app := fun P => idealPowerIncl X I ι 0 P
      naturality := fun _ _ g => (Stacks.IdealTorsion.Eta.idealPowerIncl_natural X I ι 0 g).symm }
  let ι' : I ⟶ 𝟙_ (SheafOfModules.{u} Oₓ) := ι
  have hcore : ∀ P : SheafOfModules.{u} Oₓ,
      idealPowerIncl X I ι 0 P = (P ◁ ι') ≫ (ρ_ P).hom :=
    fun P => (Stacks.IdealTorsion.Eta.idealPowerIncl_zero_eq_core X I ι P).trans
      (congrArg (· ≫ (ρ_ P).hom)
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf (𝟙 P) ι))
  have ha : ∀ P : SheafOfModules.{u} Oₓ,
      R.map (a.app P) = (tensorLeftAssocIso X I N P).hom ≫ a.app (R.obj P) := by
    intro P
    have hmon : N ◁ ((P ◁ ι') ≫ (ρ_ P).hom) =
        (α_ N P I).inv ≫ ((N ⊗ P) ◁ ι') ≫ (ρ_ (N ⊗ P)).hom := by
      rw [rightUnitor_tensor_hom, ← associator_inv_naturality_right_assoc,
        Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp]
    exact ((congrArg R.map (hcore P)).trans hmon).trans
      (congrArg ((tensorLeftAssocIso X I N P).hom ≫ ·) (hcore (R.obj P)).symm)
  have hincl := Stacks.Equivalence.powIntertwineObj_incl (tensorIdealEquivalence X I)
    (tensorIdealEquivalence X I) R (tensorLeftAssocIso X I N) a a ha n 𝒪
  have h : R.map (idealPowerIncl X I ι n 𝒪) ≫
      (powIntertwineObj (tensorIdealEquivalence X I) (tensorIdealEquivalence X I) R
        (tensorLeftAssocIso X I N) n 𝒪).hom =
      (powIntertwineObj (tensorIdealEquivalence X I) (tensorIdealEquivalence X I) R
        (tensorLeftAssocIso X I N) (n + 1) 𝒪).hom ≫ idealPowerIncl X I ι n (R.obj 𝒪) := by
    rw [Stacks.IdealTorsion.Eta.idealPowerIncl_eq_powSuccIso_inv_comp X I ι n 𝒪,
      Stacks.IdealTorsion.Eta.idealPowerIncl_eq_powSuccIso_inv_comp X I ι n (R.obj 𝒪)]
    exact hincl
  rw [idealPowerTensorLeftIso_hom, idealPowerTensorLeftIso_hom, ← Category.assoc, h,
    Category.assoc, Category.assoc]
  congr 1
  exact Stacks.IdealTorsion.Eta.idealPowerIncl_natural X I ι n
    (tensorProductRightUnitor X.sheaf.obj (Oₓ).property N).hom

/-! ### Tensoring on the left preserves cokernels -/

/-- **Tensoring on the left by a module preserves cokernels**: `N ⊗ coker g ≅ coker (N ⊗ g)`.
The functor `N ⊗ -` is a left adjoint, the category of `O_X`-modules being monoidal closed. -/
noncomputable def tensorCokernelIso (N : SheafOfModules.{u} Oₓ) {A B : SheafOfModules.{u} Oₓ}
    (g : A ⟶ B) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj (cokernel g) ≅
      cokernel (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map g) :=
  PreservesCokernel.iso _ g

/-- `tensorCokernelIso` carries the tensored projection onto the cokernel to the projection. -/
@[reassoc]
theorem tensorCokernelIso_π (N : SheafOfModules.{u} Oₓ) {A B : SheafOfModules.{u} Oₓ}
    (g : A ⟶ B) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π g) ≫ (tensorCokernelIso X N g).hom =
      cokernel.π
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map g) :=
  PreservesCokernel.π_iso_hom _ g

/-- Two morphisms out of `N ⊗ coker g` agree as soon as they agree after the tensored
projection `N ⊗ B ⟶ N ⊗ coker g`. -/
theorem tensorCokernel_hom_ext (N : SheafOfModules.{u} Oₓ) {A B T : SheafOfModules.{u} Oₓ}
    (g : A ⟶ B)
    {k₁ k₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj
      (cokernel g) ⟶ T}
    (h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π g) ≫ k₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π g) ≫ k₂) :
    k₁ = k₂ := by
  rw [← cancel_epi (tensorCokernelIso X N g).inv, ← cancel_epi (cokernel.π _),
    ← tensorCokernelIso_π X N g]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact h

/-- The cokernel of a morphism `g` tensored on the left by `N`, identified with the cokernel of
a morphism `g'` that `N ⊗ g` is isomorphic to. -/
noncomputable def tensorCokernelMapIso (N : SheafOfModules.{u} Oₓ)
    {A B A' B' : SheafOfModules.{u} Oₓ} (g : A ⟶ B) (g' : A' ⟶ B')
    (eA : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj A ≅ A')
    (eB : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj B ≅ B')
    (w : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map g ≫
      eB.hom = eA.hom ≫ g') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj (cokernel g) ≅
      cokernel g' :=
  tensorCokernelIso X N g ≪≫ cokernel.mapIso _ g' eA eB w

/-- `tensorCokernelMapIso` carries the tensored projection to `eB` followed by the
projection. -/
@[reassoc]
theorem tensorCokernelMapIso_π (N : SheafOfModules.{u} Oₓ)
    {A B A' B' : SheafOfModules.{u} Oₓ} (g : A ⟶ B) (g' : A' ⟶ B')
    (eA : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj A ≅ A')
    (eB : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj B ≅ B')
    (w : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map g ≫
      eB.hom = eA.hom ≫ g') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π g) ≫ (tensorCokernelMapIso X N g g' eA eB w).hom =
      eB.hom ≫ cokernel.π g' := by
  change _ ≫ (tensorCokernelIso X N g).hom ≫ cokernel.map _ g' eA.hom eB.hom w = _
  rw [tensorCokernelIso_π_assoc, cokernel.π_desc]

/-! ### The power quotients tensored on the left -/

/-- **`N ⊗ I^n/I^{n+1}` is the cokernel of `I^{n+1} ⊗ N ⟶ I^n ⊗ N`.** -/
noncomputable def powerQuotientTensorIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj
        (Bockstein.powerQuotient X I ι n) ≅ cokernel (idealPowerIncl X I ι n N) :=
  tensorCokernelMapIso X N (idealPowerIncl X I ι n 𝒪) (idealPowerIncl X I ι n N)
    (idealPowerTensorLeftIso X I N (n + 1)) (idealPowerTensorLeftIso X I N n)
    (idealPowerTensorLeftIso_incl X I ι N n)

/-- `powerQuotientTensorIso` carries the tensored projection to `idealPowerTensorLeftIso`
followed by the projection. -/
@[reassoc]
theorem powerQuotientTensorIso_π (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π (idealPowerIncl X I ι n 𝒪)) ≫ (powerQuotientTensorIso X I ι N n).hom =
      (idealPowerTensorLeftIso X I N n).hom ≫ cokernel.π (idealPowerIncl X I ι n N) :=
  tensorCokernelMapIso_π X N _ _ _ _ _

/-- **`powerQuotientTensorIso` is natural in `N`**, the map on the right being the one induced
on cokernels by the ideal powers of `f`. -/
theorem powerQuotientTensorIso_natural (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {N N' : SheafOfModules.{u} Oₓ} (f : N ⟶ N') (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app
        (Bockstein.powerQuotient X I ι n) ≫ (powerQuotientTensorIso X I ι N' n).hom =
      (powerQuotientTensorIso X I ι N n).hom ≫
        cokernel.map (idealPowerIncl X I ι n N) (idealPowerIncl X I ι n N')
          (idealPowerMap X I (n + 1) f) (idealPowerMap X I n f)
          (Stacks.IdealTorsion.Eta.idealPowerIncl_natural X I ι n f) := by
  apply tensorCokernel_hom_ext X N
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, powerQuotientTensorIso_π,
    powerQuotientTensorIso_π_assoc, ← Category.assoc, idealPowerTensorLeftIso_natural,
    Category.assoc, cokernel.π_desc]

/-- **`N ⊗ I^n/I^{n+2}` is the cokernel of `I^{n+2} ⊗ N ⟶ I^n ⊗ N`.** -/
noncomputable def powerQuotientTwoTensorIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).obj
        (cokernel (idealPowerIncl X I ι (n + 1) 𝒪 ≫ idealPowerIncl X I ι n 𝒪)) ≅
      cokernel (idealPowerIncl X I ι (n + 1) N ≫ idealPowerIncl X I ι n N) :=
  tensorCokernelMapIso X N (idealPowerIncl X I ι (n + 1) 𝒪 ≫ idealPowerIncl X I ι n 𝒪)
    (idealPowerIncl X I ι (n + 1) N ≫ idealPowerIncl X I ι n N)
    (idealPowerTensorLeftIso X I N (n + 1 + 1)) (idealPowerTensorLeftIso X I N n)
    (by
      rw [Functor.map_comp, Category.assoc, idealPowerTensorLeftIso_incl, ← Category.assoc,
        idealPowerTensorLeftIso_incl, Category.assoc])

/-- `powerQuotientTwoTensorIso` carries the tensored projection to `idealPowerTensorLeftIso`
followed by the projection. -/
@[reassoc]
theorem powerQuotientTwoTensorIso_π (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N).map
        (cokernel.π (idealPowerIncl X I ι (n + 1) 𝒪 ≫ idealPowerIncl X I ι n 𝒪)) ≫
          (powerQuotientTwoTensorIso X I ι N n).hom =
      (idealPowerTensorLeftIso X I N n).hom ≫
        cokernel.π (idealPowerIncl X I ι (n + 1) N ≫ idealPowerIncl X I ι n N) :=
  tensorCokernelMapIso_π X N _ _ _ _ _

/-- **`powerQuotientTwoTensorIso` is natural in `N`**, the map on the right being the one
induced on cokernels by the ideal powers of `f`. -/
theorem powerQuotientTwoTensorIso_natural (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {N N' : SheafOfModules.{u} Oₓ} (f : N ⟶ N') (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).map f).app
        (cokernel (idealPowerIncl X I ι (n + 1) 𝒪 ≫ idealPowerIncl X I ι n 𝒪)) ≫
          (powerQuotientTwoTensorIso X I ι N' n).hom =
      (powerQuotientTwoTensorIso X I ι N n).hom ≫
        cokernel.map (idealPowerIncl X I ι (n + 1) N ≫ idealPowerIncl X I ι n N)
          (idealPowerIncl X I ι (n + 1) N' ≫ idealPowerIncl X I ι n N')
          (idealPowerMap X I (n + 1 + 1) f) (idealPowerMap X I n f)
          (by
            rw [Category.assoc, Stacks.IdealTorsion.Eta.idealPowerIncl_natural,
              ← Category.assoc, Stacks.IdealTorsion.Eta.idealPowerIncl_natural,
              Category.assoc]) := by
  apply tensorCokernel_hom_ext X N
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, powerQuotientTwoTensorIso_π,
    powerQuotientTwoTensorIso_π_assoc, ← Category.assoc, idealPowerTensorLeftIso_natural,
    Category.assoc, cokernel.π_desc]

/-- **The successive power-quotient sequence tensored on the left by `N`**,
`N ⊗ (I^{n+1}/I^{n+2} → I^n/I^{n+2} → I^n/I^{n+1})`, is isomorphic to the successive quotient
sequence of `I^{n+2} ⊗ N ⟶ I^{n+1} ⊗ N ⟶ I^n ⊗ N`. The three components are
`powerQuotientTensorIso` in degree `n + 1`, `powerQuotientTwoTensorIso` and
`powerQuotientTensorIso` in degree `n`. -/
noncomputable def powerQuotientShortComplexTensorIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (Bockstein.powerQuotientShortComplex X I ι n).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N) ≅
      Bockstein.quotientShortComplex (idealPowerIncl X I ι (n + 1) N) (idealPowerIncl X I ι n N) :=
  ShortComplex.isoMk (powerQuotientTensorIso X I ι N (n + 1)) (powerQuotientTwoTensorIso X I ι N n)
    (powerQuotientTensorIso X I ι N n)
    (by
      apply tensorCokernel_hom_ext X N
      dsimp only [ShortComplex.map_f]
      rw [powerQuotientTensorIso_π_assoc, ← Functor.map_comp_assoc, cokernel.π_desc,
        cokernel.π_desc, Functor.map_comp, Category.assoc, powerQuotientTwoTensorIso_π]
      exact (Category.assoc _ _ _).trans (idealPowerTensorLeftIso_incl_assoc X I ι N n _).symm)
    (by
      apply tensorCokernel_hom_ext X N
      dsimp only [ShortComplex.map_g]
      rw [powerQuotientTwoTensorIso_π_assoc, ← Functor.map_comp_assoc, cokernel.π_desc,
        cokernel.π_desc, powerQuotientTensorIso_π])

/-- The first component of `powerQuotientShortComplexTensorIso` is `powerQuotientTensorIso` in
degree `n + 1`. -/
theorem powerQuotientShortComplexTensorIso_hom_τ₁ (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (powerQuotientShortComplexTensorIso X I ι N n).hom.τ₁ =
      (powerQuotientTensorIso X I ι N (n + 1)).hom :=
  rfl

/-- The second component of `powerQuotientShortComplexTensorIso` is
`powerQuotientTwoTensorIso`. -/
theorem powerQuotientShortComplexTensorIso_hom_τ₂ (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (powerQuotientShortComplexTensorIso X I ι N n).hom.τ₂ =
      (powerQuotientTwoTensorIso X I ι N n).hom :=
  rfl

/-- The third component of `powerQuotientShortComplexTensorIso` is `powerQuotientTensorIso` in
degree `n`. -/
theorem powerQuotientShortComplexTensorIso_hom_τ₃ (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (powerQuotientShortComplexTensorIso X I ι N n).hom.τ₃ =
      (powerQuotientTensorIso X I ι N n).hom :=
  rfl

end Stacks.IdealTorsion.ReductionDerived

end
