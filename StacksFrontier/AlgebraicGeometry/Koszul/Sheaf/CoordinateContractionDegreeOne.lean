module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.ContractionCocycle
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulAugmentation

/-!
# The coordinate contraction in degree one is the coordinate projection

Let `O♯` be a sheaf of commutative rings on a site `(C, J)`, let `F` be a sheaf of `O♯`-modules
and let `A` be a bundle of tensor, exterior and symmetric algebras of `F`. The Koszul
differential of a functional `ξ` on `F` lowers the exterior degree by one, so in the lowest
nonvanishing degree it is a morphism

`d_ξ : ⋀¹F ⟶ ⋀⁰F`,

and the defining equation of Stacks tag 062K prescribes its value on a degree-one local section:
the section `e` of `F` goes to the scalar `ξ(e)`, read in `⋀⁰F = O♯`. This file records that
equation for the transported differential of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionTransport`, in the two forms a
computation uses it: as the value of the differential itself, and -- specializing `ξ` to the
`j`-th coordinate functional of a finite free `F` -- as the identification

`δⱼ : ⋀¹((O♯)^ι) ⟶ ⋀⁰((O♯)^ι) = O♯`

with the `j`-th coordinate projection of the free sheaf of modules, read on the terms of a Koszul
chain complex.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.koszulD_sheafifiedExteriorGenerator`: on the
  realized exterior algebra `⋀(F)` the Koszul differential takes a degree-one local section `e`
  to `ξ(e)` times the algebra unit.
* `SheafOfModules.TensorExteriorSymmetricAlgebras`
  `.exteriorPieceZeroIsoUnit_koszulD_exteriorGenerator`: **the same equation on the exterior
  powers of a bundle of algebras**, read through the degree-zero identification `⋀⁰F ≅ O♯`.
* `Stacks.RegularSequence.KoszulChainData.chainXZeroIsoUnit_coordKoszulD_chainXOneIso_inv`:
  **the coordinate contraction `δⱼ` on the terms of a Koszul chain complex is the `j`-th
  coordinate of the free sheaf of modules**, through the identifications of the degree-one term
  with `(O♯)^ι` and of the degree-zero term with `O♯`.

## Implementation notes

**Why the value is obtained by transport and not from the construction.** The Koszul differential
on the exterior powers of a bundle of algebras is defined by conjugating the differential of the
realized exterior algebra with the canonical degreewise comparison, so its value on a generator
is the transported value. The three facts that carry it across are that the comparison matches
the two degree-one generators, that it intertwines the two differentials, and that it matches the
two units; the last is what turns `ξ(e)` times the realized unit into `ξ(e)` times the bundle's
unit, after which the degree-zero identification of the bundle reads off the scalar.

**Degree bookkeeping on the chain complex.** The terms of a Koszul chain complex are only *equal*
to the exterior powers, so the statement on the complex differs from the one on the exterior
powers by the two transports `chainXIso`; both are absorbed by the identifications
`Stacks.RegularSequence.KoszulChainData.chainXOneIso` and `chainXZeroIsoUnit`, which already
carry them, leaving an identity of composites with no `eqToHom`.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe v u w

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- **The Koszul differential of `⋀(F)` takes a degree-one local section to the scalar the
functional assigns to it, times the algebra unit.** This is the defining equation of Stacks tag
062K with the degree-zero identification `⋀⁰F ≅ O♯` moved to the other side: a degree-zero
section of the realized exterior algebra is determined by the scalar that identification assigns
to it. -/
theorem koszulD_sheafifiedExteriorGenerator
    (ξ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) (U : Cᵒᵖ) (e : F.val.obj U) :
    (SheafOfModules.koszulD J F ξ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
        ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e) =
      ξ.dual U e • (SheafOfModules.sheafifiedExteriorAlgebra J F).one.eval U :=
  (SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit
    (SheafOfModules.sheafifiedExteriorAlgebra J F)
    (SheafOfModules.sheafifiedExteriorPieceZeroIso J F)
    (SheafOfModules.sheafifiedExteriorPieceZeroIso_one J F) U _ _
    (SheafOfModules.koszulD_exteriorGenerator J F ξ U e)).symm

/-- **The Koszul differential of a functional on the exterior powers of a bundle of algebras
takes a degree-one local section to the scalar the functional assigns to it.** The scalar is read
off by the degree-zero identification `⋀⁰F ≅ O♯` of the bundle.

The comparison with the realized exterior algebra matches the two degree-one generators,
intertwines the two differentials and matches the two units, so the equation of
`koszulD_sheafifiedExteriorGenerator` transports verbatim. -/
theorem exteriorPieceZeroIsoUnit_koszulD_exteriorGenerator
    (ξ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) (U : Cᵒᵖ) (e : F.val.obj U) :
    A.exteriorPieceZeroIsoUnit.hom.val.app U
        ((A.koszulD ξ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          (A.exteriorGenerator.val.app U e)) = ξ.dual U e := by
  have hgen : (A.sheafifiedExteriorPieceIso 1).hom.val.app U
      ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e) =
        A.exteriorGenerator.val.app U e :=
    SheafOfModules.hom_congr_app_apply A.sheafifiedExteriorPieceIso_generator U e
  have hinter : (A.koszulD ξ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
      ((A.sheafifiedExteriorPieceIso 1).hom.val.app U
        ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e)) =
      (A.sheafifiedExteriorPieceIso 0).hom.val.app U
        ((SheafOfModules.koszulD J F ξ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e)) :=
    SheafOfModules.hom_congr_app_apply
      (A.exterior_isExteriorAlgebra.sheafifiedPieceIso_hom_comp_koszulD ξ
        (show (0 : ℤ) + 1 = 1 by norm_num)) U _
  rw [← hgen, hinter, koszulD_sheafifiedExteriorGenerator,
    map_smul (ConcreteCategory.hom ((A.sheafifiedExteriorPieceIso 0).hom.val.app U)),
    A.sheafifiedExteriorPieceIso_one U]
  exact Stacks.RegularSequence.exteriorPieceZeroIsoUnit_smul_one_apply A U _

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace Stacks.RegularSequence.KoszulChainData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J
    (SheafOfModules.free (R := toRingCat J Osharp) ι)}
  {g : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶
    SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A g)

/-- **The coordinate contraction from degree one to degree zero of a Koszul chain complex is the
coordinate contraction of the exterior powers**, the identifications of the two extreme terms
with `(O♯)^ι` and with `O♯` absorbing both transports. -/
theorem chainXOneIso_inv_comp_coordKoszulD_comp_chainXZeroIsoUnit (j : ι) :
    K.chainXOneIso.inv ≫ K.coordKoszulD j (show (0 : ℤ) + 1 = 1 by norm_num)
        ≫ K.chainXZeroIsoUnit.hom =
      A.exteriorGenerator ≫ A.coordKoszulD j (show (0 : ℤ) + 1 = 1 by norm_num)
        ≫ A.exteriorPieceZeroIsoUnit.hom := by
  simp [chainXOneIso, chainXZeroIsoUnit, coordKoszulD, chainXIso,
    SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorGeneratorIso_hom]

/-- **The coordinate contraction `δⱼ` of a Koszul chain complex is the `j`-th coordinate of the
free sheaf of modules**: reading a local section of `(O♯)^ι` as a section of the degree-one term
of the complex, contracting by the `j`-th coordinate functional and reading the result in `O♯`
returns the `j`-th coordinate of the section. -/
theorem chainXZeroIsoUnit_coordKoszulD_chainXOneIso_inv (j : ι) (U : Cᵒᵖ)
    (e : (SheafOfModules.free (R := toRingCat J Osharp) ι).val.obj U) :
    K.chainXZeroIsoUnit.hom.val.app U
        ((K.coordKoszulD j (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          (K.chainXOneIso.inv.val.app U e)) =
      (Stacks.SheafOfModules.coordExteriorFunctional j).dual U e := by
  rw [← SheafOfModules.comp_val_app_apply, ← SheafOfModules.comp_val_app_apply,
    SheafOfModules.hom_congr_app_apply
      (K.chainXOneIso_inv_comp_coordKoszulD_comp_chainXZeroIsoUnit j) U e,
    SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    SheafOfModules.TensorExteriorSymmetricAlgebras.coordKoszulD_eq_koszulD,
    A.exteriorPieceZeroIsoUnit_koszulD_exteriorGenerator]

end Stacks.RegularSequence.KoszulChainData

end
