module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafCoproductInt

/-!
# From a graded module to a quasi-coherent module over the algebra sheaf

`Stacks.RelativeSpec.gradedAlgebraSheaf X A hc` reads a sheaf of graded `𝒪_X`-algebras with
commuting homogeneous multiplication as a sheaf of commutative `𝒪_X`-algebras, and
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` proves it quasi-coherent. This file does
the same on the module side: a graded module over `A` becomes a module over the algebra sheaf,
and it is quasi-coherent as soon as the coproduct of its homogeneous pieces is.

The equivalence `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence` and its existence
clause `exists_iso_relativeSpecQcohPushforward` take a quasi-coherent module over
`Stacks.RelativeSpec.AlgebraSheaf.ringSheaf` of a quasi-coherent algebra sheaf and return a
quasi-coherent module on the relative spectrum with that direct image; this is the step of the
proof of [Stacks, Tag 0897] stating that *since `ℱ` is a quasi-coherent `ℬ`-module there is a
unique quasi-coherent `𝒪_{X'}`-module `ℱ'` such that `π_*ℱ' = ℱ`*.

## Main definitions

* `Stacks.RelativeSpec.gradedModuleSheaf`: **a left graded module over a sheaf of graded algebras
  on a scheme, as a sheaf of modules over the algebra sheaf** `gradedAlgebraSheaf`.
* `Stacks.RelativeSpec.gradedModuleSheafOfRight`: the same for a *right* graded module, Tag
  0FQZ's `SheafOfModules.GradedModule`, under the commutativity hypothesis `hc` of
  `gradedAlgebraSheaf`.

## Main results

* `Stacks.RelativeSpec.structureMap_gradedAlgebraSheaf`: the structure morphism of
  `gradedAlgebraSheaf` is the structure map of the ungraded realization, so the `𝒪_X`-module
  underlying a module over the algebra sheaf is its restriction of scalars along
  `SheafOfModules.GradedAlgebra.ungradedStructureMap`.
* `Stacks.RelativeSpec.isQuasicoherent_gradedModuleSheaf` and
  `isQuasicoherent_gradedModuleSheafOfRight`: **a graded module concentrated in nonnegative
  degrees is quasi-coherent over the algebra sheaf as soon as the coproduct of its homogeneous
  pieces is quasi-coherent over `𝒪_X` and the algebra sheaf is quasi-coherent.**
* `Stacks.RelativeSpec.qcohGradedModuleSheafOfRight` and
  `exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight`: the resulting object of the
  quasi-coherent category, and the module on the relative spectrum whose direct image it is.
* `Stacks.RelativeSpec.isQuasicoherent_gradedModuleSheaf_of_piece`,
  `isQuasicoherent_gradedModuleSheafOfRight_of_piece`,
  `qcohGradedModuleSheafOfRightOfPiece` and
  `exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece`: **the same four
  statements for a grading indexed by all of `ℤ`**, with `hzero` and the `ℕ`-indexed coproduct
  hypothesis replaced by quasi-coherence of every homogeneous piece.
* `Stacks.RelativeSpec.ι_comp_intCoprodIsoUnderlyingModule_gradedModuleSheaf_hom` and
  `Stacks.RelativeSpec.ι_comp_gradedIntCoprodIsoUnderlyingModule_hom`: **the value of the
  module-side and algebra-side `ℤ`-indexed identifications on one homogeneous degree.**

## Implementation notes

[Stacks, Tag 0FQZ], Definition 24.4.1, grades a sheaf of modules over a graded algebra by
`n ∈ ℤ`, and `SheafOfModules.GradedModule` follows it. So the `ℱ` of [Stacks, Tag 0897] carries
no vanishing in negative degrees, and the hypothesis `hzero` of
`isQuasicoherent_gradedModuleSheafOfRight` is not available there. The `_of_piece` forms assume
instead quasi-coherence of each `ℱ_n`, and go through
`SheafOfModules.LeftGradedModule.intCoprodIsoUnderlyingModule`, the `ℤ`-indexed form of
`coprodIsoUnderlyingModule`.

The passage from quasi-coherence over `𝒪_X` to quasi-coherence over the algebra sheaf is
[Stacks, Tag 0H88],
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars`:
`SheafOfModules.IsQuasicoherent` over the ungraded realization asks for a local presentation by
free modules over *that* sheaf of rings, not over `𝒪_X`. The hypothesis of 0H88, that the sheaf
of rings is quasi-coherent as an `𝒪_X`-module, is definitionally
`Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent`, which `isQuasicoherent_gradedAlgebraSheaf`
provides.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- The structure morphism of `Stacks.RelativeSpec.gradedAlgebraSheaf`, read as a morphism of
sheaves of rings, is the structure map of the ungraded realization itself. -/
theorem structureMap_gradedAlgebraSheaf :
    AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc) = A.ungradedStructureMap := rfl

/-- **The value of `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule` on the degree-`n`
summand**: the sheafification of the degree-`n` inclusion into the objectwise direct sum,
corrected by the sheafification counit at `𝒜ₙ`, and then `gradedDirectSumIsoUnderlyingModule`. -/
theorem ι_comp_gradedIntCoprodIsoUnderlyingModule_hom (n : ℤ) :
    Limits.Sigma.ι (fun k : ℤ => A.piece k) n ≫
        (Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule X A hc).hom =
      (Stacks.sheafificationDirectSumComponentIso (fun k : ℤ => A.piece k)).inv.app ⟨n⟩ ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (Stacks.inclHom (fun k : ℤ => (A.piece k).val) n) ≫
          (gradedDirectSumIsoUnderlyingModule X A hc).hom :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun z => z ≫ (gradedDirectSumIsoUnderlyingModule X A hc).hom)
        (Stacks.ι_comp_sheafifyDirectSumIso_inv (fun k : ℤ => A.piece k) n))
      (Category.assoc _ _ _))

variable (M : SheafOfModules.LeftGradedModule.{u, u, u} A)

/-- **A left graded module over a sheaf of graded algebras on a scheme, as a sheaf of modules
over the sheaf of commutative algebras the graded algebra presents.** Its underlying
`𝒪_X`-module is the sheafification of the direct sum of the homogeneous components, exactly as on
the algebra side. -/
noncomputable def gradedModuleSheaf :
    SheafOfModules.{u} (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc)) :=
  M.ungradedSheafModule

/-- **The `𝒪_X`-module underlying `Stacks.RelativeSpec.gradedModuleSheaf` of a graded module
concentrated in nonnegative degrees is the coproduct of its homogeneous pieces.** -/
noncomputable def coprodIsoUnderlyingModule_gradedModuleSheaf
    (hzero : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
      (SheafOfModules.restrictScalars.{u}
        (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).obj
          (gradedModuleSheaf X A hc M) :=
  M.coprodIsoUnderlyingModule hzero

/-- Quasi-coherence over `𝒪_X` of a module isomorphic to the underlying `𝒪_X`-module of
`Stacks.RelativeSpec.gradedModuleSheaf` gives quasi-coherence over the algebra sheaf. -/
private theorem isQuasicoherent_gradedModuleSheaf_of_iso
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    {G : SheafOfModules.{u} X.ringCatSheaf}
    (e : G ≅ (SheafOfModules.restrictScalars.{u}
      (AlgebraSheaf.structureMap _)).obj (gradedModuleSheaf X A hc M))
    (hG : G.IsQuasicoherent) : (gradedModuleSheaf X A hc M).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    (AlgebraSheaf.structureMap _) hA _ <|
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hG

/-- **`Stacks.RelativeSpec.gradedModuleSheaf` of a graded module concentrated in nonnegative
degrees is quasi-coherent as soon as the coproduct of its homogeneous pieces is and the algebra
sheaf is.** -/
theorem isQuasicoherent_gradedModuleSheaf
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hzero : ∀ n : ℤ, n < 0 → IsZero (M.piece n))
    (hqc : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent) :
    (gradedModuleSheaf X A hc M).IsQuasicoherent :=
  isQuasicoherent_gradedModuleSheaf_of_iso X A hc M hA
    (coprodIsoUnderlyingModule_gradedModuleSheaf X A hc M hzero) hqc

/-- **The `𝒪_X`-module underlying `Stacks.RelativeSpec.gradedModuleSheaf` is the coproduct of its
homogeneous pieces over all of `ℤ`.** -/
noncomputable def intCoprodIsoUnderlyingModule_gradedModuleSheaf :
    (∐ fun n : ℤ => M.piece n) ≅
      (SheafOfModules.restrictScalars.{u}
        (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).obj
          (gradedModuleSheaf X A hc M) :=
  M.intCoprodIsoUnderlyingModule

/-- **The value of `intCoprodIsoUnderlyingModule_gradedModuleSheaf` on the degree-`n` summand**:
the sheafification of the degree-`n` inclusion into the objectwise direct sum, corrected by the
sheafification counit at `ℱₙ`. -/
theorem ι_comp_intCoprodIsoUnderlyingModule_gradedModuleSheaf_hom (n : ℤ) :
    Limits.Sigma.ι (fun k : ℤ => M.piece k) n ≫
        (intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc M).hom =
      (Stacks.sheafificationDirectSumComponentIso (fun k : ℤ => M.piece k)).inv.app ⟨n⟩ ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (Stacks.inclHom (fun k : ℤ => (M.piece k).val) n) ≫
          Stacks.sheafifyHomOfPresheafHom M.ungradedDirectSumHom :=
  M.ι_comp_intCoprodIsoUnderlyingModule_hom n

/-- **`Stacks.RelativeSpec.gradedModuleSheaf` is quasi-coherent as soon as every homogeneous
piece is and the algebra sheaf is.** -/
theorem isQuasicoherent_gradedModuleSheaf_of_piece
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hM : ∀ n : ℤ, (M.piece n).IsQuasicoherent) :
    (gradedModuleSheaf X A hc M).IsQuasicoherent :=
  isQuasicoherent_gradedModuleSheaf_of_iso X A hc M hA
    (intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc M)
    (isQuasicoherent_intCoprod X (fun n => M.piece n) hM)

/-! ### The right-handed form -/

variable (F : SheafOfModules.GradedModule.{u, u, u} A)

/-- **A right graded module over a sheaf of graded algebras with commutative homogeneous
multiplication, as a sheaf of modules over the sheaf of commutative algebras the graded algebra
presents.** -/
noncomputable def gradedModuleSheafOfRight :
    SheafOfModules.{u} (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc)) :=
  gradedModuleSheaf X A hc (F.toLeftGradedModuleOfComm hc)

/-- **`Stacks.RelativeSpec.gradedModuleSheafOfRight` is quasi-coherent as soon as the coproduct
of the homogeneous pieces is and the algebra sheaf is.** -/
theorem isQuasicoherent_gradedModuleSheafOfRight
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hzero : ∀ n : ℤ, n < 0 → IsZero (F.piece n))
    (hqc : (∐ fun n : ℕ => F.piece (n : ℤ)).IsQuasicoherent) :
    (gradedModuleSheafOfRight X A hc F).IsQuasicoherent :=
  isQuasicoherent_gradedModuleSheaf X A hc (F.toLeftGradedModuleOfComm hc) hA hzero hqc

/-- **`Stacks.RelativeSpec.gradedModuleSheafOfRight`, as an object of the category of
quasi-coherent modules over the algebra sheaf.** -/
noncomputable def qcohGradedModuleSheafOfRight
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hzero : ∀ n : ℤ, n < 0 → IsZero (F.piece n))
    (hqc : (∐ fun n : ℕ => F.piece (n : ℤ)).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent
      (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc))).FullSubcategory :=
  ⟨gradedModuleSheafOfRight X A hc F,
    isQuasicoherent_gradedModuleSheafOfRight X A hc F hA hzero hqc⟩

/-- **The module `ℱ'` of the proof of [Stacks, Tag 0897], for a graded module: there is a
quasi-coherent module on the relative spectrum of `gradedAlgebraSheaf` whose direct image is
`gradedModuleSheafOfRight`.** -/
theorem exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hzero : ∀ n : ℤ, n < 0 → IsZero (F.piece n))
    (hqc : (∐ fun n : ℕ => F.piece (n : ℤ)).IsQuasicoherent) :
    ∃ F' : (SheafOfModules.isQuasicoherent
        (Stacks.AffineAlgebraEquivalence.relativeSpec
          (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory,
      Nonempty ((Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence
        (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
          qcohGradedModuleSheafOfRight X A hc F hA hzero hqc) :=
  have := hA
  Stacks.AffineAlgebraEquivalence.exists_iso_relativeSpecQcohPushforward
    (gradedAlgebraSheaf X A hc) _

/-! ### The same, for a grading indexed by all of `ℤ` -/

/-- **`Stacks.RelativeSpec.gradedModuleSheafOfRight` is quasi-coherent as soon as every
homogeneous piece is and the algebra sheaf is.** -/
theorem isQuasicoherent_gradedModuleSheafOfRight_of_piece
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    (gradedModuleSheafOfRight X A hc F).IsQuasicoherent :=
  isQuasicoherent_gradedModuleSheaf_of_piece X A hc (F.toLeftGradedModuleOfComm hc) hA hF

/-- `Stacks.RelativeSpec.qcohGradedModuleSheafOfRight` with `hzero` and the `ℕ`-indexed
coproduct hypothesis replaced by quasi-coherence of every homogeneous piece. -/
noncomputable def qcohGradedModuleSheafOfRightOfPiece
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent
      (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc))).FullSubcategory :=
  ⟨gradedModuleSheafOfRight X A hc F,
    isQuasicoherent_gradedModuleSheafOfRight_of_piece X A hc F hA hF⟩

/-- **The module `ℱ'` of the proof of [Stacks, Tag 0897] for a `ℤ`-graded module**: there is a
quasi-coherent module on the relative spectrum of `gradedAlgebraSheaf` whose direct image is
`gradedModuleSheafOfRight`.

Unlike `exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight`, this assumes no
vanishing in negative degrees: [Stacks, Tag 0FQZ], Definition 24.4.1, grades a module by `n ∈ ℤ`,
and the `ℱ` of Tag 0897 is such a module. -/
theorem exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    ∃ F' : (SheafOfModules.isQuasicoherent
        (Stacks.AffineAlgebraEquivalence.relativeSpec
          (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory,
      Nonempty ((Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence
        (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
          qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF) :=
  have := hA
  Stacks.AffineAlgebraEquivalence.exists_iso_relativeSpecQcohPushforward
    (gradedAlgebraSheaf X A hc) _

end Stacks.RelativeSpec

end
