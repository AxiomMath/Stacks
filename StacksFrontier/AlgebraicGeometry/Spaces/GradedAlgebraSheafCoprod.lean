module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian

/-!
# The algebra sheaf of a graded algebra on an algebraic space: its module and its sections

Let `W` be an algebraic space over a scheme `S` and let `A` be a sheaf of graded `𝒪_W`-algebras
on the small étale site of `W` whose homogeneous multiplication commutes in every pair of
degrees.  `AlgebraicGeometry.Space.gradedAlgebraSheaf` reads `A` as a sheaf of commutative
`𝒪_W`-algebras, through its ungraded realization; this is the algebra whose relative spectrum
Stacks 09RU takes, for the conormal algebra and for the symmetric algebra of the conormal sheaf.
This file identifies its underlying `𝒪_W`-module with the coproduct of the homogeneous pieces
when those vanish in negative degrees, and draws the two consequences the relative spectrum
needs:

* it is quasi-coherent as soon as every homogeneous piece is (Stacks 03M1 for the coproduct);
* over an affine étale chart its sections are the direct sum of the sections of the pieces
  (Stacks 0935, an affine chart being a quasi-compact object of the site), so they are bounded
  by the `ℵ₀`-th power of any cardinal bounding the pieces there.

## Main definitions

* `AlgebraicGeometry.Space.gradedDirectSumHomOfTotalSheaf`: the comparison from the objectwise
  direct sum of the homogeneous pieces to the module underlying `gradedAlgebraSheaf`.
* `AlgebraicGeometry.Space.gradedCoprodIsoUnderlyingModule`: **for pieces concentrated in
  nonnegative degrees, the module underlying `gradedAlgebraSheaf` is the coproduct of the
  pieces.**

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_gradedAlgebraSheaf`: `gradedAlgebraSheaf` is a
  quasi-coherent algebra sheaf as soon as every homogeneous piece is quasi-coherent.
* `AlgebraicGeometry.Space.mk_gradedAlgebraSheaf_sections_le`: over an affine étale chart, a
  cardinal bounding every homogeneous piece bounds the sections of `gradedAlgebraSheaf` by its
  `ℵ₀`-th power.

## Implementation notes

The two isomorphisms are the scheme-level ones of
`StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent`, instantiated at
the small étale site: the generic comparison `Stacks.GradedAlgebra.directSumIsoUnderlyingModule`
applies because the module underlying an algebra sheaf on an algebraic space *is* the restriction
of scalars of the free module of rank one along its structure morphism
(`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars`), and the structure
morphism of `gradedAlgebraSheaf` is the structure map of the ungraded realization by definition.
Local injectivity and surjectivity of the sheafification unit are read off `toSheafify` directly.

## References

* [Stacks Project, Tag 09RU](https://stacks.math.columbia.edu/tag/09RU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W))
    (hc : ∀ (i j : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : (A.piece i).val.obj V)
      (b : (A.piece j).val.obj V), HEq ((A.mul i j).app V a b) ((A.mul j i).app V b a))

/-- The sheafification unit of the ungraded realization is compatible with the structure map of
the graded algebra and the structure morphism of `AlgebraicGeometry.Space.gradedAlgebraSheaf`. -/
theorem structureHom_comp_toTotalSheaf_gradedAlgebraSheaf :
    A.toPresheafGradedAlgebra.structureHom ≫
        A.toPresheafGradedAlgebra.toTotalSheaf (SmallEtale.topology B S hS W.1) =
      (AlgebraSheaf.structureMapOfSite (gradedAlgebraSheaf B S hS W A hc)).hom :=
  rfl

/-- **The comparison from the objectwise direct sum of the pieces to the module of the graded
algebra sheaf**, built from the graded-algebra direct-sum map of the underlying presheaf of graded
algebras and the map to the total sheaf. -/
def gradedDirectSumHomOfTotalSheaf :
    Stacks.directSum (fun n : ℤ => (A.piece n).val) ⟶
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val :=
  Stacks.GradedAlgebra.directSumHom A.toPresheafGradedAlgebra
    (AlgebraSheaf.structureMapOfSite (gradedAlgebraSheaf B S hS W A hc))
    (A.toPresheafGradedAlgebra.toTotalSheaf _)
    (structureHom_comp_toTotalSheaf_gradedAlgebraSheaf B S hS W A hc)

/-- `AlgebraicGeometry.Space.gradedDirectSumHomOfTotalSheaf`, restricted to the nonnegative
degrees. -/
def gradedCoprodDirectSumHom :
    Stacks.directSum (fun n : ℕ => (A.piece (n : ℤ)).val) ⟶
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (A.piece n).val) ≫
    gradedDirectSumHomOfTotalSheaf B S hS W A hc

/-- **The module underlying `AlgebraicGeometry.Space.gradedAlgebraSheaf` of a graded algebra
concentrated in nonnegative degrees is the coproduct of its homogeneous pieces.** -/
def gradedCoprodIsoUnderlyingModule (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (∐ fun n : ℕ => A.piece (n : ℤ)) ≅
      AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc) :=
  (Stacks.sheafifyDirectSumIso (fun n : ℕ => A.piece (n : ℤ))).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective (gradedCoprodDirectSumHom B S hS W A hc)
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
          ((SmallEtale.topology B S hS W.1).W_toSheafify
            A.toPresheafGradedAlgebra.totalPresheaf).isLocallyInjective))
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
          ((SmallEtale.topology B S hS W.1).W_toSheafify
            A.toPresheafGradedAlgebra.totalPresheaf).isLocallySurjective))

/-- **`AlgebraicGeometry.Space.gradedAlgebraSheaf` of a graded algebra concentrated in
nonnegative degrees is quasi-coherent as soon as its homogeneous pieces are.**  Its module is the
coproduct of the pieces, and a coproduct of quasi-coherent modules on the small étale site of an
algebraic space is quasi-coherent (Stacks 03M1, with Stacks 03DX(2) supplied
unconditionally). -/
theorem isQuasicoherent_gradedAlgebraSheaf (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
    (hqc : ∀ n : ℕ, (A.piece (n : ℤ)).IsQuasicoherentOnSite) :
    (gradedAlgebraSheaf B S hS W A hc).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (gradedCoprodIsoUnderlyingModule B S hS W A hc hzero)
    (isQuasicoherentOnSite_coproduct_of_h03DX B S hS W.1 W.2
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS W.1 W.2) _
      (coproductIsCoproduct fun n : ℕ => A.piece (n : ℤ)) hqc)

/-- **Over an affine étale chart, the sections of `AlgebraicGeometry.Space.gradedAlgebraSheaf`
are bounded by the `ℵ₀`-th power of any cardinal bounding the homogeneous pieces there.**  The
module of `gradedAlgebraSheaf` is the coproduct of the pieces of nonnegative degree, an affine
chart is a quasi-compact object of the small étale site, so the sections over it are the direct
sum of the sections of the pieces (Stacks 0935), which embeds in their product over `ℕ`. -/
theorem mk_gradedAlgebraSheaf_sections_le (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
    (V : SmallEtale B S hS W.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    {c : Cardinal.{u}} (hcV : ∀ n : ℕ, #((A.piece (n : ℤ)).val.obj (op V)) ≤ c) :
    #((gradedAlgebraSheaf B S hS W A hc).right.obj.obj (op V)) ≤ c ^ ℵ₀ := by
  classical
  let e := gradedCoprodIsoUnderlyingModule B S hS W A hc hzero
  have h1 : #((gradedAlgebraSheaf B S hS W A hc).right.obj.obj (op V)) =
      #((∐ fun n : ℕ => A.piece (n : ℤ)).val.obj (op V)) :=
    (Cardinal.mk_congr ((SheafOfModules.evaluation _ (op V) ⋙
      forget₂ _ AddCommGrpCat).mapIso e).addCommGroupIsoToAddEquiv.toEquiv).symm
  have hbij := Stacks.Sites.bijective_coproductSectionsMap
    (Cofan.mk _ (Sigma.ι fun n : ℕ => A.piece (n : ℤ)))
    (coproductIsCoproduct fun n : ℕ => A.piece (n : ℤ)) V
    (isQuasiCompactObject_of_isAffine B S hS W.1 V hV)
  rw [h1]
  refine (Cardinal.mk_congr (Equiv.ofBijective _ hbij)).symm.trans_le ?_
  calc #(DirectSum ℕ fun n : ℕ => ((A.piece (n : ℤ)).val.obj (op V) : Type u))
      ≤ #(∀ n : ℕ, ((A.piece (n : ℤ)).val.obj (op V) : Type u)) :=
        Cardinal.mk_le_of_injective DFunLike.coe_injective
    _ = Cardinal.prod fun n : ℕ => #((A.piece (n : ℤ)).val.obj (op V)) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : ℕ => c := Cardinal.prod_le_prod _ _ hcV
    _ = c ^ ℵ₀ := by rw [Cardinal.prod_const, Cardinal.lift_uzero, Cardinal.mk_nat,
        Cardinal.lift_aleph0]

end AlgebraicGeometry.Space

end
