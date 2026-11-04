module

public import Mathlib.Algebra.Homology.AlternatingConst
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
public import StacksFrontier.Cotangent.SurjectionSymmetricPowerVanishing

/-!
# The zeroth symmetric power column: `H_i(C, Sym⁰(F)) = B` for `i = 0` and `0` for `i > 0`

Let `C` be a small category with the chaotic topology, `B` a commutative ring, `F` a diagram of
`B`-modules on `Cᵒᵖ` — a `B̲`-module on `C` — and `U_•` a point resolution as in Tag 08Q9. The
zeroth sectionwise symmetric power `Sym^0_{B̲}(F)` is the constant diagram `B̲`, so

`H_0(C, Sym^0_{B̲}(F)) = B` and `H_i(C, Sym^0_{B̲}(F)) = 0` for `i > 0`.

The same statements are then specialised to the polynomial site `C_{B/A}` of a ring map
`A → B`.

## Main definitions

* `Stacks.ChaoticSite.mooreComplexConstIso`: the Moore complex of the evaluation of a constant
  diagram on `U_•` is the alternating constant complex `M ←0- M ←𝟙- M ←0- ⋯`.
* `Stacks.ChaoticSite.symmetricPowerDiagramZeroIso`: `Sym^0_{B̲}(F)` is the constant diagram on
  `B`.
* `Stacks.ChaoticSite.leftDerivedColimZeroSymmetricPowerDiagramZeroIso` and
  `CommAlgCat.leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso`: the degree-zero
  entry, over a general site and over `C_{B/A}`.

## Main results

* `Stacks.ChaoticSite.isZero_leftDerivedColimSucc_symmetricPowerDiagram_zero` and
  `CommAlgCat.isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero`: the
  vanishing in positive degrees, over a general site and over `C_{B/A}`.

## Implementation notes

`H_i(C, -)` is `L_i colim` over `Cᵒᵖ` at linear coefficients, the homology of a category of
Tag 08PF.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace Stacks.ChaoticSite

/-! ### The Moore complex of a constant diagram -/

section MooreConst

variable {C : Type u} [SmallCategory C]

/-- The evaluation of a constant diagram on a cosimplicial object is the constant simplicial
object: both send every simplex to `M` and every map to the identity. -/
def opCompConstIso {A : Type*} [Category* A] (U : CosimplicialObject C) (M : A) :
    U.op ⋙ (Functor.const Cᵒᵖ).obj M ≅ (Functor.const SimplexCategoryᵒᵖ).obj M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp)

/-- **The Moore complex of a constant diagram is the alternating constant complex.** The
evaluation of `π^{-1}M = M̲` on `U_•` is the constant simplicial object on `M`, whose alternating
face map complex is `M ←0- M ←𝟙- M ←0- ⋯`. -/
def mooreComplexConstIso {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    (U : CosimplicialObject C) (M : A) :
    (GeneralValued.cosimplicialMooreComplex A U).obj ((Functor.const Cᵒᵖ).obj M) ≅
      ChainComplex.alternatingConst.obj M :=
  (alternatingFaceMapComplex A).mapIso (opCompConstIso U M) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app M

end MooreConst

/-! ### The zeroth symmetric power of a diagram of modules -/

section SymmetricPowerZero

variable (C : Type u) [SmallCategory C] (B : Type u) [CommRing B]
  (F : Cᵒᵖ ⥤ ModuleCat.{u} B)

/-- **`Sym^0_{B̲}(F)` is the constant diagram `B̲`**, given in each degree by
`SymmetricAlgebra.symmetricPowerZeroEquiv`. -/
def symmetricPowerDiagramZeroIso :
    (Functor.const Cᵒᵖ).obj (ModuleCat.of B B) ≅ symmetricPowerDiagram C B F 0 :=
  NatIso.ofComponents
    (fun X => (SymmetricAlgebra.symmetricPowerZeroEquiv B (F.obj X)).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      apply Subtype.ext
      change (SymmetricAlgebra.symmetricPowerZeroEquiv B (F.obj Y) r :
          SymmetricAlgebra B (F.obj Y)) =
        SymPow.symAlgMap (F.map f).hom
          (SymmetricAlgebra.symmetricPowerZeroEquiv B (F.obj X) r : SymmetricAlgebra B (F.obj X))
      rw [SymmetricAlgebra.symmetricPowerZeroEquiv_apply,
        SymmetricAlgebra.symmetricPowerZeroEquiv_apply, AlgHom.commutes])

variable (U : CosimplicialObject C)

/-- **The degree-zero homology of `Sym^0_{B̲}(F)` is `B`.** For a point resolution `U_•` of a
small chaotic site `C`, `H_0(C, Sym^0_{B̲}(F)) = B`. -/
def leftDerivedColimZeroSymmetricPowerDiagramZeroIso (hU : IsPointResolution U) :
    ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj
        (symmetricPowerDiagram C B F 0) ≅ ModuleCat.of B B :=
  ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).mapIso
      (symmetricPowerDiagramZeroIso C B F).symm ≪≫
    (ModuleValued.moduleLeftDerivedColimitNatIso U hU 0).app
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) 0).mapIso
      (mooreComplexConstIso U (ModuleCat.of B B)) ≪≫
    ChainComplex.alternatingConstHomologyZero _

/-- **The positive-degree homology of `Sym^0_{B̲}(F)` vanishes.** For a point resolution `U_•` of
a small chaotic site `C` and every `i > 0`, `H_i(C, Sym^0_{B̲}(F)) = 0`. -/
theorem isZero_leftDerivedColimSucc_symmetricPowerDiagram_zero (hU : IsPointResolution U)
    (i : ℕ) :
    IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived (i + 1)).obj
      (symmetricPowerDiagram C B F 0)) := by
  refine IsZero.of_iso ?_
    (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived (i + 1)).mapIso
        (symmetricPowerDiagramZeroIso C B F).symm ≪≫
      (ModuleValued.moduleLeftDerivedColimitNatIso U hU (i + 1)).app
        ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B)) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ)
        (i + 1)).mapIso (mooreComplexConstIso U (ModuleCat.of B B)))
  exact (ChainComplex.alternatingConst_exactAt (ModuleCat.of B B) (i + 1)
    (Nat.succ_ne_zero i)).isZero_homology

end SymmetricPowerZero

end Stacks.ChaoticSite

/-! ### The `p = 0` column over the polynomial site of a surjection -/

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The degree-zero homology of `Sym^0_{B̲}(Ω)` on `C_{B/A}` is `B`**:
`H_0(C_{B/A}, Sym^0_{B̲}(Ω)) = B`, where `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` and `H_i(C_{B/A}, -) = L_i colim`
at linear coefficients. -/
def leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) 0) ≅
      ModuleCat.of (B : Type u) (B : Type u) :=
  Stacks.ChaoticSite.leftDerivedColimZeroSymmetricPowerDiagramZeroIso _ _ _ _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B)

/-- **The positive-degree homology of `Sym^0_{B̲}(Ω)` on `C_{B/A}` vanishes**:
`H_i(C_{B/A}, Sym^0_{B̲}(Ω)) = 0` for `i > 0`, where `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`. -/
theorem isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero (i : ℕ) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived (i + 1)).obj
      (Stacks.ChaoticSite.symmetricPowerDiagram
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) 0)) :=
  Stacks.ChaoticSite.isZero_leftDerivedColimSucc_symmetricPowerDiagram_zero _ _ _ _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) i

end CommAlgCat

end
