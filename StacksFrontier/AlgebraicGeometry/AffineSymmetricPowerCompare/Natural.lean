module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricPowerCompare.Basic
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricPowerCompare.Functoriality

/-!
# Naturality of the affine symmetric-power comparison

**This file proves that `Stacks.SymGraded.tildeSymmetricPowerIso` is natural in the module**: it
commutes with the associated sheaf of `Sym^n(f)` on one side and with any unital homomorphism of
the symmetric algebra sheaves extending `f` on the degree-one generators on the other.

## Main results

* `Stacks.SymGraded.tildeSymmetricPowerIso_natural`: the naturality square.

## Implementation notes

Only the universal property is used. Both composites in the square are the degree-`n` component
of a unital homomorphism `symAlgebra M ⟶ B.symmetric`, and each carries the degree-one generator
`symGen M` to `tilde.map f ≫ B.symmetricGenerator`; the universal property of
`Stacks.SymGraded.symAlgebra` makes that homomorphism unique, hence the two agree in every
degree. The left composite is a homomorphism because of
`Stacks.SymGraded.symFunctorHom_app_natCast`, which identifies the degree-`n` component of
`Stacks.SymGraded.symFunctorHom` with `tilde.map (Sym^n f)`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N)

/-- The degree-one generator of a symmetric algebra of `Ñ`, pulled back along `tilde.map f`,
still has pairwise commuting image. -/
theorem pairwiseCommutes_map_comp_symmetricGenerator
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes
      (tilde.map f ≫ B.symmetricGenerator :
        (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ B.symmetric.piece 1) :=
  fun U _ _ => B.pairwiseCommutes_symmetricGenerator U _ _

/-- **The affine symmetric-power comparison is natural.** It respects every unital homomorphism
of symmetric algebra sheaves extending the map of generating module sheaves; the universal
property of the symmetric algebra makes such a homomorphism unique. -/
@[stacks 01I8 "symmetric_power"]
theorem tildeSymmetricPowerIso_natural (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N))
    (g : SheafOfModules.GradedAlgebra.UnitalHom A.symmetric B.symmetric)
    (hg : A.symmetricGenerator ≫ g.app 1 = tilde.map f ≫ B.symmetricGenerator) :
    tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of R (SymPow.symmetricPower n R M))
          (Y := ModuleCat.of R (SymPow.symmetricPower n R N)) (SymPow.symMap n f.hom)) ≫
        (tildeSymmetricPowerIso N B n).hom =
      (tildeSymmetricPowerIso M A n).hom ≫ g.app (n : ℤ) := by
  have hκ := pairwiseCommutes_map_comp_symmetricGenerator f B
  have hdescN := SheafOfModules.GradedAlgebra.IsUniversal.desc_extends
    (isSymmetricAlgebra N) B.symmetric B.symmetricGenerator B.symmetric_isSymmetricAlgebra.1
  have hdescM := SheafOfModules.GradedAlgebra.IsUniversal.desc_extends
    (isSymmetricAlgebra M) A.symmetric A.symmetricGenerator A.symmetric_isSymmetricAlgebra.1
  have h1 : ((symFunctorHom f).comp
        ((isSymmetricAlgebra N).desc B.symmetric B.symmetricGenerator
          B.symmetric_isSymmetricAlgebra.1)) =
      (isSymmetricAlgebra M).desc B.symmetric
        (tilde.map f ≫ B.symmetricGenerator) hκ :=
    SheafOfModules.GradedAlgebra.IsUniversal.desc_unique (isSymmetricAlgebra M)
      B.symmetric _ hκ (by
        change symGen M ≫ _ ≫ _ = _
        erw [← Category.assoc, symGen_symFunctorHom, Category.assoc, hdescN])
  have h2 : (((isSymmetricAlgebra M).desc A.symmetric A.symmetricGenerator
        A.symmetric_isSymmetricAlgebra.1).comp g) =
      (isSymmetricAlgebra M).desc B.symmetric
        (tilde.map f ≫ B.symmetricGenerator) hκ :=
    SheafOfModules.GradedAlgebra.IsUniversal.desc_unique (isSymmetricAlgebra M)
      B.symmetric _ hκ (by
        change symGen M ≫ _ ≫ _ = _
        erw [← Category.assoc, hdescM, hg])
  erw [← symFunctorHom_app_natCast f n]
  exact congrArg (fun h : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B.symmetric =>
    h.app (n : ℤ)) (h1.trans h2.symm)

/-- The canonical unital homomorphism of symmetric algebra sheaves induced by `f`: the one the
universal property of `A.symmetric` produces from `tilde.map f`, whose composite with the
degree-one generator of `B` commutes pairwise by
`pairwiseCommutes_map_comp_symmetricGenerator`. -/
noncomputable def symmetricAlgebraHom
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    SheafOfModules.GradedAlgebra.UnitalHom A.symmetric B.symmetric :=
  A.symmetric_isSymmetricAlgebra.isUniversal.desc B.symmetric
    (tilde.map f ≫ B.symmetricGenerator)
    (pairwiseCommutes_map_comp_symmetricGenerator f B)

/-- The canonical symmetric-algebra map extends `tilde.map f` on the degree-one generators, which
is the hypothesis `tildeSymmetricPowerIso_natural` quantifies over. -/
theorem symmetricAlgebraHom_app_one
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    A.symmetricGenerator ≫ (symmetricAlgebraHom f A B).app 1 =
      tilde.map f ≫ B.symmetricGenerator :=
  A.symmetric_isSymmetricAlgebra.isUniversal.desc_extends B.symmetric
    (tilde.map f ≫ B.symmetricGenerator)
    (pairwiseCommutes_map_comp_symmetricGenerator f B)

/-- **The affine symmetric-power comparison is natural, for the canonical induced map.** This is
`Stacks.SymGraded.tildeSymmetricPowerIso_natural` instantiated at `symmetricAlgebraHom`, the
unital homomorphism the universal property of the symmetric algebra provides, so that the square
is stated against a canonical map rather than a hypothesised one. The left-hand map is the
associated sheaf of `SymPow.symMap`, the `n`-th symmetric power of `f`. -/
@[stacks 01I8 "symmetric_power"]
theorem tildeSymmetricPowerIso_natural_symMap (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of R (SymPow.symmetricPower n R M))
          (Y := ModuleCat.of R (SymPow.symmetricPower n R N)) (SymPow.symMap n f.hom)) ≫
        (tildeSymmetricPowerIso N B n).hom =
      (tildeSymmetricPowerIso M A n).hom ≫ (symmetricAlgebraHom f A B).app (n : ℤ) :=
  tildeSymmetricPowerIso_natural f n A B (symmetricAlgebraHom f A B)
    (symmetricAlgebraHom_app_one f A B)

end Stacks.SymGraded
