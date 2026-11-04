module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraEpiDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.SymmetricToLaurentIso

/-!
# The symmetric algebra of a line bundle is its Laurent algebra in nonnegative degrees

Let `L` be an invertible sheaf of modules on a scheme `X`. The comparison
`Stacks.LineBundle.Situation.symmetricToLaurent` of the symmetric algebra `Sym(L)` with the
Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` is already known to vanish in negative degrees and to be an
isomorphism in degree one. This file settles it in **every nonnegative degree**: the Laurent
algebra is the symmetric algebra with the degree-one generator inverted, and inverting a
generator changes nothing in the degrees where the generator is already invertible.

The proof is an induction on the degree with two inputs. In degree zero both algebras are the
structure sheaf and the comparison preserves the unit, so it is the identity: a degree-zero local
section of `Sym(L)` is a function on the base times the algebra unit, and the comparison carries
that function times the unit to the same function times the unit. In degree `n + 1` the
multiplication of the Laurent algebra in the degrees `(n, 1)` is the coherent multiplication
isomorphism `L^{⊗ n} ⊗ L^{⊗ 1} ≅ L^{⊗ (n + 1)}` of Tag 01CU read through the sheafification unit,
hence locally surjective, so `Stacks.SheafOfModules.epi_unitalHom_app_add` turns the inductive
hypothesis in degree `n` together with the known degree-one case into epimorphy in degree
`n + 1`; both sides being invertible modules, that epimorphism is an isomorphism.

## Main definitions

* `Stacks.LineBundle.Situation.laurentMulPresheaf`: the multiplication of the Laurent algebra of
  the line bundle in a pair of degrees, as a morphism out of the objectwise tensor product of
  presheaves of modules.
* `Stacks.LineBundle.Situation.symmetricPieceZeroIso`: degree zero of `Sym(L)` is the structure
  sheaf of the scheme on which `L` lives.

## Main results

* `Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_natCast`: **the comparison of the
  symmetric algebra of the line bundle with its Laurent algebra is an isomorphism in every
  nonnegative degree**, and `isIso_symmetricToLaurent_app_of_nonneg` is the same statement for an
  integer degree that is nonnegative.
* `Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_zero` and
  `symmetricToLaurent_app_zero`: in degree zero the comparison is the identification of both
  algebras with the structure sheaf.
* `Stacks.LineBundle.Situation.epi_symmetricToLaurent_app_add`: the comparison is an epimorphism
  in a sum of two degrees in which it is an isomorphism.
* `Stacks.LineBundle.Situation.isLocallySurjective_laurentMulPresheaf`: **multiplication in the
  Laurent algebra of the line bundle is locally surjective in every pair of degrees**, being the
  sheafification unit followed by an isomorphism.
* `Stacks.LineBundle.Situation.laurentMulPresheaf_tmul`: that morphism carries a pure tensor of
  homogeneous local sections to their product.

## Implementation notes

Two tensor-power constructions live in this repository and are not identified: the `ℕ`-indexed
`SheafOfModules.tensorPower`, built by recursion on the exponent, and the `ℤ`-indexed
`Stacks.SheafOfModules.TensorPower.tensorPower`, built from the tensoring autoequivalence. The
route taken here needs neither of them: the source of the comparison is the symmetric algebra,
whose multiplication is used only through the universal property packaged in
`SheafOfModules.GradedAlgebra.UnitalHom`, and its target is the `ℤ`-indexed family throughout.
The `ℕ`-indexed powers enter only inside the already available
`Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_of_epi`, where they serve to make a
nonnegative symmetric power an invertible module. So no compatibility of the two constructions
with the graded multiplications has to be established.

The multiplication of the Laurent algebra is defined as a bilinear map on local sections, read
off the coherent multiplication isomorphism by `PresheafOfModules.toBilinear`; the morphism out
of the objectwise tensor product recorded here is the composite that bilinear map was read from,
which is why `Stacks.LineBundle.Situation.laurentMulPresheaf_tmul` holds by definitional
unfolding.

Degree zero of `Sym(L)` is identified with the structure sheaf at the level of a site, and the
compatibility of that identification with the units is not restated for a scheme, so
`Stacks.LineBundle.Situation.symmetricPieceZeroIso_hom_one` applies the site-level statement with
its four instance arguments named. This is the device recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme`: supplying the
sheaf of commutative rings would ask the elaborator to invert a projection.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 50.10](https://stacks.math.columbia.edu/tag/0FUH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

open scoped TensorProduct

universe u

namespace Stacks.LineBundle

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorPower

variable (D : Situation.{u})

/-! ### Multiplication of the Laurent algebra as a morphism out of a tensor product -/

/-- **Multiplication of the Laurent algebra of the line bundle in the degrees `i` and `j`**, as a
morphism of presheaves of modules out of the objectwise tensor product: the unit of the
sheafification defining the tensor product sheaf, followed by the coherent multiplication
isomorphism `L^{⊗ i} ⊗ L^{⊗ j} ≅ L^{⊗ (i + j)}` of Tag 01CU. -/
noncomputable def Situation.laurentMulPresheaf (i j : ℤ) :
    PresheafOfModules.tensorObj (D.laurentAlgebra.piece i).val
        (D.laurentAlgebra.piece j).val ⟶ (D.laurentAlgebra.piece (i + j)).val :=
  TensorSheafification.toSheafify D.X.sheaf.obj D.X.ringCatSheaf.property _ ≫
    (coherentMulIso D.X.sheaf.obj D.X.ringCatSheaf.property D.L i j).hom.val

/-- The multiplication of the Laurent algebra of the line bundle carries the pure tensor of two
homogeneous local sections to their graded product. -/
theorem Situation.laurentMulPresheaf_tmul (i j : ℤ) (U : (Opens ↥D.X)ᵒᵖ)
    (x : (D.laurentAlgebra.piece i).val.obj U) (y : (D.laurentAlgebra.piece j).val.obj U) :
    PresheafOfModules.Hom.app (D.laurentMulPresheaf i j) U
        (x ⊗ₜ[D.X.sheaf.obj.obj U] y) =
      (D.laurentAlgebra.mul i j).app U x y :=
  rfl

/-- **Multiplication of the Laurent algebra of the line bundle is locally surjective in every
pair of degrees**: a local section of `L^{⊗ (i + j)}` is locally a sum of products of homogeneous
sections of degrees `i` and `j`. The coherent multiplication of Tag 01CU is an isomorphism, so
the only local statement needed is the local surjectivity of the sheafification unit. -/
theorem Situation.isLocallySurjective_laurentMulPresheaf (i j : ℤ) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥D.X)
      (D.laurentMulPresheaf i j) := by
  have hiso : IsIso (coherentMulIso D.X.sheaf.obj D.X.ringCatSheaf.property D.L i j).hom.val :=
    ((SheafOfModules.forget
      (TensorSheafification.structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property)).mapIso
        (coherentMulIso D.X.sheaf.obj D.X.ringCatSheaf.property D.L i j)).isIso_hom
  exact Stacks.SheafOfModules.isLocallySurjective_comp
    (Stacks.SheafOfModules.isLocallySurjective_toSheafify D.X.ringCatSheaf.property _)
    (Stacks.SheafOfModules.isLocallySurjective_of_isIso _ hiso)

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra is an
epimorphism in a sum of two degrees in which it is an isomorphism**, multiplication of the
Laurent algebra being locally surjective there. -/
theorem Situation.epi_symmetricToLaurent_app_add (i j : ℤ)
    (hi : IsIso (D.symmetricToLaurent.app i)) (hj : IsIso (D.symmetricToLaurent.app j)) :
    Epi (D.symmetricToLaurent.app (i + j)) :=
  Stacks.SheafOfModules.epi_unitalHom_app_add (O := D.X.sheaf.obj)
    (hO := D.X.ringCatSheaf.property) D.symmetricToLaurent i j hi hj
    (D.laurentMulPresheaf i j) (D.laurentMulPresheaf_tmul i j)
    (D.isLocallySurjective_laurentMulPresheaf i j)

/-! ### Degree zero -/

/-- **Degree zero of the symmetric algebra of the line bundle is the structure sheaf of the
scheme on which `L` lives**: the zeroth symmetric power of a module is free of rank one on the
algebra unit. -/
noncomputable def Situation.symmetricPieceZeroIso :
    D.symmetricAlgebra.piece 0 ≅ SheafOfModules.unit D.X.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso D.X D.L

/-- The degree-zero identification of the symmetric algebra of the line bundle carries the
algebra unit to `1`. -/
theorem Situation.symmetricPieceZeroIso_hom_one (U : (Opens ↥D.X)ᵒᵖ) :
    D.symmetricPieceZeroIso.hom.val.app U (D.symmetricAlgebra.one.eval U) =
      (1 : D.X.ringCatSheaf.obj.obj U) :=
  @PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso_hom_one.{u, u, u} _ _ _ D.X.sheaf.obj
    D.X.ringCatSheaf (𝟙 D.X.ringCatSheaf.obj)
    (AlgebraicGeometry.Scheme.Modules.isLocallyInjective_id_ringCatSheaf D.X)
    (AlgebraicGeometry.Scheme.Modules.isLocallySurjective_id_ringCatSheaf D.X)
    inferInstance inferInstance D.L.val U

/-- **In degree zero the comparison of the symmetric algebra of the line bundle with its Laurent
algebra is the identification of both with the structure sheaf.** A degree-zero local section of
`Sym(L)` is a function on the base times the algebra unit, the comparison is linear and preserves
the unit, and degree zero of the Laurent algebra is the structure sheaf on the nose. -/
theorem Situation.symmetricToLaurent_app_zero :
    D.symmetricToLaurent.app 0 =
      D.symmetricPieceZeroIso.hom ≫ D.laurentPieceZeroIso.inv := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
  refine ModuleCat.hom_ext (LinearMap.ext (fun x => ?_))
  obtain ⟨r, hr⟩ := SheafOfModules.GradedAlgebra.exists_smul_one_of_isoUnit
    D.symmetricAlgebra D.symmetricPieceZeroIso D.symmetricPieceZeroIso_hom_one U x
  change (D.symmetricToLaurent.app 0).val.app U x = D.symmetricPieceZeroIso.hom.val.app U x
  rw [← hr, map_smul, map_smul, D.symmetricToLaurent.map_one U, D.symmetricPieceZeroIso_hom_one U]
  rfl

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra is an
isomorphism in degree zero.** -/
theorem Situation.isIso_symmetricToLaurent_app_zero : IsIso (D.symmetricToLaurent.app 0) :=
  CategoryTheory.isIso_of_eq_iso_hom (D.symmetricPieceZeroIso ≪≫ D.laurentPieceZeroIso.symm)
    D.symmetricToLaurent_app_zero

/-! ### Every nonnegative degree -/

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra is an
isomorphism in every nonnegative degree.** Degree zero is the identification of both algebras
with the structure sheaf; the step from `n` to `n + 1` multiplies by the degree-one generator,
where the comparison is already an isomorphism, and multiplication in the Laurent algebra is
locally surjective. -/
theorem Situation.isIso_symmetricToLaurent_app_natCast (n : ℕ) :
    IsIso (D.symmetricToLaurent.app (n : ℤ)) := by
  induction n with
  | zero => exact D.isIso_symmetricToLaurent_app_zero
  | succ m ih =>
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    refine D.isIso_symmetricToLaurent_app_of_epi (m + 1) ?_
    rw [hcast]
    exact D.epi_symmetricToLaurent_app_add (m : ℤ) 1 ih D.isIso_symmetricToLaurent_app_one

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra is an
isomorphism in every degree that is at least zero**, which together with its vanishing in
negative degrees describes it in every degree. -/
theorem Situation.isIso_symmetricToLaurent_app_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    IsIso (D.symmetricToLaurent.app n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact D.isIso_symmetricToLaurent_app_natCast m

end Stacks.LineBundle

end
