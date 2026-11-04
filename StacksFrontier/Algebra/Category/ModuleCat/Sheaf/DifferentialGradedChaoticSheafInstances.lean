module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionWeaklyExact

/-!
# The triangulated and linear structures over the sheaf of rings of a chaotic site

The derived pullback along a functor of chaotic sites (Tag 0GZC) and the systems of differential
graded algebras of Section 24.35 are stated for a sheaf of differential graded algebras over
`toRingCat ⊥ O`, the sheaf of rings underlying a sheaf of commutative rings `O` on a category
with the chaotic topology. The triangulated structures of `K(Mod(A, d))` (Tag 0FS7), of
`D(A, d)` (Tag 0FT4) and of `QC(A, d)` (Tag 0GZA) are stated for a ringed site, and the
`R`-linear structures of Remark 0H1E for the constant sheaf of rings `constRingSheaf R`; instance
search finds neither at a sheaf of rings written `toRingCat ⊥ O`. Each instance here is the
general one at the ringed site `⟨C, ⊥, O⟩`, or at the constant sheaf of rings, restated for that
spelling.

## Main results

* `SheafOfModules.DifferentialGradedModule.toRingCatHomotopyPretriangulated` and the companion
  instances: `K(Mod(A, d))`, `D(A, d)` and `QC(A, d)` are pretriangulated (and triangulated) for
  `A` over `toRingCat ⊥ O`.
* `SheafOfModules.DifferentialGradedModule.toRingCatHomotopyLinear` and
  `toRingCatDerivedCategoryLinear`: for `O` the constant sheaf of commutative rings with value
  `R`, they are `R`-linear, and so is `QC(A, d)`.

## References

* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Lemma 24.33.3 (Tag 0GZA)](https://stacks.math.columbia.edu/tag/0GZA)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe m u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

section Triangulated

variable {C : Type u} [Category.{u} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, m} (toRingCat (⊥ : GrothendieckTopology C) Osharp))

/-- The translation functors of `K(Mod(A, d))` (Tag 0FS7), for `A` over `toRingCat ⊥ O`. -/
@[instance_reducible]
instance toRingCatHomotopyHasShift : HasShift (HomotopyCategory.{u, m, m} A) ℤ :=
  HomotopyCategory.instHasShift (X := ⟨C, ⊥, Osharp⟩) A

/-- The translation functors of `K(Mod(A, d))` are additive, for `A` over `toRingCat ⊥ O`. -/
instance toRingCatHomotopyShiftFunctorAdditive (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{u, m, m} A) n).Additive :=
  HomotopyCategory.shiftFunctor_additive (X := ⟨C, ⊥, Osharp⟩) A n

/-- `K(Mod(A, d))` is pretriangulated (Tag 0FS7), for `A` over `toRingCat ⊥ O`. -/
@[instance_reducible]
instance toRingCatHomotopyPretriangulated : Pretriangulated (HomotopyCategory.{u, m, m} A) :=
  HomotopyCategory.instPretriangulated (X := ⟨C, ⊥, Osharp⟩) A

/-- `K(Mod(A, d))` is triangulated (Tag 0FS7), for `A` over `toRingCat ⊥ O`. -/
instance toRingCatHomotopyIsTriangulated : IsTriangulated (HomotopyCategory.{u, m, m} A) :=
  HomotopyCategory.instIsTriangulated (X := ⟨C, ⊥, Osharp⟩) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` are closed under composition and contain the
identities, for `A` over `toRingCat ⊥ O`. -/
instance toRingCatQuasiIsomorphismsIsMultiplicative :
    (quasiIsomorphisms.{u, m, m} A).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative' (X := ⟨C, ⊥, Osharp⟩) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` admit a left calculus of fractions, for `A` over
`toRingCat ⊥ O`. -/
instance toRingCatQuasiIsomorphismsHasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, m, m} A).HasLeftCalculusOfFractions :=
  quasiIsomorphisms_hasLeftCalculusOfFractions (X := ⟨C, ⊥, Osharp⟩) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` admit a right calculus of fractions, for `A` over
`toRingCat ⊥ O`. -/
instance toRingCatQuasiIsomorphismsHasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, m, m} A).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions (X := ⟨C, ⊥, Osharp⟩) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` are compatible with its triangulation, for `A` over
`toRingCat ⊥ O`. -/
instance toRingCatQuasiIsomorphismsIsCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, m, m} A).IsCompatibleWithTriangulation :=
  quasiIsomorphisms_isCompatibleWithTriangulation (X := ⟨C, ⊥, Osharp⟩) A

/-- `QC(A, d)` is closed under isomorphisms (Tag 0GZA), for `A` over `toRingCat ⊥ O`. -/
instance toRingCat_qc_isClosedUnderIsomorphisms : (Chaotic.QC A).IsClosedUnderIsomorphisms :=
  Chaotic.qc_isClosedUnderIsomorphisms (O := Osharp) A

/-- `QC(A, d)` is a triangulated subcategory of `D(A, d)` (Tag 0GZA), for `A` over
`toRingCat ⊥ O`. -/
instance toRingCat_qc_isTriangulated : (Chaotic.QC A).IsTriangulated :=
  Chaotic.qc_isTriangulated (O := Osharp) A

example : Pretriangulated (derivedCategory.{u, m, m} A) := inferInstance

example : (toDerivedCategory.{u, m, m} A).IsTriangulated := inferInstance

example : Pretriangulated (Chaotic.QC A).FullSubcategory := inferInstance

end Triangulated

section Linear

variable {C : Type u} [Category.{u} C] {R : Type u} [CommRing R]
  (A : DifferentialGradedAlgebra.{u, u}
    (toRingCat (⊥ : GrothendieckTopology C) (Stacks.PresheafOfModules.constCommRingSheaf R)))

/-- The `R`-linear structure on `Mod(A, d)` (Remark 0H1E), for `A` over the sheaf of rings
underlying the constant sheaf of commutative rings with value `R`. -/
@[instance_reducible]
instance toRingCatModuleLinear : Linear R (DifferentialGradedModule.{u, u, u} A) :=
  instLinear (C := C) (R := R) (A := A)

/-- **Multiplication by `r ∈ R` on a right differential graded `A`-module**, for `A` over the
sheaf of rings underlying the constant sheaf of commutative rings with value `R`. -/
def toRingCatScalarEnd (r : R) (M : DifferentialGradedModule.{u, u, u} A) : M ⟶ M :=
  scalarEnd (C := C) (R := R) (A := A) r M

/-- On sections over `U` in degree `n`, `toRingCatScalarEnd A r M` is multiplication by `r`. -/
theorem toRingCatScalarEnd_apply (r : R) (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ)
    (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) :
    ((toRingCatScalarEnd A r M).toHomologicalComplex.f n).val.app U x =
      (show (toRingCat (⊥ : GrothendieckTopology C)
        (Stacks.PresheafOfModules.constCommRingSheaf R)).obj.obj U from r) • x :=
  rfl

/-- Scalar multiplication of morphisms is precomposition with `toRingCatScalarEnd`. -/
theorem toRingCat_smul_eq_scalarEnd_comp (r : R) {M N : DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) : r • f = toRingCatScalarEnd A r M ≫ f :=
  smul_eq_scalarEnd_comp (C := C) (R := R) (A := A) r f

/-- The `R`-linear structure on `K(Mod(A, d))` (Remark 0H1E), for `A` over the sheaf of rings
underlying the constant sheaf of commutative rings with value `R`. -/
@[instance_reducible]
instance toRingCatHomotopyLinear : Linear R (HomotopyCategory.{u, u, u} A) :=
  HomotopyCategory.instLinear (C := C) (R := R) (A := A)

/-- The quotient functor `Mod(A, d) ⥤ K(Mod(A, d))` is `R`-linear. -/
instance toRingCatQuotientLinear : Functor.Linear R (HomotopyCategory.quotient.{u, u, u} A) :=
  HomotopyCategory.quotient_linear (C := C) (R := R) (A := A)

/-- The `R`-linear structure on `D(A, d)` (Remark 0H1E), for `A` over the sheaf of rings
underlying the constant sheaf of commutative rings with value `R`. -/
@[instance_reducible]
instance toRingCatDerivedCategoryLinear : Linear R (derivedCategory.{u, u, u} A) :=
  Localization.linear R (toDerivedCategory.{u, u, u} A) (quasiIsomorphisms.{u, u, u} A)

/-- The localization functor `K(Mod(A, d)) ⥤ D(A, d)` is `R`-linear. -/
instance toRingCatToDerivedCategoryLinear : Functor.Linear R (toDerivedCategory.{u, u, u} A) :=
  Localization.functor_linear R (toDerivedCategory.{u, u, u} A) (quasiIsomorphisms.{u, u, u} A)

example : Linear R (Chaotic.QC A).FullSubcategory := inferInstance

end Linear

end SheafOfModules.DifferentialGradedModule
