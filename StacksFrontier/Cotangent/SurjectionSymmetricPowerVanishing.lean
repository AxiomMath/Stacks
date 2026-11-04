module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex

/-!
# Vanishing of the low homology of the symmetric powers of the differentials, for a surjection

Let `A → B` be a surjective ring map and let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` be the sheaf of `B̲`-modules on
the polynomial site `C_{B/A}`. Then

`H_i(C_{B/A}, Symᵏ_{B̲}(Ω)) = 0` for `i < k`,

for every `k`. This is the final assertion of Stacks Theorem 08RF, Quillen's spectral sequence.

The proof is the source's: `π_!(Ω) = Ω_{B/A} = 0` because `A → B` is surjective, each `Ω(U)` is
free over `B` on the variables of `U`, and Tag 08RD
(`Stacks.ChaoticSite.isZero_leftDerivedColim_symmetricPowerDiagram_of_lt`) turns those two facts
into the vanishing for every `k`.

## Main results

* `CommAlgCat.flat_overDifferentials`: `B ⊗_P Ω[P⁄A]` is a flat `B`-module when `P` is a
  polynomial algebra over `A`, i.e. `Ω` is a flat `B̲`-module.
* `CommAlgCat.leftDerivedColimPolynomialCotangentIso`: **Tag 08PU** at linear coefficients,
  `H_n(C_{B/A}, Ω) = H^{-n}(L_{B/A})` as `B`-modules.
* `CommAlgCat.isZero_leftDerivedColimZero_polynomialCotangentModulePresheaf_of_surjective`:
  `H₀(C_{B/A}, Ω) = 0`, at linear coefficients.
* `CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`: the
  vanishing, for every `k`.

## Implementation notes

`H_i(C_{B/A}, -)` is read as `L_i colim` over the opposite of the small model of the
footnote-restricted site, at linear coefficients. This is the form in which Tag 08RD is stated
(`Stacks.ChaoticSite.isZero_leftDerivedColim_symmetricPowerDiagram_of_lt`), and it is Tag 08PF's
definition of the homology of a category. The abelian-coefficient reading used by
`CommAlgCat.isZero_lowerShriekZero_polynomialCotangentSheaf_of_surjective` for `k = 1` goes
through the same Moore complex, by
`Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso`.

`Symᵏ_{B̲}(Ω)` is the sectionwise symmetric power
`Stacks.ChaoticSite.symmetricPowerDiagram`, which is the sheaf symmetric power because the
topology of `C_{B/A}` is chaotic, so no sheafification intervenes.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RD](https://stacks.math.columbia.edu/tag/08RD)
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **`Ω` is a flat `B̲`-module.** For an `A`-algebra `P` over `B` which is a polynomial algebra
over `A`, the `B`-module `B ⊗_P Ω[P⁄A]` is flat: `Ω[P⁄A]` is free over `P` on the variables, and
flatness is stable under base change. -/
theorem flat_overDifferentials {X : Over B} (h : IsPolynomialAlgebra A X.left) :
    Module.Flat (B : Type u) (overDifferentials X) := by
  let : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  have : Module.Free (X.left : Type u) Ω[(X.left : Type u)⁄A] :=
    free_kaehlerDifferential_of_isPolynomialAlgebra A h
  exact Module.Flat.baseChange (R := (X.left : Type u)) (S := (B : Type u))
    (M := Ω[(X.left : Type u)⁄A])

variable (κ : Cardinal.{u})

/-- Every module of sections of `Ω` on the small model of the restricted site is flat. -/
theorem flat_smallPolynomialCotangentModulePresheaf_obj
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Module.Flat (B : Type u) ((smallPolynomialCotangentModulePresheaf A B κ).obj X) :=
  flat_overDifferentials A B
    ((smallBoundedPolynomialSiteToPolynomialSite A B κ).obj X.unop).unop.property

/-- **`Ω(P_•, ε)` for the standard resolution is the simplicial module defining `L_{B/A}`**, at
linear coefficients: the module-valued counterpart of
`CommAlgCat.standardResolutionCotangentMooreComplexIso`, which is its image under the forgetful
functor to abelian groups. -/
def standardResolutionCotangentModuleMooreIso :
    (Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) ≅
      (alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object :=
  (alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
    (smallResolutionCotangentModuleIso (standardResolution.{u, u} A B).hom
        (standardResolutionVarCardinal A B)
        (standardResolution_isPolynomialAlgebraBelow A B) ≪≫
      standardResolutionOverDifferentialsIso A B)

/-- **Tag 08PU at the small model of the restricted site `C_{B/A}`, at linear coefficients.**
The `n`th homology of `C_{B/A}` with coefficients in `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` — the `n`th left
derived functor of the colimit over the opposite of the small model, which is Tag 08PF's
definition — is the degree `-n` cohomology of the cotangent complex `L_{B/A}` of Tag 08PN, as
`B`-modules.

This is the linear-coefficient refinement of
`CommAlgCat.standardResolutionLeftDerivedCotangentComplexIso`, which is its image under the
forgetful functor to abelian groups. The proof is the same: the module half of Tag 08Q9
computes `L_n colim` on the standard resolution, and the evaluation of `Ω` there is the
simplicial module defining `L_{B/A}`. -/
@[stacks 08PU "the identification L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) read degreewise at LINEAR \
  coefficients: for every n, the nth left derived functor of the colimit over the opposite of \
  the small model of the footnote-restricted site, applied to Ω, is the degree -n cohomology of \
  the cotangent complex of Tag 08PN, as an isomorphism of B-modules. L_n colim is Tag 08PF's \
  definition of H_n(C_{B/A}, -); the identification with the sections at the point of L_nπ_! is \
  Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedPointLowerShriekNatIso. Proved for every \
  ring map A → B"]
def leftDerivedColimPolynomialCotangentIso (n : ℕ) :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived n).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) ≅
      (cotangentComplex.{u, u} A B).homology (-(n : ℤ)) :=
  (Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso
        (standardResolutionSmallCosimplicialObject A B)
        (isPointResolution_standardResolutionSmallCosimplicialObject A B) n).app
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n).mapIso
      (standardResolutionCotangentModuleMooreIso A B) ≪≫
    (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object).extendHomologyIso
      (ComplexShape.embeddingUpIntLE 0) (j := n) (j' := -(n : ℤ)) (by simp)).symm

/-- **`H₀(C_{B/A}, Ω) = 0` for a surjective `A → B`, at linear coefficients.** This is the first
step of the source's proof of Tag 08RF: `π_!(Ω) = Ω_{B/A} = 0` by Tag 08QF and
`Algebra.Lemma 00RP`. The abelian-coefficient form is
`CommAlgCat.isZero_lowerShriekZero_polynomialCotangentSheaf_of_surjective`. -/
theorem isZero_leftDerivedColimZero_polynomialCotangentModulePresheaf_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))) := by
  have hs : Subsingleton Ω[(B : Type u)⁄A] :=
    KaehlerDifferential.subsingleton_of_surjective A (B : Type u) hsurj
  have h0 : IsZero (ModuleCat.of (B : Type u) Ω[(B : Type u)⁄A]) :=
    ModuleCat.isZero_iff_subsingleton.mpr hs
  have h1 : IsZero ((cotangentComplex.{u, u} A B).homology (-((0 : ℕ) : ℤ))) := by
    rw [Nat.cast_zero, neg_zero]
    exact h0.of_iso (cotangentComplex_homologyZeroIso A B)
  exact h1.of_iso (leftDerivedColimPolynomialCotangentIso A B 0)

/-- **Stacks 08RF, the final vanishing, for every `k`.** For a surjective ring map `A → B` and
the sheaf `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` on the polynomial site `C_{B/A}`,

`H_i(C_{B/A}, Symᵏ_{B̲}(Ω)) = 0` for `i < k`.

The source's proof: `Ω` is flat and `H₀(C_{B/A}, Ω) = π_!(Ω) = Ω_{B/A} = 0` because `A → B` is
surjective, and Tag 08RD gives the vanishing from those two facts. -/
@[stacks 08RF "the final vanishing H_i(C_{B/A}, Symᵏ_{B̲}(Ω)) = 0 for i < k, for EVERY k, where \
  Symᵏ is the sectionwise symmetric power, which is the sheaf symmetric power because the \
  topology of C_{B/A} is chaotic. H_i(C_{B/A}, -) is L_i of the colimit over the opposite of \
  the small model of the footnote-restricted site at linear coefficients, which is Tag 08PF's \
  definition of the homology of a category. The proof is the source's: Ω is a flat B̲-module \
  because each Ω[P⁄A] is free over P, π_!(Ω) = Ω_{B/A} = 0 for a surjective A → B, and Tag 08RD \
  turns those into the vanishing. No hypothesis beyond the source's surjectivity of A → B"]
theorem isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (k l : ℕ) (hl : l < k) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived l).obj
      (Stacks.ChaoticSite.symmetricPowerDiagram
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) k)) :=
  Stacks.ChaoticSite.isZero_leftDerivedColim_symmetricPowerDiagram_of_lt
    (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B)
    (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))
    (flat_smallPolynomialCotangentModulePresheaf_obj A B _)
    (isZero_leftDerivedColimZero_polynomialCotangentModulePresheaf_of_surjective A B hsurj) k l hl

end CommAlgCat

end
