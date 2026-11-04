module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerDecalage
public import StacksFrontier.Cotangent.Surjection
public import StacksFrontier.Cotangent.SurjectionSymmetricPowerVanishing

/-!
# The homology of the symmetric powers of the differentials is the exterior power of `I/I²`

Let `A → B` be a surjective ring map, let `I = ker(A → B)` and let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` be the
sheaf of `B̲`-modules on the polynomial site `C_{B/A}`. Stacks Remark 08RG asserts, as its second
clause, that

`H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(I/I²)`,

deducing it from Remark 08SG applied to `Ω`. This file makes that deduction, over an arbitrary
commutative ring and with no hypothesis beyond the remark's own surjectivity of `A → B`: `Ω` is a
flat `B̲`-module with `H_0(C_{B/A}, Ω) = 0` and `C_{B/A}` carries a point resolution, so Remark
08SG applies, and `H_1(C_{B/A}, Ω) = I/I²` by the remark's opening clause, so the exterior power
of `H_1(C_{B/A}, Ω)` is the exterior power of `I/I²`.

## Main definitions

* `CommAlgCat.leftDerivedColimOneConormalLinearEquiv`: the opening clause
  `H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω) = I/I²` as an isomorphism of `B`-modules.

## Main results

* `CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`: the second
  clause of Remark 08RG.

## Implementation notes

`H_i(C_{B/A}, -)` is `L_i` of the colimit over the opposite of the small model of the
footnote-restricted site, at linear coefficients, which is Tag 08PF's definition of the homology
of a category and the form in which Remark 08SG is available
(`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`). `Sym^k_{B̲}`
is the sectionwise symmetric power, which is the sheaf symmetric power because the topology of
`C_{B/A}` is chaotic.

`I/I²` is `(CommAlgCat.surjectionExtension A B h).Cotangent`, the conormal module of the
presentation of `B` by `A` itself; it is the `B`-module Tag 08RA produces for `H^{-1}(L_{B/A})`,
and `CommAlgCat.surjectionConormalAddEquiv` identifies it with
`Ideal.Cotangent (RingHom.ker (algebraMap A B))` as an additive group.

### The route taken, and the remark's own route

Remark 08SG holds over every commutative ring, `2` invertible or not:
`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram` is that
identity, proved by Illusie's and Quillen's décalage. What the deduction below needs of 08SG is
exactly that identity, so the clause of 08RG comes out over every `B` and with no hypothesis
beyond surjectivity.

Remark 08SG's own route to its identity runs through an intermediate step whose verification the
source omits — that `H_k(C, Sym^k_{B̲}(ℱ))` is the `S_k`-coinvariants of `H_1(C, ℱ)^{⊗ k}` for
the permutation action multiplied by the sign character,
`Stacks.ChaoticSite.QuillenSignedCoinvariants`. That step is a proof erratum: it is refuted over
`ℤ` by `Stacks.ChaoticSite.not_quillenSignedCoinvariants_int`. The route below avoids it.

### Where the erratum shows up inside 08RG's own instance

The witness refuting the coinvariants step is the very instance `ℱ = Ω` that Remark 08RG uses.
Take `A = ℤ[x]` and `B = ℤ = A/(x)`, so `I = (x)` and `I/I² ≅ ℤ` is free of rank one
(`Ideal.cotangentIntEquivKerEvalZero`), and take `k = 2`. Then `∧²_ℤ(I/I²) = 0`, so the clause
below gives `H_2(C_{B/A}, Sym²(Ω)) = 0`, while the sign-twisted `S_2`-coinvariants of
`H_1(C_{B/A}, Ω)^{⊗ 2} = ℤ^{⊗ 2}` are `ℤ/2`, the class of `1 ⊗ 1` being detected by
`Stacks.SignedTensorPower.mk_tprod_one_ne_zero`. Both sides of the clause agree at `0` and it is
the coinvariants description that breaks.

The structural reason is that `S_k`-coinvariants is not exact, so the derived symmetric power is
not the coinvariants of the derived tensor power: the correct identification is the décalage
`LSym^k(M[1]) = (∧^k M)[k]`, from which the naive coinvariants of `H^{-1}(⋯)^{⊗ k}` differ by the
higher homology of `S_k`, which at `k = 2` is the `2`-torsion above.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08SG](https://stacks.math.columbia.edu/tag/08SG)
* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
-/

@[expose] public noncomputable section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  (h : Function.Surjective (algebraMap A (B : Type u)))

/-- **Stacks 08RG**, the opening clause `H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω) = I/I²` for a
surjective ring map `A → B` with kernel `I`, as an isomorphism of `B`-modules: the first
homology of `C_{B/A}` with coefficients in `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` is the conormal module `I/I²` of
the presentation of `B` by `A` itself.

The first equality is Tag 08PU in degree `n = 1`, at linear coefficients
(`CommAlgCat.leftDerivedColimPolynomialCotangentIso`); the second is Tag 08RA
(`CommAlgCat.cotangentComplex_homologyNegOneIso`). The abelian-group form of the same clause is
`CommAlgCat.polynomialSiteHomologyOneConormalIso`, which reads `H_1` as the sections at the
point of `L₁π_!`. -/
@[stacks 08RG "the opening clause H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω) = I/I² for a surjective \
  A → B with I = ker(A → B), as an isomorphism of B-MODULES: the first left derived functor of \
  the colimit over the opposite of the small model of the footnote-restricted site, applied to \
  Ω = Ω_{𝒪/A} ⊗_𝒪 B̲, is the conormal module I/I² of the presentation of B by A itself. \
  H_1(C_{B/A}, -) = L_1 colim at linear coefficients is Tag 08PF's definition; the first \
  equality is Tag 08PU in degree 1 and the second is Tag 08RA. I/I² is \
  (CommAlgCat.surjectionExtension A B h).Cotangent, which \
  CommAlgCat.surjectionConormalAddEquiv identifies with \
  Ideal.Cotangent (RingHom.ker (algebraMap A B)). No hypothesis beyond the remark's own \
  surjectivity of A → B"]
def leftDerivedColimOneConormalLinearEquiv :
    ↥(((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))) ≃ₗ[B]
      (surjectionExtension.{u, u} A B h).Cotangent :=
  (leftDerivedColimPolynomialCotangentIso A B 1 ≪≫
    eqToIso (congrArg (fun i : ℤ => (cotangentComplex.{u, u} A B).homology i)
      (show (-((1 : ℕ) : ℤ)) = -1 by norm_num)) ≪≫
    cotangentComplex_homologyNegOneIso.{u, u} A B h).toLinearEquiv

/-- **Stacks 08RG**, the second clause `H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(I/I²)`, which the remark
gets from Remark 08SG applied to `Ω`.

Let `A → B` be surjective with kernel `I` and let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` on `C_{B/A}`. Then the
`k`-th homology of `C_{B/A}` with coefficients in the `k`-th sectionwise symmetric power of `Ω`
is the `k`-th exterior power of `I/I²` over `B`, for every `k`.

The deduction is the remark's own: `Ω` is a flat `B̲`-module
(`CommAlgCat.flat_smallPolynomialCotangentModulePresheaf_obj`) with `H_0(C_{B/A}, Ω) = 0`
(`CommAlgCat.isZero_leftDerivedColimZero_polynomialCotangentModulePresheaf_of_surjective`) on a
site with a point resolution
(`CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`), so Remark 08SG
applies and gives `H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(H_1(C_{B/A}, Ω))`; the remark's opening clause
`leftDerivedColimOneConormalLinearEquiv` then replaces `H_1(C_{B/A}, Ω)` by `I/I²`.

No hypothesis is placed on `B`; in particular `2` need not be invertible. Remark 08SG is used in
the form `Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`, which
holds over every commutative ring by décalage, and not through 08SG's own sign-twisted
coinvariants step, which `Stacks.ChaoticSite.not_quillenSignedCoinvariants_int` refutes over
`ℤ`; see the module docstring. -/
@[stacks 08RG "the second clause H_k(C_{B/A}, Sym^k_{B̲}(Ω)) = ∧^k_B(I/I²) for a surjective \
  A → B with I = ker(A → B), as an isomorphism of B-modules, for every k, over an arbitrary \
  commutative ring B and with no hypothesis beyond the remark's own surjectivity of A → B; in \
  particular 2 need not be invertible. H_k(C_{B/A}, -) = L_k colim over the opposite of the \
  small model of the footnote-restricted site at linear coefficients is Tag 08PF's definition of \
  the homology of a category, Sym^k_{B̲} is the sectionwise symmetric power, which is the sheaf \
  symmetric power because the topology of C_{B/A} is chaotic, and I/I² is \
  (CommAlgCat.surjectionExtension A B h).Cotangent, the conormal module of the presentation of B \
  by A itself, which CommAlgCat.surjectionConormalAddEquiv identifies with \
  Ideal.Cotangent (RingHom.ker (algebraMap A B)). The deduction is the remark's own: Remark 08SG \
  applied to ℱ = Ω, which is a flat B̲-module with H_0(C_{B/A}, Ω) = 0 on a site with a point \
  resolution, composed with the remark's opening clause H_1(C_{B/A}, Ω) = I/I². Remark 08SG \
  enters in the form \
  Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram, which holds \
  over every commutative ring by Illusie's and Quillen's décalage; 08SG's own sign-twisted \
  S_k-coinvariants step is a proof erratum, refuted over ℤ by \
  Stacks.ChaoticSite.not_quillenSignedCoinvariants_int, and plays no role here"]
theorem exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective (k : ℕ) :
    Nonempty (↥(((colim :
              ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
                ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
            (Stacks.ChaoticSite.symmetricPowerDiagram
              (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
              (smallPolynomialCotangentModulePresheaf A B
                (standardResolutionVarCardinal A B)) k)) ≃ₗ[B]
        ⋀[(B : Type u)]^k (surjectionExtension.{u, u} A B h).Cotangent) := by
  obtain ⟨e⟩ :=
    Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram
      (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
      (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))
      (flat_smallPolynomialCotangentModulePresheaf_obj A B _)
      (isZero_leftDerivedColimZero_polynomialCotangentModulePresheaf_of_surjective A B h) k
  exact ⟨e.trans (Stacks.ChaoticSite.exteriorPowerCongr
    (leftDerivedColimOneConormalLinearEquiv A B h) k)⟩

end CommAlgCat

end
