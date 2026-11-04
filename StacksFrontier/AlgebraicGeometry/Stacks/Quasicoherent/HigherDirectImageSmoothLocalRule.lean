module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesULiftComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRuleCriterion

/-!
# The criterion of Stacks 076Z and Stacks 0770

Let `τ` be the étale or the fppf topology and let `M` be a rule assigning to every algebraic stack
`𝒳` over `S` a property `M_𝒳` of the modules on `𝒳_τ` (with sections in the universe of the
schemes) such that

1. `M_𝒳` is a weak Serre subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` for every `𝒳`;
2. for a smooth 1-morphism `f : 𝒴 ⟶ 𝒳` the inverse image `f^*` maps `M_𝒳` into `M_𝒴`;
3. for a family of smooth 1-morphisms `fᵢ : 𝒳ᵢ ⟶ 𝒳` with `|𝒳| = ⋃ᵢ |fᵢ|(|𝒳ᵢ|)`, a module `ℱ`
   lies in `M_𝒳` if and only if every `fᵢ^*ℱ` lies in `M_{𝒳ᵢ}`; and
4. for a 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks representable by affine schemes, `Rⁱf_*`
   maps `M_𝒴` into `M_𝒳`.

Then for every quasi-compact quasi-separated 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks,
`Rⁱf_*` maps `M_𝒴` into `M_𝒳` in every degree, the higher direct images being computed in the
topology `τ`. This is **Stacks 076Z** for the étale topology and **Stacks 0770** for the fppf
topology, whose proof is "identical to the proof of Lemma 076Z"; both are instances here of one
theorem for every topology finer than the étale one.

## Main results

* `AlgebraicGeometry.Stack.StackModuleRule.preservesHigherDirectImages_of_smoothBaseChange`: the
  criterion from clauses (1) to (4) and the smooth base change of **Stacks 075H**.
* `AlgebraicGeometry.Stack.StackModuleRule.preservesHigherDirectImages`: the criterion for every
  topology finer than the étale one.
* `AlgebraicGeometry.Stack.StackModuleRule.preservesHigherDirectImages_etale`: **Stacks 076Z**.
* `AlgebraicGeometry.Stack.StackModuleRule.preservesHigherDirectImages_fppf`: **Stacks 0770**.

## Implementation notes

The proof is the source's: the target is reduced to an affine scheme by clauses (2), (3) and the
base change of higher direct images along smooth 1-morphisms (**Stacks 075H**,
`AlgebraicGeometry.Stack.hasSmoothBaseChange_stackModuleDirectImageData`), and over an affine
target the source of the 1-morphism is improved four times — algebraic stack, algebraic space,
scheme, separated scheme, affine scheme — along the relative Čech spectral sequence of an affine
presentation (**Stacks 072G**), using clauses (1), (2), (4) and part (4) of **Stacks 0132**. The
pieces are `AlgebraicGeometry.Stack.StackModuleRule.preservedBy_of_affineTarget`,
`AlgebraicGeometry.Stack.AlgebraicStacks.cechLevel_induction_of_isQuasiCompact` and
`AlgebraicGeometry.Stack.StackModuleRule.hasCechSpectralSequence_stackModuleDirectImageData`;
the comparison of the higher direct images at the module universes `u` and `u + 1`, along which
the spectral sequence of **Stacks 072G** descends, is
`AlgebraicGeometry.Stack.higherDirectImageULiftComparison`.

The higher direct images are those of the direct image
`AlgebraicGeometry.Stack.stackModuleDirectImageData`, right adjoint to the inverse image, at the
universe of the schemes.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack.StackModuleRule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (τ : SiteKind)

/-- **The criterion of Stacks 076Z and Stacks 0770, from the smooth base change of Stacks 075H.**
Let `τ` be a topology finer than the étale one and let `M` be a rule satisfying clauses (1) to
(4). Granted the smooth base change of **Stacks 075H** for the direct image at the universe of the
schemes, the higher direct images along every quasi-compact quasi-separated 1-morphism of
algebraic stacks preserve `M` in every degree. -/
theorem preservesHigherDirectImages_of_smoothBaseChange
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (hbc : HasSmoothBaseChange (stackModuleDirectImageData.{u, t} B S hS τ))
    (M : StackModuleRule.{u, t} B S hS τ) (h1 : IsWeakSerre τ M)
    (h2 : IsStableUnderSmoothPullback τ M) (h3 : IsSmoothLocal.{u, t, u} τ M)
    (h4 : PreservesHigherDirectImagesOfAffine (stackModuleDirectImageData.{u, t} B S hS τ) M) :
    PreservesHigherDirectImages (stackModuleDirectImageData.{u, t} B S hS τ) M :=
  preservesHigherDirectImages_of_hasSmoothBaseChange τ hτ
    (higherDirectImageULiftComparison τ) hbc M h1 h2 h3 h4

/-- **The criterion of Stacks 076Z and Stacks 0770 for every topology finer than the étale one.**
Let `M` be a rule satisfying clauses (1) to (4). Then the higher direct images along every
quasi-compact quasi-separated 1-morphism of algebraic stacks preserve `M` in every degree. -/
theorem preservesHigherDirectImages (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (M : StackModuleRule.{u, t} B S hS τ) (h1 : IsWeakSerre τ M)
    (h2 : IsStableUnderSmoothPullback τ M) (h3 : IsSmoothLocal.{u, t, u} τ M)
    (h4 : PreservesHigherDirectImagesOfAffine (stackModuleDirectImageData.{u, t} B S hS τ) M) :
    PreservesHigherDirectImages (stackModuleDirectImageData.{u, t} B S hS τ) M :=
  preservesHigherDirectImages_of_smoothBaseChange τ hτ
    (hasSmoothBaseChange_stackModuleDirectImageData B S hS τ) M h1 h2 h3 h4

/-- **Stacks 076Z.** Let `M` be a rule which associates to every algebraic stack `𝒳` over `S` a
property `M_𝒳` of the sheaves of `𝒪_𝒳`-modules on the étale site `𝒳_étale` such that

1. `M_𝒳` is a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` for all algebraic stacks `𝒳`;
2. for a smooth 1-morphism `f : 𝒵 ⟶ 𝒳` the inverse image `f^*` maps `M_𝒳` into `M_𝒵`;
3. if `fᵢ : 𝒳ᵢ ⟶ 𝒳` is a family of smooth 1-morphisms with `|𝒳| = ⋃ᵢ |fᵢ|(|𝒳ᵢ|)`, then a module
   `ℱ` lies in `M_𝒳` if and only if every `fᵢ^*ℱ` lies in `M_{𝒳ᵢ}`; and
4. if `f : 𝒳 ⟶ 𝒴` is a 1-morphism of algebraic stacks and `𝒳` and `𝒴` are representable by
   affine schemes, then `Rⁱf_*` maps `M_𝒳` into `M_𝒴`.

Then for every quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks,
`Rⁱf_*` maps `M_𝒳` into `M_𝒴` in every degree, the higher direct images being computed in the
étale topology.

Two readings of the statement. Clause (3) is asked only for families indexed by a type in the
universe of the schemes, which makes the hypothesis weaker and the theorem stronger.
"Representable by an affine scheme" in clause (4) is equivalence over the site with the big site
of an affine scheme (`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineRepresentable`). Modules have
sections in the universe of the schemes, and the higher direct images are the right derived
functors of the direct image right adjoint to the inverse image. -/
theorem preservesHigherDirectImages_etale (M : StackModuleRule.{u, t} B S hS .etale)
    (h1 : IsWeakSerre .etale M) (h2 : IsStableUnderSmoothPullback .etale M)
    (h3 : IsSmoothLocal.{u, t, u} .etale M)
    (h4 : PreservesHigherDirectImagesOfAffine (stackModuleDirectImageData.{u, t} B S hS .etale) M) :
    PreservesHigherDirectImages (stackModuleDirectImageData.{u, t} B S hS .etale) M :=
  preservesHigherDirectImages .etale le_rfl M h1 h2 h3 h4

/-- **Stacks 0770.** Let `M` be a rule which associates to every algebraic stack `𝒳` over `S` a
property `M_𝒳` of the sheaves of `𝒪_𝒳`-modules on the fppf site of `𝒳` such that

1. `M_𝒳` is a weak Serre subcategory of `Mod(𝒪_𝒳)` for all algebraic stacks `𝒳`;
2. for a smooth 1-morphism `f : 𝒵 ⟶ 𝒳` the inverse image `f^*` maps `M_𝒳` into `M_𝒵`;
3. if `fᵢ : 𝒳ᵢ ⟶ 𝒳` is a family of smooth 1-morphisms with `|𝒳| = ⋃ᵢ |fᵢ|(|𝒳ᵢ|)`, then a module
   `ℱ` lies in `M_𝒳` if and only if every `fᵢ^*ℱ` lies in `M_{𝒳ᵢ}`; and
4. if `f : 𝒳 ⟶ 𝒴` is a 1-morphism of algebraic stacks and `𝒳` and `𝒴` are representable by
   affine schemes, then `Rⁱf_*` maps `M_𝒳` into `M_𝒴`.

Then for every quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks,
`Rⁱf_*` maps `M_𝒳` into `M_𝒴` in every degree, the higher direct images being computed in the
fppf topology.

Clause (1) is read as "`M_𝒳` is a weak Serre subcategory": the source prints "`𝒪_𝒳` is a weak
Serre subcategory", a typo, as the identical clause (1) of **Stacks 076Z** shows. Clause (3) is
asked only for families indexed by a type in the universe of the schemes, which makes the
hypothesis weaker and the theorem stronger. "Representable by an affine scheme" in clause (4) is
equivalence over the site with the big site of an affine scheme
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineRepresentable`). Modules have sections in the
universe of the schemes, and the higher direct images are the right derived functors of the
direct image right adjoint to the inverse image. -/
@[stacks 0770 "the whole statement: every rule satisfying (1)-(4), every quasi-compact \
  quasi-separated 1-morphism of algebraic stacks and every degree, higher direct images in the \
  fppf topology; (1) read as M_X weak Serre (the source's O_X is a typo), (3) asked for \
  families indexed by Type u only"]
theorem preservesHigherDirectImages_fppf (M : StackModuleRule.{u, t} B S hS .fppf)
    (h1 : IsWeakSerre .fppf M) (h2 : IsStableUnderSmoothPullback .fppf M)
    (h3 : IsSmoothLocal.{u, t, u} .fppf M)
    (h4 : PreservesHigherDirectImagesOfAffine (stackModuleDirectImageData.{u, t} B S hS .fppf) M) :
    PreservesHigherDirectImages (stackModuleDirectImageData.{u, t} B S hS .fppf) M :=
  preservesHigherDirectImages .fppf (B.baseTopology_le_topology .etale) M h1 h2 h3 h4

end AlgebraicGeometry.Stack.StackModuleRule

end
