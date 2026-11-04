module

public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringInjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardSheafHomDerived

/-!
# The relative hypercovering complex of an injective module is exact in nonzero degrees

Let `f : X ⟶ S` be a morphism of schemes, let `K` be a hypercovering of the Zariski site of `X`
with base object the top open, and let `I` be an **injective** sheaf of `𝒪_X`-modules.  The complex

`𝓚⁼(K, f, I) = ( ∏_{i ∈ I₀} (U_i)_{,*} I|_{U_i} ⟶ ∏_{i ∈ I₁} (U_i)_{,*} I|_{U_i} ⟶ ⋯ )`

of `𝒪_S`-modules is **exact in every nonzero degree**.  This is the positive-degree half of the
relative form of [Stacks, Tag 01GV].

No hypothesis is placed on the members of `K`:  in particular they need not be affine, and `f` need
not be affine or separated.

## Main results

* `exactAt_sectionsAG_hypercoveringComplexAll_of_injective`:  over every open `V` of `S` the
  sections of the complex are exact in every nonzero degree.  This is
  `Stacks.Cohomology.HypercoveringInjective.exactAt_sectionsComplex_toSheaf_of_injective` read
  through `Stacks.AlgebraicGeometry.UniversalPushforward.hypercoveringSectionsComplexIso`.
* `exactAt_hypercoveringComplexAll_of_injective`:  **the complex of `𝒪_S`-modules itself is exact
  in every nonzero degree.**

## Implementation notes

The passage from the sections to the sheaves is one-directional and that is all that is available:
evaluation of sheaves of modules at an object is left exact but not exact off the chaotic topology,
so there is no criterion "exact if and only if exact on all sections".  What there is, and what is
used, is `SheafOfModules.exact_of_forall_exists_preimage`:  a short complex of sheaves of modules
all of whose sections admit preimages is exact.  Sections-level exactness of a short complex of
abelian groups gives those preimages by `CategoryTheory.ShortComplex.ab_exact_iff`.

The hypercovering of the open `f ⁻¹ V ⊓ ⊤` used at the stage `V` is the degreewise intersection of
`K` with `f ⁻¹ V`, which is a hypercovering by [Stacks, Tag 0DAZ] in the form
`Stacks.CategoryTheory.Hypercovering.IsHypercovering.opensInf`.  Its base object is `⊤ ⊓ f ⁻¹ V`
rather than `f ⁻¹ V`; nothing here or downstream cares, the base object being a parameter
throughout.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.CategoryTheory.Hypercovering

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

variable {X S : Scheme.{u}}

/-- **Over every open `V` of `S` the sections of the relative hypercovering complex of an injective
`𝒪_X`-module are exact in every nonzero degree.**

Those sections are the complex of sections of the hypercovering `K ⊓ f ⁻¹ V` with coefficients in
the underlying abelian sheaf of `I`, by `hypercoveringSectionsComplexIso`, and that complex is
exact in every nonzero degree because an injective sheaf of modules is acyclic on every open
([Stacks, Tag 03FD]) and the comparison of [Stacks, Tag 01GY] therefore degenerates. -/
theorem exactAt_sectionsAG_hypercoveringComplexAll_of_injective (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] (V : S.Opens) (q : ℕ) (hq : q ≠ 0) :
    (((sectionsAG S V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((FormalCoproduct.cochainComplexFunctor.{u} K).obj
        ((pushforwardPresheafAll f).obj I))).ExactAt q :=
  (Stacks.Cohomology.HypercoveringInjective.exactAt_sectionsComplex_toSheaf_of_injective
    X (K ⋙ mapFormalCoproduct.{u} (Over.post (opensInf (f ⁻¹ᵁ V)) (X := (⊤ : Opens X))))
    (IsHypercovering.opensInf (f ⁻¹ᵁ V) K hK) I q hq).of_iso
      (hypercoveringSectionsComplexIso f K I V).symm

/-- **The relative hypercovering complex of an injective `𝒪_X`-module is exact in every nonzero
degree.**  This is the clause `hex` of `quasiIso_hypercoveringAugNat_app`, the positive-degree half
of the relative form of [Stacks, Tag 01GV].

The members of `K` are not assumed affine and `f` is not assumed affine or separated. -/
theorem exactAt_hypercoveringComplexAll_of_injective (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] (q : ℕ) (hq : q ≠ 0) :
    ((FormalCoproduct.cochainComplexFunctor.{u} K).obj
      ((pushforwardPresheafAll f).obj I)).ExactAt q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  refine (HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)).2 ?_
  refine SheafOfModules.exact_of_forall_exists_preimage _ ?_
  intro T x hx
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    ((HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)).1
      (exactAt_sectionsAG_hypercoveringComplexAll_of_injective f K hK I T.unop (p + 1)
        (by omega))) x hx
  exact ⟨y, hy⟩

end Stacks.AlgebraicGeometry.UniversalPushforward

end
