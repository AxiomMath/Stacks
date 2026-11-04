module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBundle
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints

/-!
# Tag 0FCY in one statement

Let `k` be a field and `V` a `k`-vector space. The projective space of `V` is the `k`-scheme
`𝐏(V) = Proj(Sym_k V)`, which is `AlgebraicGeometry.projectiveSpaceOfModule` together with its
structure morphism `AlgebraicGeometry.projectiveSpaceOfModuleToSpec`. About that scheme
Tag 0FCY makes five assertions beyond the definition itself:

* `𝐏(V) ≅ ℙⁿ_k` over `Spec k` when `dim V = n + 1`;
* reading `V` as a quasi-coherent module on `Spec k`, `𝐏(V)` is the projective space bundle of
  that module over `Spec k`;
* the `k`-valued points of `𝐏(V)` are the one-dimensional quotients of `V`;
* for a scheme `X` over `k`, an invertible `𝒪_X`-module `ℒ` and a `k`-linear map
  `ψ : V → Γ(X, ℒ)` whose image generates `ℒ`, there is a canonical morphism
  `φ_{ℒ,ψ} : X → 𝐏(V)` over `k`, an isomorphism `θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ`, and `ψ` is
  recovered from `(φ_{ℒ,ψ}, θ)`;
* for a basis `v₀, …, vₙ` of `V` the coordinate square built from `φ_{ℒ,ψ}`, the coordinate
  isomorphism `𝐏(V) ≅ ℙⁿ_k` and the morphism of Tag 01ND for the sections `ψ(vᵢ)` commutes.

Each of the five is established separately, and the five live in three mutually independent
modules, so no single declaration said what the tag says. This file states all five together.
The first three hold for every `k` and `V`; the last two are universally quantified over the
triple `(X, ℒ, ψ)` inside their conjunct, which keeps the first three free of any hypothesis
the source does not impose on them. The coordinate square is stated under the basis binder
of the source, nested inside the conjunct for `(X, ℒ, ψ)` so that it speaks about the very
morphism `φ_{ℒ,ψ}` that conjunct produces.

The morphism `φ_{ℒ,ψ}` appears by name rather than under an existential, because it is the
canonical one: `ProjectiveSpaceGeneratingSections.existsUnique_classifies` shows that it and
its trivialization are the unique pair classifying `(ℒ, ψ)`. The isomorphism `θ` is existential,
bundled with the recovery of `ψ` exactly as the source bundles them.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceOfModuleStatement.coordinates_bundle_points_sections`:
  **the five assertions of Tag 0FCY in one statement.**

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents (pullbackTwistOne pullbackSectionOne)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (grading degreeOneElement
  morphismOfGeneratingSections twistIsoOfGeneratingSections twistIso_pullbackSectionOne)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare (basisSections
  generatesStalks_basisSections morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec
  morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso)

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceOfModuleStatement

universe u

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **[Stacks, Tag 0FCY].** Let `k` be a field and `V` a `k`-vector space, and let
`𝐏(V) = Proj(Sym_k V)` be the projective space of `V`, with its structure morphism to `Spec k`.
Then:

* if `dim V = n + 1` then `𝐏(V)` is isomorphic to `ℙⁿ_k` as a scheme over `Spec k`;
* `𝐏(V)` is the projective space bundle over `Spec k` of `V` read as a quasi-coherent module on
  `Spec k`, by an isomorphism carrying the bundle projection to the structure morphism;
* the `k`-valued points of `𝐏(V)`, that is the sections of its structure morphism, correspond
  to the one-dimensional quotients of `V`, a point going to the space of vectors whose
  degree-one forms vanish at it;
* for every scheme `X` over `k`, every invertible `𝒪_X`-module `ℒ` and every `k`-linear map
  `ψ : V → Γ(X, ℒ)` whose image generates `ℒ`, the morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` is a morphism
  over `Spec k`, and there is an isomorphism `θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ` through which each
  `v : V` is sent to `ψ v` by the universal degree-one section of `v`;
* for every basis `v₀, …, vₙ` of `V`, the composite of `φ_{ℒ,ψ}` with the coordinate
  isomorphism `𝐏(V) ≅ ℙⁿ_k` of that basis is the morphism `X ⟶ ℙⁿ_k` of [Stacks, Tag 01ND] for
  the sections `ψ(v₀), …, ψ(vₙ)`. -/
@[stacks 0FCY "the five assertions of the tag in one statement"]
theorem coordinates_bundle_points_sections :
    (∀ n : ℕ, Module.finrank k V = n + 1 →
        Nonempty ((projectiveSpaceOfModule k V).asOver (Spec (.of k)) ≅
          (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k)))) ∧
      (∃ e : projectiveSpaceOfModule k V ≅
          Stacks.RelativeProj.projectiveBundle (Spec (.of k)) (tildeOfModule k V),
        e.hom ≫ Stacks.RelativeProj.projectiveBundleToBase (Spec (.of k)) (tildeOfModule k V) =
          projectiveSpaceOfModuleToSpec k V) ∧
      (∃ E : {p : Spec (.of k) ⟶ projectiveSpaceOfModule k V //
            p ≫ projectiveSpaceOfModuleToSpec k V = 𝟙 (Spec (.of k))} ≃
          {K : Submodule k V // Module.finrank k (V ⧸ K) = 1},
        ∀ p v, v ∈ (E p).val ↔
          SymmetricAlgebra.ι k V v ∈ (p.val.base default).asHomogeneousIdeal) ∧
      ∀ {X : Scheme.{u}} [X.Over (Spec (.of k))] (L : X.Modules)
          [Stacks.Ample.IsInvertibleModule X L] (ψ : V →ₗ[k] Γ(L, ⊤))
          (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤),
        morphismOfGeneratingSections k V L ψ hψ ≫ projectiveSpaceOfModuleToSpec k V =
            X ↘ Spec (.of k) ∧
          (∃ θ : pullbackTwistOne (grading k V) (morphismOfGeneratingSections k V L ψ hψ) ≅ L,
            ∀ v : V, θ.hom.app ⊤ (pullbackSectionOne (grading k V)
              (morphismOfGeneratingSections k V L ψ hψ) (degreeOneElement k V v)) = ψ v) ∧
          ∀ {n : ℕ} (b : Module.Basis (Fin (n + 1)) k V),
            morphismOfGeneratingSections k V L ψ hψ ≫
                (basisProjectiveSpaceOfModuleIso b).hom.left =
              Stacks.ProjectiveFromSections.toProjectiveSpaceOver (basisSections b ψ)
                (generatesStalks_basisSections b ψ hψ) (X ↘ Spec (.of k)) :=
  ⟨fun _ hdim => ⟨finrankProjectiveSpaceOfModuleIso hdim⟩,
    exists_iso_projectiveBundle_tildeOfModule k V,
    ⟨ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k V,
      ProjectiveSpaceOfModule.mem_kValuedPointEquivOneDimQuotient k V⟩,
    fun L _ ψ hψ =>
      ⟨morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec ψ hψ,
        ⟨twistIsoOfGeneratingSections k V L ψ hψ, twistIso_pullbackSectionOne k V L ψ hψ⟩,
        fun b => morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso b ψ hψ⟩⟩

end Stacks.AlgebraicGeometry.ProjectiveSpaceOfModuleStatement

end
