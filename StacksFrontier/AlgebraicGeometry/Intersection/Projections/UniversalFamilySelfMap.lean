module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.UniversalFamilyProductSpace
public import StacksFrontier.AlgebraicGeometry.SymProjectiveBundleTwist.Basic

/-!
# The universal family of projective transformations as a self-map of `𝐏 × 𝐏(V)`

Let `V` be a finite-dimensional vector space over a field `k`, let `E = End(V)` and let
`𝐏 = 𝐏(Eᵛ)` be the projective space of the dual of `E`. Tag 0B2W displays its universal family
of projective transformations as the partially defined self-map

`𝐏 × 𝐏(V) ⊇ U(ψ) --r_ψ--> 𝐏 × 𝐏(V)`

of the product of the parameter space with the projective space of `V`, using the two
identifications `𝐏(V ⊗ 𝒪_𝐏) = 𝐏 × 𝐏(V)` and `𝐏(V ⊗ 𝒪_𝐏(1)) = 𝐏(V ⊗ 𝒪_𝐏)`.

`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyOverProjectiveSpace.lean`
builds `ψ`, the open `U(ψ)` and the family `r_ψ` on it;
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyProductSpace.lean` makes
the first identification, for the target. **This file makes the second one and assembles the
display.** The second identification is Tag 02NC — the invariance of a relative homogeneous
spectrum under twisting by an invertible module — in its projective-bundle form
`Stacks.SymProjectiveBundleTwist.exists_iso_schemeProjectiveBundle_tensorObj`, applied to the
constant module `V ⊗ 𝒪_𝐏` and the invertible module `𝒪_𝐏(1)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalProductSpace`: the product `𝐏 × 𝐏(V)`, as
  the fibre product of the parameter space with the projective space of `V` over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalProductToParam`: its projection to `𝐏`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_iso_pullback_universalEndSource`: **the
  source of the universal family is the product `𝐏 × 𝐏(V)`**, which is Tag 0B2W's second
  displayed identification; this is what was missing.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_iso_universalEndFamily_selfMap`: **Tag
  0B2W**, the displayed diagram: both total spaces of the family are identified with `𝐏 × 𝐏(V)`
  over `𝐏`, the domain `U(ψ)` is thereby an open subscheme of `𝐏 × 𝐏(V)`, and `r_ψ`, read
  through the identifications, is a morphism from that open to `𝐏 × 𝐏(V)` over `𝐏`.

## Implementation notes

The invertible module is `𝒪_𝐏(1) = twistStructureSheaf k Eᵛ 1`, invertible by
`AlgebraicGeometry.ProjectiveSpaceOfModule.isInvertible_tautologicalModule`: the homogeneous
coordinate ring `Sym_k(Eᵛ)` is generated in degree one over its degree-zero part. The twisted
module `V ⊗ 𝒪_𝐏(1)` of the universal family is `twistObj k Eᵛ (V ⊗ 𝒪_𝐏) 1`, which **is** the
tensor product `Stacks.SymTwistChart.tensorObj (V ⊗ 𝒪_𝐏) 𝒪_𝐏(1)` the projective-bundle form of
Tag 02NC is stated for: `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` is
defined as that tensor product, so no comparison of modules is needed and none is built.

The display is recorded as one existential over the two identifications rather than against
named isomorphisms, because both inputs — Tag 02NC's comparison and the base change of Tag 01O3
— are existence statements, the second irreducibly so: it rests on
`AlgebraicGeometry.projectiveBundlePresentationsAgree`, an existence statement about two
glueings of one object.

## References

* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SymGraded
open Stacks.AlgebraicGeometry.ProjectiveSpaceSections

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- **The product `𝐏 × 𝐏(V)`** of Tag 0B2W's display: the fibre product of the parameter space
`𝐏 = 𝐏(Eᵛ)` with the projective space of `V`, over `Spec k`. -/
abbrev universalProductSpace : Scheme.{u} :=
  pullback (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
    (schemeProjectiveBundle (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
      (isQuasicoherentPieces_of_isQuasicoherent _)).toBase

/-- The projection `𝐏 × 𝐏(V) ⟶ 𝐏` of Tag 0B2W's display, the morphism the family is a family
over. -/
abbrev universalProductToParam :
    universalProductSpace k V ⟶ projectiveSpaceOfModule k (dualEndSpace k V) :=
  pullback.fst (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
    (schemeProjectiveBundle (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
      (isQuasicoherentPieces_of_isQuasicoherent _)).toBase

/-- **`𝒪_𝐏(1)` is invertible on the parameter space**, at the spelling the projective-bundle form
of Tag 02NC is stated for. -/
instance isInvertible_twistStructureSheaf_param :
    Stacks.SheafOfModules.IsInvertible
      (projectiveSpaceOfModule k (dualEndSpace k V)).sheaf.obj
      (projectiveSpaceOfModule k (dualEndSpace k V)).ringCatSheaf.property
      (twistStructureSheaf k (dualEndSpace k V) ((1 : ℕ) : ℤ)) :=
  isInvertible_tautologicalModule k (dualEndSpace k V)

/-- **The source of Tag 0B2W's universal family is the product `𝐏 × 𝐏(V)`.** The twisted total
space `𝐏(V ⊗ 𝒪_𝐏(1))` is the untwisted one `𝐏(V ⊗ 𝒪_𝐏)` by Tag 02NC over a base scheme in its
projective-bundle form, and that one is the product by the base change of Tag 01O3. This is the
second of Tag 0B2W's two displayed identifications. -/
theorem exists_iso_pullback_universalEndSource :
    ∃ e : (schemeProjectiveBundle (twistObj k (dualEndSpace k V)
          (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅ universalProductSpace k V,
      e.hom ≫ universalProductToParam k V =
        schemeProjectiveBundleToBase (twistObj k (dualEndSpace k V)
          (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
          (isQuasicoherentPieces_of_isQuasicoherent _) := by
  obtain ⟨f, hf⟩ := Stacks.SymProjectiveBundleTwist.exists_iso_schemeProjectiveBundle_tensorObj
    (constantModule k (dualEndSpace k V) V)
    (twistStructureSheaf k (dualEndSpace k V) ((1 : ℕ) : ℤ))
  obtain ⟨e₀, he₀⟩ := exists_iso_pullback_universalEndTarget k V
  refine ⟨f ≪≫ e₀, ?_⟩
  show (f.hom ≫ e₀.hom) ≫ universalProductToParam k V = _
  rw [Category.assoc, he₀]
  exact hf

/-- **[Stacks, Tag 0B2W].** The universal family of projective transformations of a
finite-dimensional vector space `V` over a field `k`, read as the partially defined self-map

`𝐏 × 𝐏(V) ⊇ U(ψ) --r_ψ--> 𝐏 × 𝐏(V)`

of the product of the parameter space `𝐏 = 𝐏(Eᵛ)`, `E = End(V)`, with the projective space of
`V`, as the source displays it.

Both total spaces of the family built in
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection` — the twisted
`𝐏(V ⊗ 𝒪_𝐏(1))` and the untwisted `𝐏(V ⊗ 𝒪_𝐏)` — are isomorphic to `𝐏 × 𝐏(V)` by isomorphisms
over `𝐏`; under the first of them the domain of definition `U(ψ)` becomes an open subscheme of
`𝐏 × 𝐏(V)`, and `r_ψ`, read through the second, is a morphism from that open subscheme to
`𝐏 × 𝐏(V)` over `𝐏`, hence a family of partially defined self-maps of `𝐏(V)` indexed by `𝐏`. -/
@[stacks 0B2W "the universal family of projective transformations as the displayed partially \
defined self-map of 𝐏 × 𝐏(V): both total spaces identified with the product over 𝐏, U(ψ) as an \
open subscheme of the product, and r_ψ as a morphism of the product over 𝐏"]
theorem exists_iso_universalEndFamily_selfMap :
    ∃ (α : (schemeProjectiveBundle (twistObj k (dualEndSpace k V)
          (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅ universalProductSpace k V)
      (β : (schemeProjectiveBundle (constantModule k (dualEndSpace k V) V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅ universalProductSpace k V),
      α.hom ≫ universalProductToParam k V =
          schemeProjectiveBundleToBase (twistObj k (dualEndSpace k V)
            (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
            (isQuasicoherentPieces_of_isQuasicoherent _) ∧
        β.hom ≫ universalProductToParam k V =
          schemeProjectiveBundleToBase (constantModule k (dualEndSpace k V) V)
            (isQuasicoherentPieces_of_isQuasicoherent _) ∧
        IsOpenImmersion ((universalEndSheafDomain k V).ι ≫ α.hom) ∧
        (universalEndSheafProjection k V ≫ β.hom) ≫ universalProductToParam k V =
          ((universalEndSheafDomain k V).ι ≫ α.hom) ≫ universalProductToParam k V := by
  obtain ⟨α, hα⟩ := exists_iso_pullback_universalEndSource k V
  obtain ⟨β, hβ⟩ := exists_iso_pullback_universalEndTarget k V
  refine ⟨α, β, hα, hβ, inferInstance, ?_⟩
  rw [Category.assoc, hβ, Category.assoc, hα]
  exact universalEndSheafProjection_comp_toBase k V

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
