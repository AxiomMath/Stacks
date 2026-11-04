module

public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections

/-!
# Projective sections of the structure sheaf along a fibre

Stacks Tag 05KX is the case `ℱ = 𝒪_X` of Tag 05KW: for `f : X ⟶ S` of finite presentation and
`s : S` such that `X` is flat over `S` at every point of the fibre `X_s`, there are an elementary
étale neighbourhood `(S', s') ⟶ (S, s)` and a commutative square
```
  X  ←ᵍ  X'
  ↓      ↓
  S  ←   S'
```
with `g` étale, `X_s ⊆ g(X')`, with `X'` and `S'` affine, and with `Γ(X', 𝒪_{X'})` a projective
`Γ(S', 𝒪_{S'})`-module. The source proof is the single sentence "This is a special case of
Lemma 05KW".

That specialisation is not vacuous in Lean, because the two tags speak about different objects:
Tag 05KW constrains a *module* — its hypothesis is Tag 08KT, flatness of `ℱ` over `S` at a point,
and its conclusion is projectivity of `Γ(X', g^*ℱ)` — whereas Tag 05KX constrains the *morphism*,
with Tag 02N3 flatness as hypothesis and `Γ(X', 𝒪_{X'})` in the conclusion. The three bridges
needed are the same ones that make Tag 05IE the case `ℱ = 𝒪_X` of Tag 05ID, and are reused from
`StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections`:
`AlgebraicGeometry.Scheme.unitModule X` is quasi-coherent and of finite presentation, so Tag 05KW
applies to it; `AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt` converts flatness of `f` at a
point into flatness of the structure sheaf over `S` at that point; and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv` identifies `Γ(X', g^*𝒪_X)` with
`Γ(X', 𝒪_{X'})`, compatibly with the restriction of scalars along `Γ(S', 𝒪_{S'}) ⟶ Γ(X', 𝒪_{X'})`
that both sides carry.

## What is proved

Every clause of Tag 05KX: the square, its commutativity, elementariness of `(S', s')`,
affineness of `X'` and of `S'`, étaleness of `g`, the inclusion `X_s ⊆ g(X')`, and projectivity
of the global sections. The hypotheses are the source's and only the source's: `f` of finite
presentation and `f` flat at every point of `X_s`. Nothing is assumed beyond them, because the
Tag 05KW used here,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre`, is itself
unconditional.

## Main results

* `exists_elementaryEtaleNeighborhood_projective_structureSheafSections_along_fibre`, in the
  `AlgebraicGeometry` namespace: **Tag 05KX**, the case `ℱ = 𝒪_X` of Tag 05KW.

## Implementation notes

The fibre is indexed by `AlgebraicGeometry.Scheme.Hom.fiber`, as in Tag 05KW, so "flat at every
point of `X_s`" reads as a hypothesis over `f.fiber s` transported to `X` along
`AlgebraicGeometry.Scheme.Hom.fiberι`; the conclusion's inclusion is stated on the preimage
`f ⁻¹' {s}`, which is the same set.

The `Γ(S', 𝒪_{S'})`-linear identification of the sections is assembled from the
`Γ(X', 𝒪_{X'})`-linear one by restriction of scalars along `h.appTop`, as in Tag 05IE: the
underlying additive equivalence is shared and only the `map_smul'` field is rebuilt.

## References

* [Stacks Project, Tag 05KX](https://stacks.math.columbia.edu/tag/05KX)
* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
* [Stacks Project, Tag 05IE](https://stacks.math.columbia.edu/tag/05IE)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05KX.** Let `f : X ⟶ S` be of finite presentation and let `s : S` be a
point at which `X` is flat over `S` at every point of the fibre `X_s`. Then there are an
elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a commutative square
```
  X  ←ᵍ  X'
  ↓      ↓
  S  ←   S'
```
with `g` étale, `X_s ⊆ g(X')`, with `X'` and `S'` affine, and with `Γ(X', 𝒪_{X'})` a projective
`Γ(S', 𝒪_{S'})`-module.

This is the case `ℱ = 𝒪_X` of Tag 05KW, as in the source. The flatness hypothesis is converted
from the morphism to the structure sheaf by
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`, and the conclusion is converted back from
`Γ(X', g^*𝒪_X)` to `Γ(X', 𝒪_{X'})` by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv`; the finite presentation of
`𝒪_X` as a module, which Tag 05KW requires of `ℱ`, is
`AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`. Tag 05KW enters as
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre`, which is
unconditional, so nothing is assumed here beyond the source's hypotheses. -/
@[stacks 05KX]
theorem exists_elementaryEtaleNeighborhood_projective_structureSheafSections_along_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (hf : FinitePresentation f)
    (hflat : ∀ x : f.fiber s, IsFlatAt f.toLRSHom.toShHom (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (X' : Scheme.{u})
      (h : X' ⟶ U.scheme) (g : X' ⟶ X),
      U.IsElementary ∧ IsAffine U.scheme ∧ IsAffine X' ∧ Etale g ∧
      g ≫ f = h ≫ U.toBase ∧
      f ⁻¹' {s} ⊆ Set.range g ∧
      (letI : Module Γ(U.scheme, ⊤) Γ(X', ⊤) := Module.compHom Γ(X', ⊤) h.appTop.hom
       Module.Projective Γ(U.scheme, ⊤) Γ(X', ⊤)) := by
  obtain ⟨U, X', h, g, hUel, hUaff, hX'aff, hg, hcomm, hcover, hproj⟩ :=
    exists_elementaryEtaleNeighborhood_projective_sections_along_fibre f
      (Scheme.unitModule X) s hf
      (fun x => (isFlatOverAt_unit_iff_isFlatAt f (f.fiberι s x)).mpr (hflat x))
  refine ⟨U, X', h, g, hUel, hUaff, hX'aff, hg, hcomm, hcover, ?_⟩
  let _ := hUaff
  let _ := hX'aff
  -- `Γ(X', g^*𝒪_X) = Γ(X', 𝒪_{X'})`, over `Γ(X', 𝒪_{X'})` and hence over `Γ(S', 𝒪_{S'})`.
  let eX : Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤)
      ≃ₗ[Γ(X', ⊤)] Γ(X', ⊤) :=
    Scheme.Modules.pullbackUnitSectionsLinearEquiv g
  let : Module Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤) :=
    Module.compHom _ h.appTop.hom
  let : Module Γ(U.scheme, ⊤) Γ(X', ⊤) := Module.compHom Γ(X', ⊤) h.appTop.hom
  let : Module.Projective Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤) := hproj
  let eU : Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤)
      ≃ₗ[Γ(U.scheme, ⊤)] Γ(X', ⊤) :=
    { eX.toAddEquiv with map_smul' := fun r m => eX.map_smul (h.appTop.hom r) m }
  exact Module.Projective.of_equiv' eU

end AlgebraicGeometry

end
