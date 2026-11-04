module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonComp
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Functorial

/-!
# Functoriality of the twist comparison across a composite of homogeneous spectra

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings whose
irrelevant ideals satisfy the hypotheses making `AlgebraicGeometry.Proj.map` defined, and let `χ`
be a third homomorphism *equal* to `ψ.comp φ`. Tag 01MY attaches to each of the three a comparison
`θ n : (Proj.map ·)^* 𝒪(n) ⟶ 𝒪(n)` of twisting sheaves,
`Stacks.ProjTwistComparison.twistMap`.

This file proves that **those three comparisons compose**, as an identity of morphisms of sheaves
of modules. It is the twist counterpart of
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq`, and the proof is the same one: the comparison
of inverse images is defined as an adjoint transpose and has no description on sections, so the
identity is proved on the other side of the adjunction, where the comparison is
`Stacks.ProjTwistComparison.pushforwardTwistMap`, explicit on sections; there it is pointwise in
the module fibres, and in a fibre it is `Stacks.ProjTwistComparison.fibreMap_comp`, which is
`Localization.localRingHom_comp`. The step back across the adjunction is
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` with the composite left as the
unknown, and `Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective` recovers the identity of
inverse images from the identity of the transposes.

Unlike the module case there is no semilinear map to carry: the twisting sheaf of a graded ring is
the sheaf of the ring itself with its grading shifted, and the comparison is induced by `φ` alone.
So the factorization is presented by the single equation `hc : χ = ψ.comp φ`, with no companion
equation on module maps.

## Main results

* `Stacks.ProjTwistComparison.transpose_twistMap`: the adjoint transpose of the comparison is the
  explicit comparison on sections. This is `Stacks.ProjTwistComparison.homEquiv_twistMap` in the
  spelling `Stacks.AlgebraicGeometry.PushforwardCocycle.transpose` uses.
* `Stacks.ProjTwistComparison.pushforwardTwistMap_comp_of_eq`: **the comparisons on sections
  compose.**
* `Stacks.ProjTwistComparison.twistMap_comp_of_eq`: **the comparisons of inverse images
  compose**, in the cocycle shape — the inverse image along the first `Proj.map` of the second
  comparison followed by the first, transported along the two pullback comparisons, is the
  comparison for the composite.

## Implementation notes

`AlgebraicGeometry.Proj.map` of a homomorphism presented as a composite is the composite of the
two, which is `Stacks.ProjModuleComparison.projMapComp`; that statement mentions no module and no
twist, so it is reused rather than restated here, which is why this file imports the module
chain's `ComparisonComp`.

The three transposes are replaced by a chain of `Eq.trans` with `CategoryTheory.whisker_eq` and
`CategoryTheory.eq_whisker`, not by `rw`, for the reason recorded in the module file:
`AlgebraicGeometry.Scheme.Modules` is a `def`, and a rewrite on a goal mentioning a pushforward of
a twisting sheaf leaves the term type-incorrect at the transparency `rw` matches with.

## Not done here

No tag is claimed: this is the functoriality of a comparison morphism, not a clause of a tag.
Compatibility of `θ` with the multiplication maps `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` — clause (4) of Tag
01NO — is a different statement and is not treated.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B C : Type u} {σ τ ρ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (n : ℤ)

/-- **The adjoint transpose of the comparison of inverse images is the comparison on sections.**
This is `Stacks.ProjTwistComparison.homEquiv_twistMap` written with
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose`, the spelling the composition law of the
transposes is stated at. -/
public theorem transpose_twistMap :
    Stacks.AlgebraicGeometry.PushforwardCocycle.transpose (AlgebraicGeometry.Proj.map φ hφ)
        (twistingSheaf 𝒜 n) (twistMap φ hφ n)
      = pushforwardTwistMap φ hφ n :=
  (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_eq_homEquiv _ _ _).trans
    (homEquiv_twistMap φ hφ n)

/-- **The comparisons on sections compose.** Comparing the sections of `𝒪_{Proj 𝒜}(n)` with those
of `𝒪_{Proj 𝒞}(n)` across the composite is comparing them with those of `𝒪_{Proj ℬ}(n)` and then,
over the preimage, with those of `𝒪_{Proj 𝒞}(n)`.

Both sides are morphisms between pushforwards, so this is checked on sections over an open of
`Proj 𝒜` and then pointwise in the module fibres, where it is
`Stacks.ProjTwistComparison.fibreMap_comp`. The congruence isomorphism of the pushforward along
the identification `Stacks.ProjModuleComparison.projMapComp` of the two spellings of the composite
is a restriction along an equality of opens, and on a family of fractions indexed by the points of
an open that restriction is a re-indexing, so it does not appear in the fibre identity. -/
public theorem pushforwardTwistMap_comp_of_eq (hc : χ = ψ.comp φ) :
    pushforwardTwistMap φ hφ n
        ≫ (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map
            (pushforwardTwistMap ψ hψ n)
        ≫ (Scheme.Modules.pushforwardCongr
            (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc)).hom.app
            (twistingSheaf 𝒞 n)
      = pushforwardTwistMap χ hχ n := by
  subst hc
  ext U a
  refine Subtype.ext (funext fun y => ?_)
  exact (fibreMap_comp φ hφ ψ hψ hχ y.1 _).symm

/-- **The comparisons of inverse images compose.** The inverse image along the first `Proj.map` of
the second comparison, followed by the first comparison, is the comparison attached to the
composite, once the two inverse images of `𝒪_{Proj 𝒜}(n)` are identified: along the
pseudofunctoriality comparison of the inverse image for the two `Proj.map`s, and along the
congruence comparison for the identification
`Stacks.ProjModuleComparison.projMapComp` of their composite with the `Proj.map` of the composite.

This is the cocycle shape that
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes, and it is
proved on the other side of the adjunction: the three comparisons have the explicit transposes
`Stacks.ProjTwistComparison.transpose_twistMap`, those compose by
`Stacks.ProjTwistComparison.pushforwardTwistMap_comp_of_eq`, and
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` with the composite left as the
unknown identifies the left-hand side's transpose with that composite of transposes. -/
public theorem twistMap_comp_of_eq (hc : χ = ψ.comp φ) :
    (Scheme.Modules.pullbackCongr
            (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc)).inv.app
          (twistingSheaf 𝒜 n)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ)
            (AlgebraicGeometry.Proj.map φ hφ)).inv.app (twistingSheaf 𝒜 n)
        ≫ (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map (twistMap φ hφ n)
        ≫ twistMap ψ hψ n
      = twistMap χ hχ n := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective _ _ ?_
  refine ((Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle
    (AlgebraicGeometry.Proj.map ψ hψ) (AlgebraicGeometry.Proj.map φ hφ)
    (AlgebraicGeometry.Proj.map χ hχ)
    (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc) _ _ _
    (twistMap φ hφ n) (twistMap ψ hψ n) _ rfl).symm).trans ?_
  refine Eq.trans (eq_whisker (transpose_twistMap φ hφ n) _) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map z)
    (transpose_twistMap ψ hψ n)) _)) ?_
  exact (pushforwardTwistMap_comp_of_eq φ hφ ψ hψ hχ n hc).trans
    (transpose_twistMap χ hχ n).symm

end Stacks.ProjTwistComparison

end
