module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Local
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist

/-!
# Functoriality of the module comparison across a composite of homogeneous spectra

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings whose
irrelevant ideals satisfy the hypotheses making `AlgebraicGeometry.Proj.map` defined, let `χ` be
a third homomorphism *equal* to `ψ.comp φ`, and let `f`, `f'`, `fχ` be semilinear maps of graded
modules over them with `fχ` pointwise the composite of `f'` and `f`.
`Stacks.ProjModuleComparison.moduleMap` of
`StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/Comparison.lean` attaches to each of the
three a comparison `(Proj.map ·)^* M̃ ⟶ ·̃` of associated module sheaves.

This file proves that **those three comparisons compose**, as an identity of morphisms of sheaves
of modules.

The comparison for the composite is defined as an adjoint transpose and has no description on
sections: the inverse image of a sheaf of modules is a sheafification of a tensor product. So the
identity is proved on the *other* side of the adjunction, where the comparison is
`Stacks.ProjModuleComparison.pushforwardModuleMap`, written down explicitly on sections, and the
sections of a pushforward are the sections of its argument over the preimage of the open. There
the identity is pointwise in the module fibres, and in a fibre it is
`Stacks.ProjModuleComparison.fibreMap_comp`. The step back across the adjunction is
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle`, which turns a cocycle condition
on morphisms of inverse images into one on their transposes, read in the direction its docstring
leaves open: with the composite put in as the unknown it computes the transpose of the composite,
and `Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective` recovers the identity of inverse
images from the identity of the transposes.

## Main results

* `Stacks.ProjModuleComparison.projMapComp`: `AlgebraicGeometry.Proj.map` of a homomorphism equal
  to a composite is the composite of the two `Proj.map`s.
* `Stacks.ProjModuleComparison.transpose_moduleMap`: the adjoint transpose of the comparison is
  the explicit comparison on sections. This is
  `Stacks.ProjModuleComparison.homEquiv_moduleMap` in the spelling
  `Stacks.AlgebraicGeometry.PushforwardCocycle.transpose` uses.
* `Stacks.ProjModuleComparison.pushforwardModuleMap_comp_of_eq`: **the comparisons on sections
  compose.**
* `Stacks.ProjModuleComparison.moduleMap_comp_of_eq`: **the comparisons of inverse images
  compose**, in the cocycle shape — the inverse image along the first `Proj.map` of the second
  comparison followed by the first, transported along the two pullback comparisons, is the
  comparison for the composite.

## Implementation notes

A factorization is presented by two equations, `hc : χ = ψ.comp φ` and
`hfc : ∀ m, fχ m = f' (f m)`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/Local.lean`: the composite of a
`φ`-semilinear and a `ψ`-semilinear map is `ψ.comp φ`-semilinear only through a
`RingHomCompTriple`, so `fχ` and the composite do not have the same type before `hc` is
substituted away. This is also what a base change of graded modules of sections supplies.

`projMapComp` is proved from `AlgebraicGeometry.Proj.map_comp` and proof irrelevance in the
irrelevant-ideal hypothesis, applied through `congrArg` rather than by `rfl`: the two sides differ
only in a proof of a proposition, but asking the elaborator for that by `rfl` unfolds
`AlgebraicGeometry.Proj.map` and reaches the deterministic `whnf` timeout.

In `moduleMap_comp_of_eq` the three transposes are replaced by a chain of `Eq.trans` with
`CategoryTheory.whisker_eq` and `CategoryTheory.eq_whisker`, not by `rw`, for the reason recorded
throughout `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/`:
`AlgebraicGeometry.Scheme.Modules` is a `def`, and a rewrite on a goal mentioning a pushforward of
an associated module sheaf leaves the term type-incorrect at the transparency `rw` matches with.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No tag is claimed: this is the functoriality of a comparison morphism, not a clause of a tag.

The composition law here is one of the three identities
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeGlue.lean`
records
as standing between the chart-level base-change comparison of `ℳ̃` and its glueing; the other two
are refinement laws for `Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso` and for
`Stacks.RelativeProj.Situation.moduleSheafChartIso`, and neither is proved here. All three are now
in place, and property (8) of Tag 01O7 is assembled from them in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeGlued.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

/-- Degrees of a graded ring act on degrees of a graded module over it by addition. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {A B C M N P : Type u} {σ τ ρ μ ν π : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  [SetLike π P] [AddSubgroupClass π P]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} {𝒬 : ℤ → π}
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩] [SetLike.GradedSMul 𝒞 𝒬]

/-- **`AlgebraicGeometry.Proj.map` of a homomorphism of graded rings equal to a composite is the
composite of the two morphisms of homogeneous spectra.** This is
`AlgebraicGeometry.Proj.map_comp` with the homomorphism of the composite and its irrelevant-ideal
hypothesis free arguments, which is the shape the comparisons below are stated at. -/
public theorem projMapComp (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
    (χ : 𝒜 →+*ᵍ 𝒞) (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hc : χ = ψ.comp φ) :
    AlgebraicGeometry.Proj.map ψ hψ ≫ AlgebraicGeometry.Proj.map φ hφ
      = AlgebraicGeometry.Proj.map χ hχ := by
  subst hc
  exact (AlgebraicGeometry.Proj.map_comp φ ψ hφ hψ).symm.trans
    (congrArg (AlgebraicGeometry.Proj.map (ψ.comp φ)) (proof_irrel _ hχ))

variable (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  (f : M →ₛₗ[φ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)
  (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  (f' : N →ₛₗ[ψ.toRingHom] P) (hf' : ∀ (i : ℤ) {n : N}, n ∈ 𝒩 i → f' n ∈ 𝒬 i)
  (χ : 𝒜 →+*ᵍ 𝒞) (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
  (fχ : M →ₛₗ[χ.toRingHom] P) (hfχ : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → fχ m ∈ 𝒬 i)

/-- **The adjoint transpose of the comparison of inverse images is the comparison on sections.**
This is `Stacks.ProjModuleComparison.homEquiv_moduleMap` written with
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose`, the spelling the composition law of the
transposes is stated at. -/
public theorem transpose_moduleMap :
    Stacks.AlgebraicGeometry.PushforwardCocycle.transpose (AlgebraicGeometry.Proj.map φ hφ)
        (associatedModuleSheaf 𝒜 𝒨) (moduleMap φ hφ f hf)
      = pushforwardModuleMap φ hφ f hf :=
  (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_eq_homEquiv _ _ _).trans
    (homEquiv_moduleMap φ hφ f hf)

/-- **The comparisons on sections compose.** Comparing the sections of `M̃` with those of `Q̃`
across the composite is comparing them with those of `Ñ` and then, over the preimage, with those
of `Q̃`.

Both sides are morphisms between pushforwards, so this is checked on sections over an open of
`Proj 𝒜` and then pointwise in the module fibres, where it is
`Stacks.ProjModuleComparison.fibreMap_comp`. The congruence isomorphism of the pushforward along
the identification `Stacks.ProjModuleComparison.projMapComp` of the two spellings of the composite
is a restriction along an equality of opens, and on a family of fractions indexed by the points of
an open that restriction is a re-indexing, so it does not appear in the fibre identity. -/
public theorem pushforwardModuleMap_comp_of_eq (hc : χ = ψ.comp φ)
    (hfc : ∀ m : M, fχ m = f' (f m)) :
    pushforwardModuleMap φ hφ f hf
        ≫ (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map
            (pushforwardModuleMap ψ hψ f' hf')
        ≫ (Scheme.Modules.pushforwardCongr (projMapComp φ hφ ψ hψ χ hχ hc)).hom.app
            (associatedModuleSheaf 𝒞 𝒬)
      = pushforwardModuleMap χ hχ fχ hfχ := by
  subst hc
  ext U a
  refine Subtype.ext (funext fun y => ?_)
  exact (fibreMap_comp φ hφ f ψ hψ f' hχ fχ hfc y.1 _).symm

/-- **The comparisons of inverse images compose.** The inverse image along the first `Proj.map` of
the second comparison, followed by the first comparison, is the comparison attached to the
composite, once the two inverse images of `M̃` are identified: along the pseudofunctoriality
comparison of the inverse image for the two `Proj.map`s, and along the congruence comparison for
the identification `Stacks.ProjModuleComparison.projMapComp` of their composite with the
`Proj.map` of the composite.

This is the cocycle shape that
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes, and it is
proved on the other side of the adjunction: the three comparisons have the explicit transposes
`Stacks.ProjModuleComparison.transpose_moduleMap`, those compose by
`Stacks.ProjModuleComparison.pushforwardModuleMap_comp_of_eq`, and
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` with the composite left as the
unknown identifies the left-hand side's transpose with that composite of transposes. -/
public theorem moduleMap_comp_of_eq (hc : χ = ψ.comp φ) (hfc : ∀ m : M, fχ m = f' (f m)) :
    (Scheme.Modules.pullbackCongr (projMapComp φ hφ ψ hψ χ hχ hc)).inv.app
          (associatedModuleSheaf 𝒜 𝒨)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ)
            (AlgebraicGeometry.Proj.map φ hφ)).inv.app (associatedModuleSheaf 𝒜 𝒨)
        ≫ (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map (moduleMap φ hφ f hf)
        ≫ moduleMap ψ hψ f' hf'
      = moduleMap χ hχ fχ hfχ := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective _ _ ?_
  refine ((Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle
    (AlgebraicGeometry.Proj.map ψ hψ) (AlgebraicGeometry.Proj.map φ hφ)
    (AlgebraicGeometry.Proj.map χ hχ) (projMapComp φ hφ ψ hψ χ hχ hc) _ _ _
    (moduleMap φ hφ f hf) (moduleMap ψ hψ f' hf') _ rfl).symm).trans ?_
  refine Eq.trans (eq_whisker (transpose_moduleMap φ hφ f hf) _) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map z)
    (transpose_moduleMap ψ hψ f' hf')) _)) ?_
  exact (pushforwardModuleMap_comp_of_eq φ hφ f hf ψ hψ f' hf' χ hχ fχ hfχ hc hfc).trans
    (transpose_moduleMap χ hχ fχ hfχ).symm

end Stacks.ProjModuleComparison

end
