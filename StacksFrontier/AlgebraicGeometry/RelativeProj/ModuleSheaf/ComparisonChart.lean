module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonComp
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine

/-!
# The module comparison against the chart description of an inverse image

Let `X` be a scheme with two charts `f₂ : Proj 𝒜 ⟶ X` and `f₁ : Proj ℬ ⟶ X`, the second factoring
through the first by `AlgebraicGeometry.Proj.map` of a homomorphism `φ : 𝒜 ⟶ ℬ` of graded rings,
and let a sheaf of modules `N₀` on `X` restrict on the two charts to the sheaves of Tag 01M6 of
graded modules `𝒨` and `𝒩`, compatibly with `φ` — that is, the chart-refinement law holds.

Then a morphism `hm : Proj 𝒞 ⟶ X` factoring through *both* charts, by `Proj.map` of `χ : 𝒜 ⟶ 𝒞`
and of `ψ : ℬ ⟶ 𝒞` with `χ = ψ ∘ φ`, has one description of `hm^* N₀`, and the comparisons of the
chart sheaves with the sheaf of a graded module `𝒬` on `Proj 𝒞` agree on it.

This is the shape in which the glueing of a base-change comparison over a cover of charts needs the
composition law `Stacks.ProjModuleComparison.moduleMap_comp_of_eq`. Stating it at bare graded data
is not a stylistic choice: instantiating `moduleMap_comp_of_eq` *on its own* at the graded section
rings of a relative projective spectrum exceeds the kernel's budget, because its statement carries
three `Stacks.ProjModuleComparison.moduleMap`s together with the comparisons of the inverse image
along a composite. The conclusion below carries only two, and the third — along with every
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr` — stays inside this proof,
where the graded data are variables.

## Main results

* `Stacks.ProjModuleComparison.moduleMap_comp_pullbackChartDesc`: **the two chart descriptions of
  an inverse image, composed with the two chart comparisons, agree.**
* `Stacks.ProjModuleComparison.map_moduleMap_comp_eq`: the composition law of the chart
  comparisons, in the shape
  `AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` consumes.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

/-- Degrees of a graded ring act on degrees of a graded module over it by addition. This repeats
the local instance of
`StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/ComparisonComp.lean`, which is local to
that file; the two are the same definition, so the instance arguments of its lemmas are accepted
here. -/
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
  [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition 𝒬]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩] [SetLike.GradedSMul 𝒞 𝒬]

variable (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  (f : M →ₛₗ[φ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)
  (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  (f' : N →ₛₗ[ψ.toRingHom] P) (hf' : ∀ (i : ℤ) {n : N}, n ∈ 𝒩 i → f' n ∈ 𝒬 i)
  (χ : 𝒜 →+*ᵍ 𝒞) (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
  (fχ : M →ₛₗ[χ.toRingHom] P) (hfχ : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → fχ m ∈ 𝒬 i)

variable {X : Scheme.{u}} (f₂ : AlgebraicGeometry.Proj 𝒜 ⟶ X) [IsOpenImmersion f₂]
  {N₀ : X.Modules} (e₂ : N₀.restrict f₂ ≅ associatedModuleSheaf 𝒜 𝒨)
  {f₁ : AlgebraicGeometry.Proj ℬ ⟶ X} [IsOpenImmersion f₁]
  (hl : f₁ = AlgebraicGeometry.Proj.map φ hφ ≫ f₂)
  (e₁ : N₀.restrict f₁ ≅ associatedModuleSheaf ℬ 𝒩)
  (hν : (Scheme.Modules.pullbackIsoOfRestrictIso f₂ e₂
          (AlgebraicGeometry.Proj.map φ hφ) hl).hom ≫ moduleMap φ hφ f hf
      = (((Scheme.Modules.restrictFunctorIsoPullback f₁).app N₀).symm ≪≫ e₁).hom)
  {hm : AlgebraicGeometry.Proj 𝒞 ⟶ X}
  (hfac₂ : hm = AlgebraicGeometry.Proj.map χ hχ ≫ f₂)
  (hfac₁ : hm = AlgebraicGeometry.Proj.map ψ hψ ≫ f₁)

include hν in
/-- **The two chart descriptions of an inverse image, composed with the two chart comparisons,
agree.** The sheaf `N₀` is described on the chart `f₂` as the sheaf of `𝒨` and on the smaller chart
`f₁` as the sheaf of `𝒩`; pulled back along `hm`, either description followed by the comparison
with the sheaf of `𝒬` gives the same morphism.

The comparison `Stacks.ProjModuleComparison.moduleMap` of the sheaves of `𝒨` and `𝒩` across `φ`
occurs twice: in `hν`, the chart-refinement law, which
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine` turns into the relation between
the two chart descriptions pulled back along `hm`, and in
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq`, which relates the two chart comparisons. The
two relations are inverse to each other on it, so composing them gives the identity. -/
public theorem moduleMap_comp_pullbackChartDesc (hc : χ = ψ.comp φ)
    (hfc : ∀ m : M, fχ m = f' (f m)) :
    (Scheme.Modules.pullbackIsoOfRestrictIso f₂ e₂
          (AlgebraicGeometry.Proj.map χ hχ) hfac₂).hom ≫ moduleMap χ hχ fχ hfχ
      = (Scheme.Modules.pullbackIsoOfRestrictIso f₁ e₁
          (AlgebraicGeometry.Proj.map ψ hψ) hfac₁).hom ≫ moduleMap ψ hψ f' hf' := by
  have hmap := moduleMap_comp_of_eq φ hφ f hf ψ hψ f' hf' χ hχ fχ hfχ hc hfc
  have hiso := Scheme.Modules.pullbackIsoOfRestrictIso_refine f₂ e₂
    (AlgebraicGeometry.Proj.map φ hφ) hl e₁ (moduleMap φ hφ f hf) hν
    (AlgebraicGeometry.Proj.map ψ hψ) (projMapComp φ hφ ψ hψ χ hχ hc) hfac₂ hfac₁
  exact (whisker_eq _ hmap.symm).trans
    (((Category.assoc _ _ _).trans (whisker_eq _
        ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))))).symm.trans
      (eq_whisker hiso _))

/-! ### The composition law of the chart comparisons, as a glueing hypothesis -/

/-- **The two chart comparisons across `φ` and across `χ` are related by the comparisons of the
inverse image along a composite.** This is
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq` solved for the inverse image along `Proj.map ψ`
of the comparison across `φ`, which is the hypothesis `hmm` of
`AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` -- the nested case of a glueing of chart
members over a cover whose charts shrink. -/
public theorem map_moduleMap_comp_eq (hc : χ = ψ.comp φ) (hfc : ∀ m : M, fχ m = f' (f m)) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map (moduleMap φ hφ f hf)
        ≫ moduleMap ψ hψ f' hf'
      = (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ)
            (AlgebraicGeometry.Proj.map φ hφ)).hom.app (associatedModuleSheaf 𝒜 𝒨)
        ≫ (Scheme.Modules.pullbackCongr (projMapComp φ hφ ψ hψ χ hχ hc)).hom.app
            (associatedModuleSheaf 𝒜 𝒨)
        ≫ moduleMap χ hχ fχ hfχ :=
  (((whisker_eq _ (whisker_eq _
      (moduleMap_comp_of_eq φ hφ f hf ψ hψ f' hf' χ hχ fχ hfχ hc hfc).symm)).trans
    (whisker_eq _ (Iso.hom_inv_id_app_assoc _ _ _))).trans
    (Iso.hom_inv_id_app_assoc _ _ _)).symm

/-! ### The nested case for the chart comparisons -/

section MemberNested

variable {X' Y : Scheme.{u}} {M₀ : Y.Modules} (r : X' ⟶ Y)
  (d : AlgebraicGeometry.Proj 𝒜 ⟶ Y) [IsOpenImmersion d]
  (eB : M₀.restrict d ≅ associatedModuleSheaf 𝒜 𝒨)
  {N' : X'.Modules}
  (c₂ : AlgebraicGeometry.Proj ℬ ⟶ X') [IsOpenImmersion c₂]
  (e'₂ : N'.restrict c₂ ≅ associatedModuleSheaf ℬ 𝒩)
  {c₁ : AlgebraicGeometry.Proj 𝒞 ⟶ X'} [IsOpenImmersion c₁]
  (hkc : AlgebraicGeometry.Proj.map ψ hψ ≫ c₂ = c₁)
  (e'₁ : N'.restrict c₁ ≅ associatedModuleSheaf 𝒞 𝒬)
  (hfac₂ : c₂ ≫ r = AlgebraicGeometry.Proj.map φ hφ ≫ d)
  (hfac₁ : c₁ ≫ r = AlgebraicGeometry.Proj.map χ hχ ≫ d)

include hkc in
/-- **The chart member of a comparison over a smaller chart of `X'` is the inverse image of the one
over the larger chart**, when the chart sheaves are the sheaves of Tag 01M6 and the comparisons are
`Stacks.ProjModuleComparison.moduleMap`.

This is `AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` with its hypothesis `hmm`
discharged by `Stacks.ProjModuleComparison.map_moduleMap_comp_eq`. Stating the instance here, at
bare graded data, is what keeps it checkable: the hypothesis `hmm` carries three `moduleMap`s and
cannot be stated at the graded section rings of a relative projective spectrum, while this
conclusion carries two. -/
public theorem moduleMap_chartMember_pullback_eq
    (hν : (Scheme.Modules.pullbackIsoOfRestrictIso c₂ e'₂
          (AlgebraicGeometry.Proj.map ψ hψ) hkc.symm).hom ≫ moduleMap ψ hψ f' hf'
      = (((Scheme.Modules.restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom)
    (hc : χ = ψ.comp φ) (hfc : ∀ m : M, fχ m = f' (f m)) :
    (Scheme.Modules.pullbackCongr hkc).inv.app ((Scheme.Modules.pullback r).obj M₀)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ) c₂).inv.app
            ((Scheme.Modules.pullback r).obj M₀)
        ≫ (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
            ((Scheme.Modules.pullbackComp c₂ r).hom.app M₀
              ≫ (Scheme.Modules.pullbackIsoOfRestrictIso d eB
                  (AlgebraicGeometry.Proj.map φ hφ) hfac₂).hom
              ≫ moduleMap φ hφ f hf
              ≫ (((Scheme.Modules.restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ) c₂).hom.app N'
        ≫ (Scheme.Modules.pullbackCongr hkc).hom.app N'
      = (Scheme.Modules.pullbackComp c₁ r).hom.app M₀
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso d eB
            (AlgebraicGeometry.Proj.map χ hχ) hfac₁).hom
        ≫ moduleMap χ hχ fχ hfχ
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).inv :=
  Scheme.Modules.chartMember_pullback_eq r d eB c₂ e'₂
    (AlgebraicGeometry.Proj.map ψ hψ) hkc e'₁
    (AlgebraicGeometry.Proj.map φ hφ) hfac₂ (projMapComp φ hφ ψ hψ χ hχ hc) hfac₁
    (moduleMap φ hφ f hf) (moduleMap χ hχ fχ hfχ) (moduleMap ψ hψ f' hf')
    hν (map_moduleMap_comp_eq φ hφ f hf ψ hψ f' hf' χ hχ fχ hfχ hc hfc)

end MemberNested

end Stacks.ProjModuleComparison

end
