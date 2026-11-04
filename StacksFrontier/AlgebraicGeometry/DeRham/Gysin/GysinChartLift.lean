module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Globalisation
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# Lifting a relative form from the closed subscheme to the ambient scheme

Let `i : Z ⟶ X` be a closed immersion and `π : X ⟶ S` a morphism of schemes. The restriction
`ω̃ ↦ ω̃|_Z` of relative differential forms, which is `Stacks.Gysin.subschemeFormPullback` on
sections, is surjective in a sense made precise here. This discharges the field
`Stacks.Gysin.ChartComparison.lift` of the chart comparisons of [Stacks, Tag 0G86]: that field is
**not** an assumption about the geometry but a consequence of `i` being a closed immersion, and
this file proves it.

Two forms are given, because the field asks for a lift over the open itself while surjectivity of
a map of sheaves is in general only local.

* Over an **affine** open the lift exists over the open itself. Both sheaves are quasi-coherent —
  `Ω^p_{X/S}` by `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms` and
  `i_*Ω^p_{Z/S}` by `Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom`, a closed
  immersion being affine — and `Γ(V, -)` is exact on quasi-coherent modules over an affine open,
  which is `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`.
* Over an arbitrary open the lift exists after shrinking around any given point, with no
  hypothesis at all, because an epimorphism of sheaves of modules is locally surjective.

The affine form is the one to use: `Stacks.Gysin.GysinChartData.comparison` asks for the
comparisons over a *covering* of each overlap, and the affine opens of a scheme are a basis, so
that covering may always be taken to consist of affine opens — `Stacks.Gysin.exists_affine_cover`
says exactly that, so the restriction to affine opens costs nothing.

## Main results

* `Stacks.Gysin.subschemeFormPullback_eq_formRestriction_app`: restriction of forms to the closed
  subscheme on sections is the morphism `AlgebraicGeometry.Scheme.Hom.formRestriction` of sheaves
  evaluated on sections. This holds by `rfl`; it is what connects
  `Stacks.Gysin.subschemeFormPullback`, defined through
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback`, to the epimorphism
  `AlgebraicGeometry.Scheme.Hom.epi_formRestriction`.
* `Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`: **the `lift` field of
  `Stacks.Gysin.ChartComparison`, proved, over an affine open.**
* `Stacks.Gysin.exists_subschemeFormPullback_restrict`: the same with no hypothesis on the open,
  after shrinking around a point.
* `Stacks.Gysin.exists_affine_cover`: every open of a scheme is covered by affine opens contained
  in it, in the shape `Stacks.Gysin.GysinChartData.comparison` asks its coverings to take.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Limits

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-- Restriction of an ambient relative differential form to the closed subscheme, on sections
over an open `V`, is the morphism `AlgebraicGeometry.Scheme.Hom.formRestriction` of sheaves of
modules read on the sections over `V`. Both are the unit of `i^* ⊣ i_*` followed by the canonical
comparison `i^*Ω^n_{X/S} ⟶ Ω^n_{Z/S}`, so this is a definitional identity; it is stated because
it is what lets the surjectivity of `formRestriction` be read on sections. -/
theorem subschemeFormPullback_eq_formRestriction_app (i : Z ⟶ X) (π : X ⟶ S) (n : ℤ)
    (V : X.Opens) (ω : Γ(relativeDifferentialForms π n, V)) :
    subschemeFormPullback i π n V ω = (formRestriction i π n).val.app (op V) ω :=
  rfl

/-- **Every relative `p`-form on the closed subscheme over the preimage of an affine open is the
restriction of an ambient `p`-form over that open.** This is the field
`Stacks.Gysin.ChartComparison.lift` of the chart comparisons of [Stacks, Tag 0G86], proved rather
than assumed, for an affine open.

Restriction of `p`-forms to a closed subscheme is an epimorphism of sheaves of modules, by
`AlgebraicGeometry.Scheme.Hom.epi_formRestriction` — that is [Stacks, Tag 08KS] for the unit of
`i^* ⊣ i_*` together with surjectivity of `i^*Ω^p_{X/S} ⟶ Ω^p_{Z/S}`. Taking sections over an
affine open is exact on quasi-coherent modules, and both modules here are quasi-coherent: the
ambient forms by `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`, and
their direct image along `i` by `Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom`,
a closed immersion being an affine morphism. -/
theorem exists_subschemeFormPullback_of_isAffineOpen (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) (p : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    ∃ ω, subschemeFormPullback i π (p : ℤ) V ω = x := by
  have : Epi (formRestriction i π (p : ℤ)) := epi_formRestriction i π p
  have : (relativeDifferentialForms π (p : ℤ)).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms π p
  have : (relativeDifferentialForms (i ≫ π) (p : ℤ)).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms (i ≫ π) p
  have : (pushforwardRelativeForms i π (p : ℤ)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom i
      (relativeDifferentialForms (i ≫ π) (p : ℤ)) inferInstance
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
    (formRestriction i π (p : ℤ)) V hV x

/-- **A relative `p`-form on the closed subscheme is, near every point, the restriction of an
ambient one.** The unconditional form of `exists_subschemeFormPullback_of_isAffineOpen`: no
affineness and no quasi-coherence, at the price of shrinking the open. Restriction of `p`-forms
is an epimorphism of sheaves of modules by
`AlgebraicGeometry.Scheme.Hom.epi_formRestriction`, and an epimorphism of sheaves of modules is
locally surjective on sections by
`Stacks.SheafOfModules.EpiMono.epi_toSheaf_map` and
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`. -/
theorem exists_subschemeFormPullback_restrict (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (p : ℕ) (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) (z : X) (hz : z ∈ V) :
    ∃ (W : X.Opens) (hWV : W ≤ V), z ∈ W ∧ ∃ ω : Γ(relativeDifferentialForms π (p : ℤ), W),
      subschemeFormPullback i π (p : ℤ) W ω =
        (pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hWV).op x := by
  have : Epi (C := SheafOfModules.{u} X.ringCatSheaf) (formRestriction i π (p : ℤ)) :=
    epi_formRestriction i π p
  have hepi : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map (formRestriction i π (p : ℤ))) :=
    Stacks.SheafOfModules.EpiMono.epi_toSheaf_map (formRestriction i π (p : ℤ))
  have hsurj : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (formRestriction i π (p : ℤ))).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  obtain ⟨W, hWV, ⟨ω, hω⟩, hzW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hsurj V x z hz
  exact ⟨W, hWV, hzW, ω, hω⟩

/-- **Every open of a scheme is covered by the affine opens contained in it**, in the shape the
coverings of `Stacks.Gysin.GysinChartData.comparison` are asked to take. This is why restricting
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen` to affine opens costs nothing: a
comparison required over *some* covering of each overlap may always be required over a covering
by affine opens. -/
theorem exists_affine_cover (V : X.Opens) :
    ∃ (J : Type u) (V' : J → X.Opens) (hle : ∀ k, V' k ≤ V),
      (∀ k, IsAffineOpen (V' k)) ∧ V ≤ ⨆ k, V' k := by
  refine ⟨{ W : X.affineOpens // W.1 ≤ V }, fun k => k.1.1, fun k => k.2,
    fun k => k.1.2, fun z hz => ?_⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hzW⟩

end Stacks.Gysin

end
