module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites

/-!
# The locally Noetherian objects of a big site

Let `S` be a locally Noetherian scheme and let `τ` be one of the five topologies Zariski, étale,
smooth, syntomic and fppf. Stacks 0GE1 sets up the full subcategory `(Noetherian/S)` of
`(Sch/S)` on the objects whose underlying scheme is locally Noetherian, and records the facts
that make it a site for the coverings of `(Sch/S)_τ` whose objects are all locally Noetherian.
This file proves parts (1), (2) and (3) of that list, uniformly in `τ`.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_of_locallyOfFiniteType_over`: a morphism of the big site
  over `S` that is locally of finite type and has locally Noetherian target has locally
  Noetherian source.
* `AlgebraicGeometry.isLocallyNoetherian_of_isPullback_over`: the vertex of a fibre product
  square along a morphism locally of finite type with locally Noetherian corner is locally
  Noetherian.
* `AlgebraicGeometry.isLocallyNoetherian_of_mem_precoverage`,
  `AlgebraicGeometry.isLocallyNoetherian_of_isCovering`,
  `AlgebraicGeometry.isLocallyNoetherian_of_isCovering_bigFppfOver`: the members of a covering
  family with locally Noetherian target are locally Noetherian, for a covering family of
  schemes, for a covering family of a big site, and for a covering family of the big fppf site
  over `S`.
* `AlgebraicGeometry.coveringMorphismProperty_le_locallyOfFiniteType`: the morphisms of a
  covering family of any of the five topologies are locally of finite type.

## References

* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {τ : CoveringTopology}

/-- Every morphism of a covering family of one of the five topologies Zariski, étale, smooth,
syntomic and fppf is locally of finite type. -/
public theorem coveringMorphismProperty_le_locallyOfFiniteType (τ : CoveringTopology) :
    coveringMorphismProperty.{u} τ ≤ @LocallyOfFiniteType := by
  intro X Y f hf
  cases τ with
  | fppf => have := hf.2; infer_instance
  | syntomic => have := AlgebraicGeometry.locallyOfFinitePresentation hf; infer_instance
  | smooth => have := hf; infer_instance
  | etale => have := hf; infer_instance
  | zariski => have := hf; infer_instance

/-- The source of a morphism of a covering family is locally Noetherian if its target is. -/
private theorem isLocallyNoetherian_of_coveringMorphismProperty (τ : CoveringTopology)
    {X Y : Scheme.{u}} {f : Y ⟶ X} (hf : coveringMorphismProperty.{u} τ f)
    (hX : IsLocallyNoetherian X) : IsLocallyNoetherian Y :=
  have := coveringMorphismProperty_le_locallyOfFiniteType τ f hf
  LocallyOfFiniteType.isLocallyNoetherian f

/-- Each morphism of a chosen covering family of a big site has the morphism property attached
to its topology. -/
public theorem coveringMorphismProperty_of_isCovering (B : BigSite.{u} τ)
    {𝒰 : Covering (siteCategory B)} (h𝒰 : isCovering τ B 𝒰) (i : 𝒰.2.I₀) :
    coveringMorphismProperty τ ((schemeBelowInclusion (cutoff τ B)).map (𝒰.2.f i)) := by
  cases τ with
  | fppf => exact (Precoverage.mem_comap_iff.mp h𝒰.1).2 (.of (𝒰.2.presieve₀_f i))
  | syntomic => exact h𝒰.1.1 i
  | smooth => exact h𝒰.1.2 ⟨i⟩
  | etale => exact h𝒰.1.2 ⟨i⟩
  | zariski => exact h𝒰.1.2 ⟨i⟩

/-- A member of a `τ`-covering family of a locally Noetherian scheme is locally Noetherian. -/
@[stacks 0GE1 "part (3): the members of a covering family of a locally Noetherian scheme"]
public theorem isLocallyNoetherian_of_mem_precoverage (τ : CoveringTopology) {X : Scheme.{u}}
    (hX : IsLocallyNoetherian X) {R : Presieve X}
    (hR : R ∈ Scheme.precoverage (coveringMorphismProperty.{u} τ) X)
    {Y : Scheme.{u}} {f : Y ⟶ X} (hf : R f) : IsLocallyNoetherian Y :=
  isLocallyNoetherian_of_coveringMorphismProperty τ (hR.2 hf) hX

/-- If a chosen covering family of a big site has locally Noetherian target, then each of its
sources is locally Noetherian. -/
@[stacks 0GE1 "part (3): the sources of a covering of a locally Noetherian object"]
public theorem isLocallyNoetherian_of_isCovering (B : BigSite.{u} τ)
    {𝒰 : Covering (siteCategory B)} (h𝒰 : isCovering τ B 𝒰)
    (hX : IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj 𝒰.1)) (i : 𝒰.2.I₀) :
    IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj (𝒰.2.X i)) :=
  isLocallyNoetherian_of_coveringMorphismProperty τ (coveringMorphismProperty_of_isCovering B h𝒰 i)
    hX

/-- If a covering family of the big fppf category over `S` has locally Noetherian target, then
each of its sources is locally Noetherian. -/
@[stacks 0GE1 "part (3) for the big fppf site over a base scheme"]
public theorem isLocallyNoetherian_of_isCovering_bigFppfOver (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {E : Covering (BigFppfOver B S hS)}
    (hE : BigFppfOver.IsCovering B S hS E)
    (hX : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj E.1)) (i : E.2.I₀) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (E.2.X i)) :=
  isLocallyNoetherian_of_isCovering (τ := .fppf) B (𝒰 := ⟨_, _⟩) hE hX i

/-- If `f : X ⟶ Y` is a morphism of the big site over `S` whose underlying morphism of schemes
is locally of finite type and whose target is locally Noetherian, then its source is locally
Noetherian. -/
@[stacks 0GE1 "part (1): a morphism locally of finite type has locally Noetherian source",
  ega "IV 1.3.3" "special case"]
public theorem isLocallyNoetherian_of_locallyOfFiniteType_over (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) {X Y : Over (base B S hS)} (f : X ⟶ Y)
    (hY : IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj Y.left))
    (hf : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.left)) :
    IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj X.left) :=
  LocallyOfFiniteType.isLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).map f.left)

/-- The functor from the big site over `S` to all schemes preserves fibre products. -/
private theorem preservesCospans_forget_comp_schemeBelowInclusion (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) :
    PreservesLimitsOfShape WalkingCospan
      (Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B)) :=
  have : (schemeSizeBelow (cutoff τ B)).IsClosedUnderIsomorphisms :=
    ⟨fun e hX ↦ (Scheme.size_congr e).symm.trans_lt hX⟩
  have : (schemeSizeBelow (cutoff τ B)).IsClosedUnderLimitsOfShape WalkingCospan := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    change (limit F).size < cutoff τ B
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right)
  comp_preservesLimitsOfShape _ _

/-- Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of the big site over `S` with `f` locally of
finite type on underlying schemes and `Z` locally Noetherian. Then the vertex of a fibre product
square on `f` and `g` is locally Noetherian. -/
@[stacks 0GE1 "part (2): the fibre product along a morphism locally of finite type"]
public theorem isLocallyNoetherian_of_isPullback_over (B : BigSite.{u} τ) (S : Scheme.{u})
    (hS : S.size < cutoff τ B) {W X Y Z : Over (base B S hS)}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback p q f g)
    (hf : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.left))
    (hZ : IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj Z.left)) :
    IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj W.left) := by
  have : IsLocallyNoetherian
      ((Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B)).obj Z) := hZ
  have := preservesCospans_forget_comp_schemeBelowInclusion B S hS
  have : LocallyOfFiniteType
      ((Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B)).map q) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (h.map (Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B))) hf
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B)).map q)

end AlgebraicGeometry

end
