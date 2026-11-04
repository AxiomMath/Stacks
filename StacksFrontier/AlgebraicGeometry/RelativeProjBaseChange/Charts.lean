module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# The base change of a relative homogeneous spectrum, chart by chart

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra, `P` a relative homogeneous
spectrum of `A` over `S` and `g : S' ⟶ S` an arbitrary morphism of schemes. Tag 01O3 asserts
that `S' ×_S P` is again a relative homogeneous spectrum, namely that of `g^*A` over `S'`. **This
file proves the local half of that assertion**: for every affine open `U` of `S` and every open
`V` of `S'` carried into `U` by `g`, the part of `S' ×_S P` lying over `V` is the fibre product
`Proj Γ(U, A) ×_U V` of the affine Proj chart over `U` with `V`; and the opens `V` which are
affine and are carried into an affine open of `S` cover `S'`, so those fibre products cover
`S' ×_S P`.

Nothing here is specific to the symmetric algebra, and nothing is specific to the relative
homogeneous spectrum built by `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`: the only
input is the cartesian square `RelativeProjData.chart_isPullback` saying that the chart over an
affine open is the inverse image of that affine open.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.baseChangeChart`: **the chart of the base
  change**, the morphism `Proj Γ(U, A) ×_U V ⟶ S' ×_S P` induced by the chart over `U` and the
  inclusion of `V`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.isPullback_chart_resLE`: `Proj Γ(U, A) ×_U V`
  is the fibre product of `P` with `V` over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.isPullback_baseChangeChart`: **the chart of
  the base change is the inverse image of `V`**, as a cartesian square over `V ⟶ S'`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.isOpenImmersion_baseChangeChart` and
  `opensRange_baseChangeChart`: it is an open immersion, with image exactly the inverse image of
  `V` in `S' ×_S P`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.exists_isAffineOpen_le_preimage`: every point
  of `S'` lies in an affine open which `g` carries into an affine open of `S`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChange.sSup_affineOpens_le_preimage_eq_top` and
  `iSup_preimage_affineOpens_eq_top`: those affine opens cover `S'`, and their inverse images
  cover `S' ×_S P`.

## Implementation notes

The morphism `V ⟶ U` induced by `g` is Mathlib's `AlgebraicGeometry.Scheme.Hom.resLE`, and the
only property of it used is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`, which identifies
`V ⟶ U ⟶ S` with `V ⟶ S' ⟶ S`. Taking `V` to be an arbitrary open carried into `U`, rather than
`g ⁻¹ᵁ U` itself, is what makes the covering statement available: `g ⁻¹ᵁ U` is in general not
affine even when `U` is, and the charts of a relative homogeneous spectrum over `S'` are indexed
by the *affine* opens of `S'`.

`baseChangeChart` is pinned down by `baseChangeChart_fst` and `baseChangeChart_snd`, which are
its two defining equations, so no statement below depends on the particular way the universal
property is invoked.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)

## Not done here

**No tag is claimed, and in particular not 01O3.** That tag asserts a canonical isomorphism
`Proj_{S'}(g^*A) ≅ S' ×_S Proj_S(A)` together with a comparison of the twisting sheaves, and
two things stand between what is proved here and it.

The first is the pullback `g^*A` of a quasi-coherent graded `𝒪_S`-algebra along an arbitrary
morphism. This library **does** have it: morphisms of such algebras are
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebraHom`
(`RelativeProjMapDomain/Hom.lean:63`), and the pullback is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.pullback`
(`RelativeProjQcohSheaf/SituationRestrict.lean:140` — note the namespace and the directory
differ), for an *arbitrary* `g : X ⟶ S` with no open-immersion hypothesis, its pieces identified
with the inverse images of the pieces by `pullback_piece` (`:153`, a `rfl`). So the right-hand
side of the tag's isomorphism can be written for a general `A`; what is still missing is the
comparison of `Proj_{S'}(g^*A)` with the fibre product on the `SheafGradedAlgebra` substrate,
since `Stacks.RelativeProj.Situation.relativeProjBaseChange` is stated for a
`Stacks.RelativeProj.Situation` and consumes that identification as a datum. For `A` the sheaf
symmetric algebra of a quasi-coherent module `ℰ` it can, because `g^*(Sym ℰ)` is `Sym(g^*ℰ)` and
`Stacks.SymGraded.schemeProjectiveBundle (g^*ℰ)` is already a term; what is then missing is the
identification of the graded ring of sections `Γ(V, Sym(g^*ℰ))` with the base change
`Γ(S', V) ⊗_{Γ(S, U)} Γ(U, Sym ℰ)`, which would turn the fibre product
`Proj Γ(U, Sym ℰ) ×_U V` appearing below into `Proj Γ(V, Sym(g^*ℰ))` by
`Stacks.AlgebraicGeometry.RelativeProjBaseChange.isPullback_map_resLE` of
`StacksFrontier.AlgebraicGeometry.RelativeProjBaseChange.AffineOpen`.

The second is the glueing. A relative homogeneous spectrum over `S'` is the colimit of its
charts over *every* affine open of `S'`, while the charts produced here are indexed by the
affine opens carried into an affine open of `S`; those form a cover of `S'` but not a cofinal
subfamily of the affine Zariski site, whose arrows go from smaller opens to larger ones. So the
comparison morphism of the tag cannot be obtained from the colimit's universal property applied
to the family below, and constructing it needs the relative homogeneous spectrum to be
recognisable from its charts over a mere basis of the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChange

universe u

variable {S S' : Scheme.{u}} {A : SheafGradedAlgebra S}

/-! ### The chart of the base change -/

/-- **The affine Proj chart over `U`, fibred over an open `V` of `S'` carried into `U`, is the
fibre product of the relative homogeneous spectrum with `V` over `S`.** This is the horizontal
paste of the fibre-product square defining `Proj Γ(U, A) ×_U V` with the cartesian square
exhibiting the chart over `U` as the inverse image of `U`. -/
public theorem isPullback_chart_resLE (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    IsPullback (pullback.fst (projInclusionToOpen A U hU) (g.resLE U V hV) ≫ P.chart U hU)
      (pullback.snd (projInclusionToOpen A U hU) (g.resLE U V hV)) P.toBase (V.ι ≫ g) := by
  rw [← Scheme.Hom.resLE_comp_ι g hV]
  exact (IsPullback.of_hasPullback (projInclusionToOpen A U hU)
    (g.resLE U V hV)).paste_horiz (P.chart_isPullback U hU)

/-- **The chart of the base change.** For `U` an affine open of `S` and `V` an open of `S'`
carried into `U` by `g`, the morphism `Proj Γ(U, A) ×_U V ⟶ S' ×_S P` whose components are the
chart over `U` and the inclusion of `V`. -/
public def baseChangeChart (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    pullback (projInclusionToOpen A U hU) (g.resLE U V hV) ⟶ pullback P.toBase g :=
  pullback.lift (pullback.fst (projInclusionToOpen A U hU) (g.resLE U V hV) ≫ P.chart U hU)
    (pullback.snd (projInclusionToOpen A U hU) (g.resLE U V hV) ≫ V.ι)
    (isPullback_chart_resLE P g hU hV).w

/-- The component of `baseChangeChart` in `P` is the chart over `U` composed with the
projection `Proj Γ(U, A) ×_U V ⟶ Proj Γ(U, A)`. -/
@[reassoc (attr := simp)]
public theorem baseChangeChart_fst (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    baseChangeChart P g hU hV ≫ pullback.fst P.toBase g =
      pullback.fst (projInclusionToOpen A U hU) (g.resLE U V hV) ≫ P.chart U hU :=
  pullback.lift_fst _ _ _

/-- The component of `baseChangeChart` in `S'` is the projection
`Proj Γ(U, A) ×_U V ⟶ V` followed by the inclusion of `V`. -/
@[reassoc (attr := simp)]
public theorem baseChangeChart_snd (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    baseChangeChart P g hU hV ≫ pullback.snd P.toBase g =
      pullback.snd (projInclusionToOpen A U hU) (g.resLE U V hV) ≫ V.ι :=
  pullback.lift_snd _ _ _

/-- **The chart of the base change is the inverse image of `V`.** The square formed by the chart,
the structure morphism `Proj Γ(U, A) ×_U V ⟶ V`, the projection `S' ×_S P ⟶ S'` and the
inclusion of `V` is cartesian. -/
public theorem isPullback_baseChangeChart (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    IsPullback (baseChangeChart P g hU hV)
      (pullback.snd (projInclusionToOpen A U hU) (g.resLE U V hV))
      (pullback.snd P.toBase g) V.ι :=
  IsPullback.of_right
    (by rw [baseChangeChart_fst]; exact isPullback_chart_resLE P g hU hV)
    (baseChangeChart_snd P g hU hV) (IsPullback.of_hasPullback P.toBase g)

/-- The chart of the base change is an open immersion, being a base change of the inclusion of an
open. -/
public instance isOpenImmersion_baseChangeChart (P : RelativeProjData A) (g : S' ⟶ S)
    {U : S.Opens} (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    IsOpenImmersion (baseChangeChart P g hU hV) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeChart P g hU hV).flip inferInstance

/-- **The image of the chart of the base change** is the inverse image of `V` under the
projection `S' ×_S P ⟶ S'`. -/
public theorem opensRange_baseChangeChart (P : RelativeProjData A) (g : S' ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    (baseChangeChart P g hU hV).opensRange = pullback.snd P.toBase g ⁻¹ᵁ V := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_baseChangeChart P g hU hV).flip ⊤
  rwa [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at h

/-! ### The opens of `S'` the charts are indexed by -/

/-- **Every point of the source of a morphism of schemes lies in an affine open which the
morphism carries into an affine open of the target.** The affine opens of a scheme are a basis of
its topology, so one may first choose an affine open around the image of the point and then an
affine open around the point inside its inverse image. -/
public theorem exists_isAffineOpen_le_preimage (g : S' ⟶ S) (x : S') :
    ∃ (U : S.Opens) (V : S'.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧ V ≤ g ⁻¹ᵁ U := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ := (Scheme.isBasis_affineOpens S).exists_subset_of_mem_open
    (Set.mem_univ (g.base x)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ := (Scheme.isBasis_affineOpens S').exists_subset_of_mem_open
    (show x ∈ (g ⁻¹ᵁ U : S'.Opens) from hxU) (g ⁻¹ᵁ U).2
  exact ⟨U, V, hU, hV, hxV, hVU⟩

/-- **The affine opens of `S'` carried by `g` into an affine open of `S` cover `S'`.** -/
public theorem sSup_affineOpens_le_preimage_eq_top (g : S' ⟶ S) :
    sSup {V : S'.Opens | IsAffineOpen V ∧ ∃ U : S.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, V, hU, hV, hxV, hVU⟩ := exists_isAffineOpen_le_preimage g x
  exact Opens.mem_sSup.2 ⟨V, ⟨hV, U, hU, hVU⟩, hxV⟩

/-- **The inverse images of those affine opens cover the base change.** Together with
`Stacks.AlgebraicGeometry.RelativeProjBaseChange.opensRange_baseChangeChart` this says that
`S' ×_S P` is covered by the fibre products `Proj Γ(U, A) ×_U V`. -/
public theorem iSup_preimage_affineOpens_eq_top (P : RelativeProjData A) (g : S' ⟶ S) :
    (⨆ V : ↥{V : S'.Opens | IsAffineOpen V ∧ ∃ U : S.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U},
      pullback.snd P.toBase g ⁻¹ᵁ (V : S'.Opens)) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _
    (by rw [← sSup_eq_iSup']; exact sSup_affineOpens_le_preimage_eq_top g)

end Stacks.AlgebraicGeometry.RelativeProjBaseChange

end
