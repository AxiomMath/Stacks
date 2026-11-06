module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.SpecialFibreThin

/-!
# The infinitesimal row of the six-term sequence of a 2-fibre product

Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over `𝒞_Λ` and let
`𝒲 = ℋ ×_ℱ 𝒢`. Part (2) of Tag 06L5 asserts a six-term exact sequence

`0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`.

This file carries the head of that sequence: the two maps

`Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)`

at a basepoint `w₀` of `𝒲` over the residue field, the injectivity of the first one, which is
the `0 →` of the source's sequence, and the exactness at `Inf(ℋ) ⊕ Inf(𝒢)`. The tail
`Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ` and its two exactness statements are
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact` and
`StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact`; exactness at `Inf(ℱ)` and all
five maps with all five exactness assertions in one statement are
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull`.

## Main definitions

* `Deformation.infProjPair`: the map `a : Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢)` of the six-term sequence,
  the pair of the maps induced on infinitesimal automorphisms by the two projections of the
  `2`-fibre product.
* `Deformation.infLegDiff`: the map `b : Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)` of the six-term sequence,
  the difference of the maps induced by the two outer legs, the second of them read through the
  comparison of basepoints that the fibre-product object `w₀` carries. The signs are the ones
  the source defers: a map into a direct sum is a pair, a map out of one is a difference.

## Main results

* `Deformation.injective_infProjPair`: **part (2) of Tag 06L5, exactness at `Inf(𝒲)`**. The
  pair of the two projections is injective on infinitesimal automorphisms, because a self-arrow
  of the `2`-fibre product whose two components are identities is the identity
  (`CategoryTheory.TwoFibreProductOver.Hom.ext'`) — the faithfulness of
  `f × g : 𝒲 → ℋ × 𝒢` that the source invokes.
* `Deformation.exact_infProjPair_infLegDiff`: **part (2) of Tag 06L5, exactness at
  `Inf(ℋ) ⊕ Inf(𝒢)`**. A pair `(β, γ)` with equal images in `Inf(ℱ)` defines a self-arrow of
  the chosen pushforward of `w₀` to the dual numbers, which is the source's "`(β, γ)` defines
  an automorphism of `w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')`"; conversely the comparison square of
  such a self-arrow says that the two legs agree on its image.
* `Deformation.pushforwardIso_eq_comparison_comp`: the identification that makes both halves
  work — the comparison isomorphism carried by a chosen pushforward of `w₀` *is* the composite
  of the comparisons of the chosen pushforwards of `f(y₀)`, of `y₀` and of `z₀`, by uniqueness
  of strongly cocartesian lifts.
* `Deformation.injective_prod_inducedInfinitesimalLinearMapOfEq`: the general criterion behind
  the injectivity, for two `1`-morphisms out of one category that are jointly faithful on
  self-arrows.
* `Deformation.exact_prod_coprod_neg_comp`: the exactness criterion in linear algebra that the
  two halves are fed to, which keeps all of the arithmetic of the direct sum out of the
  categorical argument.

## Implementation notes

The three `Inf`-terms are the tangent spaces at the identity of the automorphism functors of
the three basepoints (`Deformation.localizedAutomorphismFunctorTangent`), which is the model in
which Tag 07W6 — `Deformation.inducedInfinitesimalLinearMapOfEq`, the induced `k`-linear map —
is available. The basepoints are the images of one object `w₀` of `𝒲`, as in the source's "let
`x₀, y₀, z₀` be the image of `w₀`".

The two outer legs land at *different* objects of `ℱ`, namely `f(y₀)` and `g(z₀)`: the
`2`-fibre product identifies them only up to the comparison isomorphism `w₀.iso` that `w₀`
carries. The second leg's map is therefore followed by the canonical comparison
`Deformation.canonicalLocalizedTangentAutomorphismLinearEquiv` of Tag 06JV (2) along
`w₀.iso.inv`, which is the source's `Inf(ℱ) = Inf_{x₀}(ℱ)` of Remark 06JS made explicit. That
comparison is where the hypothesis that `w₀` lies over the residue field is used, exactly as in
the source.

Every one of the five maps of the `Inf`-row is conjugation by a comparison of chosen
pushforwards to the dual numbers, and those comparisons are pinned only by their composite with
the chosen inclusions. The exactness at `Inf(ℋ) ⊕ Inf(𝒢)` is therefore a diagram chase with
five comparisons, and it closes because of one identification, in which the comparison
isomorphism carried by the chosen pushforward of `w₀` — the `c' ∘ b'` of the source's
`w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')` — is recognized as the composite of the other four by
uniqueness of strongly cocartesian lifts
(`Deformation.pushforwardIso_eq_comparison_comp`). Two of those comparisons are produced by
`Deformation.inducedInfinitesimalLinearMapOfEq_spec_iso`, which is Tag 07W6's own comparison
with its inverse carried along, and one by
`Deformation.canonicalLocalizedTangentAutomorphismLinearEquiv_spec`, Tag 06JV (2)'s, which is
pinned only up to the action of its base map on carriers; that is what
`Deformation.isHomLift_id_of_map_apply_heq` turns into verticality. The bases of the three
dual-number objects in sight agree only propositionally, which
`Deformation.dualNumbersUnder_right_eq` records.

The self-arrow a pair `(β, γ)` defines is automatically infinitesimal, because the special
fibre of a predeformation category is thin and so the transport to it is trivial
(`Deformation.ker_transportAutHom_eq_top_of_isThin`) — the same mechanism as at the `T𝒲` spot.

Exactness at the next spot `Inf(ℱ)` is `Deformation.exact_infLegDiff_infBoundaryLinearMap`, in
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull`. It is separated from this
file because it compares the two normalizations of the square-zero extension: the boundary map
and the comparisons `Deformation.boundaryCompareFst` and `Deformation.boundaryCompareSnd` are
built at the re-based `Deformation.squareZeroCrossUnder`, whereas the identification above is at
the dual numbers `Deformation.dualNumbersUnder`, and each of the three comparisons of this file
has to be transported from one to the other. It also needs the maps of this file to be read on
the linear lift `Deformation.infinitesimalAutomorphismLinearLift`, which is the source of
`Deformation.boundaryLinearMap`, through `Deformation.tangentCarrierLinearEquiv` at the rank-one
coordinate module; that bridge is `Deformation.infBoundaryLinearMap`.

## References

* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

/-! ### Vanishing of the infinitesimal automorphism attached to the zero tangent vector -/

section Zero
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}

/-- The infinitesimal automorphism attached to the zero tangent vector of the automorphism
functor is the identity: the identification of Tag 06JV carries addition to composition, so it
carries the neutral element to the neutral element. -/
public theorem localizedTangentEquivKernel_eq_one (P : ChosenPushforwardsAt p x)
    (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    localizedTangentEquivKernel P 0 = 1 := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  obtain ⟨hadd, -⟩ := naturalLocalizedTangentModule_spec P hp
  have h : localizedTangentEquivKernel P 0 * localizedTangentEquivKernel P 0 =
      localizedTangentEquivKernel P 0 := by
    rw [← hadd, add_zero]
  exact mul_left_cancel (h.trans (mul_one _).symm)

end Zero

/-! ### Injectivity of a pair of induced maps on infinitesimal automorphisms -/

section Pair
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G₁ : Type u₂} [Category.{v₂} G₁]
  {G₂ : Type u₃} [Category.{v₃} G₂]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {q₁ : G₁ ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {q₂ : G₂ ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- A tangent vector killed by the map on infinitesimal automorphisms induced by a morphism
over `𝒞_Λ` has image the identity under that morphism: the induced map is conjugation by the
comparison of dual-number pushforwards, so it is the identity exactly when the conjugand
is. -/
public theorem map_eq_id_of_inducedInfinitesimalLinearMapOfEq_eq_zero (Φ : F ⥤ G₁) {x₀ : F}
    (hw : Φ ⋙ q₁ = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q₁)
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q₁ (Φ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    ∀ t : localizedAutomorphismFunctorTangent P,
      inducedInfinitesimalLinearMapOfEq Φ hw hp hq P Q t = 0 →
        Φ.map (localizedTangentEquivKernel P t).1.asIso.hom.val = 𝟙 _ := by
  subst hw
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  intro t ht
  have hz : inducedInfinitesimalLinearMap Φ P Q hp hq t = 0 := ht
  have hval : (localizedTangentEquivKernel Q
      (inducedInfinitesimalLinearMap Φ P Q hp hq t)).1.asIso.hom.val = 𝟙 _ := by
    rw [hz, localizedTangentEquivKernel_eq_one Q hq]
    rfl
  rw [inducedInfinitesimalLinearMap_apply Φ P Q hp hq t] at hval
  set U := dualNumbersUnder (p := Φ ⋙ q₁) (x := x₀)
  set cp := comparisonPushforward Φ P Q U
  set ci := comparisonPushforwardInv Φ P Q hq.1 U
  have hcancel : ci ≫ cp = 𝟙 (Φ.obj (P.obj U).1) :=
    comparisonPushforwardInv_comp Φ P Q hq.1 U
  calc Φ.map (localizedTangentEquivKernel P t).1.asIso.hom.val
      = (ci ≫ cp) ≫ Φ.map (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ (ci ≫ cp) := by
        rw [hcancel, Category.id_comp, Category.comp_id]
    _ = ci ≫ (cp ≫ Φ.map (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ ci) ≫ cp := by
        simp only [Category.assoc]
    _ = ci ≫ cp := by
        rw [hval]
        exact congrArg (fun z => ci ≫ z) (Category.id_comp cp)
    _ = 𝟙 _ := hcancel

/-- The pair of the maps on infinitesimal automorphisms induced by two morphisms over `𝒞_Λ` is
injective as soon as the two morphisms are jointly faithful on self-arrows. -/
public theorem injective_prod_inducedInfinitesimalLinearMapOfEq (Φ₁ : F ⥤ G₁) (Φ₂ : F ⥤ G₂)
    {x₀ : F} (hw₁ : Φ₁ ⋙ q₁ = p) (hw₂ : Φ₂ ⋙ q₂ = p) (hp : SatisfiesRS p)
    (hq₁ : SatisfiesRS q₁) (hq₂ : SatisfiesRS q₂) (P : ChosenPushforwardsAt p x₀)
    (Q₁ : ChosenPushforwardsAt q₁ (Φ₁.obj x₀)) (Q₂ : ChosenPushforwardsAt q₂ (Φ₂.obj x₀))
    (hjoint : ∀ (Z : F) (g : Z ⟶ Z), Φ₁.map g = 𝟙 _ → Φ₂.map g = 𝟙 _ → g = 𝟙 Z) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q₁ hq₁
    letI := naturalLocalizedTangentModule Q₁ hq₁
    letI := naturalLocalizedTangentAddCommGroup Q₂ hq₂
    letI := naturalLocalizedTangentModule Q₂ hq₂
    Function.Injective
      (LinearMap.prod (inducedInfinitesimalLinearMapOfEq Φ₁ hw₁ hp hq₁ P Q₁)
        (inducedInfinitesimalLinearMapOfEq Φ₂ hw₂ hp hq₂ P Q₂)) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q₁ hq₁
  let := naturalLocalizedTangentModule Q₁ hq₁
  let := naturalLocalizedTangentAddCommGroup Q₂ hq₂
  let := naturalLocalizedTangentModule Q₂ hq₂
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h1 : inducedInfinitesimalLinearMapOfEq Φ₁ hw₁ hp hq₁ P Q₁ t = 0 := congrArg Prod.fst ht
  have h2 : inducedInfinitesimalLinearMapOfEq Φ₂ hw₂ hp hq₂ P Q₂ t = 0 := congrArg Prod.snd ht
  have hg : (localizedTangentEquivKernel P t).1.asIso.hom.val = 𝟙 _ :=
    hjoint _ _
      (map_eq_id_of_inducedInfinitesimalLinearMapOfEq_eq_zero Φ₁ hw₁ hp hq₁ P Q₁ t h1)
      (map_eq_id_of_inducedInfinitesimalLinearMapOfEq_eq_zero Φ₂ hw₂ hp hq₂ P Q₂ t h2)
  apply (localizedTangentEquivKernel P).injective
  rw [localizedTangentEquivKernel_eq_one P hp]
  exact Subtype.ext (Aut.ext (Iso.ext (Subtype.ext hg)))

end Pair

/-! ### The infinitesimal row of the six-term sequence -/

section InfRow
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

variable (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)

/-- `a`, the map `Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢)` of the six-term sequence: the pair of the maps
induced on infinitesimal automorphisms by the two projections of the `2`-fibre product.

The three terms are taken at a basepoint `w₀` of `𝒲` and at its two images, as in the source,
each with a choice of pushforwards along the arrows out of its base. -/
public noncomputable def infProjPair
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y) :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule QG hG.satisfiesRS
    localizedAutomorphismFunctorTangent PW →ₗ[k]
      localizedAutomorphismFunctorTangent QH × localizedAutomorphismFunctorTangent QG :=
  letI := naturalLocalizedTangentAddCommGroup PW
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
  letI := naturalLocalizedTangentModule PW
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
  letI := naturalLocalizedTangentModule QH hH.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
  letI := naturalLocalizedTangentModule QG hG.satisfiesRS
  LinearMap.prod
    (inducedInfinitesimalLinearMapOfEq (productFst.{u, v, w} pF f g).toFunctor
      (productFst.{u, v, w} pF f g).w
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
      hH.satisfiesRS PW QH)
    (inducedInfinitesimalLinearMapOfEq (productSnd.{u, v, w} pF f g).toFunctor
      (productSnd.{u, v, w} pF f g).w
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
      hG.satisfiesRS PW QG)

/-- **Stacks Project, Tag 06L5, part (2): exactness at `Inf(𝒲)`.** The map
`a : Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢)` of the six-term sequence is injective, which is the `0 →` at
its source.

This is the source's "injectivity of the first map comes from the fact that
`f × g : 𝒲 → ℋ × 𝒢` is faithful": the induced map on infinitesimal automorphisms is
conjugation by the comparison of dual-number pushforwards
(`Deformation.inducedInfinitesimalLinearMap_apply`), so a tangent vector in the kernel of both
components is an automorphism of a pushforward of `w₀` whose two projections are identities,
and a self-arrow of the `2`-fibre product is determined by its two components
(`CategoryTheory.TwoFibreProductOver.Hom.ext'`). -/
@[stacks 06L5 "part (2), the map `Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢)` of the six-term exact sequence \
and the injectivity of it asserted at the first spot"]
public theorem injective_infProjPair
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y) :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule QG hG.satisfiesRS
    Function.Injective (infProjPair.{u, v, w} pF f g hH hG hF PW QH QG) :=
  injective_prod_inducedInfinitesimalLinearMapOfEq
    (productFst.{u, v, w} pF f g).toFunctor (productSnd.{u, v, w} pF f g).toFunctor
    (productFst.{u, v, w} pF f g).w (productSnd.{u, v, w} pF f g).w
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    hH.satisfiesRS hG.satisfiesRS PW QH QG
    (fun _ _ h₁ h₂ => TwoFibreProductOver.Hom.ext' h₁ h₂)

/-- `b`, the map `Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)` of the six-term sequence: the difference of the
maps induced on infinitesimal automorphisms by the two outer legs.

On a pair `(β, γ)` the value is `f(β) - c(g(γ))`, where `c` is the canonical linear comparison
of Tag 06JV (2) between the infinitesimal automorphisms at the two *different* objects `f(y₀)`
and `g(z₀)` of `ℱ` that the two legs land at — the `2`-fibre product identifies them only up to
the comparison isomorphism that `w₀` carries, and `c` is the identification along it. The
hypothesis that the basepoint lies over the residue field is the source's own, `w₀` being an
object of `𝒲(k)`. The sign is the one the source defers: a map out of a direct sum is a
difference, written here as the coprod of `f(β)` with the negated second map. -/
public noncomputable def infLegDiff
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x))
    (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hw₀ : (f ⋙ pF).obj w₀.x = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    (localizedAutomorphismFunctorTangent.{u, v, w, u₁, v₁} QH ×
        localizedAutomorphismFunctorTangent.{u, v, w, u₂, v₂} QG) →ₗ[k]
      localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF :=
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  LinearMap.coprod
    (inducedInfinitesimalLinearMapOfEq (firstLegBased.{u, v, w} pF f).toFunctor
      (firstLegBased.{u, v, w} pF f).w hH.satisfiesRS hF.satisfiesRS QH PF)
    ((-(canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
            w₀.iso.inv hw₀ PF' PF).toLinearMap).comp
        (inducedInfinitesimalLinearMapOfEq (secondLegBased.{u, v, w} pF g).toFunctor
          (secondLegBased.{u, v, w} pF g).w hG.satisfiesRS hF.satisfiesRS QG PF'))

end InfRow

/-! ### The comparison isomorphisms the induced maps are conjugation by -/

section Comparisons
universe u v w u₁ v₁ u₂ v₂
variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **The comparison of Tag 07W6 as an isomorphism.** The induced map on infinitesimal
automorphisms is conjugation by the comparison of dual-number pushforwards, and that comparison
is an isomorphism of the fibre: `Deformation.inducedInfinitesimalLinearMapOfEq_spec` with the
inverse of `Deformation.comparisonPushforward` carried along, which is what a diagram chase
through the row needs. -/
public theorem inducedInfinitesimalLinearMapOfEq_spec_iso (Φ : F ⥤ G) {x₀ : F}
    (hw : Φ ⋙ q = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q)
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    ∃ H : (Q.obj (dualNumbersUnder (p := q) (x := Φ.obj x₀))).1 ≅
        Φ.obj (P.obj (dualNumbersUnder (p := p) (x := x₀))).1,
      q.IsHomLift (𝟙 (dualNumbersUnder (p := q) (x := Φ.obj x₀)).right) H.hom ∧
        Q.inclusion (dualNumbersUnder (p := q) (x := Φ.obj x₀)) ≫ H.hom =
          Φ.map (P.inclusion (dualNumbersUnder (p := p) (x := x₀))) ∧
        ∀ a, (localizedTangentEquivKernel Q
            (inducedInfinitesimalLinearMapOfEq Φ hw hp hq P Q a)).1.asIso.hom.val ≫ H.hom =
          H.hom ≫ Φ.map (localizedTangentEquivKernel P a).1.asIso.hom.val := by
  subst hw
  have hconj : ∀ a, (localizedTangentEquivKernel Q
      (inducedInfinitesimalLinearMap Φ P Q hp hq a)).1.asIso.hom.val ≫
        comparisonPushforward Φ P Q (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)) =
      comparisonPushforward Φ P Q (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)) ≫
        Φ.map (localizedTangentEquivKernel P a).1.asIso.hom.val := by
    intro a
    rw [inducedInfinitesimalLinearMap_apply Φ P Q hp hq a, Category.assoc, Category.assoc,
      comparisonPushforwardInv_comp, Category.comp_id]
  exact ⟨⟨comparisonPushforward Φ P Q _, comparisonPushforwardInv Φ P Q hq.1 _,
    comparisonPushforward_comp_inv Φ P Q hq.1 _, comparisonPushforwardInv_comp Φ P Q hq.1 _⟩,
    comparisonPushforward_isHomLift Φ P Q _,
    inclusion_comp_comparisonPushforward Φ P Q _, hconj⟩

/-- The transport along an equality of objects of `𝒞_Λ` acts on carriers as a cast. -/
public theorem hom_eqToHom_apply_heq {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A = B)
    (t : ↥A) : (eqToHom h).hom t ≍ t := by
  subst h
  rfl

/-- The underlying object of `𝒞_Λ` of the canonical dual numbers under a base object, as a
function of that base object alone. -/
private noncomputable abbrev dualNumbersUnderRight (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    ArtinianLocalAlgCat.{u, max v w, w} Λ k :=
  letI := residueAlgebra A
  ((algebrasUnder A).obj (artinianDualNumbers.{max v w, w, v} A k)).right

/-- The dual numbers over equal base objects have equal underlying objects of `𝒞_Λ`. -/
private theorem dualNumbersUnderRight_eq {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (h : A = B) :
    dualNumbersUnderRight.{u, v, w} A = dualNumbersUnderRight.{u, v, w} B := by
  subst h
  rfl

/-- **The dual numbers depend on the basepoint only through its base.** Two objects, possibly
of different categories over `𝒞_Λ`, lying over the same object of `𝒞_Λ` have the same
dual-number object under them. This is the comparison the `2`-fibre product needs between the
three basepoints `w₀`, `y₀ = w₀.x` and `z₀ = w₀.y`, whose bases agree propositionally. -/
public theorem dualNumbersUnder_right_eq {x : F} {y : G} (h : p.obj x = q.obj y) :
    (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right =
      (dualNumbersUnder.{u, v, w, u₂, v₂} (p := q) (x := y)).right :=
  dualNumbersUnderRight_eq.{u, v, w} h

/-- **The specification of the canonical comparison of Tag 06JV (2).** The pinned linear
comparison between the infinitesimal automorphisms at `x` and at `x₀` is conjugation by an
isomorphism of dual-number pushforwards compatible with the two chosen inclusions and with the
morphism `j`, whose base map is the identity on carriers. This is
`Deformation.existsUnique_localizedTangentAutomorphismLinearEquiv` read at the equivalence it
chooses. -/
public theorem canonicalLocalizedTangentAutomorphismLinearEquiv_spec (hp : SatisfiesRS p) {x x₀ : F}
    (j : x ⟶ x₀) (hbase : p.obj x₀ = residueFieldObject.{u, v, w} Λ k)
    (P : ChosenPushforwardsAt p x) (Q : ChosenPushforwardsAt p x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hp
    letI := naturalLocalizedTangentModule Q hp
    ∃ (H₀ : (P.obj (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x))).1 ≅
          (Q.obj (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x₀))).1)
        (Hε : (P.obj (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x))).1 ≅
          (Q.obj (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x₀))).1),
      (P.inclusion (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)) ≫ H₀.hom =
          j ≫ Q.inclusion (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x₀))) ∧
        (P.inclusion (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x)) ≫ Hε.hom =
          j ≫ Q.inclusion (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x₀))) ∧
        (∀ t : (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right,
          (eqToHom (P.obj (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x))).2.symm ≫
            p.map Hε.hom ≫
              eqToHom (Q.obj
                (dualNumbersUnder.{u, v, w, u₁, v₁} (p := p) (x := x₀))).2).hom t = t) ∧
        (∀ a, (localizedTangentEquivKernel P a).1.asIso.hom.val ≫ Hε.hom =
          Hε.hom ≫ (localizedTangentEquivKernel Q
            (canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₁, v₁}
              hp j hbase P Q a)).1.asIso.hom.val) :=
  (Classical.choose_spec
    (existsUnique_localizedTangentAutomorphismLinearEquiv.{u, v, w, u₁, v₁} hp j hbase P Q)).1

/-- **A morphism whose base map is the identity on carriers is vertical.** If the base map of
`ψ`, read between the two objects of `𝒞_Λ` that its domain and codomain lie over, acts as a
cast on carriers, then `ψ` lies over the identity — the two objects being equal. This is how
the comparison of Tag 06JV (2), whose base map is pinned only on carriers, is recognized as
vertical. -/
public theorem isHomLift_id_of_map_apply_heq {a b : F} (ψ : a ⟶ b)
    {R S : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (ha : p.obj a = R) (hb : p.obj b = S)
    (hRS : R = S)
    (hc : ∀ t : ↥R, (eqToHom ha.symm ≫ p.map ψ ≫ eqToHom hb).hom t ≍ t) :
    p.IsHomLift (𝟙 S) ψ := by
  have hm : eqToHom ha.symm ≫ p.map ψ ≫ eqToHom hb = eqToHom hRS :=
    ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t =>
      eq_of_heq ((hc t).trans (hom_eqToHom_apply_heq.{u, v, w} hRS t).symm))
  refine IsHomLift.of_fac' p (𝟙 S) ψ (ha.trans hRS) hb ?_
  have : p.map ψ = eqToHom ha ≫ (eqToHom ha.symm ≫ p.map ψ ≫ eqToHom hb) ≫ eqToHom hb.symm := by
    simp
  rw [this, hm]
  simp

end Comparisons

/-! ### The cocartesian-uniqueness identification at the dual numbers -/

section Keystone
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)

/-- **The cocartesian-uniqueness identification at the dual numbers, the keystone of the
`Inf`-row.** The comparison isomorphism carried by a chosen pushforward of the basepoint `w₀`
of `𝒲 = ℋ ×_ℱ 𝒢` is the composite of the comparisons of all the chosen pushforwards in sight:
of `f(y₀)` with the image of the pushforward of `y₀`, of `g(z₀)` with the image of the
pushforward of `z₀`, and of the pushforwards of `f(y₀)` and `g(z₀)` along the comparison
isomorphism of `w₀` itself.

This is the source's `w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')` — the explicit form of a pushforward of
`w₀` in the `2`-fibre product — in the normalization in which the `Inf`-terms are stated.
Both sides are vertical arrows out of the chosen pushforward of `f(y₀)`, whose chosen inclusion
is strongly cocartesian, so it is enough that they agree after precomposition with that
inclusion: there both become the image under `g` of the second component of the chosen
inclusion of `w₀`, the first side by the comparison square of that inclusion. -/
public theorem pushforwardIso_eq_comparison_comp
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x) (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    {Uh : Under ((f ⋙ pF).obj w₀.x)} {Ug : Under ((g ⋙ pF).obj w₀.y)}
    {Uw : Under ((TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).obj w₀)}
    (H₁ : (QH.obj Uh).1 ≅ (PW.obj Uw).1.x)
    (H₂ : (QG.obj Ug).1 ≅ (PW.obj Uw).1.y)
    (H₃ : (PF.obj Uh).1 ≅ f.obj (QH.obj Uh).1)
    (H₄ : (PF'.obj Ug).1 ≅ g.obj (QG.obj Ug).1)
    (Hε : (PF'.obj Ug).1 ≅ (PF.obj Uh).1)
    (hH₁ : QH.inclusion Uh ≫ H₁.hom = (PW.inclusion Uw).a)
    (hH₂ : QG.inclusion Ug ≫ H₂.hom = (PW.inclusion Uw).b)
    (hH₃ : PF.inclusion Uh ≫ H₃.hom = f.map (QH.inclusion Uh))
    (hH₄ : PF'.inclusion Ug ≫ H₄.hom = g.map (QG.inclusion Ug))
    (hHε : PF'.inclusion Ug ≫ Hε.hom = w₀.iso.inv ≫ PF.inclusion Uh)
    (hl₁ : (f ⋙ pF).IsHomLift (𝟙 Uh.right) H₁.hom)
    (hl₂ : (g ⋙ pF).IsHomLift (𝟙 Ug.right) H₂.hom)
    (hl₃ : pF.IsHomLift (𝟙 Uh.right) H₃.hom)
    (hl₄ : pF.IsHomLift (𝟙 Ug.right) H₄.hom)
    (hlε : pF.IsHomLift (𝟙 Uh.right) Hε.inv) :
    H₃.hom ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom = Hε.inv ≫ H₄.hom ≫ g.map H₂.hom := by
  let _ := PF.inclusion_cocartesian Uh
  let _ := hl₃
  let _ := hlε
  let _ := hl₄
  let _ : pF.IsHomLift (𝟙 Uh.right) (f.map H₁.hom) :=
    isHomLift_map_of_comp f (𝟙 Uh.right) H₁.hom hl₁
  let _ : pF.IsHomLift (𝟙 Ug.right) (g.map H₂.hom) :=
    isHomLift_map_of_comp g (𝟙 Ug.right) H₂.hom hl₂
  let _ : pF.IsHomLift (𝟙 (PW.obj Uw).1.base) (PW.obj Uw).1.iso.hom := (PW.obj Uw).1.vertical
  let _ : pF.IsHomLift (𝟙 Uh.right) (f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom) :=
    IsHomLift.comp_lift_id_right' pF (𝟙 Uh.right) (f.map H₁.hom)
      (PW.obj Uw).1.base (PW.obj Uw).1.iso.hom
  let _ : pF.IsHomLift (𝟙 Uh.right)
      (H₃.hom ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom) := inferInstance
  let _ : pF.IsHomLift (𝟙 Ug.right) (H₄.hom ≫ g.map H₂.hom) := inferInstance
  let _ : pF.IsHomLift (𝟙 Uh.right) (Hε.inv ≫ H₄.hom ≫ g.map H₂.hom) :=
    IsHomLift.comp_lift_id_right' pF (𝟙 Uh.right) Hε.inv Ug.right
      (H₄.hom ≫ g.map H₂.hom)
  have hεinv : PF.inclusion Uh ≫ Hε.inv = w₀.iso.hom ≫ PF'.inclusion Ug := by
    calc PF.inclusion Uh ≫ Hε.inv
        = (w₀.iso.hom ≫ w₀.iso.inv ≫ PF.inclusion Uh) ≫ Hε.inv := by
          rw [Iso.hom_inv_id_assoc]
      _ = (w₀.iso.hom ≫ PF'.inclusion Ug ≫ Hε.hom) ≫ Hε.inv := by rw [hHε]
      _ = w₀.iso.hom ≫ PF'.inclusion Ug := by
          rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Functor.IsStronglyCocartesian.ext pF Uh.hom (PF.inclusion Uh) (𝟙 Uh.right) ?_
  calc PF.inclusion Uh ≫ H₃.hom ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom
      = (PF.inclusion Uh ≫ H₃.hom) ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom := by
        rw [Category.assoc]
    _ = f.map (QH.inclusion Uh ≫ H₁.hom) ≫ (PW.obj Uw).1.iso.hom := by
        rw [hH₃, f.map_comp, Category.assoc]
    _ = w₀.iso.hom ≫ g.map (PW.inclusion Uw).b := by
        rw [hH₁]
        exact (PW.inclusion Uw).w
    _ = (w₀.iso.hom ≫ PF'.inclusion Ug) ≫ H₄.hom ≫ g.map H₂.hom := by
        rw [Category.assoc, ← Category.assoc (PF'.inclusion Ug), hH₄, ← g.map_comp, hH₂]
    _ = PF.inclusion Uh ≫ Hε.inv ≫ H₄.hom ≫ g.map H₂.hom := by
        rw [← hεinv, Category.assoc]

end Keystone

/-! ### The two diagram chases of exactness at `Inf(ℋ) ⊕ Inf(𝒢)` -/

section Conj
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f : H ⥤ F} {g : G ⥤ F}
  {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
  {PW : ChosenPushforwardsAt
    (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀}
  {QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x} {QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y}
  {PF : ChosenPushforwardsAt pF (f.obj w₀.x)} {PF' : ChosenPushforwardsAt pF (g.obj w₀.y)}
  {Uh : Under ((f ⋙ pF).obj w₀.x)} {Ug : Under ((g ⋙ pF).obj w₀.y)}
  {Uw : Under ((TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).obj w₀)}
  {H₁ : (QH.obj Uh).1 ≅ (PW.obj Uw).1.x} {H₂ : (QG.obj Ug).1 ≅ (PW.obj Uw).1.y}
  {H₃ : (PF.obj Uh).1 ≅ f.obj (QH.obj Uh).1} {H₄ : (PF'.obj Ug).1 ≅ g.obj (QG.obj Ug).1}
  {Hε : (PF'.obj Ug).1 ≅ (PF.obj Uh).1}

/-- The comparison `Hε` of Tag 06JV (2) intertwines an infinitesimal automorphism at `g(z₀)`
with its image at `f(y₀)`, read in the other direction. -/
public theorem inv_comp_eq_of_conjugation {D : (PF'.obj Ug).1 ⟶ (PF'.obj Ug).1}
    {A : (PF.obj Uh).1 ⟶ (PF.obj Uh).1} (hε : D ≫ Hε.hom = Hε.hom ≫ A) :
    Hε.inv ≫ D = A ≫ Hε.inv := by
  calc Hε.inv ≫ D = Hε.inv ≫ (D ≫ Hε.hom) ≫ Hε.inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = Hε.inv ≫ Hε.hom ≫ A ≫ Hε.inv := by rw [hε, Category.assoc]
    _ = A ≫ Hε.inv := by rw [Iso.inv_hom_id_assoc]

/-- **The two legs agree on an infinitesimal automorphism of the `2`-fibre product.** If an
automorphism `A₁` at `f(y₀)` is the conjugate of the first component `a` of a self-arrow of the
chosen pushforward of `w₀`, and `A₂` is the conjugate of its second component `b` read through
the comparison of the two basepoints, then `A₁ = A₂`: the comparison isomorphism carried by the
pushforward of `w₀` intertwines `a` with `b`, and
`Deformation.pushforwardIso_eq_comparison_comp` identifies the two chains of comparisons with
it. -/
public theorem eq_of_conjugation
    (hkey : H₃.hom ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom =
      Hε.inv ≫ H₄.hom ≫ g.map H₂.hom)
    {A₁ A₂ : (PF.obj Uh).1 ⟶ (PF.obj Uh).1} {D : (PF'.obj Ug).1 ⟶ (PF'.obj Ug).1}
    {β : (QH.obj Uh).1 ⟶ (QH.obj Uh).1} {γ : (QG.obj Ug).1 ⟶ (QG.obj Ug).1}
    {a : (PW.obj Uw).1.x ⟶ (PW.obj Uw).1.x} {b : (PW.obj Uw).1.y ⟶ (PW.obj Uw).1.y}
    (hab : f.map a ≫ (PW.obj Uw).1.iso.hom = (PW.obj Uw).1.iso.hom ≫ g.map b)
    (h₃ : A₁ ≫ H₃.hom = H₃.hom ≫ f.map β) (h₁ : β ≫ H₁.hom = H₁.hom ≫ a)
    (h₄ : D ≫ H₄.hom = H₄.hom ≫ g.map γ) (h₂ : γ ≫ H₂.hom = H₂.hom ≫ b)
    (hε : D ≫ Hε.hom = Hε.hom ≫ A₂) :
    A₁ = A₂ := by
  refine (Iso.cancel_iso_hom_right A₁ A₂ (Hε.symm ≪≫ H₄ ≪≫ g.mapIso H₂)).mp ?_
  show A₁ ≫ Hε.inv ≫ H₄.hom ≫ g.map H₂.hom = A₂ ≫ Hε.inv ≫ H₄.hom ≫ g.map H₂.hom
  rw [← hkey, reassoc_of% h₃, ← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, hab,
    reassoc_of% hkey, ← g.map_comp, ← h₂, g.map_comp, ← reassoc_of% h₄,
    reassoc_of% inv_comp_eq_of_conjugation hε, hkey]

/-- **The comparison square of the self-arrow a pair of infinitesimal automorphisms defines.**
If the images of `β` at `f(y₀)` and of `γ` at `g(z₀)` agree, then the transports of `β` and `γ`
to the chosen pushforward of `w₀` satisfy the comparison-square condition of a self-arrow of
the `2`-fibre product. -/
public theorem square_of_conjugation
    (hkey : H₃.hom ≫ f.map H₁.hom ≫ (PW.obj Uw).1.iso.hom =
      Hε.inv ≫ H₄.hom ≫ g.map H₂.hom)
    {A₁ A₂ : (PF.obj Uh).1 ⟶ (PF.obj Uh).1} {D : (PF'.obj Ug).1 ⟶ (PF'.obj Ug).1}
    {β : (QH.obj Uh).1 ⟶ (QH.obj Uh).1} {γ : (QG.obj Ug).1 ⟶ (QG.obj Ug).1}
    (h₃ : A₁ ≫ H₃.hom = H₃.hom ≫ f.map β)
    (h₄ : D ≫ H₄.hom = H₄.hom ≫ g.map γ)
    (hε : D ≫ Hε.hom = Hε.hom ≫ A₂) (hA : A₁ = A₂) :
    f.map (H₁.inv ≫ β ≫ H₁.hom) ≫ (PW.obj Uw).1.iso.hom =
      (PW.obj Uw).1.iso.hom ≫ g.map (H₂.inv ≫ γ ≫ H₂.hom) := by
  refine (Iso.cancel_iso_hom_left (H₃ ≪≫ f.mapIso H₁) _ _).mp ?_
  show (H₃.hom ≫ f.map H₁.hom) ≫ f.map (H₁.inv ≫ β ≫ H₁.hom) ≫ (PW.obj Uw).1.iso.hom =
    (H₃.hom ≫ f.map H₁.hom) ≫ (PW.obj Uw).1.iso.hom ≫ g.map (H₂.inv ≫ γ ≫ H₂.hom)
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc, Functor.map_comp_assoc,
    ← reassoc_of% h₃, hkey, hA, reassoc_of% hkey, ← g.map_comp, Iso.hom_inv_id_assoc,
    g.map_comp, ← reassoc_of% inv_comp_eq_of_conjugation hε, reassoc_of% h₄]

end Conj

/-! ### The exactness criterion in linear algebra -/

section Algebra
universe z z₁ z₂ z₃ z₄ w

variable {k : Type w} [Field k]

/-- The exactness criterion, in linear algebra: the pair of two maps out of `M` is exact at
`N₁ × N₂` for the difference of two maps into `P` as soon as the two composites agree and a
pair with equal images comes from `M`. -/
public theorem exact_prod_coprod_neg_comp
    {M : Type z} {N₁ : Type z₁} {N₂ : Type z₂} {N₃ : Type z₃} {P : Type z₄}
    [AddCommGroup M] [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup P]
    [Module k M] [Module k N₁] [Module k N₂] [Module k N₃] [Module k P]
    (u : M →ₗ[k] N₁) (v : M →ₗ[k] N₂) (s : N₁ →ₗ[k] P) (t : N₃ →ₗ[k] P) (r : N₂ →ₗ[k] N₃)
    (hcomp : ∀ m, s (u m) = t (r (v m)))
    (hlift : ∀ (x : N₁) (y : N₂), s x = t (r y) → ∃ m, u m = x ∧ v m = y) :
    Function.Exact (LinearMap.prod u v) (LinearMap.coprod s ((-t).comp r)) := by
  intro b
  constructor
  · intro hb
    have hb' : s b.1 + -(t (r b.2)) = 0 := hb
    obtain ⟨m, h1, h2⟩ := hlift b.1 b.2 (add_neg_eq_zero.mp hb')
    exact ⟨m, Prod.ext h1 h2⟩
  · rintro ⟨m, rfl⟩
    show s (u m) + -(t (r (v m))) = 0
    rw [hcomp m, add_neg_cancel]

/-- Conjugating a vertical self-arrow by a vertical isomorphism gives a vertical arrow. -/
private theorem isHomLift_id_inv_comp_comp {X D : Type*} [Category X] [Category D] (p : X ⥤ D)
    {a b : X} {S : D} (e : a ≅ b) (u : a ⟶ a) (he : p.IsHomLift (𝟙 S) e.hom)
    (hu : p.IsHomLift (𝟙 S) u) : p.IsHomLift (𝟙 S) (e.inv ≫ u ≫ e.hom) := by
  have := he
  have := hu
  infer_instance

/-- Two endomorphisms conjugate by an isomorphism to the same arrow are equal. -/
private theorem eq_of_comp_hom_eq_of_eq_conj {C : Type*} [Category C] {a b : C}
    (e : a ≅ b) {x y : a ⟶ a} {m : b ⟶ b} (h : x ≫ e.hom = e.hom ≫ m)
    (hm : m = e.inv ≫ y ≫ e.hom) : x = y :=
  (Iso.cancel_iso_hom_right x y e).mp (h.trans (by rw [hm, Iso.hom_inv_id_assoc]))

end Algebra

/-! ### Exactness at `Inf(ℋ) ⊕ Inf(𝒢)` -/

section InfExact
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

variable (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)

/-- **Stacks Project, Tag 06L5, part (2): exactness at `Inf(ℋ) ⊕ Inf(𝒢)`.** In the
`Inf`-row

`Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)`

of the six-term sequence of the `2`-fibre product `𝒲 = ℋ ×_ℱ 𝒢`, the kernel of the difference
of the two outer legs is the image of the pair of the two projections.

This is the source's "if `(β, γ)` map to the same element of `Inf_{x₀}(ℱ)` then `(β, γ)`
defines an automorphism of `w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')`". Each of the five maps in sight is
conjugation by a comparison of chosen pushforwards
(`Deformation.inducedInfinitesimalLinearMapOfEq_spec_iso`,
`Deformation.canonicalLocalizedTangentAutomorphismLinearEquiv_spec`), and
`Deformation.pushforwardIso_eq_comparison_comp` identifies the composite of those comparisons
with the comparison isomorphism carried by the chosen pushforward of `w₀`. The two halves are
then the two readings of one square: the comparison square of a self-arrow of that pushforward
gives the vanishing of the composite (`Deformation.eq_of_conjugation`), and conversely a pair
with equal images satisfies that square (`Deformation.square_of_conjugation`), hence defines a
self-arrow, which is automatically infinitesimal because the special fibre of `𝒲` is thin
(`Deformation.ker_transportAutHom_eq_top_of_isThin`). -/
@[stacks 06L5 "part (2), exactness at `Inf(ℋ) ⊕ Inf(𝒢)` of the six-term exact sequence"]
public theorem exact_infProjPair_infLegDiff
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x))
    (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hw₀ : (f ⋙ pF).obj w₀.x = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Exact (infProjPair.{u, v, w} pF f g hH hG hF PW QH QG)
      (infLegDiff.{u, v, w} pF f g hH hG hF QH QG PF PF' hw₀) := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w} PW
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w} PW
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  obtain ⟨H₁, hl₁, hi₁, hc₁⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (productFst.{u, v, w} pF f g).toFunctor (productFst.{u, v, w} pF f g).w
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    hH.satisfiesRS PW QH
  obtain ⟨H₂, hl₂, hi₂, hc₂⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (productSnd.{u, v, w} pF f g).toFunctor (productSnd.{u, v, w} pF f g).w
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    hG.satisfiesRS PW QG
  obtain ⟨H₃, hl₃, hi₃, hc₃⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (firstLegBased.{u, v, w} pF f).toFunctor (firstLegBased.{u, v, w} pF f).w
    hH.satisfiesRS hF.satisfiesRS QH PF
  obtain ⟨H₄, hl₄, hi₄, hc₄⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
    hG.satisfiesRS hF.satisfiesRS QG PF'
  obtain ⟨-, Hε, -, hiε, hcarr, hcε⟩ :=
    canonicalLocalizedTangentAutomorphismLinearEquiv_spec.{u, v, w} hF.satisfiesRS
      w₀.iso.inv hw₀ PF' PF
  have hlεhom : pF.IsHomLift
      (𝟙 (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x)).right) Hε.hom :=
    isHomLift_id_of_map_apply_heq.{u, v, w} Hε.hom
      (PF'.obj (dualNumbersUnder.{u, v, w, u₂, v₂} (p := g ⋙ pF) (x := w₀.y))).2
      (PF.obj (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x))).2
      (dualNumbersUnder_right_eq.{u, v, w} (w₀.hy.trans w₀.hx.symm))
      (fun t => heq_of_eq (hcarr t))
  have hlε : pF.IsHomLift
      (𝟙 (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x)).right) Hε.inv := by
    let _ := hlεhom
    infer_instance
  have hkey := pushforwardIso_eq_comparison_comp.{u, v, w} f g PW QH QG PF PF'
    H₁ H₂ H₃ H₄ Hε hi₁ hi₂ hi₃ hi₄ hiε hl₁ hl₂ hl₃ hl₄ hlε
  have hUhw : (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x)).right =
      (dualNumbersUnder
        (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right :=
    dualNumbersUnder_right_eq.{u, v, w} w₀.hx
  have hUgw : (dualNumbersUnder.{u, v, w, u₂, v₂} (p := g ⋙ pF) (x := w₀.y)).right =
      (dualNumbersUnder
        (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right :=
    dualNumbersUnder_right_eq.{u, v, w} w₀.hy
  refine @exact_prod_coprod_neg_comp k _ _ _ _ _ _
    (naturalLocalizedTangentAddCommGroup.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS)
    (naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS)
    (naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS)
    (naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF' hF.satisfiesRS)
    (naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS)
    (naturalLocalizedTangentModule.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS)
    (naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS)
    (naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS)
    (naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF' hF.satisfiesRS)
    (naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS)
    (inducedInfinitesimalLinearMapOfEq.{u, v, w} (productFst.{u, v, w} pF f g).toFunctor
        (productFst.{u, v, w} pF f g).w
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
        hH.satisfiesRS PW QH)
    (inducedInfinitesimalLinearMapOfEq.{u, v, w} (productSnd.{u, v, w} pF f g).toFunctor
        (productSnd.{u, v, w} pF f g).w
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
        hG.satisfiesRS PW QG)
    (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₁, v₁, u₃, v₃}
        (firstLegBased.{u, v, w} pF f).toFunctor
        (firstLegBased.{u, v, w} pF f).w hH.satisfiesRS hF.satisfiesRS QH PF)
    (canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
        w₀.iso.inv hw₀ PF' PF).toLinearMap
    (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
        (secondLegBased.{u, v, w} pF g).toFunctor
        (secondLegBased.{u, v, w} pF g).w hG.satisfiesRS hF.satisfiesRS QG PF') ?_ ?_
  · -- the two legs agree on the image of an infinitesimal automorphism of `𝒲`
    intro m
    refine (localizedTangentEquivKernel PF).injective (Subtype.ext (Aut.ext (Iso.ext (Subtype.ext ?_))))
    exact eq_of_conjugation hkey
      ((localizedTangentEquivKernel PW m).1.asIso.hom.val).w (hc₃ _) (hc₁ m) (hc₄ _) (hc₂ m) (hcε _)
  · -- a pair with equal images is the image of an infinitesimal automorphism of `𝒲`
    intro x y hxy
    have hA : ((localizedTangentEquivKernel PF)
          ((inducedInfinitesimalLinearMapOfEq.{u, v, w, u₁, v₁, u₃, v₃}
            (firstLegBased.{u, v, w} pF f).toFunctor (firstLegBased.{u, v, w} pF f).w
            hH.satisfiesRS hF.satisfiesRS QH PF) x)).1.asIso.hom.val =
        ((localizedTangentEquivKernel PF)
          ((canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
            w₀.iso.inv hw₀ PF' PF)
            ((inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
              (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
              hG.satisfiesRS hF.satisfiesRS QG PF') y))).1.asIso.hom.val :=
      congrArg (fun z => ((localizedTangentEquivKernel PF) z).1.asIso.hom.val) hxy
    have hsq := square_of_conjugation hkey (hc₃ x) (hc₄ y) (hcε _) hA
    have hvβ : (f ⋙ pF).IsHomLift (𝟙 (dualNumbersUnder
      (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right)
        (H₁.inv ≫ (localizedTangentEquivKernel QH x).1.asIso.hom.val ≫ H₁.hom) := by
      rw [← hUhw]
      exact isHomLift_id_inv_comp_comp _ H₁ _ hl₁ (localizedTangentEquivKernel QH x).1.asIso.hom.2
    have hvγ : (g ⋙ pF).IsHomLift (𝟙 (dualNumbersUnder
      (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right)
        (H₂.inv ≫ (localizedTangentEquivKernel QG y).1.asIso.hom.val ≫ H₂.hom) := by
      rw [← hUgw]
      exact isHomLift_id_inv_comp_comp _ H₂ _ hl₂ (localizedTangentEquivKernel QG y).1.asIso.hom.2
    have hvτ : (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).IsHomLift
        (𝟙 (dualNumbersUnder
      (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right)
        (TwoFibreProductOver.isoMkVertical
          (P := (PW.obj (dualNumbersUnder
            (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
            (x := w₀))).1)
          (Q := (PW.obj (dualNumbersUnder
            (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
            (x := w₀))).1)
          (U := (dualNumbersUnder
      (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)).right)
          (H₁.symm ≪≫ Functor.Fiber.fiberInclusion.mapIso
            (localizedTangentEquivKernel QH x).1.asIso ≪≫ H₁)
          (H₂.symm ≪≫ Functor.Fiber.fiberInclusion.mapIso
            (localizedTangentEquivKernel QG y).1.asIso ≪≫ H₂) hvβ hvγ hsq).hom :=
      TwoFibreProductOver.structureFunctor_isHomLift _ _ hvβ
    obtain ⟨τ, hτa, hτb⟩ : ∃ τ : Aut (PW.obj (dualNumbersUnder
      (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀))),
        (productFst.{u, v, w} pF f g).toFunctor.map τ.asIso.hom.val =
            H₁.inv ≫ (localizedTangentEquivKernel QH x).1.asIso.hom.val ≫ H₁.hom ∧
          (productSnd.{u, v, w} pF f g).toFunctor.map τ.asIso.hom.val =
            H₂.inv ≫ (localizedTangentEquivKernel QG y).1.asIso.hom.val ≫ H₂.hom :=
      ⟨Aut.of <| fiberIsoOfVertical
        (PW.obj (dualNumbersUnder
          (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)))
        (PW.obj (dualNumbersUnder
          (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀)))
        _ hvτ, rfl, rfl⟩
    have hmem : τ ∈ MonoidHom.ker (PW.transportAutHom (tangentReduction
        (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀))) := by
      rw [ker_transportAutHom_eq_top_of_isThin
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation.cofibered
        PW (isThin_specialFiber.{u, v, w}
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation)
        (tangentReduction
          (p := TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) (x := w₀))]
      exact Subgroup.mem_top _
    obtain ⟨t, ht⟩ : ∃ t, (localizedTangentEquivKernel PW) t = ⟨τ, hmem⟩ :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    refine ⟨t, ?_, ?_⟩
    · exact (localizedTangentEquivKernel QH).injective (Subtype.ext (Aut.ext (Iso.ext (Subtype.ext
        (eq_of_comp_hom_eq_of_eq_conj H₁ (hc₁ t)
          ((congrArg (fun z => (productFst.{u, v, w} pF f g).toFunctor.map z.1.asIso.hom.val)
            ht).trans hτa))))))
    · exact (localizedTangentEquivKernel QG).injective (Subtype.ext (Aut.ext (Iso.ext (Subtype.ext
        (eq_of_comp_hom_eq_of_eq_conj H₂ (hc₂ t)
          ((congrArg (fun z => (productSnd.{u, v, w} pF f g).toFunctor.map z.1.asIso.hom.val)
            ht).trans hτb))))))

end InfExact


end Deformation

end
