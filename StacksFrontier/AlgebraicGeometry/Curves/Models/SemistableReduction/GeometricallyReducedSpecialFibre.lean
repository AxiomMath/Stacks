module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteGroupQuotient
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A reduced special fibre with smooth components is geometrically reduced

Let `X` be a reduced scheme over a field `k` with finitely many irreducible components
`X₁, …, Xₙ`, each taken with its reduced induced structure. If every `Xᵢ` is geometrically
reduced over `k`, then so is `X`: affine-locally, `A ⟶ ∏ᵢ A/𝔭ᵢ` is injective for the minimal
primes `𝔭ᵢ` of the reduced ring `A`, it stays injective after `- ⊗_k L` because `L` is flat over
`k`, and each `A/𝔭ᵢ ⊗_k L` is reduced. This file proves that statement and applies it to the
special fibre of a regular proper model whose components are smooth over the residue field.

## Main results

* `AlgebraicGeometry.isReduced_pullback_of_dense_iUnion_range` — let `X ⟶ S` be a morphism from
  a reduced scheme and `Y ⟶ S` a flat one. If finitely many quasi-compact morphisms
  `pᵢ : Wᵢ ⟶ X` have jointly dense image and each `Wᵢ ×_S Y` is reduced, then `X ×_S Y` is
  reduced.
* `AlgebraicGeometry.geometricallyReduced_of_dense_iUnion_range` — the same over a one-point
  integral base (the spectrum of a field), in the language of geometric reducedness.
* `AlgebraicGeometry.isReduced_pullback_of_irreducibleComponents` and
  `AlgebraicGeometry.geometricallyReduced_of_irreducibleComponents` — the special case where the
  `pᵢ` are the reduced induced closed subschemes on the irreducible components of `X`.
* `Stacks.Models.RegularProperModelSituation.geometricallyReduced_specialFiberToSpec_of_smooth`
  and `Stacks.Models.RegularProperModelSituation.isReduced_pullback_specialFiberToSpec_of_smooth`
  — if the special fibre `X_k` of a regular proper model is reduced and each of its irreducible
  components is smooth over `k`, then `X_k` is geometrically reduced over `k`.

## The argument

Let `P : ∐ᵢ Wᵢ ⟶ X` be the morphism induced by the `pᵢ`. It is quasi-compact, the index set being
finite, and dominant; since `X` is reduced, it is scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant`), that is, `𝒪_X ⟶ P_* 𝒪_{∐ Wᵢ}`
is injective. This is the sheaf form of the injectivity of `A ⟶ ∏ᵢ A/𝔭ᵢ`. Scheme-theoretic
dominance of a quasi-compact morphism is stable under flat base change
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst`), so the base change of `P` along
the flat projection `X ×_S Y ⟶ X` is a scheme-theoretically dominant, quasi-compact morphism to
`X ×_S Y`. Its source is `∐ᵢ Wᵢ ×_S Y`, coproducts of schemes being universal, and this is
reduced because each summand is. A scheme receiving a scheme-theoretically dominant quasi-compact
morphism from a reduced scheme is reduced
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced`).

For the special fibre, the components are the closed subschemes
`Stacks.Models.RegularModelSituation.specialFiberComponentIdeal` of the *model*, mapped into
`X_k` by `Stacks.Models.RegularModelSituation.specialFiberComponentι`; the image of the
component attached to `Z` is `Z` itself, so the images cover `X_k`. A smooth morphism is
geometrically reduced ([Stacks, Tag 056T], `AlgebraicGeometry.geometricallyReduced_of_smooth`),
and every morphism to the spectrum of a field is flat.

## Implementation notes

No Stacks tag is attached: the statement is used in the proof of [Stacks, Tag 0CDN] but is not
itself a numbered result.

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Reducedness of a flat base change, tested on a jointly dense finite family.** Let
`f : X ⟶ S` be a morphism from a reduced scheme and `g : Y ⟶ S` a flat morphism. If finitely
many quasi-compact morphisms `pᵢ : Wᵢ ⟶ X` have jointly dense image and each base change
`Wᵢ ×_S Y` is reduced, then `X ×_S Y` is reduced. -/
theorem isReduced_pullback_of_dense_iUnion_range {ι : Type u} [Finite ι]
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Flat g] [IsReduced X]
    {W : ι → Scheme.{u}} (p : ∀ i, W i ⟶ X) [∀ i, QuasiCompact (p i)]
    (hp : Dense (⋃ i, Set.range (p i)))
    (hred : ∀ i, IsReduced (pullback (p i ≫ f) g)) :
    IsReduced (pullback f g) := by
  have : QuasiCompact (Sigma.desc p) :=
    Space.quasiCompact_sigmaDesc_of_finite p fun i => inferInstance
  have : IsDominant (Sigma.desc p) := by
    rw [isDominant_iff]
    refine hp.mono ?_
    intro x hx
    obtain ⟨i, w, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨Sigma.ι W i w, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  have : IsSchemeTheoreticallyDominant (Sigma.desc p) := .of_isDominant _
  suffices IsReduced (pullback (pullback.fst f g) (Sigma.desc p)) from
    IsSchemeTheoreticallyDominant.isReduced (pullback.fst (pullback.fst f g) (Sigma.desc p))
  have hP (i : ι) : IsPullback (pullback.snd (p i) (pullback.fst f g))
      (pullback.fst (p i) (pullback.fst f g)) (pullback.fst f g) (p i) :=
    (IsPullback.of_hasPullback _ _).flip
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct W))
    p (Sigma.desc p) (pullback.fst f g) _ _ hP (coproductIsCoproduct _)
  have hW (i : ι) : IsReduced (pullback (p i) (pullback.fst f g)) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso f g (p i)).hom
  have : IsReduced (∐ fun i => pullback (p i) (pullback.fst f g)) :=
    @IsReduced.of_openCover _ (sigmaOpenCover _) hW
  exact @isReduced_of_isOpenImmersion _ _ H.isoPullback.inv _ this

/-- **Geometric reducedness over a field, tested on a jointly dense finite family.** Let `S` be a
one-point integral scheme (the spectrum of a field) and `f : X ⟶ S` a morphism from a reduced
scheme. If finitely many quasi-compact morphisms `pᵢ : Wᵢ ⟶ X` have jointly dense image and each
`Wᵢ` is geometrically reduced over `S`, then `X` is geometrically reduced over `S`. -/
theorem geometricallyReduced_of_dense_iUnion_range {ι : Type u} [Finite ι]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral S] [Subsingleton S] [IsReduced X]
    {W : ι → Scheme.{u}} (p : ∀ i, W i ⟶ X) [∀ i, QuasiCompact (p i)]
    (hp : Dense (⋃ i, Set.range (p i)))
    (hgr : ∀ i, GeometricallyReduced (p i ≫ f)) :
    GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsReduced (pullback f y) :=
    isReduced_pullback_of_dense_iUnion_range f y p hp fun i =>
      (hgr i).geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  exact isReduced_of_isOpenImmersion h.isoPullback.hom

/-- Schemes mapping onto the irreducible components of `X` have jointly dense image. -/
private lemma dense_iUnion_range_of_range_eq {X : Scheme.{u}}
    {W : irreducibleComponents X → Scheme.{u}} (p : ∀ Z, W Z ⟶ X)
    (h : ∀ Z, Set.range (p Z) = Z.1) : Dense (⋃ Z, Set.range (p Z)) := by
  convert dense_univ
  refine Set.eq_univ_iff_forall.2 fun x => Set.mem_iUnion.2
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [h]
  exact mem_irreducibleComponent

/-- **Reducedness of a flat base change, tested on the irreducible components.** Let `X` be a
reduced scheme with finitely many irreducible components, `f : X ⟶ S` a morphism and
`g : Y ⟶ S` a flat morphism. If the base change to `Y` of every irreducible component of `X`,
with its reduced induced structure, is reduced, then `X ×_S Y` is reduced. -/
theorem isReduced_pullback_of_irreducibleComponents {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [Flat g] [IsReduced X] [Finite (irreducibleComponents X)]
    (hred : ∀ Z : irreducibleComponents X,
      IsReduced (pullback ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ f) g)) :
    IsReduced (pullback f g) :=
  isReduced_pullback_of_dense_iUnion_range f g _
    (dense_iUnion_range_of_range_eq _ fun Z => by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl) hred

/-- **A reduced scheme over a field whose irreducible components are geometrically reduced is
geometrically reduced.** Let `S` be a one-point integral scheme (the spectrum of a field) and
`X` a reduced scheme over `S` with finitely many irreducible components. If every irreducible
component of `X`, with its reduced induced structure, is geometrically reduced over `S`, then so
is `X`. -/
@[ega "IV 11.10.7" "special case"]
theorem geometricallyReduced_of_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral S] [Subsingleton S] [IsReduced X] [Finite (irreducibleComponents X)]
    (hgr : ∀ Z : irreducibleComponents X,
      GeometricallyReduced ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ f)) :
    GeometricallyReduced f :=
  geometricallyReduced_of_dense_iUnion_range f _
    (dense_iUnion_range_of_range_eq _ fun Z => by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl) hgr

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- The closed immersion of the component attached to `Z` into the special fibre has image `Z`. -/
theorem range_specialFiberComponentι (Z : irreducibleComponents S.specialFiber) :
    Set.range (S.specialFiberComponentι Z) = Z.1 := by
  have h := congrArg (fun φ : (S.specialFiberComponentIdeal Z).subscheme ⟶ S.X => Set.range φ)
    (S.specialFiberComponentι_specialFiberι Z)
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι] at h
  rw [S.coe_support_specialFiberComponentIdeal Z] at h
  exact S.specialFiberι.isClosedEmbedding.injective.image_injective h

end RegularModelSituation

namespace RegularProperModelSituation

/-- **A reduced special fibre with smooth components is geometrically reduced.** If the special
fibre `X_k` of a regular proper model is reduced and each of its irreducible components, with
its reduced induced structure, is smooth over the residue field `k`, then `X_k` is geometrically
reduced over `k`. -/
theorem geometricallyReduced_specialFiberToSpec_of_smooth (S : RegularProperModelSituation.{u})
    [IsReduced S.specialFiber]
    (hsm : ∀ Z : irreducibleComponents S.specialFiber,
      Smooth (S.specialFiberComponentToSpec Z)) :
    GeometricallyReduced S.specialFiberToSpec := by
  refine geometricallyReduced_of_dense_iUnion_range _ S.specialFiberComponentι ?_ fun Z => ?_
  · exact dense_iUnion_range_of_range_eq _ S.range_specialFiberComponentι
  · have := hsm Z
    exact geometricallyReduced_of_smooth (S.specialFiberComponentToSpec Z)

/-- **The base change of a reduced special fibre with smooth components to a field extension of
`k` is reduced.** If the special fibre `X_k` of a regular proper model is reduced and each of
its irreducible components, with its reduced induced structure, is smooth over the residue
field `k`, then `X_k ×_k L` is reduced for every field extension `L` of `k`. -/
theorem isReduced_pullback_specialFiberToSpec_of_smooth (S : RegularProperModelSituation.{u})
    [IsReduced S.specialFiber]
    (hsm : ∀ Z : irreducibleComponents S.specialFiber, Smooth (S.specialFiberComponentToSpec Z))
    (L : Type u) [Field L] [Algebra S.k L] :
    IsReduced (pullback S.specialFiberToSpec (Spec.map (CommRingCat.ofHom (algebraMap S.k L)))) :=
  (S.geometricallyReduced_specialFiberToSpec_of_smooth hsm).geometrically_isReduced _ _ _
    (.of_hasPullback _ _)

end RegularProperModelSituation

end Stacks.Models
