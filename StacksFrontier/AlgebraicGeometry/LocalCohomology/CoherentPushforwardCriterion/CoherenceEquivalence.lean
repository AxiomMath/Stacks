module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CoherenceFromPointClosures

/-!
# The coherence criterion of Stacks 0BJZ

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open subscheme and `F` a
coherent `𝒪_U`-module. For `x ∈ U` write `i_x : W_x → U` for the integral closed subscheme with
generic point `x`. This file completes [Stacks, Tag 0BJZ]: `j_* F` is coherent if and only if
`j_* i_{x,*} 𝒪_{W_x}` is coherent for every `x ∈ Ass(F)`.

All declarations named below without a namespace lie in
`Stacks.AlgebraicGeometry.CoherenceFromPointClosures`. The implication (1) ⇒ (2) is
`isCoherent_pushforward_of_forall_isAssociatedPoint'`. What is added here is the implication
(2) ⇒ (1) without hypotheses on `U`: the comparison morphism `i_{x,*} 𝒪_{W_x} ⟶ F` of
`Stacks.AlgebraicGeometry.PointClosureComparison.exists_mono_of_isSimpleModule` exists only over a
Noetherian quasi-affine scheme, and the source's reduction to an affine base is what supplies those
two conditions.

## Main results

* `isCoherent_pushforward_pointClosure_of_isAssociatedPoint'`:
  **[Stacks, Tag 0BJZ], the implication (2) ⇒ (1)**, for an arbitrary open subscheme of a
  locally Noetherian scheme.
* `isCoherent_pushforward_iff_forall_isAssociatedPoint`:
  **[Stacks, Tag 0BJZ]**, the equivalence of the source's (1) and (2).

## Implementation notes

Coherence of `j_* i_{x,*} 𝒪_{W_x}` is local on `X`
(`isCoherent_pushforward_of_forall_affineOpens`), so it is enough to prove it over an affine open
`V ⊆ X`, where `j^{-1}V` is Noetherian and quasi-affine. Over `V` the two sides of the comparison
morphism are the *restrictions* `(i_{x,*} 𝒪_{W_x})|_{j^{-1}V}` and `F|_{j^{-1}V}`, and the
restriction of a point-closure sheaf is never identified with a point-closure sheaf of `j^{-1}V`.
That identification is avoided by running the comparison at the level of generality of
`Stacks.AlgebraicGeometry.PointClosureComparison.exists_mono_of_isSimpleModule`, which asks only
that the source be coherent, have a simple stalk at `x`, and have no associated point other than
`x`. All three survive restriction: coherence by `AlgebraicGeometry.Modules.isCoherent_restrict`,
simplicity by `isSimpleModule_stalk_restrict`, and the associated points by
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff`.

The same transfer of associated points settles the case `x ∉ j^{-1}V`: an associated point of
`(i_{x,*} 𝒪_{W_x})|_{j^{-1}V}` would lie over an associated point of `i_{x,*} 𝒪_{W_x}`, hence
over `x` itself, so there is none, and a quasi-coherent module on a locally Noetherian scheme
with no associated points is zero by [Stacks, Tag 05AG].

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 05AG](https://stacks.math.columbia.edu/tag/05AG)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherenceFromPointClosures

open PointClosureComparison Stacks.AlgebraicGeometry.CodimensionOneObstruction in
/-- **The affine piece of [Stacks, Tag 0BJZ], the implication (2) ⇒ (1).** Over an affine open
`V` of `X` the restriction `j^{-1}V` of the open subscheme is Noetherian and quasi-affine, so the
comparison morphism exists there — between the restrictions of `i_{x,*} 𝒪_{W_x}` and of `F`. -/
private theorem isCoherent_pushforward_pointClosure_restrict_of_isAssociatedPoint
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    (F : U.Modules) [F.IsQuasicoherent] (hx : Stacks.Divisors.IsAssociatedPoint F x)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent)
    (V : X.Opens) [IsAffine V.toScheme] :
    ((Scheme.Modules.pushforward (j ∣_ V)).obj
      ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι)).IsCoherent := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : AlgebraicGeometry.IsNoetherian V.toScheme := {}
  have : NoetherianSpace V.toScheme := AlgebraicGeometry.IsNoetherian.noetherianSpace
  have hNS : NoetherianSpace (j ⁻¹ᵁ V).toScheme :=
    (j ∣_ V).isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace (j ⁻¹ᵁ V).toScheme := hNS.compactSpace
  have : IsLocallyNoetherian (j ⁻¹ᵁ V).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (j ⁻¹ᵁ V).ι
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ V).toScheme := {}
  have : (j ⁻¹ᵁ V).toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion (j ∣_ V)
  have hGcoh : ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι).IsCoherent :=
    have := isCoherent_pointClosureStructureSheaf x
    AlgebraicGeometry.Modules.isCoherent_restrict _ (j ⁻¹ᵁ V)
  have hGq : ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι).IsQuasicoherent :=
    have := isQuasicoherent_pointClosureStructureSheaf x
    Scheme.Modules.isQuasicoherent_restrictFunctor (j ⁻¹ᵁ V).ι _
  have hover : ∀ y : (j ⁻¹ᵁ V).toScheme,
      y ∈ Stacks.Divisors.associatedPoints
        ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι) → (y.1 : U) = x := fun y hy =>
    associatedPoints_pointClosureStructureSheaf_subset x
      ((isAssociatedPoint_restrict_iff (j ⁻¹ᵁ V).ι _ y).mp hy)
  by_cases hxV : x ∈ j ⁻¹ᵁ V
  · have hFq : (F.restrict (j ⁻¹ᵁ V).ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor (j ⁻¹ᵁ V).ι F
    have hFpush :
        ((Scheme.Modules.pushforward (j ∣_ V)).obj (F.restrict (j ⁻¹ᵁ V).ι)).IsCoherent :=
      have := hF
      have : (((Scheme.Modules.pushforward j).obj F).restrict V.ι).IsCoherent :=
        AlgebraicGeometry.Modules.isCoherent_restrict _ V
      CoherentDevissage.isCoherent_of_iso
        (show ((Scheme.Modules.pushforward (j ∣_ V)).obj (F.restrict (j ⁻¹ᵁ V).ι)) ≅
            (((Scheme.Modules.pushforward j).obj F).restrict V.ι) from
          ((AffinePushforward.restrictPushforwardIso j V).app F).symm)
    obtain ⟨φ, hφ⟩ := exists_mono_of_isSimpleModule
      ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι) (F.restrict (j ⁻¹ᵁ V).ι)
      (⟨x, hxV⟩ : (j ⁻¹ᵁ V).toScheme)
      (isSimpleModule_stalk_restrict (j ⁻¹ᵁ V) _ ⟨x, hxV⟩
        (isSimpleModule_stalk_pointClosureStructureSheaf x))
      (fun y hy => Subtype.ext (hover y hy))
      ((isAssociatedPoint_restrict_iff (j ⁻¹ᵁ V).ι F ⟨x, hxV⟩).mpr hx)
    have := hφ
    exact Stacks.AlgebraicGeometry.PushforwardAssociatedPoints.isCoherent_pushforward_of_mono
      (j ∣_ V) φ hFpush
  · have hz : Limits.IsZero ((pointClosureStructureSheaf x).restrict (j ⁻¹ᵁ V).ι) := by
      refine (AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty _ _).mpr
        (Set.eq_empty_iff_forall_notMem.mpr fun y hy => hxV ?_)
      exact hover y hy ▸ y.2
    exact CoherentDevissage.isCoherent_of_isZero
      (Functor.map_isZero (Scheme.Modules.pushforward (j ∣_ V)) hz)

open PointClosureComparison in
/-- **[Stacks, Tag 0BJZ], the implication (2) ⇒ (1).** Let `X` be a locally Noetherian scheme,
let `j : U ⟶ X` be the inclusion of an open subscheme, let `F` be a quasi-coherent `𝒪_U`-module
and let `x` be a point associated to `F`. If `j_* F` is coherent then so is
`j_* i_{x,*} 𝒪_{W_x}`.

Coherence of a direct image is local on the target, and over an affine open of `X` the open
subscheme becomes Noetherian and quasi-affine, which is what the construction of the comparison
morphism needs. -/
theorem isCoherent_pushforward_pointClosure_of_isAssociatedPoint' {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U) (F : U.Modules)
    [F.IsQuasicoherent] (hx : Stacks.Divisors.IsAssociatedPoint F x)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent :=
  isCoherent_pushforward_of_forall_affineOpens j _ fun V =>
    have : IsAffine (V : X.Opens).toScheme := V.2
    isCoherent_pushforward_pointClosure_restrict_of_isAssociatedPoint j x F hx hF (V : X.Opens)

open PointClosureComparison in
/-- **[Stacks, Tag 0BJZ].** Let `X` be a locally Noetherian scheme, let `j : U ⟶ X` be the
inclusion of an open subscheme and let `F` be a coherent `𝒪_U`-module. For `x ∈ U` let
`i_x : W_x → U` be the integral closed subscheme with generic point `x`. Then the following are
equivalent:

1. for all `x ∈ Ass(F)` the `𝒪_X`-module `j_* i_{x,*} 𝒪_{W_x}` is coherent;
2. `j_* F` is coherent. -/
@[stacks 0BJZ]
theorem isCoherent_pushforward_iff_forall_isAssociatedPoint {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent] :
    (∀ x ∈ Stacks.Divisors.associatedPoints F,
        ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent) ↔
      ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  have : F.IsQuasicoherent := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact ⟨isCoherent_pushforward_of_forall_isAssociatedPoint' j F,
    fun hF x hx => isCoherent_pushforward_pointClosure_of_isAssociatedPoint' j x F hx hF⟩

end Stacks.AlgebraicGeometry.CoherenceFromPointClosures

end
