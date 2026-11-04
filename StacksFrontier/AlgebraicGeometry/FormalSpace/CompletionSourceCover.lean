module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionChartSquare
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianChartLocality

/-!
# A covering of the completion of a morphism by completed charts

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S` and let `T ⊆ |X|` be a closed subset with inverse image `T' ⊆ |X'|`. This file
carries out the reduction to the affine case in the source's proofs of **Stacks 0GDH** and
**Stacks 0AR2**: given étale coverings `{W_i ⟶ X}` and `{W'_k ⟶ X'}` by spectra of Noetherian
rings, each `W'_k` lying over some `W_{ι k}` compatibly with `f`, the completed charts
`(W'_k)_{/T'} ⟶ X'_{/T'}` form a covering as in Definition 0AIM, each member factors through the
completed chart `(W_{ι k})_{/T} ⟶ X_{/T}`, and the chart condition of Stacks 0ANG for a property
`P` of arrows of `WAdm^{Noeth}` holds on the factorization as soon as `P` holds on the induced map
of adic completions, and the completed charts are formal spectra of Noetherian adic rings. That is
condition (4) of **Stacks 0GCZ** for `f_{/T}` when `P` is rig-étaleness and condition (4) of
**Stacks 0GCQ** when `P` is rig-smoothness, in the form
`AlgebraicGeometry.FormalSpace.CorrespondsToNoetherianMapAfterSourceCover`.

## Main results

* `AlgebraicGeometry.FormalSpace.completionSheafMap_comp_completionSheafMap_of_comp_eq`: the
  completion of a commutative square of presheaves is a commutative square.
* `AlgebraicGeometry.FormalSpace.correspondsToNoetherianMapAfterSourceCover_completionSheafMap`:
  condition (4) of Stacks 0GCZ and Stacks 0GCQ for `f_{/T}` and the property `P`.

## Implementation notes

The charts are given in the shape `Spec A ⟶ X` of `AlgebraicGeometry.FormalSpace.affineOver`
read in the value universe of the formal algebraic spaces, which is the shape in which
`AlgebraicGeometry.FormalSpace.completionSheafMap_atlas_isRepresentable_etale_surjective`
consumes them, and each `W'_k ⟶ W_{ι k}` is the spectrum of a ring map `φ k`, so that Stacks
0GBA (2) identifies the completed map with the formal spectrum of the induced map of adic
completions (`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_completionSheafMap_spec`).

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Completion of a commutative square.** If `g ≫ a = a' ≫ f` for morphisms of presheaves
`g : W' ⟶ W`, `a : W ⟶ X`, `a' : W' ⟶ X'` and `f : X' ⟶ X`, then the completed square along a
set `T` of points of `X` commutes, the source of the completion of `g` being transported along
the equality of the two inverse images of `T` in `W'`. -/
theorem completionSheafMap_comp_completionSheafMap_of_comp_eq
    {W' W X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W' ⟶ W) (a : W ⟶ X) (a' : W' ⟶ X')
    (f : X' ⟶ X) (hsq : g ≫ a = a' ≫ f) (T : Set (Space.points B S hS X))
    (hpts : Space.pointsMap B S hS W' a' ⁻¹' (Space.pointsMap B S hS X' f ⁻¹' T) =
      Space.pointsMap B S hS W' g ⁻¹' (Space.pointsMap B S hS W a ⁻¹' T)) :
    Space.completionSheafMap B S hS a' (Space.pointsMap B S hS X' f ⁻¹' T) ≫
        Space.completionSheafMap B S hS f T =
      (eqToHom (congrArg (Space.completionSheaf B S hS W') hpts) ≫
        Space.completionSheafMap B S hS g (Space.pointsMap B S hS W a ⁻¹' T)) ≫
        Space.completionSheafMap B S hS a T := by
  have hmono := Space.mono_completionSheafInclusion B S hS X T
  rw [← cancel_mono (Space.completionSheafInclusion B S hS X T)]
  simp only [Category.assoc]
  rw [← (Space.isPullback_completionSheafMap B S hS f T).w,
    ← (Space.isPullback_completionSheafMap B S hS a T).w,
    ← Category.assoc (Space.completionSheafMap B S hS g _),
    ← (Space.isPullback_completionSheafMap B S hS g _).w,
    ← Category.assoc (Space.completionSheafMap B S hS a' _),
    ← (Space.isPullback_completionSheafMap B S hS a' _).w]
  simp only [Category.assoc, ← Space.sheafifiedULiftMap_comp, hsq]
  rw [← Category.assoc (eqToHom _), Space.completionSheafInclusion_transport B S hS W' hpts]

attribute [local instance] Space.pointTopology adicCompletionModuleTopology
  isTopologicalRing_adicCompletionModuleTopology isLinearTopology_adicCompletionModuleTopology

/-- The completion of a Noetherian affine chart along the inverse image of a closed set is
Noetherian. -/
private theorem isNoetherian_completionSheaf_preimage {A : Type u} [CommRing A] [IsNoetherianRing A]
    {hA : B.Contains (AlgebraicGeometry.Spec (.of A))} {str : AlgebraicGeometry.Spec (.of A) ⟶ S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    {T : Set (Space.points B S hS X)} (hT : IsClosed T) :
    IsNoetherian B S hS (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA str))
      (Space.pointsMap B S hS _ a ⁻¹' T)) :=
  isNoetherian_completionSheaf B S hS _ _ _ (hT.preimage (Space.continuous_pointsMap B S hS a))

/-- **The completed charts satisfy condition (4) of Stacks 0GCZ and Stacks 0GCQ.** Let
`f : X' ⟶ X` be a morphism of algebraic spaces over `S` and `T ⊆ |X|` a closed subset. Let
`{Spec A_i ⟶ X}` be an étale covering of `X` by spectra of Noetherian rings and
`{Spec A'_k ⟶ X'}` one of `X'`, each chart `Spec A'_k` mapping to a chart `Spec A_{ι k}` by the
spectrum of a ring map `φ k : A_{ι k} → A'_k` compatibly with `f`, all read in the value universe
of the formal algebraic spaces. Let `P` be a property of arrows of `WAdm^{Noeth}` invariant
under isomorphism of source and target, holding on the map of adic completions
`A_{ι k}^∧ → (A'_k)^∧` along every ideal cutting out the inverse image of `T` in `Spec A_{ι k}`.
Then the completed charts `(Spec A'_k)_{/T'} ⟶ X'_{/T'}` are a covering as in Definition 0AIM
whose members factor through the completed charts `(Spec A_{ι k})_{/T} ⟶ X_{/T}` by maps
corresponding to `P`-maps in `WAdm^{Noeth}`: both completed charts are Noetherian (the proof of
Stacks 0AQ1), and every Noetherian presentation of the map between them has `P` by Stacks
0GBA (2). -/
theorem correspondsToNoetherianMapAfterSourceCover_completionSheafMap
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPiso : PropertyInvariantUnderRingEquiv TopologicalRing.IsNoetherianAdic P)
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T)
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)] [∀ i, IsNoetherianRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    {Ik : Type (u + 1)} {A' : Ik → Type u} [∀ k, CommRing (A' k)]
    [∀ k, IsNoetherianRing (A' k)] (ι : Ik → Ix) (φ : ∀ k, A (ι k) →+* A' k)
    (hA' : ∀ k, B.Contains (AlgebraicGeometry.Spec (.of (A' k))))
    (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X')
    (ha' : ∀ k, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a' k)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a' k)).hom hai)
    (hcov' : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun k ↦ Space.sheafifiedULiftMap B S hS (a' k)))
    (h : ∀ k, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k)) ⟶
      affineOver B S hS (hA (ι k)) (str (ι k)))
    (hh : ∀ k, h k = Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k)))
    (hsq : ∀ k, yoneda.map (h k) ≫ a (ι k) = a' k ≫ f)
    (hP : ∀ k (J : Ideal (A (ι k))),
      Space.pointsMap B S hS _ (a (ι k)) ⁻¹' T =
        zeroLocusPoints B S hS (hA (ι k)) (str (ι k)) J →
      P (adicCompletionMap (φ k) J (J.map (φ k)) le_rfl)) :
    CorrespondsToNoetherianMapAfterSourceCover B S hS P
      (Space.completionSheafMap B S hS f T) := by
  let T' := Space.pointsMap B S hS X' f ⁻¹' T
  have hT' : IsClosed T' := hT.preimage (Space.continuous_pointsMap B S hS f)
  obtain ⟨hrep', hsurj'⟩ :=
    completionSheafMap_atlas_isRepresentable_etale_surjective hX' T' hA' _ a' ha' hcov'
  obtain ⟨hrep, -⟩ := completionSheafMap_atlas_isRepresentable_etale_surjective hX T hA str a ha
    hcov
  have hpts : ∀ k, Space.pointsMap B S hS _ (a' k) ⁻¹' T' =
      Space.pointsMap B S hS _ (yoneda.map (h k)) ⁻¹'
        (Space.pointsMap B S hS _ (a (ι k)) ⁻¹' T) := fun k ↦ by
    simp only [T', ← Set.preimage_comp, ← Space.pointsMap_comp, hsq]
  refine ⟨Ik, fun k ↦ Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))))
      (Space.pointsMap B S hS _ (a' k) ⁻¹' T'),
    fun k ↦ Space.completionSheafMap B S hS (a' k) T', ⟨fun k ↦ ?_, hrep', hsurj'⟩, fun k ↦ ?_⟩
  · exact (isNoetherian_completionSheaf_preimage (a' k) hT').1.1
  · obtain ⟨J, hJ⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS (hA (ι k)) (str (ι k))
      (Space.pointsMap B S hS _ (a (ι k)) ⁻¹' T)
      (hT.preimage (Space.continuous_pointsMap B S hS (a (ι k))))
    refine ⟨Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA (ι k)) (str (ι k))))
        (Space.pointsMap B S hS _ (a (ι k)) ⁻¹' T),
      Space.completionSheafMap B S hS (a (ι k)) T,
      eqToHom (congrArg (Space.completionSheaf B S hS _) (hpts k)) ≫
        Space.completionSheafMap B S hS (yoneda.map (h k))
          (Space.pointsMap B S hS _ (a (ι k)) ⁻¹' T),
      (isNoetherian_completionSheaf_preimage (a (ι k)) hT).1.1,
      hrep (ι k),
      completionSheafMap_comp_completionSheafMap_of_comp_eq _ _ _ _ (hsq k) T (hpts k), ?_⟩
    refine correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap_of_isNoetherian ?_
      (isNoetherian_completionSheaf_preimage (a' k) hT')
      (isNoetherian_completionSheaf_preimage (a (ι k)) hT)
    refine HasPropertyOnAffineChartMap.iso_hom_comp
      (eqToIso (congrArg (Space.completionSheaf B S hS _) (hpts k))) ?_
    have key : ∀ (Z : Set (Space.points B S hS (yoneda.obj
        (affineOver B S hS (hA (ι k)) (str (ι k)))))),
        Z = zeroLocusPoints B S hS (hA (ι k)) (str (ι k)) J →
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic P
          (Space.completionSheafMap B S hS (yoneda.map (h k)) Z) := by
      rintro Z rfl
      exact hasPropertyOnAffineChartMap_completionSheafMap_spec B S hS (hA (ι k)) (hA' k)
        (str (ι k)) (φ k) J (h k) P hPiso (hh k) (hP k J hJ)
    exact key _ hJ

end AlgebraicGeometry.FormalSpace

end
