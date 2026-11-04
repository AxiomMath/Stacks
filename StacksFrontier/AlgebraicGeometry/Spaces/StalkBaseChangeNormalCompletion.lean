module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularProperSurjectionNormalCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSpaceStalkBaseChange
public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion

/-!
# Normal completions of the local rings of a normal space with a regular proper cover

Let `N` be a normal algebraic space over a scheme `S` whose étale charts are locally Noetherian,
and let `g : X ⟶ N` be a proper surjective morphism from a regular algebraic space. Then

* for every étale chart `V ⟶ N` by an affine scheme and every point `v` of `V`, the completion of
  the local ring `𝒪_{V, v}` is a normal ring;
* if `N` is decent, the completion of the henselian local ring `𝒪^h_{N, y}` of
  [Stacks, Tag 0BGW] is a normal ring at every point `y` of `N`.

This is the step "`X ×_Y Spec(𝒪^h_{Y^ν, y_i})` is a regular alteration of
`Spec(𝒪^h_{Y^ν, y_i})` (some details omitted)" of the proof of [Stacks, Tag 0BHY], made precise.

## The argument

Put `A = 𝒪_{V, v}`, a Noetherian local normal domain. The canonical morphism
`τ : Spec A ⟶ V` is a flat preimmersion. The base change `X_V = X ×_N V` is étale over `X`, hence
regular, and proper surjective over `V`; its base change `X_A = X_V ×_V Spec A` is proper and
surjective over `Spec A`, and regular by
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_pullback_of_flat_isPreimmersion`.

`X_A` is an algebraic space over `S` with a morphism to `Spec A`. By the equivalence of
[Stacks, Tag 04SG] it is the lower-shriek extension of an algebraic space `F` over `Spec A`
(`AlgebraicGeometry.Space.exists_relocalize_arrowIso_of_isAlgebraicSpace`); properness,
surjectivity and regularity of `F` over `Spec A` are read off those of `X_A`. Now
`AlgebraicGeometry.Space.isNormalRing_adicCompletion_of_isProper_of_isSurjective_of_isRegular`
makes the completion of `A` normal.

The henselian local ring is a henselization of `𝒪_{V, v}` for an affine elementary étale
neighbourhood `(V, v)` of `y` ([Stacks, Tag 0EMY]), and a local ring and its henselization have
isomorphic completions, so the second assertion follows from the first. This is how the universe
gap is crossed: the henselian local ring lives in `Type (u + 1)`, but its completion is
isomorphic to the completion of the `u`-small ring `𝒪_{V, v}`, to which the results over the
site of `Spec A` apply.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_isSurjective_relocalizeMap`: surjectivity descends
  along the lower-shriek extension of [Stacks, Tag 03I5].
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_of_relocalize`: an étale-local property of the
  lower-shriek extension of an algebraic space holds for the space itself.
* `AlgebraicGeometry.Space.isNormalRing_adicCompletion_stalk_of_isProper_of_isSurjective`: the
  completion of the local ring of an affine étale chart is normal.
* `AlgebraicGeometry.Space.isNormalRing_adicCompletion_henselianLocalRing_of_isProper`: the
  completion of the henselian local ring is normal.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BHU](https://stacks.math.columbia.edu/tag/0BHU)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

/-! ### Descending properties along the lower-shriek extension -/

section Relocalize

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **Surjectivity descends along the lower-shriek extension.** A morphism of presheaves on the
big fppf site of `W` is surjective as soon as its lower-shriek extension along `h : W ⟶ S` is:
the two maps on points are conjugate along the bijections
`AlgebraicGeometry.Space.relocalizedPointsMap`. -/
theorem isSurjective_of_isSurjective_relocalizeMap {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : F ⟶ G) (hk : IsSurjective B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsSurjective B W hW k := by
  intro y
  obtain ⟨x', hx'⟩ := hk (relocalizedPointsMap B W S hW hS h G y)
  obtain ⟨x, rfl⟩ := relocalizedPointsMap_surjective B W S hW hS h F x'
  refine ⟨x, relocalizedPointsMap_injective B W S hW hS h G ?_⟩
  rw [relocalizedPointsMap_naturality, hx']

/-- **An étale-local property descends along the lower-shriek extension.** If the lower-shriek
extension of an algebraic space `F` over `W` along `h : W ⟶ S` has an étale-local property of
schemes, then so has `F`: the extension of an étale chart of `F` is an étale chart of the
extension by the same scheme. -/
theorem hasEtaleLocalProperty_of_relocalize (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B W hW F)
    (hP : HasEtaleLocalProperty B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) P) :
    HasEtaleLocalProperty B W hW F P :=
  (exists_atlas_iff_forall_etale B W hW F P hF).mpr fun _ a ha =>
    (exists_atlas_iff_forall_etale B S hS _ P (isAlgebraicSpace_viewOver B W S hW hS h F hF)).mp
      hP _ (relocalizeChart B W S hW hS h a)
      ((presheaf_relocalizeChart_iff B W S hW hS h _ a).mpr ha)

/-- **Proper surjective regular covers descend along the lower-shriek extension.** A proper
surjective morphism `p : Y ⟶ W` from a regular algebraic space over `S` is, up to isomorphism,
the lower-shriek extension of a proper surjective morphism to `W` from a regular algebraic space
over `W`. -/
theorem exists_isProper_isSurjective_isRegular_of_relocalize
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj (Over.mk h)) (hpp : IsProper B S hS p) (hps : IsSurjective B S hS p)
    (hYreg : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsRegular T)) :
    ∃ (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B W hW F),
      IsProper B W hW (toYonedaId B W hW F) ∧ IsSurjective B W hW (toYonedaId B W hW F) ∧
      HasEtaleLocalProperty B W hW F (fun T : Scheme.{u} => IsRegular T) := by
  obtain ⟨F, hF, θ, hθiso, hθ⟩ :=
    exists_relocalize_arrowIso_of_isAlgebraicSpace B S hS W hW h hY p
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · refine (isProper_relocalizeToYoneda_iff B W S hW hS h F hF).1 ?_
    rw [← hθ]
    exact (isProper_isIso_comp_iff B S hS θ _).2 hpp
  · refine isSurjective_of_isSurjective_relocalizeMap B W S hW hS h _ ?_
    have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
    have h₁ : IsSurjective B S hS (OverShriek.relocalizeToYoneda h F) := by
      rw [← hθ]
      exact isSurjective_comp B S hS (bijective_pointsMap_of_isIso B S hS θ).2 hps
    rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F] at h₁
    simpa using isSurjective_comp B S hS h₁ (bijective_pointsMap_of_isIso B S hS
      (inv (OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hW))))))).2
  · refine hasEtaleLocalProperty_of_relocalize B W S hW hS h _ hF ?_
    exact hasEtaleLocalProperty_of_isEtale B S hS (isAlgebraicSpace_viewOver B W S hW hS h F hF) hY
      (isEtale_of_isIso B S hS θ) hYreg

end Relocalize

/-! ### The local rings of an étale chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The second projection of a base change of a proper morphism of algebraic spaces is proper. -/
theorem isProper_pullback_snd {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y) (hf : IsProper B S hS f) :
    IsProper B S hS (pullback.snd f g) := by
  rw [← pullbackSymmetry_hom_comp_fst]
  exact (isProper_isIso_comp_iff B S hS _ _).2 (isProper_pullback_fst B S hS hX hY hZ f g hf)

/-- **Normal completion of the local rings of an affine étale chart.** Let `N` be a normal
algebraic space over `S` whose étale charts are locally Noetherian, let `g : X ⟶ N` be proper and
surjective with `X` regular, let `b : V ⟶ N` be an étale chart by an affine scheme and let `v` be
a point of `V`. Then the completion of `𝒪_{V, v}` is a normal ring. -/
theorem isNormalRing_adicCompletion_stalk_of_isProper_of_isSurjective
    {N X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hN : IsAlgebraicSpace B S hS N)
    (hX : IsAlgebraicSpace B S hS X) (hNnorm : IsNormal B S hS N)
    (hNnoeth : HasEtaleLocalProperty B S hS N (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (g : X ⟶ N) (hgp : IsProper B S hS g) (hgs : IsSurjective B S hS g)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ N) (hb : IsEtale B S hS b)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    IsNormalRing (AdicCompletion
      (IsLocalRing.maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v))
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)) := by
  let := B.hasPullbacks_schemes
  let Tsch := BigFppfOver.toScheme B S hS
  let Vs := Tsch.obj V
  have hbP := (isEtale_iff_presheaf_of_yoneda B S hS b).mp hb
  have : IsLocallyNoetherian Vs :=
    (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnoeth V b hbP
  have : _root_.AlgebraicGeometry.IsNormal Vs :=
    (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnorm V b hbP
  have : _root_.AlgebraicGeometry.IsNoetherian Vs := {}
  let A := Vs.presheaf.stalk v
  have : IsIntegrallyClosed A := IsNormal.stalk_normal v
  have hA : B.Contains (Spec (.of A)) := @BigFppfSite.contains_spec_stalk B Vs V.left.2 _ v
  let hmap : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk (Vs.fromSpecStalk v ≫ V.hom.hom)
  let T : BigFppfOver B S hS := Over.mk hmap
  let τ : T ⟶ V := Over.homMk (ObjectProperty.homMk (Vs.fromSpecStalk v)) rfl
  have : Flat (Tsch.map τ) := flat_fromSpecStalk Vs v
  have : IsPreimmersion (Tsch.map τ) := inferInstanceAs (IsPreimmersion (Vs.fromSpecStalk v))
  have : IsLocallyNoetherian (Tsch.obj T) := inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hXV : IsAlgebraicSpace B S hS (pullback g b) := isAlgebraicSpace_pullback B S hS g b hX hV hN
  have hfst : IsEtale B S hS (pullback.fst g b) := isEtale_pullback_fst B S hS hX hN hV g b hb
  have hXVreg : HasEtaleLocalProperty B S hS (pullback g b) (fun T : Scheme.{u} => IsRegular T) :=
    hasEtaleLocalProperty_of_isEtale B S hS hXV hX hfst hXreg
  let q := pullback.snd g b
  have hqp : IsProper B S hS q := isProper_pullback_snd B S hS hX hN hV g b hgp
  have hqs : IsSurjective B S hS q := isSurjective_pullback_snd B S hS hX hN hV g b hgs
  have hXA : IsAlgebraicSpace B S hS (pullback q (yoneda.map τ)) :=
    isAlgebraicSpace_pullback B S hS q (yoneda.map τ) hXV hT hV
  have hXAreg := hasEtaleLocalProperty_isRegular_pullback_of_flat_isPreimmersion B S hS hXV q
    hqp.2.1.1 τ hXVreg
  obtain ⟨F, hF, hFp, hFs, hFreg⟩ := exists_isProper_isSurjective_isRegular_of_relocalize B
    (Spec (.of A)) S hA hS hmap hXA (pullback.snd q (yoneda.map τ))
    (isProper_pullback_snd B S hS hXV hV hT q (yoneda.map τ) hqp)
    (isSurjective_pullback_snd B S hS hXV hV hT q (yoneda.map τ) hqs) hXAreg
  exact isNormalRing_adicCompletion_of_isProper_of_isSurjective_of_isRegular A B hA F hF
    (toYonedaId B (Spec (.of A)) hA F) hFp hFs hFreg

/-- **Normal completion of the henselian local rings.** Let `N` be a decent normal algebraic
space over `S` whose étale charts are locally Noetherian, and let `g : X ⟶ N` be proper and
surjective with `X` regular. Then at every point `y` of `N` the completion of the henselian local
ring `𝒪^h_{N, y}` along its maximal ideal is a normal ring. -/
theorem isNormalRing_adicCompletion_henselianLocalRing_of_isProper
    {N X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hN : IsAlgebraicSpace B S hS N)
    (hNdec : IsDecentSpace B S hS N)
    (hX : IsAlgebraicSpace B S hS X) (hNnorm : IsNormal B S hS N)
    (hNnoeth : HasEtaleLocalProperty B S hS N (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (g : X ⟶ N) (hgp : IsProper B S hS g) (hgs : IsSurjective B S hS g)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (y : points B S hS N) :
    letI := henselianLocalRing_isLocalRing B S hS N hN y hNdec
    IsNormalRing (AdicCompletion
      (IsLocalRing.maximalIdeal (henselianLocalRing B S hS N hN y hNdec : Type (u + 1)))
      (henselianLocalRing B S hS N hN y hNdec : Type (u + 1))) := by
  let := henselianLocalRing_isLocalRing B S hS N hN y hNdec
  obtain ⟨E, hEaff, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hN hNdec y
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj E.scheme) := hEaff
  have hstalk := isNormalRing_adicCompletion_stalk_of_isProper_of_isSurjective B S hS hN hX
    hNnorm hNnoeth g hgp hgs hXreg E.scheme E.toSpace E.etale_toSpace E.point
  let := stalkAlgebra B S hS N hN y hNdec E
  have := henselianLocalRing_isHenselization B S hS N hN y hNdec E
  obtain ⟨e, -⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization
    (R := E.scheme.left.1.presheaf.stalk E.point)
    (H := (henselianLocalRing B S hS N hN y hNdec : Type (u + 1)))
  exact IsNormalRing.congr e hstalk

end AlgebraicGeometry.Space

end
