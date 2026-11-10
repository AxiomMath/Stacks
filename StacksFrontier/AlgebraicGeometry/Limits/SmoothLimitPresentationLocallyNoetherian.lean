module

public import StacksFrontier.AlgebraicGeometry.Limits.SmoothLimitPresentationOfCompletedStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletionMapBijective

/-!
# The completed local ring of a locally Noetherian scheme as a cofiltered limit of smooth schemes

Let `S` be a locally Noetherian scheme and `s` a point of `S` whose local ring `𝒪_{S, s}` is a
G-ring. Then the spectrum of the completion `𝒪^∧_{S, s}` is the limit of a cofiltered diagram of
affine schemes smooth over `S`, compatibly with the canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ Spec 𝒪_{S, s} ⟶ S`.

## Main results

* `exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isLocallyNoetherian`: the
  affineness hypothesis removed from
  `exists_cofiltered_smooth_limit_presentation_specCompletedStalk`.

## Implementation notes

The base is shrunk to an affine open neighbourhood `V` of `s`, produced by
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`. Such a `V` is affine, and locally
Noetherian as an open subscheme of a locally Noetherian scheme, hence Noetherian, so
`exists_cofiltered_smooth_limit_presentation_specCompletedStalk` applies to it at the point
`s' := ⟨s, hs⟩`. The local ring at `s'` is the local ring at `s` by
`AlgebraicGeometry.Scheme.Opens.stalkIso`, which moves the G-ring hypothesis across by Tag 07PV
(`isGRing_of_essFiniteType`, applied to the algebra structure that the isomorphism defines).

The conclusion is transported back to `S` along an arbitrary open immersion `j : X ⟶ Y` carrying
a point `x` to a point `y`, the equality `j x = y` being a hypothesis. The point equality
`V.ι s' = s` holds by `rfl` but not syntactically; with `y` substituted away, the terms
`Spec.map (j.stalkMap x)` and `Y.fromSpecStalk (j x)` are composable on the nose:

* `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk` turns
  `X.fromSpecStalk x ≫ j` into `Spec.map (j.stalkMap x) ≫ Y.fromSpecStalk (j x)`, which is the
  geometric half.
* `AlgebraicGeometry.Scheme.Hom.bijective_completionMapAt_of_isIso_stalkMap` makes
  `j.completionMapAt rfl` bijective — `j.stalkMap x` is an isomorphism because `j` is an open
  immersion — so `RingEquiv.ofBijective` of it is an isomorphism of completed local rings, and
  `adicCompletionMap_comp_algebraMap` says it is compatible with the maps from the uncompleted
  local rings. That is the ring half. The `stalkCongr` factor hidden inside
  `AlgebraicGeometry.Scheme.Hom.stalkHomAt` is the identity here, the point equality being `rfl`.

`Spec` of that isomorphism splices into the limit identification, and the structure morphisms are
post-composed with `j`; smoothness survives because an open immersion is smooth and smooth
morphisms compose.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The affine Noetherian presentation of a completed local ring, pushed forward along an open
immersion `j : X ⟶ Y` carrying `x` to `y`. The diagram and the limit are unchanged; only the
structure morphisms are post-composed with `j`, and the completed local ring at `y` is identified
with the one at `x`. -/
private theorem exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isOpenImmersion
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [IsAffine X] [IsNoetherian X]
    (x : X) (y : Y) (hj : j x = y) (hG : IsGRing (X.presheaf.stalk x)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u})
      (p : D ⟶ (Functor.const I).obj Y)
      (c : Cone D) (_ : IsLimit c)
      (e : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y))) ≅ c.pt),
      (∀ i, IsAffine (D.obj i)) ∧
      (∀ i, Smooth (p.app i)) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ p.app i =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))) ≫
        Y.fromSpecStalk y) := by
  subst hj
  obtain ⟨I, hI, hcof, D, pp, c, hc, e, haff, hsm, hcompat⟩ :=
    exists_cofiltered_smooth_limit_presentation_specCompletedStalk x hG
  let φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk (j x))) (Y.presheaf.stalk (j x)) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
    RingEquiv.ofBijective (j.completionMapAt rfl)
      (Scheme.Hom.bijective_completionMapAt_of_isIso_stalkMap j rfl)
  let specIso : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (Y.presheaf.stalk (j x)))
        (Y.presheaf.stalk (j x)))) ≅
      Spec (CommRingCat.of (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))) :=
    asIso (Spec.map φ.toCommRingCatIso.inv)
  refine ⟨I, hI, hcof, D, pp ≫ (Functor.const I).map j, c, hc, specIso ≪≫ e, haff,
    fun i => ?_, fun i => ?_⟩
  · have := hsm i
    change Smooth (pp.app i ≫ j)
    infer_instance
  · have hgeo : X.fromSpecStalk x ≫ j =
        Spec.map (j.stalkMap x) ≫ Y.fromSpecStalk (j x) :=
      (Scheme.SpecMap_stalkMap_fromSpecStalk j (x := x)).symm
    have hring : j.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) ≫
          φ.toCommRingCatIso.inv =
        CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (j x))
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk (j x)))
            (Y.presheaf.stalk (j x)))) := by
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      have ha : φ (algebraMap (Y.presheaf.stalk (j x)) _ a) =
          algebraMap (X.presheaf.stalk x) _ (j.stalkHomAt rfl a) :=
        RingHom.congr_fun (adicCompletionMap_comp_algebraMap (j.stalkHomAt rfl)
          (maximalIdeal (Y.presheaf.stalk (j x))) (maximalIdeal (X.presheaf.stalk x))
          (IsLocalRing.map_maximalIdeal_le _)) a
      have hhom : (j.stalkMap x).hom a = j.stalkHomAt rfl a := by
        simp [Scheme.Hom.stalkHomAt, TopCat.Presheaf.stalkCongr_hom]
      change φ.symm (algebraMap (X.presheaf.stalk x) _ ((j.stalkMap x).hom a)) = _
      rw [hhom, ← ha, φ.symm_apply_apply]
      rfl
    have main : specIso.hom ≫ (e.hom ≫ c.π.app i ≫ pp.app i) ≫ j =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (j x))
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk (j x)))
            (Y.presheaf.stalk (j x))))) ≫ Y.fromSpecStalk (j x) := by
      rw [hcompat i, Category.assoc, hgeo]
      simp only [specIso, asIso_hom]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun f => Spec.map f ≫ Y.fromSpecStalk (j x)) hring
    change (specIso.hom ≫ e.hom) ≫ c.π.app i ≫ pp.app i ≫ j = _
    rw [← main]
    simp only [Category.assoc]

/-- **The completed local ring of a locally Noetherian scheme is a cofiltered limit of smooth
affine schemes over the scheme.** Let `S` be a locally Noetherian scheme and `s` a point of `S`
whose local ring is a G-ring. Then `Spec 𝒪^∧_{S, s}` is the limit of a cofiltered diagram of
affine schemes, each smooth over `S`, and the limit projections composed with the smooth
structure morphisms all agree with the canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ Spec 𝒪_{S, s} ⟶ S`. -/
public theorem exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isLocallyNoetherian
    {S : Scheme.{u}} [IsLocallyNoetherian S] (s : S)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u})
      (p : D ⟶ (Functor.const I).obj S)
      (c : Cone D) (_ : IsLimit c)
      (e : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s))) ≅ c.pt),
      (∀ i, IsAffine (D.obj i)) ∧
      (∀ i, Smooth (p.app i)) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ p.app i =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s) := by
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := s) (U := ⊤) trivial
  have : IsAffine V.toScheme := hV
  have : IsNoetherian V.toScheme := IsNoetherian.mk
  have hGV : IsGRing (V.toScheme.presheaf.stalk (⟨s, hsV⟩ : V.toScheme)) := by
    let eV : S.presheaf.stalk s ≃+* V.toScheme.presheaf.stalk (⟨s, hsV⟩ : V.toScheme) :=
      (Scheme.Opens.stalkIso V ⟨s, hsV⟩).symm.commRingCatIsoToRingEquiv
    let _ : Algebra (S.presheaf.stalk s)
        (V.toScheme.presheaf.stalk (⟨s, hsV⟩ : V.toScheme)) := eV.toRingHom.toAlgebra
    have : Algebra.FiniteType (S.presheaf.stalk s)
        (V.toScheme.presheaf.stalk (⟨s, hsV⟩ : V.toScheme)) :=
      RingHom.finiteType_algebraMap.mp
        (RingHom.FiniteType.of_surjective eV.toRingHom eV.surjective)
    exact isGRing_of_essFiniteType hG
  exact exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isOpenImmersion
    V.ι ⟨s, hsV⟩ s rfl hGV

end AlgebraicGeometry

end
