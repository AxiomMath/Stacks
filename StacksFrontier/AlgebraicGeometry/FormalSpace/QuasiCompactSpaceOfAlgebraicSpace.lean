module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection

/-!
# Quasi-compactness of an algebraic space read as a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `P` be an algebraic space over `S`,
with values in `Type u`. Its universe lift `P ⋙ uliftFunctor` is an fppf sheaf with values in
`Type (u + 1)`, the universe in which formal algebraic spaces over `S` live. This file proves
that `P` is a quasi-compact algebraic space in the sense of Stacks 03E3 exactly when an fppf
sheaf isomorphic to its universe lift is a quasi-compact formal algebraic space in the sense of
condition (3) of Stacks 0AJ9, `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`.

This is the agreement `AlgebraicGeometry.FormalSpace.QuasiCompactSpaceAgreesOnAlgebraicSpaces`
for the algebraic spaces which come from the value universe of the schemes; the fibre products
of a completion morphism `f_{/T}` with affine schemes are of this kind, which is what the proof
of Stacks 0ARU needs.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_iso_uliftFunctor`: a quasi-compact
  algebraic space is a quasi-compact formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isQuasiCompactSpace_of_iso`: an
  algebraic space which is a quasi-compact formal algebraic space is quasi-compact.

## Implementation notes

*From the algebraic space to the formal one.* By Stacks 03H6 a quasi-compact algebraic space
`P` has a surjective étale morphism `h_U ⟶ P` from an affine scheme `U` of the site. The sheaf
represented by `U` is an affine formal algebraic space, presented by the constant diagram on
`U`; the sheafified universe lift of `h_U ⟶ P` is representable by algebraic spaces and étale
(`AlgebraicGeometry.FormalSpace.exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale`) and a
surjection of sheaves; and the set-theoretic condition of Stacks 0AIS follows from that
surjection and the representability of the diagonal of `P`, by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_isAlgebraicSpace_of_mono_of_epi`.

*From the formal algebraic space to the algebraic one.* An affine formal algebraic space `Z`
mapping onto the universe lift of `P` by a surjection of sheaves is the colimit of affine
schemes along thickenings; the inclusion of one stage `T₀` into `Z` is a representable
thickening (Stacks 0AI9), hence bijective on points, and a surjection of sheaves is surjective
on points. So `h_{T₀} ⟶ P` is surjective on points, and `P` is quasi-compact as the image of
the quasi-compact algebraic space `h_{T₀}` (Stacks 040W).

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf underlying the sheaf represented by `T` is the universe lift of the
representable presheaf. -/
private noncomputable def sheafifiedYonedaObjIsoUliftYoneda (T : BigFppfOver B S hS) :
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T).obj ≅
      uliftYoneda.{u + 1}.obj T :=
  haveI := bigFppfOver_subcanonical B S hS
  (sheafToPresheaf _ (Type (u + 1))).mapIso
    ((Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).app T) ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.app T

/-- **A quasi-compact algebraic space is a quasi-compact formal algebraic space.** Let `P` be a
quasi-compact algebraic space over `S` and let `W` be an fppf sheaf with values in
`Type (u + 1)` whose underlying presheaf is isomorphic to the universe lift of `P`. Then `W`
is a quasi-compact formal algebraic space in the sense of condition (3) of Stacks 0AJ9: the
sheaf represented by an affine étale surjective chart of `P` (Stacks 03H6) maps onto it by a
morphism representable by algebraic spaces, étale and surjective. -/
theorem isQuasiCompactSpace_of_iso_uliftFunctor
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (hPqc : Space.IsQuasiCompactSpace B S hS P)
    {W : FppfSheaf B S hS} (e : W.obj ≅ P ⋙ uliftFunctor.{u + 1}) :
    IsQuasiCompactSpace B S hS W := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, a, hU, haS, haE⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P hP).mp hPqc
  -- The sheaf isomorphism between the sheafified universe lift of `P` and `W`.
  let E : Space.sheafifiedULift B S hS P ≅ W :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      ((Space.sheafifiedULiftIso B S hS P hP.isSheaf).symm ≪≫ e.symm)
  let Z := (Sheaf.sheafifiedYoneda J).obj U
  let α : Z ≅ Space.sheafifiedULift B S hS (yoneda.obj U) :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      (sheafifiedYonedaObjIsoUliftYoneda B S hS U ≪≫
        Space.sheafifiedULiftIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U).isSheaf)
  let c₀ := Space.sheafifiedULiftMap B S hS a
  let c : Z ⟶ W := α.hom ≫ c₀ ≫ E.hom
  -- The chart is a surjection of sheaves.
  have : Presheaf.IsLocallySurjective J a := isLocallySurjective_of_surjective_etale B S hS a haS
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS a).1 haE)
  have h₁ : Presheaf.IsLocallySurjective J (Functor.whiskerRight a uliftFunctor.{u + 1}) := by
    refine ⟨fun {V} s => J.superset_covering ?_ (Presheaf.imageSieve_mem J a s.down)⟩
    rintro V' g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩
  have hfac : J.toSheafify (yoneda.obj U ⋙ uliftFunctor.{u + 1}) ≫ c₀.hom =
      Functor.whiskerRight a uliftFunctor.{u + 1} ≫ J.toSheafify (P ⋙ uliftFunctor.{u + 1}) :=
    (J.toSheafify_naturality _).symm
  have h₁₂ := @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁
    (Presheaf.isLocallySurjective_toSheafify _ _)
  have hc₀epi : Epi c₀ := (Sheaf.isLocallySurjective_iff_epi c₀).mp
    (@Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hfac h₁₂)
  have hc : Sheaf.IsLocallySurjective c := (Sheaf.isLocallySurjective_iff_epi c).mpr inferInstance
  -- The chart is representable by algebraic spaces and étale.
  obtain ⟨hrep₀, het₀⟩ := exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS U) hP a haE
  let : MorphismProperty.RespectsIso
      (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom) := by
    refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_) <;>
    have : IsIso e.hom.hom :=
      ⟨e.inv.hom, congrArg (fun k => k.hom) e.hom_inv_id, congrArg (fun k => k.hom) e.inv_hom_id⟩
    · exact isEtaleULift_precomp_iso B S hS (asIso e.hom.hom) f.hom hf
    · exact isEtaleULift_comp B S hS hf (isEtaleULift_of_isIso B S hS e.hom.hom)
  have hcomm : α.hom ≫ c₀ = c ≫ E.inv := by simp [c]
  have hsq : IsPullback ((sheafToPresheaf J (Type (u + 1))).mapIso α).hom c.hom c₀.hom
      ((sheafToPresheaf J (Type (u + 1))).mapIso E).inv := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    have h := congrArg (sheafToPresheaf J (Type (u + 1))).map hcomm
    rwa [Functor.map_comp, Functor.map_comp] at h
  refine ⟨?_, Z, c, isAffineFormalAlgebraicSpace_sheafifiedYoneda B S hS U hU,
    ⟨_, Space.hasPropertyULift_of_isPullback B S hS hsq hrep₀ het₀⟩, hc⟩
  -- The set-theoretic condition.
  let q : J.uliftYoneda.{u + 1}.obj U ⟶ Space.sheafifiedULift B S hS P :=
    (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).inv.app U ≫ α.hom ≫ c₀
  have : Epi q := inferInstance
  exact satisfiesSetTheoreticCondition_of_iso B S hS E
    (satisfiesSetTheoreticCondition_of_isAlgebraicSpace_of_mono_of_epi hP (𝟙 _) U q)

/-- **An algebraic space which is a quasi-compact formal algebraic space is quasi-compact.**
Let `P` be an algebraic space over `S` and let `W` be an fppf sheaf with values in
`Type (u + 1)` whose underlying presheaf is isomorphic to the universe lift of `P`. If `W` is a
quasi-compact formal algebraic space in the sense of condition (3) of Stacks 0AJ9, then `P` is
a quasi-compact algebraic space in the sense of Stacks 03E3.

A stage `T₀` of the affine formal algebraic space surjecting onto `W` maps to it bijectively on
points (Stacks 0AI9), and a surjection of sheaves is surjective on points; so the affine scheme
`T₀` maps onto `P` surjectively on points, and `P` is quasi-compact by Stacks 040W. -/
theorem isQuasiCompactSpace_of_isQuasiCompactSpace_of_iso
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {W : FppfSheaf B S hS} (e : W.obj ≅ P ⋙ uliftFunctor.{u + 1})
    (hW : IsQuasiCompactSpace B S hS W) : Space.IsQuasiCompactSpace B S hS P := by
  classical
  obtain ⟨-, Z, c, ⟨-, I, pre, hne, hdir, D, hD, ⟨eZ⟩⟩, -, hc⟩ := hW
  let _ : Preorder I := pre
  have _ : Nonempty I := hne
  have _ : IsDirected I (· ≤ ·) := hdir
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let i₀ : I := Classical.arbitrary I
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)
  let s : (Sheaf.sheafifiedYoneda J).obj T₀ ⟶ Z :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J) i₀ ≫ eZ.symm.hom
  have hsbij : Function.Bijective (Space.pointsMapULift.{u + 1} B S hS _ s.hom) :=
    bijective_pointsMapULift_of_bijective_app B S hS s.hom
      (bijective_app_of_relativeThickening B S hS s
        (isThickening_colimitι B S hS D hD Z eZ.symm i₀))
  let ε := sheafifiedYonedaObjIsoUliftYoneda B S hS T₀
  let h : yoneda.obj T₀ ⋙ uliftFunctor.{u + 1} ⟶ P ⋙ uliftFunctor.{u + 1} :=
    ε.inv ≫ s.hom ≫ c.hom ≫ e.hom
  have hh : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ h) := by
    change Function.Surjective
      (Space.pointsMapULift.{u + 1} B S hS _ (ε.inv ≫ s.hom ≫ c.hom ≫ e.hom))
    rw [Space.pointsMapULift_comp, Space.pointsMapULift_comp, Space.pointsMapULift_comp]
    exact (((Space.surjective_pointsMapULift_of_isIso B S hS e.hom).comp
      (isSurjective_of_isLocallySurjective B S hS hc)).comp
      hsbij.2).comp (Space.surjective_pointsMapULift_of_isIso B S hS ε.inv)
  let hFF : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1}).whiskeringRight _
  let m : yoneda.obj T₀ ⟶ P := hFF.preimage h
  have hm : Functor.whiskerRight m uliftFunctor.{u + 1} = h := hFF.map_preimage h
  have hmsurj : Space.IsSurjective B S hS m := by
    refine (Space.isSurjectiveULift_whiskerRight_iff.{u + 1} B S hS m).mp ?_
    rwa [Space.IsSurjectiveULift, hm]
  have hT₀ : CompactSpace ((BigFppfOver.toScheme B S hS).obj T₀) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := (D.obj i₀).2
    infer_instance
  exact Space.IsQuasiCompactSpace.of_isSurjective B S hS (isAlgebraicSpace_yoneda B S hS T₀) hP
    hmsurj (Space.isQuasiCompact_yoneda_of_compact B S hS T₀ hT₀)

end AlgebraicGeometry.FormalSpace

end
