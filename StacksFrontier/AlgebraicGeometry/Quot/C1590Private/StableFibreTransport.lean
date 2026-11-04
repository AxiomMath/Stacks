module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableCurveOverAmple
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableNearFibre

/-!
# Stability of a fibre does not depend on the field-valued point (towards Stacks 0E76)

Let `G` be a prestable family of curves and `s` a point of its base `S`. Every field-valued point
`Spec K → S` with image `s` factors through the residue field point `Spec κ(s) → S`, so the fibre
of `G` over it is the base change of the fibre over `κ(s)` along `κ(s) → K`. Stability of the fibre
is insensitive to such extensions of the ground field
(`AlgebraicGeometry.C1590Private.isStableCurveOver_iff_of_isPullback`, through the ampleness of the
dualizing sheaf and Stacks 0D2P), and to the choice of presentation of the fibre by a scheme. So
the fibre over one field-valued point with image `s` is stable exactly when the fibres over all of
them are: this is the "formation of this open commutes with arbitrary base change" of the proof of
Stacks 0E76, read on points.

## Main definitions

* `AlgebraicGeometry.C1590Private.residueFieldValuedPoint`: the field-valued point
  `Spec κ(s) → S` of the scheme `S` underlying an object of the site.

## Main results

* `AlgebraicGeometry.C1590Private.exists_hom_residueFieldValuedPoint`: a field-valued point with
  image `s` factors through the residue field point.
* `AlgebraicGeometry.C1590Private.isStableCurveOver_iff_residueFieldValuedPoint`: the fibre over a
  field-valued point with image `s` is stable exactly when the fibre over `κ(s)` is.
* `AlgebraicGeometry.C1590Private.hasStableFibresAt_of_isStableCurveOver`: if one fibre over `s`
  is stable, all are.

## Implementation notes

Unregistered helpers. Everything here is unconditional.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The field-valued point `Spec κ(s) ⟶ S` at a point `s` of the scheme `S` underlying an object
of the site. -/
def residueFieldValuedPoint (Y : BigFppfOver B integerBase hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y) :
    Space.FieldValuedPoint B integerBase hZ (schemeSpace Y).obj where
  carrier := ((BigFppfOver.toScheme B integerBase hZ).obj Y).residueField s
  contained := BigFppfSite.residueField_spec_contains B Y.left.2 s
  toBase := ((BigFppfOver.toScheme B integerBase hZ).obj Y).fromSpecResidueField s ≫ Y.hom.hom
  value := BigFppfOver.siteMapOver B integerBase hZ Y
    (BigFppfSite.residueField_spec_contains B Y.left.2 s)
    (((BigFppfOver.toScheme B integerBase hZ).obj Y).fromSpecResidueField s)

/-- **A field-valued point with image `s` factors through the residue field point at `s`**: its
morphism `Spec K ⟶ S` is `Spec K ⟶ Spec κ(s) ⟶ S` for a field embedding `κ(s) ⟶ K`. -/
theorem exists_hom_residueFieldValuedPoint {Y : BigFppfOver B integerBase hZ}
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y).obj)
    (hQ : ∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = s) :
    ∃ (φ : ((BigFppfOver.toScheme B integerBase hZ).obj Y).residueField s ⟶ .of Q.carrier)
      (m : Q.siteObject ⟶ (residueFieldValuedPoint Y s).siteObject),
      yoneda.map m ≫ yonedaEquiv.symm (residueFieldValuedPoint Y s).value =
          yonedaEquiv.symm Q.value ∧
        (BigFppfOver.toScheme B integerBase hZ).map m = Spec.map φ := by
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨φ, hf⟩ : ∃ φ : (T.obj Y).residueField s ⟶ .of Q.carrier,
      Spec.map φ ≫ (T.obj Y).fromSpecResidueField s = T.map Q.value := by
    obtain rfl : T.map Q.value (IsLocalRing.closedPoint Q.carrier) = s := hQ _
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Q.carrier (T.obj Y)
      (T.map Q.value)⟩
  refine ⟨φ, Over.homMk ⟨Spec.map φ⟩ ?_, ?_, rfl⟩
  · ext1
    show Spec.map φ ≫ (T.obj Y).fromSpecResidueField s ≫ Y.hom.hom = Q.toBase
    rw [← Category.assoc, hf]
    exact congrArg (fun k => k.hom) (Over.w (show Q.siteObject ⟶ Y from Q.value))
  · rw [yonedaEquiv_symm_value, yonedaEquiv_symm_value]
    refine (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ?_)
    ext1
    ext1
    exact hf

/-- **The fibre over a field-valued point is stable exactly when the fibre over the residue field
is.** Let `G` be a prestable family of curves, `Q` a field-valued point of its base with image
`s`, and `W`, `W₀` presentations of the fibres of `G` over `Q` and over `Spec κ(s)`. Then `W` is a
stable curve over the field of `Q` exactly when `W₀` is a stable curve over `κ(s)`: `W` is
isomorphic over that field to the base change of `W₀` along `κ(s) ⟶ K`. -/
theorem isStableCurveOver_iff_residueFieldValuedPoint {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) (s : (BigFppfOver.toScheme B integerBase hZ).obj G.base)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (hQ : ∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = s)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ G.total.obj)
    (hr : IsPullback r (yoneda.map w) G.toBase.hom (yonedaEquiv.symm Q.value))
    {W₀ : BigFppfOver B integerBase hZ} (w₀ : W₀ ⟶ (residueFieldValuedPoint G.base s).siteObject)
    (r₀ : yoneda.obj W₀ ⟶ G.total.obj)
    (hr₀ : IsPullback r₀ (yoneda.map w₀) G.toBase.hom
      (yonedaEquiv.symm (residueFieldValuedPoint G.base s).value)) :
    IsStableCurveOver Q.carrier ((BigFppfOver.toScheme B integerBase hZ).map w) ↔
      IsStableCurveOver (residueFieldValuedPoint G.base s).carrier
        ((BigFppfOver.toScheme B integerBase hZ).map w₀) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let P := residueFieldValuedPoint G.base s
  obtain ⟨φ, m, hm, hTm⟩ := exists_hom_residueFieldValuedPoint s Q hQ
  -- the base change of `W₀` along `m` presents the fibre over `Q`
  have hsq := IsPullback.of_hasPullback w₀ m
  have hr₁ : IsPullback (yoneda.map (pullback.fst w₀ m) ≫ r₀) (yoneda.map (pullback.snd w₀ m))
      G.toBase.hom (yonedaEquiv.symm Q.value) := by
    have h := (hsq.map yoneda).paste_horiz hr₀
    rwa [hm] at h
  -- it is isomorphic to `W` over the field of `Q`
  let e := hr.isoIsPullback _ _ hr₁
  let e₀ : W ≅ pullback w₀ m := Yoneda.fullyFaithful.preimageIso e
  have he₀ : e₀.hom ≫ pullback.snd w₀ m = w := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, show yoneda.map e₀.hom = e.hom from Yoneda.fullyFaithful.map_preimage _]
    exact hr.isoIsPullback_hom_snd _ _ hr₁)
  have hiso : IsStableCurveOver Q.carrier (T.map w) ↔
      IsStableCurveOver Q.carrier (T.map (pullback.snd w₀ m)) :=
    ⟨fun h => isStableCurveOver_of_iso (T.mapIso e₀).symm
        (by rw [Iso.symm_hom, Functor.mapIso_inv, ← Functor.map_comp, ← he₀,
          Iso.inv_hom_id_assoc]) h,
      fun h => isStableCurveOver_of_iso (T.mapIso e₀)
        (by rw [Functor.mapIso_hom, ← Functor.map_comp, he₀]) h⟩
  rw [hiso]
  -- the field extension `κ(s) ⟶ K`
  let : Algebra P.carrier Q.carrier := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap P.carrier Q.carrier)) = T.map m := by
    rw [hTm]
    rfl
  have hsqT : IsPullback (T.map (pullback.fst w₀ m)) (T.map (pullback.snd w₀ m)) (T.map w₀)
      (Spec.map (CommRingCat.ofHom (algebraMap P.carrier Q.carrier))) := by
    rw [hφ]
    exact hsq.map T
  obtain ⟨hp₀, hdim₀, hH0₀, hnodal₀⟩ := fibre_properties_of_isPrestableCurveFamily hG P w₀ r₀ hr₀
  obtain ⟨hp₁, hdim₁, hH0₁, hnodal₁⟩ :=
    fibre_properties_of_isPrestableCurveFamily hG Q (pullback.snd w₀ m) _ hr₁
  exact (isStableCurveOver_iff_of_isPullback (T.map w₀) (T.map (pullback.fst w₀ m))
    (T.map (pullback.snd w₀ m)) hsqT hdim₀ hnodal₀ hdim₁ hnodal₁).symm

/-- **If one fibre over `s` is stable, all are.** For a prestable family `G`, if the fibre over
one field-valued point with image `s` has a stable presentation, then every presentation of the
fibre over every field-valued point with image `s` is a stable curve. -/
theorem hasStableFibresAt_of_isStableCurveOver {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) (s : (BigFppfOver.toScheme B integerBase hZ).obj G.base)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (hQ : ∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = s)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ G.total.obj)
    (hr : IsPullback r (yoneda.map w) G.toBase.hom (yonedaEquiv.symm Q.value))
    (h : IsStableCurveOver Q.carrier ((BigFppfOver.toScheme B integerBase hZ).map w)) :
    HasStableFibresAt G s := by
  obtain ⟨W₀, w₀, r₀, hr₀⟩ := exists_presentation_of_fieldValuedPoint G
    (residueFieldValuedPoint G.base s)
  have h₀ := (isStableCurveOver_iff_residueFieldValuedPoint hG s Q hQ w r hr w₀ r₀ hr₀).1 h
  intro Q' hQ' W' w' r' hr'
  exact (isStableCurveOver_iff_residueFieldValuedPoint hG s Q' hQ' w' r' hr' w₀ r₀ hr₀).2 h₀

end AlgebraicGeometry.C1590Private

end
