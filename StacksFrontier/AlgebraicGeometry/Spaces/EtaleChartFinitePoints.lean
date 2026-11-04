module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# An étale chart with quasi-compact relation projections has finite fibres on points

Let `X` be an algebraic space over a scheme `S` and let `φ : h_U ⟶ X` be an étale morphism
from a representable presheaf whose self-fibre product `R = h_U ×_X h_U` has quasi-compact
projections to `h_U`. Stacks 03IJ asserts that both `|U| → |X|` and `|R| → |X|` have finite
fibres. This file proves it.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.finite_fiber_pointsMap_of_etale_presentation` and
  `AlgebraicGeometry.Space.finite_fiber_selfPullback_pointsMap_of_etale_presentation` are the
  two assertions of Stacks 03IJ.
* `AlgebraicGeometry.Space.finite_fiber_pointsMap_pullback_fst`: the fibre of
  `|R| → |U|` above *any* point of `|U|` is finite. This is the substance of Stacks 03IJ; both
  of its assertions are bookkeeping on top of it.
* `AlgebraicGeometry.finite_of_etale_of_subsingleton`: a quasi-compact scheme étale over a
  one-point scheme has finitely many points.
* `AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj` of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae`: a representable
  presheaf which is a quasi-compact algebraic space over `S` has quasi-compact underlying
  scheme.

## Implementation notes

The Stacks argument identifies the fibre of `|U| → |X|` above the image of `u ∈ U` with
`s(t^{-1}(\{u\}))` and then appeals to Stacks 02GL, that an étale morphism has fibres which are
disjoint unions of spectra of fields. Here the two halves appear as follows.

The identification of the fibre is the surjectivity of
`AlgebraicGeometry.Space.exists_points_of_isPullback`, applied to the cartesian square
presenting `R = h_U ×_X h_U`: two points of `|U|` with the same image in `|X|` are the two
projections of a point of `|R|`. That is Stacks 03H4 and needs no étaleness; the fibre of
`|U| → |X|` is therefore the image under one projection of the fibre of the other projection
above one chosen point of the fibre, and the whole content of the tag is the finiteness of
*that* fibre.

For the finiteness, the chosen point of `|U|` is a class of field-valued points of Tag 03BU, so
it comes with a morphism `h_{Spec K} ⟶ h_U` presenting it
(`AlgebraicGeometry.Space.fieldMorphism`). Étaleness of `φ` makes `R ⟶ h_U` representable, so
the base change of `R ⟶ h_U` along that morphism is represented by an object `R₀` of the site
which is étale over `Spec K`; quasi-compactness of `R ⟶ h_U` in the sense of Stacks 03HE,
applied to the quasi-compact algebraic space `h_{Spec K}`, makes `R₀` quasi-compact. A
quasi-compact scheme étale over the one-point scheme `Spec K` is finite — this replaces the
appeal to Stacks 02GL, going instead through local quasi-finiteness of an étale morphism
(Stacks 03II) and finiteness of the quasi-finite points of a fibre of a finite-type morphism
(Stacks 0AAY). The fibre of `|R| → |U|` above the chosen point is then contained in the image
of `|R₀|`, which is the finite point set of `R₀` by Tag 03BX.

Two remarks on the hypotheses. Only quasi-compactness of the *first* projection is used: the
fibre of `|R| → |X|` is the union, over the finitely many points of the fibre of `|U| → |X|`,
of the fibres of the first projection, so the second projection enters only through the
cartesian square and not through its quasi-compactness. The hypothesis on the second
projection is retained because Stacks 03IJ states it, and is named `_ht`. Algebraicity of `X`
is likewise not used — representability of `R ⟶ h_U` comes from étaleness of `φ`, which
`AlgebraicGeometry.Space.IsEtale` already contains — and so, as in the Stacks statement of this
tag, it does not appear in the signature.

## References

* [Stacks Project, Tag 03IJ](https://stacks.math.columbia.edu/tag/03IJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level input -/

/-- A quasi-compact scheme étale over a scheme with at most one point has finitely many
points.

Every morphism to a scheme with at most one point out of a quasi-compact scheme is
quasi-compact, since the preimage of an open subset of the target is either empty or
everything; an étale morphism is locally quasi-finite by Stacks 03II, so Stacks 0AAY applies
and the whole source is one fibre. -/
theorem finite_of_etale_of_subsingleton {A V : Scheme.{u}} (h : A ⟶ V) [Etale h]
    [CompactSpace A] [Subsingleton V] : Finite A := by
  obtain ⟨hft, hlqf⟩ := locallyQuasiFinite_of_etale h
  rcases isEmpty_or_nonempty A with hA | hA
  · exact Finite.of_subsingleton
  · obtain ⟨x₀⟩ := hA
    have hqc : QuasiCompact h := ⟨fun U _ _ => by
      rcases U.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
      · simp
      · have hU : U = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim y s ▸ hs
        rw [hU, Set.preimage_univ]
        exact isCompact_univ⟩
    have hfin := finite_setOf_mapsTo_and_quasiFiniteAt h (h x₀)
    have heq : {x : A | h x = h x₀ ∧ quasiFiniteAt h x} = Set.univ :=
      Set.eq_univ_of_forall fun x =>
        ⟨Subsingleton.elim _ _, (forall_quasiFiniteAt_iff h).mpr ⟨hft, hlqf⟩ x⟩
    rw [heq] at hfin
    exact Set.finite_univ_iff.mp hfin

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness of a representable algebraic space -/

/-- **The relation of a quasi-compact étale chart has finite fibres over the chart.** For an
étale morphism `φ : h_U ⟶ X` of presheaves on the big fppf site of `S` out of a representable
presheaf whose first self-fibre-product projection is quasi-compact in the sense of Stacks
03HE, the fibre of `|h_U ×_X h_U| → |h_U|` above any point of `|U|` is finite.

This is the substance of Stacks 03IJ. The chosen point is presented by a morphism
`h_{Spec K} ⟶ h_U` out of the spectrum of a field, the base change of the projection along it
is represented by an object of the site which is étale over `Spec K` and quasi-compact, hence
has finitely many points, and every point of the fibre lifts to it. -/
theorem finite_fiber_pointsMap_pullback_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hφ : IsEtale B S hS φ) (hs : IsQuasiCompact B S hS (pullback.fst φ φ))
    (a₀ : points B S hS (yoneda.obj U)) :
    (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) ⁻¹' {a₀}).Finite := by
  obtain ⟨p₀, hp₀⟩ := Quot.exists_rep a₀
  have hφp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := presheaf_etale_of_isEtale B S hS hφ
  have hfstp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst φ φ) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback φ φ).flip hφp
  have sqR := hfstp.rep.isPullback (fieldMorphism B S hS (yoneda.obj U) p₀)
  have hRet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hfstp.rep.snd (fieldMorphism B S hS (yoneda.obj U) p₀))) :=
    hfstp.property_snd _
  have hVsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p₀.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p₀.carrier)))
  have hVfin : Finite ((BigFppfOver.toScheme B S hS).obj p₀.siteObject) :=
    Finite.of_subsingleton
  have hVcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj p₀.siteObject) :=
    Finite.compactSpace
  have hqcs : IsQuasiCompactSpace B S hS
      (pullback (fieldMorphism B S hS (yoneda.obj U) p₀) (pullback.fst φ φ)) :=
    hs (yoneda.obj p₀.siteObject) (isAlgebraicSpace_yoneda B S hS p₀.siteObject)
      (isQuasiCompactSpace_yoneda_obj B S hS hVcpt) _
  have hRcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hfstp.rep.pullback (fieldMorphism B S hS (yoneda.obj U) p₀))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (hqcs.of_iso B S hS
        ((IsPullback.of_hasPullback (fieldMorphism B S hS (yoneda.obj U) p₀)
          (pullback.fst φ φ)).flip.isoIsPullback _ _ sqR))
  have hRfin : Finite ((BigFppfOver.toScheme B S hS).obj
      (hfstp.rep.pullback (fieldMorphism B S hS (yoneda.obj U) p₀))) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map
      (hfstp.rep.snd (fieldMorphism B S hS (yoneda.obj U) p₀)))
  have hRpts : Finite (points B S hS (yoneda.obj
      (hfstp.rep.pullback (fieldMorphism B S hS (yoneda.obj U) p₀)))) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS _).symm
  refine Set.Finite.subset (Set.finite_range (pointsMap B S hS _
    (hfstp.rep.fst (fieldMorphism B S hS (yoneda.obj U) p₀)))) ?_
  intro r hr
  have hr' : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = a₀ := hr
  obtain ⟨w, hw1, -⟩ := exists_points_of_isPullback B S hS sqR r
    ((p₀.tautologicalPoint B S hS (yoneda.obj U)).class B S hS
      (yoneda.obj p₀.siteObject))
    (by rw [hr', pointsMap_fieldMorphism_tautologicalPoint]; exact hp₀.symm)
  exact ⟨w, hw1⟩

/-! ### Stacks 03IJ -/

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X)

/-- **Stacks 03IJ, the fibres of the presenting scheme.** An étale morphism `φ : h_U ⟶ X` of
presheaves on the big fppf site of `S` out of a representable presheaf whose self-fibre-product
projections are quasi-compact in the sense of Stacks 03HE has finite fibres on points.

Any point of a fibre of `|U| → |X|` and a fixed point of that fibre are the two projections of
a point of the relation, so the fibre is the image of a fibre of the first projection of the
relation. -/
@[stacks 03IJ "fibres of the presenting scheme"]
theorem finite_fiber_pointsMap_of_etale_presentation
    (hφ : IsEtale B S hS φ) (hs : IsQuasiCompact B S hS (pullback.fst φ φ))
    (_ht : IsQuasiCompact B S hS (pullback.snd φ φ)) (x : points B S hS X) :
    (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite := by
  rcases Set.eq_empty_or_nonempty (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}) with
    hempty | ⟨a₀, ha₀⟩
  · rw [hempty]
    exact Set.finite_empty
  · have ha₀' : pointsMap B S hS (yoneda.obj U) φ a₀ = x := ha₀
    refine Set.Finite.subset
      ((finite_fiber_pointsMap_pullback_fst B S hS φ hφ hs a₀).image
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ))) ?_
    intro a ha
    have ha' : pointsMap B S hS (yoneda.obj U) φ a = x := ha
    obtain ⟨r, hr1, hr2⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback φ φ) a₀ a (by rw [ha₀', ha'])
    exact ⟨r, hr1, hr2⟩

/-- **Stacks 03IJ, the fibres of the relation scheme.** Under the same hypotheses the relation
`h_U ×_X h_U` has finite fibres on points over `X`.

A fibre of `|R| → |X|` is the union, over the finitely many points of the corresponding fibre
of `|U| → |X|`, of the fibres of `|R| → |U|`. -/
@[stacks 03IJ "fibres of the relation scheme"]
theorem finite_fiber_selfPullback_pointsMap_of_etale_presentation
    (hφ : IsEtale B S hS φ) (hs : IsQuasiCompact B S hS (pullback.fst φ φ))
    (ht : IsQuasiCompact B S hS (pullback.snd φ φ)) (x : points B S hS X) :
    (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) ⁻¹' {x}).Finite := by
  have hcover : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) ⁻¹' {x}
      = ⋃ a ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x},
          pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) ⁻¹' {a} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      pointsMap_comp_apply, exists_prop]
    exact ⟨fun hr => ⟨_, hr, rfl⟩, fun ⟨a, ha, hra⟩ => hra ▸ ha⟩
  rw [hcover]
  exact Set.Finite.biUnion
    (finite_fiber_pointsMap_of_etale_presentation B S hS X U φ hφ hs ht x)
    fun a _ => finite_fiber_pointsMap_pullback_fst B S hS φ hφ hs a

end Space

end AlgebraicGeometry

end
